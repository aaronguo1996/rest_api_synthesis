use crate::{Expr, ExprIx, Prog, ProgIx, Traces};
use hashbrown::HashMap;
use lasso::{Rodeo, RodeoResolver, Spur};
use rand::{distributions::WeightedIndex, prelude::*, seq::SliceRandom};
use serde_json::Value;

/// A `Runner` is responsible for coordinating the whole RE process.
/// It first loads all of the traces and translates all of the expressions.
/// It then runs RE in a multithreaded fashion.
pub struct Runner {
    arena: Arena,
    /// A list of root programs stored in the `arena`.
    progs: Vec<ProgIx>,
}

impl Runner {
    pub fn new(mut arena: Arena, progs: Vec<ProgIx>) -> Self {
        // Swap arena into read-only mode
        arena = arena.swap_rodeo();

        Self { arena, progs }
    }

    /// Runs retrospective execution over a set of inputs.
    /// inputs is a map from an input argument name to a list of possible
    /// values for that input.
    pub fn run(self, inputs: &[(Spur, Vec<Value>)]) -> Vec<(ProgIx, usize)> {
        let mut res = vec![];

        // TODO: profile loop order
        // For each program, generate a few random vals and execute
        for prog in &self.progs {
            // TODO: repeat
            let mut env = HashMap::new();

            // Choose random values for our inputs
            let mut rng = thread_rng();
            for (input_name, input_vals) in inputs {
                env.insert(*input_name, input_vals.choose(&mut rng).unwrap().clone());
            }

            // Make a new execution environment
            let mut ex = ExecEnv::new(&self.arena, *prog, env);

            // TODO: do analysis on result value
            let out = ex.run(0);
            let (_res, cost) = out.unwrap_or_else(|| (None, 99999));
            res.push((*prog, cost));
        }

        res
    }
}

// TODO: separate out the environment from the execution invocation?
// struct and execution is immutable, execute takes param to mutable env
/// An `ExecEnv` is an execution environment, holding all the information
/// needed for the execution of one expression on one input.
pub struct ExecEnv<'a> {
    // invocation params
    arena: &'a Arena,
    prog: ProgIx,

    // mutating state
    env: HashMap<Spur, Value>,
}

impl<'a> ExecEnv<'a> {
    pub fn new(arena: &'a Arena, prog: ProgIx, env: HashMap<Spur, Value>) -> Self {
        Self { arena, prog, env }
    }

    pub fn run(&mut self, ip: usize) -> Option<(Option<Value>, usize)> {
        // Do some initialization for the program
        let p = &self.arena.progs[self.prog].exprs;
        if ip == p.len() - 1 {
            // If we're on the last instruction, just execute it and return its results.
            return self.exec_expr(p[ip]);
        } else {
            // Otherwise, we match against the expression ip points to.
            let e = &self.arena.exprs[p[ip]];
            match e {
                Expr::Assign(x, e, true) => {
                    // Short-circuiting behavior for binds
                    let (rhs, cost) = self.exec_expr(*e)?;

                    let mut bind_cost = 0;
                    let mut vals = vec![];

                    // For each item in the result array
                    for v in rhs?.as_array()? {
                        // Insert the binding var into the env
                        self.push_var(*x, v.clone());

                        if let Some((sub_val, sub_cost)) = self.run(ip + 1) {
                            if let Some(sub_val) = sub_val {
                                vals.push(sub_val);
                                bind_cost += sub_cost;
                            }
                        }

                        // Then remove the binding var from the env
                        self.pop_var(*x);
                    }

                    if vals.len() == 0 {
                        None
                    } else {
                        let cost = cost + bind_cost / vals.len();
                        Some((Some(vals.into()), cost))
                    }
                }
                _ => {
                    let (_val, cost) = self.exec_expr(p[ip])?;
                    let (val, ncost) = self.run(ip + 1)?;

                    Some((val, cost + ncost))
                }
            }
        }
    }

    /// Executes an expression.
    fn exec_expr(&mut self, expr: ExprIx) -> Option<(Option<Value>, usize)> {
        // TODO: yikes! cloning!
        match &self.arena.exprs[expr] {
            // At this point, assume is_bind = false
            Expr::Singleton(i) => {
                // Execute inner item
                // Then wrap in vector and return that value
                let (v, cost) = self.exec_expr(*i)?;
                Some((Some(vec![v?].into()), cost))
            }
            Expr::Assign(x, e, _) => {
                // Evaluate rhs
                let (rhs, cost) = self.exec_expr(*e)?;

                // Push assignment.
                self.push_var(*x, rhs?);
                Some((None, cost))
            }
            Expr::Var(v) => {
                // Get var
                self.env.get(&v).map(|x| (Some(x.clone()), 1))
            }
            Expr::Proj(x, v) => {
                let (x, mut cost) = self.exec_expr(*x)?;
                let mut x = x?;
                for path in self.arena.get_str(v).split('.') {
                    x = x.get(path)?.clone();
                    cost += 1;
                }

                Some((Some(x), cost))
            }
            Expr::App(f, args) => {
                let argvs = args
                    .iter()
                    .map(|(_, arg)| self.exec_expr(*arg))
                    .collect::<Option<Vec<_>>>()?;
                let scores: usize = argvs.iter().map(|x| x.1).sum();
                let vals = argvs.into_iter().map(|x| x.0).collect::<Option<Vec<_>>>()?;
                let args: Vec<Spur> =
                    args.iter().map(|x| x.0).collect();

                let val = self.arena.get_trace(*f, args, vals)?;

                Some((Some(val), 1 + scores))
            }
            Expr::Filter(obj, f, val) => {
                // Execute obj and val.
                let (obj, score1) = self.exec_expr(*obj)?;
                let (val, score2) = self.exec_expr(*val)?;

                let mut tmp = obj.clone()?;

                for path in self.arena.get_str(f).split('.') {
                    tmp = tmp.get(path)?.clone();
                }

                if tmp == val? {
                    // TODO: variables??
                    Some((obj, score1 + score2 + 1))
                } else {
                    None
                }
            }
        }
    }

    fn push_var(&mut self, x: Spur, v: Value) {
        self.env.insert(x, v);
    }

    fn pop_var(&mut self, x: Spur) {
        self.env.remove(&x);
    }
}

#[derive(Debug)]
enum RWRodeo<T> {
    Write(Rodeo<T>),
    Read(RodeoResolver<T>),
}

/// An `Arena` handles the allocated data needed for an RE pass:
/// the list of `Expr`s, the list of trace entries, and the
/// `rodeo::Rodeo` which holds interned strings. It also provides
/// methods for allocating expressions and trace entries and all
/// that.
#[derive(Debug)]
pub struct Arena {
    exprs: Vec<Expr>,
    traces: Traces,
    progs: Vec<Prog>,
    strs: RWRodeo<Spur>,
}

impl Default for Arena {
    fn default() -> Self {
        Self {
            exprs: vec![],
            traces: Traces::new(),
            progs: vec![],
            strs: RWRodeo::Write(Rodeo::default()),
        }
    }
}

impl Arena {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn alloc_expr(&mut self, e: Expr) -> ExprIx {
        self.exprs.push(e);
        self.exprs.len() - 1
    }

    pub fn push_prog(&mut self, prog: Prog) -> ProgIx {
        self.progs.push(prog);
        self.progs.len() - 1
    }

    pub fn push_trace(&mut self, f: Spur, args: Vec<Spur>, vals: Vec<(Vec<Value>, Value, usize)>) {
        self.traces.insert((f, args), vals);
    }

    fn get_trace(&self, f: Spur, args: Vec<Spur>, vals: Vec<Value>) -> Option<Value> {
        // To get a trace, we just get it from our traces map
        let possibles = self.traces.get(&(f, args))?;

        let (responses, weights): (Vec<&Value>, Vec<usize>) = possibles
            .iter()
            .filter_map(|x| if vals == x.0 { Some((&x.1, x.2)) } else { None })
            .unzip();

        if !responses.is_empty() {
            let dist = WeightedIndex::new(&weights).unwrap();
            let mut rng = thread_rng();
            Some(responses[dist.sample(&mut rng)].clone())
        } else {
            None
        }
    }

    pub fn intern_str(&mut self, s: &str) -> Spur {
        match &mut self.strs {
            RWRodeo::Write(r) => r.get_or_intern(s),
            RWRodeo::Read(_) => panic!("can't write, haven't switched rodeos!"),
        }
    }

    pub fn get_str(&self, s: &Spur) -> &str {
        match &self.strs {
            RWRodeo::Read(r) => r.resolve(s),
            RWRodeo::Write(_) => panic!("can't read, haven't switched rodeos!"),
        }
    }

    // TODO: Add some type safety? some state machine stuff
    // Arena<Write> -> Arena<Read>, different impls on each
    // or even separate types: WriteArena -> ReadArena, where the strs type
    // changes across each
    pub fn swap_rodeo(mut self) -> Self {
        self.strs = match self.strs {
            RWRodeo::Write(r) => RWRodeo::Read(r.into_resolver()),
            x => x,
        };

        self
    }
}
