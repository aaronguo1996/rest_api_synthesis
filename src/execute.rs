use crate::{Expr, ExprIx, Prog, ProgIx, Traces};
use hashbrown::HashMap;
use lasso::{Key, MiniSpur, Rodeo, RodeoResolver};
use rand::{distributions::WeightedIndex, prelude::*, seq::SliceRandom};
use rayon::prelude::*;
use serde_json::Value;
use smallvec::SmallVec;
use std::convert::TryInto;

pub type Cost = usize;

/// A `Runner` is responsible for coordinating the whole RE process.
/// It first loads all of the traces and translates all of the expressions.
/// It then runs RE in a multithreaded fashion.
pub struct Runner {
    arena: Arena,
    /// A list of programs stored in the `arena`.
    progs: Vec<Prog>,
}

impl Runner {
    pub fn new(mut arena: Arena, progs: Vec<Prog>) -> Self {
        // Swap arena into read-only mode
        arena = arena.swap_rodeo();

        Self { arena, progs }
    }

    /// Runs retrospective execution over a set of inputs.
    /// inputs is a map from an input argument name to a list of possible
    /// values for that input.
    pub fn run(self, inputs: &[(MiniSpur, Vec<Value>)]) -> Vec<(ProgIx, Cost)> {
        let mut res = Vec::with_capacity(self.progs.len());
        // let res;

        // TODO: profile loop order
        // For each program, generate a few random vals and execute
        self.progs
            .par_iter()
            .enumerate()
            .map(|(ix, prog)| {
                // res = self.progs.iter().enumerate().map(|(ix, prog)| {
                let costs: Vec<Cost> = (0..5)
                    .map(|_i| {
                        // (0..5).into_par_iter().map(|_i| {
                        let mut env = HashMap::new();

                        // Choose random values for our inputs
                        let mut rng = thread_rng();
                        for (input_name, input_vals) in inputs {
                            env.insert(*input_name, input_vals.choose(&mut rng).unwrap().clone());
                        }

                        // Make a new execution environment
                        let mut ex = ExecEnv::new(&self.arena, prog.start, prog.end, env);

                        // TODO: do analysis on result value
                        let out = ex.run();
                        // TODO
                        let (_res, cost) = out.unwrap_or_else(|| (None, 99999));
                        cost
                    })
                    .collect();
                // }).collect_into_vec(&mut costs);

                (ix, costs.iter().sum::<Cost>() / costs.len())
            })
            .collect_into_vec(&mut res);
        // }).collect();

        res
    }
}

#[derive(Debug, Copy, Clone)]
pub struct Frame {
    /// The index of the vector on the stack.
    pub stack_ix: usize,
    /// The instruction to jump to in order to get to the start of the loop.
    pub jump: usize,
    /// The current loop index.
    pub cur: usize,
    /// The loop length.
    pub len: usize,
    /// The bound variable for this loop.
    pub bound: MiniSpur,
    /// The cost before this loop began.
    pub cost: Cost,
}

/// An `ExecEnv` is an execution environment, holding all the information
/// needed for the execution of one expression on one input.
///
/// Execution is implemented as a state machine which interprets the program.
pub struct ExecEnv<'a> {
    // invocation params
    arena: &'a Arena,
    ret: ExprIx,

    // mutating state
    ip: ExprIx,
    tip: ExprIx,
    cost: usize,
    error: bool,
    env: HashMap<MiniSpur, Value>,
    data: Vec<Value>,
    call: Vec<Frame>,
}

impl<'a> ExecEnv<'a> {
    pub fn new(
        arena: &'a Arena,
        start: ExprIx,
        ret: ExprIx,
        env: HashMap<MiniSpur, Value>,
    ) -> Self {
        Self {
            arena,
            ret,

            ip: start,
            tip: 0,
            error: false,
            env,
            cost: 0,
            data: vec![],
            call: vec![],
        }
    }

    // TODO: deal with clones. probably some Cow stuff
    pub fn run(&mut self) -> Option<(Option<Value>, Cost)> {
        loop {
            // println!("{} {:?} {} tip: {}", self.ip, &self.arena.exprs[self.ip], self.data.len(), self.tip);
            // Get the current instruction
            match &self.arena.exprs[self.ip] {
                // At this point, assume is_bind = false
                Expr::Singleton => {
                    // Set top element of stack to list.
                    let l = self.data.last_mut()?;
                    *l = Value::Array(vec![l.clone()]);

                    self.ip += 1;
                }
                Expr::Var(v) => {
                    // Get var out of heap and push to stack.
                    self.data.push(self.env.get(v)?.clone());

                    self.cost += 1;
                    self.ip += 1;
                }
                Expr::Assign(v) => {
                    let top = self.data.pop()?;
                    self.env.insert(*v, top);

                    self.ip += 1;
                }
                Expr::Filter(f) => {
                    // filter(lhs.f == rhs)
                    // Pop rhs and lhs off the stack.
                    let rhs = self.data.pop()?;
                    let lhs = self.data.pop()?;

                    // Filter. if lhs.v == rhs, we good.
                    let mut tmp = &lhs;
                    for path in self.arena.get_str(f).split('.') {
                        if let Some(p) = tmp.get(path) {
                            tmp = p;
                        } else {
                            self.set_error();
                        }
                    }

                    if tmp == &rhs {
                        // TODO: variables??
                        // Filter doesn't push anything to the stack

                        self.cost += 1;
                        self.ip += 1;
                    } else {
                        self.set_error();
                    }
                }
                Expr::Proj(f) => {
                    // Pop from top of stack, project into it, push.
                    let x = self.data.pop()?;
                    let mut tmp = &x;
                    for path in self.arena.get_str(f).split('.') {
                        tmp = tmp.get(path)?;
                        self.cost += 1;
                    }
                    self.data.push(tmp.clone());

                    self.ip += 1;
                }
                Expr::Bind(v) => {
                    // First, peek at top of stack.
                    let x = self.data.last()?.as_array()?;

                    // If x is empty, error.
                    if x.is_empty() {
                        self.set_error();
                    } else {
                        // Push to call stack.
                        self.call.push(Frame {
                            stack_ix: self.data.len() - 1,
                            jump: self.ip + 1,
                            cur: 0,
                            len: x.len(),
                            bound: *v,
                            cost: self.cost,
                        });

                        // Reset cost for loop.
                        self.cost = 0;

                        // Push x[0] to env.
                        self.env.insert(*v, x.get(0).unwrap().clone());

                        // Set tip to error recovery spot; the last place with
                        // a valid data val.
                        self.tip = self.data.len() - 1;

                        self.ip += 1;
                    }
                }
                Expr::App(n) => {
                    // When we call App, the stack will look like this:
                    // arg_1 name_1 ... arg_n name_n fun_name
                    //                               ^ top
                    let n = (*n).try_into().unwrap();
                    let fun = {
                        let num: usize = self.data.pop()?.as_i64()?.try_into().ok()?;

                        MiniSpur::try_from_usize(num)?
                    };
                    let mut names: SmallVec<[MiniSpur; 8]> = SmallVec::with_capacity(n);
                    let mut vals: SmallVec<[Value; 8]> = SmallVec::with_capacity(n);

                    for _i in 0..n {
                        let name = {
                            let num: usize = self.data.pop()?.as_i64()?.try_into().ok()?;

                            MiniSpur::try_from_usize(num)?
                        };
                        let val = self.data.pop()?;

                        // Insert in sorted order of the param name
                        match names.binary_search(&name) {
                            Ok(_pos) => unreachable!(),
                            Err(pos) => {
                                names.insert(pos, name);
                                vals.insert(pos, val);
                            }
                        };
                    }

                    // Finally, actually call function :)
                    if let Some(t) = self.arena.get_trace(fun, names, vals) {
                        self.data.push(t);
                        self.ip += 1;
                    } else {
                        self.set_error();
                    }
                }
                Expr::Push(s) => {
                    // We push a MiniSpur by pushing a usize number to the stack
                    self.data.push(s.into_usize().into());

                    self.ip += 1;
                }
                Expr::Ret => loop {
                    // h o o h b o y
                    // First, we try to peek at the top of the call stack.
                    if let Some(Frame {
                        stack_ix,
                        jump,
                        mut cur,
                        len,
                        bound,
                        cost,
                    }) = self.call.pop()
                    {
                        // Increment cur.
                        cur += 1;

                        // println!("{} {}", self.error, self.tip);

                        // If error, clear stack until tip element, reset cost, and unset error state.
                        if self.error {
                            self.data.truncate(self.tip + 1);
                            self.unset_error();
                            self.cost = 0;
                        } else {
                            // Otherwise, push the current cost to the top of the stack, then
                            // reset.
                            self.data.push(self.cost.into());
                            self.cost = 0;

                            // println!("pushed data and cost");
                        }

                        // If third and fourth elements aren't equal, jump back to
                        // jump, reset tip, and try again.
                        if cur < len {
                            self.ip = jump;
                            self.tip = self.data.len() - 1;

                            // Also, reset bound var.
                            // println!("{} {} {:?}", cur, len, self.data.len());
                            self.push_var(
                                bound,
                                self.data[stack_ix]
                                    .as_array()
                                    .unwrap()
                                    .get(cur)
                                    .unwrap()
                                    .clone(),
                            );

                            // TODO: try using last_mut instead of popping and repushing
                            // Repush to the call stack
                            self.call.push(Frame {
                                stack_ix,
                                jump,
                                cur,
                                len,
                                bound,
                                cost,
                            });
                            break;
                        } else {
                            // println!("stack_ix {}", stack_ix);
                            // Unset bound var.
                            self.pop_var(bound);

                            // TODO: doing this "throw everything on the stack until
                            // stack_ix" method won't work if we move env items also
                            // to the stack.
                            let mut pairs = self.data.drain(stack_ix + 1..).collect::<Vec<_>>();

                            if pairs.is_empty() {
                                // If we have an empty vector, pop the top element off (it's the
                                // vector that we bound and left on the stack) and set the error flag.
                                self.data.pop()?;
                                self.set_error();
                            } else {
                                // Otherwise, push the vec to the stack. In the next iter
                                // of the loop, we try again :)

                                // pairs will be in the form:
                                // expr1 cost1 .. exprn costn
                                // println!("{:?}", &pairs);
                                let costs = pairs
                                    .drain_filter(|x| x.is_number())
                                    .map(|x| x.as_i64().unwrap().try_into().unwrap())
                                    .collect::<Vec<Cost>>();
                                let res = pairs;

                                // Then pop the next element off - it's the vector that we
                                // left on the stack so we could reference.
                                self.data.pop()?;

                                // Set cost
                                let bind_cost: Cost = costs.iter().sum::<Cost>() / costs.len();
                                self.cost = cost + bind_cost;

                                // Push list to stack and loop again!
                                self.data.push(res.into());
                            }

                            // Set tip to top of stack
                            self.tip = self.data.len() - 1;
                        }
                    } else {
                        if self.error {
                            // In the error case, return None.
                            return None;
                        } else {
                            // Otherwise, return the top of the data stack.
                            return Some((self.data.pop(), self.cost));
                        }
                    }
                },
            }
        }
    }

    pub fn set_error(&mut self) {
        self.error = true;
        self.ip = self.ret;
    }

    pub fn unset_error(&mut self) {
        self.error = false;
    }

    fn push_var(&mut self, x: MiniSpur, v: Value) {
        self.env.insert(x, v);
    }

    fn pop_var(&mut self, x: MiniSpur) {
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
    strs: RWRodeo<MiniSpur>,
}

impl Default for Arena {
    fn default() -> Self {
        Self {
            exprs: vec![],
            traces: Traces::new(),
            strs: RWRodeo::Write(Rodeo::new()),
        }
    }
}

impl Arena {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn get_next_prog_ix(&self) -> ExprIx {
        self.exprs.len()
    }

    pub fn alloc_expr(&mut self, e: Expr) -> ExprIx {
        self.exprs.push(e);
        self.exprs.len() - 1
    }

    pub fn push_trace(
        &mut self,
        f: MiniSpur,
        args: SmallVec<[MiniSpur; 8]>,
        vals: Vec<(HashMap<MiniSpur, Value>, Value, usize)>,
    ) {
        self.traces.insert((f, args), vals);
    }

    fn get_trace(
        &self,
        f: MiniSpur,
        args: SmallVec<[MiniSpur; 8]>,
        vals: SmallVec<[Value; 8]>,
    ) -> Option<Value> {
        // TODO: clone :/
        // To get a trace, we just get it from our traces map
        let possibles = self.traces.get(&(f, args.clone()))?;

        let (responses, weights): (Vec<&Value>, Vec<usize>) = possibles
            .iter()
            .filter_map(|x| {
                if args
                    .iter()
                    .enumerate()
                    .all(|(i, a)| x.0.get(a) == Some(vals.get(i).unwrap()))
                {
                    Some((&x.1, x.2))
                } else {
                    None
                }
            })
            .unzip();

        if !responses.is_empty() {
            let dist = WeightedIndex::new(&weights).unwrap();
            let mut rng = thread_rng();
            Some(responses[dist.sample(&mut rng)].clone())
        } else {
            None
        }
    }

    pub fn intern_str(&mut self, s: &str) -> MiniSpur {
        match &mut self.strs {
            RWRodeo::Write(r) => r.get_or_intern(s),
            RWRodeo::Read(_) => panic!("can't write, haven't switched rodeos!"),
        }
    }

    pub fn get_str(&self, s: &MiniSpur) -> &str {
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

    pub fn rodeo_len(&self) -> usize {
        match &self.strs {
            RWRodeo::Read(r) => r.len(),
            RWRodeo::Write(w) => w.len(),
        }
    }
}
