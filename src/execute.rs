use crate::{Expr, ExprIx, Prog, ProgIx, RValue, RootSlab, ThreadSlab, Traces, ValueIx};
use hashbrown::HashMap;
use lasso::{MiniSpur, Rodeo, RodeoResolver};
use nanorand::{tls_rng, RNG};
use rand::distributions::WeightedIndex;
use rand::prelude::*;
use rayon::prelude::*;
use smallvec::{smallvec, SmallVec};
use std::convert::TryInto;

pub type Cost = usize;

/// A `Runner` is responsible for coordinating the whole RE process.
/// It first loads all of the traces and translates all of the expressions.
/// It then runs RE in a multithreaded fashion.
pub struct Runner {
    arena: Arena,
    /// A list of programs stored in the `arena`.
    progs: Vec<Prog>,
    default_inputs: HashMap<MiniSpur, Vec<ValueIx>>,
}

impl Runner {
    pub fn new(
        mut arena: Arena,
        progs: Vec<Prog>,
        default_inputs: HashMap<MiniSpur, Vec<ValueIx>>,
    ) -> Self {
        // Swap arena into read-only mode
        arena = arena.swap_rodeo();

        Self {
            arena,
            progs,
            default_inputs,
        }
    }

    /// Runs retrospective execution over a set of inputs.
    /// inputs is a map from an input argument name to a list of possible
    /// values for that input.
    pub fn run(
        self,
        target_ix: ProgIx,
        multiple: bool,
        slab: &RootSlab,
        filter_num: usize,
        repeat: usize,
    ) -> Vec<usize> {
        // Not sure why the list of input solutions would be empty but
        // Apparently it happens lol
        if self.progs.is_empty() {
            return vec![];
        }

        let mut avgs: Vec<usize> = (0..filter_num)
            .into_par_iter()
            .map(|_exp| {
                let mut res = Vec::with_capacity(self.progs.len());
                // let res;

                self.progs
                    .par_iter()
                    .enumerate()
                    .map(|(ix, prog)| {
                        let mut all_none = true;
                        let mut all_singleton = true;
                        let mut all_multiple = true;
                        let mut all_empty = true;

                        let mut costs: Vec<Cost> = Vec::with_capacity(repeat);
                        let mut t = ThreadSlab::new(slab);
                        for _rep in 0..repeat {
                            // Make a new execution environment
                            let mut ex = ExecEnv::new(
                                &self.arena,
                                prog.start,
                                prog.end,
                                &self.default_inputs,
                            );

                            // Run RE!
                            let (result, cost) = ex.run(&mut t).unwrap_or_else(|| (None, 99999));

                            if let Some(r) = result {
                                all_none = false;

                                if !(t.get(r).unwrap().is_empty()) {
                                    all_empty = false;
                                }

                                let mut rr = t.get(r).unwrap();

                                while let Some(ra) = rr.as_array() {
                                    if ra.len() == 1 {
                                        rr = t.get(ra[0]).unwrap();
                                    } else {
                                        break;
                                    }
                                }

                                if rr.is_array() && rr.as_array().unwrap().len() > 1 {
                                    all_singleton = false;
                                } else {
                                    all_multiple = false;
                                }

                                costs.push(cost);
                            }

                            t.clear();
                        }

                        // println!("overall slab size: {}", slab.data.len());
                        // println!("thread slab size: {}", t.data.len());

                        if all_none {
                            return (ix, 99999);
                        }

                        let mut cost_avg = costs.iter().sum::<Cost>() / costs.len();

                        if all_singleton && multiple {
                            cost_avg += 25;
                        } else if all_multiple && !multiple {
                            cost_avg += 50;
                        }

                        if all_empty {
                            cost_avg += 10;
                        }

                        // println!("{}", cost_avg);

                        (ix, cost_avg)
                    })
                    .collect_into_vec(&mut res);

                let tgt_cost = res.get(target_ix).unwrap().1;

                // Sort the result by cost and get the cost of the target ix
                res.sort_by_key(|x| x.1);

                // println!("min (rank 1): {:?}", &res[0..20]);
                (
                    tgt_cost,
                    res.iter().position(|x| x.1 == tgt_cost).unwrap() + 1,
                )
            })
            // .filter(|x| x.0 < 99999)
            .map(|x| x.1)
            .collect();

        avgs.sort();
        avgs
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
    default_inputs: &'a HashMap<MiniSpur, Vec<ValueIx>>,
    ret: ExprIx,

    // mutating state

    // Pointers
    ip: ExprIx,
    tip: ExprIx,

    // cost
    cost: usize,

    // state flags
    candidates: bool,
    error: bool,

    // env
    env: HashMap<MiniSpur, ValueIx>,

    // stacks
    data: Vec<ValueIx>,
    call: Vec<Frame>,
}

impl<'a> ExecEnv<'a> {
    pub fn new(
        arena: &'a Arena,
        start: ExprIx,
        ret: ExprIx,
        default_inputs: &'a HashMap<MiniSpur, Vec<ValueIx>>,
    ) -> Self {
        Self {
            arena,
            default_inputs,
            ret,

            ip: start,
            tip: 0,
            error: false,
            candidates: false,
            env: HashMap::new(),
            cost: 0,
            data: Vec::with_capacity(8),
            call: Vec::with_capacity(8),
        }
    }

    pub fn run(&mut self, heap: &mut ThreadSlab) -> Option<(Option<ValueIx>, Cost)> {
        'outer: loop {
            // println!(
            //     "{} {:?} err: {} stack: {} tip: {} cost: {}",
            //     self.ip,
            //     &self.arena.exprs[self.ip],
            //     self.error,
            //     self.data.len(),
            //     self.tip,
            //     self.cost
            // );
            // Get the current instruction
            match &self.arena.exprs[self.ip] {
                // At this point, assume is_bind = false
                Expr::Singleton => {
                    // Set top element of stack to list.
                    let l = self.data.pop()?;
                    let v = heap.push_rval(RValue::Array(smallvec![l]));
                    self.data.push(v);

                    self.ip += 1;
                }
                Expr::Var(v) => {
                    // Get var out of heap and push to stack.
                    let v = if let Some(val) = self.env.get(v) {
                        *val
                    } else {
                        // If we're trying to reference an undefined variable, it must
                        // be an input value.

                        // If self.candidates has been set, use the top of the stack
                        // to populate this variable. Otherwise, use the default inputs.
                        if self.candidates {
                            let last = self.data.last()?;
                            if let Some(choices) = heap.get(*last).unwrap().as_array() {
                                // Choose one of these values for our input
                                // TODO: flatten list
                                let mut rng = tls_rng();
                                let choice = choices[rng.generate_range(0, choices.len() - 1)];
                                self.env.insert(*v, choice);

                                choice
                            } else {
                                self.env.insert(*v, *last);

                                *last
                            }
                        } else {
                            // Choose random values for our input
                            let mut rng = tls_rng();
                            let choices = self.default_inputs.get(v)?;

                            // Check that we have choices lmao
                            if choices.is_empty() {
                                return None;
                            }

                            let choice = choices[rng.generate_range(0, choices.len() - 1)];
                            self.env.insert(*v, choice);

                            choice
                        }
                    };

                    self.data.push(v);

                    // self.cost += 1;
                    self.ip += 1;
                }
                Expr::SetCandidates => {
                    self.candidates = true;

                    self.ip += 1;
                }
                Expr::Assign(v) => {
                    let top = self.data.pop()?;
                    self.env.insert(*v, top);

                    self.ip += 1;
                }
                Expr::Filter => {
                    // when we translated the filter, the lhs already has the
                    // projection. so we just check if lhs == rhs.
                    // Pop rhs and lhs off the stack.
                    let rhs = self.data.pop()?;
                    let lhs = self.data.pop()?;

                    // Reset candidates flag.
                    self.candidates = false;

                    if heap.get(lhs)?.deep_eq(heap.get(rhs)?, &heap) {
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
                    let mut tmp = (x, heap.get(x)?);

                    for path in self.arena.get_str(f).split('.') {
                        // println!("{:?}", tmp);

                        if let Some(v) = tmp.1.get(path, &heap) {
                            tmp = v;
                            self.cost += 1;
                        } else {
                            self.set_error();
                            continue 'outer;
                        }
                    }

                    if let RValue::Null = tmp.1 {
                        self.set_error();
                        continue 'outer;
                    }

                    // println!("{:?}", tmp);
                    self.data.push(tmp.0);

                    self.ip += 1;
                }
                Expr::Bind(v) => {
                    // First, peek at top of stack.
                    let (id, x) = {
                        let (id, v) = heap.get_mut(self.data.pop()?)?;
                        (id, v.as_mut_array()?)
                    };

                    let mut rng = thread_rng();
                    x.shuffle(&mut rng);

                    // If x is empty, error.
                    if x.is_empty() {
                        self.set_error();
                    } else {
                        self.data.push(id);

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
                        self.env.insert(*v, *x.get(0).unwrap());

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
                    let fun = heap.get(self.data.pop()?)?.as_symbol()?;
                    let mut names: SmallVec<[MiniSpur; 8]> = SmallVec::with_capacity(n);
                    let mut vals: SmallVec<[ValueIx; 8]> = SmallVec::with_capacity(n);

                    for _i in 0..n {
                        let name = heap.get(self.data.pop()?)?.as_symbol()?;
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
                    // println!(
                    //     "call: {:?}\nnames: {:?}\nvals: {:?}",
                    //     self.arena.get_str(&fun),
                    //     names
                    //         .iter()
                    //         .map(|x| self.arena.get_str(x))
                    //         .collect::<Vec<_>>(),
                    //     vals
                    // );
                    if let Some(t) = self.arena.get_trace(fun, names, vals) {
                        self.data.push(t);

                        self.cost += 1;
                        self.ip += 1;
                    } else {
                        self.set_error();
                    }
                }
                Expr::Push(s) => {
                    // We push a MiniSpur by pushing a usize number to the stack
                    self.data.push(heap.push_rval(RValue::Symbol(*s)));

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
                        // println!("there exists a frame!");
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
                            self.data.push(heap.push_rval(RValue::Num(self.cost)));
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
                                *heap
                                    .get(self.data[stack_ix])
                                    .unwrap()
                                    .as_array()
                                    .unwrap()
                                    .get(cur)
                                    .unwrap(),
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
                                    .drain_filter(|x| heap.get(*x).unwrap().is_num())
                                    .map(|x| heap.get(x).unwrap().as_num().unwrap())
                                    .collect::<Vec<Cost>>();
                                let res = pairs;

                                // Then pop the next element off - it's the vector that we
                                // left on the stack so we could reference.
                                self.data.pop()?;

                                // Set cost
                                let bind_cost: Cost = costs.iter().sum::<Cost>() / costs.len();
                                self.cost = cost + bind_cost;

                                // Push list to stack and loop again!
                                self.data.push(heap.push_rval(RValue::Array(res.into())));
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

    fn push_var(&mut self, x: MiniSpur, v: ValueIx) {
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

impl Arena {
    pub fn new() -> Self {
        Self {
            exprs: Vec::new(),
            traces: Traces::new(),
            strs: RWRodeo::Write(Rodeo::new()),
        }
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
        vals: Vec<(HashMap<MiniSpur, ValueIx>, ValueIx, usize)>,
    ) {
        self.traces.insert((f, args), vals);
    }

    fn get_trace(
        &self,
        f: MiniSpur,
        args: SmallVec<[MiniSpur; 8]>,
        vals: SmallVec<[ValueIx; 8]>,
    ) -> Option<ValueIx> {
        // TODO: clone :/
        // To get a trace, we just get it from our traces map
        let possibles = self.traces.get(&(f, args.clone()))?;

        let (responses, weights): (Vec<ValueIx>, Vec<usize>) = {
            let mut value_filter = possibles
                .iter()
                .filter_map(|x| {
                    if args
                        .iter()
                        .enumerate()
                        .all(|(i, a)| x.0.get(a) == Some(vals.get(i).unwrap()))
                    {
                        Some((x.1, x.2))
                    } else {
                        None
                    }
                })
                .peekable();

            // We try to peek at the iterator. If it's None, this means
            // nothing matches, and we should just use possibles as a
            // backup.
            if let Some(_) = value_filter.peek() {
                value_filter.unzip()
            } else {
                possibles.iter().map(|x| (&x.1, x.2)).unzip()
            }
        };

        if !responses.is_empty() {
            let dist = WeightedIndex::new(&weights).unwrap();
            let mut rng = thread_rng();
            Some(responses[dist.sample(&mut rng)])

            // Some(responses[weighted_choice(&weights)])
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

// fn choice(weights: &[usize]) -> usize {
//     let mut rng = tls_rng();
//     rng.generate_range(0, weights.len())
// }

// fn weighted_choice(weights: &[usize]) -> usize {
//     let mut rng = tls_rng();
//     let cumulative = weights
//         .iter()
//         .scan(0, |state, &x| {
//             *state = *state + x;
//             Some(*state)
//         })
//         .collect::<SmallVec<[usize; 16]>>();
//     let last = cumulative[cumulative.len() - 1];
//
//     let target = rng.generate_range(0, last);
//
//     match cumulative.binary_search(&target) {
//         Ok(i) => i,
//         Err(i) => i,
//     }
// }

// fn weighted_choice(weights: &[usize]) -> usize {
//     let n = weights.len();
//     let avg = weights.iter().sum::<usize>() / n;
//
//     let mut smalls: SmallVec<[(usize, usize); 16]> = weights
//         .iter()
//         .copied()
//         .enumerate()
//         .filter(|(_, w)| *w < avg)
//         .collect();
//     let mut larges: SmallVec<[(usize, usize); 16]> = weights
//         .iter()
//         .copied()
//         .enumerate()
//         .filter(|(_, w)| *w >= avg)
//         .collect();
//
//     let mut aliases: SmallVec<[(usize, usize); 16]> = smallvec::smallvec![(0, 0); n];
//
//     let mut small = smalls.pop();
//     let mut large = larges.pop();
//
//     while let (Some(s), Some(mut l)) = (small, large) {
//         aliases[s.0] = (s.1, l.0);
//         l = (l.0, l.1 - (avg - s.1));
//         if l.1 < avg {
//             small = Some(l);
//             large = larges.pop();
//         } else {
//             small = smalls.pop();
//             large = Some(l);
//         }
//     }
//
//     while let Some(s) = small {
//         aliases[s.0] = (avg, 0);
//         small = smalls.pop();
//     }
//
//     while let Some(l) = large {
//         aliases[l.0] = (n, 0);
//         large = larges.pop();
//     }
//
//     // Actually choose!
//     let mut rng = tls_rng();
//     let r2 = rng.generate_range(0, avg);
//     let r1 = r2 * n / avg;
//     // let r1 = rng.generate_range(0, n);
//
//     let (lim, other) = aliases[r1];
//     if r1 < lim {
//         // if r2 < lim {
//         r1
//     } else {
//         other
//     }
// }
