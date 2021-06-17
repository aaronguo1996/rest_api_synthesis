use crate::{Expr, ExprIx, TraceVec, Prog, ProgIx};
use lasso::{Rodeo, Spur};
use smallvec::SmallVec;

/// A `Runner` is responsible for coordinating the whole RE process.
/// It first loads all of the traces and translates all of the expressions.
/// It then runs RE in a multithreaded fashion.
pub struct Runner {
    arena: Arena,
    /// A list of root programs stored in the `arena`.
    progs: Vec<ProgIx>,
}

impl Runner {
    pub fn new(arena: Arena, progs: Vec<ExprIx>) -> Self {
        Self { arena, progs }
    }
}

/// An `ExecEnv` is an execution environment, holding all the information
/// needed for the execution of one expression on one input.
pub struct ExecEnv<'a> {
    arena: &'a Arena,

    input: (),
    prog: ProgIx,

    // ephemeral state
    cost: usize,
    // TODO: env: HashMap<(), ()>,
}

/// An `Arena` handles the allocated data needed for an RE pass:
/// the list of `Expr`s, the list of trace entries, and the
/// `rodeo::Rodeo` which holds interned strings. It also provides
/// methods for allocating expressions and trace entries and all
/// that.
#[derive(Debug)]
pub struct Arena {
    exprs: Vec<Expr>,
    progs: Vec<Prog>,
    traces: TraceVec,
    strs: Rodeo<Spur>,
}

impl Default for Arena {
    fn default() -> Self {
        Self {
            exprs: vec![],
            progs: vec![],
            traces: TraceVec::new(),
            strs: Rodeo::default(),
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

    pub fn push_prog(&mut self, prog: Prog) -> ExtraIx {
        self.progs.push(prog);
        self.progs.len() - 1
    }

    pub fn intern_str(&mut self, s: &str) -> Spur {
        self.strs.get_or_intern(s)
    }
}
