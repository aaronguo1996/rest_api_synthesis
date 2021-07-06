use lasso::MiniSpur;
use smallvec::SmallVec;

/// An index to access an `Expr` in an allocated vector.
pub type ExprIx = usize;

/// An `Expr` is an expression that will be evaluated in retrospective
/// execution. `Expr`s are translated from the Python representation of
/// Programs, and are allocated in a contiguous vector/slab.
#[derive(Debug, Clone)]
pub enum Expr {
    Var(MiniSpur),
    Assign(MiniSpur),
    Proj(MiniSpur),
    Singleton,
    Ret,

    // Filtering
    Filter,
    SetCandidates,

    // Function application
    App(u16),
    Push(MiniSpur),

    // Handling binds
    Bind(MiniSpur),
}

/// An index to access a `Prog` in an allocated vector.
pub type ProgIx = usize;

/// A program, containing a list of inputs, the start of the program, and the end of the program.
#[derive(Debug)]
pub struct Prog {
    pub inputs: SmallVec<[MiniSpur; 4]>,
    pub start: ExprIx,
    pub end: ExprIx,
}
