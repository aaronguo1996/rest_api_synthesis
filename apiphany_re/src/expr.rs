use lasso::Spur;
use smallvec::SmallVec;

/// An index to access an `Expr` in an allocated vector.
pub type ExprIx = usize;

/// An `Expr` is an expression that will be evaluated in retrospective
/// execution. `Expr`s are translated from the Python representation of
/// Programs, and are allocated in a contiguous vector/slab; `Expr`s store
/// references to these indices.
#[derive(Debug, Clone)]
pub enum Expr {
    // TODO: memory ://
    App(Spur, SmallVec<[(Spur, ExprIx); 2]>),
    Var(Spur),
    Proj(ExprIx, Spur),
    Filter(ExprIx, Spur, ExprIx),
    Assign(Spur, ExprIx, bool),
}

/// An index to access a `Prog` in an allocated vector.
pub type ProgIx = usize;

/// A program, containing a list of expressions to execute and a list of inputs.
#[derive(Debug)]
pub struct Prog {
    pub inputs: SmallVec<[Spur; 4]>,
    pub exprs: SmallVec<[ExprIx; 8]>,
}
