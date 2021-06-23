use lasso::Spur;
use smallvec::SmallVec;

/// An index to access an `Expr` in an allocated vector.
pub type ExprIx = usize;

// TODO: size of instruction is 5 bytes. we waste 3 bytes on alignment.
// Maybe use MiniSpur so we can compress more? But idk if rodeo
// is storing too many strs
// ideally, we'd have first 4 bits for discriminator, last 28 bits for
// the spur, but idk how to do that
/// An `Expr` is an expression that will be evaluated in retrospective
/// execution. `Expr`s are translated from the Python representation of
/// Programs, and are allocated in a contiguous vector/slab.
#[derive(Debug, Clone)]
pub enum Expr {
    Var(Spur),
    Assign(Spur),
    Filter(Spur),
    Proj(Spur),
    Singleton,
    Ret,
    
    // Function application
    App(u32),
    Push(Spur),

    // Handling binds
    Bind(Spur),
}

/// An index to access a `Prog` in an allocated vector.
pub type ProgIx = usize;

/// A program, containing a list of inputs, the start of the program, and the end of the program.
#[derive(Debug)]
pub struct Prog {
    pub inputs: SmallVec<[Spur; 4]>,
    pub start: ExprIx,
    pub end: ExprIx,
}
