//! Retrospective execution, reimplemented in Rust.
//!
//! This library implements the retrospective execution portion of apiphany in
//! Rust to maximize performance. 

mod execute;
mod expr;
mod interop;
mod trace;

pub use execute::Arena;
pub use expr::{Expr, ExprIx, ProgIx, Prog};
pub use trace::TraceVec;
