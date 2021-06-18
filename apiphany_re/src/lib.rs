//! Retrospective execution, reimplemented in Rust.
//!
//! This library implements the retrospective execution portion of apiphany in
//! Rust to maximize performance.

mod execute;
mod expr;
mod interop;
mod trace;

pub use execute::{Runner, Arena};
pub use expr::{Expr, ExprIx, Prog, ProgIx};
pub use trace::{Param, ParamVec, Trace, TraceVec, Method};
