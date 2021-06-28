#![feature(drain_filter, iter_order_by)]
//! Retrospective execution, reimplemented in Rust.
//!
//! This library implements the retrospective execution portion of apiphany in
//! Rust to maximize performance.

mod execute;
mod expr;
mod interop;
mod trace;
mod value;

pub use execute::{Arena, Runner};
pub use expr::{Expr, ExprIx, Prog, ProgIx};
pub use trace::Traces;
pub use value::{RValue, RootSlab, ThreadSlab, ValueIx};

pub use interop::apiphany;

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;
