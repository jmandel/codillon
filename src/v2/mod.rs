//! Refined Codillon v2: proofs as Wasm values, checked by a deterministic kernel (design 16).
//! No SMT: the kernel is lookup, evaluation and a small decision procedure (§3).

pub mod ast;
pub mod erase;
pub mod eval;
pub mod info;
pub mod kernel;
pub mod out;
pub mod sexpr;
pub mod solver;
pub mod symex;
pub mod term;

#[cfg(all(test, not(target_arch = "wasm32")))]
mod tests;
