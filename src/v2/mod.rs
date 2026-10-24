//! Refined Codillon v2: proofs as Wasm values, checked by a deterministic kernel (design 16).
//! No SMT: the kernel is lookup, evaluation and a small decision procedure (§3).

pub mod ast;
pub mod erase;
pub mod sexpr;

#[cfg(all(test, not(target_arch = "wasm32")))]
mod tests;
