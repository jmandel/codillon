//! Refined Codillon v2: proofs as Wasm values, checked by a deterministic kernel (design 16).
//! No SMT: the kernel is lookup, evaluation and a small decision procedure (§3).

pub mod adequacy;
pub mod ast;
pub mod erase;
pub mod eval;
pub mod info;
pub mod kernel;
pub mod llm;
pub mod out;
pub mod runtime;
pub mod sexpr;
pub mod solver;
pub mod symex;
pub mod term;
pub mod vericode;

#[cfg(all(test, not(target_arch = "wasm32")))]
mod tests;
#[cfg(all(test, not(target_arch = "wasm32")))]
mod vericode_tests;
#[cfg(all(test, not(target_arch = "wasm32")))]
mod fable_probes;
#[cfg(all(test, not(target_arch = "wasm32")))]
mod review_adv;
#[cfg(all(test, not(target_arch = "wasm32")))]
mod gfix_tests;
