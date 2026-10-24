# Z3 for the browser (vendored)

`z3w.wasm`, `z3w.js` and `z3w-worker.js` are Z3 5.3.1 (commit
ac9156f97cb44e56472e1c841f7a2beb1e976b24), compiled to WebAssembly without threads, so
they need no SharedArrayBuffer and no cross-origin isolation. Z3 is copyright Microsoft
Corporation and is distributed under the MIT license (https://github.com/Z3Prover/z3).

Codillon loads the worker the first time a program with specifications needs a proof
(src/prover.rs). The worker takes SMT-LIB text and returns Z3's output, and each query
is bounded by `(set-option :rlimit N)`.
