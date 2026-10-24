// Z3 Web Worker (module worker). No SharedArrayBuffer / COOP / COEP needed.
//   const w = new Worker(new URL('./z3w-worker.js', import.meta.url), { type: 'module' });
//   w.postMessage({ id: 1, smtlib: '(declare-const x Int)(assert (> x 1))(check-sat)(get-model)' });
//   w.onmessage = (e) => { const { id, output, ms } = e.data; ... };
// Protocol:
//   in : { id, smtlib }              -> out: { id, output, ms }   (output starts with "error:" on failure)
//   in : { id, reset: true }         -> out: { id, output: '', ms }   (fresh context)
//   out (once, unsolicited at startup): { ready: true, ms, version, crossOriginIsolated }
// Each request runs on one persistent context, so declarations and (push)/(pop) scopes
// carry over between requests until reset. Requests are processed strictly in order.
import { Z3W } from './z3w.js';

let z3 = null;
const t0 = performance.now();
const ready = Z3W.create().then((inst) => {
  z3 = inst;
  self.postMessage({ ready: true, ms: performance.now() - t0, version: inst.version,
                     crossOriginIsolated: self.crossOriginIsolated === true });
}, (err) => {
  self.postMessage({ ready: false, error: String(err && err.message || err) });
});

let queue = Promise.resolve();
self.onmessage = (e) => {
  const msg = e.data || {};
  queue = queue.then(() => ready).then(async () => {
    const s = performance.now();
    let output;
    try {
      if (!z3) throw new Error('z3 failed to load');
      if (msg.reset) { z3.reset(); output = ''; }
      else output = z3.eval(String(msg.smtlib ?? ''));
    } catch (err) {
      // A wasm trap (e.g. stack overflow, OOM abort) leaves the instance unusable: rebuild it.
      output = 'error:' + String(err && err.message || err);
      try { z3 = await Z3W.create(); } catch { z3 = null; }
    }
    self.postMessage({ id: msg.id, output, ms: performance.now() - s });
  });
};
