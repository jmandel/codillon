;; prove-explain: the kernel finds this proof itself; no `prove` line is needed.
;; (x·2)&1 is always 0, so i32.eqz is always 1 and br_if 0 always exits.
;; On the fall-through the lane holds the fact "(x·2)&1 ≠ 0", which is false,
;; so unreachable's cup (False) is fed from it: the facts contradict each other,
;; and the lines after br_if never run.
(func $f (param $x i32)
  local.get $x
  i32.const 2
  i32.mul
  i32.const 1
  i32.and
  i32.eqz
  br_if 0
  unreachable
)
