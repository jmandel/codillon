;; double-halve: doubling x and halving it gives x back, unless x·2 wraps. i32 arithmetic is modulo 2³², so "(x·2)/2 = x" is false: for x = 2³⁰, x·2 wraps to −2³¹ and the halved value is −2³⁰.
;; $f (line 7) states the false claim: its unreachable (line 16) is not proved, and the kernel shows an input it fails for. $f_fixed (line 18) takes only x in [−2³⁰, 2³⁰), where x·2 cannot wrap, and verifies.
(func $main ;; runs both functions on 21
  i32.const 21
  call $f
  i32.const 21
  call $f_fixed
)
;; the claim, without a precondition: fails for x = 1073741824
(func $f (param $x i32)
  local.get $x
  i32.const 2
  i32.mul
  i32.const 2
  i32.div_s
  local.get $x
  i32.eq
  br_if 0
  unreachable
)
(func $f_fixed (param $x (i32 | (i32.and (i32.lt_s (i32.const -1073741825) v) (i32.lt_s v (i32.const 1073741824)))))
  local.get $x
  i32.const 2
  i32.mul
  i32.const 2
  i32.div_s
  local.get $x
  i32.eq
  br_if 0
  unreachable
)
