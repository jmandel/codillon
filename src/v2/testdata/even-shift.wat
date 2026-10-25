;; even-shift: an even number, shifted right by 1 and multiplied by 2, minus the original, is 0.
;; No proof lines: the result cup of each function is fed automatically by the parameter's type.
(func $is_even (param $x i32) (result i32)
  local.get $x
  i32.const 1
  i32.and
  i32.eqz
)
(func $back_u (export "back_u") (param $x (i32 | $is_even)) (result (i32 | (i32.eqz v)))
  local.get $x
  i32.const 1
  i32.shr_u
  i32.const 2
  i32.mul
  local.get $x
  i32.sub
)
(func $back_s (export "back_s") (param $x (i32 | $is_even)) (result (i32 | (i32.eqz v)))
  local.get $x
  i32.const 1
  i32.shr_s
  i32.const 2
  i32.mul
  local.get $x
  i32.sub
)
(func $back_harness (export "harness:back_u") (param $x i32)
  local.get $x
  i32.const 1
  i32.shl
  call $back_u
  i32.eqz
  br_if 0
  unreachable
)
