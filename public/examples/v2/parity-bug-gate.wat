;; parity, seeded bug P1 (code bug): the gate is inverted -- line 42 `i32.eqz` became `nop`
(func $main ;; runs $parity_ok on no input passes this bug; 3 stops at the runtime check on $half's precondition
  i32.const 3
  call $parity_ok
)
(func $is_even (param $x i32) (result i32)
  local.get $x
  i32.const 1
  i32.and
  i32.eqz
)
(func $is_half (param $v i32) (param $x i32) (result i32)
  local.get $v
  i64.extend_i32_s
  local.get $v
  i64.extend_i32_s
  i64.add
  local.get $x
  i64.extend_i32_s
  i64.eq
)
(func $hon_ok (param $v i32) (param $x i32) (result i32)
  local.get $x
  call $is_even
  if (result i32)
    local.get $v
    local.get $x
    call $is_half
  else
    local.get $v
    i32.const -1
    i32.eq
  end
)
(func $half (param $x (i32 | $is_even)) (result (i32 | $is_half $x))
  local.get $x
  i32.const 1
  i32.shr_s
)
(func $half_or_neg1 (export "half_or_neg1") (param $x i32) (result (i32 | $hon_ok $x))
  local.get $x
  call $is_even
  nop
  if (result (i32 | $hon_ok $x))
    i32.const -1
  else
    local.get $x
    call $half
  end
)
(func $parity_ok (export "harness:half_or_neg1") (param $x i32)
  local.get $x
  call $half_or_neg1
  local.get $x
  call $hon_ok
  br_if 0
  unreachable
)
