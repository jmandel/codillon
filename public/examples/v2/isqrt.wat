;; isqrt: integer square root of n read unsigned; spec = harness ending in unreachable (v2 syntax)
(func $main ;; runs $isqrt_harness on a passing input
  i32.const 17
  call $isqrt_harness
)
(func $sq_le (param $r i64) (param $n i64) (result i32)
  local.get $r
  local.get $r
  i64.mul
  local.get $n
  i64.le_u
)
(func $is_isqrt (param $r i64) (param $n i64) (result i32)
  local.get $r
  local.get $n
  call $sq_le
  if (result i32)
    local.get $n
    local.get $r
    i64.const 1
    i64.add
    local.get $r
    i64.const 1
    i64.add
    i64.mul
    i64.lt_u
  else
    i32.const 0
  end
)
(func $isqrt (export "isqrt") (param $n i32) (result (i32 | (call $is_isqrt (i64.extend_i32_u v) (i64.extend_i32_u $n))))
  (local $r (i32 | (i32.le_u v 65535)))
  block $done (fact (call $is_isqrt (i64.extend_i32_u $r) (i64.extend_i32_u $n)))
    loop $grow (fact (call $sq_le (i64.extend_i32_u $r) (i64.extend_i32_u $n)))
      local.get $r
      i32.const 65535
      i32.ge_u
      br_if $done
      local.get $r
      i64.extend_i32_u
      i64.const 1
      i64.add
      local.get $r
      i64.extend_i32_u
      i64.const 1
      i64.add
      i64.mul
      local.get $n
      i64.extend_i32_u
      i64.gt_u
      br_if $done
      local.get $r
      i32.const 1
      i32.add
      local.set $r
      br $grow
    end
  end
  local.get $r
)
(func $isqrt_harness (export "harness:isqrt") (param $n i32)
  local.get $n
  call $isqrt
  i64.extend_i32_u
  local.get $n
  i64.extend_i32_u
  call $is_isqrt
  br_if 0
  unreachable
)
