;; isqrt, seeded missing invariant: the loop's fact (sq_le r n) was deleted (line 30), so nothing says r² ≤ n at the loop head and neither exit can show the block fact is_isqrt(r, n)
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
    loop $grow
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
