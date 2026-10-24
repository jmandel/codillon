;; isqrt, seeded spec bug: the harness checks in i32, so (r+1)*(r+1) wraps to 0 at r = 65535 (the isqrt overflow lesson, now in the spec)
(func $main ;; runs $isqrt_harness on a passing input (the harness bug shows at n = -1, i.e. 2^32-1)
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
    prove 0
    loop $grow (fact (call $sq_le (i64.extend_i32_u $r) (i64.extend_i32_u $n)))
      local.get $r
      i32.const 65535
      i32.ge_u
      prove 2
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
      prove 2
      br_if $done
      local.get $r
      i32.const 1
      i32.add
      prove 2
      local.set $r
      prove 3
      br $grow
    end
  end
  local.get $r
)
(func $is_isqrt32 (param $r i32) (param $n i32) (result i32)
  local.get $r
  local.get $r
  i32.mul
  local.get $n
  i32.le_u
  if (result i32)
    local.get $n
    local.get $r
    i32.const 1
    i32.add
    local.get $r
    i32.const 1
    i32.add
    i32.mul
    i32.lt_u
  else
    i32.const 0
  end
)
(func $isqrt_harness (export "harness:isqrt") (param $n i32)
  local.get $n
  call $isqrt
  local.get $n
  call $is_isqrt32
  br_if 0
  prove 2
  unreachable
)
