(func $main
  i32.const 10
  call $isqrt
  drop
)
(func $isqrt (param $n (i32 | 0 <= $n)) (result $root (i32 | 0 <= $root))
  (@ensures $root * $root <= $n < ($root + 1) * ($root + 1))
  (local $r i32)
  i32.const 0
  local.set $r
  block $done
    loop $grow
      (@invariant 0 <= $r && $r * $r <= $n)
      (@decreases $n - $r * $r)
      local.get $r
      i32.const 1
      i32.add
      local.get $r
      i32.const 1
      i32.add
      i32.mul
      local.get $n
      i32.gt_u
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
