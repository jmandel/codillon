;; The loop guard is off by one (i32.gt_s for i32.ge_s): $i is set to 6 > $n,
;; outside its refined type. The invariant still holds; the measure and the result do not.
(func $main
  i32.const 5
  call $triangle
  drop
)
(func $triangle (param $n (i32 | 0 <= $n <= 1000))
  (result $t (i32 | $t == $n * ($n + 1) / 2))
  (local $i (i32 | 0 <= $i <= $n))
  (local $acc i32)
  block $done
    loop $sum
      (@invariant $acc == $i * ($i + 1) / 2)
      (@decreases $n - $i)
      local.get $i
      local.get $n
      i32.gt_s
      br_if $done
      local.get $i
      i32.const 1
      i32.add
      local.set $i
      local.get $acc
      local.get $i
      i32.add
      local.set $acc
      br $sum
    end
  end
  local.get $acc
)
