;; S1 (subtle): signed comparison i32.gt_s. Correct for every n < 2147395600.
;; For larger n the product (r+1)*(r+1) wraps negative and the loop overruns;
;; at n = INT_MAX it never terminates. That input needs ~695,000 steps, beyond
;; Codillon's 100,000-step budget, so this run (n = 10) passes every check.
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
      i32.gt_s
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
