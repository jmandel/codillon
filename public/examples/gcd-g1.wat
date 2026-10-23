;; G1: the loop guard tests $x instead of $y. gcd(12, 8) reaches y = 0
;; with x = 4 and traps in i32.rem_u (remainder by zero). The invariant
;; held on every arrival before the trap.
(func $main
  i32.const 12
  i32.const 8
  call $gcd
  drop
)
(@define gcd($x, $y) = ($y == 0 ? $x : gcd($y, $x % $y)))
(func $gcd (param $a (i32 | 0 <= $a)) (param $b (i32 | 0 <= $b))
  (result $g (i32 | $g == gcd($a, $b)))
  (local $x i32)
  (local $y i32)
  (local $t i32)
  local.get $a
  local.set $x
  local.get $b
  local.set $y
  block $done
    loop $euclid
      (@invariant 0 <= $x && 0 <= $y && gcd($x, $y) == gcd($a, $b))
      (@decreases $y)
      local.get $x
      i32.eqz
      br_if $done
      local.get $x
      local.get $y
      i32.rem_u
      local.set $t
      local.get $y
      local.set $x
      local.get $t
      local.set $y
      br $euclid
    end
  end
  local.get $x
)
