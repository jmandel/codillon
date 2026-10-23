;; P2 (subtle): i32.shr_u instead of i32.shr_s. Fine for every even x >= 0;
;; for x = -4 it returns 2147483646, and $half's result refinement fails.
(func $main
  i32.const 6
  call $half_or_neg1
  drop
  i32.const -4
  call $half_or_neg1
  drop
)
(func $is_even (param $x i32) (result $e (i32 | $e == ($x % 2 == 0 ? 1 : 0)))
  local.get $x
  i32.const 1
  i32.and
  i32.eqz
)
(func $half (param $x (i32 | $x % 2 == 0)) (result $h i32)
  (@ensures $h + $h == $x)
  local.get $x
  i32.const 1
  i32.shr_u
)
(func $half_or_neg1 (param $x i32) (result $y i32)
  (@ensures $y == ($x % 2 == 0 ? $x / 2 : -1))
  local.get $x
  call $is_even
  i32.eqz
  if (result i32)
    i32.const -1
  else
    (@assert $x % 2 == 0)
    local.get $x
    call $half
  end
)
