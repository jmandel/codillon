;; P3 (spec bug): "half is smaller" is false for 0 and for negative even numbers.
;; Your run holds; the input search finds $half(0). The code is right; the spec is wrong.
(func $main
  i32.const 6
  call $half_or_neg1
  drop
  i32.const 7
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
  (@ensures $h + $h == $x && $h < $x)
  local.get $x
  i32.const 1
  i32.shr_s
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
