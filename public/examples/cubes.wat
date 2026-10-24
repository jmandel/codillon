;; Undecided: the assertion is Fermat's last theorem for cubes (below 1000), true but
;; beyond the solver's budget: Z3 neither proves nor refutes it, so the line shows ?.
(func $main
  i32.const 3
  i32.const 4
  i32.const 5
  call $cubes
  drop
)
(func $cubes (param $x (i32 | 1 <= $x <= 999)) (param $y (i32 | 1 <= $y <= 999))
  (param $z (i32 | 1 <= $z <= 999))
  (result $r i32)
  (@define cube($n) = ($n % 1000) * ($n % 1000) * ($n % 1000))
  nop
  (@assert cube($x) + cube($y) != cube($z))
  local.get $x
)
