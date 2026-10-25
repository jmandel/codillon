;; gcd, seeded vacuous spec: the harness precondition was meant as "a >= 0" (gt_s v -1) but says gt_u, i.e. u(a) > 2^32-1, which no input satisfies
(func $divides (param $d i64) (param $n i64) (result i32)
  local.get $d
  i64.eqz
  if (result i32)
    local.get $n
    i64.eqz
  else
    local.get $n
    local.get $d
    i64.rem_u
    i64.eqz
  end
)
(func $common (param $d i64) (param $a i32) (param $b i32) (result i32)
  local.get $d
  local.get $a
  i64.extend_i32_u
  call $divides
  if (result i32)
    local.get $d
    local.get $b
    i64.extend_i32_u
    call $divides
  else
    i32.const 0
  end
)
(func $no_cd_above (param $d i64) (param $a i32) (param $b i32) (result i32)
  local.get $d
  local.get $a
  i64.extend_i32_u
  local.get $b
  i64.extend_i32_u
  i64.add
  i64.gt_u
  if (result i32)
    i32.const 1
  else
    local.get $d
    local.get $a
    local.get $b
    call $common
    if (result i32)
      i32.const 0
    else
      local.get $d
      i64.const 1
      i64.add
      local.get $a
      local.get $b
      call $no_cd_above
    end
  end
)
(func $no_cd_above_m (export "measure:no_cd_above") (param $d i64) (param $a i32) (param $b i32) (result i64)
  local.get $a
  i64.extend_i32_u
  local.get $b
  i64.extend_i32_u
  i64.add
  i64.const 1
  i64.add
  local.get $d
  i64.sub
)
(func $is_gcd (param $g i32) (param $a i32) (param $b i32) (result i32)
  local.get $g
  i64.extend_i32_u
  local.get $a
  local.get $b
  call $common
  if (result i32)
    local.get $g
    i64.extend_i32_u
    i64.const 1
    i64.add
    local.get $a
    local.get $b
    call $no_cd_above
  else
    i32.const 0
  end
)
(func $gcd_ref (param $a i32) (param $b i32) (result i32)
  local.get $b
  i32.eqz
  if (result i32)
    local.get $a
  else
    local.get $b
    local.get $a
    local.get $b
    i32.rem_u
    call $gcd_ref
  end
)
(func $gcd_ref_m (export "measure:gcd_ref") (param $a i32) (param $b i32) (result i32)
  local.get $b
)
(func $gcd_ref_ok (export "axiom:gcd_ref_is_gcd") (param $g i32) (param $a i32) (param $b i32) (param $h (fact (i32.eq $g (call $gcd_ref $a $b)))) (result (fact (call $is_gcd $g $a $b)))
)
(func $gcd (export "gcd") (param $a i32) (param $b i32) (result (i32 | (i32.eq v (call $gcd_ref $a $b))))
  (local $x i32)
  (local $y i32)
  (local $t i32)
  local.get $a
  local.set $x
  local.get $b
  local.set $y
  block $done (fact (i32.eq (call $gcd_ref $x $y) (call $gcd_ref $a $b))) (fact (i32.eqz $y))
    loop $euclid (fact (i32.eq (call $gcd_ref $x $y) (call $gcd_ref $a $b)))
      local.get $y
      i32.eqz
      br_if $done
      local.get $x
      local.get $y
      i32.rem_u
      local.set $t
      unfold $gcd_ref $x $y
      local.get $y
      local.set $x
      local.get $t
      local.set $y
      br $euclid
    end
  end
  local.get $x
  unfold $gcd_ref $x $y
)
(func $gcd_harness (export "harness:gcd") (param $a (i32 | (i32.gt_u v -1))) (param $b i32)
  (local $g i32)
  local.get $a
  local.get $b
  call $gcd
  local.set $g
  local.get $g
  local.get $a
  local.get $b
  call $is_gcd
  br_if 0
  nop
  unreachable
)
