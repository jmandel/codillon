;; primality: $prime_spec (no divisor in [2, n), clear, slow) and $prime (stops at sqrt(n) via d > n / d), measures, axioms, lemmas (v2 syntax)
(func $nd (param $n i64) (param $lo i64) (param $hi i64) (result i32)
  local.get $lo
  local.get $hi
  i64.ge_u
  if (result i32)
    i32.const 1
  else
    local.get $lo
    i64.const 2
    i64.lt_u
    if (result i32)
      local.get $n
      local.get $lo
      i64.const 1
      i64.add
      local.get $hi
      prove 2
      call $nd
    else
      local.get $n
      local.get $lo
      prove 1
      i64.rem_u
      i64.eqz
      if (result i32)
        i32.const 0
      else
        local.get $n
        local.get $lo
        i64.const 1
        i64.add
        local.get $hi
        prove 4
        call $nd
      end
    end
  end
)
(func $nd_m (export "measure:nd") (param $n i64) (param $lo i64) (param $hi i64) (result i64)
  local.get $hi
  local.get $lo
  i64.sub
)
(func $prime_spec (param $n i64) (result i32)
  local.get $n
  i64.const 2
  i64.lt_u
  if (result i32)
    i32.const 0
  else
    local.get $n
    i64.const 2
    local.get $n
    call $nd
  end
)
(func $no_divisor_from (param $n i64) (param $d i64) (result i32)
  local.get $d
  i64.const 2
  i64.lt_u
  if (result i32)
    i32.const 0
  else
    local.get $d
    local.get $n
    local.get $d
    prove 1
    i64.div_u
    i64.gt_u
    if (result i32)
      i32.const 1
    else
      local.get $n
      local.get $d
      i64.rem_u
      i64.eqz
      if (result i32)
        i32.const 0
      else
        lemma $div_shrinks $n $d
        local.get $n
        local.get $d
        i64.const 1
        i64.add
        prove 4
        call $no_divisor_from
      end
    end
  end
)
(func $ndf_m (export "measure:no_divisor_from") (param $n i64) (param $d i64) (result i64)
  local.get $n
  local.get $d
  i64.sub
)
(func $prime (export "prime") (param $n i64) (result i32)
  local.get $n
  i64.const 2
  i64.lt_u
  if (result i32)
    i32.const 0
  else
    local.get $n
    i64.const 2
    call $no_divisor_from
  end
)
(func $div_shrinks (export "axiom:div_shrinks") (param $n i64) (param $d i64) (param $h (fact (i64.ge_u $d 2))) (result (fact (i64.le_u (i64.div_u $n $d) (i64.shr_u $n 1))))
)
(func $sqrt_suffices (export "axiom:sqrt_suffices") (param $n i64) (param $d i64) (param $h1 (fact (i64.ge_u $d 2))) (param $h2 (fact (i64.gt_u $d (i64.div_u $n $d)))) (param $h3 (fact (call $nd $n 2 $d))) (result (fact (call $nd $n $d $n)))
)
(func $nd_extend (export "axiom:nd_extend") (param $n i64) (param $lo i64) (param $hi i64) (param $h1 (fact (call $nd $n $lo $hi))) (param $h2 (fact (i64.ne (i64.rem_u $n $hi) 0))) (result (fact (call $nd $n $lo (i64.add $hi 1))))
)
(func $from_agrees (export "lemma:from_agrees") (param $n i64) (param $d i64) (param $h1 (fact (i64.ge_u $d 2))) (param $h2 (fact (call $nd $n 2 $d))) (result (fact (i32.eq (i32.eqz (call $no_divisor_from $n $d)) (i32.eqz (call $nd $n $d $n)))))
  (local $hq fact)
  (local $hr fact)
  local.get $d
  local.get $n
  local.get $d
  local.get $h1
  prove 1
  i64.div_u
  i64.gt_u
  if (fact (i32.eq (i32.eqz (call $no_divisor_from $n $d)) (i32.eqz (call $nd $n $d $n))))
    lemma $sqrt_suffices $n $d
    unfold $no_divisor_from $n $d
    local.get $h1
    prove 4
  else
    local.set $hq
    local.get $n
    local.get $d
    i64.rem_u
    i64.eqz
    if (fact (i32.eq (i32.eqz (call $no_divisor_from $n $d)) (i32.eqz (call $nd $n $d $n))))
      unfold $no_divisor_from $n $d
      unfold $nd $n $d $n
      lemma $div_shrinks $n $d
      local.get $h1
      local.get $hq
      prove 6
    else
      local.set $hr
      lemma $nd_extend $n 2 $d
      lemma $div_shrinks $n $d
      local.get $h1
      local.get $hq
      prove 4
      prove 4
      lemma $from_agrees $n (i64.add $d 1)
      unfold $no_divisor_from $n $d
      unfold $nd $n $d $n
      lemma $div_shrinks $n $d
      local.get $h1
      local.get $hq
      local.get $hr
      prove 7
    end
  end
)
(func $from_agrees_m (export "measure:from_agrees") (param $n i64) (param $d i64) (result i64)
  local.get $n
  local.get $d
  i64.sub
)
(func $prime_agrees (export "lemma:prime_agrees") (param $n i64) (result (fact (i32.eq (i32.eqz (call $prime $n)) (i32.eqz (call $prime_spec $n)))))
  local.get $n
  i64.const 2
  i64.lt_u
  if (fact (i32.eq (i32.eqz (call $prime $n)) (i32.eqz (call $prime_spec $n))))
    prove 1
  else
    unfold $nd $n 2 2
    prove 1
    lemma $from_agrees $n 2
    prove 4
  end
)
(func $prime_harness (export "harness:prime") (param $n i64)
  local.get $n
  call $prime
  i32.eqz
  local.get $n
  call $prime_spec
  i32.eqz
  i32.eq
  br_if 0
  lemma $prime_agrees $n
  prove 2
  unreachable
)
