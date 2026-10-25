;; hash table, seeded wrong proof (stale fact): the clearing loop increments $i before the store, so the guard fact u($i) < 8 is about the old $i
(memory 1)
(func $hash (param $k i32) (result i32)
  local.get $k
  i32.const 7
  i32.and
)
(func $slot (param $j i32) (result i32)
  local.get $j
  i32.const 7
  i32.and
  i32.const 2
  i32.shl
  i32.load offset=65504
)
(func $is_key (param $k i32) (result i32)
  local.get $k
  i32.eqz
  if (result i32)
    i32.const 0
  else
    local.get $k
    i32.const -1
    i32.ne
  end
)
(func $slot_or_none (param $v i32) (result i32)
  local.get $v
  i32.const 8
  i32.lt_u
  if (result i32)
    i32.const 1
  else
    local.get $v
    i32.const -1
    i32.eq
  end
)
(func $chain_ok (param $p i32) (param $n i32) (result i32)
  local.get $n
  i32.eqz
  if (result i32)
    i32.const 1
  else
    local.get $p
    call $slot
    i32.eqz
    if (result i32)
      i32.const 0
    else
      local.get $p
      i32.const 1
      i32.add
      local.get $n
      i32.const 1
      i32.sub
      call $chain_ok
    end
  end
)
(func $count_m (export "measure:chain_ok") (param $p i32) (param $n i32) (result i32)
  local.get $n
)
(func $no_dup (param $k i32) (param $p i32) (param $n i32) (result i32)
  local.get $n
  i32.eqz
  if (result i32)
    i32.const 1
  else
    local.get $p
    call $slot
    local.get $k
    i32.eq
    if (result i32)
      i32.const 0
    else
      local.get $k
      local.get $p
      i32.const 1
      i32.add
      local.get $n
      i32.const 1
      i32.sub
      call $no_dup
    end
  end
)
(func $no_dup_m (export "measure:no_dup") (param $k i32) (param $p i32) (param $n i32) (result i32)
  local.get $n
)
(func $slot_ok (param $j i32) (result i32)
  local.get $j
  call $slot
  call $is_key
  if (result i32)
    local.get $j
    call $slot
    call $hash
    local.get $j
    local.get $j
    call $slot
    call $hash
    i32.sub
    i32.const 7
    i32.and
    call $chain_ok
    if (result i32)
      local.get $j
      call $slot
      local.get $j
      i32.const 1
      i32.add
      i32.const 7
      call $no_dup
    else
      i32.const 0
    end
  else
    i32.const 1
  end
)
(func $rep_from (param $j i32) (param $n i32) (result i32)
  local.get $n
  i32.eqz
  if (result i32)
    i32.const 1
  else
    local.get $j
    call $slot_ok
    if (result i32)
      local.get $j
      i32.const 1
      i32.add
      local.get $n
      i32.const 1
      i32.sub
      call $rep_from
    else
      i32.const 0
    end
  end
)
(func $rep_from_m (export "measure:rep_from") (param $j i32) (param $n i32) (result i32)
  local.get $n
)
(func $rep_ok (result i32)
  i32.const 0
  i32.const 8
  call $rep_from
)
(func $find (export "find") (param $k i32) (result (i32 | $slot_or_none))
  (local $i i32)
  (local $j i32)
  (local $v i32)
  block $notfound
    loop $probe
      local.get $i
      i32.const 8
      i32.ge_u
      br_if $notfound
      local.get $k
      call $hash
      local.get $i
      i32.add
      i32.const 7
      i32.and
      local.tee $j
      i32.const 2
      i32.shl
      i32.load offset=65504
      local.tee $v
      local.get $k
      i32.eq
      if
        local.get $j
        return
      end
      local.get $v
      i32.eqz
      br_if $notfound
      local.get $i
      i32.const 1
      i32.add
      local.set $i
      br $probe
    end
  end
  i32.const -1
)
(func $insert (export "insert") (param $k (i32 | $is_key)) (param $inv (fact (call $rep_ok))) (result i32) (result (fact (call $rep_ok)))
  (local $i i32)
  (local $j i32)
  (local $v i32)
  (local $free i32)
  block $full
    loop $probe (fact (call $rep_ok))
      local.get $i
      i32.const 8
      i32.ge_u
      br_if $full
      local.get $k
      call $hash
      local.get $i
      i32.add
      i32.const 7
      i32.and
      local.tee $j
      i32.const 2
      i32.shl
      i32.load offset=65504
      local.tee $v
      local.get $k
      i32.eq
      if
        i32.const 1
        return
      end
      local.get $v
      i32.eqz
      if
        local.get $free
        i32.eqz
        if
          local.get $j
          i32.const 1
          i32.add
          local.set $free
        end
        local.get $free
        i32.const 1
        i32.sub
        i32.const 7
        i32.and
        i32.const 2
        i32.shl
        local.get $k
        i32.store offset=65504
        i32.const 1
        return
      end
      local.get $v
      i32.const -1
      i32.eq
      local.get $free
      i32.eqz
      i32.and
      if
        local.get $j
        i32.const 1
        i32.add
        local.set $free
      end
      local.get $i
      i32.const 1
      i32.add
      local.set $i
      br $probe
    end
  end
  local.get $free
  i32.eqz
  if
    i32.const 0
    return
  end
  local.get $free
  i32.const 1
  i32.sub
  i32.const 7
  i32.and
  i32.const 2
  i32.shl
  local.get $k
  i32.store offset=65504
  i32.const 1
)
(func $remove (export "remove") (param $k i32) (param $inv (fact (call $rep_ok))) (result (fact (call $rep_ok)))
  (local $j i32)
  local.get $k
  call $find
  local.tee $j
  i32.const -1
  i32.eq
  if
    return
  end
  local.get $j
  i32.const 2
  i32.shl
  i32.const -1
  i32.store offset=65504
)
(func $table_harness (export "harness:table") (param $a i32) (param $b i32)
  (local $i i32)
  block $c
    loop $z
      local.get $i
      i32.const 8
      i32.ge_u
      br_if $c
      local.get $i
      i32.const 1
      i32.add
      local.set $i
      local.get $i
      i32.const 2
      i32.shl
      i32.const 0
      i32.store offset=65504
      br $z
    end
  end
  local.get $a
  call $is_key
  i32.eqz
  br_if 0
  local.get $b
  call $is_key
  i32.eqz
  br_if 0
  local.get $a
  call $insert
  drop
  local.get $b
  call $insert
  drop
  block
    local.get $a
    call $find
    i32.const -1
    i32.ne
    br_if 0
    unreachable
  end
  local.get $a
  call $remove
  block
    local.get $a
    call $find
    i32.const -1
    i32.eq
    br_if 0
    unreachable
  end
  block
    local.get $a
    local.get $b
    i32.eq
    br_if 0
    local.get $b
    call $find
    i32.const -1
    i32.ne
    br_if 0
    unreachable
  end
  call $rep_ok
  br_if 0
  unreachable
)
