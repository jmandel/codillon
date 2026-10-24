;; (c) $insert no longer checks for an existing key (its find-and-update group is
;; blank). insert(3, 31) writes a second FULL slot for key 3: the free-slot loop's
;; invariant !(k in M) fails on entry, and R fails at insert's return.
(memory 1)
(global $used (mut i32) (i32.const 0))
(@ghost global $M (map i32 i32))
(@define EMPTY = 0, FULL = 1, TOMB = 2, CAP = 8, BASE = 65440)
(@define st($s) = load(BASE + 12 * $s))
(@define key($s) = load(BASE + 12 * $s + 4))
(@define val($s) = load(BASE + 12 * $s + 8))
(@define h($k) = $k & 7, at($k, $d) = (h($k) + $d) & 7)
(@define dist($k, $s) = ($s - h($k)) & 7)
(@define R0 = forall $s in 0..CAP: st($s) in {EMPTY, FULL, TOMB})
(@define stored($s) = key($s) in $M && $M[key($s)] == val($s))
(@define R1 = forall $s in 0..CAP: st($s) == FULL ==> stored($s))
(@define copies($k) = count $s in 0..CAP: st($s) == FULL && key($s) == $k)
(@define R2 = forall $k in $M: copies($k) == 1)
(@define open($k, $d) = st(at($k, $d)) != EMPTY)
(@define reach($s) = forall $d in 0..CAP: $d <= dist(key($s), $s) ==> open(key($s), $d))
(@define R3 = forall $s in 0..CAP: st($s) == FULL ==> reach($s))
(@define FULLS = count $s in 0..CAP: st($s) == FULL)
(@define USED = count $s in 0..CAP: st($s) != EMPTY)
(@define R4 = FULLS == size($M) && $used == USED && $used < CAP)
(@define R = R0 && R1 && R2 && R3 && R4)
(@define holds($s, $k) = 0 <= $s < CAP && st($s) == FULL && key($s) == $k)
(@define other($k, $s) = st($s) == FULL && key($s) != $k)
(@define passed($k, $d) = st(at($k, $d)) == TOMB || other($k, at($k, $d)))
(func $main
  i32.const 3
  i32.const 30
  call $insert
  drop
  i32.const 3
  i32.const 31
  call $insert
  drop
  i32.const 3
  i32.const -1
  call $lookup
  drop
)
(func $slot (param $i (i32 | 0 <= $i && $i < CAP))
  (result $a (i32 | $a == BASE + 12 * $i))
  local.get $i
  i32.const 12
  i32.mul
  i32.const 65440
  i32.add
)
(func $find (param $k i32)
  (result $v (i32 | ($v == -1 && !($k in $M)) || holds($v, $k)))
  (@requires R)
  (local $i i32)
  (local $p i32)
  (@ghost local $j i32)
  local.get $k
  i32.const 7
  i32.and
  local.set $i
  loop $probe
    (@invariant 0 <= $j && $j <= $used && $i == at($k, $j))
    (@invariant forall $d in 0..CAP: $d < $j ==> passed($k, $d))
    (@decreases CAP - $j)
    local.get $i
    call $slot
    local.tee $p
    i32.load
    i32.const 1
    i32.lt_u
    if
      i32.const -1
      return
    end
    local.get $p
    i32.load
    i32.const 1
    i32.eq
    local.get $p
    i32.load offset=4
    local.get $k
    i32.eq
    i32.and
    if
      local.get $i
      return
    end
    local.get $i
    i32.const 1
    i32.add
    i32.const 7
    i32.and
    local.set $i
    (@set $j := $j + 1)
    br $probe
  end
  unreachable
)
(func $lookup (param $k i32) (param $dflt i32)
  (result $v (i32 | $v == ($k in $M ? $M[$k] : $dflt)))
  (@requires R)
  (@ensures R)
  (local $i i32)
  local.get $k
  call $find
  local.tee $i
  i32.const 0
  i32.lt_s
  if
    local.get $dflt
    return
  end
  local.get $i
  call $slot
  i32.load offset=8
)
(func $delete (param $k i32)
  (result $ok (i32 | $ok == ($k in old($M) ? 1 : 0)))
  (@requires R)
  (@ensures R && $M == remove(old($M), $k))
  (local $i i32)
  local.get $k
  call $find
  local.tee $i
  i32.const 0
  i32.lt_s
  if
    i32.const 0
    return
  end
  local.get $i
  call $slot
  i32.const 2
  i32.store
  (@set $M := remove($M, $k))
  i32.const 1
)
(func $insert (param $k i32) (param $x i32)
  (result $ok (i32 | $ok == 1 || ($ok == 0 && !($k in $M) && $used == CAP - 1)))
  (@requires R)
  (@ensures R && $M == ($ok == 1 ? old($M)[$k -> $x] : old($M)))
  (local $i i32)
  (local $p i32)
  (@ghost local $j i32)














  global.get $used
  i32.const 7
  i32.ge_u
  if
    i32.const 0
    return
  end
  local.get $k
  i32.const 7
  i32.and
  local.set $i
  loop $free
    (@invariant !($k in $M) && 0 <= $j && $j <= $used && $i == at($k, $j))
    (@invariant forall $d in 0..CAP: $d < $j ==> open($k, $d))
    (@decreases CAP - $j)
    local.get $i
    call $slot
    local.tee $p
    i32.load
    if
      local.get $i
      i32.const 1
      i32.add
      i32.const 7
      i32.and
      local.set $i
      (@set $j := $j + 1)
      br $free
    end
  end
  local.get $p
  i32.const 1
  i32.store
  local.get $p
  local.get $k
  i32.store offset=4
  local.get $p
  local.get $x
  i32.store offset=8
  global.get $used
  i32.const 1
  i32.add
  global.set $used
  (@set $M := $M[$k -> $x])
  i32.const 1
)
