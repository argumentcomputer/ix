import IxCC.Lir.Opt.DivMagic

/-!
# Symbolic expressions, interval bounds, and segment memory for Lir validation

Defines the pure symbolic expression language `SymExpr`, canonical normalization
`SymExpr.norm`, arithmetic equivalence `exprEquiv` (covering algebraic identities
and Granlund–Montgomery magic-multiplier division/modulo), unsigned 64-bit
interval propagation from dominating branch facts `PFact`, and the intra-segment
byte-disjoint memory model `SymMem` (for store-to-load forwarding, load CSE,
and intra-block dead-store elimination).

All functions here are total, kernel-evaluable (structural recursion, no
`partial`), and form the trusted core of `Lir.Opt.check`.
-/

set_option autoImplicit false

namespace IxCC.Lir.Opt

open IxCC.Lir (VReg Width Ext Base Addr Arg Cond BinOp Ovf LimbOp Rhs Word Env
  sext sarWord rolWord rorWord shiftMask dispWord loadWord)

/-! ## Condition helpers -/

/-- Logical negation of a Lir condition: `(condNegate c).holds w a b = !(c.holds w a b)`. -/
def condNegate : Cond → Cond
  | .eq => .ne
  | .ne => .eq
  | .ult => .uge
  | .ule => .ugt
  | .ugt => .ule
  | .uge => .ult
  | .slt => .sge
  | .sle => .sgt
  | .sgt => .sle
  | .sge => .slt
  | .tz => .tnz
  | .tnz => .tz

/-- Operand-swapped condition: `(condSwap c).holds w b a = c.holds w a b`. -/
def condSwap : Cond → Cond
  | .eq => .eq
  | .ne => .ne
  | .ult => .ugt
  | .ule => .uge
  | .ugt => .ult
  | .uge => .ule
  | .slt => .sgt
  | .sle => .sge
  | .sgt => .slt
  | .sge => .sle
  | .tz => .tz
  | .tnz => .tnz

/-- Reflexive evaluation of `c.holds w a a`, when constant for all `a`. -/
def condReflVal : Cond → Option Bool
  | .eq | .ule | .uge | .sle | .sge => some true
  | .ne | .ult | .ugt | .slt | .sgt => some false
  | .tz | .tnz => none

/-- Whether `o` is commutative on its two word operands. -/
def binOpIsComm : BinOp → Bool
  | .add | .mul | .and | .or | .xor => true
  | _ => false

/-- Whether `o` is total (never returns `none` on any pair of words). -/
def binOpIsTotal : BinOp → Bool
  | .udiv | .urem => false
  | _ => true

/-! ## Symbolic expressions -/

/-- Pure symbolic expressions over segment-entry source registers (`reg x`),
the pinned context register (`ctx`), constants (`imm w`), arithmetic/bit/limb
operations, and segment memory snapshots (`load snapId`). -/
inductive SymExpr where
  | reg (x : VReg)
  | imm (w : Word)
  | ctx
  | bin (o : BinOp) (w : Width) (a b : SymExpr)
  | select (c : Cond) (w : Width) (a b t f : SymExpr)
  | test (c : Cond) (w : Width) (a b : SymExpr)
  | bsr64 (a : SymExpr)
  | mulHi (a b : SymExpr)
  | divQ (hi lo d : SymExpr)
  | divR (hi lo d : SymExpr)
  | addCLo (a b c : SymExpr)
  | addCHi (a b c : SymExpr)
  | subBLo (a b c : SymExpr)
  | subBHi (a b c : SymExpr)
  | load (snap : Nat) (w : Width) (e : Ext) (addr : SymExpr)
  deriving DecidableEq, Repr, Inhabited

/-- Memory snapshots indexed by snapshot id (`0` is segment entry `mem₀`). -/
abbrev MemSnaps := Nat → X86.Memory

/-- Evaluate a `SymExpr` in source environment `ρ`, context word `ctx`, and
memory snapshot map `snaps`. -/
def SymExpr.eval (ρ : Env) (ctx : Word) (snaps : MemSnaps) : SymExpr → Option Word
  | .reg x => ρ[x]?
  | .imm w => some w
  | .ctx => some ctx
  | .bin o w a b => do o.eval w (← a.eval ρ ctx snaps) (← b.eval ρ ctx snaps)
  | .select c w a b t f => do
      let va ← a.eval ρ ctx snaps
      let vb ← b.eval ρ ctx snaps
      let vt ← t.eval ρ ctx snaps
      let vf ← f.eval ρ ctx snaps
      some (if c.holds w va vb then vt else vf)
  | .test c w a b => do
      let va ← a.eval ρ ctx snaps
      let vb ← b.eval ρ ctx snaps
      some (if c.holds w va vb then 1 else 0)
  | .bsr64 a => do
      let va ← a.eval ρ ctx snaps
      if va == 0 then none else some (UInt64.ofNat va.toNat.log2)
  | .mulHi a b => do
      let va ← a.eval ρ ctx snaps
      let vb ← b.eval ρ ctx snaps
      some (UInt64.ofNat ((va.toNat * vb.toNat) / 2 ^ 64))
  | .divQ hi lo d => do
      let vhi ← hi.eval ρ ctx snaps
      let vlo ← lo.eval ρ ctx snaps
      let vd ← d.eval ρ ctx snaps
      if vd.toNat == 0 || vd.toNat ≤ vhi.toNat then none
      else some (UInt64.ofNat ((vhi.toNat * 2 ^ 64 + vlo.toNat) / vd.toNat))
  | .divR hi lo d => do
      let vhi ← hi.eval ρ ctx snaps
      let vlo ← lo.eval ρ ctx snaps
      let vd ← d.eval ρ ctx snaps
      if vd.toNat == 0 || vd.toNat ≤ vhi.toNat then none
      else some (UInt64.ofNat ((vhi.toNat * 2 ^ 64 + vlo.toNat) % vd.toNat))
  | .addCLo a b c => do
      let va ← a.eval ρ ctx snaps
      let vb ← b.eval ρ ctx snaps
      let vc ← c.eval ρ ctx snaps
      let cin : Nat := if vc == 0 then 0 else 1
      some (va + vb + UInt64.ofNat cin)
  | .addCHi a b c => do
      let va ← a.eval ρ ctx snaps
      let vb ← b.eval ρ ctx snaps
      let vc ← c.eval ρ ctx snaps
      let cin : Nat := if vc == 0 then 0 else 1
      some (if 2 ^ 64 ≤ va.toNat + vb.toNat + cin then 1 else 0)
  | .subBLo a b c => do
      let va ← a.eval ρ ctx snaps
      let vb ← b.eval ρ ctx snaps
      let vc ← c.eval ρ ctx snaps
      let bin : Nat := if vc == 0 then 0 else 1
      some (va - vb - UInt64.ofNat bin)
  | .subBHi a b c => do
      let va ← a.eval ρ ctx snaps
      let vb ← b.eval ρ ctx snaps
      let vc ← c.eval ρ ctx snaps
      let bin : Nat := if vc == 0 then 0 else 1
      some (if va.toNat < vb.toNat + bin then 1 else 0)
  | .load snap w e addr => do
      let va ← addr.eval ρ ctx snaps
      loadWord (snaps snap) w e va

/-- Whether a `SymExpr` contains no memory loads (valid across block boundaries). -/
def SymExpr.isMemFree : SymExpr → Bool
  | .reg _ | .imm _ | .ctx => true
  | .bin _ _ a b | .test _ _ a b | .mulHi a b => a.isMemFree && b.isMemFree
  | .select _ _ a b t f => a.isMemFree && b.isMemFree && t.isMemFree && f.isMemFree
  | .bsr64 a => a.isMemFree
  | .divQ a b c | .divR a b c | .addCLo a b c | .addCHi a b c
  | .subBLo a b c | .subBHi a b c => a.isMemFree && b.isMemFree && c.isMemFree
  | .load .. => false

/-- Whether a `SymExpr` is guaranteed to succeed (`some _`) whenever all of its
referenced registers are defined in `ρ` (no loads, no partial divisions/bsr). -/
def SymExpr.isTotal : SymExpr → Bool
  | .reg _ | .imm _ | .ctx => true
  | .bin o w a b =>
      a.isTotal && b.isTotal &&
      (binOpIsTotal o || match b with | .imm k => w.truncate k != 0 | _ => false)
  | .select _ _ a b t f => a.isTotal && b.isTotal && t.isTotal && f.isTotal
  | .test _ _ a b => a.isTotal && b.isTotal
  | .bsr64 a => match a with | .imm k => k != 0 | _ => false
  | .mulHi a b => a.isTotal && b.isTotal
  | .addCLo a b c | .addCHi a b c | .subBLo a b c | .subBHi a b c =>
      a.isTotal && b.isTotal && c.isTotal
  | .divQ .. | .divR .. | .load .. => false

/-- All source registers referenced by a `SymExpr`. -/
def SymExpr.vars : SymExpr → List VReg
  | .reg x => [x]
  | .imm _ | .ctx => []
  | .bin _ _ a b | .test _ _ a b | .mulHi a b => a.vars ++ b.vars
  | .select _ _ a b t f => a.vars ++ b.vars ++ t.vars ++ f.vars
  | .bsr64 a | .load _ _ _ a => a.vars
  | .divQ a b c | .divR a b c | .addCLo a b c | .addCHi a b c
  | .subBLo a b c | .subBHi a b c => a.vars ++ b.vars ++ c.vars

/-- Substitute source registers via `f` (used across edges and calls). -/
def SymExpr.subst (f : VReg → SymExpr) : SymExpr → SymExpr
  | .reg x => f x
  | .imm w => .imm w
  | .ctx => .ctx
  | .bin o w a b => .bin o w (a.subst f) (b.subst f)
  | .select c w a b t e => .select c w (a.subst f) (b.subst f) (t.subst f) (e.subst f)
  | .test c w a b => .test c w (a.subst f) (b.subst f)
  | .bsr64 a => .bsr64 (a.subst f)
  | .mulHi a b => .mulHi (a.subst f) (b.subst f)
  | .divQ a b c => .divQ (a.subst f) (b.subst f) (c.subst f)
  | .divR a b c => .divR (a.subst f) (b.subst f) (c.subst f)
  | .addCLo a b c => .addCLo (a.subst f) (b.subst f) (c.subst f)
  | .addCHi a b c => .addCHi (a.subst f) (b.subst f) (c.subst f)
  | .subBLo a b c => .subBLo (a.subst f) (b.subst f) (c.subst f)
  | .subBHi a b c => .subBHi (a.subst f) (b.subst f) (c.subst f)
  | .load s w e a => .load s w e (a.subst f)

/-! ## Ordering & canonical normalization -/

private def tagOf : SymExpr → Nat
  | .reg _ => 0 | .ctx => 1 | .bin .. => 2 | .select .. => 3
  | .test .. => 4 | .bsr64 _ => 5 | .mulHi .. => 6 | .divQ .. => 7
  | .divR .. => 8 | .addCLo .. => 9 | .addCHi .. => 10 | .subBLo .. => 11
  | .subBHi .. => 12 | .load .. => 13 | .imm _ => 14

private def widthTag : Width → Nat
  | .w8 => 0 | .w16 => 1 | .w32 => 2 | .w64 => 3

private def extTag : Ext → Nat
  | .zero => 0 | .sign => 1

private def binOpTag : BinOp → Nat
  | .add => 0 | .sub => 1 | .and => 2 | .or => 3 | .xor => 4 | .mul => 5
  | .shl => 6 | .shr => 7 | .sar => 8 | .rol => 9 | .ror => 10 | .udiv => 11 | .urem => 12

private def condTag : Cond → Nat
  | .eq => 0 | .ne => 1 | .ult => 2 | .ule => 3 | .ugt => 4 | .uge => 5
  | .slt => 6 | .sle => 7 | .sgt => 8 | .sge => 9 | .tz => 10 | .tnz => 11

private def lexCmp (o1 o2 : Ordering) : Ordering :=
  match o1 with
  | .eq => o2
  | o => o

/-- Deterministic total ordering on `SymExpr` placing `.imm` last (so commutative
normalization places constants on the right). -/
def SymExpr.cmp : SymExpr → SymExpr → Ordering
  | .reg x, .reg y => compare x y
  | .imm x, .imm y => compare x.toNat y.toNat
  | .ctx, .ctx => .eq
  | .bin o1 w1 a1 b1, .bin o2 w2 a2 b2 =>
      lexCmp (compare (binOpTag o1) (binOpTag o2)) <|
      lexCmp (compare (widthTag w1) (widthTag w2)) <|
      lexCmp (cmp a1 a2) (cmp b1 b2)
  | .select c1 w1 a1 b1 t1 f1, .select c2 w2 a2 b2 t2 f2 =>
      lexCmp (compare (condTag c1) (condTag c2)) <|
      lexCmp (compare (widthTag w1) (widthTag w2)) <|
      lexCmp (cmp a1 a2) <| lexCmp (cmp b1 b2) <| lexCmp (cmp t1 t2) (cmp f1 f2)
  | .test c1 w1 a1 b1, .test c2 w2 a2 b2 =>
      lexCmp (compare (condTag c1) (condTag c2)) <|
      lexCmp (compare (widthTag w1) (widthTag w2)) <|
      lexCmp (cmp a1 a2) (cmp b1 b2)
  | .bsr64 a1, .bsr64 a2 => cmp a1 a2
  | .mulHi a1 b1, .mulHi a2 b2 => lexCmp (cmp a1 a2) (cmp b1 b2)
  | .divQ a1 b1 c1, .divQ a2 b2 c2 => lexCmp (cmp a1 a2) (lexCmp (cmp b1 b2) (cmp c1 c2))
  | .divR a1 b1 c1, .divR a2 b2 c2 => lexCmp (cmp a1 a2) (lexCmp (cmp b1 b2) (cmp c1 c2))
  | .addCLo a1 b1 c1, .addCLo a2 b2 c2 => lexCmp (cmp a1 a2) (lexCmp (cmp b1 b2) (cmp c1 c2))
  | .addCHi a1 b1 c1, .addCHi a2 b2 c2 => lexCmp (cmp a1 a2) (lexCmp (cmp b1 b2) (cmp c1 c2))
  | .subBLo a1 b1 c1, .subBLo a2 b2 c2 => lexCmp (cmp a1 a2) (lexCmp (cmp b1 b2) (cmp c1 c2))
  | .subBHi a1 b1 c1, .subBHi a2 b2 c2 => lexCmp (cmp a1 a2) (lexCmp (cmp b1 b2) (cmp c1 c2))
  | .load s1 w1 e1 a1, .load s2 w2 e2 a2 =>
      lexCmp (compare s1 s2) <| lexCmp (compare (widthTag w1) (widthTag w2)) <|
      lexCmp (compare (extTag e1) (extTag e2)) (cmp a1 a2)
  | e1, e2 => compare (tagOf e1) (tagOf e2)

/-- Static evaluation of `c w a b` on normalized expressions. -/
def condStatic (c : Cond) (w : Width) (a b : SymExpr) : Option Bool :=
  match a, b with
  | .imm va, .imm vb => some (c.holds w va vb)
  | _, _ => if a == b then condReflVal c else none

/-- Match `x + (x << k)` or `(x << k) + x` for `k ∈ {1, 2, 3}` and canonicalize to
`x * 3`, `x * 5`, `x * 9` (aligning `lea [x + x*scale]` with `mul`). -/
def matchAddShlSelf (a b : SymExpr) : Option SymExpr :=
  match a, b with
  | x, .bin .shl .w64 y (.imm 1) =>
      if x == y then some (.bin .mul .w64 x (.imm 3)) else none
  | .bin .shl .w64 y (.imm 1), x =>
      if x == y then some (.bin .mul .w64 x (.imm 3)) else none
  | x, .bin .shl .w64 y (.imm 2) =>
      if x == y then some (.bin .mul .w64 x (.imm 5)) else none
  | .bin .shl .w64 y (.imm 2), x =>
      if x == y then some (.bin .mul .w64 x (.imm 5)) else none
  | x, .bin .shl .w64 y (.imm 3) =>
      if x == y then some (.bin .mul .w64 x (.imm 9)) else none
  | .bin .shl .w64 y (.imm 3), x =>
      if x == y then some (.bin .mul .w64 x (.imm 9)) else none
  | _, _ => none

/-- Non-recursive helper combining two 64-bit addends: `x + x → x << 1`,
`x + (x << k) → x * (1 + 2^k)` (`k ∈ {1, 2, 3}`), else commutatively ordered `+`. -/
def mkAdd64Core (a b : SymExpr) : SymExpr :=
  if a == b then .bin .shl .w64 a (.imm 1)
  else match matchAddShlSelf a b with
  | some r => r
  | none =>
      if SymExpr.cmp b a == .lt then .bin .add .w64 b a
      else .bin .add .w64 a b

/-- Non-recursive helper for 64-bit addition canonicalization (constant folding/pulling,
identity elimination, `x + x → x << 1`, and `lea` scale `*3/*5/*9` normalization). -/
def mkAdd64 (a b : SymExpr) : SymExpr :=
  match a, b with
  | .imm va, .imm vb => .imm (va + vb)
  | a, .imm 0 => a
  | .imm 0, b => b
  | .bin .add .w64 x (.imm c1), .imm c2 =>
      let c := c1 + c2
      if c == 0 then x else .bin .add .w64 x (.imm c)
  | .imm c1, .bin .add .w64 y (.imm c2) =>
      let c := c1 + c2
      if c == 0 then y else .bin .add .w64 y (.imm c)
  | .bin .add .w64 x (.imm c1), .bin .add .w64 y (.imm c2) =>
      let core := mkAdd64Core x y
      let c := c1 + c2
      if c == 0 then core else .bin .add .w64 core (.imm c)
  | .bin .add .w64 x (.imm c1), y =>
      .bin .add .w64 (mkAdd64Core x y) (.imm c1)
  | x, .bin .add .w64 y (.imm c2) =>
      .bin .add .w64 (mkAdd64Core x y) (.imm c2)
  | a, b => mkAdd64Core a b

/-- Match a single-width or masked-32-bit `(x >>> r1) ||| (x <<< r2)` rotate-right pair
in `(shr, shl)` order, returning `(rotWidth, x, r1)` when `0 < r1 < rotWidth.bits` and
`r1 + r2 = rotWidth.bits`. -/
def matchRotateShrShl (w : Width) (s1 s2 : SymExpr) : Option (Width × SymExpr × Word) :=
  match s1, s2 with
  | .bin .shr w1 x1 (.imm c1), .bin .shl w2 x2 (.imm c2) =>
      if w1 == w && w2 == w && x1 == x2 then
        let r1 := (c1 &&& shiftMask w).toNat
        let r2 := (c2 &&& shiftMask w).toNat
        if 0 < r1 && r1 < w.bits && r1 + r2 == w.bits then
          some (w, x1, UInt64.ofNat r1)
        else none
      else if w == .w64 && w1 == .w32 && w2 == .w32 && x1 == x2 then
        let r1 := (c1 &&& shiftMask .w32).toNat
        let r2 := (c2 &&& shiftMask .w32).toNat
        if 0 < r1 && r1 < 32 && r1 + r2 == 32 then
          some (.w32, x1, UInt64.ofNat r1)
        else none
      else none
  | .bin .shr .w64 (.bin .and .w64 x1 (.imm m1)) (.imm c1),
    .bin .and .w64 (.bin .shl .w64 x2 (.imm c2)) (.imm m2) =>
      if w == .w64 && m1 == 0xffffffff && m2 == 0xffffffff &&
         (x2 == x1 || x2 == .bin .and .w64 x1 (.imm 0xffffffff)) then
        let r1 := (c1 &&& 63).toNat
        let r2 := (c2 &&& 63).toNat
        if 0 < r1 && r1 < 32 && r1 + r2 == 32 then
          some (.w32, x1, UInt64.ofNat r1)
        else none
      else none
  | _, _ => none

/-- Match a rotate-right pair in either operand order of `.or`. -/
def matchRotateOr (w : Width) (a b : SymExpr) : Option (Width × SymExpr × Word) :=
  match matchRotateShrShl w a b with
  | some res => some res
  | none => matchRotateShrShl w b a

/-- Match `((x & 0xffffffff) >>> r1) ||| (x <<< r2)` (in `(shr, shl)` order) under an
outer `& 0xffffffff` mask as 32-bit `ror`. -/
def matchRotateMasked32Pair (s1 s2 : SymExpr) : Option (SymExpr × Word) :=
  match s1, s2 with
  | .bin .shr .w64 (.bin .and .w64 x1 (.imm m1)) (.imm c1),
    .bin .shl .w64 x2 (.imm c2) =>
      if m1 == 0xffffffff && (x2 == x1 || x2 == .bin .and .w64 x1 (.imm 0xffffffff)) then
        let r1 := (c1 &&& 63).toNat
        let r2 := (c2 &&& 63).toNat
        if 0 < r1 && r1 < 32 && r1 + r2 == 32 then
          some (x1, UInt64.ofNat r1)
        else none
      else none
  | _, _ => none

/-- Match `(((x & 0xffffffff) >>> r1) ||| (x <<< r2)) & 0xffffffff` in either order. -/
def matchRotateMasked32 (e : SymExpr) : Option (SymExpr × Word) :=
  match e with
  | .bin .or .w64 a b =>
      match matchRotateMasked32Pair a b with
      | some res => some res
      | none => matchRotateMasked32Pair b a
  | _ => none

/-- Single-step normalizer for `.bin o w a b` on already ordered, normalized operands `a, b`. -/
def mkBinOrdered (o : BinOp) (w : Width) (a b : SymExpr) : SymExpr :=
  -- Constant folding
  match a, b with
  | .imm va, .imm vb =>
      match o.eval w va vb with
      | some v => .imm v
      | none => .bin o w a b
  | _, _ =>
    match o with
    | .add =>
        match w with
        | .w64 => mkAdd64 a b
        | _ =>
            if a == b then .bin .shl w a (.imm 1)
            else .bin .add w a b
    | .sub =>
        if a == b then .imm 0
        else match w, a, b with
        | .w64, a, .imm k =>
            if k == 0 then a
            else mkAdd64 a (.imm (0 - k))
        | _, _, _ => .bin .sub w a b
    | .mul =>
        match a, b with
        | _, .imm 0 => .imm 0
        | a, .imm 1 => if w == .w64 then a else .bin .mul w a (.imm 1)
        | a, .imm k =>
            match findPow2 w k with
            | some sh => .bin .shl w a (.imm (UInt64.ofNat sh))
            | none => .bin .mul w a (.imm k)
        | _, _ => .bin .mul w a b
    | .and =>
        match a, b with
        | _, .imm 0 => .imm 0
        | a, .imm k =>
            if w == .w64 && k == w.mask then a
            else if w == .w64 && k == 0xffffffff then
              match matchRotateMasked32 a with
              | some (x, r) => .bin .ror .w32 x (.imm r)
              | none => .bin .and w a (.imm k)
            else .bin .and w a (.imm k)
        | _, _ =>
            if w == .w64 && a == b then a else .bin .and w a b
    | .or =>
        match a, b with
        | a, .imm 0 => if w == .w64 then a else .bin .or w a (.imm 0)
        | _, .imm k =>
            if w.truncate k == w.mask then .imm w.mask
            else if w == .w64 && k == 1 then
              match a with
              | .bin .shl .w64 _ (.imm s) =>
                  if (s &&& 63) != 0 then mkAdd64 a (.imm 1)
                  else .bin .or w a (.imm k)
              | _ => .bin .or w a (.imm k)
            else .bin .or w a (.imm k)
        | _, _ =>
            if w == .w64 && a == b then a
            else match matchRotateOr w a b with
            | some (rw, x, r) => .bin .ror rw x (.imm r)
            | none => .bin .or w a b
    | .xor =>
        if a == b then .imm 0
        else match w, a, b with
        | .w64, a, .imm 0 => a
        | _, _, _ => .bin .xor w a b
    | .shl =>
        match a, b with
        | .imm 0, _ => .imm 0
        | a, .imm k =>
            if w == .w64 && (k &&& shiftMask .w64) == 0 then a
            else .bin .shl w a (.imm (k &&& shiftMask w))
        | _, _ => .bin .shl w a b
    | .shr =>
        match a, b with
        | .imm 0, _ => .imm 0
        | a, .imm k =>
            if w == .w64 && (k &&& shiftMask .w64) == 0 then a
            else .bin .shr w a (.imm (k &&& shiftMask w))
        | _, _ => .bin .shr w a b
    | .sar =>
        match a, b with
        | .imm 0, _ => .imm 0
        | a, .imm k =>
            if w == .w64 && (k &&& shiftMask .w64) == 0 then a
            else .bin .sar w a (.imm (k &&& shiftMask w))
        | _, _ => .bin .sar w a b
    | .rol =>
        match a, b with
        | .imm 0, _ => .imm 0
        | a, .imm k =>
            if w == .w64 && (k &&& shiftMask .w64) == 0 then a
            else .bin .rol w a (.imm (k &&& shiftMask w))
        | _, _ => .bin .rol w a b
    | .ror =>
        match a, b with
        | .imm 0, _ => .imm 0
        | a, .imm k =>
            if w == .w64 && (k &&& shiftMask .w64) == 0 then a
            else .bin .ror w a (.imm (k &&& shiftMask w))
        | _, _ => .bin .ror w a b
    | .udiv =>
        match a, b with
        | a, .imm k =>
            let d := w.truncate k
            if d == 1 then (if w == .w64 then a else .bin .and w a (.imm w.mask))
            else match findPow2 w k with
            | some sh => .bin .shr w a (.imm (UInt64.ofNat sh))
            | none => .bin .udiv w a (.imm k)
        | _, _ => .bin .udiv w a b
    | .urem =>
        match a, b with
        | _, .imm k =>
            let d := w.truncate k
            if d == 1 then .imm 0
            else match findPow2 w k with
            | some sh => .bin .and w a (.imm (UInt64.ofNat (2 ^ sh - 1)))
            | none => .bin .urem w a (.imm k)
        | _, _ => .bin .urem w a b

/-- Smart constructor / single-step normalizer for `.bin o w a b` on already
normalized operands `a, b`. Every rewrite preserves `eval` whenever the input
does not get stuck. -/
def mkBin (o : BinOp) (w : Width) (a b : SymExpr) : SymExpr :=
  if binOpIsComm o && SymExpr.cmp b a == .lt then mkBinOrdered o w b a
  else mkBinOrdered o w a b

/-- Bottom-up canonical normalizer for `SymExpr`. -/
def SymExpr.norm : SymExpr → SymExpr
  | .reg x => .reg x
  | .imm w => .imm w
  | .ctx => .ctx
  | .bin o w a b => mkBin o w a.norm b.norm
  | .select c w a b t f =>
      let a' := a.norm; let b' := b.norm; let t' := t.norm; let f' := f.norm
      let (c', a', b') := if SymExpr.cmp b' a' == .lt then (condSwap c, b', a') else (c, a', b')
      if t' == f' then t'
      else match condStatic c' w a' b' with
      | some true => t'
      | some false => f'
      | none => .select c' w a' b' t' f'
  | .test c w a b =>
      let a' := a.norm; let b' := b.norm
      let (c', a', b') := if SymExpr.cmp b' a' == .lt then (condSwap c, b', a') else (c, a', b')
      match condStatic c' w a' b' with
      | some true => .imm 1
      | some false => .imm 0
      | none => .test c' w a' b'
  | .bsr64 a =>
      match a.norm with
      | .imm va => if va == 0 then .bsr64 (.imm va) else .imm (UInt64.ofNat va.toNat.log2)
      | a' => .bsr64 a'
  | .mulHi a b =>
      let a' := a.norm; let b' := b.norm
      let (a', b') := if SymExpr.cmp b' a' == .lt then (b', a') else (a', b')
      match a', b' with
      | .imm va, .imm vb => .imm (UInt64.ofNat ((va.toNat * vb.toNat) / 2 ^ 64))
      | _, .imm 0 => .imm 0
      | _, .imm 1 => .imm 0
      | _, _ => .mulHi a' b'
  | .divQ hi lo d =>
      let hi' := hi.norm; let lo' := lo.norm; let d' := d.norm
      match hi', lo', d' with
      | .imm vhi, .imm vlo, .imm vd =>
          if vd.toNat == 0 || vd.toNat ≤ vhi.toNat then .divQ hi' lo' d'
          else .imm (UInt64.ofNat ((vhi.toNat * 2 ^ 64 + vlo.toNat) / vd.toNat))
      | _, _, _ => .divQ hi' lo' d'
  | .divR hi lo d =>
      let hi' := hi.norm; let lo' := lo.norm; let d' := d.norm
      match hi', lo', d' with
      | .imm vhi, .imm vlo, .imm vd =>
          if vd.toNat == 0 || vd.toNat ≤ vhi.toNat then .divR hi' lo' d'
          else .imm (UInt64.ofNat ((vhi.toNat * 2 ^ 64 + vlo.toNat) % vd.toNat))
      | _, _, _ => .divR hi' lo' d'
  | .addCLo a b c =>
      let a' := a.norm; let b' := b.norm; let c' := c.norm
      match a', b', c' with
      | .imm va, .imm vb, .imm vc =>
          let cin : Nat := if vc == 0 then 0 else 1
          .imm (va + vb + UInt64.ofNat cin)
      | _, _, _ => .addCLo a' b' c'
  | .addCHi a b c =>
      let a' := a.norm; let b' := b.norm; let c' := c.norm
      match a', b', c' with
      | .imm va, .imm vb, .imm vc =>
          let cin : Nat := if vc == 0 then 0 else 1
          .imm (if 2 ^ 64 ≤ va.toNat + vb.toNat + cin then 1 else 0)
      | _, _, _ => .addCHi a' b' c'
  | .subBLo a b c =>
      let a' := a.norm; let b' := b.norm; let c' := c.norm
      match a', b', c' with
      | .imm va, .imm vb, .imm vc =>
          let bin : Nat := if vc == 0 then 0 else 1
          .imm (va - vb - UInt64.ofNat bin)
      | _, _, _ => .subBLo a' b' c'
  | .subBHi a b c =>
      let a' := a.norm; let b' := b.norm; let c' := c.norm
      match a', b', c' with
      | .imm va, .imm vb, .imm vc =>
          let bin : Nat := if vc == 0 then 0 else 1
          .imm (if va.toNat < vb.toNat + bin then 1 else 0)
      | _, _, _ => .subBHi a' b' c'
  | .load snap w e addr => .load snap w e addr.norm

/-- Build the `SymExpr` for a `Lir.Addr` given an environment lookup `lookup`. -/
def addrToSym (lookup : VReg → SymExpr) (m : Addr) : SymExpr :=
  let baseExpr : SymExpr := match m.base with
    | none => .imm 0
    | some (.v x) => lookup x
    | some .ctx => .ctx
  let idxExpr : SymExpr := match m.index with
    | none => .imm 0
    | some (x, s) => mkBin .mul .w64 (lookup x) (.imm s.word)
  let sum1 := mkBin .add .w64 baseExpr idxExpr
  mkBin .add .w64 sum1 (.imm (dispWord m.disp))

/-- Build the `SymExpr` for an `Arg`. -/
def argToSym (lookup : VReg → SymExpr) : Arg → SymExpr
  | .v x => lookup x
  | .imm w => .imm w

/-- Build the `SymExpr` for an `Ovf` primary result. -/
def ovfToSym (o : Ovf) (a b : SymExpr) : SymExpr :=
  match o with
  | .addC => mkBin .add .w64 a b
  | .subB => mkBin .sub .w64 a b
  | .mulOvf => mkBin .mul .w64 a b

/-- Extract `mulHi` operands matching `a` and constant `m`, accounting for commutative ordering. -/
def matchMulHiConst (a : SymExpr) : SymExpr → Option Word
  | .mulHi x (.imm m) => if x == a then some m else none
  | .mulHi (.imm m) x => if x == a then some m else none
  | _ => none

/-- Match the 64-bit add-shift inner expression `((a - hi) >>> 1) + hi` (after `mkBin`
commutative ordering on `+`). Returns `(a, m')` if `hi = mulHi(a, m')`. -/
def matchAddShiftCore (a : SymExpr) (e : SymExpr) : Option Word :=
  let check (t hi : SymExpr) : Option Word :=
    match matchMulHiConst a hi with
    | none => none
    | some m' =>
        match t with
        | .bin .shr .w64 (.bin .sub .w64 a1 hi1) (.imm 1) =>
            if a1 == a && hi1 == hi then some m' else none
        | _ => none
  match e with
  | .bin .add .w64 lhs rhs =>
      match check lhs rhs with
      | some m' => some m'
      | none => check rhs lhs
  | _ => none

/-- Match the 32-bit simple multiply-shift expression `((a &&& 0xffffffff) * m) >>> (32 + s)`
(or `a * m` when `a` is already masked). Returns `(m, s)` if valid. -/
def matchMagic32Simple (a : SymExpr) (d : Word) (e : SymExpr) : Bool :=
  let a32 := mkBin .and .w64 a (.imm 0xffffffff)
  match e with
  | .bin .shr .w64 (.bin .mul .w64 u (.imm m)) (.imm sh) =>
      (u == a32) && (32 ≤ sh.toNat) && checkMagic32 d m (sh.toNat - 32)
  | .bin .shr .w64 (.bin .mul .w64 (.imm m) u) (.imm sh) =>
      (u == a32) && (32 ≤ sh.toNat) && checkMagic32 d m (sh.toNat - 32)
  | _ => false

/-- Match 32-bit add-shift `(((u - hi) >>> 1) + hi) >>> (s - 1)` where `u = a &&& 0xffffffff`
and `hi = (u * m') >>> 32`. -/
def matchMagic32AddShift (a : SymExpr) (d : Word) (e : SymExpr) : Bool :=
  let u := mkBin .and .w64 a (.imm 0xffffffff)
  let matchHi (hi : SymExpr) : Option Word :=
    match hi with
    | .bin .shr .w64 (.bin .mul .w64 u' (.imm m')) (.imm 32) => if u' == u then some m' else none
    | .bin .shr .w64 (.bin .mul .w64 (.imm m') u') (.imm 32) => if u' == u then some m' else none
    | _ => none
  let matchCore (core : SymExpr) : Option Word :=
    let check (t hi : SymExpr) : Option Word :=
      match matchHi hi with
      | none => none
      | some m' =>
          match t with
          | .bin .shr .w64 (.bin .sub .w64 u1 hi1) (.imm 1) =>
              if u1 == u && hi1 == hi then some m' else none
          | _ => none
    match core with
    | .bin .add .w64 lhs rhs =>
        match check lhs rhs with
        | some m' => some m'
        | none => check rhs lhs
    | _ => none
  match e with
  | .bin .shr .w64 core (.imm sh) =>
      match matchCore core with
      | some m' => checkMagic32AddShift d m' (sh.toNat + 1)
      | none => false
  | core =>
      match matchCore core with
      | some m' => checkMagic32AddShift d m' 1
      | none => false

/-- Check whether `e2` computes the exact unsigned quotient of `a` by constant `d` at width `w`. -/
def checkDivMagicExpr (w : Width) (a : SymExpr) (d : Word) (e2 : SymExpr) : Bool :=
  if e2 == mkBin .udiv w a (.imm d) then true
  else match w with
  | .w64 =>
      -- Case 1: mulHi(a, m) >>> s  (including s = 0 where shr was normalized away)
      let case1 : Bool := match e2 with
        | .bin .shr .w64 hi (.imm sh) =>
            match matchMulHiConst a hi with
            | some m => checkMagicSimple d m sh.toNat
            | none => false
        | hi =>
            match matchMulHiConst a hi with
            | some m => checkMagicSimple d m 0
            | none => false
      if case1 then true
      else
        -- Case 2: (((a - hi) >>> 1) + hi) >>> (s - 1)  (including s = 1)
        match e2 with
        | .bin .shr .w64 core (.imm sh) =>
            match matchAddShiftCore a core with
            | some m' => checkMagicAddShift d m' (sh.toNat + 1)
            | none => false
        | core =>
            match matchAddShiftCore a core with
            | some m' => checkMagicAddShift d m' 1
            | none => false
  | .w32 =>
      let dw := X86.Width.w32.truncate d
      matchMagic32Simple a dw e2 || matchMagic32AddShift a dw e2
  | _ => false

/-- Match `a - q * d` (modulo width `w`) against `urem w a (.imm d)`. -/
def checkRemMagicExpr (w : Width) (a : SymExpr) (d : Word) (e2 : SymExpr) : Bool :=
  let dw := w.truncate d
  if dw == 0 then false
  else
    let isMulD (p : SymExpr) : Option SymExpr :=
      match p with
      | .bin .mul w' q (.imm d') =>
          if w' == w && w.truncate d' == dw then some q else none
      | .bin .mul w' (.imm d') q =>
          if w' == w && w.truncate d' == dw then some q else none
      | .bin .shl w' q (.imm sh) =>
          if w' == w && isPow2 w d sh.toNat then some q else none
      | _ => none
    match e2 with
    | .bin .sub w' a' prod =>
        if w' == w && a' == a then
          match isMulD prod with
          | some q => checkDivMagicExpr w a d q
          | none => false
        else false
    | _ => false

/-- Structural congruence closure over normalized `SymExpr`s with Granlund–Montgomery
constant division and remainder equivalence leaves. -/
def exprEquivAux : SymExpr → SymExpr → Bool
  | .reg x, .reg y => x == y
  | .imm k1, .imm k2 => k1 == k2
  | .ctx, .ctx => true
  | .bin o1 w1 a1 b1, e2 =>
      let leafDiv : Bool :=
        match o1, b1 with
        | .udiv, .imm d => checkDivMagicExpr w1 a1 d e2
        | .urem, .imm d => checkRemMagicExpr w1 a1 d e2
        | _, _ => false
      if leafDiv then true
      else match e2 with
      | .bin o2 w2 a2 b2 =>
          o1 == o2 && w1 == w2 && exprEquivAux a1 a2 && exprEquivAux b1 b2
      | _ => false
  | .select c1 w1 a1 b1 t1 f1, .select c2 w2 a2 b2 t2 f2 =>
      c1 == c2 && w1 == w2 && exprEquivAux a1 a2 && exprEquivAux b1 b2 &&
      exprEquivAux t1 t2 && exprEquivAux f1 f2
  | .test c1 w1 a1 b1, .test c2 w2 a2 b2 =>
      c1 == c2 && w1 == w2 && exprEquivAux a1 a2 && exprEquivAux b1 b2
  | .bsr64 a1, .bsr64 a2 => exprEquivAux a1 a2
  | .mulHi a1 b1, .mulHi a2 b2 => exprEquivAux a1 a2 && exprEquivAux b1 b2
  | .divQ a1 b1 c1, .divQ a2 b2 c2 =>
      exprEquivAux a1 a2 && exprEquivAux b1 b2 && exprEquivAux c1 c2
  | .divR a1 b1 c1, .divR a2 b2 c2 =>
      exprEquivAux a1 a2 && exprEquivAux b1 b2 && exprEquivAux c1 c2
  | .addCLo a1 b1 c1, .addCLo a2 b2 c2 =>
      exprEquivAux a1 a2 && exprEquivAux b1 b2 && exprEquivAux c1 c2
  | .addCHi a1 b1 c1, .addCHi a2 b2 c2 =>
      exprEquivAux a1 a2 && exprEquivAux b1 b2 && exprEquivAux c1 c2
  | .subBLo a1 b1 c1, .subBLo a2 b2 c2 =>
      exprEquivAux a1 a2 && exprEquivAux b1 b2 && exprEquivAux c1 c2
  | .subBHi a1 b1 c1, .subBHi a2 b2 c2 =>
      exprEquivAux a1 a2 && exprEquivAux b1 b2 && exprEquivAux c1 c2
  | .load s1 w1 ex1 a1, .load s2 w2 ex2 a2 =>
      s1 == s2 && w1 == w2 && ex1 == ex2 && exprEquivAux a1 a2
  | _, _ => false

/-- Check semantic equivalence of two normalized `SymExpr`s (`e1` from source, `e2` from target).
Soundness: if `exprEquiv e1 e2 = true` and `e1.eval ρ ctx snaps = some v`,
then `e2.eval ρ ctx snaps = some v`. -/
def exprEquiv (e1 e2 : SymExpr) : Bool :=
  let n1 := e1.norm
  let n2 := e2.norm
  if n1 == n2 then true else exprEquivAux n1 n2

/-! ## Branch facts and unsigned 64-bit interval bounds -/

/-- A known boolean outcome of `c.holds w a b` on pure normalized `SymExpr`s. -/
structure PFact where
  cond : Cond
  width : Width
  lhs : SymExpr
  rhs : SymExpr
  result : Bool
  deriving DecidableEq, Repr, Inhabited

def PFact.isMemFree (f : PFact) : Bool := f.lhs.isMemFree && f.rhs.isMemFree

def PFact.vars (f : PFact) : List VReg := f.lhs.vars ++ f.rhs.vars

def PFact.subst (s : VReg → SymExpr) (f : PFact) : PFact :=
  { f with lhs := (f.lhs.subst s).norm, rhs := (f.rhs.subst s).norm }

/-! ## Exact LSB parity domain (`Parity`, `parityOf`) -/

/-- Exact least-significant-bit parity (`v &&& 1`) of a 64-bit word. -/
inductive Parity where
  | unknown
  | even
  | odd
  deriving DecidableEq, Repr, Inhabited

def Parity.xor : Parity → Parity → Parity
  | .even, p | p, .even => p
  | .odd, .odd => .even
  | _, _ => .unknown

def Parity.mul : Parity → Parity → Parity
  | .even, _ | _, .even => .even
  | .odd, .odd => .odd
  | _, _ => .unknown

def Parity.or : Parity → Parity → Parity
  | .odd, _ | _, .odd => .odd
  | .even, .even => .even
  | _, _ => .unknown

def Parity.and : Parity → Parity → Parity
  | .even, _ | _, .even => .even
  | .odd, .odd => .odd
  | _, _ => .unknown

def Parity.join : Parity → Parity → Parity
  | .even, .even => .even
  | .odd, .odd => .odd
  | _, _ => .unknown

def Parity.meet : Parity → Parity → Parity
  | .unknown, p | p, .unknown => p
  | .even, .even => .even
  | .odd, .odd => .odd
  | _, _ => .unknown

/-- Parity of `v` implied by `c.holds w v k = res`. -/
def parityFromCondImm (w : Width) (c : Cond) (k : Word) (res : Bool) : Parity :=
  let c' := if res then c else condNegate c
  let kt := w.truncate k
  match c' with
  | .tz => if kt &&& 1 == 1 then .even else .unknown
  | .tnz => if kt == 1 then .odd else .unknown
  | .eq => if kt &&& 1 == 0 then .even else .odd
  | _ => .unknown

/-- Whether `e0` appears as an operand anywhere inside a tree of 64-bit bitwise-ANDs. -/
def andContains (e0 : SymExpr) : SymExpr → Bool
  | .bin .and .w64 x y => x == e0 || y == e0 || andContains e0 x || andContains e0 y
  | _ => false

/-- Parity of `e0` implied by a single dominating `PFact` (including `--bignat`
combined fixnum checks `tnz (a &&& b &&& ...) 1 = true` and `(x &&& m) == k` with odd `m`). -/
def parityFromFact (e0 : SymExpr) (f : PFact) : Parity :=
  let fromSide (side : SymExpr) (c : Cond) (k : Word) : Parity :=
    if side == e0 then parityFromCondImm f.width c k f.result
    else match side with
    | .bin .and .w64 x (.imm m) =>
        if x == e0 && f.width == .w64 && (m &&& 1 == 1) then
          let c' := if f.result then c else condNegate c
          if c' == .eq then (if k &&& 1 == 0 then .even else .odd) else .unknown
        else .unknown
    | .bin .and .w64 x y =>
        if andContains e0 (.bin .and .w64 x y) && f.width == .w64 && k == 1 then
          let c' := if f.result then c else condNegate c
          if c' == .tnz then .odd else .unknown
        else .unknown
    | _ => .unknown
  match f.lhs, f.rhs with
  | l, .imm k => fromSide l f.cond k
  | .imm k, r => fromSide r (condSwap f.cond) k
  | _, _ => .unknown

/-- Compute a sound LSB parity for `e` from its structure and dominating `facts`. -/
def parityOf (facts : List PFact) (e : SymExpr) : Parity :=
  let base : Parity := match e with
    | .imm w => if w &&& 1 == 0 then .even else .odd
    | .bin .add .w64 a b | .bin .sub .w64 a b | .bin .xor .w64 a b =>
        (parityOf facts a).xor (parityOf facts b)
    | .bin .mul .w64 a b => (parityOf facts a).mul (parityOf facts b)
    | .bin .or .w64 a b => (parityOf facts a).or (parityOf facts b)
    | .bin .and .w64 a b => (parityOf facts a).and (parityOf facts b)
    | .bin .shl .w64 a (.imm k) =>
        if (k &&& 63) != 0 then .even else parityOf facts a
    | .select _ _ _ _ t f => (parityOf facts t).join (parityOf facts f)
    | _ => .unknown
  facts.foldl (init := base) fun acc f => acc.meet (parityFromFact e f)

/-! ## Fact-aware algebraic normalization (`normFacts`, `exprEquivFacts`) -/

/-- Match the tagged-polynomial identity `((x >>> 1) * (x - 1)) + x = (x >>> 1) * (x + 1) + 1`
(exact mod 2^64 for every odd 64-bit word `x`, used in `sfib`). -/
def matchSfibStep (facts : List PFact) (a b : SymExpr) : Option SymExpr :=
  let check (prod x : SymExpr) : Option SymExpr :=
    if parityOf facts x != .odd then none
    else
      let q := SymExpr.bin .shr .w64 x (.imm 1)
      let xm1 := mkAdd64 x (.imm (0 - 1))
      match prod with
      | .bin .mul .w64 p1 p2 =>
          if (p1 == q && p2 == xm1) || (p1 == xm1 && p2 == q) then
            some (mkAdd64 (mkBin .mul .w64 q (mkAdd64 x (.imm 1))) (.imm 1))
          else none
      | _ => none
  match check a b with
  | some r => some r
  | none => check b a

/-- Bottom-up fact-aware normalizer: performs `SymExpr.norm` plus parity-justified
rewrites (`even ||| 1 → even + 1` and odd `((x >>> 1) * (x - 1)) + x → (x >>> 1) * (x + 1) + 1`). -/
def SymExpr.normFacts (facts : List PFact) : SymExpr → SymExpr
  | .reg x => .reg x
  | .imm w => .imm w
  | .ctx => .ctx
  | .bin o w a b =>
      let a' := a.normFacts facts
      let b' := b.normFacts facts
      let res := mkBin o w a' b'
      match res with
      | .bin .or .w64 x (.imm 1) =>
          if parityOf facts x == .even then mkAdd64 x (.imm 1) else res
      | .bin .add .w64 (.bin .add .w64 p q) (.imm c) =>
          match matchSfibStep facts p q with
          | some r => mkAdd64 r (.imm c)
          | none => res
      | .bin .add .w64 p q =>
          (matchSfibStep facts p q).getD res
      | _ => res
  | .select c w a b t f =>
      SymExpr.norm (.select c w (a.normFacts facts) (b.normFacts facts)
        (t.normFacts facts) (f.normFacts facts))
  | .test c w a b =>
      SymExpr.norm (.test c w (a.normFacts facts) (b.normFacts facts))
  | .bsr64 a => SymExpr.norm (.bsr64 (a.normFacts facts))
  | .mulHi a b => SymExpr.norm (.mulHi (a.normFacts facts) (b.normFacts facts))
  | .divQ hi lo d => SymExpr.norm (.divQ (hi.normFacts facts) (lo.normFacts facts) (d.normFacts facts))
  | .divR hi lo d => SymExpr.norm (.divR (hi.normFacts facts) (lo.normFacts facts) (d.normFacts facts))
  | .addCLo a b c => SymExpr.norm (.addCLo (a.normFacts facts) (b.normFacts facts) (c.normFacts facts))
  | .addCHi a b c => SymExpr.norm (.addCHi (a.normFacts facts) (b.normFacts facts) (c.normFacts facts))
  | .subBLo a b c => SymExpr.norm (.subBLo (a.normFacts facts) (b.normFacts facts) (c.normFacts facts))
  | .subBHi a b c => SymExpr.norm (.subBHi (a.normFacts facts) (b.normFacts facts) (c.normFacts facts))
  | .load s w e a => .load s w e (a.normFacts facts)

/-- Fact-aware semantic equivalence check between two `SymExpr`s. -/
def exprEquivFacts (facts : List PFact) (e1 e2 : SymExpr) : Bool :=
  if exprEquiv e1 e2 then true
  else exprEquiv (e1.normFacts facts) (e2.normFacts facts)

/-! ## Condition unwrapping (`select`/`test` and odd `(x & 3) == 1`) -/

/-- Unwrap `eq/ne (select sc sw sa sb kt kf) k` or `eq/ne (test sc sw sa sb) k` into
an equivalent direct comparison `(sc', sw, sa, sb)`. -/
def unwrapSelectCond (c : Cond) (w : Width) (a b : SymExpr) :
    Option (Cond × Width × SymExpr × SymExpr) :=
  if w != .w64 || (c != .eq && c != .ne) then none
  else
    let check (e : SymExpr) (k : Word) : Option (Cond × Width × SymExpr × SymExpr) :=
      match e with
      | .select sc sw sa sb (.imm kt) (.imm kf) =>
          if kt == k && kf != k then
            some (if c == .eq then sc else condNegate sc, sw, sa, sb)
          else if kf == k && kt != k then
            some (if c == .eq then condNegate sc else sc, sw, sa, sb)
          else none
      | .test sc sw sa sb =>
          if k == 1 then
            some (if c == .eq then sc else condNegate sc, sw, sa, sb)
          else if k == 0 then
            some (if c == .eq then condNegate sc else sc, sw, sa, sb)
          else none
      | _ => none
    match a, b with
    | e, .imm k => check e k
    | .imm k, e => check e k
    | _, _ => none

/-- For provably odd `x`, rewrite `(x &&& 3) == 1` / `!= 3` to `tz x 2` and
`(x &&& 3) != 1` / `== 3` to `tnz x 2`. -/
def unwrapOddBit2 (facts : List PFact) (c : Cond) (w : Width) (a b : SymExpr) :
    Option (Cond × Width × SymExpr × SymExpr) :=
  if w != .w64 || (c != .eq && c != .ne) then none
  else
    let check (e : SymExpr) (k : Word) : Option (Cond × Width × SymExpr × SymExpr) :=
      match e with
      | .bin .and .w64 x (.imm 3) =>
          if (k == 1 || k == 3) && parityOf facts x == .odd then
            let isTz := (c == .eq && k == 1) || (c == .ne && k == 3)
            some (if isTz then .tz else .tnz, .w64, x, .imm 2)
          else none
      | _ => none
    match a, b with
    | e, .imm k => check e k
    | .imm k, e => check e k
    | _, _ => none

/-! ## Unsigned 64-bit interval bounds -/

/-- Unsigned 64-bit inclusive range `[lo, hi]` with `lo ≤ hi < 2^64` (empty if `hi < lo`). -/
structure URange where
  lo : Nat := 0
  hi : Nat := 2 ^ 64 - 1
  deriving DecidableEq, Repr, Inhabited

def URange.inter (a b : URange) : URange := ⟨max a.lo b.lo, min a.hi b.hi⟩

/-- Narrow a range of `x` given `c.holds .w64 x k = res` (including endpoint tightening for `.ne`). -/
def URange.refineRight (r : URange) (c : Cond) (k : Word) (res : Bool) : URange :=
  let c' := if res then c else condNegate c
  let kn := k.toNat
  match c' with
  | .eq => r.inter ⟨kn, kn⟩
  | .ne =>
      if r.lo == kn && kn + 1 < 2 ^ 64 then r.inter ⟨kn + 1, 2 ^ 64 - 1⟩
      else if r.hi == kn && kn > 0 then r.inter ⟨0, kn - 1⟩
      else r
  | .ult => if kn == 0 then ⟨1, 0⟩ else r.inter ⟨0, kn - 1⟩
  | .ule => r.inter ⟨0, kn⟩
  | .ugt => if kn + 1 ≥ 2 ^ 64 then ⟨1, 0⟩ else r.inter ⟨kn + 1, 2 ^ 64 - 1⟩
  | .uge => r.inter ⟨kn, 2 ^ 64 - 1⟩
  | _ => r

/-- Narrow a range of `x` given a non-immediate comparison `c.holds .w64 x y = res`. -/
def URange.refineNonImm (r : URange) (c : Cond) (res : Bool) : URange :=
  let c' := if res then c else condNegate c
  match c' with
  | .ult => r.inter ⟨0, 2 ^ 64 - 2⟩
  | .ugt => r.inter ⟨1, 2 ^ 64 - 1⟩
  | _ => r

/-- Narrow range endpoints `[lo, hi]` to agree with known LSB parity `p`. -/
def URange.refineParity (r : URange) (p : Parity) : URange :=
  if r.hi < r.lo then r
  else match p with
  | .unknown => r
  | .even =>
      let lo' := if r.lo % 2 == 1 then r.lo + 1 else r.lo
      let hi' := if r.hi % 2 == 1 then r.hi - 1 else r.hi
      ⟨lo', hi'⟩
  | .odd =>
      if r.hi == 0 then ⟨1, 0⟩
      else
        let lo' := if r.lo % 2 == 0 then r.lo + 1 else r.lo
        let hi' := if r.hi % 2 == 0 then r.hi - 1 else r.hi
        ⟨lo', hi'⟩

/-- Single pass refining `r0` for expression `e` against all w64 facts and parity `p`. -/
def refineRangeOnce (facts : List PFact) (e : SymExpr) (p : Parity) (r0 : URange) : URange :=
  facts.foldl (init := r0.refineParity p) fun acc f =>
    if f.width == .w64 then
      let acc1 := match f.lhs, f.rhs with
        | l, .imm k => if l == e then acc.refineRight f.cond k f.result else acc
        | .imm k, r => if r == e then acc.refineRight (condSwap f.cond) k f.result else acc
        | l, r =>
            let a1 := if l == e then acc.refineNonImm f.cond f.result else acc
            if r == e then a1.refineNonImm (condSwap f.cond) f.result else a1
      acc1.refineParity p
    else acc

/-- Compute a sound unsigned 64-bit interval `[lo, hi]` for `e` from `facts`
(with structural recursion on `e`). -/
def rangeOf (facts : List PFact) (e : SymExpr) : URange :=
  let base : URange := match e with
    | .imm w => ⟨w.toNat, w.toNat⟩
    | .bin .add .w64 a b =>
        let ra := rangeOf facts a
        let rb := rangeOf facts b
        -- Handle both non-wrapping addition and `x + dispWord (-k)` = `x - k`
        if ra.hi + rb.hi < 2 ^ 64 then ⟨ra.lo + rb.lo, ra.hi + rb.hi⟩
        else
          match b with
          | .imm k =>
              let neg := 2 ^ 64 - k.toNat
              if neg ≤ ra.lo && ra.hi < 2 ^ 64 then ⟨ra.lo - neg, ra.hi - neg⟩
              else {}
          | _ => {}
    | .bin .sub .w64 a b =>
        let ra := rangeOf facts a
        let rb := rangeOf facts b
        if rb.hi ≤ ra.lo then ⟨ra.lo - rb.hi, ra.hi - rb.lo⟩ else {}
    | .bin .mul .w64 a b =>
        let ra := rangeOf facts a
        let rb := rangeOf facts b
        if ra.hi * rb.hi < 2 ^ 64 then ⟨ra.lo * rb.lo, ra.hi * rb.hi⟩ else {}
    | .bin .shl .w64 a (.imm k) =>
        let s := (k &&& 63).toNat
        let ra := rangeOf facts a
        if ra.hi * 2 ^ s < 2 ^ 64 then ⟨ra.lo * 2 ^ s, ra.hi * 2 ^ s⟩ else {}
    | .bin .shr .w64 a (.imm k) =>
        let s := (k &&& 63).toNat
        let ra := rangeOf facts a
        ⟨ra.lo / 2 ^ s, ra.hi / 2 ^ s⟩
    | .bin .and .w64 a (.imm k) =>
        let ra := rangeOf facts a
        ⟨0, min ra.hi k.toNat⟩
    | .bin .or .w64 a (.imm k) =>
        let ra := rangeOf facts a
        ⟨max ra.lo k.toNat, min (2 ^ 64 - 1) (ra.hi + k.toNat)⟩
    | .select _ _ _ _ t f =>
        let rt := rangeOf facts t
        let rf := rangeOf facts f
        ⟨min rt.lo rf.lo, max rt.hi rf.hi⟩
    | _ => {}
  let p := parityOf facts e
  let r1 := refineRangeOnce facts e p base
  refineRangeOnce facts e p r1

/-- Check whether `c.holds w a b` is directly implied by a single fact `f`. -/
def factMatches (f : PFact) (c : Cond) (w : Width) (a b : SymExpr) : Option Bool :=
  if f.width != w then none
  else if f.lhs == a && f.rhs == b then
    if f.cond == c then some f.result
    else if f.cond == condNegate c then some (!f.result)
    else none
  else if f.lhs == b && f.rhs == a then
    if f.cond == condSwap c then some f.result
    else if f.cond == condNegate (condSwap c) then some (!f.result)
    else none
  else none

/-- Decide a 64-bit unsigned comparison from intervals `ra, rb`. -/
def condFromRanges (c : Cond) (ra rb : URange) : Option Bool :=
  if ra.hi < ra.lo || rb.hi < rb.lo then none
  else match c with
  | .ult => if ra.hi < rb.lo then some true else if rb.hi ≤ ra.lo then some false else none
  | .ule => if ra.hi ≤ rb.lo then some true else if rb.hi < ra.lo then some false else none
  | .ugt => if rb.hi < ra.lo then some true else if ra.hi ≤ rb.lo then some false else none
  | .uge => if rb.hi ≤ ra.lo then some true else if ra.hi < rb.lo then some false else none
  | .eq =>
      if ra.lo == ra.hi && rb.lo == rb.hi && ra.lo == rb.lo then some true
      else if ra.hi < rb.lo || rb.hi < ra.lo then some false
      else none
  | .ne =>
      if ra.hi < rb.lo || rb.hi < ra.lo then some true
      else if ra.lo == ra.hi && rb.lo == rb.hi && ra.lo == rb.lo then some false
      else none
  | _ => none

/-- Core decision procedure for `c.holds w a' b'` (on already-normalized `a', b'`). -/
def condFromFactsCore (facts : List PFact) (c : Cond) (w : Width) (a' b' : SymExpr) : Option Bool :=
  match condStatic c w a' b' with
  | some r => some r
  | none =>
    match facts.findSome? (fun f => factMatches f c w a' b') with
    | some r => some r
    | none =>
      let fromParity : Option Bool :=
        if c == .tz || c == .tnz then
          let x? : Option SymExpr :=
            if b' == .imm 1 then some a' else if a' == .imm 1 then some b' else none
          match x? with
          | some x =>
              match parityOf facts x with
              | .even => some (c == .tz)
              | .odd => some (c == .tnz)
              | .unknown => none
          | none => none
        else none
      match fromParity with
      | some r => some r
      | none =>
          if w == .w64 then condFromRanges c (rangeOf facts a') (rangeOf facts b')
          else none

/-- Decide `c.holds w a b` from static identities, direct facts, parity, interval bounds,
and `select`/`test` unwrapping. -/
def condFromFacts (facts : List PFact) (c : Cond) (w : Width) (a b : SymExpr) : Option Bool :=
  let a' := a.norm; let b' := b.norm
  match condFromFactsCore facts c w a' b' with
  | some r => some r
  | none =>
      match unwrapSelectCond c w a' b' with
      | some (c1, w1, a1, b1) => condFromFactsCore facts c1 w1 a1.norm b1.norm
      | none => none

/-- Decide whether `o.eval a b` is guaranteed not to overflow (`some false`) from `facts`. -/
def ovfFromFacts (facts : List PFact) (o : Ovf) (a b : SymExpr) : Option Bool :=
  let a' := a.norm; let b' := b.norm
  match a', b' with
  | .imm va, .imm vb => some (o.eval va vb).2
  | _, _ =>
    let ra := rangeOf facts a'
    let rb := rangeOf facts b'
    if ra.hi < ra.lo || rb.hi < rb.lo then none
    else match o with
    | .addC => if ra.hi + rb.hi < 2 ^ 64 then some false else none
    | .subB => if rb.hi ≤ ra.lo then some false else none
    | .mulOvf => if ra.hi * rb.hi < 2 ^ 64 then some false else none

/-! ## Intra-segment symbolic memory (store-to-load forwarding, load CSE, DSE) -/

/-- Structured base-plus-constant-displacement address form for sound non-aliasing. -/
inductive MemBase where
  | zero
  | ctx
  | expr (e : SymExpr)
  deriving DecidableEq, Repr, Inhabited

/-- Structured address when `index = none` and `disp` fits signed 32-bit; `none` otherwise. -/
structure ConstAddr where
  base : MemBase
  disp : Int
  deriving DecidableEq, Repr, Inhabited

/-- Extract a `ConstAddr` from a `Lir.Addr` when `index = none` and `disp` fits signed 32-bit. -/
def toConstAddr (lookup : VReg → SymExpr) (m : Addr) : Option ConstAddr :=
  if m.index.isSome || !decide (-2147483648 ≤ m.disp ∧ m.disp < 2147483648) then none
  else
    let b := match m.base with
      | none => .zero
      | some .ctx => .ctx
      | some (.v x) => .expr (lookup x).norm
    some ⟨b, m.disp⟩

/-- Two `ConstAddr` accesses are **must-alias** when they have the exact same base,
displacement, and width. -/
def constAddrSame (w1 : Width) (a1 : Option ConstAddr) (w2 : Width) (a2 : Option ConstAddr) : Bool :=
  w1 == w2 && a1.isSome && a1 == a2

/-- Two accesses are **must-disjoint** (guaranteed byte-disjoint modulo 2^64 for all
runtime base words!) when both have `ConstAddr` with identical base, i32 displacements,
and non-overlapping intervals `[d1, d1 + w1.bytes)` and `[d2, d2 + w2.bytes)`. -/
def constAddrDisjoint (w1 : Width) (a1 : Option ConstAddr) (w2 : Width) (a2 : Option ConstAddr) : Bool :=
  match a1, a2 with
  | some c1, some c2 =>
      c1.base == c2.base &&
      decide (-2147483648 ≤ c1.disp ∧ c1.disp < 2147483648) &&
      decide (-2147483648 ≤ c2.disp ∧ c2.disp < 2147483648) &&
      decide (c1.disp + (w1.bytes : Int) ≤ c2.disp ∨ c2.disp + (w2.bytes : Int) ≤ c1.disp)
  | _, _ => false

/-- One symbolic write entry in the segment write log (newest first). -/
structure MemWrite where
  width : Width
  addr : SymExpr
  caddr : Option ConstAddr
  val : SymExpr
  deriving DecidableEq, Repr, Inhabited

/-- Segment memory state: normalized write list (newest first). -/
abbrev SymMem := List MemWrite

/-- Drop the first exact-shadowed write `(w, ca)` from `ws`, stopping at any may-aliasing
write (cannot commute past a may-alias). -/
def dropShadowed (w : Width) (ca : Option ConstAddr) : List MemWrite → List MemWrite
  | [] => []
  | wr :: rest =>
      if constAddrSame w ca wr.width wr.caddr then rest
      else if constAddrDisjoint w ca wr.width wr.caddr then wr :: dropShadowed w ca rest
      else wr :: rest

/-- Record a store `(w, addr, ca, val)` into `sm`, absorbing any shadowed dead store. -/
def SymMem.write (sm : SymMem) (w : Width) (addr : SymExpr) (ca : Option ConstAddr)
    (val : SymExpr) : SymMem :=
  let entry : MemWrite := { width := w, addr := addr.norm, caddr := ca, val := val.norm }
  entry :: dropShadowed w ca sm

/-- Truncate/extend a stored expression `v` to match a load of width `w` and extension `e`.
Zero-extension at `w64` is identity; narrower zero-extension masks with `w.mask`.
Sign-extension is only forwarded when `v` is an immediate constant (or `w = .w64`). -/
def forwardVal (w : Width) (e : Ext) (v : SymExpr) : Option SymExpr :=
  match w, e with
  | .w64, _ => some v
  | _, .zero => some (mkBin .and .w64 v (.imm w.mask))
  | _, .sign =>
      match v with
      | .imm k => some (.imm (sext w (w.truncate k)))
      | _ => none

/-- Walk the segment write log to either forward a stored value (`Sum.inl expr`) or
return the minimal relevant write suffix (`Sum.inr ws`) after skipping all trailing
must-disjoint stores. -/
def SymMem.readAux (w : Width) (e : Ext) (ca : Option ConstAddr) :
    List MemWrite → Sum SymExpr (List MemWrite)
  | [] => .inr []
  | wr :: rest =>
      if constAddrSame w ca wr.width wr.caddr then
        match forwardVal w e wr.val with
        | some v => .inl v
        | none => .inr (wr :: rest)
      else if constAddrDisjoint w ca wr.width wr.caddr then
        readAux w e ca rest
      else
        .inr (wr :: rest)

/-- Check that two normalized write lists `ws1` and `ws2` produce identical byte memory
(matching entry-by-entry with equivalent width, address, and value). -/
def writesEquiv : List MemWrite → List MemWrite → Bool
  | [], [] => true
  | w1 :: r1, w2 :: r2 =>
      w1.width == w2.width &&
      exprEquiv w1.addr w2.addr &&
      exprEquiv w1.val w2.val &&
      writesEquiv r1 r2
  | _, _ => false

/-- Append-only snapshot table for a single straight-line segment. Entry `0` is always `[]`
(the segment-entry memory `mem₀`). -/
abbrev SnapTable := Array (List MemWrite)

def SnapTable.init : SnapTable := #[[]]

/-- Intern a normalized write suffix `ws` into `st`, reusing any equivalent existing entry. -/
def SnapTable.intern (st : SnapTable) (ws : List MemWrite) : Nat × SnapTable :=
  let rec find (i : Nat) : Option Nat :=
    match i with
    | 0 => none
    | i + 1 =>
        let idx := st.size - (i + 1)
        match st[idx]? with
        | some existing => if writesEquiv existing ws then some idx else find i
        | none => find i
  match find st.size with
  | some id => (id, st)
  | none => (st.size, st.push ws)

/-- Evaluate a load `(w, e, addr, ca)` in segment memory `sm` against snapshot table `st`,
performing store-to-load forwarding and load-CSE snapshot canonicalization. -/
def SymMem.read (sm : SymMem) (st : SnapTable) (w : Width) (e : Ext) (addr : SymExpr)
    (ca : Option ConstAddr) : SymExpr × SnapTable :=
  match SymMem.readAux w e ca sm with
  | .inl v => (v, st)
  | .inr ws =>
      let (id, st') := st.intern ws
      (.load id w e addr.norm, st')

/-- Check that two segment memory states produce identical final memory. -/
def symMemEquiv (sm1 sm2 : SymMem) : Bool :=
  writesEquiv sm1 sm2

end IxCC.Lir.Opt
