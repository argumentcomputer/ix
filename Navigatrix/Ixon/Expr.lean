import Navigatrix.Ixon.Serialize
import Navigatrix.Ixon.Uses

/-!
# Ixon expressions, v2

ix's alpha-invariant `Expr` with modes as first-class data on the
binder nodes: `lam` carries its binder `Uses`; `all` carries binder
`Uses` and result `Owned`. The Lean 4 fragment is `many` binders with
`shared` results (`Expr.leanFragment`).

Because the constructors are unified (no separate annotated variants),
v2 consumes **no new tags**: flags stay `0x0`–`0xB` and `0xC`–`0xF`
remain free (borrow node, region node, modal-inductive block). The
telescope encodings are ix's, with one mode byte per telescope binder:

- `lam`: `Tag4(LAM, n)`, then per binder `[uses:u8][type]`, then base —
  uses in the low 2 bits, values `0–3`.
- `all`: `Tag4(ALL, n)`, then per binder `[mode:u8][type]`, then base —
  `uses | owned <<< 2`, values `0–7`.

The v1→v2 reencoder is therefore mechanical: insert `0x03` (`many`)
per lam binder and `0x07` (`many`+`shared`) per all binder.

Decoding is strict beyond `Serialize`'s size canonicity: telescopes
must be nonempty and maximal (a decoded base may not repeat the
telescope's constructor), mode bytes must be in range, and `letE`'s
nonDep flag must be `0` or `1`.
-/

namespace Navigatrix.Ixon

/-- Expression in the Ixon v2 format. Alpha-invariant: names are
stripped, presentation metadata lives in the metadata arena (as in ix).
`str`/`nat` reference the blob table; `ref`/`recur` reference the refs
table with universe-table instantiation indices; `share` references the
sharing table. -/
inductive Expr where
  | sort : UInt64 → Expr
  | var : UInt64 → Expr
  | ref : UInt64 → Array UInt64 → Expr
  | recur : UInt64 → Array UInt64 → Expr
  | prj : UInt64 → UInt64 → Expr → Expr
  | str : UInt64 → Expr
  | nat : UInt64 → Expr
  | app : Expr → Expr → Expr
  | lam : Uses → Expr → Expr → Expr
  | all : Uses → Owned → Expr → Expr → Expr
  | letE : Bool → Expr → Expr → Expr → Expr
  | share : UInt64 → Expr
  deriving BEq, Repr, Inhabited, Hashable

namespace Expr

def FLAG_SORT : UInt8 := 0x0
def FLAG_VAR : UInt8 := 0x1
def FLAG_REF : UInt8 := 0x2
def FLAG_REC : UInt8 := 0x3
def FLAG_PRJ : UInt8 := 0x4
def FLAG_STR : UInt8 := 0x5
def FLAG_NAT : UInt8 := 0x6
def FLAG_APP : UInt8 := 0x7
def FLAG_LAM : UInt8 := 0x8
def FLAG_ALL : UInt8 := 0x9
def FLAG_LET : UInt8 := 0xA
def FLAG_SHARE : UInt8 := 0xB

/-- Collect a lambda telescope: binder (uses, type) list plus base. -/
def collectLam : Expr → List (Uses × Expr) × Expr
  | .lam u ty body =>
    let (bs, base) := collectLam body
    ((u, ty) :: bs, base)
  | e => ([], e)

/-- Collect a forall telescope: binder (uses, owned, type) list plus base. -/
def collectAll : Expr → List (Uses × Owned × Expr) × Expr
  | .all u o ty body =>
    let (bs, base) := collectAll body
    ((u, o, ty) :: bs, base)
  | e => ([], e)

/-- Collect an application spine (arguments in application order). -/
def collectApp : Expr → List Expr × Expr
  | .app f a =>
    let (args, base) := collectApp f
    (args ++ [a], base)
  | e => ([], e)

/-- The Lean 4 fragment: every binder `many`, every result `shared`. -/
def leanFragment : Expr → Bool
  | .lam .many d b => leanFragment d && leanFragment b
  | .lam .. => false
  | .all .many .shared d c => leanFragment d && leanFragment c
  | .all .. => false
  | .app f a => leanFragment f && leanFragment a
  | .prj _ _ e => leanFragment e
  | .letE _ t v b => leanFragment t && leanFragment v && leanFragment b
  | _ => true

end Expr

partial def putExpr : Expr → PutM Unit
  | .sort idx => putTag4 ⟨Expr.FLAG_SORT, idx⟩
  | .var idx => putTag4 ⟨Expr.FLAG_VAR, idx⟩
  | .ref refIdx univIdxs => do
    putTag4 ⟨Expr.FLAG_REF, univIdxs.size.toUInt64⟩
    putTag0 ⟨refIdx⟩
    for idx in univIdxs do putTag0 ⟨idx⟩
  | .recur recIdx univIdxs => do
    putTag4 ⟨Expr.FLAG_REC, univIdxs.size.toUInt64⟩
    putTag0 ⟨recIdx⟩
    for idx in univIdxs do putTag0 ⟨idx⟩
  | .prj typeRefIdx fieldIdx val => do
    putTag4 ⟨Expr.FLAG_PRJ, fieldIdx⟩
    putTag0 ⟨typeRefIdx⟩
    putExpr val
  | .str refIdx => putTag4 ⟨Expr.FLAG_STR, refIdx⟩
  | .nat refIdx => putTag4 ⟨Expr.FLAG_NAT, refIdx⟩
  | e@(.app _ _) => do
    let (args, base) := Expr.collectApp e
    putTag4 ⟨Expr.FLAG_APP, args.length.toUInt64⟩
    putExpr base
    for arg in args do putExpr arg
  | e@(.lam ..) => do
    let (bs, base) := Expr.collectLam e
    putTag4 ⟨Expr.FLAG_LAM, bs.length.toUInt64⟩
    for (u, ty) in bs do
      putU8 u.toBits
      putExpr ty
    putExpr base
  | e@(.all ..) => do
    let (bs, base) := Expr.collectAll e
    putTag4 ⟨Expr.FLAG_ALL, bs.length.toUInt64⟩
    for (u, o, ty) in bs do
      putU8 (u.toBits ||| (o.toBits <<< 2))
      putExpr ty
    putExpr base
  | .letE nonDep ty val body => do
    putTag4 ⟨Expr.FLAG_LET, if nonDep then 1 else 0⟩
    putExpr ty
    putExpr val
    putExpr body
  | .share idx => putTag4 ⟨Expr.FLAG_SHARE, idx⟩

partial def getExpr : GetM Expr := do
  let tag ← getTag4
  match tag.flag with
  | 0x0 => return .sort tag.size
  | 0x1 => return .var tag.size
  | 0x2 => do
    let refIdx := (← getTag0).size
    let mut univIdxs := #[]
    for _ in [0:tag.size.toNat] do
      univIdxs := univIdxs.push (← getTag0).size
    return .ref refIdx univIdxs
  | 0x3 => do
    let recIdx := (← getTag0).size
    let mut univIdxs := #[]
    for _ in [0:tag.size.toNat] do
      univIdxs := univIdxs.push (← getTag0).size
    return .recur recIdx univIdxs
  | 0x4 => do
    let typeRefIdx := (← getTag0).size
    let val ← getExpr
    return .prj typeRefIdx tag.size val
  | 0x5 => return .str tag.size
  | 0x6 => return .nat tag.size
  | 0x7 => do
    if tag.size == 0 then throw "getExpr: empty app spine"
    let base ← getExpr
    match base with
    | .app .. => throw "getExpr: non-canonical app base"
    | _ => pure ()
    let mut result := base
    for _ in [0:tag.size.toNat] do
      result := .app result (← getExpr)
    return result
  | 0x8 => do
    if tag.size == 0 then throw "getExpr: empty lam telescope"
    let mut binders : Array (Uses × Expr) := #[]
    for _ in [0:tag.size.toNat] do
      let mb ← getU8
      match Uses.ofBits? mb with
      | none => throw s!"getExpr: invalid lam mode byte {mb}"
      | some u => binders := binders.push (u, ← getExpr)
    let body ← getExpr
    match body with
    | .lam .. => throw "getExpr: non-canonical lam telescope"
    | _ => pure ()
    let mut result := body
    for (u, ty) in binders.reverse do
      result := .lam u ty result
    return result
  | 0x9 => do
    if tag.size == 0 then throw "getExpr: empty all telescope"
    let mut binders : Array (Uses × Owned × Expr) := #[]
    for _ in [0:tag.size.toNat] do
      let mb ← getU8
      if mb >= 8 then throw s!"getExpr: invalid all mode byte {mb}"
      match Uses.ofBits? (mb &&& 0x3), Owned.ofBits? (mb >>> 2) with
      | some u, some o => binders := binders.push (u, o, ← getExpr)
      | _, _ => throw s!"getExpr: invalid all mode byte {mb}"
    let body ← getExpr
    match body with
    | .all .. => throw "getExpr: non-canonical all telescope"
    | _ => pure ()
    let mut result := body
    for (u, o, ty) in binders.reverse do
      result := .all u o ty result
    return result
  | 0xA => do
    if tag.size > 1 then throw s!"getExpr: invalid letE nonDep {tag.size}"
    let nonDep := tag.size == 1
    let ty ← getExpr
    let val ← getExpr
    let body ← getExpr
    return .letE nonDep ty val body
  | 0xB => return .share tag.size
  | f => throw s!"getExpr: invalid flag {f}"

instance : Serialize Expr where
  put := putExpr
  get := getExpr

/-! Elaboration-time roundtrip and canonicity checks. -/

private def roundtrips (e : Expr) : Bool :=
  match (de (ser e) : Except String Expr) with
  | .ok e' => e' == e
  | .error _ => false

#guard roundtrips (.sort 0)
#guard roundtrips (.var 300)
#guard roundtrips (.ref 1 #[0, 2, 200])
#guard roundtrips (.recur 2 #[1])
#guard roundtrips (.prj 3 1 (.var 0))
#guard roundtrips (.str 5)
#guard roundtrips (.nat 7)
#guard roundtrips (.share 12)
#guard roundtrips (.lam .linear (.sort 0) (.var 0))
#guard roundtrips (.lam .many (.sort 0) (.lam .erased (.sort 1) (.var 1)))
#guard roundtrips
  (.all .many .shared (.sort 1) (.all .linear .unique (.var 0) (.var 1)))
#guard roundtrips (.app (.app (.var 0) (.var 1)) (.var 2))
#guard roundtrips (.letE true (.sort 0) (.var 2) (.app (.var 0) (.var 1)))
#guard roundtrips
  (.lam .affine (.all .erased .shared (.sort 0) (.sort 0)) (.share 3))

private def rejects (bytes : Array UInt8) : Bool :=
  match (de (ByteArray.mk bytes) : Except String Expr) with
  | .ok _ => false
  | .error _ => true

-- empty lam telescope (LAM tag, count 0, then var 0)
#guard rejects #[0x80, 0x10]
-- lam mode byte out of range (LAM count 1, mode 0x04, sort 0, var 0)
#guard rejects #[0x81, 0x04, 0x00, 0x10]
-- all mode byte out of range (ALL count 1, mode 0x08, sort 0, var 0)
#guard rejects #[0x91, 0x08, 0x00, 0x10]
-- non-minimal var size (large form for a size that fits small form)
#guard rejects #[0x18, 0x05]
-- letE with nonDep flag 2
#guard rejects #[0xA2, 0x00, 0x10, 0x10]
-- trailing bytes after a complete term
#guard rejects #[0x10, 0x10]

end Navigatrix.Ixon
