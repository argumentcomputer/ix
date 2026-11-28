import IxCC.Ixon.V3.Env
import IxCC.Ixon.V3.Keys
import IxCC.Ixon.V3.Support

/-! The in-memory environment builder of the tests: synthesized Ixon v5 records
(`record`, `recordRaw`, `completeBinders`, `store`, `block`, which adds a
mutual block's projection records), a small axiom base, and an unbound (`0xE4`)
writer (`bytes`). The role-bound builder (`IxCCTests.Support.Bound`) encodes
its records here too. Every record finalized by `record` carries a complete
binder-data section (`Constant.bindersComplete`) unless explicit `binders` were
supplied; `recordRaw` encodes verbatim for negative tests. The byte writer is
test-only; production admission always reads bytes. -/

namespace IxCCTests.IxonV3.Builder

open IxCC.Ixon IxCC.Ixon.V3

abbrev E := IxCC.Ixon.V3.Expr
abbrev C := IxCC.Ixon.V3.Constant
abbrev Environment := IxCC.Ixon.V3.Env

def arrow (a b : E) : E := .all a b
def lambda (a b : E) : E := .lam a b
def letVal (nonDep : Bool) (mode : BinderMode := .many) (t v b : E) : E :=
  .letE nonDep (.value mode) t v b
def letBorrow (nonDep : Bool) (t v b : E) : E :=
  .letE nonDep .borrow t v b

/-- The numbered nodes of `e` in pre-order (`none` for `lam`/`all`, `some n`
for a binderful `share n`), mirroring `Ixon.Expr.numberedNodes`. -/
def numberedNodes (full : Array Bool) : E → Array (Option Nat) → Array (Option Nat)
  | .lam t b, acc => numberedNodes full b (numberedNodes full t (acc.push none))
  | .all t b, acc => numberedNodes full b (numberedNodes full t (acc.push none))
  | .app f a, acc => numberedNodes full a (numberedNodes full f acc)
  | .letE _ _ t v b, acc =>
      numberedNodes full b (numberedNodes full v (numberedNodes full t acc))
  | .prj _ _ v, acc => numberedNodes full v acc
  | .share n, acc => if full[n.toNat]?.getD false then acc.push (some n.toNat) else acc
  | _, acc => acc

/-- Strict `(shared, index, variant)` block order matching `Ixon.BinderBlock.keyLt`. -/
def blockKeyLt (a b : BinderBlock) : Bool :=
  (!a.shared && b.shared) ||
    (a.shared == b.shared &&
      (a.index < b.index || (a.index == b.index && a.variant < b.variant)))

private structure BuildState where
  shareVariants : Array (Array (Array BinderNode))
  blocks : Array BinderBlock
  seen : Std.HashMap (Nat × UInt64) UInt64 := {}

private def buildExprNodes (c : C) (full : Array Bool) (unchecked : Bool)
    (nodeOf : BinderPos → BinderNode) (shareHint : BinderPos → Option UInt64) :
    Nat → Bool → UInt64 → UInt64 → E → BuildState → Array BinderNode × BuildState
  | 0, _, _, _, _, st => (#[], st)
  | fuel + 1, shared, index, variant, e, st => Id.run do
    let shape := numberedNodes full e #[]
    let mut nodes : Array BinderNode := Array.mkEmpty shape.size
    let mut st := st
    for h : ord in [0:shape.size] do
      let pos : BinderPos := ⟨shared, index, variant, ord⟩
      match shape[ord] with
      | none =>
        let raw := nodeOf pos
        let node := if unchecked then .undecided (raw.mode?.getD {}) else raw
        nodes := nodes.push node
      | some n =>
        let hint := (shareHint pos).getD 0
        match st.seen[(n, hint)]? with
        | some v =>
          nodes := nodes.push (.share v)
        | none =>
          let entry := c.sharing[n]?.getD (.sort 0)
          let (subNodes, st') := buildExprNodes c full unchecked nodeOf shareHint
            fuel true n.toUInt64 hint entry st
          st := st'
          let existing := st.shareVariants[n]?.getD #[]
          match existing.findIdx? (· == subNodes) with
          | some v =>
            st := { st with seen := st.seen.insert (n, hint) v.toUInt64 }
            nodes := nodes.push (.share v.toUInt64)
          | none =>
            let v := existing.size
            st := {
              shareVariants := st.shareVariants.set! n (existing.push subNodes)
              blocks := st.blocks.push
                { shared := true, index := n.toUInt64, variant := v.toUInt64, nodes := subNodes }
              seen := st.seen.insert (n, hint) v.toUInt64
            }
            nodes := nodes.push (.share v.toUInt64)
    return (nodes, st)

/-- Populate a complete, canonical, sorted v5 binder-data section for `c` using
`nodeOf` to choose each binder's node (coerced to `.undecided` on unsafe or
partial constants so `Constant.bindersComplete` holds). Optional `shareHint`
directs which variant index `nodeOf` sees for a binderful share occurrence;
identical variant node lists are deduplicated automatically. -/
def completeBindersWith (c : C) (nodeOf : BinderPos → BinderNode)
    (shareHint : BinderPos → Option UInt64 := fun _ => none) : C := Id.run do
  let roots := c.info.binderRoots
  if roots.isEmpty then
    return { c with binders := #[] }
  let full := c.binderfulEntries
  let unchecked := c.info.uncheckedSafety
  let fuel := c.sharing.size + 2
  let mut st : BuildState :=
    { shareVariants := Array.replicate c.sharing.size #[], blocks := #[] }
  for h : r in [0:roots.size] do
    let shape := numberedNodes full roots[r] #[]
    if shape.isEmpty then continue
    let (nodes, st') := buildExprNodes c full unchecked nodeOf shareHint
      fuel false r.toUInt64 0 roots[r] st
    st := { st' with
      blocks := st'.blocks.push
        { shared := false, index := r.toUInt64, variant := 0, nodes } }
  return { c with binders := st.blocks.qsort blockKeyLt }

/-- Populate a default complete binder-data section for `c` (all default modes;
`.never {}` for safe constants, `.undecided {}` for unsafe/partial). -/
def completeBinders (c : C) : C :=
  completeBindersWith c (fun _ => .never {})

/-- Populate a complete binder-data section for `c` with custom `AllMode`s per
`BinderPos` (and `.never` data on safe constants). -/
def withBinderModes (c : C) (modeOf : BinderPos → AllMode)
    (shareHint : BinderPos → Option UInt64 := fun _ => none) : C :=
  completeBindersWith c (fun p => .never (modeOf p)) shareHint

/-- Encode `c` verbatim without auto-completing `c.binders` (for negative or
hand-crafted section tests). -/
def recordRaw (c : C) : ByteArray × IxCC.Ixon.Address :=
  let raw := constantBytes c
  (raw, Address.blake3 raw)

/-- A synthesized record's bytes and content address: the one place the test
builders finish and encode a record (`store`, `block` and the role-bound
builder, `IxCCTests.Support.Bound`, all come here). Automatically completes
`c.binders` when `c.binders.isEmpty`. -/
def record (c : C) : ByteArray × IxCC.Ixon.Address :=
  let c' := if c.binders.isEmpty then completeBinders c else c
  recordRaw c'

def store (env : Environment) (c : C) : Environment × IxCC.Ixon.Address :=
  let (raw, address) := record c
  ({ env with consts := env.consts.insert address raw }, address)

def storeRaw (env : Environment) (c : C) : Environment × IxCC.Ixon.Address :=
  let (raw, address) := recordRaw c
  ({ env with consts := env.consts.insert address raw }, address)

/-- Canonical little-endian `Nat` literal blob bytes (`#[0]` for 0, no trailing
zero byte). -/
def canonicalNatBlob (n : Nat) : ByteArray := ⟨V3.natBytesLE n⟩

/-- Store an arbitrary blob at its pure BLAKE3 content address. -/
def storeBlob (env : Environment) (raw : ByteArray) : Environment × IxCC.Ixon.Address :=
  let address := Address.blake3 raw
  ({ env with blobs := env.blobs.insert address raw }, address)

def block (env : Environment) (c : C) : Environment × IxCC.Ixon.Address := Id.run do
  let (env, address) := store env c
  let mut env := env
  if let .muts members := c.info then
    for i in [:members.size] do
      let wrapper : V3.ConstantInfo := match members[i]! with
        | .defn _ => .dPrj ⟨i.toUInt64, address⟩
        | .indc _ => .iPrj ⟨i.toUInt64, address⟩
        | .recr _ => .rPrj ⟨i.toUInt64, address⟩
      env := (store env ⟨wrapper, #[], #[], #[], #[]⟩).1
      if let .indc ind := members[i]! then
        for j in [:ind.ctors.size] do
          env := (store env ⟨.cPrj ⟨i.toUInt64, j.toUInt64, address⟩, #[], #[], #[], #[]⟩).1
  return (env, address)

def axiomType : C := ⟨.axio ⟨false, 0, .sort 0⟩, #[], #[], #[.succ .zero], #[]⟩
def base : Environment × IxCC.Ixon.Address := store {} axiomType

def identity (a : IxCC.Ixon.Address) : C :=
  completeBinders ⟨.defn ⟨.defn, .safe, {}, 0, arrow (.ref 0 #[]) (.ref 0 #[]),
    lambda (.ref 0 #[]) (.var 0)⟩, #[], #[a], #[], #[]⟩

/-- Independent framing for constructing complete adversarial input files. -/
def bytes (env : Environment) : ByteArray := _root_.Ixon.runPut do
  let constants := env.consts.toArray.qsort (fun a b => a.1.cmpBytes b.1 == .lt)
  let blobs := env.blobs.toArray.qsort (fun a b => a.1.cmpBytes b.1 == .lt)
  _root_.Ixon.putTagN 4 0xE envVersion
  _root_.Ixon.putBytes (Merkle.rootCanonical (constants.map Prod.fst)).hash
  _root_.Ixon.putU8 0
  _root_.Ixon.putTagN 0 0 env.assumptions.size.toUInt64
  for address in env.assumptions do _root_.Ixon.putBytes address.hash
  for table in #[blobs, constants] do
    _root_.Ixon.putTagN 0 0 table.size.toUInt64
    for (address, raw) in table do
      _root_.Ixon.putBytes address.hash
      _root_.Ixon.putTagN 0 0 raw.size.toUInt64
      _root_.Ixon.putBytes raw
  _root_.Ixon.putTagN 0 0 0

end IxCCTests.IxonV3.Builder
