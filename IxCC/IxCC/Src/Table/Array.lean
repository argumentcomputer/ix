import IxCC.Src.Table.Check
import IxCC.Src.ArraySpec

/-!
# DR3 / DR4 Array, ByteArray & String Table Entries (`IxCC.Src.Table.Array`)

Unfolding-table equation builders and validators for DR3 `Array` / `ByteArray`
primitives and DR4 `String` representation bridges, mirroring
`IxCC.Src.Table.Word` so Wave 3 can wire them directly into `Src.Table.Check`
and `SrcEval` with zero rework.

For each pinned operation, `arrayEqnType` / `byteArrayEqnType` / `stringEqnType`
constructs the exact syntactic `IxCC.Src.Term` equation relating the operation
to its Lean 4.34.1 reference body (`Array.toList`, `ByteArray.data`,
`String.toByteArray`). `checkArrayOp` / `checkByteArrayOp` / `checkStringOp`
verify that:
1. the constant's address matches its pin in `ArrayPins`;
2. the proposed justification theorem `thm` is a safe theorem read with its
   proof (never `Program.byStatement`);
3. its statement fits `maxTermNodes` and is syntactically equivalent (`Term.eqv`)
   to the canonical reference-body equation;
4. its transitive constant closure passes `checkAxiomClosure` (standard axioms
   `[propext, Classical.choice, Quot.sound]` only).
-/

namespace IxCC.Src.Table

open IxCC.Ixon

/-- Pinned constant addresses for DR3 `Array` / `ByteArray` and DR4 `String`
table validation (supplied by Wave 3 from `Src.Pinned`). -/
structure ArrayPins where
  arrayType : Option Nat := none
  arrayMk : Option Nat := none
  arrayToList : Option Nat := none
  byteArrayType : Option Nat := none
  byteArrayMk : Option Nat := none
  byteArrayData : Option Nat := none
  stringType : Option Nat := none
  stringOfByteArray : Option Nat := none
  stringToByteArray : Option Nat := none
  listType : Option Nat := none
  listNil : Option Nat := none
  listCons : Option Nat := none
  listLength : Option Nat := none
  listConcat : Option Nat := none
  listDropLast : Option Nat := none
  listSet : Option Nat := none
  uint8Type : Option Nat := none
  uint64Type : Option Nat := none
  arrayOps : List (ArrayOp × Nat) := []
  byteArrayOps : List (ByteArrayOp × Nat) := []
  stringOps : List (StringOp × Nat) := []
  /-- Additional pinned `Array`/`ByteArray` variants in Lean 4.34.1 (`uget`/`uset`/`empty`/`swapIfInBounds`/`get!`/`set!`). -/
  arrayUget : Option Nat := none
  arrayUset : Option Nat := none
  arraySetBang : Option Nat := none
  arraySwapIfInBounds : Option Nat := none
  byteArrayEmpty : Option Nat := none
  byteArrayUget : Option Nat := none
  byteArrayUset : Option Nat := none
  byteArrayGetBang : Option Nat := none
  byteArraySetBang : Option Nat := none
  deriving Inhabited

/-- Exact Lean 4.34.1 Ixon v5 content addresses for `Array`, `ByteArray`, `String`, and `List`
(extracted via `ix addr-of` against the frozen Lean 4.34.1 prelude). -/
def ArrayPins.fixed : ArrayPins where
  arrayType := some 0x1a31b4f2797c86158ebf5401b11364b35cb1058ce4b0be81a29f167da2d1c06f
  arrayMk := some 0xc356c7e900e3853cb89a8dd81e459d31d17eb9e2d75ad23a0c77892ce3df02c2
  arrayToList := some 0x9f1ae95cb8cd9030b88c6e421e25ef6a1e2629ce9917427585aa00f829bd138c
  byteArrayType := some 0x6b445a78e86e8fce5ebf9cfd88f6e29ad42fabb3ff7d1c330e1bb67c5cabf817
  byteArrayMk := some 0x7b9e02fc85465ac6a3f62c910e4f4d21a95543e0b552dc3c4614e1b2a1363ec9
  byteArrayData := some 0x5adfaf5600ad7afcadd7dbac1848ba5dd95190de3918edebfa16cd02e6bb3aca
  stringType := some 0x9964f625c7e537f667af5c445f1c1cd4ea18d6094dd7b7083c49f59613566306
  stringOfByteArray := some 0x7b66454521da4be88795d96d021b712db573aa0bc848a02b3e9dd0b044bdbc1f
  stringToByteArray := some 0x6fabcaf163e83cf02d51624cade44120c65b6e5dc439578fe68eb1972870d1dc
  listType := some 0x487a90b33c7dcd5f3434aa04338e1a5b290552cbe922eeb59b025b1dcdbf5de0
  listNil := some 0xacc4102c8c32f222b755f3f15b5046484ca98618da9a4932143a9711786818fa
  listCons := some 0x63cc7dc0943c85e1d79b41c5ca23cbb5e080b67aec17e5c6bfca4fd0073e01ab
  listLength := some 0x4e86835f8ec37d0ed6edd9037f45d80d2a15034ed691eb71d8d661f6eea83b8f
  listConcat := some 0xedfad99820172f098102f6f052e869846802415cb4945e7ade00b76ca0665c22
  listDropLast := some 0xe8f9a98cfc2d2442c71ba70d09bb45a4079b44bf3111e74f9e96758468a688ce
  listSet := some 0xb96681cb5af57d060aa275332caca920408e675d27fe3716b1fa1ab7a8b3cf94
  uint8Type := some 0x93be7ce2ba5276dcfdc71099cb3d30f67a72965636ea4d24ceb7a845d2f52ca6
  uint64Type := some 0x7a31307b020bb907fa3c972dc19cdafcf213109498e9b124fd0466a71b429934
  arrayOps :=
    [ (.emptyWithCapacity, 0xd27013066dc5af007427fdaa0bd0f55b01483edb54343bdbca2c37cdb457b450),
      (.size,              0x981e548b7f36a9b6af5c5c5f257cb40b2999db0dc3ab103c242d1dc4dd877324),
      (.getInternal,       0x82bc2b6a0b914596e5e67905c7c377bd65c0e15768a40b0a2abda21c479c1725),
      (.set,               0xc1999b81eba0e71a0ffd0507d82d372353a7232d3e05d04eeb0b28798d6cbdbc),
      (.setIfInBounds,     0x6c64930c7f983effe131fef9da1202cd01c287649a95b2fd334d8d0d32e1727a),
      (.push,              0xb5dab32a8c14b54dab8d779860c45f90f4a7198980d5e1dbdd53ba8174641fe1),
      (.pop,               0xd0a0c0846201ca3b44f228dc60964fdaecfde5553149dd72f15330779e6cddbe),
      (.extract,           0xcae6f7dd5032e386f05d11a61292de91835e0eb7d357e66b5b29aba9eeed537a),
      (.swap,              0x814193a95739618f8281423f7870fae2837893bbb653c4ad1aa171db68513220) ]
  byteArrayOps :=
    [ (.emptyWithCapacity, 0x15d22788c97d2dba8589b1b22152c5bbdd4b6e9571d684677f65e851be0a16c6),
      (.size,              0xbbae44fa0a44e824e6dc66bb671a62d8b9f893471978e831f7a0bfe3a6c3c1bb),
      (.get,               0x5b984a8c14903ae52470346077d73b1d72be44214273f284f6ba7f288d62216b),
      (.set,               0xac24641561b9caedc194238770bdae323f0026f68492de75ffee6c4fb6378a80),
      (.push,              0x1470babb7696bcd82315672578fcf74412b3e539884e0b1b0ebb5250805a8c9e),
      (.extract,           0x780f0fb766e23024ed5e32c0f8134c1d56a914e7ee94504bde07618b4527e47a),
      (.copySlice,         0x86238da8a725fd1772de16308f851297f575d21761b02b28b756328c614ea996) ]
  stringOps :=
    [ (.ofByteArray,       0x7b66454521da4be88795d96d021b712db573aa0bc848a02b3e9dd0b044bdbc1f),
      (.toByteArray,       0x6fabcaf163e83cf02d51624cade44120c65b6e5dc439578fe68eb1972870d1dc),
      (.utf8ByteSize,      0xe47a3627ce6d979fee7b68a3aa86abf2b2b67b8eb24d4d984f10e284c2384d7a),
      (.getUTF8Byte,       0xb8fd36cd4088894ea229965651d3bc9098ef2e0bba20d2b8792bcb41604d190c),
      (.push,              0xa132a2632e8df55be75be7c18504e894b054d24a78149eabd7f7d425ad88b8a6),
      (.append,            0x606e3f9fd1b1cb9484145af8ee112dcf66fa3203f1ff11322ebd1f4f63403a3e) ]
  arrayUget := some 0x9ed45a07fbb57ed0a01de34d89ddfda9dee57cab443a5290ff42e2d7e04d4aff
  arrayUset := some 0x58513156fc461c6f6c98aa0251fd23fd4ce431fad5c91f7ebe41c9e7d681377e
  arraySetBang := some 0x958a938e434878babbae469ef71d5b0f99bddae74204780065770c5226cb1b07
  arraySwapIfInBounds := some 0xcd9a46c704443e11518248bd132fd60bf601881ca5076077016aef3a0cc8bc8a
  byteArrayEmpty := some 0xe2872f038c01610a4f78126ca7abe6573a57f717edf7b990ce01e3d32f60b991
  byteArrayUget := some 0xdd7dbdc6174a330b11e0579320133c309e55e4c6dfbab3cc36c5cb72319c9b49
  byteArrayUset := some 0x93790a22e9306a11e0821302e5aa5762c856326273404fb91ed8809446bf7cd5
  byteArrayGetBang := some 0x16c6c06a0543ca6bf9bf931fb72c5ec1b9cceafe81e83441533a05fa52f83fc6
  byteArraySetBang := some 0x9b309d7b0333eff77b955b0bd4bc26d8a71b7cf9dca98316ae124db5359e9ed7

def ArrayPins.arrayOp? (pins : ArrayPins) (op : ArrayOp) : Option Nat :=
  (pins.arrayOps.find? (·.1 == op)).map (·.2)

def ArrayPins.byteArrayOp? (pins : ArrayPins) (op : ByteArrayOp) : Option Nat :=
  (pins.byteArrayOps.find? (·.1 == op)).map (·.2)

def ArrayPins.stringOp? (pins : ArrayPins) (op : StringOp) : Option Nat :=
  (pins.stringOps.find? (·.1 == op)).map (·.2)

private def resolvePin (p : Program) (pin : Option Nat) : Option CId :=
  pin.bind fun n => p.lookup (Pinned.addrOfNat n)

private def appS (f a : Term) : Term := .app f a .strict .rel
private def app2S (f a b : Term) : Term := appS (appS f a) b
private def app3S (f a b c : Term) : Term := appS (app2S f a b) c

/-- `@Eq.{u+1} T a b`. -/
private def eqTerm (eqC : CId) (u : Univ) (T a b : Term) : Term :=
  app3S (.const eqC [.succ u]) T a b

/-- Canonical `Array` equation statement over `Array.toList` (universe param 0
for polymorphic element type `α : Type u`, or monomorphic `Nat` for `size`). -/
def arrayEqnType (p : Program) (pins : ArrayPins) (op : ArrayOp) : Option Term := do
  let natC ← p.known.nat
  let eqC ← p.known.eq
  let arrC ← resolvePin p pins.arrayType
  let toListC ← resolvePin p pins.arrayToList
  let listC ← resolvePin p pins.listType
  let opC ← resolvePin p (pins.arrayOp? op)
  let u : Univ := .var 0
  let u1 : Univ := .succ u
  let typeU : Term := .sort u1
  let natT : Term := .const natC []
  let arrT (a : Term) : Term := appS (.const arrC [u]) a
  let listT (a : Term) : Term := appS (.const listC [u]) a
  let toList (a xs : Term) : Term := app2S (.const toListC [u]) a xs
  match op with
  | .emptyWithCapacity =>
      let nilC ← resolvePin p pins.listNil
      -- ∀ (α : Type u) (c : Nat), Array.toList (Array.emptyWithCapacity c) = List.nil
      let lhs := toList (.var 1) (app2S (.const opC [u]) (.var 1) (.var 0))
      let rhs := appS (.const nilC [u]) (.var 1)
      pure (.pi {} typeU (.pi {} natT (eqTerm eqC u (listT (.var 1)) lhs rhs)))
  | .size =>
      let lenC ← resolvePin p pins.listLength
      -- ∀ (α : Type u) (a : Array α), Array.size a = List.length (Array.toList a)
      let lhs := app2S (.const opC [u]) (.var 1) (.var 0)
      let rhs := app2S (.const lenC [u]) (.var 1) (toList (.var 1) (.var 0))
      pure (.pi {} typeU (.pi {} (arrT (.var 0)) (eqTerm eqC .zero natT lhs rhs)))
  | .push =>
      let concatC ← resolvePin p pins.listConcat
      -- ∀ (α : Type u) (a : Array α) (v : α), Array.toList (Array.push a v) = List.concat (Array.toList a) v
      let lhs := toList (.var 2) (app3S (.const opC [u]) (.var 2) (.var 1) (.var 0))
      let rhs := app3S (.const concatC [u]) (.var 2) (toList (.var 2) (.var 1)) (.var 0)
      pure (.pi {} typeU (.pi {} (arrT (.var 0)) (.pi {} (.var 1)
        (eqTerm eqC u (listT (.var 2)) lhs rhs))))
  | .pop =>
      let dropLastC ← resolvePin p pins.listDropLast
      -- ∀ (α : Type u) (a : Array α), Array.toList (Array.pop a) = List.dropLast (Array.toList a)
      let lhs := toList (.var 1) (app2S (.const opC [u]) (.var 1) (.var 0))
      let rhs := app2S (.const dropLastC [u]) (.var 1) (toList (.var 1) (.var 0))
      pure (.pi {} typeU (.pi {} (arrT (.var 0)) (eqTerm eqC u (listT (.var 1)) lhs rhs)))
  | .setIfInBounds =>
      let setC ← resolvePin p pins.listSet
      -- ∀ (α : Type u) (a : Array α) (i : Nat) (v : α),
      --   Array.toList (Array.setIfInBounds a i v) = List.set (Array.toList a) i v
      let lhs := toList (.var 3) (appS (app3S (.const opC [u]) (.var 3) (.var 2) (.var 1)) (.var 0))
      let rhs := appS (app3S (.const setC [u]) (.var 3) (toList (.var 3) (.var 2)) (.var 1)) (.var 0)
      pure (.pi {} typeU (.pi {} (arrT (.var 0)) (.pi {} natT (.pi {} (.var 2)
        (eqTerm eqC u (listT (.var 3)) lhs rhs)))))
  | .getInternal | .set | .extract | .copySlice | .swap => none

/-- Canonical `ByteArray` equation statement over `ByteArray.data` (monomorphic). -/
def byteArrayEqnType (p : Program) (pins : ArrayPins) (op : ByteArrayOp) : Option Term := do
  let natC ← p.known.nat
  let eqC ← p.known.eq
  let baC ← resolvePin p pins.byteArrayType
  let baDataC ← resolvePin p pins.byteArrayData
  let arrC ← resolvePin p pins.arrayType
  let u8C ← resolvePin p pins.uint8Type
  let opC ← resolvePin p (pins.byteArrayOp? op)
  let natT : Term := .const natC []
  let baT : Term := .const baC []
  let u8T : Term := .const u8C []
  let arrU8T : Term := appS (.const arrC [.zero]) u8T
  let dataOf (b : Term) : Term := appS (.const baDataC []) b
  match op with
  | .emptyWithCapacity =>
      let arrEmptyC ← resolvePin p (pins.arrayOp? .emptyWithCapacity)
      -- ∀ (c : Nat), ByteArray.data (ByteArray.emptyWithCapacity c) = Array.emptyWithCapacity UInt8 0
      let lhs := dataOf (appS (.const opC []) (.var 0))
      let rhs := app2S (.const arrEmptyC [.zero]) u8T (.natLit 0)
      pure (.pi {} natT (eqTerm eqC .zero arrU8T lhs rhs))
  | .size =>
      let arrSizeC ← resolvePin p (pins.arrayOp? .size)
      -- ∀ (b : ByteArray), ByteArray.size b = Array.size UInt8 (ByteArray.data b)
      let lhs := appS (.const opC []) (.var 0)
      let rhs := app2S (.const arrSizeC [.zero]) u8T (dataOf (.var 0))
      pure (.pi {} baT (eqTerm eqC .zero natT lhs rhs))
  | .push =>
      let arrPushC ← resolvePin p (pins.arrayOp? .push)
      -- ∀ (b : ByteArray) (v : UInt8), ByteArray.data (ByteArray.push b v) = Array.push UInt8 (ByteArray.data b) v
      let lhs := dataOf (app2S (.const opC []) (.var 1) (.var 0))
      let rhs := app3S (.const arrPushC [.zero]) u8T (dataOf (.var 1)) (.var 0)
      pure (.pi {} baT (.pi {} u8T (eqTerm eqC .zero arrU8T lhs rhs)))
  | .get | .set | .extract | .copySlice => none

/-- Canonical `String` equation statement over `String.toByteArray` (monomorphic). -/
def stringEqnType (p : Program) (pins : ArrayPins) (op : StringOp) : Option Term := do
  let natC ← p.known.nat
  let eqC ← p.known.eq
  let strC ← resolvePin p pins.stringType
  let toBaC ← resolvePin p pins.stringToByteArray
  let opC ← resolvePin p (pins.stringOp? op)
  let natT : Term := .const natC []
  let strT : Term := .const strC []
  match op with
  | .utf8ByteSize =>
      let baSizeC ← resolvePin p (pins.byteArrayOp? .size)
      -- ∀ (s : String), String.utf8ByteSize s = ByteArray.size (String.toByteArray s)
      let lhs := appS (.const opC []) (.var 0)
      let rhs := appS (.const baSizeC []) (appS (.const toBaC []) (.var 0))
      pure (.pi {} strT (eqTerm eqC .zero natT lhs rhs))
  | .ofByteArray | .toByteArray | .getUTF8Byte | .push | .append => none

/-! ## Certified table validators -/

/-- Check an `Array` primitive entry `op` justified by stored theorem `thm`. -/
def checkArrayOp (pins : ArrayPins) (p : Program) (f : CId) (op : ArrayOp) (thm : CId) :
    Except String Unit := do
  unless some (Pinned.addrNat (p.addr f)) == pins.arrayOp? op do
    throw s!"array: {op.leanName} address is not the pinned one"
  let some expected := arrayEqnType p pins op
    | throw s!"array: missing pinned constants or unsupported equation for {op.leanName}"
  let some (.defn .thm .safe 1 ty _) := p.decl? thm
    | throw s!"array: equation for {op.leanName} is not a safe 1-level-polymorphic theorem"
  if p.byStatement.contains thm then
    throw s!"array: equation for {op.leanName} was read by statement without its proof"
  unless ty.nodesLe maxTermNodes do
    throw s!"array: equation for {op.leanName} exceeds node budget"
  unless ty.eqv expected do
    throw s!"array: theorem does not state {op.leanName}'s reference-body equation"
  checkAxiomClosure p thm

/-- Check a `ByteArray` primitive entry `op` justified by stored theorem `thm`. -/
def checkByteArrayOp (pins : ArrayPins) (p : Program) (f : CId) (op : ByteArrayOp) (thm : CId) :
    Except String Unit := do
  unless some (Pinned.addrNat (p.addr f)) == pins.byteArrayOp? op do
    throw s!"bytearray: {op.leanName} address is not the pinned one"
  let some expected := byteArrayEqnType p pins op
    | throw s!"bytearray: missing pinned constants or unsupported equation for {op.leanName}"
  let some (.defn .thm .safe 0 ty _) := p.decl? thm
    | throw s!"bytearray: equation for {op.leanName} is not a safe level-monomorphic theorem"
  if p.byStatement.contains thm then
    throw s!"bytearray: equation for {op.leanName} was read by statement without its proof"
  unless ty.nodesLe maxTermNodes do
    throw s!"bytearray: equation for {op.leanName} exceeds node budget"
  unless ty.eqv expected do
    throw s!"bytearray: theorem does not state {op.leanName}'s reference-body equation"
  checkAxiomClosure p thm

/-- Check a `String` primitive entry `op` justified by stored theorem `thm`. -/
def checkStringOp (pins : ArrayPins) (p : Program) (f : CId) (op : StringOp) (thm : CId) :
    Except String Unit := do
  unless some (Pinned.addrNat (p.addr f)) == pins.stringOp? op do
    throw s!"string: {op.leanName} address is not the pinned one"
  let some expected := stringEqnType p pins op
    | throw s!"string: missing pinned constants or unsupported equation for {op.leanName}"
  let some (.defn .thm .safe 0 ty _) := p.decl? thm
    | throw s!"string: equation for {op.leanName} is not a safe level-monomorphic theorem"
  if p.byStatement.contains thm then
    throw s!"string: equation for {op.leanName} was read by statement without its proof"
  unless ty.nodesLe maxTermNodes do
    throw s!"string: equation for {op.leanName} exceeds node budget"
  unless ty.eqv expected do
    throw s!"string: theorem does not state {op.leanName}'s reference-body equation"
  checkAxiomClosure p thm

/-! ## Validator soundness theorems -/

/-- Verified certificate extracted from a successful `checkArrayOp`. -/
structure ValidArrayEntry (pins : ArrayPins) (p : Program) (f : CId) (op : ArrayOp) (thm : CId) : Prop where
  pinned : some (Pinned.addrNat (p.addr f)) = pins.arrayOp? op
  eqn : ∃ expected ty val,
    arrayEqnType p pins op = some expected ∧
    p.decl? thm = some (.defn .thm .safe 1 ty val) ∧
    p.byStatement.contains thm = false ∧
    ty.eqv expected = true ∧
    checkAxiomClosure p thm = .ok ()

structure ValidByteArrayEntry (pins : ArrayPins) (p : Program) (f : CId) (op : ByteArrayOp) (thm : CId) : Prop where
  pinned : some (Pinned.addrNat (p.addr f)) = pins.byteArrayOp? op
  eqn : ∃ expected ty val,
    byteArrayEqnType p pins op = some expected ∧
    p.decl? thm = some (.defn .thm .safe 0 ty val) ∧
    p.byStatement.contains thm = false ∧
    ty.eqv expected = true ∧
    checkAxiomClosure p thm = .ok ()

structure ValidStringEntry (pins : ArrayPins) (p : Program) (f : CId) (op : StringOp) (thm : CId) : Prop where
  pinned : some (Pinned.addrNat (p.addr f)) = pins.stringOp? op
  eqn : ∃ expected ty val,
    stringEqnType p pins op = some expected ∧
    p.decl? thm = some (.defn .thm .safe 0 ty val) ∧
    p.byStatement.contains thm = false ∧
    ty.eqv expected = true ∧
    checkAxiomClosure p thm = .ok ()

theorem checkArrayOp_sound {pins : ArrayPins} {p : Program} {f : CId} {op : ArrayOp} {thm : CId}
    (h : checkArrayOp pins p f op thm = .ok ()) : ValidArrayEntry pins p f op thm := by
  unfold checkArrayOp at h
  by_cases hp : (some (Pinned.addrNat (p.addr f)) == pins.arrayOp? op) = true
  · simp only [hp, ↓reduceIte, bind, Except.bind] at h
    cases he : arrayEqnType p pins op with
    | none => simp [he, throw, throwThe, MonadExceptOf.throw] at h
    | some expected =>
      simp only [he] at h
      cases hd : p.decl? thm with
      | none => simp [hd, throw, throwThe, MonadExceptOf.throw] at h
      | some d =>
        simp only [hd] at h
        cases d with
        | defn k safety uparams ty val =>
          cases k <;> cases safety <;> cases uparams <;>
            try simp [throw, throwThe, MonadExceptOf.throw] at h
          case thm.safe.succ n =>
            cases n with
            | succ _ => simp at h
            | zero =>
              by_cases hbs : p.byStatement.contains thm = true
              · simp [hbs] at h
              · simp only [hbs] at h
                by_cases hsz : ty.nodesLe maxTermNodes = true
                · simp only [hsz, ↓reduceIte] at h
                  by_cases heqv : ty.eqv expected = true
                  · simp only [heqv, ↓reduceIte] at h
                    exact ⟨beq_iff_eq.mp hp, expected, ty, val, he, hd,
                      Bool.eq_false_iff.mpr hbs, heqv, h⟩
                  · simp [heqv] at h
                · simp [hsz] at h
        | _ => simp [throw, throwThe, MonadExceptOf.throw] at h
  · simp [hp, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

theorem checkByteArrayOp_sound {pins : ArrayPins} {p : Program} {f : CId} {op : ByteArrayOp} {thm : CId}
    (h : checkByteArrayOp pins p f op thm = .ok ()) : ValidByteArrayEntry pins p f op thm := by
  unfold checkByteArrayOp at h
  by_cases hp : (some (Pinned.addrNat (p.addr f)) == pins.byteArrayOp? op) = true
  · simp only [hp, ↓reduceIte, bind, Except.bind] at h
    cases he : byteArrayEqnType p pins op with
    | none => simp [he, throw, throwThe, MonadExceptOf.throw] at h
    | some expected =>
      simp only [he] at h
      cases hd : p.decl? thm with
      | none => simp [hd, throw, throwThe, MonadExceptOf.throw] at h
      | some d =>
        simp only [hd] at h
        cases d with
        | defn k safety uparams ty val =>
          cases k <;> cases safety <;> cases uparams <;>
            try simp [throw, throwThe, MonadExceptOf.throw] at h
          by_cases hbs : p.byStatement.contains thm = true
          · simp [hbs] at h
          · simp only [hbs] at h
            by_cases hsz : ty.nodesLe maxTermNodes = true
            · simp only [hsz, ↓reduceIte] at h
              by_cases heqv : ty.eqv expected = true
              · simp only [heqv, ↓reduceIte] at h
                exact ⟨beq_iff_eq.mp hp, expected, ty, val, he, hd,
                  Bool.eq_false_iff.mpr hbs, heqv, h⟩
              · simp [heqv] at h
            · simp [hsz] at h
        | _ => simp [throw, throwThe, MonadExceptOf.throw] at h
  · simp [hp, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

theorem checkStringOp_sound {pins : ArrayPins} {p : Program} {f : CId} {op : StringOp} {thm : CId}
    (h : checkStringOp pins p f op thm = .ok ()) : ValidStringEntry pins p f op thm := by
  unfold checkStringOp at h
  by_cases hp : (some (Pinned.addrNat (p.addr f)) == pins.stringOp? op) = true
  · simp only [hp, ↓reduceIte, bind, Except.bind] at h
    cases he : stringEqnType p pins op with
    | none => simp [he, throw, throwThe, MonadExceptOf.throw] at h
    | some expected =>
      simp only [he] at h
      cases hd : p.decl? thm with
      | none => simp [hd, throw, throwThe, MonadExceptOf.throw] at h
      | some d =>
        simp only [hd] at h
        cases d with
        | defn k safety uparams ty val =>
          cases k <;> cases safety <;> cases uparams <;>
            try simp [throw, throwThe, MonadExceptOf.throw] at h
          by_cases hbs : p.byStatement.contains thm = true
          · simp [hbs] at h
          · simp only [hbs] at h
            by_cases hsz : ty.nodesLe maxTermNodes = true
            · simp only [hsz, ↓reduceIte] at h
              by_cases heqv : ty.eqv expected = true
              · simp only [heqv, ↓reduceIte] at h
                exact ⟨beq_iff_eq.mp hp, expected, ty, val, he, hd,
                  Bool.eq_false_iff.mpr hbs, heqv, h⟩
              · simp [heqv] at h
            · simp [hsz] at h
        | _ => simp [throw, throwThe, MonadExceptOf.throw] at h
  · simp [hp, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

end IxCC.Src.Table
