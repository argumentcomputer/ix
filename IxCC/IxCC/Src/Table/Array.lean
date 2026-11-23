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
  listLength : Option Nat := none
  listConcat : Option Nat := none
  listDropLast : Option Nat := none
  listSet : Option Nat := none
  uint8Type : Option Nat := none
  arrayOps : List (ArrayOp × Nat) := []
  byteArrayOps : List (ByteArrayOp × Nat) := []
  stringOps : List (StringOp × Nat) := []
  deriving Inhabited

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
