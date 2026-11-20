import Ix.Ixon
import IxC.Kernel.Ixon.ReaderSpec

namespace IxVM.ProjectionAccessor

open Ix.Kernel
open Ix.Kernel.Reader

/-- The two entries a shard must establish for this field in the reader state
preceding the accessor's record. The field sort is the level on the model's
projection iota theorem. -/
structure Field (md : Mode) where
  owner : Frontend.ProjRecOwner md
  index : Nat
  sort : Level

def Field.agrees (f : Field md) (st : State md) : Prop :=
  st.projOwners[f.owner.T]? = some f.owner ∧
  st.projLevels[Frontend.projIotaName f.owner.T f.index]? = some f.sort

/-- Locate the two entries from the field named in the stored body. -/
def fieldFor? (cx : Ctx md) (st : State md) (addr : Address) (c : Ixon.Constant) :
    Option (Field md) := do
  let .defn d := c.info | none
  let .defn := d.kind | none
  let .safe := d.safety | none
  let raw ← ((definitionReader cx addr c d).read d.value).toOption
  let .proj T i (.bvar 0) := Frontend.lamBody raw | none
  let owner ← st.projOwners[T]?
  guard (owner.T == T)
  let sort ← st.projLevels[Frontend.projIotaName T i]?
  return ⟨owner, i, sort⟩

theorem fieldFor?_agrees {cx : Ctx md} {st : State md} {addr : Address} {c : Ixon.Constant}
    {f : Field md} (found : fieldFor? cx st addr c = some f) : f.agrees st := by
  unfold fieldFor? at found
  split at found <;> try contradiction
  rename_i d _
  split at found <;> try contradiction
  split at found <;> try contradiction
  cases hraw : ((definitionReader cx addr c d).read d.value).toOption <;>
    simp [hraw, bind, Option.bind] at found
  split at found <;> try contradiction
  rename_i T i _
  cases ho : st.projOwners[T]? <;> simp [ho] at found
  rename_i owner
  by_cases ht : owner.T = T
  · cases hl : st.projLevels[Frontend.projIotaName T i]? <;> simp [ht, hl, guard] at found
    subst f
    exact ⟨ht ▸ ho, ht ▸ hl⟩
  · simp [ht, guard] at found

/-- Reconstruct an accessor using its own binders and declared result type.
The owner and field index must match the projection at the end of the lambdas. -/
def Field.rewrite (f : Field md) (cv : CVal md) (raw : CExpr md) : Option (CExpr md) := do
  let .proj T i (.bvar 0) := Frontend.lamBody raw | none
  if T == f.owner.T && i == f.index && cv.levelParams == f.owner.lps then
    Frontend.projRecValue f.owner f.sort cv.type raw f.index
  else none

/-- On the field named by the body, reconstruction has exactly IxC's result,
including its refusal when the binder or recursor shape is unsupported. -/
theorem Field.rewrite_eq {f : Field md} {st : State md} {cv : CVal md} {raw : CExpr md}
    (agrees : f.agrees st) (shape : Frontend.lamBody raw = .proj f.owner.T f.index (.bvar 0)) :
    f.rewrite cv raw = projRewrite st cv raw := by
  by_cases hl : cv.levelParams = f.owner.lps <;>
    simp [Field.rewrite, projRewrite, shape, agrees.1, agrees.2, hl, guard] <;> rfl

/-- A selected term agrees with the full reader whenever the owner and level
come from that reader. No other reader-state entries enter reconstruction. -/
theorem Field.rewrite_sound {f : Field md} {st : State md} {cv : CVal md} {raw body : CExpr md}
    (agrees : f.agrees st) (selected : f.rewrite cv raw = some body) :
    projRewrite st cv raw = some body := by
  have h := selected
  unfold Field.rewrite at h
  split at h <;> try contradiction
  rename_i T i shape
  split at h <;> try contradiction
  rename_i test
  obtain ⟨⟨ht, hi⟩, _⟩ := Bool.and_eq_true_iff.mp test |>.imp_left Bool.and_eq_true_iff.mp
  rw [eq_of_beq ht, eq_of_beq hi] at shape
  rwa [← f.rewrite_eq agrees shape]

/-- Read the original singleton using IxC's member reader. The recursor body
inherits the source key and the hint IxC computes for that body. -/
def Field.read (f : Field md) (cx : Ctx md) (heights : CName md → Nat)
    (addr : Address) (c : Ixon.Constant) : Option (CDecl md) := do
  let .defn d := c.info | none
  let .defn := d.kind | none
  let .safe := d.safety | none
  let mr := definitionReader cx addr c d
  let ref := ConstRef.member addr 0
  let key ← (cx.memberKey ref).toOption
  let ty ← (mr.read d.typ).toOption
  let raw ← (mr.read d.value).toOption
  let cv := ⟨key, singletonLps d.lvls, ty⟩
  let body ← f.rewrite cv raw
  return .defnDecl cv body ((cx.hint ref).getD (Frontend.InModel.hintFor heights body))

theorem Field.read_sound {f : Field md} {cx : Ctx md} {st : State md}
    {addr : Address} {c : Ixon.Constant} {decl : CDecl md} (agrees : f.agrees st)
    (selected : f.read cx (st.heights.getD · 0) addr c = some decl) :
    readRecord cx st addr c = .ok { decls := #[decl], projRewrites := 1 } := by
  unfold Field.read at selected
  split at selected <;> try contradiction
  rename_i d info
  split at selected <;> try contradiction
  rename_i hk
  split at selected <;> try contradiction
  rename_i hs
  cases hkey : cx.memberKey (.member addr 0) <;>
    simp [hkey, Except.toOption, bind, Option.bind] at selected
  rename_i key
  cases ht : (definitionReader cx addr c d).read d.typ <;>
    simp [ht] at selected
  rename_i ty
  cases hv : (definitionReader cx addr c d).read d.value <;>
    simp [hv] at selected
  rename_i raw
  cases hb : f.rewrite ⟨key, singletonLps d.lvls, ty⟩ raw <;>
    simp [hb] at selected
  rename_i body
  exact (readRecord_rewritten_defn_iff info hk hs decl).mpr
    ⟨key, ty, raw, body, hkey, ht, hv, f.rewrite_sound agrees hb, selected.symm⟩

/-- Checking a definition and later unfolding it may obtain field data independently.
Two successful reconstructions against the same reader state give the same declaration. -/
theorem Field.read_unique {f g : Field md} {cx : Ctx md} {st : State md}
    {addr : Address} {c : Ixon.Constant} {first second : CDecl md}
    (hf : f.agrees st) (hg : g.agrees st)
    (h₁ : f.read cx (st.heights.getD · 0) addr c = some first)
    (h₂ : g.read cx (st.heights.getD · 0) addr c = some second) : first = second := by
  have h := (Field.read_sound hf h₁).symm.trans (Field.read_sound hg h₂)
  simpa using congrArg Read.decls (Except.ok.inj h)

/-- The accessor declaration at its original source key, if the full reader
has the field metadata and the body has the supported projection shape. -/
def read? (cx : Ctx md) (st : State md) (addr : Address) (c : Ixon.Constant) :
    Option (CDecl md) := do
  let f ← fieldFor? cx st addr c
  f.read cx (st.heights.getD · 0) addr c

theorem read?_sound {cx : Ctx md} {st : State md} {addr : Address} {c : Ixon.Constant}
    {decl : CDecl md} (selected : read? cx st addr c = some decl) :
    readRecord cx st addr c = .ok { decls := #[decl], projRewrites := 1 } := by
  cases found : fieldFor? cx st addr c with
  | none => simp [read?, found] at selected
  | some f => exact f.read_sound (fieldFor?_agrees found) (by simpa [read?, found] using selected)

/-- Reconstruct from the exact bytes committed by an accessor address. -/
def readStored? (cx : Ctx md) (st : State md) (addr : Address) (bytes : ByteArray) :
    Option (CDecl md) := do
  guard (Address.blake3 bytes == addr)
  let c ← (Ixon.deConstantExact bytes).toOption
  read? cx st addr c

theorem readStored?_sound {cx : Ctx md} {st : State md} {addr : Address} {bytes : ByteArray}
    {decl : CDecl md} (selected : readStored? cx st addr bytes = some decl) :
    Address.blake3 bytes = addr ∧ ∃ c, Ixon.deConstantExact bytes = .ok c ∧
      readRecord cx st addr c = .ok { decls := #[decl], projRewrites := 1 } := by
  unfold readStored? at selected
  by_cases hash : Address.blake3 bytes = addr
  · refine ⟨hash, ?_⟩
    cases decoded : Ixon.deConstantExact bytes with
    | error e => simp [hash, decoded, guard, Except.toOption, bind, Option.bind] at selected
    | ok c =>
      exact ⟨c, rfl, read?_sound (by simpa [hash, decoded, guard, Except.toOption] using selected)⟩
  · simp [hash, guard, bind, Option.bind] at selected

end IxVM.ProjectionAccessor
