import IxVMRefinement.Assembly.FamilyFold

/-! # The family graph: what the fold reads of the walk about family records, advice and twins

A mutual or nested block installs its family record (a block of recursors) with itself; the
advice its family check validated and the container recursors that check validated are checked
inside that family check, not by the walk; and a run may accept a second family record for a
block (a twin). `FamilyGraph` states what the typing fold reads of all this beside the walk's
`TopGraph`:

* **Checked records.** A record is checked when the walk reached it (`Top`) or a family check
  checked it (`Inner`: an advice record, a container's recursor). One rank orders both.
* **Units.** A unit is a checked record in Lean's logic with a constant address the witness's
  environment does not store, that no block claims as its family record (`IsUnit`). A block's
  unit owns the block's constant addresses and its family record's (`FamOwns`).
* **Families.** `fam B = some rb`: the block `B` installs the family record `rb`. The record is
  a block of recursors, empty where the family has no recursor (the block is then stepped by
  the family step at a record that owns nothing); one block claims a record with a constant
  address; the block is a unit; where the record is itself checked it comes after its block
  (`famAfter`). A reference the family record uses is stored by the witness's
  environment, covered, a constant address of the block or of the record, or owned by a checked
  unclaimed record of rank below the block's (`OwnedBelow`). The last case is what a nested
  family needs: the constructors of the container it nests through are constant addresses of
  the container's block, which the walk reached before the block, and they are not themselves
  top-walked.
* **Advice and inner records.** An advice record of a block's family check is checked, unclaimed
  and of rank below the block. What a record checked inside a family check uses is stored,
  covered, its own, or owned below it (`innerClosed`).
* **Twins.** `twin rb' = some B`: `rb'` is a second family record of the block `B`, checked
  after `B`. It is a unit of its own: it owns its own constant addresses and needs, beside what
  it uses, the constant addresses of the block's family record (`FamilyNeeds`).

From `TopGraph` and `FamilyGraph`: distinct units own disjoint addresses (`owns_apart_family`),
the start stores nothing a unit owns (`fresh_at_family`), and every address a unit needs is
stored by the witness's environment, its own, or owned by a unit of smaller rank
(`needs_earlier_family`). These are the three facts `UnitFold.run` asks of the graph. -/

universe u

namespace IxVM.Refinement.Typing

open IxVM.Consistency
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open Ix.Kernel (ConstantInfo ConstantVal)

set_option linter.unusedVariables false

/-! ## Checked records, claims and ownership below a rank -/

/-- **A record the run checked**: the walk reached it, or a family check checked it. -/
def Walked (Top Inner : _root_.Address → Prop) (a : _root_.Address) : Prop :=
  Top a ∨ Inner a

/-- **No block claims the record at `a` as its family record.** -/
def Unclaimed (fam : _root_.Address → Option _root_.Address) (a : _root_.Address) : Prop :=
  ∀ B, fam B ≠ some a

/-- **`x` is owned by a checked, unclaimed record of rank below `n`**: a constant address of
that record, or of the family record it installs. -/
def OwnedBelow (E₀ : Ixon.Env) (Top Inner : _root_.Address → Prop)
    (rank : _root_.Address → Nat) (fam : _root_.Address → Option _root_.Address) (n : Nat)
    (x : _root_.Address) : Prop :=
  ∃ D, Walked Top Inner D ∧ Unclaimed fam D ∧ rank D < n ∧ FamOwns E₀ fam D x

/-- **A unit of the fold**: a checked record in Lean's logic that no block claims as its family
record, with a constant address the witness's environment does not store. -/
def IsUnit (t : Ix.Kernel.RoleTable) (envT : Ix.Kernel.Env .anon) (E₀ : Ixon.Env)
    (Top Inner : _root_.Address → Prop) (fam : _root_.Address → Option _root_.Address)
    (A : _root_.Address) : Prop :=
  Walked Top Inner A ∧ Unclaimed fam A ∧ ∃ c, recordOf E₀ A = some c ∧ InLogic c ∧
    ∃ x, ConstAddrOf A c x ∧ ¬ StoredAt t envT x

/-! ## The graph -/

/-- **The family records, the advice, the inner records and the twins, against the walk**
(`TopGraph`'s companion; module docstring). -/
structure FamilyGraph (t : Ix.Kernel.RoleTable) (envT : Ix.Kernel.Env .anon) (E₀ : Ixon.Env)
    (Top : _root_.Address → Prop) (rank : _root_.Address → Nat)
    (fam : _root_.Address → Option _root_.Address)
    (twin : _root_.Address → Option _root_.Address)
    (adv : _root_.Address → _root_.Address → Prop) (Inner : _root_.Address → Prop) : Prop where
  /-- A block with a family record is top-walked. -/
  famBlock : ∀ B rb, fam B = some rb → Top B
  /-- A block with a family record is a unit: unclaimed, in Lean's logic, with a constant
  address the witness's environment does not store. -/
  famUnit : ∀ B rb, fam B = some rb → Unclaimed fam B ∧
    ∃ cb, recordOf E₀ B = some cb ∧ InLogic cb ∧ ∃ x, ConstAddrOf B cb x ∧ ¬ StoredAt t envT x
  /-- A family record is a block of recursors, possibly empty (the family record of a modeled
  block whose family has no recursor). -/
  famRecord : ∀ B rb, fam B = some rb → ∃ crb rs, FamRecRecord E₀ rb crb rs
  /-- A family record that is itself checked comes after its block. -/
  famAfter : ∀ B rb, fam B = some rb → Walked Top Inner rb → rank B < rank rb
  /-- One block claims a family record with a constant address. (The empty block of recursors
  has one address, so two blocks may claim it; it owns nothing.) -/
  famInj : ∀ B B' rb x crb, fam B = some rb → fam B' = some rb → recordOf E₀ rb = some crb →
    ConstAddrOf rb crb x → B = B'
  /-- The witness's environment stores no constant address of a family record. -/
  famFresh : ∀ B rb crb x, fam B = some rb → recordOf E₀ rb = some crb →
    ConstAddrOf rb crb x → ¬ StoredAt t envT x
  /-- What a family record uses is stored by the witness's environment, covered, a constant
  address of the block or of the record, or owned by a checked unclaimed record of rank below
  the block's. -/
  famClosed : ∀ B rb x, fam B = some rb → UsedRef E₀ rb x → NeedOk E₀ x →
    StoredAt t envT x ∨ Covered t x ∨
      (∃ cb, recordOf E₀ B = some cb ∧ ConstAddrOf B cb x) ∨
      (∃ crb, recordOf E₀ rb = some crb ∧ ConstAddrOf rb crb x) ∨
      OwnedBelow E₀ Top Inner rank fam (rank B) x
  /-- An advice record of a block's family check is checked, unclaimed, of rank below the
  block's, and in Lean's logic. -/
  advEarlier : ∀ B a, adv B a → Walked Top Inner a ∧ Unclaimed fam a ∧ rank a < rank B ∧
    ∀ ca, recordOf E₀ a = some ca → InLogic ca
  /-- A record checked inside a family check is in the store. -/
  innerRecord : ∀ a, Inner a → ∃ c, recordOf E₀ a = some c
  /-- The member and constructor projection records of a block checked inside a family check
  are in the store. -/
  innerMembers : ∀ B c ms, Inner B → recordOf E₀ B = some c → c.info = .muts ms →
    ∀ i m, ms[i]? = some m →
      recordOf E₀ (memberAddr B i m) = some (memberProjection B i m) ∧
      ∀ ind j, m = .indc ind → j < ind.ctors.size →
        recordOf E₀ (ctorAddr B i j) = some (constructorProjection B i j)
  /-- A record checked inside a family check is no axiom and no quotient record. -/
  innerKind : ∀ a c, Inner a → recordOf E₀ a = some c →
    (∀ ax, c.info ≠ .axio ax) ∧ ∀ q, c.info ≠ .quot q
  /-- What a record checked inside a family check uses is stored by the witness's environment,
  covered, a constant address of the record, or owned by a checked unclaimed record of smaller
  rank. -/
  innerClosed : ∀ a x, Inner a → UsedRef E₀ a x → NeedOk E₀ x →
    StoredAt t envT x ∨ Covered t x ∨
      (∃ c, recordOf E₀ a = some c ∧ ConstAddrOf a c x) ∨
      OwnedBelow E₀ Top Inner rank fam (rank a) x
  /-- A twin is a second family record of a block with a family record, after the block; or of
  a block with none in the graph (one the witness's environment stores with its family record,
  so the twin needs nothing of this fold for it). -/
  twinBlock : ∀ rb' B, twin rb' = some B →
    (∃ rb, fam B = some rb ∧ rb' ≠ rb ∧ rank B < rank rb') ∨ fam B = none
  /-- A twin is checked, is no block's family record, and has no family record of its own. -/
  twinWalked : ∀ rb' B, twin rb' = some B →
    Walked Top Inner rb' ∧ Unclaimed fam rb' ∧ fam rb' = none
  /-- A twin is a block of recursors with at least one member. -/
  twinRecord : ∀ rb' B, twin rb' = some B →
    ∃ crb' rs', FamRecRecord E₀ rb' crb' rs' ∧ rs'.size ≠ 0

/-- **The walk alone**: no family, no advice, no inner record, no twin. -/
theorem familyGraph_none {t : Ix.Kernel.RoleTable} {envT : Ix.Kernel.Env .anon} {E₀ : Ixon.Env}
    {Top : _root_.Address → Prop} {rank : _root_.Address → Nat} :
    FamilyGraph t envT E₀ Top rank (fun _ => none) (fun _ => none) (fun _ _ => False)
      (fun _ => False) where
  famBlock := fun _ _ h => nomatch h
  famUnit := fun _ _ h => nomatch h
  famRecord := fun _ _ h => nomatch h
  famAfter := fun _ _ h => nomatch h
  famInj := fun _ _ _ _ _ h => nomatch h
  famFresh := fun _ _ _ _ h => nomatch h
  famClosed := fun _ _ _ h => nomatch h
  advEarlier := fun _ _ h => False.elim h
  innerRecord := fun _ h => False.elim h
  innerMembers := fun _ _ _ h => False.elim h
  innerKind := fun _ _ h => False.elim h
  innerClosed := fun _ _ h => False.elim h
  twinBlock := fun _ _ h => nomatch h
  twinWalked := fun _ _ h => nomatch h
  twinRecord := fun _ _ h => nomatch h

/-! ## The fold with twins -/

/-- **What a unit needs**: what `FamNeeds` lists (the in-logic constant addresses its record or
its family record uses, and the constant addresses of its advice); for a twin, the constant
addresses of the family record of its block; and the in-logic constant addresses an advice
record of its family check uses. -/
def FamilyNeeds (E₀ : Ixon.Env) (fam twin : _root_.Address → Option _root_.Address)
    (adv : _root_.Address → _root_.Address → Prop) (A x : _root_.Address) : Prop :=
  FamNeeds E₀ fam adv A x ∨
    (∃ B rb crb, twin A = some B ∧ fam B = some rb ∧ recordOf E₀ rb = some crb ∧
      ConstAddrOf rb crb x) ∨
    ∃ a, adv A a ∧ UsedRef E₀ a x ∧ NeedOk E₀ x

/-- **The typing run as a system of units, with family records and twins**: `typingFoldFam`
with the needs `FamilyNeeds`. -/
def familyFold (X : Ix.Kernel.Env .anon → Prop) (t : Ix.Kernel.RoleTable)
    (E₀ R E : Ixon.Env) (lim : Option Nat) (rank : _root_.Address → Nat)
    (fam twin : _root_.Address → Option _root_.Address)
    (adv : _root_.Address → _root_.Address → Prop) :
    UnitFold (Ix.Kernel.Env .anon) _root_.Address _root_.Address where
  Inv := FoldInv.{u} X t E₀ R E lim
  Ext := fun env env' => ∀ ci ∈ env.consts, ci ∈ env'.consts
  Stored := StoredAt t
  Post := fun A env => ∀ x, FamOwns E₀ fam A x →
    ∃ ci ∈ env.consts, ci.name = keyOf t x ∧ KeptIn t (storeOver E₀ R) (blobOver E₀ R) x ci
  owns := FamOwns E₀ fam
  needs := FamilyNeeds E₀ fam twin adv
  rank := rank
  ext_refl := fun _ _ h => h
  ext_trans := fun h₁ h₂ ci hci => h₂ ci (h₁ ci hci)
  stored_mono := fun x h hx => by
    obtain ⟨ci, hci, hname⟩ := hx
    exact ⟨ci, h ci hci, hname⟩
  post_mono := fun A h hp x hx => by
    obtain ⟨ci, hci, hname, hk⟩ := hp x hx
    exact ⟨ci, h ci hci, hname, hk⟩

/-- **The step of a twin's unit.** `UnitStep` of the second family record at `A`, handed in
addition the constant addresses of the family record `rb` of its block, stored: from the prefix
invariant at an environment that stores what the record uses and the block's family record, and
none of the record's constant addresses, some fresh constants keep the invariant and store, at
each constant address of the record, a constant that stores its reading; every other new
constant is at a derived key. -/
def UnitStepTwin (X : Ix.Kernel.Env .anon → Prop) (t : Ix.Kernel.RoleTable)
    (envT : Ix.Kernel.Env .anon) (E₀ E : Ixon.Env) (lim : Option Nat) (A : _root_.Address)
    (c : Ixon.Constant) (rb : _root_.Address) (crb : Ixon.Constant) : Prop :=
  ∀ env : Ix.Kernel.Env .anon,
    (∀ ci ∈ envT.consts, ci ∈ env.consts) → (env.consts.map (·.name)).Nodup →
    Decl.PrefixInv.{u} E t lim env → X env →
    (∀ x, UsedRef E₀ A x →
      (env.find? (keyOf t x)).isSome = true ∨ ConstAddrOf A c x ∨ ¬ NeedOk E₀ x) →
    (∀ x, ConstAddrOf rb crb x → (env.find? (keyOf t x)).isSome = true) →
    (∀ x, ConstAddrOf A c x → env.find? (keyOf t x) = none) →
    ∃ new : List (ConstantInfo .anon),
      (new.map (·.name)).Nodup ∧ (∀ ci ∈ new, env.find? ci.name = none) ∧
      Decl.PrefixInv.{u} E t lim ⟨new ++ env.consts⟩ ∧ X ⟨new ++ env.consts⟩ ∧
      (∀ x, ConstAddrOf A c x →
        ∃ ci ∈ new, ∃ ci₀, ci.name = keyOf t x ∧ Reads t E₀ x ci₀ ∧ StoredAs ci ci₀) ∧
      ∀ ci ∈ new, (∃ x, ConstAddrOf A c x ∧ ci.name = keyOf t x) ∨ ∃ k s, ci.name = .aux k s

/-- **The step of a block that installs its family record with it, over the family graph.**
`UnitStepFam` handed in addition what each advice record of the block's family check uses,
stored (unless it is a constant address of the block or of its family record, or no in-logic
constant address of the run's store): the advice is checked before the block, so its units have
stored what it uses by the time the block is stepped (`needs_earlier_family`). -/
def UnitStepFamily (X : Ix.Kernel.Env .anon → Prop) (t : Ix.Kernel.RoleTable)
    (envT : Ix.Kernel.Env .anon) (E₀ E : Ixon.Env) (lim : Option Nat) (A : _root_.Address)
    (c : Ixon.Constant) (rb : _root_.Address) (crb : Ixon.Constant)
    (adv : _root_.Address → Prop) : Prop :=
  ∀ env : Ix.Kernel.Env .anon,
    (∀ ci ∈ envT.consts, ci ∈ env.consts) → (env.consts.map (·.name)).Nodup →
    Decl.PrefixInv.{u} E t lim env → X env →
    (∀ x, UsedRef E₀ A x ∨ UsedRef E₀ rb x →
      (env.find? (keyOf t x)).isSome = true ∨ FamAddr A c rb crb x ∨ ¬ NeedOk E₀ x) →
    (∀ a, adv a → ∀ ca, recordOf E₀ a = some ca → ∀ x, ConstAddrOf a ca x →
      (env.find? (keyOf t x)).isSome = true) →
    (∀ a, adv a → ∀ x, UsedRef E₀ a x →
      (env.find? (keyOf t x)).isSome = true ∨ FamAddr A c rb crb x ∨ ¬ NeedOk E₀ x) →
    (∀ x, FamAddr A c rb crb x → env.find? (keyOf t x) = none) →
    ∃ new : List (ConstantInfo .anon),
      (new.map (·.name)).Nodup ∧ (∀ ci ∈ new, env.find? ci.name = none) ∧
      Decl.PrefixInv.{u} E t lim ⟨new ++ env.consts⟩ ∧ X ⟨new ++ env.consts⟩ ∧
      (∀ x, FamAddr A c rb crb x →
        ∃ ci ∈ new, ∃ ci₀, ci.name = keyOf t x ∧ Reads t E₀ x ci₀ ∧ StoredAs ci ci₀) ∧
      ∀ ci ∈ new, (∃ x, FamAddr A c rb crb x ∧ ci.name = keyOf t x) ∨ ∃ k s, ci.name = .aux k s

/-- A step that does not read what the advice uses is one that is handed it. -/
theorem unitStepFamily_of_unitStepFam {X : Ix.Kernel.Env .anon → Prop}
    {t : Ix.Kernel.RoleTable} {envT : Ix.Kernel.Env .anon} {E₀ E : Ixon.Env}
    {lim : Option Nat} {A : _root_.Address} {c : Ixon.Constant} {rb : _root_.Address}
    {crb : Ixon.Constant} {adv : _root_.Address → Prop}
    (h : UnitStepFam.{u} X t envT E₀ E lim A c rb crb adv) :
    UnitStepFamily.{u} X t envT E₀ E lim A c rb crb adv :=
  fun env hext hnd hinv hX hrefs hadv _ hfresh => h env hext hnd hinv hX hrefs hadv hfresh

/-! ## What the fold reads of the graph -/

section Fold

variable {X : Ix.Kernel.Env .anon → Prop} {t : Ix.Kernel.RoleTable} {R E₀ E : Ixon.Env}
  {envT : Ix.Kernel.Env .anon} {seeds : List _root_.Address} {Top : _root_.Address → Prop}
  {rank : _root_.Address → Nat} {lim : Option Nat} {us : List _root_.Address}
  {fam twin : _root_.Address → Option _root_.Address}
  {adv : _root_.Address → _root_.Address → Prop} {Inner : _root_.Address → Prop}

/-- A member's or constructor's address of a checked block holds a projection record of that
block. -/
theorem walked_block_record (hG : TopGraph t E₀ seeds Top rank)
    (hF : FamilyGraph t envT E₀ Top rank fam twin adv Inner) {A : _root_.Address}
    {c : Ixon.Constant} {ms : Array Ixon.MutConst} (hW : Walked Top Inner A)
    (hc : recordOf E₀ A = some c) (hms : c.info = .muts ms) {i : Nat} {m : Ixon.MutConst}
    (hm : ms[i]? = some m) {x : _root_.Address}
    (hx : x = memberAddr A i m ∨ ∃ ind j, m = .indc ind ∧ j < ind.ctors.size ∧ x = ctorAddr A i j) :
    ∃ P, recordOf E₀ x = some P ∧ IsProj P ∧ Ix.Cert.ownerOf x P = A := by
  rcases hW with hT | hI
  · exact hG.block_record hT hc hms hm hx
  · obtain ⟨hmem, hctor⟩ := hF.innerMembers A c ms hI hc hms i m hm
    rcases hx with hx | ⟨ind, j, hind, hj, hx⟩
    · rw [hx]
      exact ⟨_, hmem, memberProjection_isProj A i m, ownerOf_memberProjection _ A i m⟩
    · rw [hx]
      exact ⟨_, hctor ind j hind hj, constructorProjection_isProj A i j,
        ownerOf_constructorProjection _ A i j⟩

/-- A constant address of a checked record is the record's own address, or holds a projection
record of the block. -/
theorem walked_constAddr_cases (hG : TopGraph t E₀ seeds Top rank)
    (hF : FamilyGraph t envT E₀ Top rank fam twin adv Inner) {A : _root_.Address}
    {c : Ixon.Constant} {x : _root_.Address} (hW : Walked Top Inner A)
    (hc : recordOf E₀ A = some c) (hx : ConstAddrOf A c x) :
    (x = A ∧ Standalone c) ∨
      (IsBlock c ∧ ∃ P, recordOf E₀ x = some P ∧ IsProj P ∧ Ix.Cert.ownerOf x P = A) := by
  rcases hx with h | ⟨ms, i, m, hms, hm, hx⟩
  · exact Or.inl h
  · exact Or.inr ⟨⟨ms, hms⟩, walked_block_record hG hF hW hc hms hm hx⟩

/-- **Two checked records with a constant address in common are one record.** -/
theorem walked_owns_apart (hG : TopGraph t E₀ seeds Top rank)
    (hF : FamilyGraph t envT E₀ Top rank fam twin adv Inner) {A A' : _root_.Address}
    {c c' : Ixon.Constant} {x : _root_.Address} (hW : Walked Top Inner A)
    (hW' : Walked Top Inner A') (hc : recordOf E₀ A = some c) (hc' : recordOf E₀ A' = some c')
    (hx : ConstAddrOf A c x) (hx' : ConstAddrOf A' c' x) : A = A' := by
  rcases walked_constAddr_cases hG hF hW hc hx with ⟨h1, hs⟩ | ⟨hb, P, hP, hPp, hPo⟩
  · rcases walked_constAddr_cases hG hF hW' hc' hx' with ⟨h1', hs'⟩ | ⟨hb', P', hP', hPp', hPo'⟩
    · exact h1.symm.trans h1'
    · rw [h1, hc] at hP'
      have hcc : c = P' := Option.some.inj hP'
      rw [hcc] at hs
      exact (standalone_not_proj hs hPp').elim
  · rcases walked_constAddr_cases hG hF hW' hc' hx' with ⟨h1', hs'⟩ | ⟨hb', P', hP', hPp', hPo'⟩
    · rw [h1', hc'] at hP
      have hcc : c' = P := Option.some.inj hP
      rw [hcc] at hs'
      exact (standalone_not_proj hs' hPp).elim
    · rw [hP] at hP'
      have hPP : P = P' := Option.some.inj hP'
      rw [← hPP] at hPo'
      exact hPo.symm.trans hPo'

/-- A checked record that has a constant address of a family record is that family record. -/
theorem walked_eq_famRecord (hG : TopGraph t E₀ seeds Top rank)
    (hF : FamilyGraph t envT E₀ Top rank fam twin adv Inner) {A B rb : _root_.Address}
    {c crb : Ixon.Constant} {x : _root_.Address} (hW : Walked Top Inner A)
    (hc : recordOf E₀ A = some c) (hx : ConstAddrOf A c x) (hrb : fam B = some rb)
    (hcrb : recordOf E₀ rb = some crb) (hxr : ConstAddrOf rb crb x) : A = rb := by
  obtain ⟨crb', rs, hR⟩ := hF.famRecord B rb hrb
  have hcc : crb' = crb := Option.some.inj (hR.record.symm.trans hcrb)
  subst hcc
  obtain ⟨P, hP, hPp, hPo⟩ := hR.constAddr hxr
  rcases walked_constAddr_cases hG hF hW hc hx with ⟨h1, hs⟩ | ⟨-, P', hP', -, hPo'⟩
  · rw [h1, hc] at hP
    have hcP : c = P := Option.some.inj hP
    rw [hcP] at hs
    exact (standalone_not_proj hs hPp).elim
  · have hPP : P' = P := Option.some.inj (hP'.symm.trans hP)
    rw [hPP] at hPo'
    exact hPo'.symm.trans hPo

/-- **Distinct units own disjoint addresses**, family records included. A unit is no block's
family record, so a family record's constant addresses are its block's alone. -/
theorem owns_apart_family (hG : TopGraph t E₀ seeds Top rank)
    (hF : FamilyGraph t envT E₀ Top rank fam twin adv Inner)
    (hus : ∀ A, A ∈ us ↔ IsUnit t envT E₀ Top Inner fam A) :
    (familyFold.{u} X t E₀ R E lim rank fam twin adv).OwnsApart us := by
  intro A hA A' hA' x hx hx'
  obtain ⟨hW, hU, -⟩ := (hus A).mp hA
  obtain ⟨hW', hU', -⟩ := (hus A').mp hA'
  obtain ⟨c, hc, hown | ⟨rb, crb, hrb, hcrb, hxr⟩⟩ := hx <;>
    obtain ⟨c', hc', hown' | ⟨rb', crb', hrb', hcrb', hxr'⟩⟩ := hx'
  · exact walked_owns_apart hG hF hW hW' hc hc' hown hown'
  · have hAr : A = rb' := walked_eq_famRecord hG hF hW hc hown hrb' hcrb' hxr'
    rw [← hAr] at hrb'
    exact (hU A' hrb').elim
  · have hAr : A' = rb := walked_eq_famRecord hG hF hW' hc' hown' hrb hcrb hxr
    rw [← hAr] at hrb
    exact (hU' A hrb).elim
  · obtain ⟨crb₁, rs, hR⟩ := hF.famRecord A rb hrb
    obtain ⟨crb₂, rs', hR'⟩ := hF.famRecord A' rb' hrb'
    have h1 : crb₁ = crb := Option.some.inj (hR.record.symm.trans hcrb)
    have h2 : crb₂ = crb' := Option.some.inj (hR'.record.symm.trans hcrb')
    subst h1 h2
    obtain ⟨P, hP, -, hPo⟩ := hR.constAddr hxr
    obtain ⟨P', hP', -, hPo'⟩ := hR'.constAddr hxr'
    have hPP : P' = P := Option.some.inj (hP'.symm.trans hP)
    subst hPP
    have hrr : rb = rb' := hPo.symm.trans hPo'
    subst hrr
    exact hF.famInj A A' rb x _ hrb hrb' hR.record hxr

/-- **A checked, unclaimed record that owns an in-logic address the witness's environment does
not store is a unit.** -/
theorem isUnit_of_owns (hG : TopGraph t E₀ seeds Top rank)
    (hF : FamilyGraph t envT E₀ Top rank fam twin adv Inner) {D x : _root_.Address}
    (hW : Walked Top Inner D) (hU : Unclaimed fam D) (hown : FamOwns E₀ fam D x)
    (hok : NeedOk E₀ x) (hst : ¬ StoredAt t envT x) : IsUnit t envT E₀ Top Inner fam D := by
  obtain ⟨cx, hcx, hnb, hlog, hlogB⟩ := hok
  obtain ⟨c, hc, hown | ⟨rb, crb, hrb, hcrb, hxr⟩⟩ := hown
  · refine ⟨hW, hU, c, hc, ?_, x, hown, hst⟩
    rcases walked_constAddr_cases hG hF hW hc hown with ⟨h1, -⟩ | ⟨-, P, hP, -, hPo⟩
    · rw [h1, hc] at hcx
      have hcc : c = cx := Option.some.inj hcx
      rw [hcc]
      exact hlog
    · have hcP : cx = P := Option.some.inj (hcx.symm.trans hP)
      refine hlogB c ?_
      rw [hcP, hPo]
      exact hc
  · obtain ⟨-, cb, hcb, hlogcb, x₀, hx₀, hun⟩ := hF.famUnit D rb hrb
    exact ⟨hW, hU, cb, hcb, hlogcb, x₀, hx₀, hun⟩

/-- An address owned below a rank that is in Lean's logic and not stored by the witness's
environment is owned by a unit of that smaller rank. -/
theorem earlier_of_ownedBelow (hG : TopGraph t E₀ seeds Top rank)
    (hF : FamilyGraph t envT E₀ Top rank fam twin adv Inner)
    (hus : ∀ A, A ∈ us ↔ IsUnit t envT E₀ Top Inner fam A) {x : _root_.Address} {n : Nat}
    (hob : OwnedBelow E₀ Top Inner rank fam n x) (hok : NeedOk E₀ x)
    (hst : ¬ StoredAt t envT x) :
    ∃ b ∈ us, FamOwns E₀ fam b x ∧ rank b < n := by
  obtain ⟨D, hW, hU, hrk, hown⟩ := hob
  exact ⟨D, (hus D).mpr (isUnit_of_owns hG hF hW hU hown hok hst), hown, hrk⟩

/-- **What a top-walked record uses is covered or owned below it.** A top-walked reference of
smaller rank is its own record's constant address, or a constant address of its block; where
the block is a family record, it is owned by the block that claims it, which comes before it. -/
theorem top_ownedBelow (hG : TopGraph t E₀ seeds Top rank)
    (hF : FamilyGraph t envT E₀ Top rank fam twin adv Inner) {a x : _root_.Address}
    (hT : Top a) (hu : UsedRef E₀ a x) (hok : NeedOk E₀ x) :
    Covered t x ∨ OwnedBelow E₀ Top Inner rank fam (rank a) x := by
  rcases hG.closed a x hT hu with ⟨hTx, hrk⟩ | hcov
  · refine Or.inr ?_
    obtain ⟨cx, hcx, hnb, hlog, hlogB⟩ := hok
    rcases kind_cases cx with hsa | hpr | hbl
    · refine ⟨x, Or.inl hTx, ?_, hrk, cx, hcx, Or.inl (Or.inl ⟨rfl, hsa⟩)⟩
      intro B hB
      obtain ⟨crb, rs, hR⟩ := hF.famRecord B x hB
      have hcc : crb = cx := Option.some.inj (hR.record.symm.trans hcx)
      rw [← hcc] at hsa
      exact standalone_not_block hsa ⟨rs, hR.muts⟩
    · obtain ⟨hTD, hrkD⟩ := hG.owner x cx hTx hcx hpr
      obtain ⟨cb, hcb, hconst⟩ := hG.projMember x cx hTx hcx hpr
      rcases Classical.em (∃ B, fam B = some (Ix.Cert.ownerOf x cx)) with ⟨B, hB⟩ | hne
      · obtain ⟨hUB, cB, hcB, -⟩ := hF.famUnit B _ hB
        exact ⟨B, Or.inl (hF.famBlock B _ hB), hUB,
          Nat.lt_trans (Nat.lt_trans (hF.famAfter B _ hB (Or.inl hTD)) hrkD) hrk,
          cB, hcB, Or.inr ⟨_, cb, hB, hcb, hconst⟩⟩
      · exact ⟨_, Or.inl hTD, fun B hB => hne ⟨B, hB⟩, Nat.lt_trans hrkD hrk, cb, hcb,
          Or.inl hconst⟩
    · exact absurd hbl hnb
  · exact Or.inl hcov

/-- **What a checked record uses and the witness's environment does not store is a constant
address of the record, or owned by a unit of smaller rank**: a top-walked record by the walk's
closure (`top_ownedBelow`), a record checked inside a family check by `innerClosed`; a covered
reference is stored. -/
theorem walked_usedRef_cases (hG : TopGraph t E₀ seeds Top rank)
    (hF : FamilyGraph t envT E₀ Top rank fam twin adv Inner)
    (hshape : TableShape.{u} t (fun _ => True) R envT) (htwf : t.wf = true)
    (hus : ∀ A, A ∈ us ↔ IsUnit t envT E₀ Top Inner fam A) {a x : _root_.Address}
    (hW : Walked Top Inner a) (hu : UsedRef E₀ a x) (hok : NeedOk E₀ x)
    (hst : ¬ StoredAt t envT x) :
    (∃ c, recordOf E₀ a = some c ∧ ConstAddrOf a c x) ∨
      ∃ b ∈ us, FamOwns E₀ fam b x ∧ rank b < rank a := by
  have h3 : Covered t x ∨ (∃ c, recordOf E₀ a = some c ∧ ConstAddrOf a c x) ∨
      OwnedBelow E₀ Top Inner rank fam (rank a) x := by
    rcases hW with hT | hI
    · rcases top_ownedBelow hG hF hT hu hok with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rcases hF.innerClosed a x hI hu hok with h | h | h | h
      · exact absurd h hst
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  rcases h3 with hcov | h | hob
  · exact absurd (covered_stored hshape htwf hcov) hst
  · exact Or.inl h
  · exact Or.inr (earlier_of_ownedBelow hG hF hus hob hok hst)

/-- **Every address a unit needs is stored by the witness's environment, owned by the unit, or
owned by a unit of smaller rank**: the references of its record (top-walked or checked inside a
family check), those of its family record, the constant addresses of its advice, for a twin
those of its block's family record, and what an advice record of its family check uses (the
advice record's own constant addresses are its unit's, of smaller rank). -/
theorem needs_earlier_family (hG : TopGraph t E₀ seeds Top rank)
    (hF : FamilyGraph t envT E₀ Top rank fam twin adv Inner)
    (hshape : TableShape.{u} t (fun _ => True) R envT) (htwf : t.wf = true)
    (hus : ∀ A, A ∈ us ↔ IsUnit t envT E₀ Top Inner fam A) :
    (familyFold.{u} X t E₀ R E lim rank fam twin adv).NeedsEarlier envT us := by
  intro A hA x hneed
  obtain ⟨hW, hU, cA, hcA, hlogA, -⟩ := (hus A).mp hA
  rcases Classical.em (StoredAt t envT x) with hst | hst
  · exact Or.inl hst
  · rcases hneed with (⟨hu | ⟨rb, hrb, hur⟩, hok⟩ | ⟨a, ca, ha, hca, hxa⟩) |
      ⟨B, rb, crb, htw, hrb, hcrb, hxr⟩ | ⟨a, ha, hua, hok⟩
    · rcases walked_usedRef_cases hG hF hshape htwf hus hW hu hok hst with ⟨c, hc, hx⟩ | hb
      · exact Or.inr (Or.inl ⟨c, hc, Or.inl hx⟩)
      · exact Or.inr (Or.inr hb)
    · rcases hF.famClosed A rb x hrb hur hok with h | hcov | ⟨cb, hcb, hxB⟩ | ⟨crb, hcrb, hxr⟩ |
        hob
      · exact absurd h hst
      · exact absurd (covered_stored hshape htwf hcov) hst
      · exact Or.inr (Or.inl ⟨cb, hcb, Or.inl hxB⟩)
      · exact Or.inr (Or.inl ⟨cA, hcA, Or.inr ⟨rb, crb, hrb, hcrb, hxr⟩⟩)
      · exact Or.inr (Or.inr (earlier_of_ownedBelow hG hF hus hob hok hst))
    · obtain ⟨hWa, hUa, hrk, hloga⟩ := hF.advEarlier A a ha
      exact Or.inr (Or.inr ⟨a, (hus a).mpr ⟨hWa, hUa, ca, hca, hloga ca hca, x, hxa, hst⟩,
        ⟨ca, hca, Or.inl hxa⟩, hrk⟩)
    · rcases hF.twinBlock A B htw with ⟨rb₀, hrb₀, -, hrk⟩ | hnone
      · obtain ⟨hUB, cB, hcB, hlogB, x₀, hx₀, hun⟩ := hF.famUnit B rb hrb
        exact Or.inr (Or.inr ⟨B,
          (hus B).mpr ⟨Or.inl (hF.famBlock B rb hrb), hUB, cB, hcB, hlogB, x₀, hx₀, hun⟩,
          ⟨cB, hcB, Or.inr ⟨rb, crb, hrb, hcrb, hxr⟩⟩, hrk⟩)
      · rw [hnone] at hrb
        cases hrb
    · obtain ⟨hWa, hUa, hrk, hloga⟩ := hF.advEarlier A a ha
      rcases walked_usedRef_cases hG hF hshape htwf hus hWa hua hok hst with
        ⟨ca, hca, hxa⟩ | ⟨b, hb, hown, hrkb⟩
      · exact Or.inr (Or.inr ⟨a, (hus a).mpr ⟨hWa, hUa, ca, hca, hloga ca hca, x, hxa, hst⟩,
          ⟨ca, hca, Or.inl hxa⟩, hrk⟩)
      · exact Or.inr (Or.inr ⟨b, hb, hown, Nat.lt_trans hrkb hrk⟩)

/-- **A unit's own constant addresses are all unstored**: one is, and a block is stored
whole. -/
theorem unit_fresh (hG : TopGraph t E₀ seeds Top rank)
    (hF : FamilyGraph t envT E₀ Top rank fam twin adv Inner)
    (hwhole : ∀ (a B : _root_.Address) (c cb : Ixon.Constant) (ms : Array Ixon.MutConst),
      (envT.find? (keyOf t a)).isSome = true → Ix.Cert.recordAt E a = some c →
      Ix.Cert.ownerOf a c = B → B ≠ a → Ix.Cert.recordAt E B = some cb → cb.info = .muts ms →
      BlockStored t envT B ms)
    (hrun : ∀ a c, recordOf E₀ a = some c → Ix.Cert.recordAt E a = some c)
    {A : _root_.Address} (hA : IsUnit t envT E₀ Top Inner fam A) {c : Ixon.Constant}
    {x : _root_.Address} (hc : recordOf E₀ A = some c) (hx : ConstAddrOf A c x) :
    ¬ StoredAt t envT x := by
  obtain ⟨hW, -, c', hc', -, x₀, hx₀, hun⟩ := hA
  rw [hc] at hc'
  have hcc : c = c' := Option.some.inj hc'
  rw [← hcc] at hx₀
  intro hst
  rcases hx with ⟨h1, hs⟩ | ⟨ms, i, m, hms, hm, hxm⟩
  · rcases hx₀ with ⟨h0, -⟩ | ⟨ms₀, i₀, m₀, hms₀, -, -⟩
    · rw [h1] at hst
      rw [h0] at hun
      exact hun hst
    · exact standalone_not_block hs ⟨ms₀, hms₀⟩
  · rcases hx₀ with ⟨-, hs₀⟩ | ⟨ms₀, i₀, m₀, hms₀, hm₀, hx₀m⟩
    · exact standalone_not_block hs₀ ⟨ms, hms⟩
    · obtain ⟨P, hP, hPp, hPo⟩ := walked_block_record hG hF hW hc hms hm hxm
      have hne : A ≠ x := by
        intro hAx
        rw [← hAx, hc] at hP
        have hcP : c = P := Option.some.inj hP
        rw [← hcP] at hPp
        exact proj_not_block hPp ⟨ms, hms⟩
      have hbs : BlockStored t envT A ms :=
        hwhole x A P c ms (find_isSome_of_storedAt hst) (hrun x P hP) hPo hne (hrun A c hc) hms
      rw [hms] at hms₀
      have hmm : ms = ms₀ := Ixon.ConstantInfo.muts.inj hms₀
      rw [← hmm] at hm₀
      obtain ⟨hmem, hctor⟩ := hbs i₀ m₀ hm₀
      rcases hx₀m with h | ⟨ind, j, hind, hj, h⟩
      · rw [h] at hun
        obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hmem
        exact hun (storedAt_of_find hci)
      · rw [h] at hun
        obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp (hctor ind j hind hj)
        exact hun (storedAt_of_find hci)

/-- **The start stores nothing a unit owns**, family records included. -/
theorem fresh_at_family (hG : TopGraph t E₀ seeds Top rank)
    (hF : FamilyGraph t envT E₀ Top rank fam twin adv Inner)
    (hwhole : ∀ (a B : _root_.Address) (c cb : Ixon.Constant) (ms : Array Ixon.MutConst),
      (envT.find? (keyOf t a)).isSome = true → Ix.Cert.recordAt E a = some c →
      Ix.Cert.ownerOf a c = B → B ≠ a → Ix.Cert.recordAt E B = some cb → cb.info = .muts ms →
      BlockStored t envT B ms)
    (hrun : ∀ a c, recordOf E₀ a = some c → Ix.Cert.recordAt E a = some c)
    (hus : ∀ A, A ∈ us ↔ IsUnit t envT E₀ Top Inner fam A) :
    (familyFold.{u} X t E₀ R E lim rank fam twin adv).FreshAt envT us := by
  intro A hA x hx hst
  obtain ⟨c, hc, hown | ⟨rb, crb, hrb, hcrb, hxr⟩⟩ := hx
  · exact unit_fresh hG hF hwhole hrun ((hus A).mp hA) hc hown hst
  · exact hF.famFresh A rb crb x hrb hcrb hxr hst

end Fold

end IxVM.Refinement.Typing
