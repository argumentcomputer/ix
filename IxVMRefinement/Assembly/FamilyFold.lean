import IxVMRefinement.Assembly.TypingSkeleton
import IxVMRefinement.Assembly.FamilyArm

/-! # The typing fold with modeled blocks that own their family records

A mutual or nested block is installed in full (its types, its constructors and the recursors of
its family record) at the block's own position. The family record is a separate record (a block
of recursors at `rb`), so its constant addresses are not the block's (`ConstAddrOf`), and the
typing fold of `Assembly/TypingSkeleton.lean` (a unit stores only its own record's constant
addresses, `UnitStep`, `typingFold`) cannot install it there. This module states the variant:

* `UnitStepFam`: the step of a block that installs its family record with it: it is handed what
  either record uses and the advice its family check validated stored, and stores at each
  constant address of either record a constant that stores its reading;
* `typingFoldFam … fam adv`: the fold in which a block `B` with `fam B = some rb` owns the
  constant addresses of its family record `rb` beside its own, and needs `rb`'s used references
  and the constant addresses of its advice `adv B`;
* the existing fold is the special case without families: at `fam = fun _ => none` and no advice
  the variant's ownership, needs and postcondition are the existing fold's
  (`famOwns_none`, `famNeeds_none`, `famPost_none`), so its steps are the existing fold's
  (`steps_fam_none`), and the skeleton theorem's conclusion follows from the variant's
  (`typing_skeleton_core_viaFam`);
* `FamGraph`: what the variant reads of the walk beside `TopGraph`: the family records are
  block records of recursors, never top-walked, claimed by one block each, fresh at the
  witness's environment, whose used references are top-walked below their block, covered, or
  the two records' own constant addresses; and each advice record is top-walked below its block;
* `owns_apart_fam`, `needs_earlier_fam`, `fold_steps_fam`, `typing_skeleton_core_fam`: the fold
  over the variant, from `UnitStep` for the units without a family and `UnitStepFam` for the
  blocks with one.

The fields of `FamGraph` are hypotheses: the claim layer's walk (with its inner records, the
advice and family records a block's check validates) is their intended producer, `famFresh`
and `famNotTop` aside (see the lane notes). -/

universe u

namespace IxVM.Refinement.Typing

open IxVM.Consistency
open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open Ix.Kernel (ConstantInfo ConstantVal)

set_option linter.unusedVariables false

/-! ## The records -/

/-- **A modeled block's record**: a block of inductives at `B`, in Lean's logic, whose member and
constructor projection records the run's store holds. -/
structure FamBlockRecord (E₀ : Ixon.Env) (B : _root_.Address) (cb : Ixon.Constant)
    (ms : Array Ixon.MutConst) : Prop where
  record : recordOf E₀ B = some cb
  muts : cb.info = .muts ms
  indcs : ∀ m ∈ ms.toList, ∃ ind, m = .indc ind
  logic : InLogic cb
  members : ∀ i m, ms[i]? = some m →
    recordOf E₀ (memberAddr B i m) = some (memberProjection B i m)
  ctors : ∀ i ind j, ms[i]? = some (.indc ind) → j < ind.ctors.size →
    recordOf E₀ (ctorAddr B i j) = some (constructorProjection B i j)

/-- **A family record**: a block of recursors at `rb`, in Lean's logic, whose member projection
records the run's store holds. -/
structure FamRecRecord (E₀ : Ixon.Env) (rb : _root_.Address) (crb : Ixon.Constant)
    (rs : Array Ixon.MutConst) : Prop where
  record : recordOf E₀ rb = some crb
  muts : crb.info = .muts rs
  recrs : ∀ m ∈ rs.toList, ∃ r, m = .recr r
  logic : InLogic crb
  members : ∀ i m, rs[i]? = some m →
    recordOf E₀ (memberAddr rb i m) = some (memberProjection rb i m)

/-- **A constant address of the family record holds a projection record of it.** -/
theorem FamRecRecord.constAddr {E₀ : Ixon.Env} {rb : _root_.Address} {crb : Ixon.Constant}
    {rs : Array Ixon.MutConst} (hR : FamRecRecord E₀ rb crb rs) {x : _root_.Address}
    (hx : ConstAddrOf rb crb x) :
    ∃ P, recordOf E₀ x = some P ∧ IsProj P ∧ Ix.Cert.ownerOf x P = rb := by
  rcases hx with ⟨-, hs⟩ | ⟨ms, i, m, hms, hm, hxm⟩
  · exact (standalone_not_block hs ⟨rs, hR.muts⟩).elim
  · rw [hR.muts] at hms
    have hrs : rs = ms := Ixon.ConstantInfo.muts.inj hms
    subst hrs
    rcases hxm with h | ⟨ind, j, hind, -, -⟩
    · rw [h]
      exact ⟨_, hR.members i m hm, memberProjection_isProj rb i m,
        ownerOf_memberProjection _ rb i m⟩
    · have hm' : rs.toList[i]? = some m := by simpa only [Array.getElem?_toList] using hm
      obtain ⟨r, hr⟩ := hR.recrs m (List.mem_of_getElem? hm')
      rw [hind] at hr
      cases hr

/-! ## The block arm's family evidence and the unit step -/

/-- **An advice record the family check validated**: a call of `check_advice_record` at `a`
among the family check's calls. -/
def AdviceIn (cs : List (Call F)) (a : _root_.Address) : Prop :=
  ∃ (rc xa seen wset : SourceValue F) (h : Heap F),
    (⟨"KernelModeled::check_advice_record", [rc, xa, seen, wset], h⟩ : Call F) ∈ cs ∧
    Core.BaseSeams.addr h xa a

/-- **A constant address of the block or of its family record.** -/
def FamAddr (B : _root_.Address) (cb : Ixon.Constant) (rb : _root_.Address)
    (crb : Ixon.Constant) (x : _root_.Address) : Prop :=
  ConstAddrOf B cb x ∨ ConstAddrOf rb crb x

/-- **The step of a unit that installs its family record with it.** `UnitStep` of the block at
`A` with the record at `rb` joined: the step is handed what either record uses and the advice
`adv` stored, and none of their constant addresses; it stores at each constant address of
either record a constant that stores its reading, and nothing else outside derived keys. -/
def UnitStepFam (X : Ix.Kernel.Env .anon → Prop) (t : Ix.Kernel.RoleTable)
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
    (∀ x, FamAddr A c rb crb x → env.find? (keyOf t x) = none) →
    ∃ new : List (ConstantInfo .anon),
      (new.map (·.name)).Nodup ∧ (∀ ci ∈ new, env.find? ci.name = none) ∧
      Decl.PrefixInv.{u} E t lim ⟨new ++ env.consts⟩ ∧ X ⟨new ++ env.consts⟩ ∧
      (∀ x, FamAddr A c rb crb x →
        ∃ ci ∈ new, ∃ ci₀, ci.name = keyOf t x ∧ Reads t E₀ x ci₀ ∧ StoredAs ci ci₀) ∧
      ∀ ci ∈ new, (∃ x, FamAddr A c rb crb x ∧ ci.name = keyOf t x) ∨ ∃ k s, ci.name = .aux k s

/-! ## The fold variant -/

/-- **What a unit owns, its family record's constant addresses joined**: the constant addresses
of the record at `A`, and those of the family record `fam A` names. -/
def FamOwns (E₀ : Ixon.Env) (fam : _root_.Address → Option _root_.Address)
    (A x : _root_.Address) : Prop :=
  ∃ c, recordOf E₀ A = some c ∧
    (ConstAddrOf A c x ∨
      ∃ rb crb, fam A = some rb ∧ recordOf E₀ rb = some crb ∧ ConstAddrOf rb crb x)

/-- **What a unit needs**: the in-logic constant addresses its record or its family record
uses, and the constant addresses of the advice its family check validated. -/
def FamNeeds (E₀ : Ixon.Env) (fam : _root_.Address → Option _root_.Address)
    (adv : _root_.Address → _root_.Address → Prop) (A x : _root_.Address) : Prop :=
  ((UsedRef E₀ A x ∨ ∃ rb, fam A = some rb ∧ UsedRef E₀ rb x) ∧ NeedOk E₀ x) ∨
    ∃ a ca, adv A a ∧ recordOf E₀ a = some ca ∧ ConstAddrOf a ca x

/-- **The typing run as a system of units, blocks owning their family records**: as
`typingFold`, with ownership `FamOwns` and needs `FamNeeds`; the postcondition stores a kept
reading at every address the unit owns. -/
def typingFoldFam (X : Ix.Kernel.Env .anon → Prop) (t : Ix.Kernel.RoleTable)
    (E₀ R E : Ixon.Env) (lim : Option Nat) (rank : _root_.Address → Nat)
    (fam : _root_.Address → Option _root_.Address)
    (adv : _root_.Address → _root_.Address → Prop) :
    UnitFold (Ix.Kernel.Env .anon) _root_.Address _root_.Address where
  Inv := FoldInv.{u} X t E₀ R E lim
  Ext := fun env env' => ∀ ci ∈ env.consts, ci ∈ env'.consts
  Stored := StoredAt t
  Post := fun A env => ∀ x, FamOwns E₀ fam A x →
    ∃ ci ∈ env.consts, ci.name = keyOf t x ∧ KeptIn t (storeOver E₀ R) (blobOver E₀ R) x ci
  owns := FamOwns E₀ fam
  needs := FamNeeds E₀ fam adv
  rank := rank
  ext_refl := fun _ _ h => h
  ext_trans := fun h₁ h₂ ci hci => h₂ ci (h₁ ci hci)
  stored_mono := fun x h hx => by
    obtain ⟨ci, hci, hname⟩ := hx
    exact ⟨ci, h ci hci, hname⟩
  post_mono := fun A h hp x hx => by
    obtain ⟨ci, hci, hname, hk⟩ := hp x hx
    exact ⟨ci, h ci hci, hname, hk⟩

/-! ## The existing fold is the case without families -/

section NoFamily

variable {X : Ix.Kernel.Env .anon → Prop} {t : Ix.Kernel.RoleTable} {R E₀ E : Ixon.Env}
  {lim : Option Nat} {rank : _root_.Address → Nat}

/-- Without families a unit owns its record's constant addresses. -/
theorem famOwns_none (A x : _root_.Address) :
    FamOwns E₀ (fun _ => none) A x ↔ (typingFold.{u} X t E₀ R E lim rank).owns A x := by
  constructor
  · rintro ⟨c, hc, hx | ⟨rb, crb, hrb, -⟩⟩
    · exact ⟨c, hc, hx⟩
    · cases hrb
  · rintro ⟨c, hc, hx⟩
    exact ⟨c, hc, Or.inl hx⟩

/-- Without families or advice a unit needs the in-logic constant addresses its record uses. -/
theorem famNeeds_none (A x : _root_.Address) :
    FamNeeds E₀ (fun _ => none) (fun _ _ => False) A x ↔
      (typingFold.{u} X t E₀ R E lim rank).needs A x := by
  constructor
  · rintro (⟨hu | ⟨rb, hrb, -⟩, hok⟩ | ⟨a, ca, ha, -⟩)
    · exact ⟨hu, hok⟩
    · cases hrb
    · exact False.elim ha
  · rintro ⟨hu, hok⟩
    exact Or.inl ⟨Or.inl hu, hok⟩

/-- Without families the postcondition is the existing fold's. -/
theorem famPost_none (A : _root_.Address) (env : Ix.Kernel.Env .anon) :
    (typingFoldFam.{u} X t E₀ R E lim rank (fun _ => none) (fun _ _ => False)).Post A env ↔
      (typingFold.{u} X t E₀ R E lim rank).Post A env := by
  constructor
  · intro hp c hc x hx
    exact hp x ⟨c, hc, Or.inl hx⟩
  · intro hp x hx
    obtain ⟨c, hc, hx | ⟨rb, crb, hrb, -⟩⟩ := hx
    · exact hp c hc x hx
    · cases hrb

/-- **The existing fold's steps are the variant's without families.** -/
theorem steps_fam_none {s₀ : Ix.Kernel.Env .anon} {us : List _root_.Address}
    (h : (typingFold.{u} X t E₀ R E lim rank).Steps s₀ us) :
    (typingFoldFam.{u} X t E₀ R E lim rank (fun _ => none) (fun _ _ => False)).Steps s₀ us := by
  intro s A hA hinv hext hneed hfr
  have hO : ∀ x, FamOwns E₀ (fun _ => none) A x ↔
      (typingFold.{u} X t E₀ R E lim rank).owns A x :=
    fun x => famOwns_none (X := X) (R := R) (E := E) (lim := lim) (rank := rank) A x
  have hN : ∀ x, FamNeeds E₀ (fun _ => none) (fun _ _ => False) A x ↔
      (typingFold.{u} X t E₀ R E lim rank).needs A x :=
    fun x => famNeeds_none (X := X) (R := R) (E := E) (lim := lim) (rank := rank) A x
  have hP : ∀ env, (typingFoldFam.{u} X t E₀ R E lim rank (fun _ => none)
      (fun _ _ => False)).Post A env ↔ (typingFold.{u} X t E₀ R E lim rank).Post A env :=
    fun env => famPost_none A env
  obtain ⟨s', hinv', hext', hown', hpost', hframe'⟩ := h s A hA hinv hext
    (fun x hx => (hneed x ((hN x).mpr hx)).imp id (hO x).mp)
    (fun x hx => hfr x ((hO x).mpr hx))
  exact ⟨s', hinv', hext', fun x hx => hown' x ((hO x).mp hx), (hP s').mpr hpost',
    fun x hx => (hframe' x hx).imp id (hO x).mpr⟩

end NoFamily

/-! ## What the variant reads of the walk -/

/-- **The family records and the advice, against the walk** (`TopGraph`'s companion for the
variant): a block claiming a family record is a top-walked block record; the family record is a
block of recursors whose member records the store holds, is never top-walked, is claimed by one
block, and stores no constant address at the witness's environment; a reference it uses is
top-walked below its block, covered, or a constant address of the block or of itself; and each
advice record of a block's family check is top-walked below the block, in Lean's logic. -/
structure FamGraph (t : Ix.Kernel.RoleTable) (envT : Ix.Kernel.Env .anon) (E₀ : Ixon.Env)
    (Top : _root_.Address → Prop) (rank : _root_.Address → Nat)
    (fam : _root_.Address → Option _root_.Address)
    (adv : _root_.Address → _root_.Address → Prop) : Prop where
  famBlock : ∀ B rb, fam B = some rb → Top B
  famRecord : ∀ B rb, fam B = some rb → ∃ crb rs, FamRecRecord E₀ rb crb rs
  famNotTop : ∀ B rb, fam B = some rb → ¬ Top rb
  famInj : ∀ B B' rb, fam B = some rb → fam B' = some rb → B = B'
  famFresh : ∀ B rb crb x, fam B = some rb → recordOf E₀ rb = some crb →
    ConstAddrOf rb crb x → ¬ StoredAt t envT x
  famClosed : ∀ B rb x, fam B = some rb → UsedRef E₀ rb x →
    (Top x ∧ rank x < rank B) ∨ Covered t x ∨
      (∃ cb, recordOf E₀ B = some cb ∧ ConstAddrOf B cb x) ∨
      (∃ crb, recordOf E₀ rb = some crb ∧ ConstAddrOf rb crb x)
  advEarlier : ∀ B a, adv B a →
    Top a ∧ rank a < rank B ∧ ∀ ca, recordOf E₀ a = some ca → InLogic ca

/-- **The walk alone, without families or advice.** -/
theorem famGraph_none {t : Ix.Kernel.RoleTable} {envT : Ix.Kernel.Env .anon} {E₀ : Ixon.Env}
    {Top : _root_.Address → Prop} {rank : _root_.Address → Nat} :
    FamGraph t envT E₀ Top rank (fun _ => none) (fun _ _ => False) where
  famBlock := fun _ _ h => nomatch h
  famRecord := fun _ _ h => nomatch h
  famNotTop := fun _ _ h => nomatch h
  famInj := fun _ _ _ h => nomatch h
  famFresh := fun _ _ _ _ h => nomatch h
  famClosed := fun _ _ _ h => nomatch h
  advEarlier := fun _ _ h => False.elim h

/-! ## The fold over the variant -/

section Fold

variable {X : Ix.Kernel.Env .anon → Prop} {t : Ix.Kernel.RoleTable} {R E₀ E : Ixon.Env}
  {envT : Ix.Kernel.Env .anon} {seeds : List _root_.Address} {Top : _root_.Address → Prop}
  {rank : _root_.Address → Nat} {lim : Option Nat} {us : List _root_.Address}
  {fam : _root_.Address → Option _root_.Address} {adv : _root_.Address → _root_.Address → Prop}

/-- A family record's constant address is no constant address of a top-walked record. -/
theorem fam_not_own (hG : TopGraph t E₀ seeds Top rank)
    (hF : FamGraph t envT E₀ Top rank fam adv) {A B rb : _root_.Address}
    {c crb : Ixon.Constant} {x : _root_.Address} (hT : Top A) (hc : recordOf E₀ A = some c)
    (hx : ConstAddrOf A c x) (hrb : fam B = some rb) (hcrb : recordOf E₀ rb = some crb)
    (hxr : ConstAddrOf rb crb x) : False := by
  obtain ⟨crb', rs, hR⟩ := hF.famRecord B rb hrb
  have hcc : crb' = crb := Option.some.inj (hR.record.symm.trans hcrb)
  subst hcc
  obtain ⟨P, hP, hPp, hPo⟩ := hR.constAddr hxr
  rcases hG.constAddr_cases hT hc hx with ⟨h1, hs⟩ | ⟨-, P', hP', -, hPo'⟩
  · rw [h1, hc] at hP
    have : c = P := Option.some.inj hP
    subst this
    exact standalone_not_proj hs hPp
  · have hPP : P' = P := Option.some.inj (hP'.symm.trans hP)
    rw [hPP] at hPo'
    have hAr : A = rb := hPo'.symm.trans hPo
    rw [hAr] at hT
    exact hF.famNotTop B rb hrb hT

/-- **Distinct units own disjoint addresses, family records included.** -/
theorem owns_apart_fam (hG : TopGraph t E₀ seeds Top rank)
    (hF : FamGraph t envT E₀ Top rank fam adv)
    (hus : ∀ A, A ∈ us ↔ IsAnchor t envT E₀ Top A) :
    (typingFoldFam.{u} X t E₀ R E lim rank fam adv).OwnsApart us := by
  intro A hA A' hA' x hx hx'
  have hT := ((hus A).mp hA).1
  have hT' := ((hus A').mp hA').1
  obtain ⟨c, hc, hown | ⟨rb, crb, hrb, hcrb, hxr⟩⟩ := hx <;>
    obtain ⟨c', hc', hown' | ⟨rb', crb', hrb', hcrb', hxr'⟩⟩ := hx'
  · exact hG.owns_apart hT hT' hc hc' hown hown'
  · exact (fam_not_own hG hF hT hc hown hrb' hcrb' hxr').elim
  · exact (fam_not_own hG hF hT' hc' hown' hrb hcrb hxr).elim
  · obtain ⟨crb₁, rs, hR⟩ := hF.famRecord A rb hrb
    obtain ⟨crb₂, rs', hR'⟩ := hF.famRecord A' rb' hrb'
    have h1 : crb₁ = crb := Option.some.inj (hR.record.symm.trans hcrb)
    have h2 : crb₂ = crb' := Option.some.inj (hR'.record.symm.trans hcrb')
    subst h1 h2
    obtain ⟨P, hP, -, hPo⟩ := hR.constAddr hxr
    obtain ⟨P', hP', -, hPo'⟩ := hR'.constAddr hxr'
    have : P' = P := Option.some.inj (hP'.symm.trans hP)
    subst this
    have hrr : rb = rb' := hPo.symm.trans hPo'
    subst hrr
    exact hF.famInj A A' rb hrb hrb'

/-- A top-walked in-logic reference of rank below `rank A` that is not a block is stored by
the witness's environment or owned by a unit of rank below `rank A`. -/
theorem earlier_of_top (hG : TopGraph t E₀ seeds Top rank)
    (hus : ∀ A, A ∈ us ↔ IsAnchor t envT E₀ Top A) {A x : _root_.Address}
    (hTx : Top x) (hrk : rank x < rank A) (hok : NeedOk E₀ x) :
    StoredAt t envT x ∨
      ∃ b ∈ us, (typingFoldFam.{u} X t E₀ R E lim rank fam adv).owns b x ∧ rank b < rank A := by
  obtain ⟨cx, hcx, hnb, hlog, hlogB⟩ := hok
  by_cases hst : StoredAt t envT x
  · exact Or.inl hst
  · rcases kind_cases cx with hsa | hpr | hbl
    · exact Or.inr ⟨x, (hus x).mpr ⟨hTx, cx, hcx, hlog, x, Or.inl ⟨rfl, hsa⟩, hst⟩,
        ⟨cx, hcx, Or.inl (Or.inl ⟨rfl, hsa⟩)⟩, hrk⟩
    · obtain ⟨hTB, hrkB⟩ := hG.owner x cx hTx hcx hpr
      obtain ⟨cb, hcb, hconst⟩ := hG.projMember x cx hTx hcx hpr
      exact Or.inr ⟨Ix.Cert.ownerOf x cx,
        (hus _).mpr ⟨hTB, cb, hcb, hlogB cb hcb, x, hconst, hst⟩,
        ⟨cb, hcb, Or.inl hconst⟩, Nat.lt_trans hrkB hrk⟩
    · exact absurd hbl hnb

/-- **Every address a unit needs is stored by the witness's environment, owned by the unit, or
owned by a unit of smaller rank**, family records and advice included. -/
theorem needs_earlier_fam (hG : TopGraph t E₀ seeds Top rank)
    (hF : FamGraph t envT E₀ Top rank fam adv)
    (hshape : TableShape.{u} t (fun _ => True) R envT) (htwf : t.wf = true)
    (hus : ∀ A, A ∈ us ↔ IsAnchor t envT E₀ Top A) :
    (typingFoldFam.{u} X t E₀ R E lim rank fam adv).NeedsEarlier envT us := by
  intro A hA x hneed
  have hAn := (hus A).mp hA
  rcases hneed with ⟨hu | ⟨rb, hrb, hur⟩, hok⟩ | ⟨a, ca, ha, hca, hxa⟩
  · rcases hG.closed A x hAn.1 hu with ⟨hTx, hrk⟩ | hcov
    · rcases earlier_of_top.{u} (X := X) (R := R) (E := E) (lim := lim) (fam := fam) (adv := adv)
        hG hus hTx hrk hok with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · exact Or.inl (covered_stored hshape htwf hcov)
  · rcases hF.famClosed A rb x hrb hur with ⟨hTx, hrk⟩ | hcov | ⟨cb, hcb, hxB⟩ | ⟨crb, hcrb, hxr⟩
    · rcases earlier_of_top.{u} (X := X) (R := R) (E := E) (lim := lim) (fam := fam) (adv := adv)
        hG hus hTx hrk hok with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · exact Or.inl (covered_stored hshape htwf hcov)
    · exact Or.inr (Or.inl ⟨cb, hcb, Or.inl hxB⟩)
    · obtain ⟨cA, hcA, -⟩ := hAn.2
      exact Or.inr (Or.inl ⟨cA, hcA, Or.inr ⟨rb, crb, hrb, hcrb, hxr⟩⟩)
  · obtain ⟨hTa, hrk, hlog⟩ := hF.advEarlier A a ha
    by_cases hst : StoredAt t envT x
    · exact Or.inl hst
    · exact Or.inr (Or.inr ⟨a, (hus a).mpr ⟨hTa, ca, hca, hlog ca hca, x, hxa, hst⟩,
        ⟨ca, hca, Or.inl hxa⟩, hrk⟩)

/-- **The start stores nothing a unit owns**, family records included. -/
theorem fresh_at_fam (hG : TopGraph t E₀ seeds Top rank)
    (hF : FamGraph t envT E₀ Top rank fam adv)
    (hwhole : ∀ (a B : _root_.Address) (c cb : Ixon.Constant) (ms : Array Ixon.MutConst),
      (envT.find? (keyOf t a)).isSome = true → Ix.Cert.recordAt E a = some c →
      Ix.Cert.ownerOf a c = B → B ≠ a → Ix.Cert.recordAt E B = some cb → cb.info = .muts ms →
      BlockStored t envT B ms)
    (hrun : ∀ a c, recordOf E₀ a = some c → Ix.Cert.recordAt E a = some c)
    (hus : ∀ A, A ∈ us ↔ IsAnchor t envT E₀ Top A) :
    (typingFoldFam.{u} X t E₀ R E lim rank fam adv).FreshAt envT us := by
  intro A hA x hx hst
  obtain ⟨c, hc, hown | ⟨rb, crb, hrb, hcrb, hxr⟩⟩ := hx
  · exact anchor_fresh hG hwhole hrun ((hus A).mp hA) hc hown hst
  · exact hF.famFresh A rb crb x hrb hcrb hxr hst

/-- A reading kept over the run of a constant address that holds no axiom record. -/
private theorem kept_of_reads {t : Ix.Kernel.RoleTable} {E₀ R : Ixon.Env} {x : _root_.Address}
    {ci ci₀ : ConstantInfo .anon} (hr : Reads t E₀ x ci₀) (hst : StoredAs ci ci₀)
    (hnax : ∀ c' ax, recordOf E₀ x = some c' → c'.info = .axio ax → False) :
    KeptIn t (storeOver E₀ R) (blobOver E₀ R) x ci :=
  keptIn_over_run ⟨fun c' ax hc' hinfo => (hnax c' ax hc' hinfo).elim, ci₀, hr, hst⟩

/-- **The steps of the variant**, from `UnitStep` for each unit without a family record and
`UnitStepFam` for each block with one. -/
theorem fold_steps_fam (hG : TopGraph t E₀ seeds Top rank)
    (hF : FamGraph t envT E₀ Top rank fam adv)
    (hshape : TableShape.{u} t (fun _ => True) R envT) (htwf : t.wf = true)
    (hroles : (t.bound.toList.map (·.1)).Nodup)
    (hwhole : ∀ (a B : _root_.Address) (c cb : Ixon.Constant) (ms : Array Ixon.MutConst),
      (envT.find? (keyOf t a)).isSome = true → Ix.Cert.recordAt E a = some c →
      Ix.Cert.ownerOf a c = B → B ≠ a → Ix.Cert.recordAt E B = some cb → cb.info = .muts ms →
      BlockStored t envT B ms)
    (hrun : ∀ a c, recordOf E₀ a = some c → Ix.Cert.recordAt E a = some c)
    (hus : ∀ A, A ∈ us ↔ IsAnchor t envT E₀ Top A)
    (hstep : ∀ A c, Top A → recordOf E₀ A = some c → InLogic c → UnitKind c → fam A = none →
      UnitStep.{u} X t envT E₀ E lim A c)
    (hstepFam : ∀ A c rb crb rs, Top A → recordOf E₀ A = some c → InLogic c → UnitKind c →
      fam A = some rb → FamRecRecord E₀ rb crb rs →
      UnitStepFam.{u} X t envT E₀ E lim A c rb crb (adv A)) :
    (typingFoldFam.{u} X t E₀ R E lim rank fam adv).Steps envT us := by
  intro env A hA hinv hext hneed hfr
  have hFI : FoldInv.{u} X t E₀ R E lim env := hinv
  have hextT : ∀ ci ∈ envT.consts, ci ∈ env.consts := hext
  have hAn := (hus A).mp hA
  obtain ⟨hT, c, hc, hlog, x₀, hx₀, hun⟩ := hAn
  have hkind : UnitKind c := by
    rcases kind_cases c with hsa | hpr | hbl
    · rcases hsa with ⟨d, h⟩ | ⟨rc, h⟩ | hax | hq
      · exact Or.inl ⟨d, h⟩
      · exact Or.inr (Or.inl ⟨rc, h⟩)
      · exfalso
        obtain ⟨r, hr, ha⟩ := hG.standing A c hT hc (Or.inl hax)
        exact anchor_fresh hG hwhole hrun ((hus A).mp hA) hc
          (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inl hax))⟩) (standing_stored hshape htwf hr ha)
      · exfalso
        obtain ⟨r, hr, ha⟩ := hG.standing A c hT hc (Or.inr hq)
        exact anchor_fresh hG hwhole hrun ((hus A).mp hA) hc
          (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr hq))⟩) (standing_stored hshape htwf hr ha)
    · exfalso
      rcases hx₀ with ⟨-, hs⟩ | ⟨ms, i, m, hms, -, -⟩
      · exact standalone_not_proj hs hpr
      · exact proj_not_block hpr ⟨ms, hms⟩
    · exact Or.inr (Or.inr hbl)
  -- an own constant address holds no axiom record
  have hnaxA : ∀ x, ConstAddrOf A c x → ∀ c' ax, recordOf E₀ x = some c' →
      c'.info = .axio ax → False := by
    intro x hx c' ax hc' hinfo
    rcases hG.constAddr_cases hT hc hx with ⟨h1, -⟩ | ⟨-, P, hP, hPp, -⟩
    · rw [h1, hc] at hc'
      have hcc : c = c' := Option.some.inj hc'
      rw [← hcc] at hinfo
      rcases hkind with ⟨d, h⟩ | ⟨rc, h⟩ | ⟨ms, h⟩ <;> (rw [h] at hinfo; cases hinfo)
    · rw [hP] at hc'
      have hcc : P = c' := Option.some.inj hc'
      rw [← hcc] at hinfo
      rcases hPp with ⟨p, h⟩ | ⟨p, h⟩ | ⟨p, h⟩ | ⟨p, h⟩ <;> (rw [h] at hinfo; cases hinfo)
  -- the frame and the new state, once the step has given `new` at the owned addresses
  have hfinish : ∀ (new : List (ConstantInfo .anon)) (Own : _root_.Address → Prop),
      (∀ x, Own x ↔ FamOwns E₀ fam A x) →
      (new.map (·.name)).Nodup → (∀ ci ∈ new, env.find? ci.name = none) →
      Decl.PrefixInv.{u} E t lim ⟨new ++ env.consts⟩ → X ⟨new ++ env.consts⟩ →
      (∀ x, Own x → ∃ ci ∈ new, ci.name = keyOf t x ∧
        KeptIn t (storeOver E₀ R) (blobOver E₀ R) x ci) →
      (∀ ci ∈ new, (∃ x, Own x ∧ ci.name = keyOf t x) ∨ ∃ k s, ci.name = .aux k s) →
      ∃ s', (typingFoldFam.{u} X t E₀ R E lim rank fam adv).Inv s' ∧
        (∀ ci ∈ env.consts, ci ∈ s'.consts) ∧
        (∀ x, FamOwns E₀ fam A x → StoredAt t s' x) ∧
        (typingFoldFam.{u} X t E₀ R E lim rank fam adv).Post A s' ∧
        ∀ x, StoredAt t s' x → StoredAt t env x ∨ FamOwns E₀ fam A x := by
    intro new Own hOwn hnd' hfresh' hinv' hX' hkept hnames
    have hgrow : Ix.Kernel.Grows (fun _ => True) env ⟨new ++ env.consts⟩ :=
      ⟨new, rfl, fun ci hci => ⟨trivial, hfresh' ci hci⟩, hnd'⟩
    have hprov : ∀ ci ∈ (claimedEnv ⟨new ++ env.consts⟩).consts,
        (∃ tbl, ci = .projInfo tbl) ∨ PinnedBasis ci ∨
          ∃ a, KeptIn t (storeOver E₀ R) (blobOver E₀ R) a ci := by
      intro ci hci
      obtain ⟨hmem, hkeep⟩ := List.mem_filter.mp hci
      rcases List.mem_append.mp hmem with hnew | hold
      · rcases hnames ci hnew with ⟨x, hx, hname⟩ | haux
        · obtain ⟨ci', hci', hname', hk⟩ := hkept x hx
          have hcc : ci' = ci := eq_of_name_eq hnd' hci' hnew (hname'.trans hname.symm)
          rw [hcc] at hk
          exact Or.inr (Or.inr ⟨x, hk⟩)
        · exact Or.inl (projInfo_of_aux haux (by simpa using hkeep))
      · exact hFI.prov ci (List.mem_filter.mpr ⟨hold, hkeep⟩)
    have hFI' : FoldInv.{u} X t E₀ R E lim ⟨new ++ env.consts⟩ :=
      ⟨hgrow.nodup hFI.nodup, hinv', hX', hprov⟩
    refine ⟨⟨new ++ env.consts⟩, hFI', fun ci hci => List.mem_append_right _ hci, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨ci, hci, hname, -⟩ := hkept x ((hOwn x).mpr hx)
      exact ⟨ci, List.mem_append_left _ hci, hname⟩
    · intro x hx
      obtain ⟨ci, hci, hname, hk⟩ := hkept x ((hOwn x).mpr hx)
      exact ⟨ci, List.mem_append_left _ hci, hname, hk⟩
    · intro x hx
      obtain ⟨ci, hci, hname⟩ := hx
      rcases List.mem_append.mp hci with hnew | hold
      · rcases hnames ci hnew with ⟨x', hx', hname'⟩ | ⟨k, s, haux⟩
        · have hxx : x = x' := keyOf_inj hroles (hname.symm.trans hname')
          rw [hxx]
          exact Or.inr ((hOwn x').mp hx')
        · exact absurd (hname.symm.trans haux) (keyOf_nonAux t x k s)
      · exact Or.inl ⟨ci, hold, hname⟩
  cases hfa : fam A with
  | none =>
    have hOwn : ∀ x, ConstAddrOf A c x ↔ FamOwns E₀ fam A x := by
      intro x
      constructor
      · intro hx
        exact ⟨c, hc, Or.inl hx⟩
      · rintro ⟨c', hc', hx | ⟨rb, crb, hrb, -⟩⟩
        · rw [hc] at hc'
          have hcc : c = c' := Option.some.inj hc'
          rw [hcc]
          exact hx
        · rw [hfa] at hrb
          cases hrb
    have hrefs : ∀ x, UsedRef E₀ A x →
        (env.find? (keyOf t x)).isSome = true ∨ ConstAddrOf A c x ∨ ¬ NeedOk E₀ x := by
      intro x hused
      by_cases hok : NeedOk E₀ x
      · rcases hneed x (Or.inl ⟨Or.inl hused, hok⟩) with hs | hown
        · exact Or.inl (find_isSome_of_storedAt hs)
        · exact Or.inr (Or.inl ((hOwn x).mpr hown))
      · exact Or.inr (Or.inr hok)
    have hfresh : ∀ x, ConstAddrOf A c x → env.find? (keyOf t x) = none :=
      fun x hx => find_none_of_not_storedAt (hfr x ((hOwn x).mp hx))
    obtain ⟨new, hnd', hfresh', hinv', hX', hreads, hnames⟩ :=
      hstep A c hT hc hlog hkind hfa env hextT hFI.nodup hFI.inv hFI.extra hrefs hfresh
    obtain ⟨s', h1, h2, h3, h4, h5⟩ := hfinish new (ConstAddrOf A c) hOwn hnd' hfresh' hinv' hX'
      (fun x hx => by
        obtain ⟨ci, hci, ci₀, hname, hr, hst⟩ := hreads x hx
        exact ⟨ci, hci, hname, kept_of_reads hr hst (hnaxA x hx)⟩)
      hnames
    exact ⟨s', h1, h2, h3, h4, h5⟩
  | some rb =>
    obtain ⟨crb, rs, hR⟩ := hF.famRecord A rb hfa
    have hOwn : ∀ x, FamAddr A c rb crb x ↔ FamOwns E₀ fam A x := by
      intro x
      constructor
      · rintro (hx | hx)
        · exact ⟨c, hc, Or.inl hx⟩
        · exact ⟨c, hc, Or.inr ⟨rb, crb, hfa, hR.record, hx⟩⟩
      · rintro ⟨c', hc', hx | ⟨rb', crb', hrb', hcrb', hx⟩⟩
        · rw [hc] at hc'
          have hcc : c = c' := Option.some.inj hc'
          rw [hcc]
          exact Or.inl hx
        · rw [hfa] at hrb'
          have hrr : rb = rb' := Option.some.inj hrb'
          subst hrr
          have hcc : crb = crb' := Option.some.inj (hR.record.symm.trans hcrb')
          subst hcc
          exact Or.inr hx
    have hrefs : ∀ x, UsedRef E₀ A x ∨ UsedRef E₀ rb x →
        (env.find? (keyOf t x)).isSome = true ∨ FamAddr A c rb crb x ∨ ¬ NeedOk E₀ x := by
      intro x hused
      by_cases hok : NeedOk E₀ x
      · have hn : FamNeeds E₀ fam adv A x := by
          refine Or.inl ⟨?_, hok⟩
          rcases hused with h | h
          · exact Or.inl h
          · exact Or.inr ⟨rb, hfa, h⟩
        rcases hneed x hn with hs | hown
        · exact Or.inl (find_isSome_of_storedAt hs)
        · exact Or.inr (Or.inl ((hOwn x).mpr hown))
      · exact Or.inr (Or.inr hok)
    have hadv : ∀ a, adv A a → ∀ ca, recordOf E₀ a = some ca → ∀ x, ConstAddrOf a ca x →
        (env.find? (keyOf t x)).isSome = true := by
      intro a ha ca hca x hxa
      rcases hneed x (Or.inr ⟨a, ca, ha, hca, hxa⟩) with hs | hown
      · exact find_isSome_of_storedAt hs
      · by_cases hstT : StoredAt t envT x
        · obtain ⟨ci, hci, hname⟩ := hstT
          exact find_isSome_of_storedAt ⟨ci, hextT ci hci, hname⟩
        · exfalso
          obtain ⟨hTa, hrk, hloga⟩ := hF.advEarlier A a ha
          have haU : a ∈ us := (hus a).mpr ⟨hTa, ca, hca, hloga ca hca, x, hxa, hstT⟩
          have hAa : a = A :=
            owns_apart_fam.{u} (X := X) (R := R) (E := E) (lim := lim) hG hF hus
              a haU A hA x ⟨ca, hca, Or.inl hxa⟩ hown
          rw [hAa] at hrk
          exact Nat.lt_irrefl _ hrk
    have hfresh : ∀ x, FamAddr A c rb crb x → env.find? (keyOf t x) = none :=
      fun x hx => find_none_of_not_storedAt (hfr x ((hOwn x).mp hx))
    obtain ⟨new, hnd', hfresh', hinv', hX', hreads, hnames⟩ :=
      hstepFam A c rb crb rs hT hc hlog hkind hfa hR env hextT hFI.nodup hFI.inv hFI.extra
        hrefs hadv hfresh
    have hnax : ∀ x, FamAddr A c rb crb x → ∀ c' ax, recordOf E₀ x = some c' →
        c'.info = .axio ax → False := by
      rintro x (hx | hx) c' ax hc' hinfo
      · exact hnaxA x hx c' ax hc' hinfo
      · obtain ⟨P, hP, hPp, -⟩ := hR.constAddr hx
        rw [hP] at hc'
        have hcc : P = c' := Option.some.inj hc'
        rw [← hcc] at hinfo
        rcases hPp with ⟨p, h⟩ | ⟨p, h⟩ | ⟨p, h⟩ | ⟨p, h⟩ <;> (rw [h] at hinfo; cases hinfo)
    obtain ⟨s', h1, h2, h3, h4, h5⟩ := hfinish new (FamAddr A c rb crb) hOwn hnd' hfresh'
      hinv' hX'
      (fun x hx => by
        obtain ⟨ci, hci, ci₀, hname, hr, hst⟩ := hreads x hx
        exact ⟨ci, hci, hname, kept_of_reads hr hst (hnax x hx)⟩)
      hnames
    exact ⟨s', h1, h2, h3, h4, h5⟩

end Fold

/-! ## The skeleton over the variant -/

section Skeleton

variable {t : Ix.Kernel.RoleTable} {R E₀ : Ixon.Env} {envT : Ix.Kernel.Env .anon}
  {seeds : List _root_.Address} {calls : List (Call F)}
  {Top : _root_.Address → Prop} {rank : _root_.Address → Nat}

/-- **The typing conclusion from the walk and the steps, blocks installing their family
records**, where the run hashed no collision: `typing_skeleton_core` over `typingFoldFam`, the
units without a family stepped by `UnitStep` and the blocks with one by `UnitStepFam`. -/
theorem typing_skeleton_core_fam {V : View} {extra : List ByteArray}
    {X : Ix.Kernel.Env .anon → Prop} {lim : Option Nat}
    {fam : _root_.Address → Option _root_.Address} {adv : _root_.Address → _root_.Address → Prop}
    (hshape : TableShape.{u} t (fun _ => True) R envT)
    (hfacts : Facts.{u} t (fun _ => True) R envT) (hX : X envT) (ht : t.check = .ok ())
    (hb : Bounded calls) (hextra : ∀ x ∈ committedFootprint, x ∈ extra)
    (hnc : ¬ CollisionWith V extra R calls) (hS : LoadedReads.RunStore calls E₀)
    (hG : TopGraph t E₀ seeds Top rank) (hF : FamGraph t envT E₀ Top rank fam adv)
    (hstep : ∀ E, StepCtx.{u} calls t R envT E₀ E → ∀ A c, Top A → recordOf E₀ A = some c →
      InLogic c → UnitKind c → fam A = none → UnitStep.{u} X t envT E₀ E lim A c)
    (hstepFam : ∀ E, StepCtx.{u} calls t R envT E₀ E → ∀ A c rb crb rs, Top A →
      recordOf E₀ A = some c → InLogic c → UnitKind c → fam A = some rb →
      FamRecRecord E₀ rb crb rs → UnitStepFam.{u} X t envT E₀ E lim A c rb crb (adv A)) :
    ConsistentReadOver.{u} calls t R envT seeds := by
  have htwf : t.wf = true := by
    unfold Ix.Kernel.RoleTable.wf
    rw [ht]
    rfl
  have hroles : (t.bound.toList.map (·.1)).Nodup := (Ix.Kernel.RoleTable.check_nodup ht).1
  have hload : LoadedBy calls E₀ := hS.loaded
  have hdec : Ingress.EnvDecoded E₀ := hS.decoded
  obtain ⟨E, hM⟩ := merged_exists E₀ R
  have hrf : RecordsFor R E := hM.recordsFor hload hdec hshape.committed hextra hnc
  have hrun : ∀ a c, recordOf E₀ a = some c → Ix.Cert.recordAt E a = some c :=
    fun a c h => hM.run_record hload hdec hextra hnc h
  have hctx : StepCtx.{u} calls t R envT E₀ E :=
    ⟨hshape, hrf, hrun, fun a b h => hM.run_blob hload hnc h,
      fun env lim => hM.good hload hshape.zeroFree hextra hnc hb env t lim⟩
  have hrec := records_agree hload hnc
  have hblob := blobs_agree hload hnc
  have hinvT : Decl.PrefixInv.{u} E t lim envT := hfacts.inv E hrf lim (limWithin_all t lim)
  have hwhole := hfacts.whole E hrf
  obtain ⟨us, hus⟩ := exists_list_of_records E₀ (IsAnchor t envT E₀ Top)
    (fun A hA => hG.record A hA.1)
  have h₀ : FoldInv.{u} X t E₀ R E lim envT :=
    ⟨hshape.reading.nodup, hinvT, hX,
      provenance_over_witness hrec hblob hshape.reading.provenance⟩
  obtain ⟨env, hinv, hext, hdone, -⟩ :=
    (typingFoldFam.{u} X t E₀ R E lim rank fam adv).run h₀ (owns_apart_fam hG hF hus)
      (fresh_at_fam hG hF hwhole hrun hus)
      (needs_earlier_fam hG hF hshape htwf hus)
      (fold_steps_fam hG hF hshape htwf hroles hwhole hrun hus (hstep E hctx) (hstepFam E hctx))
  have hFI : FoldInv.{u} X t E₀ R E lim env := hinv
  have hextT : ∀ ci ∈ envT.consts, ci ∈ env.consts := hext
  refine ⟨E₀, env, hload, hFI.nodup, hextT, hFI.prov, ?_,
    claimedEnv_models_of_prefixInv hFI.inv hFI.nodup hFI.prov⟩
  intro a ha a' hsc
  have hTa := hG.seedsTop a ha
  obtain ⟨c, hc⟩ := hG.record a hTa
  obtain ⟨hlogc, hlogB⟩ := hG.seedLogic a ha c hc
  have hpost : ∀ (A : _root_.Address) (cA : Ixon.Constant) (y : _root_.Address), A ∈ us →
      recordOf E₀ A = some cA → ConstAddrOf A cA y →
      ∃ ci, env.find? (keyOf t y) = some ci ∧
        (PinnedBasis ci ∨ KeptIn t (storeOver E₀ R) (blobOver E₀ R) y ci) := by
    intro A cA y hA hcA hca
    obtain ⟨ci, hci, hname, hk⟩ := (hdone A hA).2 y ⟨cA, hcA, Or.inl hca⟩
    have hf := find_of_mem_nodup hFI.nodup hci
    rw [hname] at hf
    exact ⟨ci, hf, Or.inr hk⟩
  by_cases hst : StoredAt t envT a'
  · obtain ⟨ci, hci, hname⟩ := hst
    have hfT := find_of_mem_nodup hshape.reading.nodup hci
    rw [hname] at hfT
    have hf := find_of_mem_nodup hFI.nodup (hextT ci hci)
    rw [hname] at hf
    exact ⟨ci, hf, stored_provenance hroles hrec hblob hshape.reading.provenance hfT⟩
  · rcases hsc with ⟨haa, hnm⟩ | ⟨c', ms, i, m, hc', hms, hm, hx⟩
    · rw [haa] at hst
      rw [haa]
      rcases kind_cases c with hsa | hpr | hbl
      · exact hpost a c a ((hus a).mpr ⟨hTa, c, hc, hlogc, a, Or.inl ⟨rfl, hsa⟩, hst⟩) hc
          (Or.inl ⟨rfl, hsa⟩)
      · obtain ⟨hTB, -⟩ := hG.owner a c hTa hc hpr
        obtain ⟨cb, hcb, hconst⟩ := hG.projMember a c hTa hc hpr
        exact hpost _ cb a ((hus _).mpr ⟨hTB, cb, hcb, hlogB cb hcb, a, hconst, hst⟩) hcb hconst
      · obtain ⟨ms, hms⟩ := hbl
        exact absurd hms (hnm c ms hc)
    · rw [hc] at hc'
      have hcc : c = c' := Option.some.inj hc'
      rw [← hcc] at hms
      have hca : ConstAddrOf a c a' := Or.inr ⟨ms, i, m, hms, hm, hx⟩
      exact hpost a c a' ((hus a).mpr ⟨hTa, c, hc, hlogc, a', hca, hst⟩) hc hca

/-- **The existing skeleton is the variant's case without families**: `typing_skeleton_core`'s
hypotheses give its conclusion through `typing_skeleton_core_fam` at `fam = fun _ => none` and
no advice (`famGraph_none`; no block has a family record, so no `UnitStepFam` is asked). -/
theorem typing_skeleton_core_viaFam {V : View} {extra : List ByteArray}
    {X : Ix.Kernel.Env .anon → Prop} {lim : Option Nat}
    (hshape : TableShape.{u} t (fun _ => True) R envT)
    (hfacts : Facts.{u} t (fun _ => True) R envT) (hX : X envT) (ht : t.check = .ok ())
    (hb : Bounded calls) (hextra : ∀ x ∈ committedFootprint, x ∈ extra)
    (hnc : ¬ CollisionWith V extra R calls) (hS : LoadedReads.RunStore calls E₀)
    (hG : TopGraph t E₀ seeds Top rank)
    (hstep : ∀ E, StepCtx.{u} calls t R envT E₀ E → ∀ A c, Top A → recordOf E₀ A = some c →
      InLogic c → UnitKind c → UnitStep.{u} X t envT E₀ E lim A c) :
    ConsistentReadOver.{u} calls t R envT seeds :=
  typing_skeleton_core_fam (fam := fun _ => none) (adv := fun _ _ => False) hshape hfacts hX
    ht hb hextra hnc hS hG famGraph_none
    (fun E hE A c hT hc hl hk _ => hstep E hE A c hT hc hl hk)
    (fun _ _ _ _ _ _ _ _ _ _ _ h => nomatch h)

end Skeleton

end IxVM.Refinement.Typing
