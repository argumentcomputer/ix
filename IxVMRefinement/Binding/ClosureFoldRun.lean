import IxVMRefinement.Binding.ClosureFoldStore
import IxVMRefinement.Assembly.TypingFold

/-! # The closure fold: its units, their order and their steps

The closure of group `g` is a `UnitFold` (`closureFold`) over the closure's store `R₁`
(`closureStore`):

* the units are the records new in `R₁` that no block claims as its family record and that own
  a constant address (`IsClosureUnit`); a unit owns its record's constant addresses and, for a
  block with a selected family record, the record's (`FamOwns R₁ famOf`);
* a unit needs what `ClosureNeeds` lists and, for a twin, the constant addresses of its block's
  family record (`ClosureFoldNeeds`);
* the state is an environment; its invariant (`ClosureFoldInv`) holds distinct names, the fold's
  clause at every record store for `R₁` with one registry, the provenance of its claimed
  constants over `R₁`, the operations' keys unchanged, and every selected family record whose
  constant addresses are stored installed with its companions.

Proved here, from the context the fold hands its steps (`ClosureCtx`):

* `closureUnit_owner`: every new non-block record of `R₁` is owned by a unit of rank at most its
  own (itself, its block, or the block claiming its block as family record);
* `closureFold_ownsApart`, `closureFold_freshAt`, `closureFold_needsEarlier`: the three facts
  `UnitFold.run` asks of the units;
* `closureFold_steps`: the steps, from the plain, family and twin step premises;
* `closureFold_run`: the fold's result. -/

universe u

namespace IxVM.Refinement.Binding

open IxVM.Consistency
open IxVM.Refinement.Typing
open IxVM.Refinement.Typing.TwinFamily (FamilyInstalled)
open IxVM.Refinement.Binding.FamilyOf (FamilyOfBlock)
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel.Semantics (NativeFam)
open Ix.Kernel (ConstantInfo)

set_option linter.unusedVariables false

/-! ## The fold -/

/-- **A unit of the closure** (module docstring). -/
def IsClosureUnit (R R₁ : Ixon.Env) (famOf : _root_.Address → Option _root_.Address)
    (A : _root_.Address) : Prop :=
  New R R₁ A ∧ (∀ B, famOf B ≠ some A) ∧ ∃ x, FamOwns R₁ famOf A x

/-- **What a unit of the closure needs stored** (module docstring). -/
def ClosureFoldNeeds (E₀ R₁ : Ixon.Env) (famOf₀ famOf : _root_.Address → Option _root_.Address)
    (adv : _root_.Address → _root_.Address → Prop) (rank : _root_.Address → Nat)
    (A x : _root_.Address) : Prop :=
  ClosureNeeds E₀ famOf adv A x ∨
  ∃ B rb crb, recordOf R₁ rb = some crb ∧
    (famOf₀ B = some rb ∨ (famOf B = some rb ∧ rank B < rank A)) ∧ ConstAddrOf rb crb x

/-- **The fold's invariant** (module docstring). -/
structure ClosureFoldInv (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    (t : Ix.Kernel.RoleTable) (g : Nat) (R₁ : Ixon.Env) (env₀ : Ix.Kernel.Env .anon)
    (famOf₀ famOf : _root_.Address → Option _root_.Address) (s : Ix.Kernel.Env .anon) :
    Prop where
  nodup : (s.consts.map (·.name)).Nodup
  clause : FoldClauseOver.{u} L t (· < g) R₁ s
  prov : ∀ ci ∈ (claimedEnv s).consts, (∃ tbl, ci = .projInfo tbl) ∨ PinnedBasis ci ∨
    ∃ a, KeptIn t (recordOf R₁) (fun y => R₁.blobs.get? y) a ci
  ops : ∀ n ∈ RoleOps.opNames, s.find? n = env₀.find? n
  famInst : ∀ B rb crb, (famOf₀ B = some rb ∨ famOf B = some rb) → recordOf R₁ rb = some crb →
    (∀ x, ConstAddrOf rb crb x → StoredAt t s x) → FamilyInstalled t s rb crb
  famRecs : ∀ B rb cb crb, (famOf₀ B = some rb ∨ famOf B = some rb) →
    recordOf R₁ B = some cb → recordOf R₁ rb = some crb →
    (∀ x, ConstAddrOf rb crb x → StoredAt t s x) → StoredFamilyRecs t R₁ s B cb rb crb

/-- **The closure as a system of units** (module docstring). -/
def closureFold (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop) (t : Ix.Kernel.RoleTable)
    (g : Nat) (E₀ R₁ : Ixon.Env) (env₀ : Ix.Kernel.Env .anon)
    (famOf₀ famOf : _root_.Address → Option _root_.Address)
    (adv : _root_.Address → _root_.Address → Prop) (rank : _root_.Address → Nat) :
    UnitFold (Ix.Kernel.Env .anon) _root_.Address _root_.Address where
  Inv := ClosureFoldInv.{u} L t g R₁ env₀ famOf₀ famOf
  Ext := fun s s' => (∀ ci ∈ s.consts, ci ∈ s'.consts) ∧ Ix.Kernel.EnvExt s s'
  Stored := StoredAt t
  Post := fun A s => ∀ x, FamOwns R₁ famOf A x →
    ∃ ci ∈ s.consts, ci.name = keyOf t x ∧ ∃ ci₀, Reads t R₁ x ci₀ ∧ StoredAs ci ci₀
  owns := FamOwns R₁ famOf
  needs := ClosureFoldNeeds E₀ R₁ famOf₀ famOf adv rank
  rank := rank
  ext_refl := fun s => ⟨fun _ h => h, Ix.Kernel.EnvExt.refl s⟩
  ext_trans := fun h₁ h₂ => ⟨fun ci hci => h₂.1 ci (h₁.1 ci hci), h₁.2.trans h₂.2⟩
  stored_mono := fun x h hx => by
    obtain ⟨ci, hci, hname⟩ := hx
    exact ⟨ci, h.1 ci hci, hname⟩
  post_mono := fun A h hp x hx => by
    obtain ⟨ci, hci, hname, hr⟩ := hp x hx
    exact ⟨ci, h.1 ci hci, hname, hr⟩

/-- Ownership without a family record is the record's constant addresses. -/
theorem famOwns_none {R₁ : Ixon.Env} {famOf : _root_.Address → Option _root_.Address}
    {A : _root_.Address} {c : Ixon.Constant} (hfa : famOf A = none)
    (hc : recordOf R₁ A = some c) (x : _root_.Address) :
    FamOwns R₁ famOf A x ↔ ConstAddrOf A c x := by
  constructor
  · rintro ⟨c', hc', hx | ⟨rb, crb, hrb, -⟩⟩
    · rw [hc] at hc'
      rw [Option.some.inj hc']
      exact hx
    · rw [hfa] at hrb
      cases hrb
  · intro hx
    exact ⟨c, hc, Or.inl hx⟩

/-- Ownership with a family record is the two records' constant addresses. -/
theorem famOwns_some {R₁ : Ixon.Env} {famOf : _root_.Address → Option _root_.Address}
    {A rb : _root_.Address} {c crb : Ixon.Constant} (hfa : famOf A = some rb)
    (hc : recordOf R₁ A = some c) (hcrb : recordOf R₁ rb = some crb) (x : _root_.Address) :
    FamOwns R₁ famOf A x ↔ FamAddr A c rb crb x := by
  constructor
  · rintro ⟨c', hc', hx | ⟨rb', crb', hrb', hcrb', hx⟩⟩
    · rw [hc] at hc'
      rw [Option.some.inj hc']
      exact Or.inl hx
    · rw [hfa] at hrb'
      have e : rb = rb' := Option.some.inj hrb'
      subst e
      rw [hcrb] at hcrb'
      rw [Option.some.inj hcrb']
      exact Or.inr hx
  · rintro (hx | hx)
    · exact ⟨c, hc, Or.inl hx⟩
    · exact ⟨c, hc, Or.inr ⟨rb, crb, hfa, hcrb, hx⟩⟩

section Fold

variable {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop} {calls : List (Call F)} {ρ : BRun}
  {t : Ix.Kernel.RoleTable} {g : Nat} {R R' : Ixon.Env} {env : Ix.Kernel.Env .anon}
  {famOf₀ famOf : _root_.Address → Option _root_.Address}
  {adv cont : _root_.Address → _root_.Address → Prop} {bAddr : _root_.Address}

local notation "R₁" => closureStore t g R R'

/-! ### Records -/

theorem rec₁₂ {a : _root_.Address} {c : Ixon.Constant} (h : recordOf R₁ a = some c) :
    recordOf R' a = some c :=
  (recordOf_closureStore_down h).1

theorem rec₂₀ (hadm : Admits ρ t g R R') {a : _root_.Address} {c : Ixon.Constant}
    (h : recordOf R' a = some c) : recordOf ρ.E₀ a = some c :=
  recordOf_of_loaded hadm.loaded h

theorem rec_eq {S : Ixon.Env} {a : _root_.Address} {c c' : Ixon.Constant}
    (h : recordOf S a = some c) (h' : recordOf S a = some c') : c = c' :=
  Option.some.inj (h.symm.trans h')

theorem usedRef₂ (hadm : Admits ρ t g R R') {A x : _root_.Address} {c : Ixon.Constant}
    (hc : recordOf R' A = some c) (h : UsedRef ρ.E₀ A x) : UsedRef R' A x := by
  obtain ⟨c', i, hc', hi, hx⟩ := h
  have e : c' = c := rec_eq hc' (rec₂₀ hadm hc)
  subst e
  exact ⟨c', i, hc, hi, hx⟩

/-- A record of `R₁` is at no new role unit's address. -/
theorem notNewUnit_of_rec₁ {a : _root_.Address} {c : Ixon.Constant}
    (h : recordOf R₁ a = some c) : ¬ NewUnit t g R R' a :=
  (recordOf_closureStore_down h).2

/-- A block of the run's store is no new role unit's record. -/
theorem notNewUnit_of_block (hadm : Admits ρ t g R R')
    (hform : ∀ a c, RoleUnitAt t g a → New R R' a → recordOf R' a = some c →
      (∃ d, c.info = .defn d) ∨ ∃ ax, c.info = .axio ax)
    {a : _root_.Address} {cb : Ixon.Constant} (hcb : recordOf ρ.E₀ a = some cb)
    (hb : IsBlock cb) : ¬ NewUnit t g R R' a := by
  intro hu
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hu.2.1
  have e : c = cb := rec_eq (rec₂₀ hadm hc) hcb
  subst e
  exact (newUnit_not_proj_block hform hu hc).2 hb

/-- A record new in `R₁` is no axiom and no quotient: those are the group's standard axiom, a
role unit. -/
theorem new₁_not_axiomLike (hadm : Admits ρ t g R R') {a : _root_.Address} {c : Ixon.Constant}
    (hnew : New R R₁ a) (hc : recordOf R₁ a = some c) (hax : IsAxiomLike c) : False := by
  obtain ⟨hnew', hnu⟩ := new_of_closureStore hnew
  obtain ⟨r, hr, hstd, ha⟩ := hadm.standing a c hnew' (rec₁₂ hc) hax
  exact hnu ⟨⟨r, hr, ha, Or.inr hstd⟩, hnew'⟩

/-! ### The selected family records -/


theorem famRec_nonempty_ind (hC : ClosureCtx.{u} L calls ρ t g R R' R₁ env famOf₀ famOf adv cont bAddr)
    {B rb : _root_.Address} (hfa : famOf B = some rb) :
    ∃ cb ms crb rs flat, FamilyOfBlock ρ.E₀ B cb ms rb crb rs flat ∧ 0 < ms.size := by
  obtain ⟨cb, ms, crb, rs, flat, hF⟩ := hC.checks.family B rb hfa
  obtain ⟨cb', ms', hcb', hms', hpos⟩ := hC.run.famNonempty B rb hfa
  have e : cb' = cb := rec_eq hcb' hF.block.record
  subst e
  rw [hF.block.muts] at hms'
  have e' : ms = ms' := Ixon.ConstantInfo.muts.inj hms'
  subst e'
  exact ⟨cb', ms, crb, rs, flat, hF, hpos⟩

/-- **No block claims a block with a selected family record**: it is a non-empty block of
inductives, a family record a block of recursors. -/
theorem fam_unclaimed (hC : ClosureCtx.{u} L calls ρ t g R R' R₁ env famOf₀ famOf adv cont bAddr)
    {B rb : _root_.Address} (hfa : famOf B = some rb) :
    ∀ B', famOf B' ≠ some B := by
  intro B' hB'
  obtain ⟨cb, ms, crb, rs, flat, hF, hpos⟩ := famRec_nonempty_ind hC hfa
  obtain ⟨cb', ms', crb', rs', flat', hF'⟩ := hC.checks.family B' B hB'
  have e : crb' = cb := rec_eq hF'.record.record hF.block.record
  subst e
  have hmm := hF'.record.muts
  rw [hF.block.muts] at hmm
  have e' : ms = rs' := Ixon.ConstantInfo.muts.inj hmm
  subst e'
  have hm0 : ms.toList[0]? = some ms[0] := by
    simpa only [Array.getElem?_toList] using Array.getElem?_eq_getElem hpos
  have hmem := List.mem_of_getElem? hm0
  obtain ⟨ind, hind⟩ := hF.block.indcs _ hmem
  obtain ⟨r, hr⟩ := hF'.record.recrs _ hmem
  rw [hind] at hr
  cases hr

/-- **One block selects a family record.** -/
theorem fam_inj (hC : ClosureCtx.{u} L calls ρ t g R R' R₁ env famOf₀ famOf adv cont bAddr)
    {B B' rb : _root_.Address} (hfa : famOf B = some rb) (hfa' : famOf B' = some rb) :
    B = B' := by
  obtain ⟨cb, ms, crb, rs, flat, hF, hpos⟩ := famRec_nonempty_ind hC hfa
  obtain ⟨cb', ms', crb', rs', flat', hF', hpos'⟩ := famRec_nonempty_ind hC hfa'
  have e : crb' = crb := rec_eq hF'.record.record hF.record.record
  subst e
  have hrs := hF'.record.muts
  rw [hF.record.muts] at hrs
  have e' : rs = rs' := Ixon.ConstantInfo.muts.inj hrs
  subst e'
  have hm : ms[0]? = some ms[0] := Array.getElem?_eq_getElem hpos
  have hm' : ms'[0]? = some ms'[0] := Array.getElem?_eq_getElem hpos'
  obtain ⟨r, hr, n, hmaj⟩ := hF.recursor_at (hF.originals 0 _ hm)
  obtain ⟨r', hr', n', hmaj'⟩ := hF'.recursor_at (hF'.originals 0 _ hm')
  rw [hr] at hr'
  have er : r = r' := Ixon.MutConst.recr.inj (Option.some.inj hr')
  subst er
  have ha := FamilyOf.majorHeadAt_unique hmaj hmaj'
  have h1 := hF.block.members 0 _ hm
  have h2 := hF'.block.members 0 _ hm'
  rw [ha] at h1
  have hp := rec_eq h1 h2
  have := congrArg (Ix.Cert.ownerOf (memberAddr B' 0 ms'[0])) hp
  rwa [ownerOf_memberProjection, ownerOf_memberProjection] at this

/-- **A block with a selected family record and its record are new in `R₁`, the record after
the block.** -/
theorem fam_new (hC : ClosureCtx.{u} L calls ρ t g R R' R₁ env famOf₀ famOf adv cont bAddr)
    {B rb : _root_.Address} (hfa : famOf B = some rb) :
    ∃ cb crb ms rs, recordOf R₁ B = some cb ∧ recordOf R₁ rb = some crb ∧
      cb.info = .muts ms ∧ crb.info = .muts rs ∧ New R R₁ B ∧ New R R₁ rb ∧
      ρ.rank g B < ρ.rank g rb := by
  obtain ⟨cb, ms, crb, rs, flat, hF⟩ := hC.checks.family B rb hfa
  obtain ⟨hnewB, -⟩ := hC.checks.famCall B rb hfa
  obtain ⟨hnewrb, hrank⟩ := hC.famAdmits.famNew B rb hfa hnewB
  have hform := hC.run.roleUnitForm
  have huB : ¬ NewUnit t g R R' B :=
    notNewUnit_of_block hC.admits hform hF.block.record ⟨ms, hF.block.muts⟩
  have hurb : ¬ NewUnit t g R R' rb :=
    notNewUnit_of_block hC.admits hform hF.record.record ⟨rs, hF.record.muts⟩
  obtain ⟨cB, hcB⟩ := Option.isSome_iff_exists.mp hnewB.1
  obtain ⟨crb', hcrb'⟩ := Option.isSome_iff_exists.mp hnewrb.1
  have e1 : cB = cb := rec_eq (rec₂₀ hC.admits hcB) hF.block.record
  have e2 : crb' = crb := rec_eq (rec₂₀ hC.admits hcrb') hF.record.record
  subst e1 e2
  refine ⟨cB, crb', ms, rs, ?_, ?_, hF.block.muts, hF.record.muts,
    new_closureStore_of hnewB huB, new_closureStore_of hnewrb hurb, hrank⟩
  · rw [recordOf_closureStore huB]
    exact hcB
  · rw [recordOf_closureStore hurb]
    exact hcrb'

/-! ### Owners -/

/-- **A constant address of a record new in `R₁` is owned by a unit**: the record, or the
block that claims it, ranked below it. -/
theorem owner_of_constAddr (hC : ClosureCtx.{u} L calls ρ t g R R' R₁ env famOf₀ famOf adv cont bAddr)
    {D x : _root_.Address} {cD : Ixon.Constant} (hnew : New R R₁ D)
    (hcD : recordOf R₁ D = some cD) (hx : ConstAddrOf D cD x) :
    ∃ U, IsClosureUnit R R₁ famOf U ∧ FamOwns R₁ famOf U x ∧
      (U = D ∨ ρ.rank g U < ρ.rank g D) := by
  by_cases hcl : ∃ B, famOf B = some D
  · obtain ⟨B, hB⟩ := hcl
    obtain ⟨cb, crb, ms, rs, hcb, hcrb, -, -, hnewB, -, hrank⟩ := fam_new hC hB
    have e : crb = cD := rec_eq hcrb hcD
    subst e
    exact ⟨B, ⟨hnewB, fam_unclaimed hC hB, x, cb, hcb, Or.inr ⟨D, crb, hB, hcrb, hx⟩⟩,
      ⟨cb, hcb, Or.inr ⟨D, crb, hB, hcrb, hx⟩⟩, Or.inr hrank⟩
  · have hun : ∀ B, famOf B ≠ some D := fun B hB => hcl ⟨B, hB⟩
    exact ⟨D, ⟨hnew, hun, x, cD, hcD, Or.inl hx⟩, ⟨cD, hcD, Or.inl hx⟩, Or.inl rfl⟩

/-- **Every new non-block record of `R₁` is owned by a unit of rank at most its own**
(module docstring). -/
theorem closureUnit_owner (hC : ClosureCtx.{u} L calls ρ t g R R' R₁ env famOf₀ famOf adv cont bAddr)
    {x : _root_.Address} {cx : Ixon.Constant} (hnew : New R R₁ x)
    (hcx : recordOf R₁ x = some cx) (hnb : ¬ IsBlock cx) :
    ∃ U, IsClosureUnit R R₁ famOf U ∧ FamOwns R₁ famOf U x ∧
      (U = x ∨ ρ.rank g U < ρ.rank g x) := by
  rcases kind_cases cx with hs | hp | hb
  · rcases hs with hd | hr | hax | hq
    · exact owner_of_constAddr hC hnew hcx (Or.inl ⟨rfl, Or.inl hd⟩)
    · exact owner_of_constAddr hC hnew hcx (Or.inl ⟨rfl, Or.inr (Or.inl hr)⟩)
    · exact (new₁_not_axiomLike hC.admits hnew hcx (Or.inl hax)).elim
    · exact (new₁_not_axiomLike hC.admits hnew hcx (Or.inr hq)).elim
  · obtain ⟨hnew', hnu⟩ := new_of_closureStore hnew
    have hcx' := rec₁₂ hcx
    obtain ⟨cb, hcb, hconst⟩ := hC.admits.projMember x cx hnew' hcx' hp
    have hblock : IsBlock cb := by
      rcases hconst with ⟨he, hs⟩ | ⟨ms, -, -, hms, -, -⟩
      · rw [← he] at hcb
        rw [hcx'] at hcb
        rw [← Option.some.inj hcb] at hs
        exact (standalone_not_proj hs hp).elim
      · exact ⟨ms, hms⟩
    rcases hC.admits.rankOwner x cx hnew' hcx' hp with ⟨hnewO, hrk⟩ | hold
    · have huO : ¬ NewUnit t g R R' (Ix.Cert.ownerOf x cx) :=
        notNewUnit_of_block hC.admits hC.run.roleUnitForm (rec₂₀ hC.admits hcb) hblock
      have hcbO : recordOf R₁ (Ix.Cert.ownerOf x cx) = some cb := by
        rw [recordOf_closureStore huO]
        exact hcb
      obtain ⟨U, hU, hown, hrkU⟩ :=
        owner_of_constAddr hC (new_closureStore_of hnewO huO) hcbO hconst
      refine ⟨U, hU, hown, Or.inr ?_⟩
      rcases hrkU with e | h
      · rw [e]
        exact hrk
      · exact Nat.lt_trans h hrk
    · exfalso
      obtain ⟨cR, hcR⟩ := Option.isSome_iff_exists.mp hold
      have e : cR = cb := rec_eq (recordOf_of_loaded hC.admits.mono hcR) hcb
      subst e
      obtain ⟨ms, i, m, hms, hm, hxm⟩ : ∃ ms i m, cR.info = .muts ms ∧ ms[i]? = some m ∧
          (x = memberAddr (Ix.Cert.ownerOf x cx) i m ∨ ∃ ind j, m = .indc ind ∧
            j < ind.ctors.size ∧ x = ctorAddr (Ix.Cert.ownerOf x cx) i j) := by
        rcases hconst with ⟨he, hs⟩ | h
        · exact (standalone_not_block hs hblock).elim
        · exact h
      obtain ⟨hmem, hctor⟩ := hC.bnd.shape.usedClosed.2 _ cR ms hcR hms i m hm
      rcases hxm with hxe | ⟨ind, j, hind, hj, hxe⟩
      · rw [← hxe, hnew'.2] at hmem
        cases hmem
      · have h2 := hctor ind hind j hj
        rw [← hxe, hnew'.2] at h2
        cases h2
  · exact (hnb hb).elim

/-- An owned address holds a record of `R₁`, new in it. -/
theorem owned_new (hC : ClosureCtx.{u} L calls ρ t g R R' R₁ env famOf₀ famOf adv cont bAddr)
    {A x : _root_.Address} (hA : IsClosureUnit R R₁ famOf A)
    (hx : FamOwns R₁ famOf A x) :
    ∃ D cD, New R R₁ D ∧ recordOf R₁ D = some cD ∧ ConstAddrOf D cD x ∧ New R R₁ x ∧
      (∀ ax, ∀ c, recordOf R₁ x = some c → c.info ≠ .axio ax) := by
  obtain ⟨c, hc, hxc | ⟨rb, crb, hfa, hcrb, hxr⟩⟩ := hx
  · have key : ∀ D cD, New R R₁ D → recordOf R₁ D = some cD → ConstAddrOf D cD x →
        New R R₁ x ∧ (∀ ax, ∀ c, recordOf R₁ x = some c → c.info ≠ .axio ax) := by
      intro D cD hnD hcD hxD
      rcases constAddr_record hC.closed hcD hxD with ⟨he, hs⟩ | ⟨-, P, hP, hPp, hPo⟩
      · subst he
        refine ⟨hnD, fun ax c' hc' hi => ?_⟩
        exact new₁_not_axiomLike hC.admits hnD hc' (Or.inl ⟨ax, hi⟩)
      · refine ⟨⟨Option.isSome_iff_exists.mpr ⟨P, hP⟩, ?_⟩, fun ax c' hc' hi => ?_⟩
        · cases hR : recordOf R x with
          | none => rfl
          | some p₀ =>
            exfalso
            have e : p₀ = P := rec_eq (recordOf_closureStore_of_R hC.admits hR) hP
            subst e
            obtain ⟨hown, -⟩ := hC.bnd.shape.usedClosed.1 x p₀ hR
            rw [hPo, hnD.2] at hown
            simp at hown
        · have e : c' = P := rec_eq hc' hP
          subst e
          rcases hPp with ⟨p, h⟩ | ⟨p, h⟩ | ⟨p, h⟩ | ⟨p, h⟩ <;> (rw [h] at hi; cases hi)
    obtain ⟨h1, h2⟩ := key A c hA.1 hc hxc
    exact ⟨A, c, hA.1, hc, hxc, h1, h2⟩
  · obtain ⟨cb, crb', ms, rs, hcb, hcrb', -, hrs, -, hnrb, -⟩ := fam_new hC hfa
    have e : crb' = crb := rec_eq hcrb' hcrb
    subst e
    rcases constAddr_record hC.closed hcrb' hxr with ⟨he, hs⟩ | ⟨-, P, hP, hPp, hPo⟩
    · subst he
      exact (standalone_not_block hs ⟨rs, hrs⟩).elim
    · refine ⟨rb, crb', hnrb, hcrb', hxr, ⟨Option.isSome_iff_exists.mpr ⟨P, hP⟩, ?_⟩, fun ax c' hc' hi => ?_⟩
      · cases hR : recordOf R x with
        | none => rfl
        | some p₀ =>
          exfalso
          have e : p₀ = P := rec_eq (recordOf_closureStore_of_R hC.admits hR) hP
          subst e
          obtain ⟨hown, -⟩ := hC.bnd.shape.usedClosed.1 x p₀ hR
          rw [hPo, hnrb.2] at hown
          simp at hown
      · have e : c' = P := rec_eq hc' hP
        subst e
        rcases hPp with ⟨p, h⟩ | ⟨p, h⟩ | ⟨p, h⟩ | ⟨p, h⟩ <;> (rw [h] at hi; cases hi)

/-- **Two units owning one address are one unit.** -/
theorem closureUnits_apart (hC : ClosureCtx.{u} L calls ρ t g R R' R₁ env famOf₀ famOf adv cont bAddr)
    {A A' x : _root_.Address} (hA : IsClosureUnit R R₁ famOf A)
    (hA' : IsClosureUnit R R₁ famOf A') (hx : FamOwns R₁ famOf A x)
    (hx' : FamOwns R₁ famOf A' x) : A = A' := by
  obtain ⟨c, hc, hxc | ⟨rb, crb, hfa, hcrb, hxr⟩⟩ := hx <;>
    obtain ⟨c', hc', hxc' | ⟨rb', crb', hfa', hcrb', hxr'⟩⟩ := hx'
  · exact constAddr_same hC.closed hc hc' hxc hxc'
  · have e : A = rb' := constAddr_same hC.closed hc hcrb' hxc hxr'
    subst e
    exact (hA.2.1 A' hfa').elim
  · have e : rb = A' := constAddr_same hC.closed hcrb hc' hxr hxc'
    subst e
    exact (hA'.2.1 A hfa).elim
  · have e : rb = rb' := constAddr_same hC.closed hcrb hcrb' hxr hxr'
    subst e
    exact fam_inj hC hfa hfa'

/-! ### The start -/

/-- **A constant address of a record new in the group is not stored by the witness's
environment.** -/
theorem new_constAddr_not_stored (hC : ClosureCtx.{u} L calls ρ t g R R' R₁ env famOf₀ famOf adv cont bAddr)
    (htwf : t.wf = true) {D x : _root_.Address} {cD : Ixon.Constant}
    (hnew : New R R' D) (hcD : recordOf R' D = some cD) (hx : ConstAddrOf D cD x) :
    ¬ StoredAt t env x := by
  intro hst
  obtain ⟨ci, hci, hname⟩ := hst
  have hf : env.find? (keyOf t x) = some ci := by
    rw [← hname]
    exact find_of_mem_nodup hC.bnd.shape.reading.nodup hci
  obtain ⟨hclaimed, hna⟩ := seed_claimed hf
  rcases hC.bnd.shape.reading.provenance ci hclaimed with ⟨tbl, htbl⟩ | hpin | ⟨a, hk⟩
  · rw [htbl] at hna
    exact hna tbl.structName .projTable rfl
  · exact hC.run.noPinned D cD x ci hnew hcD hx hpin hname
  · have haa : a = x := Core.keyOf_inj htwf ((keptIn_name hk).symm.trans hname)
    subst haa
    obtain ⟨-, ci₀, ⟨c₀, hc₀, -⟩, -⟩ := hk
    rcases constAddr_record hC.admits.usedClosed hcD hx with ⟨he, -⟩ | ⟨-, P, hP, -, hPo⟩
    · subst he
      rw [hnew.2] at hc₀
      cases hc₀
    · have e : c₀ = P := rec_eq (recordOf_of_loaded hC.admits.mono hc₀) hP
      subst e
      obtain ⟨hown, -⟩ := hC.bnd.shape.usedClosed.1 a c₀ hc₀
      rw [hPo, hnew.2] at hown
      simp at hown

/-- **A unit's owned addresses are not stored at the start.** -/
theorem owned_not_stored (hC : ClosureCtx.{u} L calls ρ t g R R' R₁ env famOf₀ famOf adv cont bAddr)
    (htwf : t.wf = true) {A x : _root_.Address}
    (hA : IsClosureUnit R R₁ famOf A) (hx : FamOwns R₁ famOf A x) : ¬ StoredAt t env x := by
  obtain ⟨D, cD, hnD, hcD, hxD, -⟩ := owned_new hC hA hx
  exact new_constAddr_not_stored hC htwf (new_of_closureStore hnD).1 (rec₁₂ hcD) hxD

/-! ### The order -/

/-- **An address held before the group that a unit needs is stored at the start**: it holds no
block (a reference a step needs is no block; an advice record's constant address is the record
itself, which is no block, or a member's or a constructor's projection record of the advice
block, which the store after the group holds), and every non-block record held before the group
is stored (`RecordsStored`). -/
theorem old_needed_stored (hC : ClosureCtx.{u} L calls ρ t g R R' R₁ env famOf₀ famOf adv cont bAddr)
    {A x : _root_.Address} (hnA : New R R' A)
    (hneed : ClosureNeeds ρ.E₀ famOf adv A x) (hold : (recordOf R x).isSome = true) :
    StoredAt t env x := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hold
  have hc' : recordOf R' x = some c := recordOf_of_loaded hC.admits.mono hc
  have hc₀ : recordOf ρ.E₀ x = some c := rec₂₀ hC.admits hc'
  have hnb : ∀ ms, c.info ≠ .muts ms := by
    intro ms hms
    have hok : NeedOk ρ.E₀ x → False := by
      rintro ⟨c₁, hc₁, hnb₁, -⟩
      exact hnb₁ ⟨ms, by rw [rec_eq hc₀ hc₁] at hms; exact hms⟩
    rcases hneed with ⟨-, hn⟩ | ⟨_, -, -, hn⟩ | ⟨rb, a, ca, hfa, ha, hca, hx⟩ |
        ⟨_, _, -, -, -, hn⟩
    · exact hok hn
    · exact hok hn
    · obtain ⟨haR', -⟩ := hC.famAdmits.advice A rb a hfa hnA ha
      obtain ⟨ca', hca'⟩ := Option.isSome_iff_exists.mp haR'
      have e : ca' = ca := rec_eq (rec₂₀ hC.admits hca') hca
      rw [e] at hca'
      rcases hx with ⟨rfl, hst⟩ | ⟨ms', i, m, hms', hm, hx⟩
      · rw [rec_eq hc₀ hca] at hms
        exact standalone_not_block hst ⟨ms, hms⟩
      · obtain ⟨h1, h2⟩ := hC.admits.usedClosed.2 a ca ms' hca' hms' i m hm
        rcases hx with rfl | ⟨ind, j, rfl, hj, rfl⟩
        · rw [rec_eq hc' h1] at hms
          cases m <;> simp [memberProjection] at hms
        · rw [rec_eq hc' (h2 ind rfl j hj)] at hms
          simp [constructorProjection] at hms
    · exact hok hn
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp (hC.stored x c hc hnb)
  exact storedAt_of_find hci

/-- **A new non-block record of rank below `A`'s is owned by a unit of rank below `A`'s.** -/
theorem new_needed_below (hC : ClosureCtx.{u} L calls ρ t g R R' R₁ env famOf₀ famOf adv cont bAddr)
    {A x : _root_.Address} (hnewx : New R R' x)
    (hnu : ¬ NewUnit t g R R' x) (hnb : ∀ cx, recordOf ρ.E₀ x = some cx → ¬ IsBlock cx)
    (hrk : ρ.rank g x < ρ.rank g A) :
    ∃ U, IsClosureUnit R R₁ famOf U ∧ FamOwns R₁ famOf U x ∧ ρ.rank g U < ρ.rank g A := by
  obtain ⟨cx, hcx⟩ := Option.isSome_iff_exists.mp hnewx.1
  have hcx₁ : recordOf R₁ x = some cx := by
    rw [recordOf_closureStore hnu]
    exact hcx
  obtain ⟨U, hU, hown, hrkU⟩ := closureUnit_owner hC (new_closureStore_of hnewx hnu) hcx₁
    (hnb cx (rec₂₀ hC.admits hcx))
  refine ⟨U, hU, hown, ?_⟩
  rcases hrkU with e | h
  · rw [e]
    exact hrk
  · exact Nat.lt_trans h hrk

/-- A used reference of a record new in the group: held before, or new below it and no role
unit's. -/
theorem usedRef_cases (hC : ClosureCtx.{u} L calls ρ t g R R' R₁ env famOf₀ famOf adv cont bAddr)
    {A x : _root_.Address} {c : Ixon.Constant} (hnA : New R R' A)
    (hc : recordOf R' A = some c) (hused : UsedRef ρ.E₀ A x) :
    (recordOf R x).isSome = true ∨
      (New R R' x ∧ ¬ NewUnit t g R R' x ∧ ρ.rank g x < ρ.rank g A) := by
  have hused' := usedRef₂ hC.admits hc hused
  rcases hC.admits.rankUsed A x hnA hused' with ⟨hnx, hrk⟩ | hold
  · exact Or.inr ⟨hnx, fun hu => hC.admits.unitsLast A x hnA hused' hu.1, hrk⟩
  · exact Or.inl hold

/-- **The order condition of the fold** (`UnitFold.NeedsEarlier`). -/
theorem closureFold_needsEarlier (hC : ClosureCtx.{u} L calls ρ t g R R' R₁ env famOf₀ famOf adv cont bAddr)
    {us : List _root_.Address}
    (hus : ∀ A, A ∈ us ↔ IsClosureUnit R R₁ famOf A) :
    (closureFold.{u} L t g ρ.E₀ R₁ env famOf₀ famOf adv (ρ.rank g)).NeedsEarlier env us := by
  intro A hAu x hneed
  have hA := (hus A).mp hAu
  obtain ⟨hnA, hnuA⟩ := new_of_closureStore hA.1
  obtain ⟨cA, hcA⟩ := Option.isSome_iff_exists.mp hA.1.1
  have hcA' := rec₁₂ hcA
  have below : ∀ U, IsClosureUnit R R₁ famOf U → FamOwns R₁ famOf U x →
      ρ.rank g U < ρ.rank g A →
      StoredAt t env x ∨ FamOwns R₁ famOf A x ∨
        ∃ b ∈ us, FamOwns R₁ famOf b x ∧ ρ.rank g b < ρ.rank g A :=
    fun U hU hown hrk => Or.inr (Or.inr ⟨U, (hus U).mpr hU, hown, hrk⟩)
  have newBelow : New R R' x → ¬ NewUnit t g R R' x → NeedOk ρ.E₀ x →
      ρ.rank g x < ρ.rank g A →
      StoredAt t env x ∨ FamOwns R₁ famOf A x ∨
        ∃ b ∈ us, FamOwns R₁ famOf b x ∧ ρ.rank g b < ρ.rank g A := by
    intro hnx hnux hok hrk
    obtain ⟨cx, hcx, hnb, -⟩ := hok
    obtain ⟨U, hU, hown, hrkU⟩ := new_needed_below hC hnx hnux
      (fun c' hc' hb => hnb (by rw [rec_eq hcx hc']; exact hb)) hrk
    exact below U hU hown hrkU
  rcases hneed with hcn | ⟨B, rb, crb, hcrb, hor, hxr⟩
  · rcases hcn with ⟨hused, hok⟩ | ⟨rb, hfa, hused, hok⟩ |
        ⟨rb, a, ca, hfa, ha, hca, hxa⟩ | ⟨rb, a, hfa, ha, hused, hok⟩
    · rcases usedRef_cases hC hnA hcA' hused with hold | ⟨hnx, hnux, hrk⟩
      · exact Or.inl (old_needed_stored hC hnA (Or.inl ⟨hused, hok⟩) hold)
      · exact newBelow hnx hnux hok hrk
    · obtain ⟨cb, crb, ms, rs, hcb, hcrb, -, -, -, hnrb, -⟩ := fam_new hC hfa
      have e : cb = cA := rec_eq hcb hcA
      subst e
      rcases usedRef_cases hC (new_of_closureStore hnrb).1 (rec₁₂ hcrb) hused with
        hold | ⟨hnx, hnux, -⟩
      · exact Or.inl (old_needed_stored hC hnA (Or.inr (Or.inl ⟨rb, hfa, hused, hok⟩)) hold)
      · rcases hC.run.famRefs A rb x hfa hused hok hnx with ⟨cb', crb', hcb', hcrb', hfx⟩ | hrk
        · have e1 : cb' = cb := rec_eq hcb' hcA'
          have e2 : crb' = crb := rec_eq hcrb' (rec₁₂ hcrb)
          subst e1 e2
          exact Or.inr (Or.inl ((famOwns_some hfa hcA hcrb x).mpr hfx))
        · exact newBelow hnx hnux hok hrk
    · obtain ⟨haR', hadvRk⟩ := hC.famAdmits.advice A rb a hfa hnA ha
      have hnua : ¬ NewUnit t g R R' a := hC.run.advNotUnit A rb a hfa ha
      obtain ⟨ca', hca'⟩ := Option.isSome_iff_exists.mp haR'
      have e : ca' = ca := rec_eq (rec₂₀ hC.admits hca') hca
      subst e
      have hca₁ : recordOf R₁ a = some ca' := by
        rw [recordOf_closureStore hnua]
        exact hca'
      cases hRa : recordOf R a with
      | some a₀ =>
        have e : a₀ = ca' := rec_eq (recordOf_of_loaded hC.admits.mono hRa) hca'
        subst e
        have hold : (recordOf R x).isSome = true := by
          rcases constAddr_record hC.bnd.shape.usedClosed hRa hxa with ⟨he, -⟩ |
              ⟨-, P, hP, -, -⟩
          · rw [he, hRa]
            rfl
          · rw [hP]
            rfl
        exact Or.inl (old_needed_stored hC hnA
          (Or.inr (Or.inr (Or.inl ⟨rb, a, a₀, hfa, ha, hca, hxa⟩))) hold)
      | none =>
        have hna : New R R' a := ⟨haR', hRa⟩
        have hrk := hadvRk hna
        obtain ⟨U, hU, hown, hrkU⟩ :=
          owner_of_constAddr hC (new_closureStore_of hna hnua) hca₁ hxa
        refine below U hU hown ?_
        rcases hrkU with e | h
        · rw [e]
          exact hrk
        · exact Nat.lt_trans h hrk
    · obtain ⟨haR', hadvRk⟩ := hC.famAdmits.advice A rb a hfa hnA ha
      obtain ⟨ca', hca'⟩ := Option.isSome_iff_exists.mp haR'
      cases hRa : recordOf R a with
      | some a₀ =>
        have e : a₀ = ca' := rec_eq (recordOf_of_loaded hC.admits.mono hRa) hca'
        subst e
        obtain ⟨c', i, hc', hi, hx⟩ := hused
        have e' : c' = a₀ := rec_eq hc' (rec₂₀ hC.admits hca')
        subst e'
        have hold := (hC.bnd.shape.usedClosed.1 a c' hRa).2 i hi x hx
        exact Or.inl (old_needed_stored hC hnA
          (Or.inr (Or.inr (Or.inr ⟨rb, a, hfa, ha, ⟨c', i, hc', hi, hx⟩, hok⟩))) hold)
      | none =>
        have hna : New R R' a := ⟨haR', hRa⟩
        rcases usedRef_cases hC hna hca' hused with hold | ⟨hnx, hnux, hrk⟩
        · exact Or.inl (old_needed_stored hC hnA
            (Or.inr (Or.inr (Or.inr ⟨rb, a, hfa, ha, hused, hok⟩))) hold)
        · exact newBelow hnx hnux hok (Nat.lt_trans hrk (hadvRk hna))
  · rcases hor with h₀ | ⟨hfa, hrk⟩
    · obtain ⟨cb, ms, crb', rs, flat, hF⟩ := hC.fams.family B rb h₀
      have e : crb' = crb := rec_eq (recordOf_closureStore_of_R hC.admits hF.record.record) hcrb
      subst e
      exact Or.inl ((hC.fams.installed B rb crb' h₀ hF.record.record).1 x hxr)
    · obtain ⟨cb, crb', ms, rs, hcb, hcrb', -, -, hnB, -, -⟩ := fam_new hC hfa
      have e : crb' = crb := rec_eq hcrb' hcrb
      subst e
      exact below B ⟨hnB, fam_unclaimed hC hfa, x, cb, hcb, Or.inr ⟨rb, crb', hfa, hcrb', hxr⟩⟩
        ⟨cb, hcb, Or.inr ⟨rb, crb', hfa, hcrb', hxr⟩⟩ hrk

end Fold

end IxVM.Refinement.Binding
