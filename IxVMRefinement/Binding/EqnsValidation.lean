import IxVMRefinement.Binding.ShapeAnchors
import IxVMRefinement.Binding.EqnsRendered
import IxVMRefinement.Decl.Common
import IxVMRefinement.Roles.Lookups
import IxVMRefinement.Lib.Lists

/-! # Stored shapes at the equation and walked-anchor groups (`46..76`)

Proves `roleFreeShapes_eqnsGroup`: at every binding run and every group `g` with `46 ≤ g < 77`,
the closure's environment `env₁` satisfies `Shapes (· < g + 1) env₁`, recording for each role `r`
in group `g`:
* `RoleExactTy env₁ r` (and `RoleExactTy env₁ ar` for each anchor `ar ∈ eqnsAnchorsOf r` walked by
  `KernelRoles::validate_eqns_anchors`),
* `EqnValid env₁ r e` for every equation `e ∈ eqnsOfRole r`, whether validated by definitional
  equality (`Defeq`) or by a stored theorem (`Proof`),
* `RoleExactTy env₁ r` for walked anchor roles in `46..76` (`of_decide_eq_true` and
  `of_decide_eq_false`).

Each load uses the standing prefix invariant `hb₁.facts.inv` at the stored context
`Ctx.stored ⟨Ec, env₁, t, some (valLimit g)⟩` (whose scope allows every call and whose keying
resolves every stored key), turning `Ingress::get_ci` directly into `CIPtrRep` and
`KernelDefEq::k_is_def_eq` directly into `DefEq env₁ 0`. -/

universe u

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace IxVM.Refinement.Binding

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM (F)
open IxVM.Consistency
open IxVM.Refinement.Core
open Ix.Kernel (Role)
open Ix.Kernel.Rules (DefEq)
open Ix.Kernel.Semantics (NativeFam)

/-! ## `CIRep` field extraction -/

private theorem ciRep_notTower {κ : _root_.Address → KKey} {h : Heap F} {v : SourceValue F}
    {ci : Ix.Kernel.ConstantInfo .anon} (hci : CIRep κ h v ci) :
    ci.isTowerEntry = false := by
  cases hci with
  | quot _ hk =>
    rcases hk with ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ <;> rfl
  | _ => rfl

private theorem ciRep_valRep {κ : _root_.Address → KKey} {h : Heap F} {v : SourceValue F}
    {ci : Ix.Kernel.ConstantInfo .anon} (hci : CIRep κ h v ci) :
    ∃ (tag : String) (nl ty : SourceValue F) (rest : List (SourceValue F)),
      v = .construct kciEnum tag (nl :: ty :: rest) ∧
        ValRep κ h nl ty ci.toConstantVal := by
  cases hci with
  | axio hv => exact ⟨_, _, _, _, rfl, hv⟩
  | opaq hv => exact ⟨_, _, _, _, rfl, hv⟩
  | defn hv _ => exact ⟨_, _, _, _, rfl, hv⟩
  | thm hv _ => exact ⟨_, _, _, _, rfl, hv⟩
  | quot hv _ => exact ⟨_, _, _, _, rfl, hv⟩
  | induct hv _ _ => exact ⟨_, _, _, _, rfl, hv⟩
  | ctor hv _ _ _ _ => exact ⟨_, _, _, _, rfl, hv⟩
  | recr hv _ _ _ _ _ _ _ _ _ _ => exact ⟨_, _, _, _, rfl, hv⟩

private theorem const_num_lvls_ciRep {κ : _root_.Address → KKey} {h₀ h h' : Heap F}
    {v r : SourceValue F} {ci : Ix.Kernel.ConstantInfo .anon} {cs : List (Call F)}
    (hci : CIRep κ h₀ v ci)
    (ev : ObsFn W "KernelInfer::const_num_lvls" [v] h r h' cs) :
    r = .field (ci.toConstantVal.levelParams.length : F) ∧ h' = h := by
  obtain ⟨tag, nl, ty, rest, hvv, hval⟩ := ciRep_valRep hci
  rcases Obs.«KernelInfer::const_num_lvls».obs ev with
    ⟨x_n, _, _, hv, he, hh, -⟩ |
    ⟨x_n, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨x_n, _, _, _, _, hv, he, hh, -⟩ |
    ⟨x_n, _, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨x_n, _, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨x_n, _, _, _, _, _, _, _, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨x_n, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨x_n, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, he, hh, -⟩
  all_goals
    rw [hvv] at hv
    have hl := (Value.construct.inj hv).2.2
    simp only [List.cons.injEq] at hl
    exact ⟨he.trans (hl.1.symm.trans hval.1), hh⟩

private theorem const_type_of_ciRep {κ : _root_.Address → KKey} {h₀ h h' : Heap F}
    {v r : SourceValue F} {ci : Ix.Kernel.ConstantInfo .anon} {cs : List (Call F)}
    (hci : CIRep κ h₀ v ci)
    (ev : ObsFn W "KernelInfer::const_type_of" [v] h r h' cs) :
    h' = h ∧ TmC κ h₀ (posOf ci.toConstantVal.levelParams ci.toConstantVal.type) r := by
  obtain ⟨tag, nl, ty, rest, hvv, hval⟩ := ciRep_valRep hci
  rcases Obs.«KernelInfer::const_type_of».obs ev with
    ⟨_, x_ty, _, hv, he, hh, -⟩ |
    ⟨_, x_ty, _, _, _, _, hv, he, hh, -⟩ |
    ⟨_, x_ty, _, _, _, hv, he, hh, -⟩ |
    ⟨_, x_ty, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨_, x_ty, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨_, x_ty, _, _, _, _, _, _, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨_, x_ty, _, _, _, _, _, _, _, _, _, _, _, _, hv, he, hh, -⟩ |
    ⟨_, x_ty, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hv, he, hh, -⟩
  all_goals
    rw [hvv] at hv
    have hl := (Value.construct.inj hv).2.2
    simp only [List.cons.injEq] at hl
    refine ⟨hh, ?_⟩
    rw [he, ← hl.2.1]
    exact hval.2.2.2

private theorem levels_eq_of_ciRep {κ : _root_.Address → KKey} {r : Role} {n : Nat}
    (hn : roleSpecLevels r = some n) {v v₁ v₂ : SourceValue F} {h₀ h₁ h₂ h₃ : Heap F}
    {ci : Ix.Kernel.ConstantInfo .anon} {cs₁ cs₂ : List (Call F)}
    (hci : CIRep κ h₀ v ci)
    (ev₁ : ObsFn W "KernelInfer::const_num_lvls" [v] h₁ v₁ h₂ cs₁)
    (ev₂ : ObsFn W "KernelRoleSpec::role_levels" [.field (roleNum r)] h₂ v₂ h₃ cs₂)
    (he : v₁ = v₂) :
    ci.toConstantVal.levelParams.length = n := by
  obtain ⟨e₁, -⟩ := const_num_lvls_ciRep hci ev₁
  obtain ⟨e₂, -, hlt⟩ := role_levels_spec hn ev₂
  obtain ⟨_, _, _, _, -, hv⟩ := ciRep_valRep hci
  have hlen : ci.toConstantVal.levelParams.length < 4294967296 := hv.2.1
  have hf : ((ci.toConstantVal.levelParams.length : Nat) : F) = ((n : Nat) : F) :=
    Value.field.inj (e₁.symm.trans (he.trans e₂))
  have hval := congrArg ZMod.val hf
  rw [RolesAux.val_natCast (by omega), RolesAux.val_natCast (by omega)] at hval
  exact hval

private theorem levels_eq_of_valRep {κ : _root_.Address → KKey} {r : Role} {n : Nat}
    (hn : roleSpecLevels r = some n) {nl ty v₂ : SourceValue F} {h₀ h₂ h₃ : Heap F}
    {cv : Ix.Kernel.ConstantVal .anon} {cs₂ : List (Call F)}
    (hv : ValRep κ h₀ nl ty cv)
    (ev₂ : ObsFn W "KernelRoleSpec::role_levels" [.field (roleNum r)] h₂ v₂ h₃ cs₂)
    (he : nl = v₂) :
    cv.levelParams.length = n := by
  obtain ⟨e₂, -, hlt⟩ := role_levels_spec hn ev₂
  have hlen : cv.levelParams.length < 4294967296 := hv.2.1
  have hf : ((cv.levelParams.length : Nat) : F) = ((n : Nat) : F) :=
    Value.field.inj (hv.1.symm.trans (he.trans e₂))
  have hval := congrArg ZMod.val hf
  rw [RolesAux.val_natCast (by omega), RolesAux.val_natCast (by omega)] at hval
  exact hval

/-! ## Decidable coverage of every role constant in groups `46..76` -/

/-- Roles guaranteed to be stored in `env₁` when closing group `g` (`46 ≤ g < 77`) for role `r`. -/
def roleStoredBy (g : Nat) (r s : Role) : Bool :=
  decide (Ix.SpecDigest.groupOf s < 46 ∧
    (IxVM.Consistency.walkedRole s = true ∨ s ∈ IxVM.Consistency.shapeAnchors ∨
      s ∈ IxVM.Consistency.preludeRoles)) ||
  decide (s = r) ||
  decide (s ∈ eqnsAnchorsOf r) ||
  decide (46 ≤ Ix.SpecDigest.groupOf s ∧ Ix.SpecDigest.groupOf s < g ∧
    (RoleVal.roleSpecKindNat s = 5 ∨ (RoleVal.roleSpecKindNat s = 1 ∧ RoleVal.anchorWalked s = true))) ||
  Role.all.any fun r' =>
    decide (46 ≤ Ix.SpecDigest.groupOf r' ∧ Ix.SpecDigest.groupOf r' < g ∧
      RoleVal.roleSpecKindNat r' = 5 ∧ s ∈ eqnsAnchorsOf r')

def keyStoredBy (g : Nat) (r : Role) : KKey → Bool
  | .role s => roleStoredBy g r s
  | _ => false

/-- Pinned anchor indices in `validate_anchor`'s `match`. -/
private def pinnedIdxs : List Nat :=
  [4, 5, 6, 7, 20, 21, 22, 29, 30, 31, 37, 38, 39, 40]

def eqnsTermsStoredOk : Bool :=
  Role.all.all fun r =>
    let g := Ix.SpecDigest.groupOf r
    if 46 ≤ g && g < 77 then
      if RoleVal.roleSpecKindNat r == 5 then
        isEqnsOrAnchorRole r &&
        (match roleSpecLevels r, roleTypeExact r with
         | some _, some T₀ => T₀.constsResolveBy (keyStoredBy g r)
         | _, _ => false) &&
        (eqnsAnchorsOf r).all (fun ar =>
          isEqnsOrAnchorRole ar &&
          match roleSpecLevels ar, roleTypeExact ar with
          | some _, some T₀ => T₀.constsResolveBy (keyStoredBy g r)
          | _, _ => false) &&
        decide ((eqnsOfRole r).length < 64) &&
        (eqnsOfRole r).all (fun e =>
          (eqnsStmtExact e).constsResolveBy (keyStoredBy g r) &&
          (if e.hyps.isEmpty then
             (eqnsSideExact e e.lhs).constsResolveBy (keyStoredBy g r) &&
             (eqnsSideExact e e.rhs).constsResolveBy (keyStoredBy g r)
           else true))
      else if RoleVal.roleSpecKindNat r == 1 && RoleVal.anchorWalked r then
        isEqnsOrAnchorRole r &&
        !(r.idx ∈ pinnedIdxs) &&
        (match roleSpecLevels r, roleTypeExact r with
         | some _, some T₀ => T₀.constsResolveBy (keyStoredBy g r)
         | _, _ => false)
      else true
    else true

set_option maxRecDepth 2000000 in
theorem eqnsTermsStoredOk_true : eqnsTermsStoredOk = true := by decide +kernel

private theorem stored_of_roleStoredBy {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {t : Ix.Kernel.RoleTable} {R₁ : Ixon.Env} {env₁ : Ix.Kernel.Env .anon}
    (hall : AllBound t) {g : Nat} (hg : 46 ≤ g) {r s : Role}
    (hb₁ : BndOver.{u} L t (· < g) R₁ env₁)
    (hr_st : ∃ ci, env₁.find? (.role r) = some ci)
    (hanc_st : ∀ ar ∈ eqnsAnchorsOf r, ∃ ci, env₁.find? (.role ar) = some ci)
    (hs : roleStoredBy g r s = true) :
    ∃ ci, env₁.find? (.role s) = some ci := by
  unfold roleStoredBy at hs
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true] at hs
  rcases hs with (((⟨hlt46, hkp⟩ | rfl) | har) | ⟨h46, hltg, hk⟩) | ⟨r', _, h46', hlt', h5', har'⟩
  · obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (hall s)
    rcases hkp with hw | hsh | hpr
    · obtain ⟨ci, hf, -⟩ := hb₁.shape.kept (Ix.SpecDigest.groupOf s) s a
        (Nat.lt_of_lt_of_le hlt46 hg) (role_mem_roleGroup s) (Or.inl (Or.inl hw)) ha
      exact ⟨ci, hf⟩
    · obtain ⟨ci, hf, -⟩ := hb₁.shape.kept (Ix.SpecDigest.groupOf s) s a
        (Nat.lt_of_lt_of_le hlt46 hg) (role_mem_roleGroup s) (Or.inl (Or.inr hsh)) ha
      exact ⟨ci, hf⟩
    · obtain ⟨ci, hf, -⟩ := hb₁.shape.preludeKept (Ix.SpecDigest.groupOf s) s a
        (Nat.lt_of_lt_of_le hlt46 hg) (role_mem_roleGroup s) hpr ha
      exact ⟨ci, hf⟩
  · exact hr_st
  · exact hanc_st s har
  · have hsh := hb₁.facts.shapes.eqns s h46 hltg
    rcases hk with h5 | ⟨h1, haw⟩
    · obtain ⟨ci, _, hf, -⟩ := (hsh.1 h5).1
      exact ⟨ci, hf⟩
    · obtain ⟨ci, _, hf, -⟩ := hsh.2 h1 haw
      exact ⟨ci, hf⟩
  · have hsh := hb₁.facts.shapes.eqns r' h46' hlt'
    obtain ⟨ci, _, hf, -⟩ := (hsh.1 h5').2.1 s har'
    exact ⟨ci, hf⟩

/-! ## Rekeying rendered terms and `assert_type_meets` -/

private theorem tmCExact_to_stored {Ec : Ixon.Env} {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    {env₁ : Ix.Kernel.Env .anon} (htwf : t.wf = true)
    {h : Heap F} {T₀ : KExpr} {p : SourceValue F} {g : Nat} {r : Role}
    (hrep : Decl.TmCExact (Core.keyOf t) h T₀ p)
    (hcells : ∀ x, AddrIn h p x → ∃ s, t.addressOf? s = some (ixAddr x) ∧
      ∀ P, T₀.constsResolveBy P = true → P (.role s) = true)
    (hres : T₀.constsResolveBy (keyStoredBy g r) = true)
    (hstored : ∀ s, roleStoredBy g r s = true → ∃ ci, env₁.find? (.role s) = some ci) :
    TmC (Ctx.stored ⟨Ec, env₁, t, lim⟩).κ h T₀ p := by
  have hfind : ∀ x, AddrIn h p x → ∃ ci, env₁.find? (Core.keyOf t (ixAddr x)) = some ci := by
    intro x hx
    obtain ⟨s, hs, hP⟩ := hcells x hx
    have hsb : roleStoredBy g r s = true := hP (keyStoredBy g r) hres
    obtain ⟨ci, hci⟩ := hstored s hsb
    rw [keyOf_of_addressOf htwf hs]
    exact ⟨ci, hci⟩
  refine TmC.rekey (fun d Γ => (hrep d Γ).toTm) (fun a ha => ?_) (fun a ha _ => ?_)
  · obtain ⟨ci, hci⟩ := hfind a ha
    exact Ctx.stored_key_of_find (c := ⟨Ec, env₁, t, lim⟩) hci
  · obtain ⟨ci, hci⟩ := hfind a ha.addrIn
    exact Ctx.stored_projPermitted_of_find (c := ⟨Ec, env₁, t, lim⟩) hci

private theorem assert_type_meets_defEq {Ec : Ixon.Env} {t : Ix.Kernel.RoleTable} {g : Nat}
    {env₁ : Ix.Kernel.Env .anon}
    (hPI : Decl.PrefixInv.{u} Ec t (some (valLimit g)) env₁)
    {x_rc x_ty x_spec res : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {T₁ T₂ : KExpr}
    (hrc : RCRep t (some (valLimit g)) h x_rc)
    (hgood : CoreGood (Ctx.stored ⟨Ec, env₁, t, some (valLimit g)⟩) cs)
    (ev : ObsFn W "KernelRoles::assert_type_meets" [x_rc, x_ty, x_spec] h res h' cs)
    (hT₁ : TmC (Ctx.stored ⟨Ec, env₁, t, some (valLimit g)⟩).κ h T₁ x_ty)
    (hT₂ : TmC (Ctx.stored ⟨Ec, env₁, t, some (valLimit g)⟩).κ h T₂ x_spec) :
    DefEq env₁ 0 T₁ T₂ := by
  obtain ⟨v12, m15, cs23, m52, hm60, ev25, heq70, -, -, hc75⟩ :=
    Obs.«KernelRoles::assert_type_meets».obs ev
  subst heq70
  let c : ScopedCtx := Ctx.stored ⟨Ec, env₁, t, some (valLimit g)⟩
  have ext : Heap.Extends h m52 := by rw [hm60]; exact Heap.Extends.snoc h _
  have hgood23 : CoreGood c cs23 := hgood.sub (fun cl hm => by rw [hc75]; simp [hm])
  exact Decl.scoped_core_defeq (c := c) (Γ := fun _ => .sort .zero) (d := 0)
    (hrc.mono ext) (by rw [hm60]; exact Decl.typesRep_alloc_nil c.κ (fun _ => .sort .zero) h)
    (Decl.ghostScoped_zero _) hPI.scopedCoreFacts.env hPI.loads hgood23 ev25
    (Tm.mono ext (hT₁ 0 (fun _ => .sort .zero)))
    (Tm.mono ext (hT₂ 0 (fun _ => .sort .zero)))

/-! ## Loading a stored record via `PrefixInv` -/

private theorem notMuts_of_get_ci {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {ρ : BRun}
    {Rs : Nat → Ixon.Env} (hrun : BindingRun calls t ρ Rs)
    {R R' : Ixon.Env} {g : Nat} (hadm : Admits ρ t g R R')
    {ap ptr : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {a : Bytes.Address}
    {c : Ixon.Constant}
    (hsub : ∀ cl ∈ cs, cl ∈ calls)
    (ha : Bytes.RepAddressRef addrTy h a ap)
    (ev : ObsFn W "Ingress::get_ci" [ap] h ptr h' cs)
    (hrec : recordOf R' (ixAddr a) = some c) :
    ∀ ms, c.info ≠ .muts ms := by
  have hbound : Bounded cs := RomBound.bounded_mono hrun.bounded hsub
  obtain ⟨-, bytes, E_ld, hhash, hblake, -, hL1⟩ := L1.get_ci_loadedL1_spec hbound ha ev
  have hrecA : Ix.Cert.recordAt ρ.E₀ (ixAddr a) = some c := by
    rw [← hrun.runStore.recordOf_eq_recordAt]
    unfold recordOf at hrec ⊢
    cases hg_c : R'.consts.get? (ixAddr a) with
    | none => rw [hg_c] at hrec; cases hrec
    | some lc => rw [hg_c] at hrec; rw [hadm.loaded _ _ hg_c]; exact hrec
  obtain ⟨-, -, _, _, hraw⟩ :=
    LoadedReads.loadedL1_record hrun.runStore hsub hhash hblake hL1 hrecA
  intro ms hms
  unfold L1.RawCIRep at hraw
  rw [hms] at hraw
  exact hraw

private theorem stored_get_ci {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {ρ : BRun}
    {Rs : Nat → Ixon.Env} (hrun : BindingRun calls t ρ Rs)
    {R R' : Ixon.Env} {g : Nat} (hadm : Admits ρ t g R R')
    {Ec : Ixon.Env} {env₁ : Ix.Kernel.Env .anon}
    (hPI : Decl.PrefixInv.{u} Ec t (some (valLimit g)) env₁)
    (hgoodAll : CoreGood (Ctx.stored ⟨Ec, env₁, t, some (valLimit g)⟩) calls)
    (hrec : ∀ x c, recordOf R' x = some c → (∀ ms, c.info ≠ .muts ms) →
      (env₁.find? (Core.keyOf t x)).isSome = true)
    {ap ptr v : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {a : Bytes.Address}
    (hsub : ∀ cl ∈ cs, cl ∈ calls)
    (ha : Bytes.RepAddressRef addrTy h a ap)
    (ev : ObsFn W "Ingress::get_ci" [ap] h ptr h' cs)
    (hld : loadValue h' ptr = .ok v)
    (hinR' : (recordOf R' (ixAddr a)).isSome = true) :
    ∃ ci, env₁.find? (Core.keyOf t (ixAddr a)) = some ci ∧
      CIRep (Ctx.stored ⟨Ec, env₁, t, some (valLimit g)⟩).κ h' v ci := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hinR'
  have hnm := notMuts_of_get_ci hrun hadm hsub ha ev hc
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp (hrec (ixAddr a) c hc hnm)
  let cx : ScopedCtx := Ctx.stored ⟨Ec, env₁, t, some (valLimit g)⟩
  have hres : cx.κ (ixAddr a) ≠ unresolvedKey := hPI.loads.storedRes (ixAddr a) ci hci
  have hk : cx.κ (ixAddr a) = Core.keyOf t (ixAddr a) :=
    Ctx.stored_key_of_find (c := ⟨Ec, env₁, t, some (valLimit g)⟩) hci
  obtain ⟨ci', hci', v', hld', hrep'⟩ :=
    hPI.loads.getCI ap ptr h h' cs a ev trivial hres (hgoodAll.sub hsub) ha
  rw [hk] at hci'
  have eci : ci = ci' := Option.some.inj (hci.symm.trans hci')
  subst eci
  have ev' : v = v' := Except.ok.inj (hld.symm.trans hld')
  subst ev'
  exact ⟨ci, hci, hrep'⟩

/-! ## `walk_bound_anchor` and `validate_eqns_anchors` -/

private theorem walk_bound_anchor_roleExactTy {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {ρ : BRun} {Rs : Nat → Ixon.Env} (hrun : BindingRun calls t ρ Rs) (ht : t.check = .ok ())
    {R R' : Ixon.Env} {g : Nat} (hadm : Admits ρ t g R R')
    {Ec : Ixon.Env} {env₁ : Ix.Kernel.Env .anon}
    (hPI : Decl.PrefixInv.{u} Ec t (some (valLimit g)) env₁)
    (hgoodAll : CoreGood (Ctx.stored ⟨Ec, env₁, t, some (valLimit g)⟩) calls)
    (hrec : ∀ x c, recordOf R' x = some c → (∀ ms, c.info ≠ .muts ms) →
      (env₁.find? (Core.keyOf t x)).isSome = true)
    {bAddr : _root_.Address} {r ar : Role} {n : Nat} {T₀ : KExpr}
    (hiso : isEqnsOrAnchorRole ar = true)
    (hlv : roleSpecLevels ar = some n)
    (hrt : roleTypeExact ar = some T₀)
    (hres : T₀.constsResolveBy (keyStoredBy g r) = true)
    (hstored : ∀ s, roleStoredBy g r s = true → ∃ ci, env₁.find? (.role s) = some ci)
    (hinR' : ∀ a, t.addressOf? ar = some a → (recordOf R' a).isSome = true)
    {x_rc x_tbl res : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hrc : Claim.RCFullRep t bAddr (valLimit g) h x_rc)
    (htbl : Claim.TableFullRep t bAddr h x_tbl)
    (ev : ObsFn W "KernelRoles::walk_bound_anchor" [x_rc, x_tbl, .field (roleNum ar)] h res h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    RoleExactTy env₁ ar := by
  have htwf : t.wf = true := wf_of_check ht
  let cx : ScopedCtx := Ctx.stored ⟨Ec, env₁, t, some (valLimit g)⟩
  obtain ⟨v_a, m_a, cs_a, v_ci, m_ci, p_ci, cs_ci, v_nl, v_rl, m_nl, cs_nl, m_rl, cs_rl,
    _, m_chk, cs_chk, cs_atm, v_ty, v_sp, m_ty, cs_ty, m_sp, cs_sp,
    ev_ba, ev_ci, ld_ci, ev_nl, ev_rl, heq_nl, ev_chk, ev_ty, ev_sp, ev_atm, hc⟩ :=
    Obs.«KernelRoles::walk_bound_anchor».obs ev
  have hsub_ci : ∀ cl ∈ cs_ci, cl ∈ calls := fun cl hm => hsub cl (by rw [hc]; simp [hm])
  have hsub_atm : ∀ cl ∈ cs_atm, cl ∈ calls := fun cl hm => hsub cl (by rw [hc]; simp [hm])
  obtain ⟨ext_ba, a', ⟨b, hb, rfl⟩, had⟩ :=
    RoleVal.role_bound_addr_uncond htbl.toTableRep ev_ba
  obtain ⟨ci, hci_k, hci_rep⟩ :=
    stored_get_ci hrun hadm hPI hgoodAll hrec hsub_ci hb ev_ci ld_ci (hinR' _ had)
  rw [keyOf_of_addressOf htwf had] at hci_k
  have hlen : ci.toConstantVal.levelParams.length = n :=
    levels_eq_of_ciRep hlv hci_rep ev_nl ev_rl heq_nl
  obtain ⟨hm_ty, hty_rep⟩ := const_type_of_ciRep hci_rep ev_ty
  have ext_ci_ty : Heap.Extends m_ci m_ty :=
    ev_nl.heap_extends.trans (ev_rl.heap_extends.trans (ev_chk.heap_extends.trans ev_ty.heap_extends))
  have ext_h_ty : Heap.Extends h m_ty := ext_ba.trans (ev_ci.heap_extends.trans ext_ci_ty)
  obtain ⟨ext_sp, hsp_exact, hsp_cells⟩ :=
    roleTypeExactRenders hiso hrt htwf (htbl.toTableRep.mono ext_h_ty) ev_sp
  have hsp_tm : TmC cx.κ m_sp T₀ v_sp :=
    tmCExact_to_stored htwf hsp_exact hsp_cells hres hstored
  have hty_tm : TmC cx.κ m_sp (posOf ci.toConstantVal.levelParams ci.toConstantVal.type) v_ty :=
    fun d Γ => Tm.mono (ext_ci_ty.trans ext_sp) (hty_rep d Γ)
  have hde : DefEq env₁ 0 (posOf ci.toConstantVal.levelParams ci.toConstantVal.type) T₀ :=
    assert_type_meets_defEq hPI ((hrc.mono (ext_h_ty.trans ext_sp)).toRCRep)
      (hgoodAll.sub hsub_atm) ev_atm hty_tm hsp_tm
  exact ⟨ci, T₀, hci_k, ciRep_notTower hci_rep, by rw [hlen]; exact hlv, hrt, hde⟩

private theorem validate_eqns_anchors_exact {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {ρ : BRun} {Rs : Nat → Ixon.Env} (hrun : BindingRun calls t ρ Rs) (ht : t.check = .ok ())
    {R R' : Ixon.Env} {g : Nat} (hadm : Admits ρ t g R R')
    {Ec : Ixon.Env} {env₁ : Ix.Kernel.Env .anon}
    (hPI : Decl.PrefixInv.{u} Ec t (some (valLimit g)) env₁)
    (hgoodAll : CoreGood (Ctx.stored ⟨Ec, env₁, t, some (valLimit g)⟩) calls)
    (hrec : ∀ x c, recordOf R' x = some c → (∀ ms, c.info ≠ .muts ms) →
      (env₁.find? (Core.keyOf t x)).isSome = true)
    {bAddr : _root_.Address} {r : Role}
    (hhrg : r ∈ roleGroup g) (h5 : RoleVal.roleSpecKindNat r = 5)
    (hanc_ok : ∀ ar ∈ eqnsAnchorsOf r, isEqnsOrAnchorRole ar = true ∧
      ∃ n T₀, roleSpecLevels ar = some n ∧ roleTypeExact ar = some T₀ ∧
        T₀.constsResolveBy (keyStoredBy g r) = true)
    (hstored : ∀ s, roleStoredBy g r s = true → ∃ ci, env₁.find? (.role s) = some ci)
    {x_rc x_tbl res : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hrc : Claim.RCFullRep t bAddr (valLimit g) h x_rc)
    (htbl : Claim.TableFullRep t bAddr h x_tbl)
    (ev : ObsFn W "KernelRoles::validate_eqns_anchors" [x_rc, x_tbl, .field (roleNum r)] h res h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ calls) :
    ∀ ar ∈ eqnsAnchorsOf r, RoleExactTy env₁ ar := by
  have oneAnchor : ∀ (ar : Role) (har : ar ∈ eqnsAnchorsOf r)
      {x_r' : SourceValue F} {ha_m hb_m : Heap F} {cs' : List (Call F)},
      Heap.Extends h ha_m →
      ObsFn W "KernelRoles::walk_bound_anchor" [x_rc, x_tbl, .field (roleNum ar)] ha_m x_r' hb_m cs' →
      (∀ cl ∈ cs', cl ∈ calls) → RoleExactTy env₁ ar := by
    intro ar har x_r' ha_m hb_m cs' hext ev_w hsub_w
    obtain ⟨hiso, n, T₀, hlv, hrt, htr⟩ := hanc_ok ar har
    exact walk_bound_anchor_roleExactTy hrun ht hadm hPI hgoodAll hrec hiso hlv hrt htr hstored
      (hadm.eqnsAnchors r hhrg h5 ar har) (hrc.mono hext) (htbl.mono hext) ev_w hsub_w
  cases Obs.«KernelRoles::validate_eqns_anchors».obs ev with
  | n65 v1 m1 cs1 v2 m2 cs2 v3 m3 cs3 cs4 hv ev1 ev2 ev3 ev4 hc =>
    have hr : r = .decidableDecide := RolesAux.roleNum_inj (Value.field.inj hv)
    subst hr
    intro ar har
    simp only [eqnsAnchorsOf, RoleVal.eqnsAnchorsOf, List.mem_cons, List.not_mem_nil, or_false] at har
    rcases har with rfl | rfl | rfl | rfl
    · exact oneAnchor .decidable (by decide) (Heap.Extends.refl _) ev1
        (fun cl hm => hsub cl (by rw [hc]; simp [hm]))
    · exact oneAnchor .decidableIsTrue (by decide) ev1.heap_extends ev2
        (fun cl hm => hsub cl (by rw [hc]; simp [hm]))
    · exact oneAnchor .decidableIsFalse (by decide) (ev1.heap_extends.trans ev2.heap_extends) ev3
        (fun cl hm => hsub cl (by rw [hc]; simp [hm]))
    · exact oneAnchor .notProp (by decide)
        (ev1.heap_extends.trans (ev2.heap_extends.trans ev3.heap_extends)) ev4
        (fun cl hm => hsub cl (by rw [hc]; simp [hm]))
  | n68 cs1 _ hv ev1 hc =>
    have hr : r = .natDecLe := RolesAux.roleNum_inj (Value.field.inj hv)
    subst hr
    intro ar har
    simp only [eqnsAnchorsOf, RoleVal.eqnsAnchorsOf, List.mem_cons, List.not_mem_nil, or_false] at har
    subst har
    exact oneAnchor .natLe (by decide) (Heap.Extends.refl _) ev1
      (fun cl hm => hsub cl (by rw [hc]; simp [hm]))
  | n73 v1 m1 cs1 v2 m2 cs2 cs3 _ _ hv ev1 ev2 ev3 hc =>
    have hr : r = .intNegOfNat := RolesAux.roleNum_inj (Value.field.inj hv)
    subst hr
    intro ar har
    simp only [eqnsAnchorsOf, RoleVal.eqnsAnchorsOf, List.mem_cons, List.not_mem_nil, or_false] at har
    rcases har with rfl | rfl | rfl
    · exact oneAnchor .int (by decide) (Heap.Extends.refl _) ev1
        (fun cl hm => hsub cl (by rw [hc]; simp [hm]))
    · exact oneAnchor .intOfNat (by decide) ev1.heap_extends ev2
        (fun cl hm => hsub cl (by rw [hc]; simp [hm]))
    · exact oneAnchor .intNegSucc (by decide) (ev1.heap_extends.trans ev2.heap_extends) ev3
        (fun cl hm => hsub cl (by rw [hc]; simp [hm]))
  | n85 v1 m1 cs1 cs2 _ _ _ hv ev1 ev2 hc =>
    have hr : r = .bitVecToNat := RolesAux.roleNum_inj (Value.field.inj hv)
    subst hr
    intro ar har
    simp only [eqnsAnchorsOf, RoleVal.eqnsAnchorsOf, List.mem_cons, List.not_mem_nil, or_false] at har
    rcases har with rfl | rfl
    · exact oneAnchor .bitVec (by decide) (Heap.Extends.refl _) ev1
        (fun cl hm => hsub cl (by rw [hc]; simp [hm]))
    · exact oneAnchor .bitVecOfNat (by decide) ev1.heap_extends ev2
        (fun cl hm => hsub cl (by rw [hc]; simp [hm]))
  | n90 v1 m1 cs1 cs2 _ _ _ _ hv ev1 ev2 hc =>
    have hr : r = .stringToByteArray := RolesAux.roleNum_inj (Value.field.inj hv)
    subst hr
    intro ar har
    simp only [eqnsAnchorsOf, RoleVal.eqnsAnchorsOf, List.mem_cons, List.not_mem_nil, or_false] at har
    rcases har with rfl | rfl
    · exact oneAnchor .byteArray (by decide) (Heap.Extends.refl _) ev1
        (fun cl hm => hsub cl (by rw [hc]; simp [hm]))
    · exact oneAnchor .byteArrayEmpty (by decide) ev1.heap_extends ev2
        (fun cl hm => hsub cl (by rw [hc]; simp [hm]))
  | n96 cs1 _ _ _ _ _ hv ev1 hc =>
    have hr : r = .intDecLe := RolesAux.roleNum_inj (Value.field.inj hv)
    subst hr
    intro ar har
    simp only [eqnsAnchorsOf, RoleVal.eqnsAnchorsOf, List.mem_cons, List.not_mem_nil, or_false] at har
    subst har
    exact oneAnchor .intLe (by decide) (Heap.Extends.refl _) ev1
      (fun cl hm => hsub cl (by rw [hc]; simp [hm]))
  | other hne65 hne68 hne73 hne85 hne90 hne96 _ _ _ =>
    intro ar har
    cases r <;> first
      | exact absurd rfl hne65
      | exact absurd rfl hne68
      | exact absurd rfl hne73
      | exact absurd rfl hne85
      | exact absurd rfl hne90
      | exact absurd rfl hne96
      | (simp [eqnsAnchorsOf, RoleVal.eqnsAnchorsOf] at har)

/-! ## `validate_eqns_equations` loop -/

private theorem evList_length_spec {es : List (Ix.Kernel.Evidence _root_.Address)}
    {l r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::length<KernelRoles::RoleEvidence>» [l] h r h' cs)
    (hl : RepList evListEnum EvRep h es l) :
    r = .field (es.length : F) ∧ h' = h := by
  have ev' : ObsFn W (Instance.mk "Lists::length" [.named "KernelRoles::RoleEvidence" []]).symbol
      [l] h r h' cs := by
    rw [Obs.Names.«Lists::length<KernelRoles::RoleEvidence>».symbol]; exact ev
  have hl' : RepList (Instance.mk "Lists::Node" [.named "KernelRoles::RoleEvidence" []]).symbol
      EvRep h es l := by
    rw [Obs.Names.«Lists::Node<KernelRoles::RoleEvidence>».symbol]; exact hl
  exact Lib.Lists.length_spec ev' hl'

private theorem validate_eqns_equations_valid {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {ρ : BRun} {Rs : Nat → Ixon.Env} (hrun : BindingRun calls t ρ Rs) (ht : t.check = .ok ())
    {R R' : Ixon.Env} {g : Nat} (hadm : Admits ρ t g R R')
    {Ec : Ixon.Env} {env₁ : Ix.Kernel.Env .anon}
    (hPI : Decl.PrefixInv.{u} Ec t (some (valLimit g)) env₁)
    (hgoodAll : CoreGood (Ctx.stored ⟨Ec, env₁, t, some (valLimit g)⟩) calls)
    (hrec : ∀ x c, recordOf R' x = some c → (∀ ms, c.info ≠ .muts ms) →
      (env₁.find? (Core.keyOf t x)).isSome = true)
    {bAddr : _root_.Address} {r : Role} {n : Nat}
    (hhrg : r ∈ roleGroup g) (h5 : RoleVal.roleSpecKindNat r = 5)
    (hlv : roleSpecLevels r = some n)
    (heqns_ok : ∀ e ∈ eqnsOfRole r,
      (eqnsStmtExact e).constsResolveBy (keyStoredBy g r) = true ∧
      (e.hyps.isEmpty = true →
        (eqnsSideExact e e.lhs).constsResolveBy (keyStoredBy g r) = true ∧
        (eqnsSideExact e e.rhs).constsResolveBy (keyStoredBy g r) = true))
    (hstored : ∀ s, roleStoredBy g r s = true → ∃ ci, env₁.find? (.role s) = some ci)
    {x_rc x_tbl : SourceValue F}
    (es : List (Ix.Kernel.Evidence _root_.Address)) :
    ∀ (k : Nat) {v_ev res : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      (∀ thm, Ix.Kernel.Evidence.proof thm ∈ es → (recordOf R' thm).isSome = true) →
      Claim.RCFullRep t bAddr (valLimit g) h x_rc →
      Claim.TableFullRep t bAddr h x_tbl →
      RepList evListEnum EvRep h es v_ev →
      ObsFn W "KernelRoles::validate_eqns_equations"
        [x_rc, x_tbl, .field (roleNum r), v_ev, .field ((k : Nat) : F)] h res h' cs →
      (∀ cl ∈ cs, cl ∈ calls) →
      ∀ i (e : Ix.Kernel.Equation .anon),
        k ≤ i → i - k < es.length → (eqnsOfRole r)[i]? = some e → EqnValid env₁ r e := by
  have htwf : t.wf = true := wf_of_check ht
  let cx : ScopedCtx := Ctx.stored ⟨Ec, env₁, t, some (valLimit g)⟩
  induction es with
  | nil =>
    intro k _ _ _ _ _ _ _ _ _ _ _ i _ _ hlt _
    simp at hlt
  | cons ev0 rest ih =>
    intro k v_ev res h h' cs hproofs hrc htbl hlist ev hsub i e hki hlt hget
    cases Obs.«KernelRoles::validate_eqns_equations».obs ev with
    | Nil ld12 _ _ _ =>
      cases Lib.rep_nil_of_load hlist ld12
    | Cons x_e x_rest v432 m433 cs435 cs444 v451 ld12 sg440 op493 ev446 hc495 =>
      obtain ⟨ev0', rest', heq_l, hev0, hrest⟩ := Lib.rep_cons_of_load hlist ld12
      injection heq_l with he1 he2
      subst he1 he2
      have hsub435 : ∀ cl ∈ cs435, cl ∈ calls := fun cl hm => hsub cl (by rw [hc495]; simp [hm])
      have hsub444 : ∀ cl ∈ cs444, cl ∈ calls := fun cl hm => hsub cl (by rw [hc495]; simp [hm])
      by_cases hik : i = k
      · subst hik
        have hmem_e : e ∈ eqnsOfRole r := List.mem_of_getElem? hget
        obtain ⟨hstmt_ok, hside_ok⟩ := heqns_ok e hmem_e
        cases sg440 with
        | Defeq v69 m72 cs80 v117 m120 cs128 v132 v133 m143 cs151 m179 cs187 m215
            hv56 ev82 heq105 ev153 ev189 hm223 ev130 heq233 _ _ hc238 =>
          obtain ⟨hv69, hm72⟩ := eqns_conditional_spec hget ev82
          have hm72' : m72 = h := hm72
          cases hm72'
          have huncond : e.hyps.isEmpty = true := by
            cases hcnd : e.hyps.isEmpty
            · rw [hcnd] at hv69
              have h10 : (Value.field (1 : F) : SourceValue F) = .field 0 := hv69.symm.trans heq105
              exact absurd h10 NatAux.field_one_ne_zero
            · rfl
          obtain ⟨hlhs_ok, hrhs_ok⟩ := hside_ok huncond
          obtain ⟨ext143, hlhs_ex, hlhs_cells⟩ :=
            eqnsLhsExactRenders hget huncond htwf htbl.toTableRep ev153
          obtain ⟨ext179, hrhs_ex, hrhs_cells⟩ :=
            eqnsRhsExactRenders hget huncond htwf (htbl.toTableRep.mono ext143) ev189
          have hlhs_tm : TmC cx.κ m143 (eqnsSideExact e e.lhs) v132 :=
            tmCExact_to_stored htwf hlhs_ex hlhs_cells hlhs_ok hstored
          have hrhs_tm : TmC cx.κ m179 (eqnsSideExact e e.rhs) v133 :=
            tmCExact_to_stored htwf hrhs_ex hrhs_cells hrhs_ok hstored
          have ext215 : Heap.Extends m179 m215 := by rw [hm223]; exact Heap.Extends.snoc m179 _
          have ext_all : Heap.Extends h m215 := ext143.trans (ext179.trans ext215)
          have hsub128 : ∀ cl ∈ cs128, cl ∈ calls :=
            fun cl hm => hsub435 cl (by rw [hc238]; simp [hm])
          subst heq233
          have hde : DefEq env₁ 0 (eqnsSideExact e e.lhs) (eqnsSideExact e e.rhs) :=
            Decl.scoped_core_defeq (c := cx) (Γ := fun _ => .sort .zero) (d := 0)
              ((hrc.mono ext_all).toRCRep)
              (by rw [hm223]; exact Decl.typesRep_alloc_nil cx.κ (fun _ => .sort .zero) m179)
              (Decl.ghostScoped_zero _) hPI.scopedCoreFacts.env hPI.loads
              (hgoodAll.sub hsub128) ev130
              (Tm.mono (ext179.trans ext215) (hlhs_tm 0 (fun _ => .sort .zero)))
              (Tm.mono ext215 (hrhs_tm 0 (fun _ => .sort .zero)))
          exact Or.inl ⟨huncond, hde⟩
        | Proof x_thm m252 p260 cs266 x_nlvls x_tty w283 v311 m320 cs328 v340 m341 cs351
            cs373 v378 m394 cs402 _ hv244 ev268 ld262 ev330 heq339 ev353 ev404 ev375 hc429 =>
          have hsub266 : ∀ cl ∈ cs266, cl ∈ calls :=
            fun cl hm => hsub435 cl (by rw [hc429]; simp [hm])
          have hsub373 : ∀ cl ∈ cs373, cl ∈ calls :=
            fun cl hm => hsub435 cl (by rw [hc429]; simp [hm])
          obtain ⟨a_thm, ha_thm, hev_pf⟩ :
              ∃ a_thm : Bytes.Address, Bytes.RepAddressRef addrTy h a_thm x_thm ∧
                ev0 = .proof (ixAddr a_thm) := by
            rcases hev0 with ⟨_, hdef⟩ | ⟨a_thm, p, hpf, hv_p, ha_p⟩
            · rw [hdef] at hv244
              injection hv244 with _ hc_eq
              exact absurd hc_eq (by decide)
            · rw [hv_p] at hv244
              have hp : p = x_thm := List.cons.inj (Value.construct.inj hv244).2.2 |>.1
              subst hp
              exact ⟨a_thm, ha_p, hpf⟩
          have hinR' : (recordOf R' (ixAddr a_thm)).isSome = true :=
            hproofs (ixAddr a_thm) (by rw [hev_pf]; exact List.mem_cons_self ..)
          obtain ⟨ci_thm, hci_find, hci_rep⟩ :=
            stored_get_ci hrun hadm hPI hgoodAll hrec hsub266 ha_thm ev268 ld262 hinR'
          generalize hv_ci : (Value.construct kciEnum "Thm" [x_nlvls, x_tty, w283] : SourceValue F) = v_ci at hci_rep
          cases hci_rep with
          | thm hval_rep _ =>
            injection hv_ci with _ _ hl_ci
            simp only [List.cons.injEq, and_true] at hl_ci
            obtain ⟨rfl, rfl, rfl⟩ := hl_ci
            have hlen : _ = n := levels_eq_of_valRep hlv hval_rep ev330 heq339
            have ext252_341 : Heap.Extends m252 m341 :=
              ev330.heap_extends.trans ev353.heap_extends
            have ext_h_341 : Heap.Extends h m341 := ev268.heap_extends.trans ext252_341
            obtain ⟨ext394, hst_ex, hst_cells⟩ :=
              eqnsStatementExactRenders hget htwf (htbl.toTableRep.mono ext_h_341) ev404
            have hst_tm : TmC cx.κ m394 (eqnsStmtExact e) v378 :=
              tmCExact_to_stored htwf hst_ex hst_cells hstmt_ok hstored
            have hty_tm : TmC cx.κ m394 _ x_tty :=
              fun d Γ => Tm.mono (ext252_341.trans ext394) (hval_rep.2.2.2 d Γ)
            have hde := assert_type_meets_defEq hPI
              ((hrc.mono (ext_h_341.trans ext394)).toRCRep)
              (hgoodAll.sub hsub373) ev375 hty_tm hst_tm
            exact Or.inr ⟨Core.keyOf t (ixAddr a_thm), _, _, hci_find, by rw [hlen]; exact hlv, hde⟩
          | _ =>
            injection hv_ci with _ hc_ci _
            exact absurd hc_ci (by decide)
      · have ext433 : Heap.Extends h m433 := by
          cases sg440 with
          | Defeq _ _ _ _ _ _ _ _ _ _ m179 _ m215 _ ev82 _ ev153 ev189 hm223 ev130 _ _ hm433 _ =>
            rw [hm433]
            have e215 : Heap.Extends m179 m215 := by rw [hm223]; exact Heap.Extends.snoc m179 _
            exact ev82.heap_extends.trans (ev153.heap_extends.trans
              (ev189.heap_extends.trans (e215.trans ev130.heap_extends)))
          | Proof _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev268 _ ev330 _ ev353 ev404 ev375 _ =>
            exact ev268.heap_extends.trans (ev330.heap_extends.trans
              (ev353.heap_extends.trans (ev404.heap_extends.trans ev375.heap_extends)))
        have hv451 : v451 = .field (((k + 1 : Nat) : F)) := by
          have := NatAux.add_ok op493
          rw [this]
          simp [Nat.cast_add, Nat.cast_one]
        rw [hv451] at ev446
        exact ih (k + 1)
          (fun thm hm => hproofs thm (List.mem_cons_of_mem _ hm))
          (hrc.mono ext433) (htbl.mono ext433)
          (repList_heapMono₂ evListEnum evRep_heapMono₂ ext433 hrest)
          ev446 hsub444 i e (by omega) (by simp at hlt; omega) hget

/-! ## `EqnsRoleShape` at groups `46..76` -/

private theorem eqnsRoleShape_at_group {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {ρ : BRun} {Rs : Nat → Ixon.Env}
    (hrun : BindingRun calls t ρ Rs) (hall : AllBound t) (ht : t.check = .ok ())
    {g : Nat} (hg : 46 ≤ g ∧ g < 77) {r : Role} (hgr : Ix.SpecDigest.groupOf r = g)
    {R R₁ R' : Ixon.Env} {env₁ : Ix.Kernel.Env .anon}
    (hadm : Admits ρ t g R R') (hle : StoreLe R₁ R')
    (hb₁ : BndOver.{u} L t (· < g) R₁ env₁)
    (hrec : ∀ x c, recordOf R' x = some c → (∀ ms, c.info ≠ .muts ms) →
      (env₁.find? (Core.keyOf t x)).isSome = true) :
    EqnsRoleShape env₁ r := by
  have htwf : t.wf = true := wf_of_check ht
  have hhrg : r ∈ roleGroup g := hgr ▸ role_mem_roleGroup r
  obtain ⟨Ec, hRF, hstep⟩ := hrun.stepStores R₁
    (fun a lc h => hadm.loaded a lc (hle.1 a lc h))
    (fun a b h => hadm.loadedBlobs a b (hle.2 a b h))
    hb₁.shape.committed hb₁.shape.zeroFree
  have hPI : Decl.PrefixInv.{u} Ec t (some (valLimit g)) env₁ :=
    hb₁.inv hRF (carried_valLimit g) (limWithin_below t g)
  let cx : ScopedCtx := Ctx.stored ⟨Ec, env₁, t, some (valLimit g)⟩
  have hgoodAll : CoreGood cx calls :=
    CoreGood.ofRaw (hstep.good env₁ (some (valLimit g))) (fun _ _ => trivial)
  -- extract the run's observed validation of `r`
  have hval := hadm.validated r hhrg
  obtain ⟨bAddr, tb, -, -, hρ⟩ := hrun.observed
  have hval' : RoleValidationIn calls bAddr t g r := by
    have e : ρ.validated = (observedRun calls bAddr t ρ.E₀ ρ.rank).validated :=
      congrArg BRun.validated hρ
    rw [e] at hval
    exact hval
  obtain ⟨h, h', x_rc, x_tbl, res, cs, hrc, htbl, ev_val, hsub⟩ := hval'
  have hdec := List.all_eq_true.mp eqnsTermsStoredOk_true r (Role.mem_all r)
  simp only [hgr, hg.1, hg.2, decide_true, Bool.and_self, ↓reduceIte] at hdec
  constructor
  · -- `roleSpecKindNat r = 5`: `validate_eqns`
    intro h5
    simp only [h5, beq_self_eq_true, ↓reduceIte, Bool.and_eq_true, List.all_eq_true,
      decide_eq_true_eq] at hdec
    obtain ⟨⟨⟨⟨hiso, hty_dec⟩, hanc_dec⟩, hlen64⟩, heqns_dec⟩ := hdec
    cases hlv : roleSpecLevels r with
    | none => rw [hlv] at hty_dec; simp at hty_dec
    | some n =>
      cases hrt : roleTypeExact r with
      | none => rw [hlv, hrt] at hty_dec; simp at hty_dec
      | some T₀ =>
        rw [hlv, hrt] at hty_dec
        cases Obs.«KernelRoles::validate_role».obs ev_val with
        | n5 v1 m2 cs12 v31 m32 p39 cs45 v67 v68 m70 cs78 m90 cs98 m111 cs122 cs376
            ev14 ev47 ld41 ev80 ev100 heq109 ev124 ev378 hc419 =>
          have hsub45 : ∀ cl ∈ cs45, cl ∈ calls := fun cl hm => hsub cl (by rw [hc419]; simp [hm])
          have hsub376 : ∀ cl ∈ cs376, cl ∈ calls := fun cl hm => hsub cl (by rw [hc419]; simp [hm])
          obtain ⟨ext_ba, a', ⟨b, hb, rfl⟩, had⟩ :=
            RoleVal.role_bound_addr_uncond htbl.toTableRep ev14
          obtain ⟨ci, hci_k, hci_rep⟩ :=
            stored_get_ci hrun hadm hPI hgoodAll hrec hsub45 hb ev47 ld41
              (hadm.eqnsBound r hhrg h5 _ had)
          rw [keyOf_of_addressOf htwf had] at hci_k
          obtain ⟨x_nlvls, x_ty, w17, x_safety, w18, v100, m101, cs103, v121, m130, cs138,
            v150, m151, cs161, v166, m182, cs190, v_la, m_la, cs_la, v209, m210, cs220,
            v239, m240, cs250, v280, v281, m283, cs291, m303, cs311, cs326,
            hv15, sg108, ev140, heq149, ev192, ev163, ev_anc, ev222, ev252, ev293, ev313,
            heq322, ev328, hc368⟩ := Obs.«KernelRoles::validate_eqns».obs ev378
          have hsub161 : ∀ cl ∈ cs161, cl ∈ calls :=
            fun cl hm => hsub376 cl (by rw [hc368]; simp [hm])
          have hsub_la : ∀ cl ∈ cs_la, cl ∈ calls :=
            fun cl hm => hsub376 cl (by rw [hc368]; simp [hm])
          have hsub326 : ∀ cl ∈ cs326, cl ∈ calls :=
            fun cl hm => hsub376 cl (by rw [hc368]; simp [hm])
          -- Anchor storage (`ar ∈ eqnsAnchorsOf r`) comes from `walk_bound_anchor` inside `ev_anc`!
          -- We prove every `ar ∈ eqnsAnchorsOf r` is stored in `env₁` first so `hstored` holds!
          have ext_h_111 : Heap.Extends h m111 :=
            ext_ba.trans (ev47.heap_extends.trans (ev80.heap_extends.trans
              (ev100.heap_extends.trans ev124.heap_extends)))
          have ext_111_101 : Heap.Extends m111 m101 := by
            cases sg108 with
            | Safe _ _ hm _ => rw [hm]
            | other _ _ _ hm _ => rw [hm]
          have ext_111_182 : Heap.Extends m111 m182 :=
            ext_111_101.trans (ev140.heap_extends.trans ev192.heap_extends)
          have ext_h_151 : Heap.Extends h m151 :=
            ext_h_111.trans (ext_111_182.trans ev163.heap_extends)
          have hanc_stored : ∀ ar ∈ eqnsAnchorsOf r, ∃ ci_a, env₁.find? (.role ar) = some ci_a := by
            have oneStored : ∀ (ar : Role) (har : ar ∈ eqnsAnchorsOf r)
                {vr : SourceValue F} {ha hb : Heap F} {csw : List (Call F)},
                Heap.Extends m151 ha →
                ObsFn W "KernelRoles::walk_bound_anchor" [x_rc, x_tbl, .field (roleNum ar)] ha vr hb csw →
                (∀ cl ∈ csw, cl ∈ calls) → ∃ ci_a, env₁.find? (.role ar) = some ci_a := by
              intro ar har vr ha hb csw hext ev_w hsub_w
              obtain ⟨va, ma, csa, vci, mci, pci, csci, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
                evba, evci, ldci, _, _, _, _, _, _, _, hcw⟩ :=
                Obs.«KernelRoles::walk_bound_anchor».obs ev_w
              obtain ⟨_, a_ar, ⟨b_ar, hb_ar, rfl⟩, had_ar⟩ :=
                RoleVal.role_bound_addr_uncond (htbl.toTableRep.mono (ext_h_151.trans hext)) evba
              obtain ⟨ci_a, hci_a, -⟩ := stored_get_ci hrun hadm hPI hgoodAll hrec
                (fun cl hm => hsub_w cl (by rw [hcw]; simp [hm])) hb_ar evci ldci
                (hadm.eqnsAnchors r hhrg h5 ar har _ had_ar)
              rw [keyOf_of_addressOf htwf had_ar] at hci_a
              exact ⟨ci_a, hci_a⟩
            cases Obs.«KernelRoles::validate_eqns_anchors».obs ev_anc with
            | n65 v1 m1 cs1 v2 m2 cs2 v3 m3 cs3 cs4 hv ev1 ev2 ev3 ev4 hca =>
              have hr : r = .decidableDecide := RolesAux.roleNum_inj (Value.field.inj hv)
              subst hr
              intro ar har
              simp only [eqnsAnchorsOf, RoleVal.eqnsAnchorsOf, List.mem_cons, List.not_mem_nil, or_false] at har
              rcases har with rfl | rfl | rfl | rfl
              · exact oneStored .decidable (by decide) (Heap.Extends.refl _) ev1
                  (fun cl hm => hsub_la cl (by rw [hca]; simp [hm]))
              · exact oneStored .decidableIsTrue (by decide) ev1.heap_extends ev2
                  (fun cl hm => hsub_la cl (by rw [hca]; simp [hm]))
              · exact oneStored .decidableIsFalse (by decide) (ev1.heap_extends.trans ev2.heap_extends) ev3
                  (fun cl hm => hsub_la cl (by rw [hca]; simp [hm]))
              · exact oneStored .notProp (by decide)
                  (ev1.heap_extends.trans (ev2.heap_extends.trans ev3.heap_extends)) ev4
                  (fun cl hm => hsub_la cl (by rw [hca]; simp [hm]))
            | n68 cs1 _ hv ev1 hca =>
              have hr : r = .natDecLe := RolesAux.roleNum_inj (Value.field.inj hv)
              subst hr
              intro ar har
              simp only [eqnsAnchorsOf, RoleVal.eqnsAnchorsOf, List.mem_cons, List.not_mem_nil, or_false] at har
              subst har
              exact oneStored .natLe (by decide) (Heap.Extends.refl _) ev1
                (fun cl hm => hsub_la cl (by rw [hca]; simp [hm]))
            | n73 v1 m1 cs1 v2 m2 cs2 cs3 _ _ hv ev1 ev2 ev3 hca =>
              have hr : r = .intNegOfNat := RolesAux.roleNum_inj (Value.field.inj hv)
              subst hr
              intro ar har
              simp only [eqnsAnchorsOf, RoleVal.eqnsAnchorsOf, List.mem_cons, List.not_mem_nil, or_false] at har
              rcases har with rfl | rfl | rfl
              · exact oneStored .int (by decide) (Heap.Extends.refl _) ev1
                  (fun cl hm => hsub_la cl (by rw [hca]; simp [hm]))
              · exact oneStored .intOfNat (by decide) ev1.heap_extends ev2
                  (fun cl hm => hsub_la cl (by rw [hca]; simp [hm]))
              · exact oneStored .intNegSucc (by decide) (ev1.heap_extends.trans ev2.heap_extends) ev3
                  (fun cl hm => hsub_la cl (by rw [hca]; simp [hm]))
            | n85 v1 m1 cs1 cs2 _ _ _ hv ev1 ev2 hca =>
              have hr : r = .bitVecToNat := RolesAux.roleNum_inj (Value.field.inj hv)
              subst hr
              intro ar har
              simp only [eqnsAnchorsOf, RoleVal.eqnsAnchorsOf, List.mem_cons, List.not_mem_nil, or_false] at har
              rcases har with rfl | rfl
              · exact oneStored .bitVec (by decide) (Heap.Extends.refl _) ev1
                  (fun cl hm => hsub_la cl (by rw [hca]; simp [hm]))
              · exact oneStored .bitVecOfNat (by decide) ev1.heap_extends ev2
                  (fun cl hm => hsub_la cl (by rw [hca]; simp [hm]))
            | n90 v1 m1 cs1 cs2 _ _ _ _ hv ev1 ev2 hca =>
              have hr : r = .stringToByteArray := RolesAux.roleNum_inj (Value.field.inj hv)
              subst hr
              intro ar har
              simp only [eqnsAnchorsOf, RoleVal.eqnsAnchorsOf, List.mem_cons, List.not_mem_nil, or_false] at har
              rcases har with rfl | rfl
              · exact oneStored .byteArray (by decide) (Heap.Extends.refl _) ev1
                  (fun cl hm => hsub_la cl (by rw [hca]; simp [hm]))
              · exact oneStored .byteArrayEmpty (by decide) ev1.heap_extends ev2
                  (fun cl hm => hsub_la cl (by rw [hca]; simp [hm]))
            | n96 cs1 _ _ _ _ _ hv ev1 hca =>
              have hr : r = .intDecLe := RolesAux.roleNum_inj (Value.field.inj hv)
              subst hr
              intro ar har
              simp only [eqnsAnchorsOf, RoleVal.eqnsAnchorsOf, List.mem_cons, List.not_mem_nil, or_false] at har
              subst har
              exact oneStored .intLe (by decide) (Heap.Extends.refl _) ev1
                (fun cl hm => hsub_la cl (by rw [hca]; simp [hm]))
            | other hne65 hne68 hne73 hne85 hne90 hne96 _ _ _ =>
              intro ar har
              cases r <;> first
                | exact absurd rfl hne65 | exact absurd rfl hne68 | exact absurd rfl hne73
                | exact absurd rfl hne85 | exact absurd rfl hne90 | exact absurd rfl hne96
                | (simp [eqnsAnchorsOf, RoleVal.eqnsAnchorsOf] at har)
          have hstored : ∀ s, roleStoredBy g r s = true → ∃ ci_s, env₁.find? (.role s) = some ci_s :=
            fun s hs => stored_of_roleStoredBy hall hg.1 hb₁ ⟨ci, hci_k⟩ hanc_stored hs
          -- 1. `RoleExactTy env₁ r`
          have hroleTy : RoleExactTy env₁ r := by
            have hlen : ci.toConstantVal.levelParams.length = n :=
              levels_eq_of_ciRep hlv hci_rep ev80 ev100 heq109
            rw [hv15] at hci_rep
            generalize hv_ci : (Value.construct kciEnum "Defn" [x_nlvls, x_ty, w17, x_safety, w18] : SourceValue F) = v_ci at hci_rep
            cases hci_rep with
            | defn hval_rep _ =>
              injection hv_ci with _ _ hl_ci
              simp only [List.cons.injEq, and_true] at hl_ci
              obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hl_ci
              have ext_32_130 : Heap.Extends m32 m130 :=
                ev80.heap_extends.trans (ev100.heap_extends.trans (ev124.heap_extends.trans
                  (ext_111_101.trans ev140.heap_extends)))
              have ext_h_130 : Heap.Extends h m130 := ext_ba.trans (ev47.heap_extends.trans ext_32_130)
              obtain ⟨ext_192, hsp_ex, hsp_cells⟩ :=
                roleTypeExactRenders hiso hrt htwf (htbl.toTableRep.mono ext_h_130) ev192
              have hsp_tm : TmC cx.κ m182 T₀ v166 :=
                tmCExact_to_stored htwf hsp_ex hsp_cells hty_dec hstored
              have hty_tm : TmC cx.κ m182 _ x_ty :=
                fun d Γ => Tm.mono (ext_32_130.trans ext_192) (hval_rep.2.2.2 d Γ)
              have hde := assert_type_meets_defEq hPI
                ((hrc.mono (ext_h_130.trans ext_192)).toRCRep)
                (hgoodAll.sub hsub161) ev163 hty_tm hsp_tm
              exact ⟨_, T₀, hci_k, rfl, by rw [hlen]; exact hlv, hrt, hde⟩
            | _ =>
              injection hv_ci with _ hc_ci _
              exact absurd hc_ci (by decide)
          -- 2. `∀ ar ∈ eqnsAnchorsOf r, RoleExactTy env₁ ar`
          have hanc_ok : ∀ ar ∈ eqnsAnchorsOf r, isEqnsOrAnchorRole ar = true ∧
              ∃ n_a T_a, roleSpecLevels ar = some n_a ∧ roleTypeExact ar = some T_a ∧
                T_a.constsResolveBy (keyStoredBy g r) = true := by
            intro ar har
            have ha := hanc_dec ar har
            refine ⟨ha.1, ?_⟩
            cases h1 : roleSpecLevels ar with
            | none => rw [h1] at ha; simp at ha
            | some n_a =>
              cases h2 : roleTypeExact ar with
              | none => rw [h1, h2] at ha; simp at ha
              | some T_a =>
                rw [h1, h2] at ha
                exact ⟨n_a, T_a, rfl, rfl, ha.2⟩
          have hancTy : ∀ ar ∈ eqnsAnchorsOf r, RoleExactTy env₁ ar :=
            validate_eqns_anchors_exact hrun ht hadm hPI hgoodAll hrec hhrg h5 hanc_ok hstored
              (hrc.mono ext_h_151) (htbl.mono ext_h_151) ev_anc hsub_la
          -- 3. `∀ e ∈ eqnsOfRole r, EqnValid env₁ r e`
          have heqns_valid : ∀ e ∈ eqnsOfRole r, EqnValid env₁ r e := by
            have ext_h_210 : Heap.Extends h m210 :=
              ext_h_151.trans (ev_anc.heap_extends.trans ev222.heap_extends)
            obtain ⟨es, hes_list, hes_src⟩ :=
              role_evidence_step cx ev252 x_tbl r rfl (htbl.toTableRep.mono ext_h_210)
            obtain ⟨hv280, hm283⟩ := evList_length_spec ev293 hes_list
            obtain ⟨hv281, hm303⟩ := eqns_equation_count_exact r ev313
            have hle_len : (eqnsOfRole r).length ≤ es.length := by
              have hf : ((es.length : Nat) : F) = (((eqnsOfRole r).length : Nat) : F) :=
                Value.field.inj (hv280.symm.trans (heq322.trans hv281))
              have hval := congrArg ZMod.val hf
              rw [ZMod.val_natCast, NatAux.val_natCast (by omega)] at hval
              exact hval ▸ Nat.mod_le es.length _
            have hproofs : ∀ thm, Ix.Kernel.Evidence.proof thm ∈ es → (recordOf R' thm).isSome = true := by
              intro thm hmem
              rcases hes_src with rfl | ⟨arr, hmem_arr, rfl⟩
              · cases hmem
              · exact hadm.eqnsProofs r hhrg h5 arr thm hmem_arr hmem
            have ext_h_303 : Heap.Extends h m303 :=
              ext_h_210.trans (ev252.heap_extends.trans (ev293.heap_extends.trans ev313.heap_extends))
            have heqns_ok : ∀ e ∈ eqnsOfRole r,
                (eqnsStmtExact e).constsResolveBy (keyStoredBy g r) = true ∧
                (e.hyps.isEmpty = true →
                  (eqnsSideExact e e.lhs).constsResolveBy (keyStoredBy g r) = true ∧
                  (eqnsSideExact e e.rhs).constsResolveBy (keyStoredBy g r) = true) := by
              intro e he
              have h1 := heqns_dec e he
              refine ⟨h1.1, fun hu => ?_⟩
              have h2 := h1.2
              simp only [hu, ↓reduceIte, Bool.and_eq_true] at h2
              exact h2
            have hes_list303 : RepList evListEnum EvRep m303 es v239 := by
              rw [hm303, hm283]; exact hes_list
            intro e he
            obtain ⟨i, hget⟩ := List.mem_iff_getElem?.mp he
            have hi_lt : i < (eqnsOfRole r).length := by
              cases hlt_i : decide (i < (eqnsOfRole r).length) with
              | true => exact of_decide_eq_true hlt_i
              | false =>
                rw [List.getElem?_eq_none (by simp at hlt_i; omega)] at hget
                cases hget
            exact validate_eqns_equations_valid hrun ht hadm hPI hgoodAll hrec hhrg h5 hlv
              heqns_ok hstored es 0 hproofs (hrc.mono ext_h_303) (htbl.mono ext_h_303)
              hes_list303 (by simpa using ev328) hsub326 i e (Nat.zero_le i)
              (by omega) hget
          exact ⟨hroleTy, hancTy, heqns_valid⟩
        | n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
          obtain ⟨hsk_f, -⟩ := RoleVal.role_spec_kind_spec ev124
          rw [h5] at hsk_f; exact absurd (Value.field.inj hsk_f) (by decide)
        | n1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
          obtain ⟨hsk_f, -⟩ := RoleVal.role_spec_kind_spec ev124
          rw [h5] at hsk_f; exact absurd (Value.field.inj hsk_f) (by decide)
        | n2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
          obtain ⟨hsk_f, -⟩ := RoleVal.role_spec_kind_spec ev124
          rw [h5] at hsk_f; exact absurd (Value.field.inj hsk_f) (by decide)
        | n3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
          obtain ⟨hsk_f, -⟩ := RoleVal.role_spec_kind_spec ev124
          rw [h5] at hsk_f; exact absurd (Value.field.inj hsk_f) (by decide)
        | n4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
          obtain ⟨hsk_f, -⟩ := RoleVal.role_spec_kind_spec ev124
          rw [h5] at hsk_f; exact absurd (Value.field.inj hsk_f) (by decide)
  · -- `roleSpecKindNat r = 1` and `anchorWalked r = true`: `validate_anchor` (`of_decide_eq_{true,false}`)
    intro h1 haw
    have hne5 : (RoleVal.roleSpecKindNat r == 5) = false := by rw [h1]; decide
    have h1' : (RoleVal.roleSpecKindNat r == 1) = true := by rw [h1]; rfl
    simp only [hne5, h1', haw, Bool.and_self, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true,
      Bool.not_eq_true'] at hdec
    obtain ⟨⟨hiso, hnotPin⟩, hty_dec⟩ := hdec
    cases hlv : roleSpecLevels r with
    | none => rw [hlv] at hty_dec; simp at hty_dec
    | some n =>
      cases hrt : roleTypeExact r with
      | none => rw [hlv, hrt] at hty_dec; simp at hty_dec
      | some T₀ =>
        rw [hlv, hrt] at hty_dec
        cases Obs.«KernelRoles::validate_role».obs ev_val with
        | n1 v1 m2 cs12 v31 m32 p39 cs45 v67 v68 m70 cs78 m90 cs98 m111 cs122 cs192
            ev14 ev47 ld41 ev80 ev100 heq109 ev124 ev194 hc227 =>
          have hsub45 : ∀ cl ∈ cs45, cl ∈ calls := fun cl hm => hsub cl (by rw [hc227]; simp [hm])
          have hsub192 : ∀ cl ∈ cs192, cl ∈ calls := fun cl hm => hsub cl (by rw [hc227]; simp [hm])
          obtain ⟨ext_ba, a', ⟨b, hb, rfl⟩, had⟩ :=
            RoleVal.role_bound_addr_uncond htbl.toTableRep ev14
          obtain ⟨ci, hci_k, hci_rep⟩ :=
            stored_get_ci hrun hadm hPI hgoodAll hrec hsub45 hb ev47 ld41
              (hadm.walkedAnchors r hhrg haw _ had)
          rw [keyOf_of_addressOf htwf had] at hci_k
          have hlen : ci.toConstantVal.levelParams.length = n :=
            levels_eq_of_ciRep hlv hci_rep ev80 ev100 heq109
          have hnoAnc : eqnsAnchorsOf r = [] := by
            cases r <;> first | exact absurd h1 (by decide) | rfl
          have hstored : ∀ s, roleStoredBy g r s = true → ∃ ci_s, env₁.find? (.role s) = some ci_s :=
            fun s hs => stored_of_roleStoredBy hall hg.1 hb₁ ⟨ci, hci_k⟩
              (fun ar har => by rw [hnoAnc] at har; cases har) hs
          have h_extract_atm : ∀ {v23 v139 m140 v605 m606 cs608},
              Heap.Extends m32 m140 →
              TmC cx.κ m32 (posOf ci.toConstantVal.levelParams ci.toConstantVal.type) v23 →
              Decl.TmCExact (Core.keyOf t) m140 T₀ v139 →
              (∀ x, AddrIn m140 v139 x → ∃ s, t.addressOf? s = some (ixAddr x) ∧
                ∀ P, T₀.constsResolveBy P = true → P (.role s) = true) →
              Obs.«KernelRoles::validate_anchor».Seg1 v139 v23 x_rc x_tbl (.field (roleNum r)) v31
                m140 v605 m606 cs608 →
              (∀ cl ∈ cs608, cl ∈ calls) →
              DefEq env₁ 0 (posOf ci.toConstantVal.levelParams ci.toConstantVal.type) T₀ := by
            intro v23 v139 m140 v605 m606 cs608 ext_32_140 hty_rep hsp_ex hsp_cells sg hsub_sg
            have badPin : ∀ k ∈ pinnedIdxs, roleNum r = (k : F) → False := by
              intro k hk he
              have hv := congrArg ZMod.val he
              rw [RolesAux.val_roleNum, RolesAux.val_natCast (by
                simp only [pinnedIdxs, List.mem_cons, List.not_mem_nil, or_false] at hk
                rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)] at hv
              rw [hv] at hnotPin
              exact absurd hk (of_decide_eq_false hnotPin)
            cases sg with
            | n4 _ hv _ _ => exact absurd (Value.field.inj hv) (badPin 4 (by decide))
            | n5 _ _ hv _ _ => exact absurd (Value.field.inj hv) (badPin 5 (by decide))
            | n6 _ _ _ hv _ _ => exact absurd (Value.field.inj hv) (badPin 6 (by decide))
            | n7 _ _ _ _ hv _ _ => exact absurd (Value.field.inj hv) (badPin 7 (by decide))
            | n20 _ _ _ _ _ hv _ _ => exact absurd (Value.field.inj hv) (badPin 20 (by decide))
            | n21 _ _ _ _ _ _ hv _ _ => exact absurd (Value.field.inj hv) (badPin 21 (by decide))
            | n22 _ _ _ _ _ _ _ hv _ _ => exact absurd (Value.field.inj hv) (badPin 22 (by decide))
            | n29 _ _ _ _ _ _ _ _ hv _ _ => exact absurd (Value.field.inj hv) (badPin 29 (by decide))
            | n30 _ _ _ _ _ _ _ _ _ hv _ _ => exact absurd (Value.field.inj hv) (badPin 30 (by decide))
            | n31 _ _ _ _ _ _ _ _ _ _ hv _ _ => exact absurd (Value.field.inj hv) (badPin 31 (by decide))
            | n37 _ _ _ _ _ _ _ _ _ _ _ hv _ _ => exact absurd (Value.field.inj hv) (badPin 37 (by decide))
            | n38 _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ => exact absurd (Value.field.inj hv) (badPin 38 (by decide))
            | n39 _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ => exact absurd (Value.field.inj hv) (badPin 39 (by decide))
            | n40 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hv _ _ => exact absurd (Value.field.inj hv) (badPin 40 (by decide))
            | other cs577 _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev579 hc604 =>
              have ext_h_140 : Heap.Extends h m140 := ext_ba.trans (ev47.heap_extends.trans ext_32_140)
              have hsp_tm : TmC cx.κ m140 T₀ v139 :=
                tmCExact_to_stored htwf hsp_ex hsp_cells hty_dec hstored
              have hty_tm : TmC cx.κ m140 _ v23 :=
                fun d Γ => Tm.mono ext_32_140 (hty_rep d Γ)
              exact assert_type_meets_defEq hPI ((hrc.mono ext_h_140).toRCRep)
                (hgoodAll.sub (fun cl hm => hsub_sg cl (by rw [hc604]; simp [hm])))
                ev579 hty_tm hsp_tm
          cases Obs.«KernelRoles::validate_anchor».obs ev194 with
          | n1 v1' m2' cs12' v_ok m_ok cs_ok v23 m24 cs34 v45 m46 cs56 v61 m76 cs84 v95 m96 cs106
              m127 v139 m140 cs150 v605 m606 cs608 _ _ _ _ _ _
              ev14' ev_ok _ ev36 ev86 ev58 hm135 ev108 ev152 sg613 _ _ _ hc684 =>
            obtain ⟨_, hty_rep⟩ := const_type_of_ciRep hci_rep ev36
            have ext_m127 : Heap.Extends m46 m127 := by rw [hm135]; exact Heap.Extends.snoc m46 _
            have ext_32_96 : Heap.Extends m32 m96 :=
              ev80.heap_extends.trans (ev100.heap_extends.trans (ev124.heap_extends.trans
                (ev14'.heap_extends.trans (ev_ok.heap_extends.trans (ev36.heap_extends.trans
                  (ev86.heap_extends.trans (ev58.heap_extends.trans
                    (ext_m127.trans ev108.heap_extends))))))))
            have ext_h_96 : Heap.Extends h m96 := ext_ba.trans (ev47.heap_extends.trans ext_32_96)
            obtain ⟨ext140, hsp_ex, hsp_cells⟩ :=
              roleTypeExactRenders hiso hrt htwf (htbl.toTableRep.mono ext_h_96) ev152
            have hde := h_extract_atm (ext_32_96.trans ext140) hty_rep hsp_ex hsp_cells sg613
              (fun cl hm => hsub192 cl (by rw [hc684]; simp [hm]))
            exact ⟨ci, T₀, hci_k, ciRep_notTower hci_rep, by rw [hlen]; exact hlv, hrt, hde⟩
          | other v1' m2' cs12' v_ok m_ok cs_ok v23 m24 cs34 v45 m46 cs56 v61 m76 cs84 v95 m96 cs106
              m127 v139 m140 cs150 v605 m606 cs608 _ _ _
              ev14' ev_ok _ ev36 ev86 ev58 hm135 ev108 ev152 sg613 _ _ _ _ hc693 =>
            obtain ⟨_, hty_rep⟩ := const_type_of_ciRep hci_rep ev36
            have ext_m127 : Heap.Extends m46 m127 := by rw [hm135]; exact Heap.Extends.snoc m46 _
            have ext_32_96 : Heap.Extends m32 m96 :=
              ev80.heap_extends.trans (ev100.heap_extends.trans (ev124.heap_extends.trans
                (ev14'.heap_extends.trans (ev_ok.heap_extends.trans (ev36.heap_extends.trans
                  (ev86.heap_extends.trans (ev58.heap_extends.trans
                    (ext_m127.trans ev108.heap_extends))))))))
            have ext_h_96 : Heap.Extends h m96 := ext_ba.trans (ev47.heap_extends.trans ext_32_96)
            obtain ⟨ext140, hsp_ex, hsp_cells⟩ :=
              roleTypeExactRenders hiso hrt htwf (htbl.toTableRep.mono ext_h_96) ev152
            have hde := h_extract_atm (ext_32_96.trans ext140) hty_rep hsp_ex hsp_cells sg613
              (fun cl hm => hsub192 cl (by rw [hc693]; simp [hm]))
            exact ⟨ci, T₀, hci_k, ciRep_notTower hci_rep, by rw [hlen]; exact hlv, hrt, hde⟩
        | n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
          obtain ⟨hsk_f, -⟩ := RoleVal.role_spec_kind_spec ev124
          rw [h1] at hsk_f; exact absurd (Value.field.inj hsk_f) (by decide)
        | n2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
          obtain ⟨hsk_f, -⟩ := RoleVal.role_spec_kind_spec ev124
          rw [h1] at hsk_f; exact absurd (Value.field.inj hsk_f) (by decide)
        | n3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
          obtain ⟨hsk_f, -⟩ := RoleVal.role_spec_kind_spec ev124
          rw [h1] at hsk_f; exact absurd (Value.field.inj hsk_f) (by decide)
        | n4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
          obtain ⟨hsk_f, -⟩ := RoleVal.role_spec_kind_spec ev124
          rw [h1] at hsk_f; exact absurd (Value.field.inj hsk_f) (by decide)
        | n5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
          obtain ⟨hsk_f, -⟩ := RoleVal.role_spec_kind_spec ev124
          rw [h1] at hsk_f; exact absurd (Value.field.inj hsk_f) (by decide)

/-- **`RoleFreeShapes` at every equation / walked-anchor group `46 ≤ g < 77`**. -/
theorem roleFreeShapes_eqnsGroup {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {calls : List (Call F)} {t : Ix.Kernel.RoleTable} {ρ : BRun} {Rs : Nat → Ixon.Env}
    (hrun : BindingRun calls t ρ Rs) (hall : AllBound t) (ht : t.check = .ok ())
    {g : Nat} (hg : 46 ≤ g ∧ g < 77) :
    RoleFreeShapes.{u} L ρ t g := by
  intro _ R R₁ R' env₁ hadm _ hle hb₁ _ hrec
  have hs := hb₁.facts.shapes
  obtain ⟨gB, -, -, gC, gS, gL, -, -, gCN, gSL, gI, gN⟩ := anchor_groups
  have below : ∀ X : Role, Ix.SpecDigest.groupOf X < g + 1 →
      Ix.SpecDigest.groupOf X ≠ g → Ix.SpecDigest.groupOf X < g := fun _ h hne => by omega
  exact {
    bool := fun h => hs.bool (below _ h (by rw [gB]; omega))
    char := fun h => hs.char (below _ h (by rw [gC]; omega))
    string := fun h => hs.string (below _ h (by rw [gS]; omega))
    list := fun h => hs.list (below _ h (by rw [gL]; omega))
    charOfNat := fun h => hs.charOfNat (below _ h (by rw [gCN]; omega))
    stringOfList := fun h => hs.stringOfList (below _ h (by rw [gSL]; omega))
    iff := fun h => hs.iff (below _ h (by rw [gI]; omega))
    nonempty := fun h => hs.nonempty (below _ h (by rw [gN]; omega))
    eqns := fun r h46 hlt => by
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hlt) with hlt' | heq
      · exact hs.eqns r h46 hlt'
      · exact eqnsRoleShape_at_group hrun hall ht hg heq hadm hle hb₁ hrec }

end IxVM.Refinement.Binding
