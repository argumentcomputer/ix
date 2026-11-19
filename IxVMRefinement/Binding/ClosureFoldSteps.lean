import IxVMRefinement.Binding.ClosureFoldRun

/-! # The closure fold: its steps and its result

* `reads_owned`: the reading of an owned address over the run's records is a reading over the
  closure's store (the admission's reading clause, then `reads_closureStore`);
* `closure_finish`: the state after a unit's step, from the step's new constants;
* `closureFold_steps`: the steps of the fold (`UnitFold.Steps`), from the plain, family and twin
  step premises: a unit with a selected family record by the family step, handed its family
  check's advice; a unit of a twin's shape by the twin step, handed its block's family record
  installed; every other unit by its plain step;
* `closureFold_start`: the invariant at the witness's environment;
* `closureFold_run`: the fold's result: an environment with the invariant, extending the
  witness's, storing every unit's owned addresses with their readings over the closure's store,
  and nothing else new. -/

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

section Steps

variable {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop} {calls : List (Call F)} {ρ : BRun}
  {t : Ix.Kernel.RoleTable} {g : Nat} {R R' : Ixon.Env} {env : Ix.Kernel.Env .anon}
  {famOf₀ famOf : _root_.Address → Option _root_.Address}
  {adv cont : _root_.Address → _root_.Address → Prop} {bAddr : _root_.Address}

local notation "R₁" => closureStore t g R R'

/-- **The reading of an owned address over the run's records is a reading over the closure's
store.** -/
theorem reads_owned
    (hC : ClosureCtx.{u} L calls ρ t g R R' R₁ env famOf₀ famOf adv cont bAddr)
    {A x : _root_.Address} (hA : IsClosureUnit R R₁ famOf A) (hx : FamOwns R₁ famOf A x)
    {ci₀ : ConstantInfo .anon} (h : Reads t ρ.E₀ x ci₀) : Reads t R₁ x ci₀ := by
  obtain ⟨D, cD, hnD, hcD, hxD, hnx, -⟩ := owned_new hC hA hx
  obtain ⟨hnD', -⟩ := new_of_closureStore hnD
  have h' := hC.reads.reads D cD x ci₀ hnD' (rec₁₂ hcD) hxD h
  obtain ⟨cx, hcx⟩ := Option.isSome_iff_exists.mp hnx.1
  exact reads_closureStore hC.run.roleUnitForm (notNewUnit_of_rec₁ hcx) h'

/-- **The state after a unit's step** (module docstring). -/
theorem closure_finish
    (hC : ClosureCtx.{u} L calls ρ t g R R' R₁ env famOf₀ famOf adv cont bAddr)
    (htwf : t.wf = true) {s : Ix.Kernel.Env .anon}
    (hI : ClosureFoldInv.{u} L t g R₁ env famOf₀ famOf s)
    {A : _root_.Address} (hA : IsClosureUnit R R₁ famOf A)
    (new : List (ConstantInfo .anon)) (Reg' : NativeFam .anon → Prop)
    (hnd : (new.map (·.name)).Nodup) (hfresh : ∀ ci ∈ new, s.find? ci.name = none)
    (hcl : ∀ E, RecordsFor R₁ E → ∀ lim, Carried lim → LimWithin (· < g) t lim →
      FoldClauseWith.{u} L t E lim ⟨new ++ s.consts⟩ Reg')
    (hops : ∀ ci ∈ new, ci.name ∉ RoleOps.opNames)
    (hreads : ∀ x, FamOwns R₁ famOf A x →
      ∃ ci ∈ new, ∃ ci₀, ci.name = keyOf t x ∧ Reads t ρ.E₀ x ci₀ ∧ StoredAs ci ci₀)
    (hnames : ∀ ci ∈ new, (∃ x, FamOwns R₁ famOf A x ∧ ci.name = keyOf t x) ∨
      ∃ k s, ci.name = .aux k s)
    (hinst : ∀ rb crb, famOf A = some rb → recordOf R₁ rb = some crb →
      FamilyInstalled t ⟨new ++ s.consts⟩ rb crb)
    (hrecs : ∀ cb rb crb, famOf A = some rb → recordOf R₁ A = some cb → recordOf R₁ rb = some crb →
      StoredFamilyRecs t R₁ ⟨new ++ s.consts⟩ A cb rb crb) :
    ∃ s', ClosureFoldInv.{u} L t g R₁ env famOf₀ famOf s' ∧
      (∀ ci ∈ s.consts, ci ∈ s'.consts) ∧
      (∀ x, FamOwns R₁ famOf A x → StoredAt t s' x) ∧
      (∀ x, FamOwns R₁ famOf A x →
        ∃ ci ∈ s'.consts, ci.name = keyOf t x ∧ ∃ ci₀, Reads t R₁ x ci₀ ∧ StoredAs ci ci₀) ∧
      ∀ x, StoredAt t s' x → StoredAt t s x ∨ FamOwns R₁ famOf A x := by
  have hgrow : Ix.Kernel.Grows (fun _ => True) s ⟨new ++ s.consts⟩ :=
    ⟨new, rfl, fun ci hci => ⟨trivial, hfresh ci hci⟩, hnd⟩
  have hnd' := hgrow.nodup hI.nodup
  have hext : ∀ ci ∈ s.consts, ci ∈ (⟨new ++ s.consts⟩ : Ix.Kernel.Env .anon).consts :=
    fun ci h => List.mem_append_right _ h
  have hreads₁ : ∀ x, FamOwns R₁ famOf A x →
      ∃ ci ∈ new, ci.name = keyOf t x ∧ ∃ ci₀, Reads t R₁ x ci₀ ∧ StoredAs ci ci₀ := by
    intro x hx
    obtain ⟨ci, hci, ci₀, hname, hr, hst⟩ := hreads x hx
    exact ⟨ci, hci, hname, ci₀, reads_owned hC hA hx hr, hst⟩
  have hkept : ∀ x, FamOwns R₁ famOf A x → ∀ ci ∈ new, ci.name = keyOf t x →
      KeptIn t (recordOf R₁) (fun y => (R₁).blobs.get? y) x ci := by
    intro x hx ci hci hname
    obtain ⟨ci', hci', hname', ci₀, hr, hst⟩ := hreads₁ x hx
    have hcc : ci' = ci := eq_of_name_eq hnd hci' hci (hname'.trans hname.symm)
    subst hcc
    obtain ⟨-, -, -, -, -, -, hnax⟩ := owned_new hC hA hx
    exact ⟨fun c ax hc hi => (hnax ax c hc hi).elim, ci₀, hr, hst⟩
  have hframe : ∀ x, StoredAt t ⟨new ++ s.consts⟩ x → StoredAt t s x ∨ FamOwns R₁ famOf A x := by
    intro x hx
    obtain ⟨ci, hci, hname⟩ := hx
    rcases List.mem_append.mp hci with hnew | hold
    · rcases hnames ci hnew with ⟨x', hx', hname'⟩ | ⟨k, s', haux⟩
      · have hxx : x = x' := Core.keyOf_inj htwf (hname.symm.trans hname')
        rw [hxx]
        exact Or.inr hx'
      · exact absurd (hname.symm.trans haux) (keyOf_nonAux t x k s')
    · exact Or.inl ⟨ci, hold, hname⟩
  have hprov : ∀ ci ∈ (claimedEnv ⟨new ++ s.consts⟩).consts,
      (∃ tbl, ci = .projInfo tbl) ∨ PinnedBasis ci ∨
        ∃ a, KeptIn t (recordOf R₁) (fun y => (R₁).blobs.get? y) a ci := by
    intro ci hci
    obtain ⟨hmem, hkeep⟩ := List.mem_filter.mp hci
    rcases List.mem_append.mp hmem with hnew | hold
    · rcases hnames ci hnew with ⟨x, hx, hname⟩ | haux
      · exact Or.inr (Or.inr ⟨x, hkept x hx ci hnew hname⟩)
      · exact Or.inl (projInfo_of_aux haux (by simpa using hkeep))
    · exact hI.prov ci (List.mem_filter.mpr ⟨hold, hkeep⟩)
  have hops' : ∀ n ∈ RoleOps.opNames,
      (⟨new ++ s.consts⟩ : Ix.Kernel.Env .anon).find? n = env.find? n := by
    intro n hn
    rw [← hI.ops n hn]
    have hnm : n ∉ new.map (·.name) := by
      intro hm
      obtain ⟨ci, hci, hname⟩ := List.mem_map.mp hm
      exact hops ci hci (hname ▸ hn)
    exact Ix.Kernel.Semantics.find?_append_of_not_mem hnm
  have hfamInst : ∀ B rb crb, (famOf₀ B = some rb ∨ famOf B = some rb) →
      recordOf R₁ rb = some crb →
      (∀ x, ConstAddrOf rb crb x → StoredAt t ⟨new ++ s.consts⟩ x) →
      FamilyInstalled t ⟨new ++ s.consts⟩ rb crb := by
    intro B0 rb0 crb0 hor hcrb0 hall
    by_cases hA0 : famOf A = some rb0
    · exact hinst rb0 crb0 hA0 hcrb0
    · have hall_s : ∀ x, ConstAddrOf rb0 crb0 x → StoredAt t s x := by
        intro x hx
        rcases hframe x (hall x hx) with h | hown
        · exact h
        · exfalso
          obtain ⟨c, hc, hxc | ⟨rb, crb, hfa, hcrb, hxr⟩⟩ := hown
          · have e : rb0 = A := constAddr_same hC.closed hcrb0 hc hx hxc
            subst e
            rcases hor with h₀ | h₁
            · obtain ⟨cb, ms, crb', rs, flat, hF⟩ := hC.fams.family B0 rb0 h₀
              have hR := hF.record.record
              rw [hA.1.2] at hR
              cases hR
            · exact hA.2.1 B0 h₁
          · have e : rb0 = rb := constAddr_same hC.closed hcrb0 hcrb hx hxr
            subst e
            exact hA0 hfa
      exact familyInstalled_mono hext hnd' (hI.famInst B0 rb0 crb0 hor hcrb0 hall_s)
  have hfamRecs : ∀ B rb cb crb, (famOf₀ B = some rb ∨ famOf B = some rb) →
      recordOf R₁ B = some cb → recordOf R₁ rb = some crb →
      (∀ x, ConstAddrOf rb crb x → StoredAt t ⟨new ++ s.consts⟩ x) →
      StoredFamilyRecs t R₁ ⟨new ++ s.consts⟩ B cb rb crb := by
    intro B0 rb0 cb0 crb0 hor hcb0 hcrb0 hall
    by_cases hA0 : famOf A = some rb0
    · have hB0A : B0 = A := by
        rcases hor with h₀ | h₁
        · exfalso
          obtain ⟨cb, ms, crb', rs, flat, hF⟩ := hC.fams.family B0 rb0 h₀
          obtain ⟨cb', crb'', ms', rs', _, _, _, _, _, hnrb, _⟩ := fam_new hC hA0
          have hR := hF.record.record
          rw [hnrb.2] at hR
          cases hR
        · exact fam_inj hC h₁ hA0
      subst hB0A
      exact hrecs cb0 rb0 crb0 hA0 hcb0 hcrb0
    · have hall_s : ∀ x, ConstAddrOf rb0 crb0 x → StoredAt t s x := by
        intro x hx
        rcases hframe x (hall x hx) with h | hown
        · exact h
        · exfalso
          obtain ⟨c, hc, hxc | ⟨rb, crb, hfa, hcrb, hxr⟩⟩ := hown
          · have e : rb0 = A := constAddr_same hC.closed hcrb0 hc hx hxc
            subst e
            rcases hor with h₀ | h₁
            · obtain ⟨cb, ms, crb', rs, flat, hF⟩ := hC.fams.family B0 rb0 h₀
              have hR := hF.record.record
              rw [hA.1.2] at hR
              cases hR
            · exact hA.2.1 B0 h₁
          · have e : rb0 = rb := constAddr_same hC.closed hcrb0 hcrb hx hxr
            subst e
            exact hA0 hfa
      exact (hI.famRecs B0 rb0 cb0 crb0 hor hcb0 hcrb0 hall_s).mono_env hext hnd'
  refine ⟨⟨new ++ s.consts⟩, ⟨hnd', ⟨Reg', hcl⟩, hprov, hops', hfamInst, hfamRecs⟩, hext, ?_, ?_,
    hframe⟩
  · intro x hx
    obtain ⟨ci, hci, hname, -⟩ := hreads₁ x hx
    exact ⟨ci, List.mem_append_left _ hci, hname⟩
  · intro x hx
    obtain ⟨ci, hci, hname, hr⟩ := hreads₁ x hx
    exact ⟨ci, List.mem_append_left _ hci, hname, hr⟩

/-- A unit's record is a definition, a recursor or a block. -/
theorem closureUnit_kind
    (hC : ClosureCtx.{u} L calls ρ t g R R' R₁ env famOf₀ famOf adv cont bAddr)
    {A : _root_.Address} {c : Ixon.Constant} (hA : IsClosureUnit R R₁ famOf A)
    (hc : recordOf R₁ A = some c) (hfa : famOf A = none) :
    UnitKind c ∧ ∃ x, ConstAddrOf A c x := by
  obtain ⟨hnA, -, x₀, hx₀⟩ := hA
  have hx : ConstAddrOf A c x₀ := (famOwns_none hfa hc x₀).mp hx₀
  refine ⟨?_, x₀, hx⟩
  rcases kind_cases c with hs | hp | hb
  · rcases hs with hd | hr | hax | hq
    · exact Or.inl hd
    · exact Or.inr (Or.inl hr)
    · exact (new₁_not_axiomLike hC.admits hnA hc (Or.inl hax)).elim
    · exact (new₁_not_axiomLike hC.admits hnA hc (Or.inr hq)).elim
  · exfalso
    rcases hx with ⟨-, hs⟩ | ⟨ms, -, -, hms, -, -⟩
    · exact standalone_not_proj hs hp
    · exact proj_not_block hp ⟨ms, hms⟩
  · exact Or.inr (Or.inr hb)

/-- **The steps of the closure fold** (module docstring). -/
theorem closureFold_steps
    (hC : ClosureCtx.{u} L calls ρ t g R R' R₁ env famOf₀ famOf adv cont bAddr)
    (htwf : t.wf = true) (hunit : ClosureUnitSteps.{u} L calls ρ t g)
    (hfam : ClosureFamilySteps.{u} L calls ρ t g) (htwin : ClosureTwinSteps.{u} L calls ρ t g)
    {us : List _root_.Address} (hus : ∀ A, A ∈ us ↔ IsClosureUnit R R₁ famOf A) :
    (closureFold.{u} L t g ρ.E₀ R₁ env famOf₀ famOf adv (ρ.rank g)).Steps env us := by
  intro s A hAu hinv hext hneed hfr
  have hA := (hus A).mp hAu
  have hI : ClosureFoldInv.{u} L t g R₁ env famOf₀ famOf s := hinv
  have hextT : ∀ ci ∈ env.consts, ci ∈ s.consts := hext
  have hneed' : ∀ x, ClosureFoldNeeds ρ.E₀ R₁ famOf₀ famOf adv (ρ.rank g) A x →
      StoredAt t s x ∨ FamOwns R₁ famOf A x := hneed
  have hfr' : ∀ x, FamOwns R₁ famOf A x → ¬ StoredAt t s x := hfr
  obtain ⟨Reg, hReg⟩ := hI.clause
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hA.1.1
  have hnA' : New R R' A := (new_of_closureStore hA.1).1
  have hrefs : ∀ x, UsedRef ρ.E₀ A x →
      (s.find? (keyOf t x)).isSome = true ∨ FamOwns R₁ famOf A x ∨ ¬ NeedOk ρ.E₀ x := by
    intro x hused
    by_cases hok : NeedOk ρ.E₀ x
    · rcases hneed' x (Or.inl (Or.inl ⟨hused, hok⟩)) with hs | ho
      · exact Or.inl (find_isSome_of_storedAt hs)
      · exact Or.inr (Or.inl ho)
    · exact Or.inr (Or.inr hok)
  cases hfa : famOf A with
  | some rb =>
    obtain ⟨cb, crb, ms, rs, hcb, hcrb, -, -, -, hnrb, hrk⟩ := fam_new hC hfa
    have e : cb = c := rec_eq hcb hc
    subst e
    have hown : ∀ x, FamOwns R₁ famOf A x ↔ FamAddr A cb rb crb x := famOwns_some hfa hcb hcrb
    have step := hfam R R' R₁ env s famOf₀ famOf adv cont bAddr A rb cb crb hC hextT hI.nodup
      hA.1 hcb hA.2.1 hfa hcrb (fun x hx => hfr' x ((hown x).mpr hx))
    have hrefsF : ∀ x, UsedRef ρ.E₀ A x ∨ UsedRef ρ.E₀ rb x →
        (s.find? (keyOf t x)).isSome = true ∨ FamAddr A cb rb crb x ∨ ¬ NeedOk ρ.E₀ x := by
      intro x hu
      by_cases hok : NeedOk ρ.E₀ x
      · have hn : ClosureFoldNeeds ρ.E₀ R₁ famOf₀ famOf adv (ρ.rank g) A x := by
          refine Or.inl ?_
          rcases hu with h | h
          · exact Or.inl ⟨h, hok⟩
          · exact Or.inr (Or.inl ⟨rb, hfa, h, hok⟩)
        rcases hneed' x hn with hs | ho
        · exact Or.inl (find_isSome_of_storedAt hs)
        · exact Or.inr (Or.inl ((hown x).mp ho))
      · exact Or.inr (Or.inr hok)
    have hadvA : ∀ a, adv A a → ∀ ca, recordOf ρ.E₀ a = some ca → ∀ x, ConstAddrOf a ca x →
        (s.find? (keyOf t x)).isSome = true := by
      intro a ha ca hca x hx
      rcases hneed' x (Or.inl (Or.inr (Or.inr (Or.inl ⟨rb, a, ca, hfa, ha, hca, hx⟩)))) with
        hs | ho
      · exact find_isSome_of_storedAt hs
      · exfalso
        obtain ⟨haR', hadvRk⟩ := hC.famAdmits.advice A rb a hfa hnA' ha
        have hnua := hC.run.advNotUnit A rb a hfa ha
        obtain ⟨ca', hca'⟩ := Option.isSome_iff_exists.mp haR'
        have e : ca' = ca := rec_eq (rec₂₀ hC.admits hca') hca
        subst e
        have hca₁ : recordOf R₁ a = some ca' := by
          rw [recordOf_closureStore hnua]
          exact hca'
        rcases (hown x).mp ho with hxA | hxr
        · have e : a = A := constAddr_same hC.closed hca₁ hcb hx hxA
          subst e
          exact Nat.lt_irrefl _ (hadvRk hnA')
        · have e : a = rb := constAddr_same hC.closed hca₁ hcrb hx hxr
          subst e
          exact Nat.lt_asymm hrk (hadvRk (new_of_closureStore hnrb).1)
    have hadvU : ∀ a, adv A a → ∀ x, UsedRef ρ.E₀ a x →
        (s.find? (keyOf t x)).isSome = true ∨ FamAddr A cb rb crb x ∨ ¬ NeedOk ρ.E₀ x := by
      intro a ha x hused
      by_cases hok : NeedOk ρ.E₀ x
      · rcases hneed' x (Or.inl (Or.inr (Or.inr (Or.inr ⟨rb, a, hfa, ha, hused, hok⟩)))) with
          hs | ho
        · exact Or.inl (find_isSome_of_storedAt hs)
        · exact Or.inr (Or.inl ((hown x).mp ho))
      · exact Or.inr (Or.inr hok)
    obtain ⟨new, Reg', hnd, hfresh, hcl, hops, hreads, hinst, hrecs, hnames⟩ :=
      step s Reg (fun ci h => h) hI.nodup hReg hrefsF hadvA hadvU
        (fun x hx => find_none_of_not_storedAt (hfr' x ((hown x).mpr hx)))
    exact closure_finish hC htwf hI hA new Reg' hnd hfresh hcl hops
      (fun x hx => hreads x ((hown x).mp hx))
      (fun ci hci => (hnames ci hci).imp
        (fun ⟨x, hx, hn⟩ => ⟨x, (hown x).mpr hx, hn⟩) id)
      (fun rb' crb' hfa' hcrb' => by
        rw [hfa] at hfa'
        have e1 : rb = rb' := Option.some.inj hfa'
        subst e1
        have e2 : crb = crb' := rec_eq hcrb hcrb'
        subst e2
        exact hinst)
      (fun cb' rb' crb' hfa' hcb' hcrb' => by
        rw [hfa] at hfa'
        have e1 : rb = rb' := Option.some.inj hfa'
        subst e1
        have e2 : cb = cb' := rec_eq hcb hcb'
        subst e2
        have e3 : crb = crb' := rec_eq hcrb hcrb'
        subst e3
        exact hrecs)
  | none =>
    have hown : ∀ x, FamOwns R₁ famOf A x ↔ ConstAddrOf A c x := famOwns_none hfa hc
    have hrefs' : ∀ x, UsedRef ρ.E₀ A x →
        (s.find? (keyOf t x)).isSome = true ∨ ConstAddrOf A c x ∨ ¬ NeedOk ρ.E₀ x :=
      fun x h => (hrefs x h).imp id (Or.imp (fun ho => (hown x).mp ho) id)
    have hfresh₀ : ∀ x, ConstAddrOf A c x → s.find? (keyOf t x) = none :=
      fun x hx => find_none_of_not_storedAt (hfr' x ((hown x).mpr hx))
    have hfreshS : ∀ x, ConstAddrOf A c x → ¬ StoredAt t s x :=
      fun x hx => hfr' x ((hown x).mpr hx)
    have hstepped : ∃ (new : List (ConstantInfo .anon)) (Reg' : NativeFam .anon → Prop),
        (new.map (·.name)).Nodup ∧ (∀ ci ∈ new, s.find? ci.name = none) ∧
        (∀ E, RecordsFor R₁ E → ∀ lim, Carried lim → LimWithin (· < g) t lim →
          FoldClauseWith.{u} L t E lim ⟨new ++ s.consts⟩ Reg') ∧
        (∀ ci ∈ new, ci.name ∉ RoleOps.opNames) ∧
        (∀ x, ConstAddrOf A c x →
          ∃ ci ∈ new, ∃ ci₀, ci.name = keyOf t x ∧ Reads t ρ.E₀ x ci₀ ∧ StoredAs ci ci₀) ∧
        ∀ ci ∈ new, (∃ x, ConstAddrOf A c x ∧ ci.name = keyOf t x) ∨
          ∃ k s, ci.name = .aux k s := by
      by_cases htw : IsTwinShape c
      · obtain ⟨B, rb, crb, hcrb, hor, hst⟩ :=
          htwin R R' R₁ env famOf₀ famOf adv cont bAddr A c hC hA.1 hc htw hfa hA.2.1
        have hallRb : ∀ x, ConstAddrOf rb crb x → StoredAt t s x := by
          intro x hx
          rcases hneed' x (Or.inr ⟨B, rb, crb, hcrb, hor, hx⟩) with hs | ho
          · exact hs
          · exfalso
            have hxA := (hown x).mp ho
            have e : rb = A := constAddr_same hC.closed hcrb hc hx hxA
            subst e
            rcases hor with h₀ | ⟨h₁, -⟩
            · obtain ⟨cb, ms, crb', rs, flat, hF⟩ := hC.fams.family B rb h₀
              have hR := hF.record.record
              rw [hA.1.2] at hR
              cases hR
            · exact hA.2.1 B h₁
        have hinstT : FamilyInstalled t s rb crb :=
          hI.famInst B rb crb (hor.imp id (fun h => h.1)) hcrb hallRb
        have hfamB : ∃ cbB msB rsB,
            recordOf R₁ B = some cbB ∧ cbB.info = .muts msB ∧
            FamRecRecord ρ.E₀ rb crb rsB := by
          rcases hor with h₀ | ⟨h₁, -⟩
          · obtain ⟨cbB, msB, crbB, rsB, -, hFB⟩ := hC.fams.family B rb h₀
            have hcbB₁ : recordOf R₁ B = some cbB :=
              recordOf_closureStore_of_R hC.admits hFB.block.record
            have hcrbB₁ : recordOf R₁ rb = some crbB :=
              recordOf_closureStore_of_R hC.admits hFB.record.record
            have ecrb : crbB = crb := rec_eq hcrbB₁ hcrb
            subst ecrb
            exact ⟨cbB, msB, rsB, hcbB₁, hFB.block.muts,
              ⟨rec₂₀ hC.admits (rec₁₂ hcrb), hFB.record.muts, hFB.record.recrs, hFB.record.logic,
                fun i m hm => rec₂₀ hC.admits (rec₁₂
                  (recordOf_closureStore_of_R hC.admits (hFB.record.members i m hm)))⟩⟩
          · obtain ⟨cbB, msB, crbB, rsB, -, hFB⟩ := hC.checks.family B rb h₁
            obtain ⟨cb₁, crb₁, _, _, hcb₁, hcrb₁, -, -, -, -, -⟩ := fam_new hC h₁
            have ecb : cb₁ = cbB := rec_eq (rec₂₀ hC.admits (rec₁₂ hcb₁)) hFB.block.record
            have ecrb₁ : crb₁ = crb := rec_eq hcrb₁ hcrb
            have ecrbB : crbB = crb := rec_eq hFB.record.record (rec₂₀ hC.admits (rec₁₂ hcrb))
            subst ecb ecrb₁ ecrbB
            exact ⟨cb₁, msB, rsB, hcb₁, hFB.block.muts, hFB.record⟩
        have hstoredRb : ∀ x, ConstAddrOf rb crb x →
            ∃ ci ci₀, s.find? (keyOf t x) = some ci ∧ Reads t ρ.E₀ x ci₀ ∧ StoredAs ci ci₀ := by
          obtain ⟨cbB, msB, rsB, hcbB, hmsB, hRB⟩ := hfamB
          have hFR := hI.famRecs B rb cbB crb (hor.imp id (fun h => h.1)) hcbB hcrb hallRb
          intro x hx
          rcases hx with ⟨-, hs⟩ | ⟨ms, k, m, hms, hm, hxm⟩
          · exact (standalone_not_block hs ⟨rsB, hRB.muts⟩).elim
          · rw [hRB.muts] at hms
            have ems : rsB = ms := Ixon.ConstantInfo.muts.inj hms
            subst ems
            have hm' : rsB.toList[k]? = some m := by simpa only [Array.getElem?_toList] using hm
            obtain ⟨rc, hrc⟩ := hRB.recrs m (List.mem_of_getElem? hm')
            subst hrc
            rcases hxm with rfl | ⟨ind, j, hind, -, -⟩
            · obtain ⟨cv, mI, rP, rules₀, cv', rules', hku, hRR, hf, -, -, hSA, -⟩ :=
                hFR.member msB rsB k rc hmsB hRB.muts hm
              have hk_toNat : k.toUInt64.toNat = k := UInt64.toNat_ofNat' hku
              have hRR₀ : RecReads t (recordOf ρ.E₀) (fun y => ρ.E₀.blobs.get? y) crb
                  (blockSelf t rb rsB) (keyOf t (memberAddr rb k (.recr rc))) rc
                  (.recInfo cv mI rP rules₀) :=
                ReaderReads.recReads_mono (fun a c h => rec₂₀ hC.admits (rec₁₂ h))
                  (fun y b h => hC.admits.loadedBlobs y b ((closureStore_spec hC.admits).le₂.2 y b h))
                  hRR
              refine ⟨.recInfo cv' mI rP rules', .recInfo cv mI rP rules₀, hf, ?_, hSA⟩
              refine ⟨memberProjection rb k (.recr rc), hRB.members k (.recr rc) hm,
                crb, rsB, rc, ⟨hRB.record, hRB.muts, ?_, ?_, ?_, hRB.logic⟩, hRR₀⟩
              · rw [hk_toNat]; exact hm
              · rw [hk_toNat]
              · rw [hk_toNat]
            · cases hind
        exact hst s hextT hI.nodup hfreshS s Reg (fun ci h => h) hI.nodup hReg hrefs' hinstT
          hstoredRb hfresh₀
      · obtain ⟨hk, hca⟩ := closureUnit_kind hC hA hc hfa
        exact hunit R R' R₁ env s famOf₀ famOf adv cont bAddr A c hC hextT hI.nodup hA.1 hc hk
          hca hfa hA.2.1 htw hfreshS s Reg (fun ci h => h) hI.nodup hReg hrefs' hfresh₀
    obtain ⟨new, Reg', hnd, hfresh, hcl, hops, hreads, hnames⟩ := hstepped
    exact closure_finish hC htwf hI hA new Reg' hnd hfresh hcl hops
      (fun x hx => hreads x ((hown x).mp hx))
      (fun ci hci => (hnames ci hci).imp
        (fun ⟨x, hx, hn⟩ => ⟨x, (hown x).mpr hx, hn⟩) id)
      (fun rb crb hfa' => by
        rw [hfa] at hfa'
        cases hfa')
      (fun cb rb crb hfa' => by
        rw [hfa] at hfa'
        cases hfa')

/-- **A record store for the closure's store is one for `R`.** -/
theorem recordsFor_R_of_closureStore (hadm : Admits ρ t g R R') {E : Ixon.Env}
    (hE : RecordsFor R₁ E) : RecordsFor R E :=
  ⟨hE.1, fun a c h => hE.2.1 a c (recordOf_closureStore_of_R hadm h),
    fun x b h => hE.2.2.1 x b ((closureStore_spec hadm).le₁.2 x b h), hE.2.2.2⟩

/-- **The fold's invariant at the witness's environment.** -/
theorem closureFold_start
    (hC : ClosureCtx.{u} L calls ρ t g R R' R₁ env famOf₀ famOf adv cont bAddr)
    (htwf : t.wf = true) : ClosureFoldInv.{u} L t g R₁ env famOf₀ famOf env := by
  obtain ⟨Reg, hR⟩ := hC.bnd.clause
  refine ⟨hC.bnd.shape.reading.nodup,
    ⟨Reg, fun E hE lim hc hl => hR E (recordsFor_R_of_closureStore hC.admits hE) lim hc hl⟩,
    fun ci hci => ?_, fun _ _ => rfl, fun B rb crb hor hcrb hall => ?_,
    fun B rb cb crb hor hcb hcrb hall => ?_⟩
  · rcases hC.bnd.shape.reading.provenance ci hci with h | h | ⟨a, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨a, keptIn_closureStore hC.admits h⟩)
  · rcases hor with h₀ | h₁
    · obtain ⟨cb, ms, crb', rs, flat, hF⟩ := hC.fams.family B rb h₀
      have e : crb' = crb :=
        rec_eq (recordOf_closureStore_of_R hC.admits hF.record.record) hcrb
      subst e
      exact (hC.fams.installed B rb crb' h₀ hF.record.record).2
    · intro x hx
      exfalso
      obtain ⟨cb, crb', ms, rs, hcb, hcrb', -, -, hnB, -, -⟩ := fam_new hC h₁
      have e : crb' = crb := rec_eq hcrb' hcrb
      subst e
      exact owned_not_stored hC htwf ⟨hnB, fam_unclaimed hC h₁, x, cb, hcb,
        Or.inr ⟨rb, crb', h₁, hcrb', hx⟩⟩ ⟨cb, hcb, Or.inr ⟨rb, crb', h₁, hcrb', hx⟩⟩ (hall x hx)
  · rcases hor with h₀ | h₁
    · obtain ⟨cb', ms, crb', rs, flat, hF⟩ := hC.fams.family B rb h₀
      have e1 : cb' = cb :=
        rec_eq (recordOf_closureStore_of_R hC.admits hF.block.record) hcb
      have e2 : crb' = crb :=
        rec_eq (recordOf_closureStore_of_R hC.admits hF.record.record) hcrb
      subst e1 e2
      exact (hC.fams.recs B rb cb' crb' h₀ hF.block.record hF.record.record).mono
        (fun a c hac => recordOf_closureStore_of_R hC.admits hac)
        (closureStore_spec hC.admits).le₁.2 (fun h => h)
    · refine ⟨fun ms' rs' k rc _ hrs' hk => ?_⟩
      exfalso
      obtain ⟨cb', crb', ms, rs, hcb', hcrb', -, -, hnB, -, -⟩ := fam_new hC h₁
      have e : crb' = crb := rec_eq hcrb' hcrb
      subst e
      have hx : ConstAddrOf rb crb' (memberAddr rb k (.recr rc)) :=
        Or.inr ⟨rs', k, .recr rc, hrs', hk, Or.inl rfl⟩
      exact owned_not_stored hC htwf ⟨hnB, fam_unclaimed hC h₁, _, cb', hcb',
        Or.inr ⟨rb, crb', h₁, hcrb', hx⟩⟩ ⟨cb', hcb', Or.inr ⟨rb, crb', h₁, hcrb', hx⟩⟩ (hall _ hx)

/-- **The closure fold's result** (module docstring). -/
theorem closureFold_run
    (hC : ClosureCtx.{u} L calls ρ t g R R' R₁ env famOf₀ famOf adv cont bAddr)
    (htwf : t.wf = true) (hunit : ClosureUnitSteps.{u} L calls ρ t g)
    (hfam : ClosureFamilySteps.{u} L calls ρ t g) (htwin : ClosureTwinSteps.{u} L calls ρ t g) :
    ∃ env₁ : Ix.Kernel.Env .anon, ClosureFoldInv.{u} L t g R₁ env famOf₀ famOf env₁ ∧
      (∀ ci ∈ env.consts, ci ∈ env₁.consts) ∧
      (∀ A, IsClosureUnit R R₁ famOf A → ∀ x, FamOwns R₁ famOf A x →
        ∃ ci ∈ env₁.consts, ci.name = keyOf t x ∧ ∃ ci₀, Reads t R₁ x ci₀ ∧ StoredAs ci ci₀) ∧
      ∀ x, StoredAt t env₁ x → StoredAt t env x ∨
        ∃ A, IsClosureUnit R R₁ famOf A ∧ FamOwns R₁ famOf A x := by
  obtain ⟨us, hus⟩ := exists_list_of_records R₁ (IsClosureUnit R R₁ famOf)
    (fun A hA => Option.isSome_iff_exists.mp hA.1.1)
  obtain ⟨s, hinv, hext, hdone, hframe⟩ :=
    (closureFold.{u} L t g ρ.E₀ R₁ env famOf₀ famOf adv (ρ.rank g)).run
      (closureFold_start hC htwf)
      (fun a ha b hb x hx hx' => closureUnits_apart hC ((hus a).mp ha) ((hus b).mp hb) hx hx')
      (fun a ha x hx => owned_not_stored hC htwf ((hus a).mp ha) hx)
      (closureFold_needsEarlier hC hus)
      (closureFold_steps hC htwf hunit hfam htwin hus)
  refine ⟨s, hinv, hext, fun A hA x hx => (hdone A ((hus A).mpr hA)).2 x hx, fun x hx => ?_⟩
  rcases hframe x hx with h | ⟨A, hAu, hown⟩
  · exact Or.inl h
  · exact Or.inr ⟨A, (hus A).mp hAu, hown⟩

end Steps

end IxVM.Refinement.Binding
