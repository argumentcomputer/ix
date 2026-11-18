import IxVMRefinement.TwinFamily.Keeps

/-! # The twin's unit step from its target

`TwinStepTarget` gives, for the second family record of a block, IxC's twin record at the
positional package and each member stored as a constant that stores its reading. This module
turns it into the twin's unit step over the family graph (`UnitStepTwin`) at the clause
`X ∧ FamilyRecsModeled`:

* `twinRun_parts`: what the twin record says of the constants it adds: the twin recursors under
  the block's names, then model copies at derived keys, all fresh and with distinct names;
* `TwinStepKeeps`: the keeping of the prefix invariant and of `X` across the twin record, with
  what the step is handed (the statement the clause's keeping lemmas prove);
* `unitStepTwin_of_target`: the twin's unit step from the target, the run facts the target
  takes, and the keeping. The block's family record is installed by the clause
  (`familyInstalled_of_clause`); the clause is kept because every new constant at the key of an
  address is a twin recursor, which the target gives a model companion. -/

universe u

namespace IxVM.Refinement.Typing.TwinFamily

open IxVM.Consistency
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open IxVM.Refinement.Decl (twinPosRulesJ)
open IxVM.Refinement.Typing.FamilyAlias (FamilyCallAtLim)
open Ix.Kernel (ConstantInfo)
open Ix.Kernel.Semantics (Judgements DeclRecTwinRunJ TwinRecPart twinModels twinRecs)
open Ix.Kernel.Model (HasModel)

set_option linter.unusedVariables false

/-- **The constants a twin record adds**: the twin recursors, one under the name of each member
of the block, then model copies, definitions at the model keys of twin recursors; fresh in the
prefix, with distinct names. -/
theorem twinRun_parts {J : Judgements .anon} {env env₂ : Ix.Kernel.Env .anon}
    {blk : List (ConstantInfo .anon)} (hrun : DeclRecTwinRunJ J env blk env₂) :
    ∃ ws : List (TwinRecPart .anon),
      env₂ = ⟨(twinRecs ws ++ twinModels ws) ++ env.consts⟩ ∧
      ((twinRecs ws ++ twinModels ws).map (·.name)).Nodup ∧
      (∀ ci ∈ twinRecs ws ++ twinModels ws, env.find? ci.name = none) ∧
      (twinRecs ws).map (·.name) = blk.map (·.name) ∧
      (∀ ci ∈ twinRecs ws, ∃ cv mI rP rules, ci = .recInfo cv mI rP rules) ∧
      ∀ ci ∈ twinModels ws, ∃ ci' ∈ twinRecs ws, ci.name = Ix.Kernel.auxKey ci'.name .model ∧
        ∃ cv v hint, ci = .defnInfo cv v hint := by
  obtain ⟨ws, f, -, hblk, henv, hnd, hfr, -, hall⟩ := hrun
  refine ⟨ws, ?_, hnd, hfr, ?_, ?_, ?_⟩
  · rw [henv]
    exact congrArg Ix.Kernel.Env.mk (List.append_assoc _ _ _).symm
  · rw [hblk]
    simp only [twinRecs, List.map_map]
    refine List.map_congr_left (fun w hw => ?_)
    exact (hall w hw).1.name_eq
  · intro ci hci
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hci
    exact ⟨_, _, _, _, rfl⟩
  · intro ci hc
    obtain ⟨w, hw, hmi⟩ := List.mem_filterMap.mp hc
    unfold TwinRecPart.modelInfo? at hmi
    obtain ⟨⟨cvm, mval, hint⟩, -, rfl⟩ := Option.map_eq_some_iff.mp hmi
    refine ⟨.recInfo w.cvW' w.mI w.rP w.rulesW', List.mem_map.mpr ⟨w, hw, rfl⟩, ?_,
      _, _, _, rfl⟩
    show Ix.Kernel.auxKey w.cvW.name .model = Ix.Kernel.auxKey w.cvW'.name .model
    rw [(hall w hw).1.name_eq]

/-- **The keeping the twin's step needs**: across a twin record of the second record `A` (as
the target gives it: the record's declaration as read, IxC's record at the positional package,
each member stored as its reading with a model companion), from an environment the twin's step
is handed, the prefix invariant and the clause `X` are kept. -/
def TwinStepKeeps (X : Ix.Kernel.Env .anon → Prop) (t : Ix.Kernel.RoleTable)
    (envT : Ix.Kernel.Env .anon) (E₀ E : Ixon.Env) (lim : Option Nat) (A : _root_.Address)
    (c : Ixon.Constant) : Prop :=
  ∀ (env env₂ : Ix.Kernel.Env .anon) (blk : List (ConstantInfo .anon)),
    (∀ ci ∈ envT.consts, ci ∈ env.consts) → (env.consts.map (·.name)).Nodup →
    Decl.PrefixInv.{u} E t lim env → X env →
    (∀ x, UsedRef E₀ A x →
      (env.find? (keyOf t x)).isSome = true ∨ ConstAddrOf A c x ∨ ¬ NeedOk E₀ x) →
    (∀ x, ConstAddrOf A c x → env.find? (keyOf t x) = none) →
    TwinDeclReads t E₀ A c blk →
    DeclRecTwinRunJ twinPosRulesJ env blk env₂ →
    (∀ ci ∈ blk, ∃ c', env₂.find? ci.name = some c' ∧ StoredAs c' ci) →
    (∀ ci ∈ blk, HasModel env₂ ci.name) →
    Decl.CoreCompanions ⟨E, env₂, t, lim⟩ →
    Decl.PrefixInv.{u} E t lim env₂ ∧ X env₂


/-- **The twin's unit step from its target, at a clause that gives the block's family record
installed**: from the target, the run facts it takes, the family record installed at every
environment the step is handed (`hinst`: wherever it comes from), and the keeping of the
clause. -/
theorem unitStepTwin_of_installed (hT : TwinStepTarget.{u}) {X : Ix.Kernel.Env .anon → Prop}
    {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
    {envT : Ix.Kernel.Env .anon} {E₀ E : Ixon.Env} {lim : Option Nat} {A B rb : _root_.Address}
    {c cb crb : Ixon.Constant} {ms rs' : Array Ixon.MutConst} {cs : List (Call F)}
    (ht : t.check = .ok ()) (hRS : LoadedReads.RunStore calls E₀)
    (hSS : StepStore calls t E₀ E) (hB : FamBlockRecord E₀ B cb ms)
    (hrbB : FamRecOfBlock calls bAddr t E₀ B rb crb lim)
    (hA : FamRecRecord E₀ A c rs') (hsz : rs'.size ≠ 0)
    (hne : A ≠ rb) (hcall : FamilyCallAtLim calls bAddr t B A lim cs)
    (hroute : ModeledRouteAt calls B)
    (hkey : ∀ x, ConstAddrOf A c x → Decl.KeyFree (keyOf t x))
    (hinst : ∀ env : Ix.Kernel.Env .anon, (∀ ci ∈ envT.consts, ci ∈ env.consts) →
      (env.consts.map (·.name)).Nodup → Decl.PrefixInv.{u} E t lim env → X env →
      (∀ x, ConstAddrOf rb crb x → (env.find? (keyOf t x)).isSome = true) →
      FamilyInstalled t env rb crb)
    (hkeep : TwinStepKeeps.{u} X t envT E₀ E lim A c) :
    UnitStepTwin.{u} X t envT E₀ E lim A c rb crb := by
  intro env hext hnd hinv hX href hrbS hfresh
  have hroles : (t.bound.toList.map (·.1)).Nodup := (Ix.Kernel.RoleTable.check_nodup ht).1
  obtain ⟨blk, env₂, hreads, hrun, hstored, hmodel, hcomp⟩ :=
    hT calls bAddr t E₀ E env B rb A cb crb c ms rs' lim cs ht hRS hSS hB hrbB hA hsz hne
      hcall hroute hinv href (hinst env hext hnd hinv hX hrbS) hfresh hkey
  obtain ⟨hinv₂, hX₂⟩ :=
    hkeep env env₂ blk hext hnd hinv hX href hfresh hreads hrun hstored hmodel hcomp
  obtain ⟨ws, henv, hnd₂, hfr₂, hnames, hrecs, hmods⟩ := twinRun_parts hrun
  subst henv
  have hrecName : ∀ ci ∈ twinRecs ws, ∃ ci₀ ∈ blk, ci₀.name = ci.name := by
    intro ci hci
    have hm : ci.name ∈ blk.map (·.name) := by
      rw [← hnames]
      exact List.mem_map.mpr ⟨ci, hci, rfl⟩
    obtain ⟨ci₀, hci₀, he⟩ := List.mem_map.mp hm
    exact ⟨ci₀, hci₀, he⟩
  refine ⟨twinRecs ws ++ twinModels ws, hnd₂, hfr₂, hinv₂, hX₂, ?_, ?_⟩
  · intro x hx
    obtain ⟨ci₀, hci₀, hn₀⟩ := hreads.2.2 x hx
    obtain ⟨x', hx', hn', hrd⟩ := hreads.2.1 ci₀ hci₀
    have hxx : x' = x := keyOf_inj hroles (hn'.symm.trans hn₀)
    rw [hxx] at hrd
    obtain ⟨c', hc', hsa⟩ := hstored ci₀ hci₀
    rcases find?_append_cases (twinRecs ws ++ twinModels ws) hc' with hm | hold
    · refine ⟨c', hm, ci₀, ?_, hrd, hsa⟩
      rw [Core.WhnfAux.name_of_find hc', hn₀]
    · rw [hn₀, hfresh x hx] at hold
      cases hold
  · intro ci hci
    rcases List.mem_append.mp hci with hr | hmo
    · obtain ⟨ci₀, hci₀, he⟩ := hrecName ci hr
      obtain ⟨x, hx, hn, -⟩ := hreads.2.1 ci₀ hci₀
      exact Or.inl ⟨x, hx, he.symm.trans hn⟩
    · obtain ⟨ci', -, hk, -⟩ := hmods ci hmo
      exact Or.inr ⟨ci'.name, .model, hk⟩

/-- **The clause that hands the twin its block's family record is kept across the twin
record**: every new constant at the key of an address is a twin recursor, which the target gives
a model companion. -/
theorem TwinStepKeeps.and_familyRecsModeled {X : Ix.Kernel.Env .anon → Prop}
    {t : Ix.Kernel.RoleTable} {envT : Ix.Kernel.Env .anon} {E₀ E : Ixon.Env} {lim : Option Nat}
    {A : _root_.Address} {c : Ixon.Constant} {fam : _root_.Address → Option _root_.Address}
    (h : TwinStepKeeps.{u} X t envT E₀ E lim A c) :
    TwinStepKeeps.{u} (fun env => X env ∧ FamilyRecsModeled t E₀ fam env) t envT E₀ E lim A c := by
  intro env env₂ blk hext hnd hinv hXe href hfresh hreads hrun hstored hmodel hcomp
  obtain ⟨hX, hfm⟩ := hXe
  obtain ⟨hinv₂, hX₂⟩ :=
    h env env₂ blk hext hnd hinv hX href hfresh hreads hrun hstored hmodel hcomp
  obtain ⟨ws, henv, hnd₂, hfr₂, hnames, hrecs, hmods⟩ := twinRun_parts hrun
  subst henv
  have hgrow : Ix.Kernel.Grows (fun k => env.find? k = none) env
      ⟨(twinRecs ws ++ twinModels ws) ++ env.consts⟩ :=
    ⟨_, rfl, fun ci hci => ⟨hfr₂ ci hci, hfr₂ ci hci⟩, hnd₂⟩
  have hfind : ∀ {k : Ix.Kernel.Key .anon} {c' : ConstantInfo .anon}, env.find? k = some c' →
      (⟨(twinRecs ws ++ twinModels ws) ++ env.consts⟩ : Ix.Kernel.Env .anon).find? k =
        some c' := by
    intro k c' hk
    rw [hgrow.find_eq (by show ¬ (env.find? k = none); rw [hk]; simp)]
    exact hk
  refine ⟨hinv₂, hX₂, FamilyRecsModeled.step hfm hfind ?_⟩
  intro B' rb' x crb' hrb' hcrb' hx hs hnone
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hs
  have hname : ci.name = keyOf t x := Core.WhnfAux.name_of_find hci
  rcases find?_append_cases (twinRecs ws ++ twinModels ws) hci with hm | hold
  · rcases List.mem_append.mp hm with hr | hmo
    · have hm' : ci.name ∈ blk.map (·.name) := by
        rw [← hnames]
        exact List.mem_map.mpr ⟨ci, hr, rfl⟩
      obtain ⟨ci₀, hci₀, he⟩ := List.mem_map.mp hm'
      obtain ⟨cv, mI, rP, rules, hci'⟩ := hrecs ci hr
      refine ⟨⟨cv, mI, rP, rules, hci.trans (congrArg some hci')⟩, ?_⟩
      have hm₀ := hmodel ci₀ hci₀
      rw [he, hname] at hm₀
      exact hm₀
    · obtain ⟨ci', -, hk, -⟩ := hmods ci hmo
      exact (keyOf_nonAux t x ci'.name .model (hname.symm.trans hk)).elim
  · rw [hnone] at hold
    cases hold

/-- **The twin's unit step from its target at the clause `X ∧ FamilyRecsModeled`**, for a block
whose family record this fold installed (`fam B = some rb`): the clause gives the family record
installed (`familyInstalled_of_clause`). -/
theorem unitStepTwin_of_target (hT : TwinStepTarget.{u}) {X : Ix.Kernel.Env .anon → Prop}
    {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
    {envT : Ix.Kernel.Env .anon} {E₀ E : Ixon.Env} {lim : Option Nat}
    {fam : _root_.Address → Option _root_.Address} {A B rb : _root_.Address}
    {c cb crb : Ixon.Constant} {ms rs' : Array Ixon.MutConst} {cs : List (Call F)}
    (ht : t.check = .ok ()) (hRS : LoadedReads.RunStore calls E₀)
    (hSS : StepStore calls t E₀ E) (hB : FamBlockRecord E₀ B cb ms)
    (hrbB : FamRecOfBlock calls bAddr t E₀ B rb crb lim)
    (hcrb : recordOf E₀ rb = some crb) (hA : FamRecRecord E₀ A c rs') (hsz : rs'.size ≠ 0)
    (hne : A ≠ rb) (hcall : FamilyCallAtLim calls bAddr t B A lim cs)
    (hroute : ModeledRouteAt calls B)
    (hkey : ∀ x, ConstAddrOf A c x → Decl.KeyFree (keyOf t x)) (hfam : fam B = some rb)
    (hkeep : TwinStepKeeps.{u} X t envT E₀ E lim A c) :
    UnitStepTwin.{u} (fun env => X env ∧ FamilyRecsModeled t E₀ fam env) t envT E₀ E lim A c
      rb crb :=
  unitStepTwin_of_installed hT ht hRS hSS hB hrbB hA hsz hne hcall hroute hkey
    (fun env _ _ _ hXe hrbS => familyInstalled_of_clause hXe.2 hfam hcrb hrbS)
    hkeep.and_familyRecsModeled

end IxVM.Refinement.Typing.TwinFamily
