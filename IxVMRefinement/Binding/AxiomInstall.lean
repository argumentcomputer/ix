import IxVMRefinement.Binding.OpRoleUnit

/-! # A standard axiom's group in the binding fold: the install of the axiom

The groups of `propext` and `Classical.choice` have one role each, a standard axiom, and it is a
role unit: it is installed after the group's closure. This file is that install, in the form of
the operations' (`OpInstall.roleOp_step`), and the role unit the composed residual takes as its
hypothesis `standardAxiomRoleUnit`.

* `roleAxiom_step`: **the axiom installed.** From the invariant below `g` at the closure's store
  `R₁` and environment `env₁` (which does not store the axiom's key), the axiom's declaration
  checked (`ConstantValRunJ`: its type elaborates to a sort), its stored type matching the
  kernel's pin (`ConstantVal.matchesPin` against `propextA` or `choiceA`), the reading of its
  record and the reload of the stored constant: the invariant before the raise past `g` at the
  store with the axiom's record and `env₁` with the axiom stored. The declaration step is the
  kernel's (`DeclAxiomRunJ`): `stdAxiomOk` holds at `env₁` because `Iff` (for `propext`) and
  `Nonempty` (for `choice`) are of earlier groups and stored as pinned (`Shapes.iff`,
  `Shapes.nonempty`). The clause is kept by `FoldClauseWith.consValue` (an axiom is a value
  constant).
* `roleAxiom_stored`: the same when `env₁` already stores the axiom's key. `AddsAt R₁ R' a`
  does not say that `R₁` lacks the record at `a`, and when `R₁` holds it, `env₁` stores the key
  as a reading of that record (`ReadingOf`); then `env₁` itself is the environment before the
  raise.
* `AxiomValidationFacts L calls`: what the run's validation of a standard axiom
  (`KernelRoles::validate_standard_axiom`) gives the step, at every binding run with its record
  stores (`RunStepStores`, the run predicate's `BindingRun.stepStores`).
* `standardAxiomRoleUnit_of_validation`, `standardAxiomRoleUnit`: the role unit of the standard
  axioms, from those facts.

The raise past an axiom's group needs nothing of the environment: neither axiom is a companion
role or a fabricated role, and their groups are not the last well-founded or literal group
(`raise_axiom`).
-/

universe u

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace IxVM.Refinement.Binding.AxiomInstall

open IxVM.Consistency
open IxVM.Refinement.Typing
open IxVM.Refinement.Binding
open IxVM.Refinement.Binding.OpInstall
open Aiur.Generic.SourceSemantics (Call)
open IxVM (F)
open Ix.Kernel.Semantics (NativeFam)

/-! ## The pinned signature and the environment after the axiom -/

/-- **The kernel's pinned signature of a standard axiom**: `propext`'s, else `choice`'s. -/
def stdAxiomPin (r : Ix.Kernel.Role) : Ix.Kernel.ConstantVal .anon :=
  if r = .propext then Ix.Kernel.propextA else Ix.Kernel.choiceA

/-- **The environment with the standard axiom `r` stored**, at its role key. -/
abbrev axInstalled (env : Ix.Kernel.Env .anon) (r : Ix.Kernel.Role)
    (lps : List Ix.Kernel.LevelParam) (ty : Core.KExpr) : Ix.Kernel.Env .anon :=
  ⟨.axiomInfo ⟨.role r, lps, ty⟩ :: env.consts⟩

/-! ## Decided facts about the two standard axioms -/

set_option maxRecDepth 100000 in
private theorem std_facts : ∀ r ∈ standardAxioms,
    Ix.SpecDigest.groupOf r ≠ 40 ∧ Ix.SpecDigest.groupOf r ≠ 45 ∧ r ∉ preludeRoles ∧
      r ∈ axiomRoles ∧ r ∉ companionRoles ∧
      (Ix.Kernel.Key.role r : Core.KKey) ∉ Ix.Kernel.Rules.natBinOpNames ∧
      Core.fabricatedRole r = false ∧ r ∉ RoleOps.opRoles := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- `Iff` is of a group before `propext`'s, `Nonempty` of one before `choice`'s. -/
private theorem std_order :
    Ix.SpecDigest.groupOf .iff < Ix.SpecDigest.groupOf .propext ∧
      Ix.SpecDigest.groupOf .nonempty < Ix.SpecDigest.groupOf .choice := by
  decide +kernel

theorem std_cases {r : Ix.Kernel.Role} (h : r ∈ standardAxioms) : r = .propext ∨ r = .choice := by
  simpa [standardAxioms] using h

/-! ## The shapes and the raise -/

/-- `stdAxiomOk` reads the environment at the keys of `Eq`, `Iff` and `Nonempty` and their
constructors and recursors only, none of them a standard axiom's. -/
theorem stdAxiomOk_congr_ax {env env' : Ix.Kernel.Env .anon} {r : Ix.Kernel.Role}
    (hr : r = .propext ∨ r = .choice)
    (h : ∀ X : Ix.Kernel.Role, X ≠ r →
      env'.find? (Ix.Kernel.Key.role X) = env.find? (Ix.Kernel.Key.role X))
    (cvA : Ix.Kernel.ConstantVal .anon) :
    Ix.Kernel.stdAxiomOk env' cvA = Ix.Kernel.stdAxiomOk env cvA := by
  have hne : ∀ X : Ix.Kernel.Role, X ∈ [Ix.Kernel.Role.eq, .iff, .iffIntro, .iffRec, .nonempty,
      .nonemptyIntro, .nonemptyRec] → X ≠ r := by
    intro X hX he
    subst he
    rcases hr with e | e <;> (rw [e] at hX; revert hX; decide)
  have h1 : env'.find? Ix.Kernel.eqName = env.find? Ix.Kernel.eqName := h .eq (hne _ (by decide))
  have h2 : env'.find? Ix.Kernel.iffName = env.find? Ix.Kernel.iffName :=
    h .iff (hne _ (by decide))
  have h3 : env'.find? Ix.Kernel.iffIntroName = env.find? Ix.Kernel.iffIntroName :=
    h .iffIntro (hne _ (by decide))
  have h4 : env'.find? Ix.Kernel.iffRecName = env.find? Ix.Kernel.iffRecName :=
    h .iffRec (hne _ (by decide))
  have h5 : env'.find? Ix.Kernel.nonemptyName = env.find? Ix.Kernel.nonemptyName :=
    h .nonempty (hne _ (by decide))
  have h6 : env'.find? Ix.Kernel.nonemptyIntroName = env.find? Ix.Kernel.nonemptyIntroName :=
    h .nonemptyIntro (hne _ (by decide))
  have h7 : env'.find? Ix.Kernel.nonemptyRecName = env.find? Ix.Kernel.nonemptyRecName :=
    h .nonemptyRec (hne _ (by decide))
  unfold Ix.Kernel.stdAxiomOk
  rw [h1, h2, h3, h4, h5, h6, h7]

/-- **The shapes on the groups below `g` give the shapes up to `g`** at an extension that agrees
at every role key but the axiom's: the group's one role is the axiom, which no shape reads. -/
theorem shapes_axiom {g : Nat} {r : Ix.Kernel.Role} {env env' : Ix.Kernel.Env .anon}
    (hgrp : roleGroup g = [r]) (hr : r = .propext ∨ r = .choice)
    (hext : Ix.Kernel.EnvExt env env')
    (hfr : ∀ X : Ix.Kernel.Role, X ≠ r →
      env'.find? (Ix.Kernel.Key.role X) = env.find? (Ix.Kernel.Key.role X))
    (hs : Shapes (· < g) env) : Shapes (· < g + 1) env' := by
  have hnot : ∀ X : Ix.Kernel.Role, X ≠ r → Ix.SpecDigest.groupOf X ≠ g := by
    intro X hX hg
    have hm : X ∈ roleGroup g := hg ▸ role_mem_roleGroup X
    rw [hgrp, List.mem_singleton] at hm
    exact hX hm
  have below : ∀ X : Ix.Kernel.Role, X ≠ r →
      Ix.SpecDigest.groupOf X < g + 1 → Ix.SpecDigest.groupOf X < g := by
    intro X hX hor
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hor) with h | h
    · exact h
    · exact absurd h (hnot X hX)
  have nr : ∀ X : Ix.Kernel.Role, X ∈ [Ix.Kernel.Role.bool, .char, .string, .list, .listNil,
      .listCons, .charOfNat, .stringOfList, .iff, .nonempty] → X ≠ r := by
    intro X hX he
    subst he
    rcases hr with e | e <;> (rw [e] at hX; revert hX; decide)
  exact {
    bool := fun h => by
      obtain ⟨h1, h2, h3⟩ := hs.bool (below .bool (nr _ (by decide)) h)
      exact ⟨h1.mono hext, h2.mono hext, h3.mono hext⟩
    char := fun h => by
      have e : env'.find? Ix.Kernel.charName = env.find? Ix.Kernel.charName :=
        hfr .char (nr _ (by decide))
      rw [e]
      exact hs.char (below .char (nr _ (by decide)) h)
    string := fun h => by
      have e : env'.find? Ix.Kernel.stringName = env.find? Ix.Kernel.stringName :=
        hfr .string (nr _ (by decide))
      rw [e]
      exact hs.string (below .string (nr _ (by decide)) h)
    list := fun h => by
      have e1 : env'.find? Ix.Kernel.listName = env.find? Ix.Kernel.listName :=
        hfr .list (nr _ (by decide))
      have e2 : env'.find? Ix.Kernel.listNilName = env.find? Ix.Kernel.listNilName :=
        hfr .listNil (nr _ (by decide))
      have e3 : env'.find? Ix.Kernel.listConsName = env.find? Ix.Kernel.listConsName :=
        hfr .listCons (nr _ (by decide))
      rw [e1, e2, e3]
      exact hs.list (below .list (nr _ (by decide)) h)
    charOfNat := fun h => by
      have e : env'.find? Ix.Kernel.charOfNatName = env.find? Ix.Kernel.charOfNatName :=
        hfr .charOfNat (nr _ (by decide))
      rw [e]
      exact hs.charOfNat (below .charOfNat (nr _ (by decide)) h)
    stringOfList := fun h => by
      have e : env'.find? Ix.Kernel.stringOfListName = env.find? Ix.Kernel.stringOfListName :=
        hfr .stringOfList (nr _ (by decide))
      rw [e]
      exact hs.stringOfList (below .stringOfList (nr _ (by decide)) h)
    iff := fun h cvA hn hm => by
      rw [stdAxiomOk_congr_ax hr hfr cvA]
      exact hs.iff (below .iff (nr _ (by decide)) h) cvA hn hm
    nonempty := fun h cvA hn hm => by
      rw [stdAxiomOk_congr_ax hr hfr cvA]
      exact hs.nonempty (below .nonempty (nr _ (by decide)) h) cvA hn hm }

/-- **The raise past a standard axiom's group needs nothing of the environment.** -/
theorem raise_axiom {t : Ix.Kernel.RoleTable} {env : Ix.Kernel.Env .anon} {g : Nat}
    {r : Ix.Kernel.Role} (hgrp : roleGroup g = [r]) (hstd : r ∈ standardAxioms) :
    RaiseAt t env g := by
  obtain ⟨h40, h45, -, -, hcomp, hbin, hfab, -⟩ := std_facts r hstd
  have hgr : Ix.SpecDigest.groupOf r = g :=
    groupOf_of_mem_roleGroup (by rw [hgrp]; exact List.mem_singleton.mpr rfl)
  exact {
    succ := fun _ r'' hr'' _ => by
      rw [hgrp, List.mem_singleton] at hr''
      subst hr''
      exact ⟨Or.inr (Or.inr ⟨hcomp, hbin⟩), fun h => by rw [hfab] at h; cases h⟩
    wf := fun h => absurd (hgr.trans h) h40
    literal := fun h => absurd (hgr.trans h) h45 }

/-- **A reading of `R'` at another address than the new record's is a reading of `R₁`**, the
new record being an axiom. -/
theorem reads_down_ax {t : Ix.Kernel.RoleTable} {R₁ R' : Ixon.Env} {a : _root_.Address}
    (hs : AddsAt R₁ R' a) (hsolo : ∃ c ax, recordOf R' a = some c ∧ c.info = .axio ax)
    {x : _root_.Address} (hx : x ≠ a) {ci₀ : Ix.Kernel.ConstantInfo .anon}
    (h : Reads t R' x ci₀) : Reads t R₁ x ci₀ := by
  obtain ⟨c₀, d₀, hc₀, hd₀⟩ := hsolo
  have hS : AgreeBut (recordOf R₁) (recordOf R') a := by
    refine ⟨fun y hy => recordOf_ne hs hy, fun c hc => ?_⟩
    rw [hc₀] at hc
    have hcc : c₀ = c := Option.some.inj hc
    rw [← hcc, hd₀]
    exact ⟨(fun ms e => nomatch e), (fun p e => nomatch e)⟩
  have h' := readsIn_back (blob := fun y => R'.blobs.get? y) hS hx h
  have hbl := blobs_eq hs
  unfold Reads
  rw [← hbl]
  exact h'

/-! ## The step -/

set_option maxHeartbeats 1600000 in
/-- **The standard axiom's group, after its closure and before the raise past it**: from the
invariant below `g` at the closure's store and environment, which does not store the axiom's
key, the axiom's declaration checked with its stored type matching the kernel's pin, the reading
of its record and the reload of the stored constant: the invariant before the raise past `g` at
the store with the axiom's record and the environment with the axiom stored. -/
theorem roleAxiom_step {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop} (hL : LinkLaws L)
    {ρ : BRun} {t : Ix.Kernel.RoleTable} {g : Nat} {R R₁ R' : Ixon.Env}
    {env₁ : Ix.Kernel.Env .anon} {r : Ix.Kernel.Role} {a : _root_.Address}
    {lps : List Ix.Kernel.LevelParam} {tyD ty : Core.KExpr}
    (hall : AllBound t) (hgrp : roleGroup g = [r]) (hstd : r ∈ standardAxioms)
    (ha : t.addressOf? r = some a) (hadm : Admits ρ t g R R')
    (hb : BndOver.{u} L t (· < g) R₁ env₁) (hadds : AddsAt R₁ R' a)
    (hfresh : env₁.find? (Ix.Kernel.Key.role r) = none)
    (hcv : Ix.Kernel.Semantics.ConstantValRunJ Ix.Kernel.Model.rulesJ env₁
      ⟨.role r, lps, tyD⟩ ty)
    (hpin : Ix.Kernel.ConstantVal.matchesPin ⟨.role r, lps, ty⟩ (stdAxiomPin r) = true)
    (hnaux : tyD.RefsIn Decl.NonAuxKey)
    (hty : Annotates ty tyD)
    (hreads : Reads t R' a (.axiomInfo ⟨.role r, lps, tyD⟩))
    (hsolo : ∃ c ax, recordOf R' a = some c ∧ c.info = .axio ax)
    (hsize : a.hash.size = 32)
    (hreload : ∀ E, RecordsFor R' E →
      Decl.ReloadsAs E t (axInstalled env₁ r lps ty) (.axiomInfo ⟨.role r, lps, ty⟩)) :
    BeforeRaise.{u} L t g R' (axInstalled env₁ r lps ty) := by
  -- the group, the axiom's key
  have hrg : r ∈ roleGroup g := by rw [hgrp]; exact List.mem_singleton.mpr rfl
  have hgr : Ix.SpecDigest.groupOf r = g := groupOf_of_mem_roleGroup hrg
  have hr := std_cases hstd
  obtain ⟨-, -, hnpre, hax, -, -, -, hnop⟩ := std_facts r hstd
  have htwf : t.wf = true := by
    obtain ⟨E, hE⟩ := recordsFor_exists hb.shape.committed
    exact (hb.inv hE (carried_valLimit g) (limWithin_below t g)).tableWf
  have hkeya : keyOf t a = Ix.Kernel.Key.role r := Core.keyOf_of_addressOf htwf ha
  have hkey_role : ∀ x, keyOf t x = Ix.Kernel.Key.role r → x = a := by
    intro x hx
    have h1 := Core.addressOf_of_keyOf htwf hx
    rw [ha] at h1
    exact (Option.some.inj h1).symm
  have hnt : ∀ T : Ix.Kernel.Key .anon,
      (Ix.Kernel.Key.role r : Core.KKey) ≠ Ix.Kernel.projTableName T := by
    intro T
    rw [← hkeya]
    exact Decl.ne_projTableName_of_isBaseKey (Decl.isBaseKey_keyOf t a)
  -- the new constant
  have hext : Ix.Kernel.EnvExt env₁ (axInstalled env₁ r lps ty) :=
    Ix.Kernel.EnvExt.cons hfresh (fun _ => hnt _)
  have hself : (axInstalled env₁ r lps ty).find? (Ix.Kernel.Key.role r) =
      some (.axiomInfo ⟨.role r, lps, ty⟩) := by
    show (⟨(Ix.Kernel.ConstantInfo.axiomInfo ⟨.role r, lps, ty⟩) :: env₁.consts⟩ :
      Ix.Kernel.Env .anon).find? _ = _
    rw [Ix.Kernel.Env.find?_cons]
    exact ite_eq_left rfl
  have hfind_ne : ∀ X : Ix.Kernel.Role, X ≠ r →
      (axInstalled env₁ r lps ty).find? (Ix.Kernel.Key.role X) =
        env₁.find? (Ix.Kernel.Key.role X) := by
    intro X hX
    show (⟨(Ix.Kernel.ConstantInfo.axiomInfo ⟨.role r, lps, ty⟩) :: env₁.consts⟩ :
      Ix.Kernel.Env .anon).find? _ = _
    rw [Ix.Kernel.Env.find?_cons]
    exact ite_eq_right (fun h => hX (Ix.Kernel.Key.role.inj
      (show (Ix.Kernel.Key.role r : Core.KKey) = Ix.Kernel.Key.role X from h)).symm)
  -- the kernel's declaration step: `stdAxiomOk` from the pinned `Iff` or `Nonempty`
  have hstdok : Ix.Kernel.stdAxiomOk env₁ ⟨.role r, lps, ty⟩ = true := by
    obtain ⟨hio, hno⟩ := std_order
    rcases hr with rfl | rfl
    · have hp : Ix.Kernel.ConstantVal.matchesPin ⟨.role .propext, lps, ty⟩
          Ix.Kernel.propextA = true := by simpa [stdAxiomPin] using hpin
      exact hb.facts.shapes.iff (show Ix.SpecDigest.groupOf .iff < g by rw [← hgr]; exact hio)
        _ rfl hp
    · have hp : Ix.Kernel.ConstantVal.matchesPin ⟨.role .choice, lps, ty⟩
          Ix.Kernel.choiceA = true := by simpa [stdAxiomPin] using hpin
      exact hb.facts.shapes.nonempty
        (show Ix.SpecDigest.groupOf .nonempty < g by rw [← hgr]; exact hno) _ rfl hp
  have hrun : Ix.Kernel.Semantics.DeclRunJ Ix.Kernel.Model.rulesJ
      (Ix.Kernel.Semantics.IndRoutesJ Ix.Kernel.Model.rulesJ env₁) env₁
      (.axiomDecl ⟨.role r, lps, tyD⟩) (axInstalled env₁ r lps ty) := by
    show Ix.Kernel.Semantics.DeclAxiomRunJ Ix.Kernel.Model.rulesJ env₁ ⟨.role r, lps, tyD⟩
      (axInstalled env₁ r lps ty)
    exact Or.inr ⟨ty, hcv, Or.inl ⟨hstdok, rfl⟩⟩
  have hna : Decl.DeclNonAux (.axiomDecl ⟨.role r, lps, tyD⟩) := by
    unfold Decl.DeclNonAux
    simp only [IxVM.Consistency.installs]
    split
    · simp
    · refine ⟨fun ci₀ hm => ?_, by simp⟩
      rw [List.mem_singleton] at hm
      subst hm
      exact ⟨hkeya ▸ nonAux_keyOf t a, hnaux, trivial⟩
  -- the prefix invariant at the limits within the groups below `g`
  have hinvA : ∀ E, RecordsFor R' E → ∀ lim, Carried lim → LimWithin (· < g) t lim →
      Decl.PrefixInv.{u} E t lim (axInstalled env₁ r lps ty) := by
    intro E hE lim hc hw
    have h0 := hb.inv (recordsFor_down hadds hE) hc hw
    exact h0.cons_value (cn := .axiomInfo ⟨.role r, lps, ty⟩) (a₀ := a) hkeya.symm hfresh
      hnt (fun _ _ e => nomatch e) (fun _ _ _ e => nomatch e) (fun _ _ _ _ e => nomatch e)
      (fun _ e => nomatch e) (Decl.fullDeclInv_step_declRunJ hna hrun)
      (Decl.foldStoreInv_step_declRunJ (d := .axiomDecl ⟨.role r, lps, tyD⟩) h0.store
        (fun _ _ heq => nomatch heq) hrun)
      (hreload E hE)
  -- the clause at those limits, by the axiom's own declaration step
  have hclause : FoldClauseOver.{u} L t (· < g) R' (axInstalled env₁ r lps ty) := by
    obtain ⟨Reg, hR⟩ := hb.clause
    refine ⟨Reg, fun E hE lim hc hw => ?_⟩
    have h0 := hR E (recordsFor_down hadds hE) lim hc hw
    exact FoldClauseWith.consValue hL h0 (cn := .axiomInfo ⟨.role r, lps, ty⟩)
      (d₀ := .axiomDecl ⟨.role r, lps, tyD⟩) hfresh (Or.inr (Or.inr ⟨_, rfl⟩)) hnt hrun
      ⟨a, hkeya.symm, hsize⟩ (hinvA E hE lim hc hw)
  -- the new record
  obtain ⟨cA, axA, hcA, hdA⟩ := hsolo
  have hkeptNew : KeptIn t (recordOf R') (fun x => R'.blobs.get? x) a
      (.axiomInfo ⟨.role r, lps, ty⟩) :=
    ⟨fun _ _ _ _ => ⟨r, hax, hkeya⟩, _, hreads, ⟨⟨rfl, rfl, hty⟩, trivial⟩⟩
  -- the reading of `R'`
  have hnodup : ((axInstalled env₁ r lps ty).consts.map (·.name)).Nodup :=
    List.nodup_cons.mpr ⟨not_mem_names_of_find_none hfresh, hb.shape.reading.nodup⟩
  have hprov : ∀ ci ∈ (claimedEnv (axInstalled env₁ r lps ty)).consts,
      (∃ tbl, ci = .projInfo tbl) ∨ PinnedBasis ci ∨
        ∃ x, KeptIn t (recordOf R') (fun y => R'.blobs.get? y) x ci := by
    intro ci hci
    unfold claimedEnv at hci
    obtain ⟨hmem, hp⟩ := List.mem_filter.mp hci
    rcases List.mem_cons.mp hmem with rfl | hold
    · exact Or.inr (Or.inr ⟨a, hkeptNew⟩)
    · rcases hb.shape.reading.provenance ci (List.mem_filter.mpr ⟨hold, hp⟩) with
        h | h | ⟨x, hx⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨x, keptIn_up hadds hx⟩)
  have hreading : ReadingOf t R' (axInstalled env₁ r lps ty) := by
    refine ⟨hnodup, hprov, fun x hx => ?_⟩
    by_cases hxa : x = a
    · subst hxa
      rw [hkeya]
      exact ⟨_, hself, Or.inr ⟨_, hreads, ⟨⟨rfl, rfl, hty⟩, trivial⟩⟩⟩
    · obtain ⟨ci₀, hr₀⟩ := hx
      obtain ⟨ci, hci, hpin'⟩ := hb.shape.reading.stored x ⟨ci₀, reads_down_ax hadds
        ⟨cA, axA, hcA, hdA⟩ hxa hr₀⟩
      refine ⟨ci, hext.find hci, ?_⟩
      rcases hpin' with hp | ⟨ci₁, hr₁, hst⟩
      · exact Or.inl hp
      · exact Or.inr ⟨ci₁, ReadsIn.mono (fun y c hc => recordOf_up hadds hc)
          (fun y b hb' => (hadds.2.2 y b).mpr hb') hr₁, hst⟩
  have hshape : TableShape.{u} t (· < g + 1) R' (axInstalled env₁ r lps ty) := {
    needsClosed := fun k hk r' hr' => by
      have h1 := groupNeeded_lt hr'
      have hk' : k < g + 1 := hk
      show Ix.SpecDigest.groupOf r' < g + 1
      omega
    bound := fun k _ r' _ => hall r'
    prelude := hb.shape.prelude
    literals := hb.shape.literals
    hashed := hadm.hashed
    usedClosed := hadm.usedClosed
    committed := hadm.committed
    zeroFree := hadm.zeroFree
    kept := fun k r' a' hk hr' hkr ha' => by
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hk | rfl
      · obtain ⟨ci, hci, hpin'⟩ := hb.shape.kept k r' a' hk hr' hkr ha'
        refine ⟨ci, hext.find hci, ?_⟩
        rcases hpin' with hp | hp
        · exact Or.inl hp
        · exact Or.inr (keptIn_up hadds hp)
      · rw [hgrp, List.mem_singleton] at hr'
        subst hr'
        rw [ha] at ha'
        obtain rfl := Option.some.inj ha'
        exact ⟨_, hself, Or.inr hkeptNew⟩
    reading := hreading
    pins := fun kind ci hci => List.mem_cons_of_mem _ (hb.shape.pins kind ci hci)
    preludeKept := fun k r' a' hk hr' hpr ha' => by
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hk | rfl
      · obtain ⟨ci, hci, hpin'⟩ := hb.shape.preludeKept k r' a' hk hr' hpr ha'
        refine ⟨ci, hext.find hci, ?_⟩
        rcases hpin' with hp | hp
        · exact Or.inl hp
        · exact Or.inr (keptIn_up hadds hp)
      · rw [hgrp, List.mem_singleton] at hr'
        subst hr'
        exact absurd hpr hnpre
    model := by
      obtain ⟨E, hE⟩ := recordsFor_exists hadm.committed
      exact claimedEnv_models_of_prefixInv
        (hinvA E hE (some (valLimit g)) (carried_valLimit g) (limWithin_below t g)) hnodup
        hprov }
  have hfacts : BoundaryFacts t (· < g + 1) R' (axInstalled env₁ r lps ty) := {
    whole := fun E hE x B c cb ms hfx hrec hown hne hrecB hmuts => by
      by_cases hk : keyOf t x = Ix.Kernel.Key.role r
      · have hx := hkey_role x hk
        subst hx
        have hrA : Ix.Cert.recordAt E x = some cA := hE.2.1 x cA hcA
        rw [hrA] at hrec
        have hcc : cA = c := Option.some.inj hrec
        subst hcc
        have hown' : Ix.Cert.ownerOf x cA = x := by
          unfold Ix.Cert.ownerOf
          rw [hdA]
        exact absurd (hown.symm.trans hown') hne
      · have e : (axInstalled env₁ r lps ty).find? (keyOf t x) = env₁.find? (keyOf t x) := by
          show (⟨(Ix.Kernel.ConstantInfo.axiomInfo ⟨.role r, lps, ty⟩) :: env₁.consts⟩ :
            Ix.Kernel.Env .anon).find? _ = _
          rw [Ix.Kernel.Env.find?_cons]
          exact ite_eq_right (fun h => hk h.symm)
        have hfx' : (env₁.find? (keyOf t x)).isSome = true := by
          rw [← e]
          exact hfx
        have hbs := hb.facts.whole E (recordsFor_down hadds hE) x B c cb ms hfx' hrec hown hne
          hrecB hmuts
        intro i m hm
        obtain ⟨h1, h2⟩ := hbs i m hm
        refine ⟨?_, fun ind j hind hj => ?_⟩
        · obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp h1
          rw [hext.find hci]
          rfl
        · obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp (h2 ind j hind hj)
          rw [hext.find hci]
          rfl
    opsPinned := RoleOps.OpsPinned.ext hb.facts.opsPinned hext (fun n hn hs => by
      rw [RoleOps.opNames_eq_map] at hn
      obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hn
      have hne : r' ≠ r := fun e => hnop (e ▸ hr')
      rwa [hfind_ne r' hne] at hs)
    opsAdmitted := fun r'' hr'' hs => by
      show Ix.SpecDigest.groupOf r'' < g + 1
      have hne : r'' ≠ r := fun e => hnop (e ▸ hr'')
      rw [hfind_ne r'' hne] at hs
      exact Nat.lt_succ_of_lt (hb.facts.opsAdmitted r'' hr'' hs)
    shapes := shapes_axiom hgrp hr hext hfind_ne hb.facts.shapes }
  exact ⟨hshape, hclause, hfacts, raise_axiom hgrp hstd⟩

/-- **The standard axiom's group when the closure's environment already stores the axiom's
key**: then the closure's store holds the axiom's record and the environment stores a pin or
the record's reading there, and the environment itself is the one before the raise past `g`. -/
theorem roleAxiom_stored {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {ρ : BRun} {t : Ix.Kernel.RoleTable} {g : Nat} {R R₁ R' : Ixon.Env}
    {env₁ : Ix.Kernel.Env .anon} {r : Ix.Kernel.Role} {a : _root_.Address}
    (hall : AllBound t) (hgrp : roleGroup g = [r]) (hstd : r ∈ standardAxioms)
    (ha : t.addressOf? r = some a) (hadm : Admits ρ t g R R')
    (hb : BndOver.{u} L t (· < g) R₁ env₁) (hadds : AddsAt R₁ R' a)
    (hsolo : ∃ c ax, recordOf R' a = some c ∧ c.info = .axio ax)
    {ci : Ix.Kernel.ConstantInfo .anon} (hci : env₁.find? (Ix.Kernel.Key.role r) = some ci) :
    BeforeRaise.{u} L t g R' env₁ := by
  have hr := std_cases hstd
  obtain ⟨-, -, hnpre, -, -, -, -, -⟩ := std_facts r hstd
  have htwf : t.wf = true := by
    obtain ⟨E, hE⟩ := recordsFor_exists hb.shape.committed
    exact (hb.inv hE (carried_valLimit g) (limWithin_below t g)).tableWf
  have hkeya : keyOf t a = Ix.Kernel.Key.role r := Core.keyOf_of_addressOf htwf ha
  have hkey_role : ∀ x, keyOf t x = Ix.Kernel.Key.role r → x = a := by
    intro x hx
    have h1 := Core.addressOf_of_keyOf htwf hx
    rw [ha] at h1
    exact (Option.some.inj h1).symm
  -- what the environment stores at the axiom's key
  have hkept : PinnedBasis ci ∨ KeptIn t (recordOf R') (fun x => R'.blobs.get? x) a ci := by
    have hf : env₁.find? (keyOf t a) = some ci := by rw [hkeya]; exact hci
    obtain ⟨hcl, hna⟩ := seed_claimed hf
    rcases hb.shape.reading.provenance ci hcl with ⟨tbl, htbl⟩ | hpin | ⟨x, hk⟩
    · rw [htbl] at hna
      exact absurd rfl (hna tbl.structName .projTable)
    · exact Or.inl hpin
    · have hname : ci.name = keyOf t a := Ix.Kernel.Semantics.Env.find?_name hf
      have hx : x = a := hkey_role x ((keptIn_name hk).symm.trans (hname.trans hkeya))
      subst hx
      exact Or.inr (keptIn_up hadds hk)
  have hreading : ReadingOf t R' env₁ := by
    refine ⟨hb.shape.reading.nodup, fun ci' hci' => ?_, fun x hx => ?_⟩
    · rcases hb.shape.reading.provenance ci' hci' with h | h | ⟨x, hx⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨x, keptIn_up hadds hx⟩)
    · by_cases hxa : x = a
      · rw [hxa, hkeya]
        rcases hkept with hp | ⟨-, ci₀, hr₀, hst⟩
        · exact ⟨ci, hci, Or.inl hp⟩
        · exact ⟨ci, hci, Or.inr ⟨ci₀, hr₀, hst⟩⟩
      · obtain ⟨ci₀, hr₀⟩ := hx
        obtain ⟨ci₂, hci₂, hpin'⟩ := hb.shape.reading.stored x
          ⟨ci₀, reads_down_ax hadds hsolo hxa hr₀⟩
        refine ⟨ci₂, hci₂, ?_⟩
        rcases hpin' with hp | ⟨ci₁, hr₁, hst⟩
        · exact Or.inl hp
        · exact Or.inr ⟨ci₁, ReadsIn.mono (fun y c hc => recordOf_up hadds hc)
            (fun y b hb' => (hadds.2.2 y b).mpr hb') hr₁, hst⟩
  have hshape : TableShape.{u} t (· < g + 1) R' env₁ := {
    needsClosed := fun k hk r' hr' => by
      have h1 := groupNeeded_lt hr'
      have hk' : k < g + 1 := hk
      show Ix.SpecDigest.groupOf r' < g + 1
      omega
    bound := fun k _ r' _ => hall r'
    prelude := hb.shape.prelude
    literals := hb.shape.literals
    hashed := hadm.hashed
    usedClosed := hadm.usedClosed
    committed := hadm.committed
    zeroFree := hadm.zeroFree
    kept := fun k r' a' hk hr' hkr ha' => by
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hk | rfl
      · obtain ⟨ci', hci', hpin'⟩ := hb.shape.kept k r' a' hk hr' hkr ha'
        refine ⟨ci', hci', ?_⟩
        rcases hpin' with hp | hp
        · exact Or.inl hp
        · exact Or.inr (keptIn_up hadds hp)
      · rw [hgrp, List.mem_singleton] at hr'
        subst hr'
        rw [ha] at ha'
        obtain rfl := Option.some.inj ha'
        exact ⟨ci, hci, hkept⟩
    reading := hreading
    pins := hb.shape.pins
    preludeKept := fun k r' a' hk hr' hpr ha' => by
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hk | rfl
      · obtain ⟨ci', hci', hpin'⟩ := hb.shape.preludeKept k r' a' hk hr' hpr ha'
        refine ⟨ci', hci', ?_⟩
        rcases hpin' with hp | hp
        · exact Or.inl hp
        · exact Or.inr (keptIn_up hadds hp)
      · rw [hgrp, List.mem_singleton] at hr'
        subst hr'
        exact absurd hpr hnpre
    model := hb.shape.model }
  have hfacts : BoundaryFacts t (· < g + 1) R' env₁ := {
    whole := fun E hE => hb.facts.whole E (recordsFor_down hadds hE)
    opsPinned := hb.facts.opsPinned
    opsAdmitted := fun r'' hr'' hs => by
      show Ix.SpecDigest.groupOf r'' < g + 1
      exact Nat.lt_succ_of_lt (hb.facts.opsAdmitted r'' hr'' hs)
    shapes := shapes_axiom hgrp hr (Ix.Kernel.EnvExt.refl env₁) (fun _ _ => rfl)
      hb.facts.shapes }
  have hclause : FoldClauseOver.{u} L t (· < g) R' env₁ := by
    obtain ⟨Reg, hR⟩ := hb.clause
    exact ⟨Reg, fun E hE lim hc hw => hR E (recordsFor_down hadds hE) lim hc hw⟩
  exact ⟨hshape, hclause, hfacts, raise_axiom hgrp hstd⟩

/-! ## The role unit -/

/-- **What a binding run's validation of a standard axiom gives the fold**: at every group `g`
whose one role is the standard axiom `r` bound at `a`, every admission of `g` by the run from
`R` to `R'`, and every store `R₁` and environment `env₁` with the invariant below `g` such that
`R'` is `R₁` and the record at `a`: the axiom's declaration checked at `env₁` (its declared type
`tyD` elaborates to a sort, stored as `ty`), the stored signature matching the kernel's pin, the
declared type naming no derived key, `ty` annotating `tyD`, the record at `a` an axiom record
reading as the declaration, at an address of 32 bytes, and the stored constant the one every
load of the record represents.

From the run: `KernelRoles::validate_standard_axiom` (`KernelRoles.lean:926`) asserts the record
an axiom with no unsafe flag, its type well scoped (`validate_expr_well_scoped`) and a sort under
the group's role context (`k_ensure_sort`), and its type structurally equal to `role_type(tbl,
r)` (`assert_type_pinned`), which is the specified type up to binder data
(`roleTypeRenders`). -/
def AxiomValidationFacts (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    (calls : List (Call F)) : Prop :=
  ∀ (t : Ix.Kernel.RoleTable) (ρ : BRun) (Rs : Nat → Ixon.Env),
    BindingRun calls t ρ Rs → RunStepStores calls t ρ.E₀ → AllBound t → t.check = .ok () →
    ∀ (g : Nat) (r : Ix.Kernel.Role) (a : _root_.Address) (R R₁ R' : Ixon.Env)
      (env₁ : Ix.Kernel.Env .anon),
      6 ≤ g → g < 77 → roleGroup g = [r] → r ∈ standardAxioms → t.addressOf? r = some a →
      Admits ρ t g R R' → AdmitsReads ρ t R R' → BndOver.{u} L t (· < g) R₁ env₁ →
      AddsAt R₁ R' a →
      ∃ (lps : List Ix.Kernel.LevelParam) (tyD ty : Core.KExpr),
        Ix.Kernel.Semantics.ConstantValRunJ Ix.Kernel.Model.rulesJ env₁
          ⟨.role r, lps, tyD⟩ ty ∧
        Ix.Kernel.ConstantVal.matchesPin ⟨.role r, lps, ty⟩ (stdAxiomPin r) = true ∧
        tyD.RefsIn Decl.NonAuxKey ∧ Annotates ty tyD ∧
        Reads t R' a (.axiomInfo ⟨.role r, lps, tyD⟩) ∧
        (∃ c ax, recordOf R' a = some c ∧ c.info = .axio ax) ∧ a.hash.size = 32 ∧
        ∀ E, RecordsFor R' E →
          Decl.ReloadsAs E t (axInstalled env₁ r lps ty) (.axiomInfo ⟨.role r, lps, ty⟩)

/-- **The standard axioms' role unit, from the validation facts.** -/
theorem standardAxiomRoleUnit_of_validation {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    (hL : LinkLaws L) {calls : List (Call F)} (hv : AxiomValidationFacts.{u} L calls) :
    AtGroups (BindingRun calls) (RoleUnitStepOver.{u} (· ∈ standardAxioms) L) := by
  intro t ρ Rs hrun hall ht g h6 h77 r a R R₁ R' env₁ hgrp hstd ha hadm hreads hb hadds
  obtain ⟨lps, tyD, ty, hcv, hpin, hnaux, hty, hrd, hsolo, hsize, hreload⟩ :=
    hv t ρ Rs hrun hrun.stepStores hall ht g r a R R₁ R' env₁ h6 h77 hgrp hstd ha hadm hreads
      hb hadds
  cases hf : env₁.find? (Ix.Kernel.Key.role r) with
  | none =>
    exact ⟨axInstalled env₁ r lps ty, fun ci hci => List.mem_cons_of_mem _ hci,
      roleAxiom_step hL hall hgrp hstd ha hadm hb hadds hf hcv hpin hnaux hty hrd hsolo hsize
        hreload⟩
  | some ci =>
    exact ⟨env₁, fun _ h => h, roleAxiom_stored hall hgrp hstd ha hadm hb hadds hsolo hf⟩

/-- **The standard axioms' role unit at the link the composed fold carries**, in the form the
composed residual takes it. -/
theorem standardAxiomRoleUnit
    (hv : ∀ calls : List (Call F), AxiomValidationFacts.{u} FormerOpenTraceAt calls) :
    ∀ calls : List (Call F), AtGroups (BindingRun calls)
      (RoleUnitStepOver.{u} (· ∈ standardAxioms) FormerOpenTraceAt) :=
  fun calls => standardAxiomRoleUnit_of_validation linkLaws_formerOpenTrace (hv calls)

end IxVM.Refinement.Binding.AxiomInstall
