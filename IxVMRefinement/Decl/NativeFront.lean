import IxVMRefinement.Decl.NativeEnv
import IxVMRefinement.Callees.ProjAddr
import IxVMRefinement.Subst.Spine
import IxVMRefinement.Obs.KernelCheck0
import IxVMRefinement.Obs.KernelCheck1
import IxVMRefinement.Obs.KernelCheck2
import IxVMRefinement.Obs.KernelCheck5
import IxVMRefinement.Obs.KernelCheck12
import IxVMRefinement.Obs.KernelDefEq3
import IxVMRefinement.Obs.KernelTypes0
import IxC.Kernel.Verify.PropWhen

/-! # Native one-type inductive front stages and recursor-less route

This module refines the shared front-end stages of `KernelCheck::check_const` on unpinned
one-type native inductive blocks (`check_inductive_shape`, `get_result_sort_level`,
`former_decl_ok`, `ctor_zero_all`, `check_inductive_shape_ctors`, `check_param_agreement`,
`check_ctor_return_type`, `check_field_universes`, and `check_positivity`) to `SumIndRunJ`,
`SumCtorsRunJ`, `classifyFixKinds`, `nativeFieldsOk`, `FieldSortsJ`, and `FormerReadJ`, and
closes the recursor-less native route (`DeclNativeNoRecRunJ` + `InstallStep`). -/

universe u

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList repKLevel_heapMono₂)
open Ix.Kernel (ConstantInfo ConstantVal Declaration Expr Level LevelParam)
open Ix.Kernel.Rules (Red DefEq Infer)
open Ix.Kernel.Semantics (Judgements ConstantValRunJ ConstantValCheckJ DeclRunJ IndRoutesJ
  SumIndRunJ FormerStoredJ FormerReadJ SumCtorsRunJ SumCtorRunJ StructDomsJ FieldSortsJ
  DeclNativeNoRecRunJ nativePartsNoRec? nativeRecStub ctorZeroOk famDomOk famHead pwsAll)
open Ix.Kernel.Model (rulesJ)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-! ## Level zero-ness, `isEquiv`, `Levels` wrapper, and recogniser inversions -/

/-- Wrapper for `KernelLevels::level_leq` returning `1` from `L2` (`IxVM.Consistency.Levels`). -/
theorem levels_leq_one (hLevels : IxVM.Consistency.Levels) {a b : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} {la lb : KLevel}
    (ev : ObsFn W "KernelLevels::level_leq" [a, b] h (.field 1) h' cs)
    (hbnd : IxVM.Consistency.Bounded cs)
    (ha : RepKLevel h la a) (hb : RepKLevel h lb b) :
    ∀ φ, Level.eval φ la ≤ Level.eval φ lb :=
  hLevels.1 a b h h' cs la lb ev hbnd ha hb

theorem simplify_eq_zero_of_eval_zero :
    ∀ {l : KLevel}, (∀ φ : LevelParam → Nat, Level.eval φ l = 0) → Level.simplify l = .zero
  | .zero, _ => rfl
  | .param p, h => by
    have h1 := h (fun _ => 1)
    simp [Level.eval] at h1
  | .succ l, h => by
    have h0 := h (fun _ => 0)
    simp [Level.eval] at h0
  | .max l r, h => by
    have hl : ∀ φ, Level.eval φ l = 0 := fun φ => by
      have := h φ; simp only [Level.eval] at this; omega
    have hr : ∀ φ, Level.eval φ r = 0 := fun φ => by
      have := h φ; simp only [Level.eval] at this; omega
    simp [Level.simplify, simplify_eq_zero_of_eval_zero hl,
      simplify_eq_zero_of_eval_zero hr, Level.combining]
  | .imax l r, h => by
    have hr : ∀ φ, Level.eval φ r = 0 := fun φ => by
      have := h φ
      simp only [Level.eval] at this
      split at this
      · assumption
      · omega
    have hrs := simplify_eq_zero_of_eval_zero hr
    simp only [Level.simplify, hrs]
    split <;> rfl

theorem isEquiv_zero_of_eval_zero {l : KLevel}
    (h : ∀ φ : LevelParam → Nat, Level.eval φ l = 0) :
    (Level.isEquiv l .zero == some true) = true := by
  have hs : Level.simplify l = Level.simplify .zero := simplify_eq_zero_of_eval_zero h
  rw [Level.isEquiv_eq_withoutPtr, ite_eq_left hs]
  rfl

theorem eval_zero_of_isEquiv_zero {l : KLevel}
    (h : (Level.isEquiv l .zero == some true) = true) :
    ∀ φ : LevelParam → Nat, Level.eval φ l = 0 := by
  have heq : Level.isEquiv l .zero = some true := eq_of_beq h
  intro φ
  simpa [Level.eval] using Level.isEquiv_sound' heq φ

theorem isEquiv_zero_iff_eval_zero {l : KLevel} :
    (Level.isEquiv l .zero == some true) = true ↔ (∀ φ : LevelParam → Nat, Level.eval φ l = 0) :=
  ⟨eval_zero_of_isEquiv_zero, isEquiv_zero_of_eval_zero⟩

theorem isEquiv_zero_congr {u v : KLevel} (h : LvEq u v) :
    (Level.isEquiv u .zero == some true) = (Level.isEquiv v .zero == some true) := by
  by_cases hu : (Level.isEquiv u .zero == some true) = true
  · have hv : (Level.isEquiv v .zero == some true) = true :=
      isEquiv_zero_of_eval_zero fun φ => by rw [← h φ]; exact eval_zero_of_isEquiv_zero hu φ
    rw [hu, hv]
  · simp only [Bool.not_eq_true] at hu
    by_cases hv : (Level.isEquiv v .zero == some true) = true
    · have hu' : (Level.isEquiv u .zero == some true) = true :=
        isEquiv_zero_of_eval_zero fun φ => by rw [h φ]; exact eval_zero_of_isEquiv_zero hv φ
      rw [hu] at hu'; exact nomatch hu'
    · simp only [Bool.not_eq_true] at hv
      rw [hu, hv]

theorem stripPis_of_piBinders_sort :
    ∀ (e : KExpr) {bs : List (KExpr × Ix.Kernel.BinderMeta)} {s : KLevel},
      e.piBinders = (bs, .sort s) → e.stripPis bs.length = some (bs, .sort s)
  | .forallE ty b m, bs, s, h => by
    simp only [Expr.piBinders] at h
    rcases hpb : b.piBinders with ⟨bs₁, rest⟩
    rw [hpb] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [List.length_cons, Expr.stripPis]
    rw [stripPis_of_piBinders_sort b hpb]
    rfl
  | .bvar _, bs, s, h | .fvar _ _, bs, s, h | .sort _, bs, s, h | .const _ _, bs, s, h
  | .app _ _, bs, s, h | .lam _ _ _, bs, s, h | .letE _ _ _ _, bs, s, h | .lit _, bs, s, h
  | .proj _ _ _, bs, s, h => by
    simp only [Expr.piBinders, Prod.mk.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    simp [h2, Expr.stripPis]

theorem stripPis_sort_of_annotates :
    ∀ (n : Nat) {e' e : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)} {s : KLevel},
      IxVM.Consistency.Annotates e' e →
      e.stripPis n = some (bs, .sort s) →
      ∃ bs', e'.stripPis n = some (bs', .sort s) ∧ bs'.length = bs.length
  | 0, _, _, bs, s, ha, hst => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, rfl⟩ := hst
    cases ha with
    | sort => exact ⟨[], rfl, rfl⟩
  | n + 1, _, _, bs, s, ha, hst => by
    cases ha with
    | @forallE ty' _ _ _ m' _ _ hbo =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at hst
      obtain ⟨⟨bs₁, body₁⟩, hst₁, hst⟩ := hst
      simp only [Prod.mk.injEq] at hst
      obtain ⟨rfl, rfl⟩ := hst
      obtain ⟨bs', hst', hlen⟩ := stripPis_sort_of_annotates n hbo hst₁
      exact ⟨(ty', m') :: bs', by simp [Expr.stripPis, hst'], by simp [hlen]⟩
    | bvar | fvar _ | sort | const | app _ _ | lam _ _ | letE _ | lit | proj _ =>
      simp [Expr.stripPis] at hst

theorem stripPis_instantiate1_sort :
    ∀ (m : Nat) {bo v : KExpr} {k : Nat}
      {bs : List (KExpr × Ix.Kernel.BinderMeta)} {s : KLevel},
      bo.stripPis m = some (bs, .sort s) →
      ∃ bs', (bo.instantiate1 v k).stripPis m = some (bs', .sort s)
  | 0, bo, v, k, bs, s, hst => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hst
    obtain ⟨rfl, rfl⟩ := hst
    exact ⟨[], rfl⟩
  | m + 1, bo, v, k, bs, s, hst => by
    cases bo with
    | forallE dom body bi =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at hst
      obtain ⟨⟨bs₁, body₁⟩, hst₁, hst⟩ := hst
      simp only [Prod.mk.injEq] at hst
      obtain ⟨rfl, rfl⟩ := hst
      obtain ⟨bs', hst'⟩ := stripPis_instantiate1_sort m (v := v) (k := k + 1) hst₁
      exact ⟨(dom.instantiate1 v k, bi) :: bs',
        by simp [Expr.instantiate1, Expr.stripPis, hst']⟩
    | _ => simp [Expr.stripPis] at hst

theorem stripPis_split :
    ∀ (a b : Nat) {e : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)} {body : KExpr},
      e.stripPis (a + b) = some (bs, body) →
      ∃ bs₁ mid bs₂,
        e.stripPis a = some (bs₁, mid) ∧
        mid.stripPis b = some (bs₂, body) ∧
        bs₁ ++ bs₂ = bs ∧
        bs₁.length = a
  | 0, b, e, bs, body, h => by
    rw [Nat.zero_add] at h
    exact ⟨[], e, bs, rfl, h, rfl, rfl⟩
  | a + 1, b, e, bs, body, h => by
    cases e with
    | forallE dom bo bi =>
      rw [Nat.add_right_comm a 1 b] at h
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs', body'⟩, h', heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      obtain ⟨bs₁, mid, bs₂, h₁, h₂, happ, hlen⟩ := stripPis_split a b h'
      exact ⟨(dom, bi) :: bs₁, mid, bs₂,
        by simp [Expr.stripPis, h₁], h₂, by simp [happ], by simp [hlen]⟩
    | _ =>
      rw [Nat.add_right_comm a 1 b] at h
      simp [Expr.stripPis] at h

theorem sumSplit_append_recStub :
    ∀ (rest : List KConstantInfo) (cvR : KConstantVal),
      rest.all (fun | .ctorInfo .. => true | _ => false) = true →
      ∃ cs : List (KConstantVal × Nat × Nat),
        Ix.Kernel.sumSplit (rest ++ [.recInfo cvR 0 0 []]) = some (cs, cvR, 0, 0, []) ∧
        rest = cs.map (fun c => .ctorInfo c.1 c.2.1 c.2.2)
  | [], cvR, _ => ⟨[], rfl, rfl⟩
  | ci :: rest, cvR, hall => by
    cases ci with
    | ctorInfo cvC nP nF =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨cs, hsp, hrest⟩ := sumSplit_append_recStub rest cvR hall.2
      refine ⟨(cvC, nP, nF) :: cs, ?_, by simp [hrest]⟩
      simp [List.cons_append, Ix.Kernel.sumSplit, hsp]
    | _ => simp at hall

theorem nativeShape?_inv {nPd : Nat} {block : List KConstantInfo}
    {p : Ix.Kernel.InductiveShape .anon}
    (h : Ix.Kernel.nativeShape? nPd block = some p) :
    ∃ (caps₀ : Ix.Kernel.IndCaps .anon) (rest : List KConstantInfo)
      (cs : List (KConstantVal × Nat × Nat)) (mI rP : Nat) (rules : List (Ix.Kernel.RecRule .anon)),
      block = .indInfo p.cvT caps₀ :: rest ∧
      Ix.Kernel.sumSplit rest = some (cs, p.cvR, mI, rP, rules) ∧
      Ix.Kernel.nativeCounts? nPd p.cvT cs mI rP = some (p.nP, p.nIdx) ∧
      p.nP = nPd ∧
      p.ctors = cs.map (fun c => (c.1, c.2.2)) ∧
      p.rhss = rules.map (·.rhs) ∧
      Ix.Kernel.reservedBasisNames.contains p.cvT.name = false ∧
      Ix.Kernel.reservedBasisNames.contains p.cvR.name = false ∧
      (∀ c ∈ cs, c.2.1 = p.nP ∧ c.1.levelParams = p.cvT.levelParams ∧
        Ix.Kernel.reservedBasisNames.contains c.1.name = false) ∧
      (∀ c ∈ p.ctors, c.1.levelParams = p.cvT.levelParams ∧
        Ix.Kernel.reservedBasisNames.contains c.1.name = false) ∧
      p.isProp = (Level.isEquiv p.resSort .zero == some true) ∧
      (∀ bs s₀, p.cvT.type.stripPis (p.nP + p.nIdx) = some (bs, .sort s₀) → p.resSort = s₀) ∧
      ((∀ elim, p.cvR.levelParams ≠ elim :: p.cvT.levelParams) → p.large = false) := by
  cases block with
  | nil => simp [Ix.Kernel.nativeShape?] at h
  | cons hd rest =>
    cases hd with
    | indInfo cvT caps₀ =>
      cases hsp : Ix.Kernel.sumSplit rest with
      | none => simp [Ix.Kernel.nativeShape?, hsp] at h
      | some q =>
        rcases q with ⟨cs, cvR, mI, rP, rules⟩
        cases hcnt : Ix.Kernel.nativeCounts? nPd cvT cs mI rP with
        | none => simp [Ix.Kernel.nativeShape?, hsp, hcnt] at h
        | some cnt =>
          rcases cnt with ⟨nP, nIdx⟩
          have hnP : nP = nPd := by
            unfold Ix.Kernel.nativeCounts? at hcnt
            split at hcnt
            · split at hcnt
              · simp only [Option.some.injEq, Prod.mk.injEq] at hcnt; exact hcnt.1.symm
              · exact nomatch hcnt
            · split at hcnt
              · exact nomatch hcnt
              · split at hcnt
                · next heq =>
                  simp only [Option.some.injEq, Prod.mk.injEq] at hcnt
                  have heq' := eq_of_beq heq
                  omega
                · exact nomatch hcnt
          simp only [Ix.Kernel.nativeShape?, hsp, hcnt] at h
          by_cases hcond :
            (Ix.Kernel.reservedBasisNames.contains cvT.name == false &&
              Ix.Kernel.reservedBasisNames.contains cvR.name == false &&
              cs.all (fun c => c.2.1 == nP && c.1.levelParams == cvT.levelParams &&
                Ix.Kernel.reservedBasisNames.contains c.1.name == false)) = true
          · rw [ite_eq_left hcond] at h
            have hcond' := hcond
            simp only [Bool.and_eq_true, List.all_eq_true] at hcond'
            obtain ⟨⟨hnbT_b, hnbR_b⟩, hcs⟩ := hcond'
            have hnbT : Ix.Kernel.reservedBasisNames.contains cvT.name = false := eq_of_beq hnbT_b
            have hnbR : Ix.Kernel.reservedBasisNames.contains cvR.name = false := eq_of_beq hnbR_b
            have hcs' : ∀ c ∈ cs, c.2.1 = nP ∧ c.1.levelParams = cvT.levelParams ∧
                Ix.Kernel.reservedBasisNames.contains c.1.name = false := by
              intro c hc
              have h1 := hcs c hc
              exact ⟨eq_of_beq h1.1.1, eq_of_beq h1.1.2, eq_of_beq h1.2⟩
            cases hrlps : cvR.levelParams with
            | nil =>
              rw [hrlps] at h
              dsimp only at h
              injection h with h
              subst h
              refine ⟨caps₀, rest, cs, mI, rP, rules, rfl, hsp, hcnt, hnP, rfl, rfl,
                hnbT, hnbR, hcs', ?_, rfl, ?_, fun _ => rfl⟩
              · intro c hc
                obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hc
                exact ⟨(hcs' c₀ hc₀).2.1, (hcs' c₀ hc₀).2.2⟩
              · intro bs s₀ hst; simp [hst]
            | cons el relps =>
              rw [hrlps] at h
              dsimp only at h
              by_cases heq_rel : (relps == cvT.levelParams && !cvT.levelParams.contains el) = true
              · rw [ite_eq_left heq_rel] at h
                dsimp only at h
                injection h with h
                subst h
                refine ⟨caps₀, rest, cs, mI, rP, rules, rfl, hsp, hcnt, hnP, rfl, rfl,
                  hnbT, hnbR, hcs', ?_, rfl, ?_, ?_⟩
                · intro c hc
                  obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hc
                  exact ⟨(hcs' c₀ hc₀).2.1, (hcs' c₀ hc₀).2.2⟩
                · intro bs s₀ hst; simp [hst]
                · intro hno_elim
                  simp only [Bool.and_eq_true] at heq_rel
                  exact absurd (hrlps.trans (congrArg (el :: ·) (eq_of_beq heq_rel.1))) (hno_elim el)
              · rw [ite_eq_right heq_rel] at h
                dsimp only at h
                injection h with h
                subst h
                refine ⟨caps₀, rest, cs, mI, rP, rules, rfl, hsp, hcnt, hnP, rfl, rfl,
                  hnbT, hnbR, hcs', ?_, rfl, ?_, fun _ => rfl⟩
                · intro c hc
                  obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.mp hc
                  exact ⟨(hcs' c₀ hc₀).2.1, (hcs' c₀ hc₀).2.2⟩
                · intro bs s₀ hst; simp [hst]
          · rw [ite_eq_right hcond] at h
            exact nomatch h
    | _ => simp [Ix.Kernel.nativeShape?] at h

theorem nativeParts?_inv {nPd : Nat} {block : List KConstantInfo}
    {p₀ : Ix.Kernel.NativeParts .anon}
    (h : Ix.Kernel.nativeParts? nPd block = some p₀) :
    Ix.Kernel.nativeShape? nPd block = some p₀.toInductiveShape ∧
      p₀.kinds = [] ∧
      p₀.recPinned = Ix.Kernel.nativeRecPinOk p₀.toInductiveShape block := by
  unfold Ix.Kernel.nativeParts? at h
  obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨hs, rfl, rfl⟩

theorem nativePartsNoRec?_inv {nPd : Nat} {block : List KConstantInfo}
    {p₀ : Ix.Kernel.NativeParts .anon}
    (h : nativePartsNoRec? nPd block = some p₀) :
    ∃ (caps₀ : Ix.Kernel.IndCaps .anon),
      block = .indInfo p₀.cvT caps₀ :: p₀.ctors.map (fun c => .ctorInfo c.1 p₀.nP c.2) ∧
      p₀.nP = nPd ∧
      p₀.large = false ∧
      Ix.Kernel.reservedBasisNames.contains p₀.cvT.name = false ∧
      (∀ c ∈ p₀.ctors, c.1.levelParams = p₀.cvT.levelParams ∧
        Ix.Kernel.reservedBasisNames.contains c.1.name = false) ∧
      (∃ bs₀, p₀.cvT.type.stripPis (p₀.nP + p₀.nIdx) = some (bs₀, .sort p₀.resSort)) ∧
      p₀.isProp = (Level.isEquiv p₀.resSort .zero == some true) := by
  cases block with
  | nil => simp [nativePartsNoRec?] at h
  | cons hd rest =>
    cases hd with
    | indInfo cvT caps₀ =>
      simp only [nativePartsNoRec?] at h
      split at h
      · next hall₀ =>
        have hall : (rest.all fun | .ctorInfo .. => true | _ => false) = true := by
          rw [List.all_eq_true] at hall₀ ⊢
          intro x hx
          have hx₀ := hall₀ x hx
          cases x <;> simp at hx₀ ⊢
        obtain ⟨hsh, _, _⟩ := nativeParts?_inv h
        obtain ⟨caps₁, rest₁, cs, mI, rP, rules, hblk, hsp, hcnt, hnP, hctors, _,
          hnbT, _, hcs, hctors_wf, hisProp, hres_eq, hlarge_fn⟩ := nativeShape?_inv hsh
        simp only [List.cons.injEq, ConstantInfo.indInfo.injEq] at hblk
        obtain ⟨⟨rfl, rfl⟩, hrest₁⟩ := hblk
        let stubR : KConstantVal :=
          { name := Ix.Kernel.auxKey p₀.cvT.name .recursor
            levelParams := p₀.cvT.levelParams
            type := .sort .zero }
        have hstub : nativeRecStub p₀.cvT = .recInfo stubR 0 0 [] := rfl
        obtain ⟨cs₀, hsp₀, hrest_eq⟩ := sumSplit_append_recStub rest stubR hall
        rw [hstub] at hrest₁
        rw [← hrest₁] at hsp
        rw [hsp₀] at hsp
        simp only [Option.some.injEq, Prod.mk.injEq] at hsp
        obtain ⟨rfl, hcvR_eq, rfl, rfl, rfl⟩ := hsp
        have hcvR_lps : p₀.cvR.levelParams = p₀.cvT.levelParams := by
          rw [← hcvR_eq]
        have hrest_map : rest = p₀.ctors.map (fun c => .ctorInfo c.1 p₀.nP c.2) := by
          rw [hrest_eq, hctors, List.map_map]
          apply List.map_congr_left
          intro c hc
          simp [(hcs c hc).1]
        have hlarge : p₀.large = false := by
          apply hlarge_fn
          intro elim heq
          rw [hcvR_lps] at heq
          have hlen := congrArg List.length heq
          simp at hlen
        have hstrip :
            ∃ bs₀, p₀.cvT.type.stripPis (p₀.nP + p₀.nIdx) = some (bs₀, .sort p₀.resSort) := by
          unfold Ix.Kernel.nativeCounts? at hcnt
          split at hcnt
          · next bs s₀ hpb =>
            split at hcnt
            · next hle =>
              simp only [Option.some.injEq, Prod.mk.injEq] at hcnt
              obtain ⟨hnP_cnt, hnIdx_cnt⟩ := hcnt
              have hst := stripPis_of_piBinders_sort p₀.cvT.type hpb
              have hst' :
                  p₀.cvT.type.stripPis (p₀.nP + p₀.nIdx) = some (bs, .sort s₀) := by
                rwa [show p₀.nP + p₀.nIdx = bs.length by omega]
              rw [hres_eq bs s₀ hst']
              exact ⟨bs, hst'⟩
            · exact nomatch hcnt
          · exfalso
            have hlt : (0 < cs₀.length + 1) = true := by simp
            simp [hlt] at hcnt
        exact ⟨caps₀, by rw [hrest_map], hnP, hlarge, hnbT, hctors_wf, hstrip, hisProp⟩
      · exact nomatch h
    | _ => simp [nativePartsNoRec?] at h

/-! ## Exact spine collection, ghost-context opening, and `compute_iprj_addr` -/

theorem tmExact_heapMono₂ {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {k : Nat} :
    HeapMono₂ (fun h E p => TmExact κ d Γ h k E p) :=
  fun _ _ _ _ ext rep => rep.mono ext

theorem mkAppN_append_singleton (H : KExpr) :
    ∀ (As : List KExpr) (a : KExpr),
      Expr.mkAppN H (As ++ [a]) = .app (Expr.mkAppN H As) a
  | [], _ => rfl
  | x :: xs, a => mkAppN_append_singleton (.app H x) xs a

/-- Pairwise heap representation relating a `SourceValue F` pointer simultaneously to its
raw heap syntax `R : KExpr` (preserving `"Let"` cells as `.letE RT RV RB default`) and its
ζ-expanded kernel term `E : KExpr` (`TmExact`). Every constructor of `RawTmExact` has a
distinct head constructor in `R`, so structural case analysis on `R` determines the exact
heap cell tag without `instShift` ambiguity. -/
inductive RawTmExact (κ : _root_.Address → KKey) (d : Nat) (Γ : Nat → KExpr) (h : Heap F) :
    Nat → KExpr → KExpr → SourceValue F → Prop where
  | bvarLocal {k addr : Nat} {i : F}
      (cell : h[addr]? = some (.construct kexprEnum "BVar" [.field i]))
      (hsmall : ZMod.val i < 9223372036854775808) (hi : ZMod.val i < k) :
      RawTmExact κ d Γ h k (.bvar (ZMod.val i)) (.bvar (ZMod.val i)) (.ptr (.enum kexprEnum) addr)
  | bvarFree {k addr : Nat} {i : F}
      (cell : h[addr]? = some (.construct kexprEnum "BVar" [.field i]))
      (hsmall : ZMod.val i < 9223372036854775808) (hk : k ≤ ZMod.val i)
      (hd : ZMod.val i - k < d) :
      RawTmExact κ d Γ h k
        (.fvar (fvIdx d k (ZMod.val i)) (Γ (fvIdx d k (ZMod.val i))))
        (.fvar (fvIdx d k (ZMod.val i)) (Γ (fvIdx d k (ZMod.val i))))
        (.ptr (.enum kexprEnum) addr)
  | sort {k addr : Nat} {lp : SourceValue F} {l : KLevel}
      (cell : h[addr]? = some (.construct kexprEnum "Srt" [lp]))
      (rl : RepKLevel h l lp) :
      RawTmExact κ d Γ h k (.sort l) (.sort l) (.ptr (.enum kexprEnum) addr)
  | const {k addr : Nat} {ap lsp : SourceValue F} {a : Bytes.Address} {ls : List KLevel}
      (cell : h[addr]? = some (.construct kexprEnum "Const" [ap, lsp]))
      (ra : Bytes.RepAddressRef addrTy h a ap) (rls : RepKLevelList h ls lsp) :
      RawTmExact κ d Γ h k (.const (κ (ixAddr a)) ls) (.const (κ (ixAddr a)) ls)
        (.ptr (.enum kexprEnum) addr)
  | app {k addr : Nat} {fp ap : SourceValue F} {Rf Ra Ef Ea : KExpr}
      (cell : h[addr]? = some (.construct kexprEnum "App" [fp, ap]))
      (rf : RawTmExact κ d Γ h k Rf Ef fp) (ra : RawTmExact κ d Γ h k Ra Ea ap) :
      RawTmExact κ d Γ h k (.app Rf Ra) (.app Ef Ea) (.ptr (.enum kexprEnum) addr)
  | lam {k addr : Nat} {tp bp lp : SourceValue F} {RT RB T B : KExpr} {ℓ : KLevel}
      (cell : h[addr]? = some (.construct kexprEnum "Lam" [tp, bp, lp]))
      (rt : RawTmExact κ d Γ h k RT T tp) (rb : RawTmExact κ d Γ h (k + 1) RB B bp)
      (rl : RepKLevel h ℓ lp) :
      RawTmExact κ d Γ h k (.lam RT RB (bmeta ℓ)) (.lam T B (bmeta ℓ))
        (.ptr (.enum kexprEnum) addr)
  | forallE {k addr : Nat} {tp bp lp : SourceValue F} {RT RB T B : KExpr} {ℓ : KLevel}
      (cell : h[addr]? = some (.construct kexprEnum "Forall" [tp, bp, lp]))
      (rt : RawTmExact κ d Γ h k RT T tp) (rb : RawTmExact κ d Γ h (k + 1) RB B bp)
      (rl : RepKLevel h ℓ lp) :
      RawTmExact κ d Γ h k (.forallE RT RB (bmeta ℓ)) (.forallE T B (bmeta ℓ))
        (.ptr (.enum kexprEnum) addr)
  | letE {k addr : Nat} {tp vp bp : SourceValue F} {RT RV RB T V B : KExpr}
      (cell : h[addr]? = some (.construct kexprEnum "Let" [tp, vp, bp]))
      (rt : RawTmExact κ d Γ h k RT T tp) (rv : RawTmExact κ d Γ h k RV V vp)
      (rb : RawTmExact κ d Γ h (k + 1) RB B bp) :
      RawTmExact κ d Γ h k (.letE RT RV RB default) (instShift V 0 B)
        (.ptr (.enum kexprEnum) addr)
  | litNat {k addr : Nat} {lp : SourceValue F} {limbs : List UInt64}
      (cell : h[addr]? = some (.construct kexprEnum "Lit" [.construct klitEnum "Nat" [lp]]))
      (rl : RepList limbListEnum RepU64 h limbs lp) (hc : limbs.getLast? ≠ some 0) :
      RawTmExact κ d Γ h k (.lit (.natVal (limbsVal limbs))) (.lit (.natVal (limbsVal limbs)))
        (.ptr (.enum kexprEnum) addr)
  | litStr {k addr : Nat} {bp : SourceValue F} {bytes : List UInt8} {s : String}
      (cell : h[addr]? = some (.construct kexprEnum "Lit" [.construct klitEnum "Str" [bp]]))
      (rb : Bytes.RepByteStream byteListEnum h bytes bp) (hs : StrBytes s bytes) :
      RawTmExact κ d Γ h k (.lit (.strVal s)) (.lit (.strVal s))
        (.ptr (.enum kexprEnum) addr)
  | proj {k addr : Nat} {ap ep : SourceValue F} {a : Bytes.Address} {i : F} {RE E : KExpr}
      (cell : h[addr]? = some (.construct kexprEnum "Proj" [ap, .field i, ep]))
      (ra : Bytes.RepAddressRef addrTy h a ap) (re : RawTmExact κ d Γ h k RE E ep) :
      RawTmExact κ d Γ h k (.proj (κ (ixAddr a)) (ZMod.val i) RE)
        (.proj (κ (ixAddr a)) (ZMod.val i) E) (.ptr (.enum kexprEnum) addr)

theorem RawTmExact.toTmExact {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {p : SourceValue F}
    (rep : RawTmExact κ d Γ h k R E p) : TmExact κ d Γ h k E p := by
  induction rep with
  | bvarLocal cell hs hi => exact .bvarLocal cell hs hi
  | bvarFree cell hs hk hd => exact .bvarFree cell hs hk hd
  | sort cell rl => exact .sort cell rl
  | const cell ra rls => exact .const cell ra rls
  | app cell _ _ ihf iha => exact .app cell ihf iha
  | lam cell _ _ rl iht ihb => exact .lam cell iht ihb rl
  | forallE cell _ _ rl iht ihb => exact .forallE cell iht ihb rl
  | letE cell _ _ _ iht ihv ihb => exact .letE cell iht ihv ihb
  | litNat cell rl hc => exact .litNat cell rl hc
  | litStr cell rb hs => exact .litStr cell rb hs
  | proj cell ra _ ihe => exact .proj cell ra ihe

theorem RawTmExact.mono {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h₁ h₂ : Heap F} {k : Nat} {R E : KExpr} {p : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (rep : RawTmExact κ d Γ h₁ k R E p) :
    RawTmExact κ d Γ h₂ k R E p := by
  induction rep with
  | bvarLocal cell hs hi => exact .bvarLocal (ext.getElem?_eq cell) hs hi
  | bvarFree cell hs hk hd => exact .bvarFree (ext.getElem?_eq cell) hs hk hd
  | sort cell rl => exact .sort (ext.getElem?_eq cell) (repKLevel_heapMono₂ ext rl)
  | const cell ra rls =>
    exact .const (ext.getElem?_eq cell)
      (Bytes.repAddressRef_heapMono₂ addrTy ext ra) (rls.mono ext)
  | app cell _ _ ihf iha => exact .app (ext.getElem?_eq cell) ihf iha
  | lam cell _ _ rl iht ihb =>
    exact .lam (ext.getElem?_eq cell) iht ihb (repKLevel_heapMono₂ ext rl)
  | forallE cell _ _ rl iht ihb =>
    exact .forallE (ext.getElem?_eq cell) iht ihb (repKLevel_heapMono₂ ext rl)
  | letE cell _ _ _ iht ihv ihb => exact .letE (ext.getElem?_eq cell) iht ihv ihb
  | litNat cell rl hc =>
    exact .litNat (ext.getElem?_eq cell)
      (repList_heapMono₂ limbListEnum repU64_heapMono₂ ext rl) hc
  | litStr cell rb hs =>
    exact .litStr (ext.getElem?_eq cell)
      (Bytes.repByteStream_heapMono₂ byteListEnum ext rb) hs
  | proj cell ra _ ihe =>
    exact .proj (ext.getElem?_eq cell) (Bytes.repAddressRef_heapMono₂ addrTy ext ra) ihe

theorem RawTmExact.forallE_of_load {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {p tp bp lp : SourceValue F}
    (rep : RawTmExact κ d Γ h k R E p)
    (ld : loadValue h p = .ok (.construct kexprEnum "Forall" [tp, bp, lp])) :
    ∃ RT RB T B ℓ,
      R = .forallE RT RB (bmeta ℓ) ∧
      E = .forallE T B (bmeta ℓ) ∧
      RawTmExact κ d Γ h k RT T tp ∧
      RawTmExact κ d Γ h (k + 1) RB B bp ∧
      RepKLevel h ℓ lp := by
  cases rep with
  | forallE cell rt rb rl =>
    obtain ⟨-, hxs⟩ := load_cell cell ld
    injection hxs with h1 hxs; injection hxs with h2 hxs; injection hxs with h3
    subst h1 h2 h3
    exact ⟨_, _, _, _, _, rfl, rfl, rt, rb, rl⟩
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ | const cell _ _
  | app cell _ _ | lam cell _ _ _ | letE cell _ _ _ | litNat cell _ _
  | litStr cell _ _ | proj cell _ _ =>
    exact (load_cell_ne cell ld (by decide)).elim

theorem RawTmExact.not_forallE_of_load {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {p v : SourceValue F}
    (rep : RawTmExact κ d Γ h k R E p)
    (ld : loadValue h p = .ok v)
    (hne : ∀ vs : List (SourceValue F), vs.length = 3 → v ≠ .construct kexprEnum "Forall" vs) :
    ∀ RT RB RM, R ≠ .forallE RT RB RM := by
  intro RT RB RM hEq
  subst hEq
  cases rep with
  | forallE cell _ _ _ =>
    rw [loadValue_enum_cell cell] at ld
    injection ld with hv
    exact hne [_, _, _] rfl hv.symm

theorem RawTmExact.app_of_load {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {p fp ap : SourceValue F}
    (rep : RawTmExact κ d Γ h k R E p)
    (ld : loadValue h p = .ok (.construct kexprEnum "App" [fp, ap])) :
    ∃ Rf Ra Ef Ea,
      R = .app Rf Ra ∧
      E = .app Ef Ea ∧
      RawTmExact κ d Γ h k Rf Ef fp ∧
      RawTmExact κ d Γ h k Ra Ea ap := by
  cases rep with
  | app cell rf ra =>
    obtain ⟨-, hxs⟩ := load_cell cell ld
    injection hxs with h1 hxs; injection hxs with h2
    subst h1 h2
    exact ⟨_, _, _, _, rfl, rfl, rf, ra⟩
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ | const cell _ _
  | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _
  | litStr cell _ _ | proj cell _ _ =>
    exact (load_cell_ne cell ld (by decide)).elim

theorem RawTmExact.const_of_load {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {h : Heap F} {k : Nat} {R E : KExpr} {p ap lsp : SourceValue F}
    (rep : RawTmExact κ d Γ h k R E p)
    (ld : loadValue h p = .ok (.construct kexprEnum "Const" [ap, lsp])) :
    ∃ a ls,
      R = .const (κ (ixAddr a)) ls ∧
      E = .const (κ (ixAddr a)) ls ∧
      Bytes.RepAddressRef addrTy h a ap ∧
      RepKLevelList h ls lsp := by
  cases rep with
  | const cell ra rls =>
    obtain ⟨-, hxs⟩ := load_cell cell ld
    injection hxs with h1 hxs; injection hxs with h2
    subst h1 h2
    exact ⟨_, _, rfl, rfl, ra, rls⟩
  | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ | app cell _ _
  | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _
  | litStr cell _ _ | proj cell _ _ =>
    exact (load_cell_ne cell ld (by decide)).elim

theorem collect_spine_raw_spec {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {k : Nat} {R E : KExpr} {pe r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hRaw : RawTmExact κ d Γ h k R E pe)
    (ev : ObsFn W "KernelTypes::collect_spine" [pe] h r h' cs) :
    ∃ hd sp RH EH RAs As,
      r = .tuple [hd, sp] ∧
      RawTmExact κ d Γ h' k RH EH hd ∧
      (∀ rf ra, RH ≠ .app rf ra) ∧
      RepList kexprListEnum (fun h₀ X p₀ => TmExact κ d Γ h₀ k X p₀) h' As sp ∧
      R = Expr.mkAppN RH RAs ∧
      E = Expr.mkAppN EH As := by
  match Obs.«KernelTypes::collect_spine».obs ev with
  | .App (ld12 := ld) (ev43 := e1) (he69 := hr) (ev88 := e2) (he105 := he) .. =>
    subst hr he
    obtain ⟨Rf, Ra, Ef, Ea, rfl, rfl, hf, ha⟩ := hRaw.app_of_load ld
    obtain ⟨hd, sp, RH, EH, RAs, As, htup, hH, hna, hAs, rfl, rfl⟩ :=
      collect_spine_raw_spec hf e1
    injection htup with hl; injection hl with h1 hl; injection hl with h2; subst h1 h2
    refine ⟨_, _, RH, EH, RAs ++ [Ra], As ++ [Ea], rfl, hH.mono e2.heap_extends, hna, ?_,
      (mkAppN_append_singleton RH RAs Ra).symm, (mkAppN_append_singleton EH As Ea).symm⟩
    exact SubstAux.ksnoc tmExact_heapMono₂ e2 hAs (ha.toTmExact.mono e1.heap_extends)
  | .other (v1 := v1) (ld12 := ld) (hne107 := hne) (he115 := hr) (hm132 := hm) (he136 := he) .. =>
    subst hr hm he
    have hna : ∀ rf ra, R ≠ .app rf ra := by
      intro rf ra hEq
      subst hEq
      cases hRaw with
      | app cell _ _ =>
        rw [loadValue_enum_cell cell] at ld
        injection ld with hv
        exact hne [_, _] rfl hv.symm
    exact ⟨pe, _, R, E, [], [], rfl, hRaw.mono (Heap.Extends.snoc _ _), hna, .nil (by simp),
      rfl, rfl⟩

theorem collect_spine_exact_spec {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {k : Nat} {E : KExpr} {pe r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hE : TmExact κ d Γ h k E pe)
    (ev : ObsFn W "KernelTypes::collect_spine" [pe] h r h' cs) :
    ∃ hd sp H As,
      r = .tuple [hd, sp] ∧
      TmExact κ d Γ h' k H hd ∧
      RepList kexprListEnum (fun h₀ X p₀ => TmExact κ d Γ h₀ k X p₀) h' As sp ∧
      E = Expr.mkAppN H As := by
  match Obs.«KernelTypes::collect_spine».obs ev with
  | .App (ld12 := ld) (ev43 := e1) (he69 := hr) (ev88 := e2) (he105 := he) .. =>
    subst hr he
    obtain ⟨Ef, Ea, rfl, hf, ha⟩ := hE.app_of_load ld
    obtain ⟨hd, sp, H, As, htup, hH, hAs, rfl⟩ := collect_spine_exact_spec hf e1
    injection htup with hl; injection hl with h1 hl; injection hl with h2; subst h1 h2
    refine ⟨_, _, H, As ++ [Ea], rfl, hH.mono e2.heap_extends, ?_,
      (mkAppN_append_singleton H As Ea).symm⟩
    exact SubstAux.ksnoc tmExact_heapMono₂ e2 hAs (ha.mono e1.heap_extends)
  | .other (he115 := hr) (hm132 := hm) (he136 := he) .. =>
    subst hr hm he
    exact ⟨pe, _, E, [], rfl, hE.mono (Heap.Extends.snoc _ _), .nil (by simp), rfl⟩

theorem TypesRep.mono_congr {κ : _root_.Address → KKey} {h₁ h₂ : Heap F}
    {d : Nat} {Γ Γ' : Nat → KExpr} {p : SourceValue F}
    (ext : Heap.Extends h₁ h₂)
    (hΓ : ∀ j, j < d → Γ' j = Γ j)
    (rr : TypesRep κ Γ h₁ d p) :
    TypesRep κ Γ' h₂ d p := by
  induction rr generalizing Γ' with
  | nil cell => exact .nil (ext.getElem?_eq cell)
  | @cons d₀ _ tp _ cell rt _ ih =>
    have hΓd : Γ' d₀ = Γ d₀ := hΓ d₀ (Nat.lt_succ_self d₀)
    have hΓ_sub : ∀ j, j < d₀ → Γ' j = Γ j := fun j hj => hΓ j (Nat.lt_succ_of_lt hj)
    have rt' : Tm κ d₀ Γ' h₂ 0 (Γ' d₀) tp := by
      rw [hΓd]
      exact (rt.mono ext).congr_ghost hΓ_sub
    exact .cons (ext.getElem?_eq cell) rt' (ih hΓ_sub)

/-- Push one opened binder domain `dom` onto `types` at depth `d`, updating `Γ` to
`Ghost.extend Γ d dom`. -/
theorem push_binder_types {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {h : Heap F}
    {d : Nat} {dom : KExpr} {pdom types : SourceValue F}
    (hdom : Tm κ d Γ h 0 dom pdom)
    (htypes : TypesRep κ Γ h d types)
    (hsc : GhostScoped Γ d) :
    let h' := h ++ [.construct kexprListEnum "Cons" [pdom, types]]
    let Γ' := Ghost.extend Γ d dom
    Heap.Extends h h' ∧
      TypesRep κ Γ' h' (d + 1) (.ptr (.enum kexprListEnum) h.length) ∧
      GhostScoped Γ' (d + 1) := by
  have ext : Heap.Extends h (h ++ [.construct kexprListEnum "Cons" [pdom, types]]) :=
    Heap.Extends.snoc h _
  have hsc_dom : dom.wscopedB d = true := hdom.wscopedB hsc
  have hdom' : Tm κ d (Ghost.extend Γ d dom)
      (h ++ [.construct kexprListEnum "Cons" [pdom, types]]) 0
      (Ghost.extend Γ d dom d) pdom := by
    rw [Ghost.extend_at]
    exact (hdom.mono ext).congr_ghost (Ghost.extend_below Γ d dom)
  have htypes' := TypesRep.mono_congr ext (Ghost.extend_below Γ d dom) htypes
  exact ⟨ext, .cons (by simp) hdom' htypes', hsc.extend hsc_dom⟩

/-- Standalone `KernelDefEq::compute_iprj_addr` specification under `Good`. -/
theorem compute_iprj_addr_spec {c : Ctx} {bp : SourceValue F} {b : Bytes.Address}
    {idx : Nat} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hidx : idx < 4294967296)
    (hb : Bytes.RepAddressRef addrTy h b bp)
    (hgood : Good c cs)
    (ev : ObsFn W "KernelDefEq::compute_iprj_addr" [bp, .field (idx : F)] h r h' cs) :
    ∃ a : Bytes.Address, Bytes.RepAddressRef addrTy h' a r ∧
      ixAddr a = iprjAddr (ixAddr b) idx := by
  obtain ⟨v1, m2, cs12, m84, m97, m110, m123, v135, m136, cs146, m159, cs174,
    ev14, hm92, hm105, hm118, hm131, hm167, ev148, ev176, hc185⟩ :=
    Obs.«KernelDefEq::compute_iprj_addr».obs ev
  obtain ⟨n, hn, hx, rfl, hm2⟩ := Lib.u64_from_field_spec ev14
  injection hx with hx
  have hval_idx : ZMod.val (idx : F) = idx :=
    ZMod.val_natCast_of_lt (Nat.lt_trans hidx (by decide))
  have hval_n : ZMod.val (idx : F) = n := by
    rw [hx]
    exact ZMod.val_natCast_of_lt (Nat.lt_trans hn (by decide))
  have hn_eq : idx = n := hval_idx.symm.trans hval_n
  have e1 : Heap.Extends m2 m84 := by rw [hm92]; exact Heap.Extends.snoc _ _
  have e2 : Heap.Extends m84 m97 := by rw [hm105]; exact Heap.Extends.snoc _ _
  have e3 : Heap.Extends m97 m110 := by rw [hm118]; exact Heap.Extends.snoc _ _
  have e4 : Heap.Extends m110 m123 := by rw [hm131]; exact Heap.Extends.snoc _ _
  have e5 : Heap.Extends m123 m159 := by rw [hm167]; exact Heap.Extends.snoc _ _
  have E : Heap.Extends h m159 := by
    rw [← hm2]
    exact e1.trans (e2.trans (e3.trans (e4.trans e5)))
  have c1 : m159[m2.length]? = some (.construct Specs.Callees.ixExprListEnum "Nil" []) :=
    (e2.trans (e3.trans (e4.trans e5))).getElem?_eq (by rw [hm92]; simp)
  have c2 : m159[m84.length]? = some (.construct addrListEnum "Nil" []) :=
    (e3.trans (e4.trans e5)).getElem?_eq (by rw [hm105]; simp)
  have c3 : m159[m97.length]? = some (.construct Specs.Callees.ixUnivListEnum "Nil" []) :=
    (e4.trans e5).getElem?_eq (by rw [hm118]; simp)
  have c4 : m159[m110.length]? = some (.construct Specs.Callees.ixBinderListEnum "Nil" []) :=
    e5.getElem?_eq (by rw [hm131]; simp)
  have c5 : m159[m123.length]? = some (.construct byteListEnum "Nil" []) := by
    rw [hm167]; simp
  have hrep : RepU64 m159 idx.toUInt64 (TagN.u64Value n) := by
    rw [hn_eq]
    have e := Lib.repU64_ofNatLT m159 (m := n) (Nat.lt_trans hn (by decide))
    rwa [UInt64.ofNatLT_eq_ofNat] at e
  have hinfo : Specs.Callees.ProjInfoRep m159 (.iPrj ⟨idx.toUInt64, ixAddr b⟩)
      (.construct "Ixon::ConstantInfo" "IPrj"
        [.construct "Ixon::InductiveProj" "Mk" [TagN.u64Value n, bp]]) := by
    simp only [Specs.Callees.ProjInfoRep]
    exact ⟨TagN.u64Value n, bp, b, rfl, hrep, Bytes.repAddressRef_heapMono₂ addrTy E hb, rfl⟩
  have hbytes := put_constant_step c ev148 _ _
    (.iPrj ⟨idx.toUInt64, ixAddr b⟩) [] rfl
    ⟨_, _, _, _, _, rfl, hinfo, RepLinkedList.nil c1, RepLinkedList.nil c2,
      RepLinkedList.nil c3, RepLinkedList.nil c4⟩
    (RepLinkedList.nil c5)
  have hgood_bta : Good c cs174 :=
    hgood.sub (by rw [hc185]; intro x hx; simp [hx])
  obtain ⟨a, ha, haddr⟩ := bytes_to_addr_step c ev176 v135 _ rfl hgood_bta hbytes
  refine ⟨a, ha, ?_⟩
  rw [haddr, ProjAddrAux.bytes_mk_toList]
  rfl

/-! ## `noProjAt` and `mentionsConst` across `instantiate1Lift` (`Let` ζ-reduction) -/

theorem noProjAt_liftLooseBVars (T : KKey) :
    ∀ (e : KExpr) (s n : Nat), noProjAt T (e.liftLooseBVars s n) = noProjAt T e
  | .bvar _, _, _ => by simp only [Expr.liftLooseBVars]; split <;> rfl
  | .fvar _ _, _, _ | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, s, n => by
    simp [Expr.liftLooseBVars, noProjAt, noProjAt_liftLooseBVars T f s n,
      noProjAt_liftLooseBVars T a s n]
  | .lam ty bo _, s, n | .forallE ty bo _, s, n => by
    simp [Expr.liftLooseBVars, noProjAt, noProjAt_liftLooseBVars T ty s n,
      noProjAt_liftLooseBVars T bo s (n + 1)]
  | .letE ty v bo _, s, n => by
    simp [Expr.liftLooseBVars, noProjAt, noProjAt_liftLooseBVars T ty s n,
      noProjAt_liftLooseBVars T v s n, noProjAt_liftLooseBVars T bo s (n + 1)]
  | .proj _ _ e, s, n => by
    simp [Expr.liftLooseBVars, noProjAt, noProjAt_liftLooseBVars T e s n]

theorem noProjAt_of_instantiate1Lift {T : KKey} {v : KExpr} :
    ∀ {e : KExpr} {s : Nat},
      noProjAt T (e.instantiate1Lift v s) = true →
      noProjAt T e = true ∧ (e.hasLooseBVar s = true → noProjAt T v = true)
  | .bvar i, s, h => by
    simp only [Expr.instantiate1Lift] at h
    by_cases his : i = s
    · subst his
      simp only [↓reduceIte, noProjAt_liftLooseBVars] at h
      exact ⟨rfl, fun _ => h⟩
    · refine ⟨rfl, fun hb => ?_⟩
      simp only [Expr.hasLooseBVar, beq_iff_eq] at hb
      exact absurd hb.symm his
  | .fvar _ _, _, h => ⟨h, fun hb => nomatch hb⟩
  | .sort _, _, _ => ⟨rfl, fun hb => nomatch hb⟩
  | .const _ _, _, _ => ⟨rfl, fun hb => nomatch hb⟩
  | .lit _, _, _ => ⟨rfl, fun hb => nomatch hb⟩
  | .app f a, s, h => by
    simp only [Expr.instantiate1Lift, noProjAt, Bool.and_eq_true] at h
    obtain ⟨hf, hvf⟩ := noProjAt_of_instantiate1Lift h.1
    obtain ⟨ha, hva⟩ := noProjAt_of_instantiate1Lift h.2
    refine ⟨by simp [noProjAt, hf, ha], fun hb => ?_⟩
    simp only [Expr.hasLooseBVar, Bool.or_eq_true] at hb
    rcases hb with hb | hb
    · exact hvf hb
    · exact hva hb
  | .lam ty bo _, s, h => by
    simp only [Expr.instantiate1Lift, noProjAt, Bool.and_eq_true] at h
    obtain ⟨hty, hvty⟩ := noProjAt_of_instantiate1Lift h.1
    obtain ⟨hbo, hvbo⟩ := noProjAt_of_instantiate1Lift h.2
    refine ⟨by simp [noProjAt, hty, hbo], fun hb => ?_⟩
    simp only [Expr.hasLooseBVar, Bool.or_eq_true] at hb
    rcases hb with hb | hb
    · exact hvty hb
    · exact hvbo hb
  | .forallE ty bo _, s, h => by
    simp only [Expr.instantiate1Lift, noProjAt, Bool.and_eq_true] at h
    obtain ⟨hty, hvty⟩ := noProjAt_of_instantiate1Lift h.1
    obtain ⟨hbo, hvbo⟩ := noProjAt_of_instantiate1Lift h.2
    refine ⟨by simp [noProjAt, hty, hbo], fun hb => ?_⟩
    simp only [Expr.hasLooseBVar, Bool.or_eq_true] at hb
    rcases hb with hb | hb
    · exact hvty hb
    · exact hvbo hb
  | .letE ty val bo _, s, h => by
    simp only [Expr.instantiate1Lift, noProjAt, Bool.and_eq_true] at h
    obtain ⟨hty, hvty⟩ := noProjAt_of_instantiate1Lift h.1.1
    obtain ⟨hval, hvval⟩ := noProjAt_of_instantiate1Lift h.1.2
    obtain ⟨hbo, hvbo⟩ := noProjAt_of_instantiate1Lift h.2
    refine ⟨by simp [noProjAt, hty, hval, hbo], fun hb => ?_⟩
    simp only [Expr.hasLooseBVar, Bool.or_eq_true] at hb
    rcases hb with (hb | hb) | hb
    · exact hvty hb
    · exact hvval hb
    · exact hvbo hb
  | .proj sn idx e, s, h => by
    simp only [Expr.instantiate1Lift, noProjAt, Bool.and_eq_true] at h
    obtain ⟨he, hve⟩ := noProjAt_of_instantiate1Lift h.2
    exact ⟨by simp [noProjAt, h.1, he], hve⟩

theorem mentionsConst_liftLooseBVars (T : KKey) :
    ∀ (e : KExpr) (s n : Nat),
      (e.liftLooseBVars s n).mentionsConst T = e.mentionsConst T
  | .bvar _, _, _ => by simp only [Expr.liftLooseBVars]; split <;> rfl
  | .fvar _ _, _, _ | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, s, n => by
    simp [Expr.liftLooseBVars, Expr.mentionsConst,
      mentionsConst_liftLooseBVars T f s n, mentionsConst_liftLooseBVars T a s n]
  | .lam ty bo _, s, n | .forallE ty bo _, s, n => by
    simp [Expr.liftLooseBVars, Expr.mentionsConst,
      mentionsConst_liftLooseBVars T ty s n, mentionsConst_liftLooseBVars T bo s (n + 1)]
  | .letE ty v bo _, s, n => by
    simp [Expr.liftLooseBVars, Expr.mentionsConst,
      mentionsConst_liftLooseBVars T ty s n, mentionsConst_liftLooseBVars T v s n,
      mentionsConst_liftLooseBVars T bo s (n + 1)]
  | .proj _ _ e, s, n => by
    simp [Expr.liftLooseBVars, Expr.mentionsConst, mentionsConst_liftLooseBVars T e s n]

theorem mentionsConst_instantiate1Lift_false {T : KKey} {v : KExpr} :
    ∀ {e : KExpr} {s : Nat},
      e.mentionsConst T = false →
      (e.hasLooseBVar s = true → v.mentionsConst T = false) →
      (e.instantiate1Lift v s).mentionsConst T = false
  | .bvar i, s, _, hv => by
    simp only [Expr.instantiate1Lift]
    by_cases his : i = s
    · subst his
      simp only [↓reduceIte, mentionsConst_liftLooseBVars]
      exact hv (by simp [Expr.hasLooseBVar])
    · rw [ite_eq_right his]
      split <;> rfl
  | .fvar _ _, _, he, _ => he
  | .sort _, _, _, _ | .lit _, _, _, _ => rfl
  | .const _ _, _, he, _ => he
  | .app f a, s, he, hv => by
    simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at he
    simp only [Expr.instantiate1Lift, Expr.mentionsConst, Bool.or_eq_false_iff]
    exact ⟨mentionsConst_instantiate1Lift_false he.1 (fun hb => hv (by simp [Expr.hasLooseBVar, hb])),
      mentionsConst_instantiate1Lift_false he.2 (fun hb => hv (by simp [Expr.hasLooseBVar, hb]))⟩
  | .lam ty bo _, s, he, hv | .forallE ty bo _, s, he, hv => by
    simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at he
    simp only [Expr.instantiate1Lift, Expr.mentionsConst, Bool.or_eq_false_iff]
    exact ⟨mentionsConst_instantiate1Lift_false he.1 (fun hb => hv (by simp [Expr.hasLooseBVar, hb])),
      mentionsConst_instantiate1Lift_false he.2 (fun hb => hv (by simp [Expr.hasLooseBVar, hb]))⟩
  | .letE ty val bo _, s, he, hv => by
    simp only [Expr.instantiate1Lift, Expr.mentionsConst, Bool.or_eq_false_iff] at he ⊢
    refine ⟨⟨mentionsConst_instantiate1Lift_false he.1.1
        (fun hb => hv (by simp [Expr.hasLooseBVar, hb])),
      mentionsConst_instantiate1Lift_false he.1.2
        (fun hb => hv (by simp [Expr.hasLooseBVar, hb]))⟩,
      mentionsConst_instantiate1Lift_false he.2
        (fun hb => hv (by simp [Expr.hasLooseBVar, hb]))⟩
  | .proj sn idx e, s, he, hv => by
    simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at he
    simp only [Expr.instantiate1Lift, Expr.mentionsConst, Bool.or_eq_false_iff]
    exact ⟨he.1, mentionsConst_instantiate1Lift_false he.2 hv⟩

/-! ## Block-mention and peer-inductive specs (`addr_list_contains`, `caddr_is_peer`,
`expr_mentions_block`, `list_any_mentions_block`) -/

/-- Record-load correspondence for the single inductive member `T` of a one-type block `b₀`
at context `c`. -/
structure OneTypePeerFacts (c : Ctx) (b₀ : Bytes.Address) (T : KKey)
    (nl nP nIdx nCtors : Nat) : Prop where
  self_key : T = c.κ (iprjAddr (ixAddr b₀) 0)
  self_ind : ∀ (addr ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F))
      (a : Bytes.Address),
    ObsFn W "Ingress::get_ci" [addr] h ptr h' cs →
    Good c cs →
    Bytes.RepAddressRef addrTy h a addr →
    c.κ (ixAddr a) = T →
    ∃ (ty u blk : SourceValue F) (b' : Bytes.Address),
      loadValue h' ptr = .ok (.construct kciEnum "Induct"
        [.field (nl : F), ty, .field (nP : F), .field (nIdx : F), .field (nCtors : F),
          u, blk, .field 0]) ∧
      Bytes.RepAddressRef addrTy h' b' blk ∧
      ixAddr b' = ixAddr b₀
  peer_only_self : ∀ (a : Bytes.Address) (cm : Ixon.Constant) (idx : UInt64),
    Ix.Cert.recordAt c.E (ixAddr a) = some cm →
    cm.info = .iPrj ⟨idx, ixAddr b₀⟩ →
    c.κ (ixAddr a) = T

theorem ixAddr_inj {a₁ a₂ : Bytes.Address} (h : ixAddr a₁ = ixAddr a₂) : a₁ = a₂ :=
  Vector.toArray_inj.mp (congrArg (fun x : _root_.Address => x.hash.data) h)

theorem repAddressRef_ixAddr_unique {h : Heap F} {b₁ b₂ : Bytes.Address} {p : SourceValue F}
    (h₁ : Bytes.RepAddressRef addrTy h b₁ p) (h₂ : Bytes.RepAddressRef addrTy h b₂ p) :
    ixAddr b₁ = ixAddr b₂ :=
  congrArg ixAddr (Bytes.repAddressRef_inj Aiur.Library.U32.Goldilocks.compatible h₁ h₂)

theorem addr_list_contains_ret_bit {xs target r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W "KernelCheck::addr_list_contains" [xs, target] h r h' cs) :
    r = .field 0 ∨ r = .field 1 := by
  match Obs.«KernelCheck::addr_list_contains».obs ev with
  | .Nil (he20 := hr) .. => exact Or.inl hr
  | .Cons_n1 (he75 := hr) .. => exact Or.inr hr
  | .Cons_other (ev87 := ev') (hc104 := hc) .. =>
    exact addr_list_contains_ret_bit ev'
termination_by cs.length
decreasing_by
  simp only [hc, List.length_cons, List.length_append]
  omega

theorem caddr_is_peer_ret_bit {ca bas r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W "KernelCheck::caddr_is_peer" [ca, bas] h r h' cs) :
    r = .field 0 ∨ r = .field 1 := by
  match Obs.«KernelCheck::caddr_is_peer».obs ev with
  | .Induct (ev94 := ev') .. => exact addr_list_contains_ret_bit ev'
  | .other (he116 := hr) .. => exact Or.inl hr

theorem expr_mentions_block_ret_bit {e bas r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W "KernelCheck::expr_mentions_block" [e, bas] h r h' cs) :
    r = .field 0 ∨ r = .field 1 := by
  match Obs.«KernelCheck::expr_mentions_block».obs ev with
  | .BVar (he26 := hr) .. | .Srt (he42 := hr) .. | .Lit (he486 := hr) .. => exact Or.inl hr
  | .Const (ev68 := ev') .. => exact caddr_is_peer_ret_bit ev'
  | .App_n1 (he138 := hr) .. | .Lam_n1 (he226 := hr) .. | .Forall_n1 (he314 := hr) ..
  | .Let_n1 (he401 := hr) .. | .Let_other_n1 (he443 := hr) .. => exact Or.inr hr
  | .App_other (ev150 := ev') (hc167 := hc) ..
  | .Lam_other (ev238 := ev') (hc255 := hc) ..
  | .Forall_other (ev326 := ev') (hc343 := hc) ..
  | .Let_other_other (ev455 := ev') (hc472 := hc) ..
  | .Proj (ev518 := ev') (hc535 := hc) .. =>
    exact expr_mentions_block_ret_bit ev'
termination_by cs.length
decreasing_by
  all_goals
    simp only [hc, List.length_cons, List.length_append]
    omega

theorem list_any_mentions_block_ret_bit {es bas r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W "KernelCheck::list_any_mentions_block" [es, bas] h r h' cs) :
    r = .field 0 ∨ r = .field 1 := by
  match Obs.«KernelCheck::list_any_mentions_block».obs ev with
  | .Nil (he20 := hr) .. => exact Or.inl hr
  | .Cons_n1 (he75 := hr) .. => exact Or.inr hr
  | .Cons_other (ev87 := ev') (hc104 := hc) .. =>
    exact list_any_mentions_block_ret_bit ev'
termination_by cs.length
decreasing_by
  simp only [hc, List.length_cons, List.length_append]
  omega

theorem addr_list_contains_singleton_spec {b₀ b' : Bytes.Address} {bas tgt r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hbas : RepList addrListEnum (Bytes.RepAddressRef addrTy) h [b₀] bas)
    (htgt : Bytes.RepAddressRef addrTy h b' tgt)
    (ev : ObsFn W "KernelCheck::addr_list_contains" [bas, tgt] h r h' cs) :
    h' = h ∧ ((r = .field 1 ∧ ixAddr b' = ixAddr b₀) ∨ (r = .field 0 ∧ ixAddr b' ≠ ixAddr b₀)) := by
  cases hbas with
  | cons cell_cons hb₀ hnil =>
    match Obs.«KernelCheck::addr_list_contains».obs ev with
    | .Nil (ld12 := ld) .. =>
      exact (load_cell_ne cell_cons ld (by decide)).elim
    | .Cons_n1 (ld12 := ld) (ev54 := ev_eq) (he75 := hr) (he76 := hh) .. =>
      obtain ⟨-, hxs⟩ := load_cell cell_cons ld
      injection hxs with h1 h2; injection h2 with h2; subst h1 h2
      obtain ⟨heq_v, rfl⟩ := Lib.address_eq_spec ev_eq hb₀ htgt
      have hb_eq : b₀ = b' := by
        by_cases hab : b₀ = b'
        · exact hab
        · rw [ite_eq_right hab] at heq_v
          exact absurd (Value.field.inj heq_v) one_ne_zero
      subst hb_eq
      exact ⟨hh, Or.inl ⟨hr, rfl⟩⟩
    | .Cons_other (v40 := v40) (ld12 := ld) (ev54 := ev_eq) (hne78 := hne)
        (ev87 := ev_rest) .. =>
      obtain ⟨-, hxs⟩ := load_cell cell_cons ld
      injection hxs with h1 h2; injection h2 with h2; subst h1 h2
      obtain ⟨heq_v, rfl⟩ := Lib.address_eq_spec ev_eq hb₀ htgt
      have hne_addr : ixAddr b' ≠ ixAddr b₀ := by
        intro hsame
        have hb_eq : b₀ = b' := (ixAddr_inj hsame).symm
        rw [ite_eq_left hb_eq] at heq_v
        exact hne heq_v
      cases hnil with
      | nil cell_nil =>
        match Obs.«KernelCheck::addr_list_contains».obs ev_rest with
        | .Nil (he20 := hr) (he21 := hh) .. =>
          exact ⟨hh, Or.inr ⟨hr, hne_addr⟩⟩
        | .Cons_n1 (ld12 := ld') .. | .Cons_other (ld12 := ld') .. =>
          exact (load_cell_ne cell_nil ld' (by decide)).elim

theorem caddr_is_peer_singleton_spec {c : Ctx} {b₀ a : Bytes.Address} {T : KKey}
    {nl nP nIdx nCtors : Nat} {ca bas r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hpeer : OneTypePeerFacts c b₀ T nl nP nIdx nCtors)
    (hlf : LoadFacts c)
    (hgood : Good c cs)
    (hca : Bytes.RepAddressRef addrTy h a ca)
    (hbas : RepList addrListEnum (Bytes.RepAddressRef addrTy) h [b₀] bas)
    (ev : ObsFn W "KernelCheck::caddr_is_peer" [ca, bas] h r h' cs) :
    (r = .field 1 ∧ c.κ (ixAddr a) = T) ∨ (r = .field 0 ∧ c.κ (ixAddr a) ≠ T) := by
  match Obs.«KernelCheck::caddr_is_peer».obs ev with
  | .Induct (m2 := m2) (p9 := p9) (cs15 := cs15) (x_ba := xba) (ev17 := ev_ci)
      (ld11 := ld) (ev94 := ev_in) (hc111 := hc) .. =>
    subst hc
    have hg1 : Good c cs15 := hgood.sub (fun x hx => by simp [hx])
    obtain ⟨cm, b', idx, hcm, hb', rfl, hinfo⟩ :=
      hlf.inductRecord ca p9 h m2 cs15 a _ _ _ _ _ _ _ _ ev_ci hg1 hca ld
    have hbas' := repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy)
      ev_ci.heap_extends hbas
    obtain ⟨_, hres⟩ := addr_list_contains_singleton_spec hbas' hb' ev_in
    rcases hres with ⟨hr1, heq⟩ | ⟨hr0, hne⟩
    · rw [heq] at hinfo
      exact Or.inl ⟨hr1, hpeer.peer_only_self a cm _ hcm hinfo⟩
    · refine Or.inr ⟨hr0, fun hT => ?_⟩
      obtain ⟨_, _, blk', b'', ld', hb'', hix⟩ := hpeer.self_ind ca p9 h m2 cs15 a ev_ci hg1 hca hT
      rw [ld] at ld'
      simp only [Except.ok.injEq, Value.construct.injEq, List.cons.injEq] at ld'
      obtain ⟨-, -, -, -, -, -, -, -, hblk, -⟩ := ld'
      subst hblk
      exact hne ((repAddressRef_ixAddr_unique hb' hb'').trans hix)
  | .other (v1 := v1) (m2 := m2) (p9 := p9) (cs15 := cs15) (ev17 := ev_ci)
      (ld11 := ld) (hne112 := hne_ind) (he116 := hr) (hc118 := hc) .. =>
    subst hc
    have hg1 : Good c cs15 := hgood.sub (fun x hx => by simp [hx])
    refine Or.inr ⟨hr, fun hT => ?_⟩
    obtain ⟨ty', u', blk', b'', ld', _, _⟩ := hpeer.self_ind ca p9 h m2 cs15 a ev_ci hg1 hca hT
    rw [ld] at ld'
    injection ld' with hv1
    exact hne_ind [_, ty', _, _, _, u', blk', _] rfl hv1

theorem expr_mentions_block_zero_spec {c : Ctx} {b₀ : Bytes.Address} {T : KKey}
    {nl nP nIdx nCtors : Nat} {Γ : Nat → KExpr}
    {k : Nat} {E : KExpr} {pe bas : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hpeer : OneTypePeerFacts c b₀ T nl nP nIdx nCtors)
    (hlf : LoadFacts c)
    (hgood : Good c cs)
    (hE : TmExact c.κ 0 Γ h k E pe)
    (hnp : noProjAt T E = true)
    (hbas : RepList addrListEnum (Bytes.RepAddressRef addrTy) h [b₀] bas)
    (ev : ObsFn W "KernelCheck::expr_mentions_block" [pe, bas] h (.field 0) h' cs) :
    E.mentionsConst T = false := by
  match Obs.«KernelCheck::expr_mentions_block».obs ev with
    | .BVar (ld12 := ld) .. =>
      obtain ⟨i, rfl, _, hcases⟩ := hE.bvar_of_load ld
      rcases hcases with ⟨_, rfl⟩ | ⟨_, hd, _⟩
      · rfl
      · omega
    | .Srt (ld12 := ld) .. =>
      obtain ⟨_, rfl, _⟩ := hE.sort_of_load ld
      rfl
    | .Lit (ld12 := ld) .. =>
      rcases hE.lit_of_load ld with ⟨_, _, _, rfl, _⟩ | ⟨_, _, _, _, rfl, _, _⟩ <;> rfl
    | .Const (cs66 := cs66) (ld12 := ld) (ev68 := ev_peer) (hc85 := hc) .. =>
      subst hc
      obtain ⟨a, ls, rfl, ha, _⟩ := hE.const_of_load ld
      have hg1 : Good c cs66 := hgood.sub (fun x hx => by simp [hx])
      rcases caddr_is_peer_singleton_spec hpeer hlf hg1 ha hbas ev_peer with
        ⟨h01, _⟩ | ⟨_, hne⟩
      · exact nomatch h01
      · simp [Expr.mentionsConst, hne]
    | .App_n1 (he138 := hr) .. | .Lam_n1 (he226 := hr) .. | .Forall_n1 (he314 := hr) ..
    | .Let_n1 (he401 := hr) .. | .Let_other_n1 (he443 := hr) .. =>
      exact nomatch hr
    | .App_other (cs115 := cs1) (cs148 := cs2) (ld12 := ld) (ev117 := ev1) (hne141 := hne1)
        (ev150 := ev2) (hc167 := hc) .. =>
      obtain ⟨Ef, Ea, rfl, hf, ha⟩ := hE.app_of_load ld
      simp only [noProjAt, Bool.and_eq_true] at hnp
      rcases expr_mentions_block_ret_bit ev1 with hv0 | hv1
      · rw [hv0] at ev1
        have hg1 : Good c cs1 := hgood.sub (fun x hx => by simp [hc, hx])
        have hg2 : Good c cs2 := hgood.sub (fun x hx => by simp [hc, hx])
        have hmf := expr_mentions_block_zero_spec hpeer hlf hg1 hf hnp.1 hbas ev1
        have hma := expr_mentions_block_zero_spec hpeer hlf hg2 (ha.mono ev1.heap_extends) hnp.2
          (repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy)
            ev1.heap_extends hbas) ev2
        simp [Expr.mentionsConst, hmf, hma]
      · exact absurd hv1 hne1
    | .Lam_other (cs203 := cs1) (cs236 := cs2) (ld12 := ld) (ev205 := ev1) (hne229 := hne1)
        (ev238 := ev2) (hc255 := hc) .. =>
      obtain ⟨Et, Eb, _, rfl, ht, hb, _⟩ := hE.lam_of_load ld
      simp only [noProjAt, Bool.and_eq_true] at hnp
      rcases expr_mentions_block_ret_bit ev1 with hv0 | hv1
      · rw [hv0] at ev1
        have hg1 : Good c cs1 := hgood.sub (fun x hx => by simp [hc, hx])
        have hg2 : Good c cs2 := hgood.sub (fun x hx => by simp [hc, hx])
        have hmt := expr_mentions_block_zero_spec hpeer hlf hg1 ht hnp.1 hbas ev1
        have hmb := expr_mentions_block_zero_spec hpeer hlf hg2 (hb.mono ev1.heap_extends) hnp.2
          (repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy)
            ev1.heap_extends hbas) ev2
        simp [Expr.mentionsConst, hmt, hmb]
      · exact absurd hv1 hne1
    | .Forall_other (cs291 := cs1) (cs324 := cs2) (ld12 := ld) (ev293 := ev1) (hne317 := hne1)
        (ev326 := ev2) (hc343 := hc) .. =>
      obtain ⟨Et, Eb, _, rfl, ht, hb, _⟩ := hE.forallE_of_load ld
      simp only [noProjAt, Bool.and_eq_true] at hnp
      rcases expr_mentions_block_ret_bit ev1 with hv0 | hv1
      · rw [hv0] at ev1
        have hg1 : Good c cs1 := hgood.sub (fun x hx => by simp [hc, hx])
        have hg2 : Good c cs2 := hgood.sub (fun x hx => by simp [hc, hx])
        have hmt := expr_mentions_block_zero_spec hpeer hlf hg1 ht hnp.1 hbas ev1
        have hmb := expr_mentions_block_zero_spec hpeer hlf hg2 (hb.mono ev1.heap_extends) hnp.2
          (repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy)
            ev1.heap_extends hbas) ev2
        simp [Expr.mentionsConst, hmt, hmb]
      · exact absurd hv1 hne1
    | .Let_other_other (cs420 := cs2) (cs453 := cs3) (ld12 := ld) (ev380 := ev1) (ev422 := ev2)
        (hne446 := hne2) (ev455 := ev3) (hc472 := hc) .. =>
      obtain ⟨Et, Ev, Eb, rfl, _, hv, hb⟩ := hE.letE_of_load ld
      obtain ⟨hnp_b, hnp_v⟩ := noProjAt_of_instantiate1Lift hnp
      rcases expr_mentions_block_ret_bit ev2 with hv2_0 | hv2_1
      · rw [hv2_0] at ev2
        have hg2 : Good c cs2 := hgood.sub (fun x hx => by simp [hc, hx])
        have hg3 : Good c cs3 := hgood.sub (fun x hx => by simp [hc, hx])
        have ext12 := ev1.heap_extends.trans ev2.heap_extends
        have hbas1 := repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy)
          ev1.heap_extends hbas
        have hbas2 := repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy)
          ext12 hbas
        have hmb := expr_mentions_block_zero_spec hpeer hlf hg3 (hb.mono ext12) hnp_b hbas2 ev3
        exact mentionsConst_instantiate1Lift_false hmb fun hloose =>
          expr_mentions_block_zero_spec hpeer hlf hg2 (hv.mono ev1.heap_extends)
            (hnp_v hloose) hbas1 ev2
      · exact absurd hv2_1 hne2
    | .Proj (cs516 := cs1) (ld12 := ld) (ev518 := ev1) (hc535 := hc) .. =>
      obtain ⟨a, i, E1, _, rfl, _, he1⟩ := hE.proj_of_load ld
      simp only [noProjAt, Bool.and_eq_true, Bool.not_eq_true'] at hnp
      have hg1 : Good c cs1 := hgood.sub (fun x hx => by simp [hc, hx])
      have hm1 := expr_mentions_block_zero_spec hpeer hlf hg1 he1 hnp.2 hbas ev1
      simp [Expr.mentionsConst, hnp.1, hm1]
termination_by cs.length
decreasing_by
  all_goals
    simp only [hc, List.length_cons, List.length_append]
    omega

theorem list_any_mentions_block_zero_spec {c : Ctx} {b₀ : Bytes.Address} {T : KKey}
    {nl nP nIdx nCtors : Nat} {Γ : Nat → KExpr} {k : Nat} :
    ∀ {Es : List KExpr} {pes bas : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      OneTypePeerFacts c b₀ T nl nP nIdx nCtors →
      LoadFacts c →
      Good c cs →
      RepList kexprListEnum (fun h₀ X p₀ => TmExact c.κ 0 Γ h₀ k X p₀) h Es pes →
      (∀ e ∈ Es, noProjAt T e = true) →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h [b₀] bas →
      ObsFn W "KernelCheck::list_any_mentions_block" [pes, bas] h (.field 0) h' cs →
      ∀ e ∈ Es, e.mentionsConst T = false
  | _, _, _, _, _, _, _, _, _, .nil cell, _, _, ev => by
    intro _ hm; exact nomatch hm
  | _, _, bas, h, h', cs, hpeer, hlf, hgood, .cons cell he hes, hnp, hbas, ev => by
    match Obs.«KernelCheck::list_any_mentions_block».obs ev with
    | .Nil (ld12 := ld) .. =>
      exact (load_cell_ne cell ld (by decide)).elim
    | .Cons_n1 (he75 := hr) .. =>
      exact nomatch hr
    | .Cons_other (cs52 := cs1) (cs85 := cs2) (ld12 := ld) (ev54 := ev1)
        (hne78 := hne1) (ev87 := ev2) (hc104 := hc) .. =>
      subst hc
      obtain ⟨-, hxs⟩ := load_cell cell ld
      injection hxs with h1 h2; injection h2 with h2; subst h1 h2
      rcases expr_mentions_block_ret_bit ev1 with hv0 | hv1
      · rw [hv0] at ev1
        have hg1 : Good c cs1 := hgood.sub (fun x hx => by simp [hx])
        have hg2 : Good c cs2 := hgood.sub (fun x hx => by simp [hx])
        have hm_hd := expr_mentions_block_zero_spec hpeer hlf hg1 he
          (hnp _ List.mem_cons_self) hbas ev1
        have hm_tl := list_any_mentions_block_zero_spec hpeer hlf hg2
          (repList_heapMono₂ kexprListEnum tmExact_heapMono₂ ev1.heap_extends hes)
          (fun x hx => hnp x (List.mem_cons_of_mem _ hx))
          (repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy)
            ev1.heap_extends hbas) ev2
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hxtl
        · exact hm_hd
        · exact hm_tl x hxtl
      · exact absurd hv1 hne1

/-! ## Former checks (`former_is_tele`, `get_result_sort_level`, `nat_pi_binders`,
`dom_zero_ok`, `ctor_zero_ok`, `ctor_zero_all`, `former_decl_ok`) -/

theorem former_is_tele_one_spec {κ : _root_.Address → KKey} {Γ : Nat → KExpr} :
    ∀ (n : Nat) {k : Nat} {E : KExpr} {pe : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      n < 549755813888 →
      TmExact κ 0 Γ h k E pe →
      ObsFn W "KernelCheck::former_is_tele" [pe, .field (n : F)] h (.field 1) h' cs →
      h' = h ∧ ∃ bs s, E.stripPis n = some (bs, .sort s) ∧ bs.length = n
  | 0, k, E, pe, h, h', cs, _, hE, ev => by
    match Obs.«KernelCheck::former_is_tele».obs ev with
    | .n0_Srt (ld26 := ld) (he41 := hh) .. =>
      obtain ⟨s, rfl, _⟩ := hE.sort_of_load ld
      exact ⟨hh, [], s, rfl, rfl⟩
    | .n0_other (he47 := hr) .. => exact nomatch hr
    | .other_Forall (hne50 := hne) .. => exact absurd rfl hne
    | .other_other (he125 := hr) .. => exact nomatch hr
  | m + 1, k, E, pe, h, h', cs, hlt, hE, ev => by
    match Obs.«KernelCheck::former_is_tele».obs ev with
    | .n0_Srt (hv14 := hv) .. | .n0_other (hv14 := hv) .. =>
      exact absurd hv (succ_field_ne_zero hlt)
    | .other_other (he125 := hr) .. => exact nomatch hr
    | .other_Forall (ld65 := ld) (op118 := op) (ev95 := ev') .. =>
      obtain ⟨T, B, ℓ, rfl, _, hb, _⟩ := hE.forallE_of_load ld
      rw [evalBinOp_sub_succ m op] at ev'
      obtain ⟨hh, bs, s, hst, hlen⟩ := former_is_tele_one_spec m (by omega) hb ev'
      exact ⟨hh, (T, bmeta ℓ) :: bs, s, by simp [Expr.stripPis, hst], by simp [hlen]⟩

theorem get_result_sort_level_spec (hCore : IxVM.Consistency.Core S₀) {c : Ctx} :
    ∀ (n : Nat) {d : Nat} {Γ : Nat → KExpr} {E : KExpr}
      {rc pe types r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      n < 549755813888 →
      RCRep c.t c.lim h rc →
      TypesRep c.κ Γ h d types →
      GhostScoped Γ d →
      EnvFacts c →
      LoadFacts c →
      Good c cs →
      Tm c.κ d Γ h 0 E pe →
      ObsFn W "KernelCheck::get_result_sort_level" [rc, pe, .field (n : F), types] h r h' cs →
      ∃ ℓ : KLevel, RepKLevel h' ℓ r ∧
        ∀ bs s, E.stripPis n = some (bs, .sort s) → LvEq s ℓ
  | 0, d, Γ, E, rc, pe, types, r, h, h', cs, _, hrc, hty, hsc, hef, hlf, hgood, hE, ev => by
    match Obs.«KernelCheck::get_result_sort_level».obs ev with
    | .n0 (cs12 := cs12) (ev14 := ev_w) (ld64 := ld) (he78 := hr) (he79 := hh) (hc80 := hc) .. =>
      subst hc hr hh
      have hg1 : Good c cs12 := hgood.sub (fun x hx => by simp [hx])
      obtain ⟨E', hE', hred⟩ := core_whnf hCore hrc hty hsc hef hlf hg1 ev_w hE
      obtain ⟨u, rfl, ℓ, hℓ, huℓ⟩ := hE'.sort_of_load ld
      refine ⟨ℓ, hℓ, fun bs s hst => ?_⟩
      simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hst
      obtain ⟨rfl, rfl⟩ := hst
      have hsort := Red.sort_eq hred
      injection hsort with hsu
      subst hsu
      exact huℓ
    | .other (hne82 := hne) .. => exact absurd rfl hne
  | m + 1, d, Γ, E, rc, pe, types, r, h, h', cs, hlt, hrc, hty, hsc, hef, hlf, hgood, hE, ev => by
    match Obs.«KernelCheck::get_result_sort_level».obs ev with
    | .n0 (hv52 := hv) .. => exact absurd hv (succ_field_ne_zero hlt)
    | .other (cs12 := cs12) (x_body := xbody) (cs124 := cs2) (m161 := m3) (ev14 := ev_w)
        (ld97 := ld) (op158 := op) (hm169 := hm3) (ev126 := ev_rec) (hc189 := hc) .. =>
      subst hc
      have hg1 : Good c cs12 := hgood.sub (fun x hx => by simp [hx])
      have hg2 : Good c cs2 := hgood.sub (fun x hx => by simp [hx])
      obtain ⟨E', hE', hred⟩ := core_whnf hCore hrc hty hsc hef hlf hg1 ev_w hE
      obtain ⟨T, B, _, rfl, hT, hB, _⟩ := hE'.forallE_of_load ld
      have ext_w := ev_w.heap_extends
      obtain ⟨ext_push, hty', hsc'⟩ := push_binder_types hT (hty.mono ext_w) hsc
      rw [← hm3] at ext_push hty'
      have hB_open : Tm c.κ (d + 1) (Ghost.extend Γ d T) m3 0 (B.instantiate1 (.fvar d T)) xbody :=
        (hB.open_body (Ghost.extend_at Γ d T) (Ghost.extend_below Γ d T)).mono ext_push
      rw [evalBinOp_sub_succ m op] at ev_rec
      obtain ⟨ℓ, hℓ, htele⟩ := get_result_sort_level_spec hCore m (by omega)
        (hrc.mono (ext_w.trans ext_push)) hty' hsc' hef hlf hg2 hB_open ev_rec
      refine ⟨ℓ, hℓ, fun bs s hst => ?_⟩
      cases E with
      | forallE dom₀ bo₀ m₀ =>
        obtain ⟨rfl, rfl, rfl⟩ := Red.forallE_eq hred
        simp only [Expr.stripPis, Option.map_eq_some_iff] at hst
        obtain ⟨⟨bs₁, body₁⟩, hst₁, hst⟩ := hst
        simp only [Prod.mk.injEq] at hst
        obtain ⟨rfl, rfl⟩ := hst
        obtain ⟨bs₂, hst₂⟩ := stripPis_instantiate1_sort m (v := .fvar d T) (k := 0) hst₁
        exact htele bs₂ s hst₂
      | _ => simp [Expr.stripPis] at hst

theorem mkAppN_not_forallE :
    ∀ (H : KExpr), (∀ d b m, H ≠ .forallE d b m) →
      ∀ (As : List KExpr) (d b : KExpr) (m : Ix.Kernel.BinderMeta),
        Expr.mkAppN H As ≠ .forallE d b m
  | H, hnf, [], d, b, m => hnf d b m
  | H, _, a :: As, d, b, m =>
    mkAppN_not_forallE (.app H a) (fun _ _ _ h => nomatch h) As d b m

theorem mkAppN_const_not_forallE (c : KKey) (us : List KLevel)
    (As : List KExpr) (d b : KExpr) (m : Ix.Kernel.BinderMeta) :
    Expr.mkAppN (.const c us) As ≠ .forallE d b m :=
  mkAppN_not_forallE (.const c us) (fun _ _ _ h => nomatch h) As d b m

theorem famHead_true_mentionsConst (T : KKey) :
    ∀ (e : KExpr), famHead T e = true → e.mentionsConst T = true
  | .forallE ty b _, h => by
    simp only [famHead] at h
    have ih := famHead_true_mentionsConst T b h
    simp [Expr.mentionsConst, ih]
  | .app f a, h => by
    simp only [famHead] at h
    have ih := famHead_true_mentionsConst T f h
    simp [Expr.mentionsConst, ih]
  | .const c _, h => by
    simpa [famHead, Expr.mentionsConst] using h
  | e, h => by
    cases e <;> simp [famHead] at h <;>
      first
      | (have ih := famHead_true_mentionsConst T _ h; simp [Expr.mentionsConst, ih])
      | (simpa [Expr.mentionsConst] using h)

theorem famHead_eq_false_of_mentionsConst_false {T : KKey} {e : KExpr}
    (hm : e.mentionsConst T = false) : famHead T e = false := by
  cases hfh : famHead T e with
  | false => rfl
  | true =>
    have ht := famHead_true_mentionsConst T e hfh
    rw [hm] at ht
    exact nomatch ht

/-- Alignment of a strictly-positive recursive field domain's binder spine between its raw heap
term `R` and its ζ-expanded kernel term `E`: both peel the exact same `∀`-binders (with identical
binder metadata `m`) down to an application spine headed by `.const T us`. -/
inductive RawRecSpine (T : KKey) : KExpr → KExpr → Prop where
  | app {us : List KLevel} {rAs eAs : List KExpr} :
      RawRecSpine T (Expr.mkAppN (.const T us) rAs) (Expr.mkAppN (.const T us) eAs)
  | forallE {rd rb ed eb : KExpr} {m : Ix.Kernel.BinderMeta} :
      RawRecSpine T rb eb →
      RawRecSpine T (.forallE rd rb m) (.forallE ed eb m)

theorem nat_pi_binders_of_rawRecSpine {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {T : KKey} :
    ∀ {R E : KExpr}, RawRecSpine T R E →
      ∀ {k : Nat} {pe pbs plast : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
        RawTmExact κ d Γ h k R E pe →
        ObsFn W "KernelCheck::nat_pi_binders" [pe] h (.tuple [pbs, plast]) h' cs →
        ∃ k' us rAs eAs,
          RawTmExact κ d Γ h' k'
            (Expr.mkAppN (.const T us) rAs) (Expr.mkAppN (.const T us) eAs) plast
  | _, _, .app (us := us) (rAs := rAs) (eAs := eAs), k, pe, pbs, plast, h, h', cs, hRaw, ev => by
    match Obs.«KernelCheck::nat_pi_binders».obs ev with
    | .Forall (ld12 := ld) .. =>
      obtain ⟨RT, RB, _, _, _, hR_eq, _, _, _, _⟩ := hRaw.forallE_of_load ld
      exact (mkAppN_const_not_forallE T us rAs RT RB _ hR_eq).elim
    | .other (he138 := hr) .. =>
      have ext_ev := ev.heap_extends
      injection hr with hl; injection hl with _ hl; injection hl with hpe
      subst hpe
      exact ⟨k, us, rAs, eAs, hRaw.mono ext_ev⟩
  | _, _, .forallE (rd := rd) (rb := rb) (ed := ed) (eb := eb) (m := m) hrb,
      k, pe, pbs, plast, h, h', cs, hRaw, ev => by
    match Obs.«KernelCheck::nat_pi_binders».obs ev with
    | .Forall (x_b := xb) (m36 := m1) (x_bs := xbs) (x_r := xr) (m76 := m2)
        (ld12 := ld) (ev48 := ev') (he74 := hr) (hm84 := hm2) (he128 := hh) .. =>
      obtain ⟨RT, RB, T', B', ℓ, hR_eq, hE_eq, _, hb, _⟩ := hRaw.forallE_of_load ld
      injection hR_eq with _ hrb_eq _
      injection hE_eq with _ heb_eq _
      subst hrb_eq heb_eq
      injection hr with hl; injection hl with _ hl; injection hl with hxr
      subst hxr
      obtain ⟨k', us, rAs, eAs, hlast⟩ := nat_pi_binders_of_rawRecSpine hrb hb ev'
      exact ⟨k', us, rAs, eAs, hlast.mono (by rw [hh, hm2]; exact Heap.Extends.snoc m1 _)⟩
    | .other (ld12 := ld) (hne130 := hne) .. =>
      exact (hRaw.not_forallE_of_load ld hne rd rb m rfl).elim

theorem dom_zero_ok_of_rawRecSpine {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {T : KKey} {ℓ_res : KLevel} :
    ∀ {R E : KExpr}, RawRecSpine T R E →
      ∀ {k : Nat} {pe pres r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
        RawTmExact κ d Γ h k R E pe →
        RepKLevel h ℓ_res pres →
        ObsFn W "KernelCheck::dom_zero_ok" [pe, pres] h r h' cs →
        pwsAll ℓ_res.zeronessOf E = true
  | _, _, .app (us := us) (rAs := rAs) (eAs := eAs),
      k, pe, pres, r, h, h', cs, hRaw, _, ev => by
    match Obs.«KernelCheck::dom_zero_ok».obs ev with
    | .Forall (ld12 := ld) .. =>
      obtain ⟨RT, RB, _, _, _, hR_eq, _, _, _, _⟩ := hRaw.forallE_of_load ld
      exact (mkAppN_const_not_forallE T us rAs RT RB _ hR_eq).elim
    | .other .. =>
      cases hE : Expr.mkAppN (.const T us) eAs with
      | forallE dom bo bi => exact (mkAppN_const_not_forallE T us eAs dom bo bi hE).elim
      | _ => rfl
  | _, _, .forallE (rd := rd) (rb := rb) (ed := ed) (eb := eb) (m := m) hrb,
      k, pe, pres, r, h, h', cs, hRaw, hres, ev => by
    match Obs.«KernelCheck::dom_zero_ok».obs ev with
    | .Forall (x_b := xb) (x_m := xm) (m50 := m1)
        (ld12 := ld) (ev60 := ev_pw) (heq83 := heq) (ev89 := ev_rec) .. =>
      obtain ⟨RT, RB, T', B', ℓ, hR_eq, hE_eq, _, hb, hℓ⟩ := hRaw.forallE_of_load ld
      injection hR_eq with _ hrb_eq hm_eq
      injection hE_eq with hed_eq heb_eq _
      subst hrb_eq hm_eq hed_eq heb_eq
      rw [heq] at ev_pw
      have hpw := pw_eq_one hℓ hres ev_pw
      have ext1 := ev_pw.heap_extends
      have hrec := dom_zero_ok_of_rawRecSpine hrb (hb.mono ext1) (hres.mono ext1) ev_rec
      simp [pwsAll, bmeta, hpw, hrec]
    | .other (ld12 := ld) (hne107 := hne) .. =>
      exact (hRaw.not_forallE_of_load ld hne rd rb m rfl).elim

theorem ctor_zero_ok_raw_go {κ : _root_.Address → KKey} {Γ : Nat → KExpr}
    {t_addr : Bytes.Address} {T : KKey} {ℓ_res : KLevel} {us₀ : List KLevel}
    (hκ_inj : ∀ a : Bytes.Address, κ (ixAddr a) = T → ixAddr a = ixAddr t_addr) :
    ∀ (n : Nat) {k : Nat} {R E : KExpr} {rbs ebs : List (KExpr × Ix.Kernel.BinderMeta)}
      {rargs eargs : List KExpr} {pe pt pres r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      R.stripPis n = some (rbs, Expr.mkAppN (.const T us₀) rargs) →
      E.stripPis n = some (ebs, Expr.mkAppN (.const T us₀) eargs) →
      (∀ idx < n,
        (ebs.getD idx default).1.mentionsConst T = false ∨
        RawRecSpine T (rbs.getD idx default).1 (ebs.getD idx default).1) →
      RawTmExact κ 0 Γ h k R E pe →
      Bytes.RepAddressRef addrTy h t_addr pt →
      RepKLevel h ℓ_res pres →
      ObsFn W "KernelCheck::ctor_zero_ok" [pe, pt, pres] h r h' cs →
      ctorZeroOk T ℓ_res.zeronessOf E = true
  | 0, k, R, E, rbs, ebs, rargs, eargs, pe, pt, pres, r, h, h', cs,
      hstR, hstE, _, hRaw, _, _, ev => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hstR hstE
    obtain ⟨_, rfl⟩ := hstR
    obtain ⟨_, rfl⟩ := hstE
    match Obs.«KernelCheck::ctor_zero_ok».obs ev with
    | .Forall (ld12 := ld) .. =>
      obtain ⟨RT, RB, _, _, _, hR_eq, _, _, _, _⟩ := hRaw.forallE_of_load ld
      exact (mkAppN_const_not_forallE T us₀ rargs RT RB _ hR_eq).elim
    | .other .. =>
      cases hE : Expr.mkAppN (.const T us₀) eargs with
      | forallE dom bo bi => exact (mkAppN_const_not_forallE T us₀ eargs dom bo bi hE).elim
      | _ => rfl
  | m + 1, k, R, E, rbs, ebs, rargs, eargs, pe, pt, pres, r, h, h', cs,
      hstR, hstE, hdoms, hRaw, hpt, hres, ev => by
    cases R with
    | forallE rdom rbo rm =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at hstR
      obtain ⟨⟨rbs₁, rbody₁⟩, hstR₁, hstR⟩ := hstR
      simp only [Prod.mk.injEq] at hstR
      obtain ⟨rfl, rfl⟩ := hstR
      cases hRaw with
      | @forallE _ _ _ _ _ _ _ edom _ _ cell hdom hbo hℓ =>
        simp only [Expr.stripPis, Option.map_eq_some_iff] at hstE
        obtain ⟨⟨ebs₁, ebody₁⟩, hstE₁, hstE⟩ := hstE
        simp only [Prod.mk.injEq] at hstE
        obtain ⟨rfl, rfl⟩ := hstE
        match Obs.«KernelCheck::ctor_zero_ok».obs ev with
        | .other (ld12 := ld) (hne301 := hne) .. =>
          rw [loadValue_enum_cell cell] at ld
          injection ld with hv
          exact absurd hv.symm (hne [_, _, _] rfl)
        | .Forall (x_d := xd) (x_b := xb) (x_m := xm) (m49 := m1)
            (x_last := xlast) (m84 := m2) (x_h := xh) (m120 := m3) (m262 := m4)
            (ld12 := ld) (ev59 := ev_pw) (heq82 := heq) (ev96 := ev_pb) (ev132 := ev_sp)
            (sg269 := sg) (ev275 := ev_rec) .. =>
          obtain ⟨-, hxs⟩ := load_cell cell ld
          injection hxs with h1 hxs; injection hxs with h2 hxs; injection hxs with h3
          subst h1 h2 h3
          rw [heq] at ev_pw
          have hpw := pw_eq_one hℓ hres ev_pw
          have ext1 := ev_pw.heap_extends
          have ext2 := ev_pb.heap_extends
          have ext3 := ev_sp.heap_extends
          have ext123 := ext1.trans (ext2.trans ext3)
          have hfam_dom : famDomOk T ℓ_res.zeronessOf edom = true := by
            have hd0 := hdoms 0 (by omega)
            simp only [List.getD_cons_zero] at hd0
            rcases hd0 with hnoT | hrec_sp
            · simp [famDomOk, famHead_eq_false_of_mentionsConst_false hnoT]
            · obtain ⟨k', us, rAs, eAs, hlast⟩ :=
                nat_pi_binders_of_rawRecSpine hrec_sp (hdom.mono ext1) ev_pb
              obtain ⟨hd, sp, RH, EH, RAs', _, htup, hH, hna, _, hlast_eq, _⟩ :=
                collect_spine_raw_spec hlast ev_sp
              injection htup with hl; injection hl with hxh hl; injection hl with _; subst hxh
              have hRH_eq : RH = .const T us := by
                have hfn := congrArg Expr.getAppFn hlast_eq
                rw [nat_getAppFn_mkAppN, nat_getAppFn_mkAppN] at hfn
                cases RH with
                | app rf ra => exact (hna rf ra rfl).elim
                | _ => exact hfn.symm
              subst hRH_eq
              cases sg with
              | Const_n1 _ _ m_eq _ _ _ ev_eq ev_dom _ =>
                have ext_eq := ev_eq.heap_extends
                have hpws := dom_zero_ok_of_rawRecSpine hrec_sp
                  (hdom.mono (ext123.trans ext_eq)) (hres.mono (ext123.trans ext_eq)) ev_dom
                simp [famDomOk, hpws]
              | Const_other xc _ v_eq m_eq _ ld_h ev_eq hne_eq _ _ _ =>
                obtain ⟨a_c, ls_c, hR_c, _, ha_c, _⟩ := hH.const_of_load ld_h
                injection hR_c with hc_eq _
                have ha_eq : a_c = t_addr := ixAddr_inj (hκ_inj a_c hc_eq.symm)
                subst ha_eq
                obtain ⟨hv_eq, _⟩ := Lib.address_eq_spec ev_eq ha_c
                  (Bytes.repAddressRef_heapMono₂ addrTy ext123 hpt)
                simp at hv_eq
                exact (hne_eq hv_eq).elim
              | other _ ld_h hne_c _ _ _ =>
                cases hH with
                | const cell_c _ _ =>
                  rw [loadValue_enum_cell cell_c] at ld_h
                  injection ld_h with hv
                  exact (hne_c [_, _] rfl hv.symm).elim
          have ext4 : Heap.Extends m3 m4 := by
            cases sg with
            | Const_n1 _ _ _ _ _ _ ev_eq ev_dom _ =>
              exact ev_eq.heap_extends.trans ev_dom.heap_extends
            | Const_other _ _ _ _ _ _ ev_eq _ _ hm4 _ =>
              rw [hm4]; exact ev_eq.heap_extends
            | other _ _ _ _ hm4 _ =>
              rw [hm4]
          have ext_all := ext123.trans ext4
          have hdoms' : ∀ idx < m,
              (ebs₁.getD idx default).1.mentionsConst T = false ∨
              RawRecSpine T (rbs₁.getD idx default).1 (ebs₁.getD idx default).1 := by
            intro idx hidx
            have h := hdoms (idx + 1) (by omega)
            simpa [List.getD_cons_succ] using h
          have hrec := ctor_zero_ok_raw_go hκ_inj m hstR₁ hstE₁ hdoms' (hbo.mono ext_all)
            (Bytes.repAddressRef_heapMono₂ addrTy ext_all hpt) (hres.mono ext_all) ev_rec
          simp [ctorZeroOk, bmeta, hpw, hfam_dom, hrec]
    | _ => simp [Expr.stripPis] at hstR


/-! ## Arithmetic, list-drop, and constructor-stage specs -/

theorem evalBinOp_add_nat (a b : Nat) {v : SourceValue F}
    (op : evalBinOp .add (.field (a : F)) (.field (b : F)) = .ok v) :
    v = .field (((a + b : Nat) : F)) := by
  simp only [evalBinOp] at op
  injection op with hv
  rw [← hv]
  simp [Nat.cast_add]

theorem evalBinOp_sub_nat {a b : Nat} (hle : b ≤ a) {v : SourceValue F}
    (op : evalBinOp .sub (.field (a : F)) (.field (b : F)) = .ok v) :
    v = .field (((a - b : Nat) : F)) := by
  simp only [evalBinOp] at op
  injection op with hv
  rw [← hv]
  simp [Nat.cast_sub hle]

theorem kdrop_exact {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {k : Nat}
    {xs : List KExpr} {l r : SourceValue F} {cnt : Nat} {h h' : Heap F} {cs : List (Call F)}
    (hcnt : cnt < 4294967296)
    (ev : ObsFn W Obs.Names.«Lists::drop<&KernelTypes::KExprNode>» [l, .field (cnt : F)] h r h' cs)
    (hl : RepList kexprListEnum (fun h₀ X p₀ => TmExact κ d Γ h₀ k X p₀) h xs l) :
    cnt ≤ xs.length ∧
      RepList kexprListEnum (fun h₀ X p₀ => TmExact κ d Γ h₀ k X p₀) h (xs.drop cnt) r ∧
      h' = h := by
  have hval : ZMod.val (cnt : F) = cnt :=
    ZMod.val_natCast_of_lt (Nat.lt_trans hcnt (by decide))
  have hres := Lib.Lists.drop_spec (t := .ptr (.named "KernelTypes::KExprNode" []))
    (R := fun h₀ X p₀ => TmExact κ d Γ h₀ k X p₀) cnt hval
    (by rw [Obs.Names.«Lists::drop<&KernelTypes::KExprNode>».symbol]; exact ev)
    (by rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl)
  rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol, hval] at hres
  exact hres

theorem klength_exact {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {k : Nat}
    {xs : List KExpr} {l r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W Obs.Names.«Lists::length<&KernelTypes::KExprNode>» [l] h r h' cs)
    (hl : RepList kexprListEnum (fun h₀ X p₀ => TmExact κ d Γ h₀ k X p₀) h xs l) :
    r = .field (xs.length : F) ∧ h' = h := by
  have ev' : ObsFn W (Instance.mk "Lists::length" [(.ptr (.named "KernelTypes::KExprNode" []))]).symbol
      [l] h r h' cs := by
    rw [Obs.Names.«Lists::length<&KernelTypes::KExprNode>».symbol]; exact ev
  have hl' : RepList (Instance.mk "Lists::Node" [(.ptr (.named "KernelTypes::KExprNode" []))]).symbol
      (fun h₀ X p₀ => TmExact κ d Γ h₀ k X p₀) h xs l := by
    rw [Obs.Names.«Lists::Node<&KernelTypes::KExprNode>».symbol]; exact hl
  exact Lib.Lists.length_spec ev' hl'

theorem assert_first_args_are_param_bvars_go {κ : _root_.Address → KKey} {Γ : Nat → KExpr}
    {nP nF k_loc : Nat} (hlt : nP + nF < 549755813888) :
    ∀ (rem i : Nat) {args : List KExpr} {pargs r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      rem = nP - i →
      i ≤ nP →
      RepList kexprListEnum (fun h₀ X p₀ => TmExact κ 0 Γ h₀ k_loc X p₀) h args pargs →
      ObsFn W "KernelCheck::assert_first_args_are_param_bvars"
        [pargs, .field (nP : F), .field (nF : F), .field (i : F)] h r h' cs →
      h' = h ∧ args.take rem = (List.range rem).map (fun m => Expr.bvar (nF + nP - 1 - (i + m)))
  | 0, i, args, pargs, r, h, h', cs, hrem, hle, hargs, ev => by
    have hi_eq : i = nP := by omega
    cases hi_eq.symm
    match Obs.«KernelCheck::assert_first_args_are_param_bvars».obs ev with
    | .n0 (he27 := hh) .. => exact ⟨hh, rfl⟩
    | .other (op17 := op) (hne29 := hne) .. =>
      rw [evalBinOp_sub_nat (Nat.le_refl nP) op, Nat.sub_self] at hne
      exact absurd rfl hne
  | rem + 1, i, args, pargs, r, h, h', cs, hrem, hle, hargs, ev => by
    have hi_lt : i < nP := by omega
    match Obs.«KernelCheck::assert_first_args_are_param_bvars».obs ev with
    | .n0 (op17 := op) .. =>
      have hsub := evalBinOp_sub_nat hle op
      have h0 : (.field (((nP - i : Nat) : F)) : SourceValue F) = .field ((0 : Nat) : F) :=
        hsub.symm
      have heq := nat_eq_of_field_eq (by omega) (by decide) h0
      omega
    | .other (x_arg := xarg) (x_rest := xrest) (x_j := xj) (ld44 := ld_cons) (ld73 := ld_bv)
        (op135 := op_add) (op127 := op_sub1) (op119 := op_sub2) (heq139 := heq_j)
        (op192 := op_inc) (ev153 := ev_rec) (he197 := hh) .. =>
      obtain ⟨arg, rest, rfl, harg, hrest⟩ := RepList.cons_of_load hargs ld_cons
      obtain ⟨jf, rfl, hsmall, hbv⟩ := harg.bvar_of_load ld_bv
      rcases hbv with ⟨_, rfl⟩ | ⟨_, hd, _⟩
      · rw [evalBinOp_add_nat nF nP op_add] at op_sub1
        rw [evalBinOp_sub_nat (by omega : 1 ≤ nF + nP) op_sub1] at op_sub2
        rw [evalBinOp_sub_nat (by omega : i ≤ nF + nP - 1) op_sub2] at heq_j
        injection heq_j with hjf
        have hj_val : ZMod.val jf = nF + nP - 1 - i := by
          have hcast : (((ZMod.val jf : Nat) : F) : F) = (((nF + nP - 1 - i : Nat) : F) : F) := by
            simpa using hjf
          have h1 : ZMod.val jf < 18446744069414584321 := Nat.lt_trans hsmall (by decide)
          have h2 : nF + nP - 1 - i < 18446744069414584321 :=
            Nat.lt_trans (by omega : nF + nP - 1 - i < 549755813888) (by decide)
          have hz1 : ZMod.val ((ZMod.val jf : Nat) : F) = ZMod.val jf := ZMod.val_natCast_of_lt h1
          have hz2 : ZMod.val ((nF + nP - 1 - i : Nat) : F) = nF + nP - 1 - i :=
            ZMod.val_natCast_of_lt h2
          rw [← hz1, hcast, hz2]
        rw [evalBinOp_add_one i op_inc] at ev_rec
        obtain ⟨hh_rec, htake⟩ := assert_first_args_are_param_bvars_go hlt rem (i + 1)
          (by omega) (by omega) hrest ev_rec
        refine ⟨hh.trans hh_rec, ?_⟩
        rw [List.take_succ_cons, hj_val, htake, List.range_succ_eq_map]
        simp only [List.map_cons, Nat.add_zero, List.map_map, Function.comp_def]
        congr 1
        apply List.map_congr_left
        intro m _
        congr 1
        omega
      · omega

/-- Exact heap-cell witness that `p` starts with `m` literal `"Forall"` cells followed by a
non-`"Forall"` `"KernelTypes::KExprNode"` cell (established by `peel_n_foralls` + `collect_spine`
in `check_ctor_return_type` and consumed by `check_field_universes` and `check_positivity`). -/
inductive NoTopLetSpine : Nat → Heap F → SourceValue F → Prop where
  | zero {h : Heap F} {addr : Nat} {tag : String} {args : List (SourceValue F)}
      (cell : h[addr]? = some (.construct kexprEnum tag args))
      (hne : tag ≠ "Forall") :
      NoTopLetSpine 0 h (.ptr (.enum kexprEnum) addr)
  | succ {m : Nat} {h : Heap F} {addr : Nat} {tp bp lp : SourceValue F}
      (cell : h[addr]? = some (.construct kexprEnum "Forall" [tp, bp, lp]))
      (rest : NoTopLetSpine m h bp) :
      NoTopLetSpine (m + 1) h (.ptr (.enum kexprEnum) addr)

theorem NoTopLetSpine.mono {m : Nat} {h₁ h₂ : Heap F} {p : SourceValue F}
    (ext : Heap.Extends h₁ h₂) (hs : NoTopLetSpine m h₁ p) :
    NoTopLetSpine m h₂ p :=
  match m, p, hs with
  | _, _, .zero cell hne => .zero (ext.getElem?_eq cell) hne
  | _, _, .succ cell rest => .succ (ext.getElem?_eq cell) (rest.mono ext)

theorem NoTopLetSpine.zero_not_forall {h : Heap F} {p : SourceValue F}
    {vs : List (SourceValue F)}
    (hs : NoTopLetSpine 0 h p)
    (ld : loadValue h p = .ok (.construct kexprEnum "Forall" vs)) : False := by
  cases hs with
  | zero cell hne =>
    obtain ⟨heq, -⟩ := load_cell cell ld
    exact hne heq

theorem NoTopLetSpine.succ_forall {m : Nat} {h : Heap F} {p v : SourceValue F}
    (hs : NoTopLetSpine (m + 1) h p)
    (ld : loadValue h p = .ok v) :
    ∃ tp bp lp, v = .construct kexprEnum "Forall" [tp, bp, lp] ∧ NoTopLetSpine m h bp := by
  cases hs with
  | @succ _ _ _ tp bp lp cell rest =>
    rw [loadValue_enum_cell cell] at ld
    injection ld with hv
    exact ⟨tp, bp, lp, hv.symm, rest⟩

theorem NoTopLetSpine.succ_not_other {m : Nat} {h : Heap F} {p v : SourceValue F}
    (hs : NoTopLetSpine (m + 1) h p)
    (ld : loadValue h p = .ok v)
    (hne : ∀ vs : List (SourceValue F), vs.length = 3 → v ≠ .construct kexprEnum "Forall" vs) :
    False := by
  obtain ⟨tp, bp, lp, rfl, -⟩ := hs.succ_forall ld
  exact hne [tp, bp, lp] rfl rfl

theorem collect_spine_const_noTopLetSpine {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {k : Nat} {R E : KExpr} {pe hd sp xa xu : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hRaw : RawTmExact κ d Γ h k R E pe)
    (ev : ObsFn W "KernelTypes::collect_spine" [pe] h (.tuple [hd, sp]) h' cs)
    (ld_hd : loadValue h' hd = .ok (.construct kexprEnum "Const" [xa, xu])) :
    NoTopLetSpine 0 h' pe := by
  match Obs.«KernelTypes::collect_spine».obs ev with
  | .App (ld12 := ld) .. =>
    cases hRaw with
    | app cell _ _ => exact .zero (ev.heap_extends.getElem?_eq cell) (by decide)
    | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ | const cell _ _
    | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _
    | litStr cell _ _ | proj cell _ _ =>
      exact (load_cell_ne cell ld (by decide)).elim
  | .other (he115 := hr) .. =>
    injection hr with hl; injection hl with hpe _; subst hpe
    have hRaw' := hRaw.mono ev.heap_extends
    cases hRaw' with
    | const cell _ _ => exact .zero cell (by decide)
    | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ | app cell _ _
    | lam cell _ _ _ | forallE cell _ _ _ | letE cell _ _ _ | litNat cell _ _
    | litStr cell _ _ | proj cell _ _ =>
      exact (load_cell_ne cell ld_hd (by decide)).elim

theorem peel_n_foralls_raw_spec {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} :
    ∀ (n : Nat) {k : Nat} {R E : KExpr} {pe r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      n < 4294967296 →
      RawTmExact κ d Γ h k R E pe →
      ObsFn W "KernelCheck::peel_n_foralls" [pe, .field (n : F)] h r h' cs →
      h' = h ∧ ∃ rbs rbody bs body,
        R.stripPis n = some (rbs, rbody) ∧
        E.stripPis n = some (bs, body) ∧
        rbs.length = n ∧
        bs.length = n ∧
        RawTmExact κ d Γ h (k + n) rbody body r
  | 0, k, R, E, pe, r, h, h', cs, _, hRaw, ev => by
    rcases Obs.«KernelCheck::peel_n_foralls».obs ev with
      ⟨_, rfl, rfl, _⟩ | ⟨_, _, _, _, _, hne, _, _, _, _⟩
    · exact ⟨rfl, [], R, [], E, rfl, rfl, rfl, rfl, by simpa using hRaw⟩
    · exact absurd rfl hne
  | m + 1, k, R, E, pe, r, h, h', cs, hlt, hRaw, ev => by
    rcases Obs.«KernelCheck::peel_n_foralls».obs ev with
      ⟨hv, _, _, _⟩ | ⟨_, xb, _, _, _, _, ld, op, ev_rec, _⟩
    · exact absurd hv (succ_field_ne_zero (by omega))
    · obtain ⟨RT, RB, T, B, ℓ, rfl, rfl, _, hb, _⟩ := hRaw.forallE_of_load ld
      rw [evalBinOp_sub_succ m op] at ev_rec
      obtain ⟨hh, rbs, rbody, bs, body, hstR, hstE, hrlen, hblen, hbody⟩ :=
        peel_n_foralls_raw_spec m (by omega) hb ev_rec
      refine ⟨hh, (RT, bmeta ℓ) :: rbs, rbody, (T, bmeta ℓ) :: bs, body,
        by simp [Expr.stripPis, hstR], by simp [Expr.stripPis, hstE],
        by simp [hrlen], by simp [hblen], ?_⟩
      rw [show k + (m + 1) = k + 1 + m by omega]
      exact hbody

theorem peel_n_foralls_noTopLetSpine {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} :
    ∀ (m : Nat) {k : Nat} {R E : KExpr} {pe r : SourceValue F} {h h' : Heap F}
      {cs : List (Call F)},
      m < 4294967296 →
      RawTmExact κ d Γ h k R E pe →
      ObsFn W "KernelCheck::peel_n_foralls" [pe, .field (m : F)] h r h' cs →
      ∀ {h₂ : Heap F}, Heap.Extends h' h₂ → NoTopLetSpine 0 h₂ r → NoTopLetSpine m h₂ pe
  | 0, _, _, _, pe, r, h, h', cs, _, _, ev, _, _, hs => by
    rcases Obs.«KernelCheck::peel_n_foralls».obs ev with
      ⟨_, rfl, rfl, _⟩ | ⟨_, _, _, _, _, hne, _, _, _, _⟩
    · exact hs
    · exact absurd rfl hne
  | m + 1, k, R, E, pe, r, h, h', cs, hlt, hRaw, ev, h₂, ext₂, hs => by
    rcases Obs.«KernelCheck::peel_n_foralls».obs ev with
      ⟨hv, _, _, _⟩ | ⟨_, xb, _, _, _, _, ld, op, ev_rec, _⟩
    · exact absurd hv (succ_field_ne_zero (by omega))
    · rw [evalBinOp_sub_succ m op] at ev_rec
      cases hRaw with
      | forallE cell _ hb _ =>
        obtain ⟨-, hxs⟩ := load_cell cell ld
        injection hxs with _ hxs; injection hxs with hbp _; subst hbp
        have hex : Heap.Extends h h₂ := ev_rec.heap_extends.trans ext₂
        exact .succ (hex.getElem?_eq cell)
          (peel_n_foralls_noTopLetSpine m (by omega) hb ev_rec ext₂ hs)
      | bvarLocal cell _ _ | bvarFree cell _ _ _ | sort cell _ | const cell _ _
      | app cell _ _ | lam cell _ _ _ | letE cell _ _ _ | litNat cell _ _
      | litStr cell _ _ | proj cell _ _ =>
        exact (load_cell_ne cell ld (by decide)).elim

/-- `check_ctor_return_type` refines to the exact constructor residual shape
`mkAppN (.const T (lps.map .param)) (structPsAt nF nP ++ es)` with `es.length = nIdx`,
every `a ∈ es` free of `T`, raw residual witness on `raw_cty`, and
`NoTopLetSpine (nP + nF) h' pcty`. -/
theorem check_ctor_return_type_spec {c : Ctx} {b₀ : Bytes.Address} {T : KKey}
    {lps : List LevelParam} {nP nIdx nF nCtors : Nat} {Γ : Nat → KExpr} {raw_cty cty : KExpr}
    {pcty pblk r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hlps : lps = List.range lps.length)
    (hlps_lt : lps.length < 4294967296)
    (hnPF_lt : nP + nF < 4294967296)
    (hnPI_lt : nP + nIdx < 4294967296)
    (hpeer : OneTypePeerFacts c b₀ T lps.length nP nIdx nCtors)
    (hlf : LoadFacts c)
    (hgood : Good c cs)
    (hcty : RawTmExact c.κ 0 Γ h 0 raw_cty cty pcty)
    (hnp : noProjAt T cty = true)
    (hblk : Bytes.RepAddressRef addrTy h b₀ pblk)
    (ev : ObsFn W "KernelCheck::check_ctor_return_type"
      [pcty, .field (nP : F), .field (nIdx : F), .field (nF : F),
        .field (lps.length : F), pblk, .field 0] h r h' cs) :
    NoTopLetSpine (nP + nF) h' pcty ∧
    ∃ (rcbs : List (KExpr × Ix.Kernel.BinderMeta)) (rargs : List KExpr)
      (cbs : List (KExpr × Ix.Kernel.BinderMeta)) (es : List KExpr),
      raw_cty.stripPis (nP + nF) =
        some (rcbs, Expr.mkAppN (.const T (lps.map .param)) rargs) ∧
      rcbs.length = nP + nF ∧
      cty.stripPis (nP + nF) =
        some (cbs, Expr.mkAppN (.const T (lps.map .param)) (Ix.Kernel.structPsAt nF nP ++ es)) ∧
      cbs.length = nP + nF ∧
      es.length = nIdx ∧
      ∀ a ∈ es, a.mentionsConst T = false := by
  match Obs.«KernelCheck::check_ctor_return_type».obs ev with
  | .run (v1 := v1) (m2 := m2) (m41 := m41) (x_head := xhd) (x_args := xargs)
      (x_head_addr := xhda) (x_lvls := xlvls) (m109 := m109) (cs119 := cs_par)
      (m147 := m147) (cs157 := cs_lvls) (m197 := m197) (m234 := m234)
      (v278 := vdrop) (m279 := m279)
      (m309 := m309) (m333 := m333) (v356 := v_any) (m359 := m359) (cs367 := cs_any)
      (op37 := op_pf) (ev14 := ev_peel) (ev54 := ev_sp) (ld90 := ld_hd)
      (ev121 := ev_par) (ev159 := ev_lvls) (ev207 := ev_len) (op229 := op_pi)
      (heq232 := heq_len) (ev246 := ev_bvars) (ev291 := ev_drop)
      (hm319 := hm309) (hm341 := hm333) (ev369 := ev_any) (heq392 := heq_any)
      (he396 := hh') (hc397 := hc) .. =>
    subst hc hh'
    rw [evalBinOp_add_nat nP nF op_pf] at ev_peel
    obtain ⟨hm2, rcbs, rbody, cbs, body, hstR, hstrip, hrcbs_len, hcbs_len, hbody⟩ :=
      peel_n_foralls_raw_spec (nP + nF) (by omega) hcty ev_peel
    subst hm2
    rw [Nat.zero_add] at hbody
    obtain ⟨hd, sp, RH, H, RAs, As, htup, hH, _, hAs, rfl, rfl⟩ :=
      collect_spine_raw_spec hbody ev_sp
    injection htup with hl; injection hl with h1 hl; injection hl with h2; subst h1 h2
    have ext_sp := ev_sp.heap_extends
    have hsp0 : NoTopLetSpine 0 m41 v1 := collect_spine_const_noTopLetSpine hbody ev_sp ld_hd
    have hsp_peel : NoTopLetSpine (nP + nF) m41 pcty :=
      peel_n_foralls_noTopLetSpine (nP + nF) (by omega) hcty ev_peel ext_sp hsp0
    obtain ⟨a_hd, us_hd, rfl, rfl, ha_hd, hus_hd⟩ := hH.const_of_load ld_hd
    have hg_par : Good c cs_par := hgood.sub (fun x hx => by simp [hx])
    have hblk_41 := Bytes.repAddressRef_heapMono₂ addrTy ext_sp hblk
    have hpar_T : c.κ (ixAddr a_hd) = T := by
      match Obs.«KernelCheck::assert_return_head_is_parent».obs ev_par with
      | .run (m2 := mp2) (p9 := p9) (cs15 := csp1) (ev17 := ev_ci) (ld11 := ld_ind)
          (ev112 := ev_aeq) (heq135 := heq1) (hc168 := hcp) .. =>
        subst hcp
        have hgp1 : Good c csp1 := hg_par.sub (fun x hx => by simp [hx])
        obtain ⟨cm, b', _, hcm, hb', rfl, hinfo⟩ :=
          hlf.inductRecord xhda p9 m41 mp2 csp1 a_hd _ _ _ _ _ _ _ _ ev_ci hgp1 ha_hd ld_ind
        obtain ⟨hv_eq, _⟩ := Lib.address_eq_spec ev_aeq hb'
          (Bytes.repAddressRef_heapMono₂ addrTy ev_ci.heap_extends hblk_41)
        rw [heq1] at hv_eq
        by_cases hb_eq : b' = b₀
        · subst hb_eq
          exact hpeer.peer_only_self a_hd cm _ hcm hinfo
        · simp [hb_eq] at hv_eq
    have ext_par := ev_par.heap_extends
    have hbnd_lvls : IxVM.Consistency.Bounded cs_lvls :=
      (hgood.sub (fun x hx => by simp [hx])).2
    obtain ⟨hus_eq, hm147⟩ := assert_lvls_are_params_spec lps.length 0 (by omega) hbnd_lvls
      (hus_hd.mono ext_par) ev_lvls
    rw [hm147] at ev_len
    have hus_lps : us_hd = lps.map .param := by
      rw [hus_eq]
      conv_rhs => rw [hlps]
      simp
    have hAs_109 := repList_heapMono₂ kexprListEnum tmExact_heapMono₂ ext_par hAs
    obtain ⟨hv_len, hm197⟩ := klength_exact ev_len hAs_109
    rw [hm197] at ev_bvars
    rw [evalBinOp_add_nat nP nIdx op_pi, hv_len] at heq_len
    have hAs_lt : As.length < 549755813888 :=
      RomBound.bounded_length_lt hgood.2
        (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [xargs], m147⟩)
        (by simp)
        List.mem_cons_self
        (by rw [hm147]; exact hAs_109)
    have hAs_len : As.length = nP + nIdx :=
      nat_eq_of_field_eq hAs_lt (by omega) heq_len
    obtain ⟨hm234, hAs_take⟩ := assert_first_args_are_param_bvars_go (nP := nP) (nF := nF)
      (by omega) nP 0 (by omega) (Nat.zero_le nP) hAs_109 ev_bvars
    rw [hm234] at ev_drop
    have hAs_take' : As.take nP = Ix.Kernel.structPsAt nF nP := by
      rw [hAs_take]
      simp [Ix.Kernel.structPsAt, Nat.add_comm nF nP]
    obtain ⟨_, hAs_drop, hm279⟩ := kdrop_exact (by omega : nP < 4294967296) ev_drop hAs_109
    rw [hm279] at hm333 hm309
    have ext_nil : Heap.Extends m109 m333 := by rw [hm333]; exact Heap.Extends.snoc _ _
    have ext_cons : Heap.Extends m333 m309 := by rw [hm309]; exact Heap.Extends.snoc _ _
    have ext_bas : Heap.Extends m109 m309 := ext_nil.trans ext_cons
    have hnil_cell : m309[m109.length]? = some (.construct addrListEnum "Nil" []) :=
      ext_cons.getElem?_eq (by rw [hm333]; simp)
    have hcons_cell :
        m309[m333.length]? =
          some (.construct addrListEnum "Cons" [pblk, .ptr (.enum addrListEnum) m109.length]) := by
      rw [hm309]; simp
    have hblk_309 := Bytes.repAddressRef_heapMono₂ addrTy
      (ext_sp.trans (ext_par.trans ext_bas)) hblk
    have hbas_309 : RepList addrListEnum (Bytes.RepAddressRef addrTy) m309 [b₀]
        (.ptr (.enum addrListEnum) m333.length) :=
      RepLinkedList.cons hcons_cell hblk_309 (RepLinkedList.nil hnil_cell)
    have hnp_body : noProjAt T (Expr.mkAppN (.const (c.κ (ixAddr a_hd)) us_hd) As) = true :=
      (noProjAt_stripPis hstrip hnp).2
    have hnp_As : ∀ a ∈ As, noProjAt T a = true := by
      have hga := (noProjAt_getApp hnp_body).2
      rwa [getAppArgs_mkAppN_const] at hga
    have hnp_drop : ∀ a ∈ As.drop nP, noProjAt T a = true :=
      fun a ha => hnp_As a (List.mem_of_mem_drop ha)
    rw [heq_any] at ev_any
    have hg_any : Good c cs_any := hgood.sub (fun x hx => by simp [hx])
    have hnoT_drop := list_any_mentions_block_zero_spec hpeer hlf hg_any
      (repList_heapMono₂ kexprListEnum tmExact_heapMono₂ ext_bas hAs_drop)
      hnp_drop hbas_309 ev_any
    have ext_end : Heap.Extends m41 h' :=
      ext_par.trans (ext_bas.trans ev_any.heap_extends)
    refine ⟨hsp_peel.mono ext_end, rcbs, RAs, cbs, As.drop nP, ?_, hrcbs_len, ?_, hcbs_len,
      ?_, hnoT_drop⟩
    · rw [hpar_T, hus_lps] at hstR
      exact hstR
    · rw [hpar_T, hus_lps] at hstrip
      have hsplit : As = As.take nP ++ As.drop nP := (List.take_append_drop nP As).symm
      rw [hsplit, hAs_take'] at hstrip
      exact hstrip
    · rw [List.length_drop, hAs_len]
      omega

/-! ## Parameter agreement (`check_param_agreement` and `StructDomsShared`) -/

/-- Circuit-exact parameter-agreement relation: `check_param_agreement` opens both `ta` and `tb`
with the **former's** free variables `tfvs` and checks `DefEq env i da_i db_i` at each parameter
depth `i < n`. When `ta` and `tb` share identical parameter domain terms up to `n`, `fvsP = tfvs`
holds syntactically and `StructDomsJ` follows unconditionally. -/
def StructDomsShared (env : Ix.Kernel.Env .anon) (ta tb : KExpr) (n : Nat) : Prop :=
  ∃ (tfvs : List KExpr) (trest : KExpr),
    Ix.Kernel.openPisAtFvars n ta 0 = some (tfvs, trest) ∧
    ∀ i, i < n →
      ∃ (cbs : List (KExpr × Ix.Kernel.BinderMeta)) (cbody : KExpr) (fv : KExpr),
        tb.stripPis n = some (cbs, cbody) ∧
        tfvs[i]? = some fv ∧
        DefEq env i fv.fvarTypeD (instOpen (tfvs.take i) 0 (cbs.getD i default).1)

theorem openPisAtFvars_len :
    ∀ (m : Nat) {e : KExpr} {d : Nat} {fvs : List KExpr} {o : KExpr},
      Ix.Kernel.openPisAtFvars m e d = some (fvs, o) → fvs.length = m
  | 0, _, _, _, _, h => by
    simp only [Ix.Kernel.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; rfl
  | m + 1, e, d, fvs, o, h => by
    cases e with
    | forallE dom bo _ =>
      simp only [Ix.Kernel.openPisAtFvars] at h
      rcases hop' : Ix.Kernel.openPisAtFvars m (bo.instantiate1 (.fvar d dom)) (d + 1) with
        _ | ⟨fvs', o'⟩ <;> rw [hop'] at h
      · exact nomatch h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1, List.length_cons, openPisAtFvars_len m hop']
    | _ => simp [Ix.Kernel.openPisAtFvars] at h

theorem mentionsConst_stripPis_false {T : KKey} :
    ∀ (m : Nat) {e : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)} {body : KExpr},
      e.mentionsConst T = false →
      e.stripPis m = some (bs, body) →
      ∀ i < m, (bs.getD i default).1.mentionsConst T = false
  | 0, _, _, _, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | m + 1, e, bs, body, hno, hst, i, hi => by
    cases e with
    | forallE dom bo _ =>
      simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at hno
      simp only [Expr.stripPis, Option.map_eq_some_iff] at hst
      obtain ⟨⟨bs', body'⟩, hst', hst⟩ := hst
      simp only [Prod.mk.injEq] at hst
      obtain ⟨rfl, rfl⟩ := hst
      cases i with
      | zero => exact hno.1
      | succ k => exact mentionsConst_stripPis_false m hno.2 hst' k (by omega)
    | _ => simp [Expr.stripPis] at hst

/-- When `tb`'s first `n` parameter domains agree syntactically with `ta`'s, `fvsP = tfvs`,
so `StructDomsJ` and `mentionsConst T = false` on parameter domains hold unconditionally! -/
theorem structDomsJ_and_noT_of_same_doms {env : Ix.Kernel.Env .anon} {T : KKey}
    {ta tb : KExpr} {n : Nat}
    {fvsP tfvs : List KExpr} {crest trest : KExpr}
    {tbs cbs : List (KExpr × Ix.Kernel.BinderMeta)} {tbody cbody : KExpr}
    (hopC : Ix.Kernel.openPisAtFvars n tb 0 = some (fvsP, crest))
    (hopT : Ix.Kernel.openPisAtFvars n ta 0 = some (tfvs, trest))
    (hstT : ta.stripPis n = some (tbs, tbody))
    (hstC : tb.stripPis n = some (cbs, cbody))
    (hta_noT : ta.mentionsConst T = false)
    (hdoms_eq : ∀ i < n, (cbs.getD i default).1 = (tbs.getD i default).1) :
    StructDomsJ rulesJ env 0 fvsP (tfvs.map Expr.fvarTypeD) n ∧
      (∀ p < n, (cbs.getD p default).1.mentionsConst T = false) := by
  have hlenC : fvsP.length = n := openPisAtFvars_len n hopC
  have hlenT : tfvs.length = n := openPisAtFvars_len n hopT
  have hlen_cbs : cbs.length = n := Expr.stripPis_length n hstC
  have hlen_tbs : tbs.length = n := Expr.stripPis_length n hstT
  have hcharC := (openPisAtFvars_eq_instOpen n hstC hopC).2.2
  have hcharT := (openPisAtFvars_eq_instOpen n hstT hopT).2.2
  have hget : ∀ t < n, fvsP[t]? = tfvs[t]? := by
    intro t
    induction t using Nat.strongRecOn with
    | ind t iht =>
      intro ht
      have htake : fvsP.take t = tfvs.take t := by
        apply List.ext_getElem?
        intro s
        by_cases hst : s < t
        · rw [List.getElem?_take_of_lt hst, List.getElem?_take_of_lt hst]
          exact iht s hst (by omega)
        · rw [List.getElem?_take_eq_none (by omega), List.getElem?_take_eq_none (by omega)]
      have htC : t < fvsP.length := by omega
      have htT : t < tfvs.length := by omega
      have htb_c : t < cbs.length := by omega
      have htb_t : t < tbs.length := by omega
      have hfvC := hcharC t cbs[t] fvsP[t] (List.getElem?_eq_getElem htb_c)
        (List.getElem?_eq_getElem htC)
      have hfvT := hcharT t tbs[t] tfvs[t] (List.getElem?_eq_getElem htb_t)
        (List.getElem?_eq_getElem htT)
      have hdom_t : cbs[t].1 = tbs[t].1 := by
        have hd := hdoms_eq t ht
        rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htb_c, Option.getD_some,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htb_t, Option.getD_some] at hd
      rw [List.getElem?_eq_getElem htC, List.getElem?_eq_getElem htT, hfvC, hfvT, htake, hdom_t]
  have hfvs_eq : fvsP = tfvs := by
    apply List.ext_getElem?
    intro t
    by_cases ht : t < n
    · exact hget t ht
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  subst hfvs_eq
  refine ⟨?_, ?_⟩
  · intro i hi
    have hi_lt : i < fvsP.length := by omega
    refine ⟨fvsP[i], fvsP[i].fvarTypeD, List.getElem?_eq_getElem hi_lt, ?_, .refl⟩
    rw [List.getElem?_map, List.getElem?_eq_getElem hi_lt]
    rfl
  · intro p hp
    rw [hdoms_eq p hp]
    exact mentionsConst_stripPis_false n hta_noT hstT p hp

private theorem instOpen_erasedEq :
    ∀ {vs ws : List KExpr}, List.Forall₂ Expr.ErasedEq vs ws →
      ∀ {e e' : KExpr}, Expr.ErasedEq e e' → ∀ j,
        Expr.ErasedEq (instOpen vs j e) (instOpen ws j e')
  | [], [], .nil, _, _, he, _ => he
  | _ :: _, _ :: _, .cons hv hs, _, _, he, j => by
    simp only [instOpen]
    rw [← hs.length_eq]
    exact instOpen_erasedEq hs (Expr.ErasedEq.instantiate1 he hv) j

private theorem instOpen_leaves :
    ∀ (vs : List KExpr) (j : Nat) (e : KExpr) (l : Nat × KExpr),
      l ∈ (instOpen vs j e).fvarLeaves →
      l ∈ e.fvarLeaves ∨ ∃ v ∈ vs, l ∈ v.fvarLeaves
  | [], _, _, _, hl => Or.inl hl
  | v :: vs, j, e, l, hl => by
    rcases instOpen_leaves vs j (e.instantiate1 v (j + vs.length)) l hl with h | h
    · rcases Expr.fvarLeaves_instantiate1 e (j + vs.length) h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨v, List.mem_cons_self, h⟩
    · obtain ⟨w, hw, hlw⟩ := h
      exact Or.inr ⟨w, List.mem_cons_of_mem _ hw, hlw⟩

/-- The comparison performed by parameter agreement differs from the constructor's own
opened domain only in free-variable annotations, all drawn from earlier former variables. -/
theorem StructDomsShared.toSharedPins {env : Ix.Kernel.Env .anon} {ta tb : KExpr} {n : Nat}
    {tfvs cfvs : List KExpr} {trest crest tbody cbody : KExpr}
    {tbs cbs : List (KExpr × Ix.Kernel.BinderMeta)}
    (hshared : StructDomsShared env ta tb n)
    (hopT : Ix.Kernel.openPisAtFvars n ta 0 = some (tfvs, trest))
    (hopC : Ix.Kernel.openPisAtFvars n tb 0 = some (cfvs, crest))
    (hstT : ta.stripPis n = some (tbs, tbody))
    (hstC : tb.stripPis n = some (cbs, cbody))
    (hclosed : tb.hasFvar = false) :
    Ix.Kernel.Semantics.SharedStructDomsJ rulesJ env cfvs tfvs n := by
  unfold Ix.Kernel.Semantics.SharedStructDomsJ
  obtain ⟨sfvs, srest, hsop, hcomp⟩ := hshared
  have hsOpen : (sfvs, srest) = (tfvs, trest) := Option.some.inj (hsop.symm.trans hopT)
  obtain ⟨hsFvs, hsRest⟩ := Prod.mk.inj hsOpen
  subst sfvs srest
  have hlenC := openPisAtFvars_len n hopC
  have hlenT := openPisAtFvars_len n hopT
  have hlenCB := Expr.stripPis_length n hstC
  have hlenTB := Expr.stripPis_length n hstT
  have hcharC := (openPisAtFvars_eq_instOpen n hstC hopC).2.2
  have hcharT := (openPisAtFvars_eq_instOpen n hstT hopT).2.2
  intro i hi
  obtain ⟨cbs', cbody', b, hsC, hb, hde⟩ := hcomp i hi
  have hsBody : (cbs', cbody') = (cbs, cbody) := Option.some.inj (hsC.symm.trans hstC)
  obtain ⟨hsBinders, hsResult⟩ := Prod.mk.inj hsBody
  subst cbs' cbody'
  have hiC : i < cfvs.length := by omega
  have hiCB : i < cbs.length := by omega
  have hgetCB : cbs[i]? = some (cbs.getD i default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiCB]
    rfl
  have hprefix : List.Forall₂ Expr.ErasedEq (cfvs.take i) (tfvs.take i) := by
    refine List.forall₂_iff_get.mpr ⟨?_, ?_⟩
    · simp only [List.length_take, hlenC, hlenT]
    · intro j hjC hjT
      have hjn : j < n := by
        have hbound : j < min i cfvs.length := by simpa only [List.length_take] using hjC
        omega
      have hjc : j < cfvs.length := by omega
      have hjt : j < tfvs.length := by omega
      have hjcb : j < cbs.length := by omega
      have hjtb : j < tbs.length := by omega
      have hcj := hcharC j cbs[j] cfvs[j] (List.getElem?_eq_getElem hjcb)
        (List.getElem?_eq_getElem hjc)
      have htj := hcharT j tbs[j] tfvs[j] (List.getElem?_eq_getElem hjtb)
        (List.getElem?_eq_getElem hjt)
      simp only [List.get_eq_getElem, List.getElem_take]
      rw [hcj, htj]
      rfl
  refine ⟨cfvs[i], b, instOpen (tfvs.take i) 0 (cbs.getD i default).1,
    List.getElem?_eq_getElem hiC, hb, ?_, hde.symm, ?_⟩
  · rw [hcharC i (cbs.getD i default) cfvs[i] hgetCB (List.getElem?_eq_getElem hiC)]
    exact instOpen_erasedEq hprefix (Expr.ErasedEq.rfl _) 0
  · intro l hl
    rcases instOpen_leaves (tfvs.take i) 0 (cbs.getD i default).1 l hl with h | h
    · have hnf := (Ix.Kernel.stripPis_not_hasFvar n hstC hclosed).1
        (cbs.getD i default) (List.mem_of_getElem? hgetCB)
      rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hnf] at h
      exact nomatch h
    · exact h



private def isForallE : KExpr → Bool
  | .forallE _ _ _ => true
  | _ => false

private theorem isForallE_instantiate1_fvar {q : Nat} {ty : KExpr} {k : Nat} {e : KExpr}
    (hf : isForallE e = false) :
    isForallE (e.instantiate1 (.fvar q ty) k) = false := by
  cases e with
  | bvar i =>
    simp only [Expr.instantiate1]
    split
    · rfl
    · split <;> rfl
  | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ | letE _ _ _ _ | lit _ | proj _ _ _ =>
    simp [Expr.instantiate1, isForallE]
  | forallE _ _ _ =>
    simp [isForallE] at hf

private theorem isForallE_instOpen_false {vs : List KExpr}
    (hvs : ∀ v ∈ vs, ∃ q ty, v = .fvar q ty) :
    ∀ {j : Nat} {e : KExpr}, isForallE e = false → isForallE (instOpen vs j e) = false := by
  induction vs with
  | nil => intro _ _ hf; exact hf
  | cons v rest ih =>
    intro j e hf
    obtain ⟨q, ty, rfl⟩ := hvs v List.mem_cons_self
    exact ih (fun x hx => hvs x (List.mem_cons_of_mem _ hx)) (isForallE_instantiate1_fvar hf)

theorem instOpen_forallE_inv {vs : List KExpr}
    (hvs : ∀ v ∈ vs, ∃ q ty, v = .fvar q ty)
    {j : Nat} {e Db Bb : KExpr} {mb : Ix.Kernel.BinderMeta}
    (heq : instOpen vs j e = .forallE Db Bb mb) :
    ∃ db_raw bb_raw,
      e = .forallE db_raw bb_raw mb ∧
      Db = instOpen vs j db_raw ∧
      Bb = instOpen vs (j + 1) bb_raw := by
  by_cases hfa : isForallE e = true
  · cases e with
    | forallE d b m =>
      rw [instOpen_forallE] at heq
      simp only [Expr.forallE.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact ⟨d, b, rfl, rfl, rfl⟩
    | _ => simp [isForallE] at hfa
  · simp only [Bool.not_eq_true] at hfa
    have hf : isForallE (instOpen vs j e) = false :=
      isForallE_instOpen_false hvs hfa
    rw [heq] at hf
    exact nomatch hf

private theorem check_param_agreement_go_spec (hCore : IxVM.Consistency.Core S₀)
    {c : Ctx} :
    ∀ (m : Nat) {d : Nat} {Γ : Nat → KExpr} {tfvs_pre : List KExpr}
      {ta_open tb_raw : KExpr} {rc pta ptb types r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      d + m < 4294967296 →
      tfvs_pre.length = d →
      (∀ v ∈ tfvs_pre, ∃ q ty, v = .fvar q ty) →
      RCRep c.t c.lim h rc →
      TypesRep c.κ Γ h d types →
      GhostScoped Γ d →
      EnvFacts c →
      LoadFacts c →
      Good c cs →
      Tm c.κ d Γ h 0 ta_open pta →
      Tm c.κ d Γ h 0 (instOpen tfvs_pre 0 tb_raw) ptb →
      ObsFn W "KernelCheck::check_param_agreement_go"
        [rc, pta, ptb, .field (m : F), types] h r h' cs →
      ∃ (tfvs_suf : List KExpr) (trest : KExpr)
        (cbs_suf : List (KExpr × Ix.Kernel.BinderMeta)) (cbody : KExpr),
        Ix.Kernel.openPisAtFvars m ta_open d = some (tfvs_suf, trest) ∧
        tb_raw.stripPis m = some (cbs_suf, cbody) ∧
        ∀ k < m, ∃ fv,
          tfvs_suf[k]? = some fv ∧
          DefEq c.env (d + k) fv.fvarTypeD
            (instOpen ((tfvs_pre ++ tfvs_suf).take (d + k)) 0 (cbs_suf.getD k default).1)
  | 0, _, _, _, ta_open, tb_raw, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ev => by
    match Obs.«KernelCheck::check_param_agreement_go».obs ev with
    | .n0 .. =>
      exact ⟨[], ta_open, [], tb_raw, rfl, rfl, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩
    | .other (hne20 := hne) .. =>
      exact absurd rfl hne
  | m + 1, d, Γ, tfvs_pre, ta_open, tb_raw, rc, pta, ptb, types, r, h, h', cs,
      hdm, hlen, hvs_pre, hrc, hty, hsc, hef, hlf, hgood, hta, htb, ev => by
    match Obs.«KernelCheck::check_param_agreement_go».obs ev with
    | .n0 (hv14 := hv0) .. =>
      exact absurd hv0 (succ_field_ne_zero (by omega))
    | .other (x_da := xda) (x_ba := xba) (w43 := w43) (x_db := xdb) (x_bb := xbb)
        (w78 := w78) (v94 := v94) (m95 := m95) (cs105 := cs_de) (m168 := m168)
        (cs201 := cs_go) (v207 := v207) (ld35 := ld_a) (ld70 := ld_b)
        (ev107 := ev_de) (heq166 := hv94) (hm178 := hm168) (op243 := op_sub)
        (ev203 := ev_go) (hc252 := hc) .. =>
      subst hc hv94
      obtain ⟨Da, Ba, ℓa, rfl, hDa, hBa, _⟩ := hta.forallE_of_load ld_a
      obtain ⟨Db, Bb, ℓb, heq_tb, hDb, hBb, _⟩ := htb.forallE_of_load ld_b
      obtain ⟨db_raw, bb_raw, rfl, hDb_eq, hBb_eq⟩ := instOpen_forallE_inv hvs_pre heq_tb
      have hg_de : Good c cs_de := hgood.sub (fun x hx => by simp [hx])
      have hg_go : Good c cs_go := hgood.sub (fun x hx => by simp [hx])
      have hde : DefEq c.env d Da Db :=
        core_defeq hCore hrc hty hsc hef hlf hg_de ev_de hDa hDb
      have ext_de := ev_de.heap_extends
      obtain ⟨ext_cons, hty', hsc'⟩ :=
        push_binder_types (hDa.mono ext_de) (hty.mono ext_de) hsc
      rw [← hm168] at ext_cons hty'
      have ext_all := ext_de.trans ext_cons
      let fv := Expr.fvar (md := .anon) d Da
      let Γ' := Ghost.extend Γ d Da
      have hBa_open : Tm c.κ (d + 1) Γ' m168 0 (Ba.instantiate1 fv) xba :=
        Tm.open_body (Ghost.extend_at Γ d Da) (Ghost.extend_below Γ d Da) (hBa.mono ext_all)
      have hBb_open₀ : Tm c.κ (d + 1) Γ' m168 0 (Bb.instantiate1 fv) xbb :=
        Tm.open_body (Ghost.extend_at Γ d Da) (Ghost.extend_below Γ d Da) (hBb.mono ext_all)
      have hBb_eq' : Bb.instantiate1 fv = instOpen (tfvs_pre ++ [fv]) 0 bb_raw := by
        rw [hBb_eq, instOpen_append]
        rfl
      rw [hBb_eq'] at hBb_open₀
      rw [evalBinOp_sub_succ m op_sub] at ev_go
      have hlen' : (tfvs_pre ++ [fv]).length = d + 1 := by simp [hlen]
      have hvs' : ∀ v ∈ tfvs_pre ++ [fv], ∃ q ty, v = .fvar q ty := by
        intro v hv
        rcases List.mem_append.mp hv with hv | hv
        · exact hvs_pre v hv
        · simp only [List.mem_singleton] at hv
          exact ⟨d, Da, hv⟩
      obtain ⟨tfvs_suf, trest, cbs_suf, cbody, hop_suf, hst_suf, hdoms_suf⟩ :=
        check_param_agreement_go_spec hCore m (by omega) hlen' hvs'
          (hrc.mono ext_all) hty' hsc' hef hlf hg_go hBa_open hBb_open₀ ev_go
      refine ⟨fv :: tfvs_suf, trest, (db_raw, bmeta ℓb) :: cbs_suf, cbody, ?_, ?_, ?_⟩
      · simp [Ix.Kernel.openPisAtFvars, fv, hop_suf]
      · simp [Expr.stripPis, hst_suf]
      · intro k hk
        cases k with
        | zero =>
          refine ⟨fv, rfl, ?_⟩
          have htake : (tfvs_pre ++ fv :: tfvs_suf).take d = tfvs_pre :=
            List.take_left' hlen
          rw [Nat.add_zero, htake]
          simpa [fv, Expr.fvarTypeD, hDb_eq] using hde
        | succ k' =>
          obtain ⟨fv', hfv', hde'⟩ := hdoms_suf k' (by omega)
          refine ⟨fv', hfv', ?_⟩
          have happ : (tfvs_pre ++ [fv]) ++ tfvs_suf = tfvs_pre ++ fv :: tfvs_suf := by
            simp
          rw [happ, show d + 1 + k' = d + (k' + 1) by omega] at hde'
          exact hde'

/-- `check_param_agreement` establishes `StructDomsShared c.env ta tb n`. -/
theorem check_param_agreement_spec (hCore : IxVM.Consistency.Core S₀) {c : Ctx}
    {Γ : Nat → KExpr} {ta tb : KExpr} {n : Nat}
    {rc pta ptb r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hn : n < 4294967296)
    (hrc : RCRep c.t c.lim h rc)
    (hef : EnvFacts c)
    (hlf : LoadFacts c)
    (hgood : Good c cs)
    (hta : Tm c.κ 0 Γ h 0 ta pta)
    (htb : Tm c.κ 0 Γ h 0 tb ptb)
    (ev : ObsFn W "KernelCheck::check_param_agreement" [rc, pta, ptb, .field (n : F)] h r h' cs) :
    StructDomsShared c.env ta tb n := by
  match Obs.«KernelCheck::check_param_agreement».obs ev with
  | .run (cs4 := cs_go) (m41 := m41) (hm49 := hm41) (ev6 := ev_go) (hc53 := hc) =>
    subst hc
    have ext : Heap.Extends h m41 := by rw [hm41]; exact Heap.Extends.snoc h _
    have hty : TypesRep c.κ Γ m41 0 (.ptr (.enum kexprListEnum) h.length) := by
      rw [hm41]; exact typesRep_alloc_nil c.κ Γ h
    have hg_go : Good c cs_go := hgood.sub (fun x hx => by simp [hx])
    obtain ⟨tfvs, trest, cbs, cbody, hop, hst, hdoms⟩ :=
      check_param_agreement_go_spec hCore n (d := 0) (tfvs_pre := []) (tb_raw := tb)
        (by omega) rfl (fun _ hv => nomatch hv) (hrc.mono ext) hty (ghostScoped_zero Γ)
        hef hlf hg_go (hta.mono ext) (htb.mono ext) ev_go
    refine ⟨tfvs, trest, hop, fun i hi => ?_⟩
    obtain ⟨fv, hfv, hde⟩ := hdoms i hi
    rw [Nat.zero_add, List.nil_append] at hde
    exact ⟨cbs, cbody, fv, hst, hfv, hde⟩

/-! ## Constructor residual opening and `check_field_universes` -/

theorem instOpen_bvar_at :
    ∀ (vs : List KExpr) {j r : Nat} {v : KExpr},
      (∀ w ∈ vs, ∃ q ty, w = .fvar q ty) →
      vs[r]? = some v →
      instOpen vs j (.bvar (j + (vs.length - 1 - r))) = v
  | [], _, _, _, _, hr => nomatch hr
  | w :: rest, j, 0, v, hvs, hr => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hr
    subst hr
    obtain ⟨q, ty, rfl⟩ := hvs w List.mem_cons_self
    simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_zero, instOpen,
      Expr.instantiate1, ↓reduceIte, instOpen_fvar]
  | w :: rest, j, r + 1, v, hvs, hr => by
    simp only [List.getElem?_cons_succ] at hr
    have hr_lt : r < rest.length := (List.getElem?_eq_some_iff.mp hr).1
    have hidx : j + ((w :: rest).length - 1 - (r + 1)) = j + (rest.length - 1 - r) := by
      simp; omega
    rw [hidx]
    simp only [instOpen, Expr.instantiate1,
      ite_eq_right (show j + (rest.length - 1 - r) ≠ j + rest.length by omega),
      ite_eq_right (show ¬ (j + rest.length < j + (rest.length - 1 - r)) by omega)]
    exact instOpen_bvar_at rest (fun x hx => hvs x (List.mem_cons_of_mem _ hx)) hr

theorem nat_openPisAtFvars_split :
    ∀ (a b : Nat) {e : KExpr} {d : Nat} {fvsA : List KExpr} {oA : KExpr}
      {fvs₁ : List KExpr} {r₁ : KExpr},
      Ix.Kernel.openPisAtFvars (a + b) e d = some (fvsA, oA) →
      Ix.Kernel.openPisAtFvars a e d = some (fvs₁, r₁) →
      ∃ fvs₂, Ix.Kernel.openPisAtFvars b r₁ (d + a) = some (fvs₂, oA) ∧ fvsA = fvs₁ ++ fvs₂
  | 0, b, e, d, fvsA, oA, fvs₁, r₁, hab, ha => by
    simp only [Ix.Kernel.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at ha
    obtain ⟨rfl, rfl⟩ := ha
    rw [Nat.zero_add] at hab
    rw [Nat.add_zero]
    exact ⟨fvsA, hab, rfl⟩
  | a + 1, b, e, d, fvsA, oA, fvs₁, r₁, hab, ha => by
    cases e with
    | forallE dom bo _ =>
      rw [show a + 1 + b = a + b + 1 by omega] at hab
      simp only [Ix.Kernel.openPisAtFvars] at hab ha
      rcases h1 : Ix.Kernel.openPisAtFvars (a + b) (bo.instantiate1 (.fvar d dom)) (d + 1) with
        _ | ⟨fvs₁', oA'⟩ <;> rw [h1] at hab
      · exact nomatch hab
      · simp only [Option.some.injEq, Prod.mk.injEq] at hab
        obtain ⟨rfl, rfl⟩ := hab
        rcases h2 : Ix.Kernel.openPisAtFvars a (bo.instantiate1 (.fvar d dom)) (d + 1) with
          _ | ⟨fvs₂', r₁'⟩ <;> rw [h2] at ha
        · exact nomatch ha
        · simp only [Option.some.injEq, Prod.mk.injEq] at ha
          obtain ⟨rfl, rfl⟩ := ha
          obtain ⟨fvs₂, hb', happ⟩ := nat_openPisAtFvars_split a b h1 h2
          rw [show d + (a + 1) = d + 1 + a by omega]
          exact ⟨fvs₂, hb', by simp [happ]⟩
    | _ => simp [Ix.Kernel.openPisAtFvars] at ha

/-- Open parameters `nP` and fields `nF` on a constructor whose `stripPis (nP + nF)` has residual
`mkAppN (.const T (lps.map .param)) (structPsAt nF nP ++ es)`. -/
theorem ctor_openPis_residual {T : KKey} {lps : List LevelParam} {nP nIdx nF : Nat}
    {cty : KExpr} {cbs : List (KExpr × Ix.Kernel.BinderMeta)} {es : List KExpr}
    (hstrip : cty.stripPis (nP + nF) =
      some (cbs, Expr.mkAppN (.const T (lps.map .param)) (Ix.Kernel.structPsAt nF nP ++ es)))
    (hes_len : es.length = nIdx) :
    ∃ fvsP crest xFvs idxArgs,
      Ix.Kernel.openPisAtFvars nP cty 0 = some (fvsP, crest) ∧
      Ix.Kernel.openPisAtFvars nF crest nP =
        some (xFvs, Expr.mkAppN (.const T (lps.map .param)) (fvsP ++ idxArgs)) ∧
      Ix.Kernel.openPisAtFvars (nP + nF) cty 0 =
        some (fvsP ++ xFvs, Expr.mkAppN (.const T (lps.map .param)) (fvsP ++ idxArgs)) ∧
      idxArgs.length = nIdx := by
  obtain ⟨cbs₁, crest₀, _, hstP, _, _, _⟩ := stripPis_split nP nF hstrip
  obtain ⟨fvsP, crest, hopP⟩ :=
    Ix.Kernel.Model.openPisAtFvars_of_stripPis_isSome nP 0 (by rw [hstP]; rfl)
  obtain ⟨fvsAll, xrest, hopAll⟩ :=
    Ix.Kernel.Model.openPisAtFvars_of_stripPis_isSome (nP + nF) 0 (by rw [hstrip]; rfl)
  obtain ⟨xFvs, hopF, rfl⟩ := nat_openPisAtFvars_split nP nF hopAll hopP
  rw [Nat.zero_add] at hopF
  obtain ⟨hxrest_eq, hall_fv, _⟩ := openPisAtFvars_eq_instOpen (nP + nF) hstrip hopAll
  have hfvsP_len : fvsP.length = nP := openPisAtFvars_len nP hopP
  have hxFvs_len : xFvs.length = nF := openPisAtFvars_len nF hopF
  have hall_len : (fvsP ++ xFvs).length = nP + nF := by simp [hfvsP_len, hxFvs_len]
  have hps_map : (Ix.Kernel.structPsAt nF nP).map (instOpen (fvsP ++ xFvs) 0) = fvsP := by
    apply List.ext_getElem?
    intro p
    by_cases hp : p < nP
    · have hp_fvs : p < fvsP.length := by omega
      have hget : (fvsP ++ xFvs)[p]? = some fvsP[p] := by
        rw [List.getElem?_append_left hp_fvs, List.getElem?_eq_getElem hp_fvs]
      simp only [Ix.Kernel.structPsAt, List.map_map, List.getElem?_map,
        List.getElem?_range hp, Option.map_some, Function.comp_apply]
      rw [List.getElem?_eq_getElem hp_fvs]
      congr 1
      have hbidx : nF + nP - 1 - p = 0 + ((fvsP ++ xFvs).length - 1 - p) := by
        rw [hall_len]; omega
      rw [hbidx]
      exact instOpen_bvar_at (fvsP ++ xFvs) hall_fv hget
    · have hlen_ps : ((Ix.Kernel.structPsAt nF nP : List KExpr).map
          (instOpen (fvsP ++ xFvs) 0)).length = nP := by simp [Ix.Kernel.structPsAt]
      rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  let idxArgs := es.map (instOpen (fvsP ++ xFvs) 0)
  have hxrest_app :
      xrest = Expr.mkAppN (.const T (lps.map .param)) (fvsP ++ idxArgs) := by
    rw [hxrest_eq, instOpen_mkAppN, instOpen_const, List.map_append, hps_map]
  rw [hxrest_app] at hopF hopAll
  exact ⟨fvsP, crest, xFvs, idxArgs, hopP, hopF, hopAll, by simp [idxArgs, hes_len]⟩

private theorem check_field_universes_skip_params_spec {c : Ctx} :
    ∀ (m : Nat) {d : Nat} {Γ : Nat → KExpr} {nF : Nat}
      {cty_open : KExpr} {rc pcty pind types r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      d + m < 4294967296 →
      RCRep c.t c.lim h rc →
      TypesRep c.κ Γ h d types →
      GhostScoped Γ d →
      Tm c.κ d Γ h 0 cty_open pcty →
      NoTopLetSpine (m + nF) h pcty →
      ObsFn W "KernelCheck::check_field_universes_skip_params"
        [rc, pcty, .field (m : F), pind, types] h r h' cs →
      ∃ (fvsP : List KExpr) (crest : KExpr) (Γ' : Nat → KExpr)
        (pcty' types' : SourceValue F) (h₁ : Heap F) (cs_in : List (Call F)),
        Ix.Kernel.openPisAtFvars m cty_open d = some (fvsP, crest) ∧
        Heap.Extends h h₁ ∧
        (∀ x ∈ cs_in, x ∈ cs) ∧
        RCRep c.t c.lim h₁ rc ∧
        TypesRep c.κ Γ' h₁ (d + m) types' ∧
        GhostScoped Γ' (d + m) ∧
        Tm c.κ (d + m) Γ' h₁ 0 crest pcty' ∧
        NoTopLetSpine nF h₁ pcty' ∧
        ObsFn W "KernelCheck::check_field_universes_inner"
          [rc, pcty', pind, types'] h₁ r h' cs_in
  | 0, d, Γ, nF, cty_open, rc, pcty, pind, types, r, h, h', cs,
      _, hrc, hty, hsc, hcty, hnt, ev => by
    match Obs.«KernelCheck::check_field_universes_skip_params».obs ev with
    | .n0 (cs18 := cs_in) (ev20 := ev_in) (hc53 := hc) .. =>
      subst hc
      rw [Nat.zero_add] at hnt
      rw [Nat.add_zero]
      exact ⟨[], cty_open, Γ, pcty, types, h, cs_in, rfl, Heap.Extends.refl h,
        (fun x hx => by simp [hx]), hrc, hty, hsc, hcty, hnt, ev_in⟩
    | .other (hne54 := hne) .. =>
      exact absurd rfl hne
  | m + 1, d, Γ, nF, cty_open, rc, pcty, pind, types, r, h, h', cs,
      hdm, hrc, hty, hsc, hcty, hnt, ev => by
    match Obs.«KernelCheck::check_field_universes_skip_params».obs ev with
    | .n0 (hv14 := hv0) .. =>
      exact absurd hv0 (succ_field_ne_zero (by omega))
    | .other (x_dom := xdom) (x_body := xbody) (w77 := w77) (cs96 := cs96)
        (v101 := v101) (m141 := m141) (ld69 := ld) (op131 := op_sub)
        (hm149 := hm141) (ev98 := ev_rec) (hc169 := hc) .. =>
      subst hc
      obtain ⟨D, B, ℓ, rfl, hD, hB, _⟩ := hcty.forallE_of_load ld
      rw [show m + 1 + nF = (m + nF) + 1 by omega] at hnt
      obtain ⟨_, bp, _, hv_nt, hnt_B⟩ := hnt.succ_forall ld
      injection hv_nt with _ _ hxs_nt; injection hxs_nt with _ hxs_nt
      injection hxs_nt with hxb_nt _; subst hxb_nt
      obtain ⟨ext_cons, hty', hsc'⟩ := push_binder_types hD hty hsc
      rw [← hm141] at ext_cons hty'
      let fv := Expr.fvar (md := .anon) d D
      let Γ₁ := Ghost.extend Γ d D
      have hB_open : Tm c.κ (d + 1) Γ₁ m141 0 (B.instantiate1 fv) xbody :=
        Tm.open_body (Ghost.extend_at Γ d D) (Ghost.extend_below Γ d D) (hB.mono ext_cons)
      rw [evalBinOp_sub_succ m op_sub] at ev_rec
      obtain ⟨fvsP', crest, Γ', pcty', types', h₁, cs_in, hop', ext', hsub',
          hrc', hty'', hsc'', hcrest, hnt', ev_in⟩ :=
        check_field_universes_skip_params_spec m (d := d + 1) (by omega)
          (hrc.mono ext_cons) hty' hsc' hB_open (hnt_B.mono ext_cons) ev_rec
      rw [show d + 1 + m = d + (m + 1) by omega] at hty'' hsc'' hcrest
      refine ⟨fv :: fvsP', crest, Γ', pcty', types', h₁, cs_in, ?_, ext_cons.trans ext',
        (fun x hx => by simp [hsub' x hx]), hrc', hty'', hsc'', hcrest, hnt', ev_in⟩
      simp [Ix.Kernel.openPisAtFvars, fv, hop']

private theorem check_field_universes_inner_spec (hLevels : IxVM.Consistency.Levels)
    (hCore : IxVM.Consistency.Core S₀) {c : Ctx} {T : KKey} {us : List KLevel}
    {resSort ind_lvl : KLevel} (hlveq : LvEq resSort ind_lvl) :
    ∀ (m : Nat) {d : Nat} {Γ : Nat → KExpr} {crest : KExpr} {xFvs args : List KExpr}
      {rc pty pind types r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      Ix.Kernel.openPisAtFvars m crest d = some (xFvs, Expr.mkAppN (.const T us) args) →
      RCRep c.t c.lim h rc →
      TypesRep c.κ Γ h d types →
      GhostScoped Γ d →
      EnvFacts c →
      LoadFacts c →
      Good c cs →
      RepKLevel h ind_lvl pind →
      Tm c.κ d Γ h 0 crest pty →
      NoTopLetSpine m h pty →
      ObsFn W "KernelCheck::check_field_universes_inner" [rc, pty, pind, types] h r h' cs →
      ∃ sorts : List KLevel,
        sorts.length = m ∧
        ∀ i < m, ∃ fv ty u,
          xFvs[i]? = some fv ∧ sorts[i]? = some u ∧
          Infer c.env .full (d + i) fv.fvarTypeD ty ∧
          Red c.env (d + i) ty (.sort u) ∧
          (∀ φ, Level.eval φ u ≤ Level.eval φ resSort)
  | 0, d, Γ, crest, xFvs, args, rc, pty, pind, types, r, h, h', cs,
      hop, _, _, _, _, _, _, _, hpty, _, ev => by
    simp only [Ix.Kernel.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, rfl⟩ := hop
    match Obs.«KernelCheck::check_field_universes_inner».obs ev with
    | .other .. =>
      exact ⟨[], rfl, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
    | .Forall (ld12 := ld) .. =>
      obtain ⟨D, B, ℓ, heq, _⟩ := hpty.forallE_of_load ld
      exact absurd heq (mkAppN_const_not_forallE T us args D B (bmeta ℓ))
  | m + 1, d, Γ, crest, xFvs, args, rc, pty, pind, types, r, h, h', cs,
      hop, hrc, hty, hsc, hef, hlf, hgood, hpind, hpty, hnt, ev => by
    match Obs.«KernelCheck::check_field_universes_inner».obs ev with
    | .other (ld12 := ld) (hne183 := hne) .. =>
      exact (hnt.succ_not_other ld hne).elim
    | .Forall (x_dom := xdom) (x_body := xbody) (w20 := w20) (v36 := v36) (m37 := m37)
        (cs47 := cs_es) (v85 := v85) (m88 := m88) (cs96 := cs_leq) (cs125 := cs_in)
        (m154 := m154) (ld12 := ld) (ev49 := ev_es) (ev98 := ev_leq) (heq121 := hv85)
        (hm162 := hm154) (ev127 := ev_in) (hc182 := hc) =>
      subst hc hv85
      obtain ⟨D, B, ℓ, rfl, hD, hB, _⟩ := hpty.forallE_of_load ld
      simp only [Ix.Kernel.openPisAtFvars] at hop
      rcases hop' : Ix.Kernel.openPisAtFvars m (B.instantiate1 (.fvar d D)) (d + 1) with
        _ | ⟨xFvs', o'⟩ <;> rw [hop'] at hop
      · exact nomatch hop
      · simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        have hg_es : Good c cs_es := hgood.sub (fun x hx => by simp [hx])
        have hg_leq : Good c cs_leq := hgood.sub (fun x hx => by simp [hx])
        have hg_in : Good c cs_in := hgood.sub (fun x hx => by simp [hx])
        obtain ⟨sdom, u₀, ℓ_dom, hinf_d, hred_d, hrep_dom, hlveq_dom⟩ :=
          core_ensure_sort hCore hrc hty hsc hef hlf hg_es ev_es hD
        have e1 := ev_es.heap_extends
        have e2 := ev_leq.heap_extends
        have hleq_lvl := levels_leq_one hLevels ev_leq hg_leq.2 hrep_dom
          (repKLevel_heapMono₂ e1 hpind)
        have hleq_u : ∀ φ, Level.eval φ u₀ ≤ Level.eval φ resSort := by
          intro φ
          rw [hlveq_dom φ, hlveq φ]
          exact hleq_lvl φ
        obtain ⟨ext_cons, hty', hsc'⟩ :=
          push_binder_types (hD.mono (e1.trans e2)) (hty.mono (e1.trans e2)) hsc
        rw [← hm154] at ext_cons hty'
        have ext_all := e1.trans (e2.trans ext_cons)
        let fv := Expr.fvar (md := .anon) d D
        let Γ' := Ghost.extend Γ d D
        have hB_open : Tm c.κ (d + 1) Γ' m154 0 (B.instantiate1 fv) xbody :=
          Tm.open_body (Ghost.extend_at Γ d D) (Ghost.extend_below Γ d D) (hB.mono ext_all)
        obtain ⟨_, bp, _, hv_nt, hnt_B₀⟩ := hnt.succ_forall ld
        injection hv_nt with _ _ hxs_nt; injection hxs_nt with _ hxs_nt
        injection hxs_nt with hxb_nt _; subst hxb_nt
        have hnt_B : NoTopLetSpine m m154 xbody := hnt_B₀.mono ext_all
        obtain ⟨sorts', hlen', hsorts'⟩ :=
          check_field_universes_inner_spec hLevels hCore hlveq m hop'
            (hrc.mono ext_all) hty' hsc' hef hlf hg_in
            (repKLevel_heapMono₂ ext_all hpind) hB_open hnt_B ev_in
        refine ⟨u₀ :: sorts', by simp [hlen'], fun i hi => ?_⟩
        cases i with
        | zero =>
          rw [Nat.add_zero]
          exact ⟨fv, sdom, u₀, rfl, rfl, hinf_d, hred_d, hleq_u⟩
        | succ i' =>
          obtain ⟨fv', ty', u', hfv', hu', hinf', hred', hleq'⟩ := hsorts' i' (by omega)
          rw [show d + 1 + i' = d + (i' + 1) by omega] at hinf' hred'
          exact ⟨fv', ty', u', hfv', hu', hinf', hred', hleq'⟩

/-- `check_field_universes` establishes `FieldSortsJ rulesJ c.env (Level.isEquiv resSort .zero) false`
for constructor fields `xFvs` at `large = false`. -/
theorem check_field_universes_spec (hLevels : IxVM.Consistency.Levels)
    (hCore : IxVM.Consistency.Core S₀) {c : Ctx} {T : KKey} {us : List KLevel}
    {resSort ind_lvl : KLevel} {nP nF : Nat} {Γ : Nat → KExpr}
    {cty stype_cty crest : KExpr} {fvsP xFvs idxArgs : List KExpr}
    {rc pcty pind r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hnP : nP < 4294967296)
    (hlveq : LvEq resSort ind_lvl)
    (hinf_cty : Infer c.env .full 0 cty stype_cty)
    (hopP : Ix.Kernel.openPisAtFvars nP cty 0 = some (fvsP, crest))
    (hopF : Ix.Kernel.openPisAtFvars nF crest nP =
      some (xFvs, Expr.mkAppN (.const T us) (fvsP ++ idxArgs)))
    (hopAll : Ix.Kernel.openPisAtFvars (nP + nF) cty 0 =
      some (fvsP ++ xFvs, Expr.mkAppN (.const T us) (fvsP ++ idxArgs)))
    (hrc : RCRep c.t c.lim h rc)
    (hef : EnvFacts c)
    (hlf : LoadFacts c)
    (hgood : Good c cs)
    (hpind : RepKLevel h ind_lvl pind)
    (hcty : Tm c.κ 0 Γ h 0 cty pcty)
    (hnt : NoTopLetSpine (nP + nF) h pcty)
    (ev : ObsFn W "KernelCheck::check_field_universes"
      [rc, pcty, .field (nP : F), pind] h r h' cs) :
    ∃ sorts : List KLevel,
      FieldSortsJ rulesJ c.env (Level.isEquiv resSort .zero == some true) false resSort
        nP xFvs idxArgs nF sorts := by
  match Obs.«KernelCheck::check_field_universes».obs ev with
  | .Zero (ld12 := ld_zero) .. =>
    have hind_zero : ind_lvl = .zero := by
      cases hpind with
      | zero _ => rfl
      | succ cell _ | max cell _ _ | imax cell _ _ | param _ cell =>
        exact (load_cell_ne cell ld_zero (by decide)).elim
    subst hind_zero
    have hisProp : (Level.isEquiv resSort .zero == some true) = true :=
      isEquiv_zero_of_eval_zero (fun φ => hlveq φ)
    have hfvsP_len : fvsP.length = nP := openPisAtFvars_len nP hopP
    have hall := infer_openPisAtFvars_sorts (nP + nF) hinf_cty hopAll
    have hfield : ∀ i : Fin nF, ∃ fv sdom u,
        xFvs[i.1]? = some fv ∧
        Infer c.env .full (nP + i.1) fv.fvarTypeD sdom ∧
        Red c.env (nP + i.1) sdom (.sort u) := by
      intro ⟨i, hi⟩
      obtain ⟨fv, sdom, u, hfv, hinf, hred⟩ := hall (nP + i) (by omega)
      rw [Nat.zero_add] at hinf hred
      rw [List.getElem?_append_right (by omega), hfvsP_len, Nat.add_sub_cancel_left] at hfv
      exact ⟨fv, sdom, u, hfv, hinf, hred⟩
    let sorts : List KLevel := (List.finRange nF).map fun i =>
      Classical.choose (Classical.choose_spec (Classical.choose_spec (hfield i)))
    refine ⟨sorts, by simp [sorts], fun i hi => ?_⟩
    let fi : Fin nF := ⟨i, hi⟩
    have hspec := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hfield fi)))
    have hs_get : sorts[i]? =
        some (Classical.choose (Classical.choose_spec (Classical.choose_spec (hfield fi)))) := by
      rw [List.getElem?_eq_getElem (by simp [sorts]; exact hi)]
      simp [sorts, fi]
    exact ⟨_, _, _, hspec.1, hs_get, hspec.2.1, hspec.2.2,
      (fun hfalse => by rw [hisProp] at hfalse; exact nomatch hfalse),
      (fun _ hlarge => nomatch hlarge)⟩
  | .other (cs32 := cs_sk) (m69 := m69) (hm77 := hm69) (ev34 := ev_sk) (hc81 := hc) .. =>
    subst hc
    have ext : Heap.Extends h m69 := by rw [hm69]; exact Heap.Extends.snoc h _
    have hty : TypesRep c.κ Γ m69 0 (.ptr (.enum kexprListEnum) h.length) := by
      rw [hm69]; exact typesRep_alloc_nil c.κ Γ h
    have hg_sk : Good c cs_sk := hgood.sub (fun x hx => by simp [hx])
    obtain ⟨fvsP', crest', Γ', pcty', types', h₁, cs_in, hopP', ext', hsub',
        hrc', hty', hsc', hcrest', hnt', ev_in⟩ :=
      check_field_universes_skip_params_spec nP (d := 0) (by omega)
        (hrc.mono ext) hty (ghostScoped_zero Γ) (hcty.mono ext) (hnt.mono ext) ev_sk
    rw [Nat.zero_add] at hty' hsc' hcrest'
    rw [hopP] at hopP'
    simp only [Option.some.injEq, Prod.mk.injEq] at hopP'
    obtain ⟨rfl, rfl⟩ := hopP'
    obtain ⟨sorts, hlen, hsorts⟩ :=
      check_field_universes_inner_spec hLevels hCore hlveq nF hopF
        hrc' hty' hsc' hef hlf (hg_sk.sub hsub')
        (repKLevel_heapMono₂ (ext.trans ext') hpind) hcrest' hnt' ev_in
    refine ⟨sorts, hlen, fun i hi => ?_⟩
    obtain ⟨fv, ty, u, hfv, hu, hinf, hred, hleq⟩ := hsorts i hi
    exact ⟨fv, ty, u, hfv, hu, hinf, hred, (fun _ => hleq), (fun _ hlarge => nomatch hlarge)⟩

/-! ## Strict positivity (`check_positivity` → `recFieldKind ≠ .negative ∧ ≠ .unsupported`) -/

private theorem assert_occ_param_bvars_go {κ : _root_.Address → KKey} {Γ : Nat → KExpr}
    {nP depth : Nat} (hnP_lt : nP < 4294967296) (hnP_le : nP ≤ depth)
    (hdepth_lt : depth < 9223372036854775808) :
    ∀ (m i : Nat) {args : List KExpr} {pargs r : SourceValue F}
      {h h' : Heap F} {cs : List (Call F)},
      m + i = nP →
      RepList kexprListEnum (TmExact κ 0 Γ · depth) h args pargs →
      ObsFn W "KernelCheck::assert_occ_param_bvars"
        [pargs, .field (nP : F), .field (depth : F), .field (i : F)] h r h' cs →
      args.take m = (List.range m).map (fun t => .bvar (depth - 1 - (i + t)))
  | 0, i, args, pargs, r, h, h', cs, hmi, _, ev => by
    match Obs.«KernelCheck::assert_occ_param_bvars».obs ev with
    | .n0 .. => simp
    | .other (op17 := op) (hne29 := hne) .. =>
      have hi : i = nP := by omega
      cases hi.symm
      rw [evalBinOp_sub_nat (Nat.le_refl nP) op, Nat.sub_self] at hne
      exact absurd rfl hne
  | m + 1, i, args, pargs, r, h, h', cs, hmi, hargs, ev => by
    match Obs.«KernelCheck::assert_occ_param_bvars».obs ev with
    | .n0 (op17 := op) .. =>
      have hsub : (.field ((0 : Nat) : F) : SourceValue F) =
          .field (((nP - i : Nat) : F)) := by
        simpa using evalBinOp_sub_nat (by omega : i ≤ nP) op
      have heq := nat_eq_of_field_eq (by decide) (by omega) hsub
      omega
    | .other (x_arg := xarg) (x_rest := xrest) (x_j := xj)
        (ld44 := ld_cons) (ld73 := ld_bvar) (op127 := op_d1)
        (op119 := op_sub) (heq130 := hxj_eq) (op175 := op_add) (ev136 := ev_rec) .. =>
      obtain ⟨a, rest, rfl, ha, hrest⟩ := RepList.cons_of_load hargs ld_cons
      obtain ⟨jf, rfl, hjf_lt, hcases⟩ := ha.bvar_of_load ld_bvar
      rcases hcases with ⟨_, rfl⟩ | ⟨_, hd, _⟩
      · rw [evalBinOp_sub_nat (by omega : 1 ≤ depth) op_d1] at op_sub
        rw [evalBinOp_sub_nat (by omega : i ≤ depth - 1) op_sub] at hxj_eq
        injection hxj_eq with hjf_eq
        have htarget_lt : depth - 1 - i < 9223372036854775808 := by omega
        have hj_val : ZMod.val jf = depth - 1 - i := by
          rw [hjf_eq]
          exact ZMod.val_natCast_of_lt (Nat.lt_trans htarget_lt (by decide))
        rw [evalBinOp_add_one i op_add] at ev_rec
        have hrec := assert_occ_param_bvars_go hnP_lt hnP_le hdepth_lt m (i + 1)
          (by omega) hrest ev_rec
        rw [hj_val, List.take_succ_cons, hrec, List.range_succ_eq_map]
        simp only [Nat.add_zero, List.cons.injEq, true_and, List.map_cons, List.map_map]
        refine List.map_congr_left fun t _ => ?_
        congr 1
        omega
      · omega

private theorem check_valid_ind_app_spec {c : Ctx} {b₀ a : Bytes.Address} {T : KKey}
    {lps : List LevelParam} {nP nIdx nCtors o k : Nat} {Γ : Nat → KExpr}
    {us : List KLevel} {args : List KExpr} {E : KExpr}
    {pca pus pargs bas r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hlps : lps = List.range lps.length)
    (hlps_lt : lps.length < 4294967296)
    (hnPI_lt : nP + nIdx < 4294967296)
    (hdepth_lt : nP + o + k < 9223372036854775808)
    (hpeer : OneTypePeerFacts c b₀ T lps.length nP nIdx nCtors)
    (hlf : LoadFacts c)
    (hgood : Good c cs)
    (hca : Bytes.RepAddressRef addrTy h a pca)
    (hT : c.κ (ixAddr a) = T)
    (hus : RepKLevelList h us pus)
    (hargs : RepList kexprListEnum (TmExact c.κ 0 Γ · (nP + o + k)) h args pargs)
    (hargs_np : ∀ x ∈ args, noProjAt T x = true)
    (hbas : RepList addrListEnum (Bytes.RepAddressRef addrTy) h [b₀] bas)
    (hfn : E.getAppFn = .const T us)
    (hga : E.getAppArgs = args)
    (ev : ObsFn W "KernelCheck::check_valid_ind_app"
      [pca, pus, pargs, bas, .field ((nP + o + k : Nat) : F)] h r h' cs) :
    Ix.Kernel.recFamOk T lps nP nIdx (o + k) E = true := by
  match Obs.«KernelCheck::check_valid_ind_app».obs ev with
  | .run (m2 := m2) (p9 := p9) (cs15 := cs_ci) (x_occ_nlvls := xnl)
      (x_occ_params := xnp) (x_occ_indices := xni) (m88 := m88) (cs98 := cs_lvls)
      (v135 := vlen) (v136 := vsum) (m138 := m138)
      (m175 := m175) (v230 := vany) (cs241 := cs_any)
      (v244 := vdrop) (m247 := m247)
      (ev17 := ev_ci) (ld11 := ld_ci) (ev100 := ev_lvls) (ev148 := ev_len)
      (op170 := op_add) (heq173 := heq_len) (ev187 := ev_bvars) (ev257 := ev_drop)
      (ev243 := ev_any) (heq287 := hvany) (hc292 := hc) .. =>
    have hg_ci : Good c cs_ci := hgood.sub (fun x hx => by simp [hc, hx])
    have hbnd_lvls : IxVM.Consistency.Bounded cs_lvls :=
      (hgood.sub (fun x hx => by simp [hc, hx])).2
    have hg_any : Good c cs_any := hgood.sub (fun x hx => by simp [hc, hx])
    obtain ⟨ty', u', blk', b'', ld_self, _, _⟩ :=
      hpeer.self_ind pca p9 h m2 cs_ci a ev_ci hg_ci hca hT
    rw [ld_self] at ld_ci
    injection ld_ci with hval
    injection hval with _ _ h1
    injection h1 with hnl h1; injection h1 with _ h1; injection h1 with hnp h1
    injection h1 with hni _
    subst hnl hnp hni
    have e1 := ev_ci.heap_extends
    obtain ⟨hus_eq, hm88⟩ := assert_lvls_are_params_spec lps.length 0 (by omega) hbnd_lvls
      (hus.mono e1) ev_lvls
    subst hm88
    have hus_lps : us = lps.map .param := by
      rw [hus_eq]
      conv_rhs => rw [hlps]
      simp
    have hargs_m2 := repList_heapMono₂ kexprListEnum tmExact_heapMono₂ e1 hargs
    obtain ⟨hvlen, hm138⟩ := klength_exact ev_len hargs_m2
    subst hm138
    have hargs_lt : args.length < 549755813888 :=
      RomBound.bounded_length_lt hgood.2
        (c := ⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [pargs], _⟩)
        (by simp [hc]) (by simp) hargs_m2
    rw [evalBinOp_add_nat nP nIdx op_add, hvlen] at heq_len
    have hlen_eq : args.length = nP + nIdx :=
      nat_eq_of_field_eq hargs_lt (by omega) heq_len
    have htake :=
      assert_occ_param_bvars_go (κ := c.κ) (Γ := Γ) (nP := nP) (depth := nP + o + k)
        (by omega) (by omega) hdepth_lt nP 0 (by omega) hargs_m2 ev_bvars
    have htake_ps : args.take nP = Ix.Kernel.structPsAt (o + k) nP := by
      rw [htake]
      unfold Ix.Kernel.structPsAt
      apply List.map_congr_left
      intro t ht
      have ht_lt : t < nP := List.mem_range.mp ht
      congr 1
      omega
    have e3 := ev_bvars.heap_extends
    have hargs_m175 := repList_heapMono₂ kexprListEnum tmExact_heapMono₂ e3 hargs_m2
    obtain ⟨_, hdrop_rep, hm247⟩ := kdrop_exact (by omega : nP < 4294967296) ev_drop hargs_m175
    subst hm247
    rw [hvany] at ev_any
    have hbas_m175 := repList_heapMono₂ addrListEnum
      (Bytes.repAddressRef_heapMono₂ addrTy) (e1.trans e3) hbas
    have hdrop_np : ∀ x ∈ args.drop nP, noProjAt T x = true :=
      fun x hx => hargs_np x (List.mem_of_mem_drop hx)
    have hdrop_noT :=
      list_any_mentions_block_zero_spec hpeer hlf hg_any hdrop_rep hdrop_np hbas_m175 ev_any
    unfold Ix.Kernel.recFamOk
    rw [hfn, hus_lps, hga, hlen_eq, htake_ps]
    simp only [beq_self_eq_true, Bool.true_and, List.all_eq_true]
    intro x hx
    simp [hdrop_noT x hx]

private theorem check_positivity_aug_go {c : Ctx} {b₀ : Bytes.Address} {T : KKey}
    {lps : List LevelParam} {nP nIdx nCtors o : Nat} {Γ : Nat → KExpr} {h₀ : Heap F}
    (hlps : lps = List.range lps.length)
    (hlps_lt : lps.length < 4294967296)
    (hnPI_lt : nP + nIdx < 4294967296)
    (hpeer : OneTypePeerFacts c b₀ T lps.length nP nIdx nCtors)
    (hlf : LoadFacts c)
    {R E : KExpr} {k : Nat} {pdom bas r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ext₀ : Heap.Extends h₀ h)
    (hd : ∀ n, RomBound.HeapDescent h₀ (.enum kexprEnum) pdom n →
      nP + o + k + n < 9223372036854775808)
    (hgood : Good c cs)
    (hRaw₀ : RawTmExact c.κ 0 Γ h₀ (nP + o + k) R E pdom)
    (hnp : noProjAt T E = true)
    (hbas : RepList addrListEnum (Bytes.RepAddressRef addrTy) h [b₀] bas)
    (ev : ObsFn W "KernelCheck::check_positivity_aug"
      [pdom, bas, .field ((nP + o + k : Nat) : F)] h r h' cs) :
    (Ix.Kernel.recPositivity T lps nP nIdx o E k ≠ .negative ∧
     Ix.Kernel.recPositivity T lps nP nIdx o E k ≠ .unsupported) ∧
    (E.mentionsConst T = false ∨ RawRecSpine T R E) := by
  have hE : TmExact c.κ 0 Γ h (nP + o + k) E pdom := hRaw₀.toTmExact.mono ext₀
  match Obs.«KernelCheck::check_positivity_aug».obs ev with
  | .n0 (cs13 := cs13) (ev15 := ev_mb) (hc40 := hc) .. =>
    have hg1 : Good c cs13 := hgood.sub (fun x hx => by simp [hc, hx])
    have hnoT : E.mentionsConst T = false :=
      expr_mentions_block_zero_spec hpeer hlf hg1 hE hnp hbas ev_mb
    refine ⟨?_, Or.inl hnoT⟩
    cases E with
    | forallE d b m =>
      simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at hnoT
      have hrec_ord : ∀ (B : KExpr) (j : Nat),
          B.mentionsConst T = false →
          Ix.Kernel.recPositivity T lps nP nIdx o B j = .ordinary := by
        intro B
        induction B with
        | forallE d' b' _ _ ih =>
          intro j hB
          simp only [Expr.mentionsConst, Bool.or_eq_false_iff] at hB
          simp [Ix.Kernel.recPositivity, hB.1, ih (j + 1) hB.2]
        | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ | letE _ _ _ _
        | lit _ | proj _ _ _ =>
          intro j hB
          simp [Ix.Kernel.recPositivity, hB]
      have heq : Ix.Kernel.recPositivity T lps nP nIdx o (.forallE d b m) k = .ordinary := by
        simp [Ix.Kernel.recPositivity, hnoT.1, hrec_ord b (k + 1) hnoT.2]
      rw [heq]; exact ⟨by decide, by decide⟩
    | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ | letE _ _ _ _
    | lit _ | proj _ _ _ =>
      simp [Ix.Kernel.recPositivity, hnoT]
  | .other_Forall (m2 := m2) (x_idom := xidom) (x_ibody := xibody) (w64 := w64)
      (v91 := v91) (m94 := m94) (cs102 := cs_idom) (cs131 := cs_rec) (v136 := v136)
      (ev15 := ev1) (ld56 := ld_fa) (ev104 := ev_idom) (heq127 := hv91)
      (op164 := op_add) (ev133 := ev_rec) (hc166 := hc) .. =>
    subst hv91
    have e1 := ev1.heap_extends
    have e2 := ev_idom.heap_extends
    cases hRaw₀ with
    | @forallE _ _ tp₀ bp₀ lp₀ RT RB idom ibody ℓ cell₀ rdom₀ rbody₀ _ =>
      have hcell_m2 := (ext₀.trans e1).getElem?_eq cell₀
      obtain ⟨-, hxs⟩ := load_cell hcell_m2 ld_fa
      injection hxs with h1 h2; injection h2 with h2 h3; injection h3 with h3
      rw [← h1] at ev_idom
      rw [← h2] at ev_rec
      simp only [noProjAt, Bool.and_eq_true] at hnp
      have hg_idom : Good c cs_idom := hgood.sub (fun x hx => by simp [hc, hx])
      have hg_rec : Good c cs_rec := hgood.sub (fun x hx => by simp [hc, hx])
      have hbas_m2 := repList_heapMono₂ addrListEnum
        (Bytes.repAddressRef_heapMono₂ addrTy) e1 hbas
      have hidom_noT : idom.mentionsConst T = false :=
        expr_mentions_block_zero_spec hpeer hlf hg_idom
          (rdom₀.toTmExact.mono (ext₀.trans e1)) hnp.1 hbas_m2 ev_idom
      have hv136 : v136 = .field ((nP + o + (k + 1) : Nat) : F) :=
        evalBinOp_add_one (nP + o + k) op_add
      rw [hv136] at ev_rec
      have hd' : ∀ n, RomBound.HeapDescent h₀ (.enum kexprEnum) bp₀ n →
          nP + o + (k + 1) + n < 9223372036854775808 := by
        intro n dstep
        have d0 : RomBound.HeapDescent h₀ (.enum kexprEnum) _ (n + 1) :=
          .down cell₀ (by simp [Value.type]) (by simp [RomBound.cellArgs]) dstep
        have := hd (n + 1) d0
        omega
      rw [show nP + o + k + 1 = nP + o + (k + 1) by omega] at rbody₀
      have hbas_m94 := repList_heapMono₂ addrListEnum
        (Bytes.repAddressRef_heapMono₂ addrTy) e2 hbas_m2
      obtain ⟨hpos_bo, hsp_bo⟩ := check_positivity_aug_go hlps hlps_lt hnPI_lt hpeer hlf
        (ext₀.trans (e1.trans e2)) hd' hg_rec rbody₀ hnp.2 hbas_m94 ev_rec
      refine ⟨by simpa [Ix.Kernel.recPositivity, hidom_noT] using hpos_bo, ?_⟩
      rcases hsp_bo with hnoT_bo | hsp_bo
      · exact Or.inl (by simp [Expr.mentionsConst, hidom_noT, hnoT_bo])
      · exact Or.inr (.forallE hsp_bo)
    | bvarLocal cell₀ _ _ | bvarFree cell₀ _ _ _ | sort cell₀ _ | const cell₀ _ _
    | app cell₀ _ _ | lam cell₀ _ _ _ | letE cell₀ _ _ _ | litNat cell₀ _ _
    | litStr cell₀ _ _ | proj cell₀ _ _ =>
      exact (load_cell_ne ((ext₀.trans e1).getElem?_eq cell₀) ld_fa (by decide)).elim
  | .other_other_Const_n1 (m2 := m2) (m172 := m172)
      (x_head := xhd) (x_args := xargs) (x_caddr := xca) (x_us := xus)
      (m240 := m240) (cs251 := cs_peer) (cs277 := cs_va)
      (ev15 := ev1) (ev185 := ev_sp)
      (ld221 := ld_const) (ev253 := ev_peer) (ev279 := ev_va) (hc320 := hc) .. =>
    have e1 := ev1.heap_extends
    obtain ⟨hd_p, sp_p, RH, EH, RAs, args_expr, htup, hhd_rep, _, hargs_rep, hR_app, hE_app⟩ :=
      collect_spine_raw_spec (hRaw₀.mono (ext₀.trans e1)) ev_sp
    injection htup with hl; injection hl with h1 hl; injection hl with h2; subst h1 h2
    have e2 := ev_sp.heap_extends
    obtain ⟨a, us, rfl, rfl, hca, hus⟩ := hhd_rep.const_of_load ld_const
    have hnot_fa : ∀ d b m, E ≠ .forallE d b m := by
      rw [hE_app]; exact mkAppN_const_not_forallE _ _ _
    have hfn : E.getAppFn = .const (c.κ (ixAddr a)) us := by
      rw [hE_app, nat_getAppFn_mkAppN]; rfl
    have hga : E.getAppArgs = args_expr := by
      rw [hE_app, getAppArgs_mkAppN_const]
    have hnp_args : ∀ x ∈ args_expr, noProjAt T x = true := by
      have hga_np := (noProjAt_getApp hnp).2
      rwa [hga] at hga_np
    have hg_peer : Good c cs_peer := hgood.sub (fun x hx => by simp [hc, hx])
    have hg_va : Good c cs_va := hgood.sub (fun x hx => by simp [hc, hx])
    have hbas_m172 := repList_heapMono₂ addrListEnum
      (Bytes.repAddressRef_heapMono₂ addrTy) (e1.trans e2) hbas
    rcases caddr_is_peer_singleton_spec hpeer hlf hg_peer hca hbas_m172 ev_peer with
      ⟨_, hT_eq⟩ | ⟨h10, _⟩
    · have e3 := ev_peer.heap_extends
      have hdepth_lt : nP + o + k < 9223372036854775808 := by
        cases hRaw₀ with
        | bvarLocal cell₀ _ _ | bvarFree cell₀ _ _ _ | sort cell₀ _ | const cell₀ _ _
        | app cell₀ _ _ | lam cell₀ _ _ _ | forallE cell₀ _ _ _ | letE cell₀ _ _ _
        | litNat cell₀ _ _ | litStr cell₀ _ _ | proj cell₀ _ _ =>
          have := hd 0 (.here cell₀ (by simp [Value.type]))
          omega
      have hfam := check_valid_ind_app_spec hlps hlps_lt hnPI_lt hdepth_lt hpeer hlf hg_va
        (Bytes.repAddressRef_heapMono₂ addrTy e3 hca) hT_eq (hus.mono e3)
        (repList_heapMono₂ kexprListEnum tmExact_heapMono₂ e3 hargs_rep)
        hnp_args
        (repList_heapMono₂ addrListEnum (Bytes.repAddressRef_heapMono₂ addrTy) e3 hbas_m172)
        (by rwa [hT_eq] at hfn) hga ev_va
      refine ⟨?_, Or.inr (by rw [hR_app, hE_app, hT_eq]; exact .app)⟩
      rw [Ix.Kernel.recPositivity_leaf T lps nP nIdx o E k hnot_fa]
      unfold Ix.Kernel.recPositivityLeaf
      have hfn_beq : (E.getAppFn == .const T (lps.map .param)) = true := by
        unfold Ix.Kernel.recFamOk at hfam
        simp only [Bool.and_eq_true] at hfam
        exact hfam.1.1.1
      have harity_beq :
          (E.getAppArgs.length == nP + nIdx &&
            E.getAppArgs.take nP == Ix.Kernel.structPsAt (o + k) nP) = true := by
        unfold Ix.Kernel.recFamOk at hfam
        simp only [Bool.and_eq_true] at hfam
        simp [hfam.1.1.2, hfam.1.2]
      rw [hfn_beq, harity_beq, hfam]
      simp only [↓reduceIte]
      split
      · exact ⟨by decide, by decide⟩
      · split <;> exact ⟨by decide, by decide⟩
    · exact nomatch h10
  | .other_other_Const_other (heq350 := h01) .. | .other_other_other (heq385 := h01) .. =>
    exact nomatch h01
termination_by cs.length
decreasing_by
  simp [hc]
  omega

private theorem check_positivity_fields_go {c : Ctx} {b₀ : Bytes.Address} {T : KKey}
    {lps : List LevelParam} {nP nIdx nCtors : Nat} {Γ : Nat → KExpr} {h₀ : Heap F}
    (hlps : lps = List.range lps.length)
    (hlps_lt : lps.length < 4294967296)
    (hnPI_lt : nP + nIdx < 4294967296)
    (hpeer : OneTypePeerFacts c b₀ T lps.length nP nIdx nCtors)
    (hlf : LoadFacts c) :
    ∀ (m o : Nat) {R E : KExpr} {rbs bs : List (KExpr × Ix.Kernel.BinderMeta)}
      {rbody body : KExpr} {pty bas r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      R.stripPis m = some (rbs, rbody) →
      E.stripPis m = some (bs, body) →
      Heap.Extends h₀ h →
      (∀ n, RomBound.HeapDescent h₀ (.enum kexprEnum) pty n →
        nP + o + n < 9223372036854775808) →
      Good c cs →
      RawTmExact c.κ 0 Γ h₀ (nP + o) R E pty →
      noProjAt T E = true →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h [b₀] bas →
      ObsFn W "KernelCheck::check_positivity_fields"
        [pty, bas, .field ((nP + o : Nat) : F)] h r h' cs →
      ∀ i < m,
        (Ix.Kernel.recFieldKind T lps nP nIdx (o + i) (bs.getD i default).1 ≠ .negative ∧
         Ix.Kernel.recFieldKind T lps nP nIdx (o + i) (bs.getD i default).1 ≠ .unsupported) ∧
        ((bs.getD i default).1.mentionsConst T = false ∨
         RawRecSpine T (rbs.getD i default).1 (bs.getD i default).1)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hi =>
    absurd hi (Nat.not_lt_zero _)
  | m + 1, o, R, E, rbs, bs, rbody, body, pty, bas, r, h, h', cs,
      hstR, hst, ext₀, hd, hgood, hRaw₀, hnp, hbas, ev, i, hi => by
    match Obs.«KernelCheck::check_positivity_fields».obs ev with
    | .other (ld12 := ld) (hne113 := hne) .. =>
      cases R with
      | forallE rd rb rm =>
        exact ((hRaw₀.mono ext₀).not_forallE_of_load ld hne rd rb rm rfl).elim
      | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ | letE _ _ _ _
      | lit _ | proj _ _ _ =>
        simp [Expr.stripPis] at hstR
    | .Forall (x_dom := xdom) (x_body := xbody) (w20 := w20) (m37 := m37)
        (cs47 := cs_aug) (cs77 := cs_rec) (v82 := v82) (ld12 := ld)
        (ev49 := ev_aug) (op110 := op_add) (ev79 := ev_rec) (hc112 := hc) .. =>
      cases hRaw₀ with
      | @forallE _ _ tp₀ bp₀ _ rdom rbo dom bo ℓ cell₀ rdom₀ rbody₀ _ =>
        obtain ⟨-, hxs⟩ := load_cell (ext₀.getElem?_eq cell₀) ld
        injection hxs with h1 h2; injection h2 with h2 h3; injection h3 with h3
        rw [← h1] at ev_aug
        rw [← h2] at ev_rec
        simp only [Expr.stripPis, Option.map_eq_some_iff] at hstR hst
        obtain ⟨⟨rbs', rbody'⟩, hstR', heq_rbs⟩ := hstR
        simp only [Prod.mk.injEq] at heq_rbs
        obtain ⟨rfl, rfl⟩ := heq_rbs
        obtain ⟨⟨bs', body'⟩, hst', heq_bs⟩ := hst
        simp only [Prod.mk.injEq] at heq_bs
        obtain ⟨rfl, rfl⟩ := heq_bs
        simp only [noProjAt, Bool.and_eq_true] at hnp
        cases i with
        | zero =>
          rw [Nat.add_zero]
          simp only [List.getD_cons_zero]
          have hg_aug : Good c cs_aug := hgood.sub (fun x hx => by simp [hc, hx])
          have hd_dom : ∀ n, RomBound.HeapDescent h₀ (.enum kexprEnum) tp₀ n →
              nP + o + 0 + n < 9223372036854775808 := by
            intro n dstep
            have d0 : RomBound.HeapDescent h₀ (.enum kexprEnum) _ (n + 1) :=
              .down cell₀ (by simp [Value.type]) (by simp [RomBound.cellArgs]) dstep
            have := hd (n + 1) d0
            omega
          obtain ⟨hpos_dom, hsp_dom⟩ := check_positivity_aug_go hlps hlps_lt hnPI_lt hpeer hlf
            ext₀ hd_dom hg_aug (by simpa using rdom₀) hnp.1 hbas ev_aug
          refine ⟨?_, hsp_dom⟩
          unfold Ix.Kernel.recFieldKind
          split
          · exact hpos_dom
          · exact ⟨by decide, by decide⟩
        | succ i' =>
          have e1 := ev_aug.heap_extends
          have hg_rec : Good c cs_rec := hgood.sub (fun x hx => by simp [hc, hx])
          have hv82 : v82 = .field ((nP + (o + 1) : Nat) : F) :=
            evalBinOp_add_one (nP + o) op_add
          rw [hv82] at ev_rec
          have hd_bo : ∀ n, RomBound.HeapDescent h₀ (.enum kexprEnum) bp₀ n →
              nP + (o + 1) + n < 9223372036854775808 := by
            intro n dstep
            have d0 : RomBound.HeapDescent h₀ (.enum kexprEnum) _ (n + 1) :=
              .down cell₀ (by simp [Value.type]) (by simp [RomBound.cellArgs]) dstep
            have := hd (n + 1) d0
            omega
          rw [show nP + o + 1 = nP + (o + 1) by omega] at rbody₀
          have hbas' := repList_heapMono₂ addrListEnum
            (Bytes.repAddressRef_heapMono₂ addrTy) e1 hbas
          have hrec := check_positivity_fields_go hlps hlps_lt hnPI_lt hpeer hlf
            m (o + 1) hstR' hst' (ext₀.trans e1) hd_bo hg_rec rbody₀ hnp.2 hbas' ev_rec
            i' (by omega)
          simpa [List.getD_cons_succ, show o + 1 + i' = o + (i' + 1) by omega] using hrec
      | bvarLocal cell₀ _ _ | bvarFree cell₀ _ _ _ | sort cell₀ _ | const cell₀ _ _
      | app cell₀ _ _ | lam cell₀ _ _ _ | letE cell₀ _ _ _ | litNat cell₀ _ _
      | litStr cell₀ _ _ | proj cell₀ _ _ =>
        exact (load_cell_ne (ext₀.getElem?_eq cell₀) ld (by decide)).elim

private theorem peel_n_foralls_raw_h0 :
    ∀ (m : Nat) {κ : _root_.Address → KKey} {T : KKey} {Γ : Nat → KExpr} {h₀ h h' : Heap F}
      {k : Nat} {R E : KExpr} {pe r : SourceValue F} {cs : List (Call F)},
      m < 4294967296 →
      Heap.Extends h₀ h →
      (∀ n, RomBound.HeapDescent h₀ (.enum kexprEnum) pe n → k + n < 9223372036854775808) →
      RawTmExact κ 0 Γ h₀ k R E pe →
      noProjAt T E = true →
      ObsFn W "KernelCheck::peel_n_foralls" [pe, .field (m : F)] h r h' cs →
      h' = h ∧ ∃ rbs rbody bs body,
        R.stripPis m = some (rbs, rbody) ∧
        E.stripPis m = some (bs, body) ∧
        RawTmExact κ 0 Γ h₀ (k + m) rbody body r ∧
        noProjAt T body = true ∧
        ∀ n, RomBound.HeapDescent h₀ (.enum kexprEnum) r n → k + m + n < 9223372036854775808
  | 0, _, _, _, _, _, _, k, R, E, pe, _, _, _, _, hd, hRaw₀, hnp, ev => by
    rcases Obs.«KernelCheck::peel_n_foralls».obs ev with
      ⟨_, rfl, rfl, _⟩ | ⟨_, _, _, _, _, hne, _, _, _, _⟩
    · rw [Nat.add_zero]
      exact ⟨rfl, [], R, [], E, rfl, rfl, hRaw₀, hnp, hd⟩
    · exact absurd rfl hne
  | m + 1, κ, T, Γ, h₀, h, h', k, R, E, pe, r, cs, hlt, ext₀, hd, hRaw₀, hnp, ev => by
    rcases Obs.«KernelCheck::peel_n_foralls».obs ev with
      ⟨hv, _, _, _⟩ | ⟨_, x_body, _, _, _, _, ld, op, ev_rec, _⟩
    · exact absurd hv (succ_field_ne_zero (by omega))
    · cases hRaw₀ with
      | @forallE _ _ _ bp₀ _ rdom rbo dom bo ℓ cell₀ _ rbody₀ _ =>
        obtain ⟨-, hxs⟩ := load_cell (ext₀.getElem?_eq cell₀) ld
        injection hxs with _ h2; injection h2 with h2 _
        rw [← h2] at ev_rec
        simp only [noProjAt, Bool.and_eq_true] at hnp
        rw [evalBinOp_sub_succ m op] at ev_rec
        have hd_bo : ∀ n, RomBound.HeapDescent h₀ (.enum kexprEnum) bp₀ n →
            (k + 1) + n < 9223372036854775808 := by
          intro n dstep
          have d0 : RomBound.HeapDescent h₀ (.enum kexprEnum) _ (n + 1) :=
            .down cell₀ (by simp [Value.type]) (by simp [RomBound.cellArgs]) dstep
          have := hd (n + 1) d0
          omega
        obtain ⟨hh', rbs', rbody', bs', body', hstR', hst', hbody', hnp_body, hd'⟩ :=
          peel_n_foralls_raw_h0 m (by omega) ext₀ hd_bo rbody₀ hnp.2 ev_rec
        rw [show k + 1 + m = k + (m + 1) by omega] at hbody' hd'
        exact ⟨hh', (rdom, bmeta ℓ) :: rbs', rbody', (dom, bmeta ℓ) :: bs', body',
          by simp [Expr.stripPis, hstR'], by simp [Expr.stripPis, hst'],
          hbody', hnp_body, hd'⟩
      | bvarLocal cell₀ _ _ | bvarFree cell₀ _ _ _ | sort cell₀ _ | const cell₀ _ _
      | app cell₀ _ _ | lam cell₀ _ _ _ | letE cell₀ _ _ _ | litNat cell₀ _ _
      | litStr cell₀ _ _ | proj cell₀ _ _ =>
        exact (load_cell_ne (ext₀.getElem?_eq cell₀) ld (by decide)).elim

/-- `check_positivity` establishes `recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1`
is neither `.negative` nor `.unsupported` AND yields `RawRecSpine` (or `mentionsConst T = false`)
for all `i < nF`. -/
theorem check_positivity_spec {c : Ctx} {b₀ : Bytes.Address} {T : KKey}
    {lps : List LevelParam} {nP nIdx nF nCtors : Nat} {Γ : Nat → KExpr}
    {raw_cty rbody cty cbody : KExpr} {rcbs cbs : List (KExpr × Ix.Kernel.BinderMeta)}
    {pcty pblk r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hlps : lps = List.range lps.length)
    (hlps_lt : lps.length < 4294967296)
    (hnP_lt : nP < 4294967296)
    (hnPI_lt : nP + nIdx < 4294967296)
    (hpeer : OneTypePeerFacts c b₀ T lps.length nP nIdx nCtors)
    (hlf : LoadFacts c)
    (hgood : Good c cs)
    (hcty : RawTmExact c.κ 0 Γ h 0 raw_cty cty pcty)
    (hnp : noProjAt T cty = true)
    (hstR : raw_cty.stripPis (nP + nF) = some (rcbs, rbody))
    (hstrip : cty.stripPis (nP + nF) = some (cbs, cbody))
    (hblk : Bytes.RepAddressRef addrTy h b₀ pblk)
    (ev : ObsFn W "KernelCheck::check_positivity"
      [pcty, .field (nP : F), pblk] h r h' cs) :
    ∀ i < nF,
      (Ix.Kernel.recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1 ≠ .negative ∧
       Ix.Kernel.recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1 ≠ .unsupported) ∧
      ((cbs.getD (nP + i) default).1.mentionsConst T = false ∨
       RawRecSpine T (rcbs.getD (nP + i) default).1 (cbs.getD (nP + i) default).1) := by
  match Obs.«KernelCheck::check_positivity».obs ev with
  | .run (m2 := m2) (m26 := m26) (v38 := v38) (m39 := m39)
      (cs71 := cs_fields) (hm12 := hm2) (hm34 := hm26)
      (ev51 := ev_peel) (ev73 := ev_fields) (hc98 := hc) =>
    have e26 : Heap.Extends h m26 := by rw [hm26]; exact Heap.Extends.snoc h _
    have e2 : Heap.Extends m26 m2 := by rw [hm2]; exact Heap.Extends.snoc m26 _
    have ext_m2 : Heap.Extends h m2 := e26.trans e2
    have hcty_m2 : RawTmExact c.κ 0 Γ m2 0 raw_cty cty pcty := hcty.mono ext_m2
    have hd_m2 : ∀ n, RomBound.HeapDescent m2 (.enum kexprEnum) pcty n →
        0 + n < 9223372036854775808 := by
      intro n dstep
      have hlt_rom : n < 2 ^ 39 :=
        RomBound.bounded_descent_lt hgood.2
          (c := ⟨"KernelCheck::peel_n_foralls", [pcty, .field (nP : F)], m2⟩)
          (by simp [hc]) (by simp) dstep
      omega
    obtain ⟨hm39, rbsP, rcrest₀, bsP, crest₀, hstRP, hstP, hcrest₀, hnp_crest, hd_crest⟩ :=
      peel_n_foralls_raw_h0 (T := T) nP (by omega) (Heap.Extends.refl m2)
        hd_m2 hcty_m2 hnp ev_peel
    rw [hm39] at ev_fields
    rw [Nat.zero_add] at hcrest₀ hd_crest
    obtain ⟨rcbs₁, rcrest₁, rcbs₂, hstRP', hstRF, hrcbs_app, hrlen₁⟩ :=
      stripPis_split nP nF hstR
    rw [hstRP] at hstRP'
    simp only [Option.some.injEq, Prod.mk.injEq] at hstRP'
    obtain ⟨rfl, rfl⟩ := hstRP'
    obtain ⟨cbs₁, crest₁, cbs₂, hstP', hstF, hcbs_app, hlen₁⟩ := stripPis_split nP nF hstrip
    rw [hstP] at hstP'
    simp only [Option.some.injEq, Prod.mk.injEq] at hstP'
    obtain ⟨rfl, rfl⟩ := hstP'
    have hnil : RepList addrListEnum (Bytes.RepAddressRef addrTy) m2 []
        (.ptr (.enum addrListEnum) h.length) :=
      RepLinkedList.nil (e2.getElem?_eq (by rw [hm26]; simp))
    have hbas_m2 : RepList addrListEnum (Bytes.RepAddressRef addrTy) m2 [b₀]
        (.ptr (.enum addrListEnum) m26.length) :=
      RepLinkedList.cons (by rw [hm2]; simp)
        (Bytes.repAddressRef_heapMono₂ addrTy ext_m2 hblk) hnil
    have hg_fields : Good c cs_fields := hgood.sub (fun x hx => by simp [hc, hx])
    have hfields := check_positivity_fields_go hlps hlps_lt hnPI_lt hpeer hlf
      nF 0 hstRF hstF (Heap.Extends.refl m2) (by simpa using hd_crest) hg_fields
      (by simpa using hcrest₀) hnp_crest hbas_m2 ev_fields
    intro i hi
    have hget : (cbs.getD (nP + i) default).1 = (cbs₂.getD i default).1 := by
      have hi₂ : i < cbs₂.length := by
        have := Expr.stripPis_length nF hstF; omega
      have hi_all : nP + i < cbs.length := by
        rw [← hcbs_app, List.length_append, hlen₁]; omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_all,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi₂]
      simp only [Option.getD_some]
      have hget? : cbs[nP + i]? = cbs₂[i]? := by
        rw [← hcbs_app, List.getElem?_append_right (by omega), hlen₁, Nat.add_sub_cancel_left]
      rw [List.getElem?_eq_getElem hi_all, List.getElem?_eq_getElem hi₂, Option.some.injEq] at hget?
      exact congrArg Prod.fst hget?
    have hrget : (rcbs.getD (nP + i) default).1 = (rcbs₂.getD i default).1 := by
      have hi₂ : i < rcbs₂.length := by
        have := Expr.stripPis_length nF hstRF; omega
      have hi_all : nP + i < rcbs.length := by
        rw [← hrcbs_app, List.length_append, hrlen₁]; omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi_all,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi₂]
      simp only [Option.getD_some]
      have hget? : rcbs[nP + i]? = rcbs₂[i]? := by
        rw [← hrcbs_app, List.getElem?_append_right (by omega), hrlen₁, Nat.add_sub_cancel_left]
      rw [List.getElem?_eq_getElem hi_all, List.getElem?_eq_getElem hi₂, Option.some.injEq] at hget?
      exact congrArg Prod.fst hget?
    rw [hget, hrget]
    simpa using hfields i hi

/-! ## `former_decl_ok`, `OneTypeBlockWitness`, `nativeFront_pass`, and `DeclNativeNoRecRunJ` -/

theorem nat_keyOf_injective {t : Ix.Kernel.RoleTable} (hwf : t.wf = true)
    {a₁ a₂ : _root_.Address} (heq : keyOf t a₁ = keyOf t a₂) : a₁ = a₂ := by
  cases hq₁ : t.bound.find? (·.2 == a₁) with
  | some q₁ =>
    have hk₁ : keyOf t a₁ = .role q₁.1 := by unfold keyOf; rw [hq₁]
    have h1 := addressOf_of_keyOf hwf hk₁
    have h2 := addressOf_of_keyOf hwf (heq.symm.trans hk₁)
    rw [h1] at h2
    exact Option.some.inj h2
  | none =>
    have hk₁ : keyOf t a₁ = .id a₁ := by unfold keyOf; rw [hq₁]
    have hk₂ : keyOf t a₂ = .id a₁ := heq.symm.trans hk₁
    unfold keyOf at hk₂
    cases hq₂ : t.bound.find? (·.2 == a₂) with
    | some _ => rw [hq₂] at hk₂; cases hk₂
    | none => rw [hq₂] at hk₂; cases hk₂; rfl

/-- Direct constructor-projection record loader witness for `b₀` at constructor index `j`. -/
def CtorLoadAt (t : Ix.Kernel.RoleTable) (b₀ : Bytes.Address) (nP : Nat)
    (cs_root : List (Call F)) (ctors ctorsA : List (KConstantVal × Nat))
    (ctorRawTypes : List KExpr) : Prop :=
  ctorsA.length = ctors.length ∧
  ∀ j < ctors.length, ∃ c cvCa₀,
    ctors[j]? = some c ∧
    ctorsA[j]? = some (cvCa₀, c.2) ∧
    IxVM.Consistency.ValStored cvCa₀ c.1 ∧
    ∀ (bp ptr : SourceValue F) (h h' : Heap F) (cs : List (Call F)),
      (∀ x ∈ cs, x ∈ cs_root) →
      Bytes.RepAddressRef addrTy h b₀ bp →
      ObsFn W "Ingress::get_ci_cprj" [bp, .field 0, .field (j : F)] h ptr h' cs →
      ∃ (nl cty cblk cnp cnf : SourceValue F) (b_c : Bytes.Address),
        loadValue h' ptr = .ok (.construct kciEnum "Ctor"
          [nl, cty, cblk, .field 0, .field (j : F), cnp, cnf, .field 0]) ∧
        Bytes.RepAddressRef addrTy h' b_c cblk ∧
        ixAddr b_c = ixAddr b₀ ∧
        (∀ d Γ, RawTmExact (keyOf t) d Γ h' 0
          (ctorRawTypes.getD j default) (posOf cvCa₀.levelParams cvCa₀.type) cty) ∧
        CIRepExact (keyOf t) h'
          (.construct kciEnum "Ctor"
            [nl, cty, cblk, .field 0, .field (j : F), cnp, cnf, .field 0])
          (.ctorInfo cvCa₀ nP c.2)

private theorem ctor_zero_all_go {t : Ix.Kernel.RoleTable}
    {b₀ a_t : Bytes.Address} {T : KKey} {nP : Nat} {ind_lvl : KLevel}
    {cs_root : List (Call F)} {ctors ctorsA : List (KConstantVal × Nat)}
    {ctorRawTypes : List KExpr}
    (hwf : t.wf = true)
    (hlps_ctors : ∀ c ∈ ctors, c.1.levelParams = List.range c.1.levelParams.length)
    (hT_eq : T = keyOf t (ixAddr a_t))
    (hcload : CtorLoadAt t b₀ nP cs_root ctors ctorsA ctorRawTypes)
    (hctor_sp : ∀ k < ctors.length, ∀ c cvCa₀,
      ctors[k]? = some c →
      ctorsA[k]? = some (cvCa₀, c.2) →
      ∃ rcbs rargs cbs eargs us₀,
        (ctorRawTypes.getD k default).stripPis (nP + c.2) =
          some (rcbs, Expr.mkAppN (.const T us₀) rargs) ∧
        cvCa₀.type.stripPis (nP + c.2) =
          some (cbs, Expr.mkAppN (.const T us₀) eargs) ∧
        ∀ idx < nP + c.2,
          (cbs.getD idx default).1.mentionsConst T = false ∨
          RawRecSpine T (rcbs.getD idx default).1 (cbs.getD idx default).1)
    (hnCtors_lt : ctors.length < 4294967296) :
    ∀ (m j : Nat) {bp pt pind r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      m + j = ctors.length →
      (∀ x ∈ cs, x ∈ cs_root) →
      Bytes.RepAddressRef addrTy h b₀ bp →
      Bytes.RepAddressRef addrTy h a_t pt →
      RepKLevel h ind_lvl pind →
      ObsFn W "KernelCheck::ctor_zero_all"
        [bp, .field 0, .field (ctors.length : F), .field (j : F), pt, pind] h r h' cs →
      ∀ k, j ≤ k → k < ctors.length → ∀ cA, ctorsA[k]? = some cA →
        ctorZeroOk T ind_lvl.zeronessOf cA.1.type = true
  | 0, _, _, _, _, _, _, _, _, hmj, _, _, _, _, _, _, hjk, hkt, _, _ => by omega
  | m + 1, j, bp, pt, pind, r, h, h', cs, hmj, hsub, hbp, hpt, hpind, ev, k, hjk, hkt, cA, hcA => by
    match Obs.«KernelCheck::ctor_zero_all».obs ev with
    | .n0 (op17 := op) .. =>
      have hsub_op : (.field ((0 : Nat) : F) : SourceValue F) =
          .field (((ctors.length - j : Nat) : F)) := by
        simpa using evalBinOp_sub_nat (by omega : j ≤ ctors.length) op
      have hj_eq := nat_eq_of_field_eq (by decide) (by omega) hsub_op
      omega
    | .other (m34 := m34) (p41 := p41) (cs47 := cs_cprj) (x_cty := xcty)
        (m125 := m125) (cs165 := cs_rec) (v171 := v171)
        (ev49 := ev_cprj) (ld43 := ld_ctor) (ev137 := ev_cz)
        (op208 := op_add) (ev167 := ev_rec) (hc224 := hc) .. =>
      obtain ⟨c_j, cvCa₀, hc_j, hcA_j, hvs_j, hload_j⟩ := hcload.2 j (by omega)
      have hsub_cprj : ∀ x ∈ cs_cprj, x ∈ cs_root := fun x hx => hsub x (by simp [hc, hx])
      have hsub_rec : ∀ x ∈ cs_rec, x ∈ cs_root := fun x hx => hsub x (by simp [hc, hx])
      obtain ⟨nl', cty', cblk', cnp', cnf', _, ld_c', _, _, hraw_rep, _⟩ :=
        hload_j bp p41 h m34 cs_cprj hsub_cprj hbp ev_cprj
      rw [ld_c'] at ld_ctor
      injection ld_ctor with hval; injection hval with _ _ h1
      injection h1 with _ h1; injection h1 with hcty_eq _
      cases hcty_eq.symm
      have e1 := ev_cprj.heap_extends
      have e2 := ev_cz.heap_extends
      by_cases hkj : k = j
      · subst hkj
        rw [hcA_j] at hcA
        injection hcA with hcA_eq; subst hcA_eq
        have hlps_cj : cvCa₀.levelParams = List.range cvCa₀.levelParams.length := by
          rw [hvs_j.2.1]
          exact hlps_ctors c_j (List.mem_of_getElem? hc_j)
        have hcty_raw :
            RawTmExact (keyOf t) 0 (fun _ => default) m34 0
              (ctorRawTypes.getD k default) cvCa₀.type xcty := by
          have h0 := hraw_rep 0 (fun _ => default)
          rwa [hlps_cj, posOf_range] at h0
        obtain ⟨rcbs, rargs, cbs, eargs, us₀, hstR, hstE, hdoms⟩ :=
          hctor_sp k (by omega) c_j cvCa₀ hc_j hcA_j
        have hκ_inj : ∀ a : Bytes.Address, keyOf t (ixAddr a) = T → ixAddr a = ixAddr a_t := by
          intro a ha
          rw [hT_eq] at ha
          exact nat_keyOf_injective hwf ha
        exact ctor_zero_ok_raw_go hκ_inj (nP + c_j.2) hstR hstE hdoms hcty_raw
          (Bytes.repAddressRef_heapMono₂ addrTy e1 hpt)
          (repKLevel_heapMono₂ e1 hpind) ev_cz
      · have hv171 : v171 = .field ((j + 1 : Nat) : F) := evalBinOp_add_nat j 1 op_add
        rw [hv171] at ev_rec
        exact ctor_zero_all_go hwf hlps_ctors hT_eq hcload hctor_sp hnCtors_lt
          m (j + 1) (by omega) hsub_rec
          (Bytes.repAddressRef_heapMono₂ addrTy (e1.trans e2) hbp)
          (Bytes.repAddressRef_heapMono₂ addrTy (e1.trans e2) hpt)
          (repKLevel_heapMono₂ (e1.trans e2) hpind) ev_rec
          k (by omega) hkt cA hcA

theorem former_decl_ok_spec {c : Ctx}
    {b₀ : Bytes.Address} {T : KKey} {nP nIdx : Nat} {ty : KExpr} {ind_lvl : KLevel}
    {cs_root : List (Call F)} {ctors ctorsA : List (KConstantVal × Nat)}
    {ctorRawTypes : List KExpr}
    {pty bp pind r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hwf : c.t.wf = true)
    (hnPI_lt : nP + nIdx < 4294967296)
    (hnCtors_lt : ctors.length < 4294967296)
    (hT_iprj : T = c.κ (iprjAddr (ixAddr b₀) 0))
    (hlps_ctors : ∀ cb ∈ ctors, cb.1.levelParams = List.range cb.1.levelParams.length)
    (hcload : CtorLoadAt c.t b₀ nP cs_root ctors ctorsA ctorRawTypes)
    (hctor_sp : ∀ k < ctors.length, ∀ c cvCa₀,
      ctors[k]? = some c →
      ctorsA[k]? = some (cvCa₀, c.2) →
      ∃ rcbs rargs cbs eargs us₀,
        (ctorRawTypes.getD k default).stripPis (nP + c.2) =
          some (rcbs, Expr.mkAppN (.const T us₀) rargs) ∧
        cvCa₀.type.stripPis (nP + c.2) =
          some (cbs, Expr.mkAppN (.const T us₀) eargs) ∧
        ∀ idx < nP + c.2,
          (cbs.getD idx default).1.mentionsConst T = false ∨
          RawRecSpine T (rcbs.getD idx default).1 (cbs.getD idx default).1)
    (hsub : ∀ x ∈ cs, x ∈ cs_root)
    (hgood : Good c cs)
    (hty : TmExact c.κ 0 (fun _ => default) h 0 ty pty)
    (hbp : Bytes.RepAddressRef addrTy h b₀ bp)
    (hpind : RepKLevel h ind_lvl pind)
    (ev : ObsFn W "KernelCheck::former_decl_ok"
      [pty, .field (nP : F), .field (nIdx : F), .field (ctors.length : F),
        bp, .field 0, pind] h r h' cs) :
    (∃ bs s, ty.stripPis (nP + nIdx) = some (bs, .sort s) ∧ bs.length = nP + nIdx) ∨
    (nIdx ≠ 0 ∧ ∀ k < ctorsA.length, ∀ cA, ctorsA[k]? = some cA →
      ctorZeroOk T ind_lvl.zeronessOf cA.1.type = true) := by
  match Obs.«KernelCheck::former_decl_ok».obs ev with
  | .n1 (v17 := v17) (op38 := op_add) (ev15 := ev_tele) .. =>
    have hv17 : v17 = .field ((nP + nIdx : Nat) : F) := evalBinOp_add_nat nP nIdx op_add
    rw [hv17] at ev_tele
    obtain ⟨_, bs, s, hst, hlen⟩ := former_is_tele_one_spec (nP + nIdx) (by omega) hty ev_tele
    exact Or.inl ⟨bs, s, hst, hlen⟩
  | .other (m2 := m2) (v65 := v65) (m68 := m68)
      (cs97 := cs_cz) (v104 := v104) (m134 := m134) (cs142 := cs_ip)
      (ev15 := ev_tele) (ev78 := ev_iz) (heq93 := hv65)
      (ev144 := ev_iprj) (ev99 := ev_cz) (hc168 := hc) .. =>
    subst hv65
    obtain ⟨hiz, _⟩ := Lib.is_zero_spec ev_iz
    have hnIdx_ne : nIdx ≠ 0 := by
      intro h0
      subst h0
      simp at hiz
    have e1 := ev_tele.heap_extends
    have e2 := ev_iz.heap_extends
    have hg_ip : Good c cs_ip := hgood.sub (fun x hx => by simp [hc, hx])
    obtain ⟨a_t, ha_t, hix_t⟩ :=
      compute_iprj_addr_spec (idx := 0) (by omega)
        (Bytes.repAddressRef_heapMono₂ addrTy (e1.trans e2) hbp) hg_ip ev_iprj
    have e3 := ev_iprj.heap_extends
    have hT_at : T = keyOf c.t (ixAddr a_t) := by
      rw [hT_iprj, hix_t]
    have hsub_cz : ∀ x ∈ cs_cz, x ∈ cs_root := fun x hx => hsub x (by simp [hc, hx])
    have hcz := ctor_zero_all_go hwf hlps_ctors hT_at hcload hctor_sp hnCtors_lt
      ctors.length 0 (by omega) hsub_cz
      (Bytes.repAddressRef_heapMono₂ addrTy (e1.trans (e2.trans e3)) hbp)
      ha_t
      (repKLevel_heapMono₂ (e1.trans (e2.trans e3)) hpind) ev_cz
    exact Or.inr ⟨hnIdx_ne, fun k hk cA hcA =>
      hcz k (Nat.zero_le k) (by rw [← hcload.1]; exact hk) cA hcA⟩

/-- Per-constructor output of `check_inductive_shape_ctors`. -/
structure NativeCtorOut (envI₀ : Ix.Kernel.Env .anon) (T : KKey) (lps : List LevelParam)
    (nP nIdx : Nat) (resSort : KLevel) (ta raw_cty : KExpr)
    (c cA : KConstantVal × Nat) (sorts : List KLevel) : Prop where
  nF_eq : cA.2 = c.2
  stored : IxVM.Consistency.ValStored cA.1 c.1
  cvCheck : ConstantValCheckJ rulesJ envI₀ c.1 cA.1
  noProj : noProjAt T cA.1.type = true
  inferSort : ∃ stype u, Infer envI₀ .full 0 cA.1.type stype ∧ Red envI₀ 0 stype (.sort u)
  residual : ∃ (rcbs : List (KExpr × Ix.Kernel.BinderMeta)) (rargs : List KExpr)
    (cbs : List (KExpr × Ix.Kernel.BinderMeta)) (es : List KExpr),
    raw_cty.stripPis (nP + c.2) =
      some (rcbs, Expr.mkAppN (.const T (lps.map .param)) rargs) ∧
    rcbs.length = nP + c.2 ∧
    cA.1.type.stripPis (nP + c.2) =
      some (cbs, Expr.mkAppN (.const T (lps.map .param)) (Ix.Kernel.structPsAt c.2 nP ++ es)) ∧
    cbs.length = nP + c.2 ∧
    es.length = nIdx ∧
    (∀ a ∈ es, a.mentionsConst T = false) ∧
    (∀ i < c.2,
      Ix.Kernel.recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1 ≠ .negative ∧
      Ix.Kernel.recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1 ≠ .unsupported) ∧
    (∀ i < c.2,
      (cbs.getD (nP + i) default).1.mentionsConst T = false ∨
      RawRecSpine T (rcbs.getD (nP + i) default).1 (cbs.getD (nP + i) default).1)
  domsShared : StructDomsShared envI₀ ta cA.1.type nP
  opened : ∃ fvsP crest xFvs idxArgs,
    Ix.Kernel.openPisAtFvars nP cA.1.type 0 = some (fvsP, crest) ∧
    Ix.Kernel.openPisAtFvars c.2 crest nP =
      some (xFvs, Expr.mkAppN (.const T (lps.map .param)) (fvsP ++ idxArgs)) ∧
    idxArgs.length = nIdx ∧
    (∀ x ∈ xFvs, x.fvarTypeD.constsResolve envI₀ = true) ∧
    (∀ e ∈ idxArgs, e.constsResolve envI₀ = true) ∧
    FieldSortsJ rulesJ envI₀ (Level.isEquiv resSort .zero == some true) false resSort
      nP xFvs idxArgs c.2 sorts

theorem fieldSortsJ_congr_sort {env : Ix.Kernel.Env .anon} {large : Bool}
    {s₁ s₂ : KLevel} {nP : Nat} {xFvs idxArgs : List KExpr} {nF : Nat} {sorts : List KLevel}
    (hlveq : LvEq s₁ s₂)
    (h : FieldSortsJ rulesJ env (Level.isEquiv s₁ .zero == some true) large s₁
      nP xFvs idxArgs nF sorts) :
    FieldSortsJ rulesJ env (Level.isEquiv s₂ .zero == some true) large s₂
      nP xFvs idxArgs nF sorts := by
  rw [← isEquiv_zero_congr hlveq]
  refine ⟨h.1, fun i hi => ?_⟩
  obtain ⟨fv, ty, u, hfv, hu, hinf, hred, h1, h2⟩ := h.2 i hi
  exact ⟨fv, ty, u, hfv, hu, hinf, hred,
    (fun hp φ => by rw [← hlveq φ]; exact h1 hp φ), h2⟩

theorem ne_projFnName_of_isProjFnShape_false {k : KKey} (h : k.isProjFnShape = false) :
    ∀ T j, k ≠ Ix.Kernel.projFnName T j := by
  intro T j heq
  rw [heq] at h
  exact Bool.noConfusion h

theorem perm_append_singleton {α : Type _} :
    ∀ (xs : List α) (y : α), (xs ++ [y]).Perm (y :: xs)
  | [], _ => List.Perm.refl _
  | x :: xs, y => (List.Perm.cons x (perm_append_singleton xs y)).trans (List.Perm.swap y x xs)

theorem perm_reverse {α : Type _} :
    ∀ (xs : List α), xs.reverse.Perm xs
  | [] => List.Perm.nil
  | x :: xs => by
    rw [List.reverse_cons]
    exact (perm_append_singleton xs.reverse x).trans (List.Perm.cons x (perm_reverse xs))

theorem consts_consSumCtors_eq (nP : Nat) :
    ∀ (ctorsA : List (KConstantVal × Nat)) (env : Ix.Kernel.Env .anon),
      (Ix.Kernel.consSumCtors nP ctorsA env).consts =
        (ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 nP c.2)).reverse ++ env.consts
  | [], _ => rfl
  | _ :: cs, env => by
    simp [Ix.Kernel.consSumCtors, consts_consSumCtors_eq nP cs, List.append_assoc]

theorem find?_cons_ne {ci : KConstantInfo} {consts : List KConstantInfo} {k : KKey}
    (hne : ci.name ≠ k) :
    (Ix.Kernel.Env.mk (ci :: consts)).find? k = (Ix.Kernel.Env.mk consts).find? k := by
  rw [Ix.Kernel.Env.find?_cons, ite_eq_right hne]

theorem find?_cons_indInfo_ne (cv : KConstantVal) (caps : Ix.Kernel.IndCaps .anon)
    (consts : List KConstantInfo) {k : KKey} (hne : cv.name ≠ k) :
    (Ix.Kernel.Env.mk (.indInfo cv caps :: consts)).find? k =
      (Ix.Kernel.Env.mk consts).find? k :=
  find?_cons_ne (ci := .indInfo cv caps) hne

theorem find?_consSumCtors_ne (nP : Nat) {k : KKey} :
    ∀ (ctorsA : List (KConstantVal × Nat)) (env : Ix.Kernel.Env .anon),
      (∀ c ∈ ctorsA, c.1.name ≠ k) →
      (Ix.Kernel.consSumCtors nP ctorsA env).find? k = env.find? k
  | [], _, _ => rfl
  | c :: cs, env, hne => by
    simp only [Ix.Kernel.consSumCtors]
    rw [find?_consSumCtors_ne nP cs _ (fun x hx => hne x (List.mem_cons_of_mem _ hx))]
    exact find?_cons_ne (hne c List.mem_cons_self)

theorem CIRepExact.ctor_inv {κ : _root_.Address → KKey} {h : Heap F}
    {nl ty blk ind cidx np nf u : SourceValue F}
    {cv : ConstantVal .anon} {nP nF : Nat}
    (hci : CIRepExact κ h (.construct kciEnum "Ctor" [nl, ty, blk, ind, cidx, np, nf, u])
      (.ctorInfo cv nP nF)) :
    ValRepExact κ h nl ty cv ∧ np = .field (nP : F) ∧ nf = .field (nF : F) := by
  generalize hv : Value.construct kciEnum "Ctor" [nl, ty, blk, ind, cidx, np, nf, u] = v₀ at hci
  generalize hinfo : ConstantInfo.ctorInfo cv nP nF = ci₀ at hci
  cases hci
  case ctor hv_rep hnp hnf _ _ =>
    injection hv with _ _ hxs
    injection hxs with h1 hxs; injection hxs with h2 hxs; injection hxs with _ hxs
    injection hxs with _ hxs; injection hxs with _ hxs; injection hxs with h6 hxs
    injection hxs with h7 _
    injection hinfo with hcv hnP hnF
    rw [h1, h2, h6, h7, hcv, hnP, hnF]
    exact ⟨hv_rep, hnp, hnf⟩
  all_goals
    injection hv with _ hc _
    exact absurd hc (by decide)

private theorem check_inductive_shape_ctors_go (hLevels : IxVM.Consistency.Levels)
    (hCore : IxVM.Consistency.Core S₀) {c₁ : Ctx}
    {b₀ : Bytes.Address} {T : KKey} {lps : List LevelParam}
    {nP nIdx : Nat} {ta : KExpr} {resSort ind_lvl : KLevel}
    {cs_root : List (Call F)} {ctors ctorsA : List (KConstantVal × Nat)}
    {ctorRawTypes : List KExpr}
    (hlps : lps = List.range lps.length)
    (hlps_lt : lps.length < 4294967296)
    (hnP_lt : nP < 2147483648)
    (hnIdx_lt : nIdx < 2147483648)
    (hnCtors_lt : ctors.length < 4294967296)
    (hnF_lt : ∀ c ∈ ctors, c.2 < 2147483648)
    (hlveq : LvEq resSort ind_lvl)
    (hcload : CtorLoadAt c₁.t b₀ nP cs_root ctors ctorsA ctorRawTypes)
    (hlps_ctors : ∀ c ∈ ctors, c.1.levelParams = lps)
    (hlbd_ctors : ∀ c ∈ ctors, c.1.type.looseBVarsBounded 0 = true)
    (hfv_ctors : ∀ c ∈ ctors, c.1.type.hasFvar = false)
    (hfresh_ctors : ∀ c ∈ ctors, c₁.env.find? c.1.name = none)
    (hbasis_ctors : ∀ c ∈ ctors, Ix.Kernel.reservedBasisNames.contains c.1.name = false)
    (hshape_ctors : ∀ c ∈ ctors, c.1.name.isProjFnShape = false)
    (hno_proj_T : ∀ i, c₁.env.findProj? T i = none)
    (hstore₁ : Ix.Kernel.Open.StoreInv c₁.env)
    (hef₁ : EnvFacts c₁)
    (hlf₁ : LoadFacts c₁)
    (hpeer₁ : OneTypePeerFacts c₁ b₀ T lps.length nP nIdx ctors.length) :
    ∀ (m j : Nat) {rc pta bp pind r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      m + j = ctors.length →
      (∀ x ∈ cs, x ∈ cs_root) →
      Good c₁ cs →
      RCRep c₁.t c₁.lim h rc →
      Tm c₁.κ 0 (fun _ => default) h 0 ta pta →
      Bytes.RepAddressRef addrTy h b₀ bp →
      RepKLevel h ind_lvl pind →
      ObsFn W "KernelCheck::check_inductive_shape_ctors"
        [rc, pta, .field (nP : F), .field (nIdx : F), .field (ctors.length : F),
          .field (lps.length : F), bp, .field 0, pind, .field 0, .field (j : F)] h r h' cs →
      ∃ sortss_suf : List (List KLevel),
        sortss_suf.length = m ∧
        ∀ t_idx < m, ∃ c cA sorts,
          ctors[j + t_idx]? = some c ∧
          ctorsA[j + t_idx]? = some cA ∧
          sortss_suf[t_idx]? = some sorts ∧
          NativeCtorOut c₁.env T lps nP nIdx resSort ta
            (ctorRawTypes.getD (j + t_idx) default) c cA sorts
  | 0, j, _, _, _, _, _, _, _, _, hmj, _, _, _, _, _, _, ev => by
    match Obs.«KernelCheck::check_inductive_shape_ctors».obs ev with
    | .n0 .. =>
      exact ⟨[], rfl, fun _ ht => absurd ht (Nat.not_lt_zero _)⟩
    | .other (op17 := op) (hne29 := hne) .. =>
      have hj_eq : j = ctors.length := by omega
      cases hj_eq.symm
      rw [evalBinOp_sub_nat (Nat.le_refl ctors.length) op, Nat.sub_self] at hne
      exact absurd rfl hne
  | m + 1, j, rc, pta, bp, pind, r, h, h', cs, hmj, hsub, hgood, hrc, hta, hbp, hpind, ev => by
    match Obs.«KernelCheck::check_inductive_shape_ctors».obs ev with
    | .n0 (op17 := op) .. =>
      have hsub_op : (.field ((0 : Nat) : F) : SourceValue F) =
          .field (((ctors.length - j : Nat) : F)) := by
        simpa using evalBinOp_sub_nat (by omega : j ≤ ctors.length) op
      have hj_eq := nat_eq_of_field_eq (by decide) (by omega) hsub_op
      omega
    | .other (m34 := m34) (p41 := p41) (cs47 := cs_cprj)
        (x_c_nlvls := xcnl) (x_cty := xcty) (x_c_block := xcblk)
        (x_c_np := xcnp) (x_c_nf := xcnf)
        (m144 := m144) (m319 := m319) (cs329 := cs_ws)
        (m356 := m356) (cs366 := cs_es) (m387 := m387)
        (m400 := m400) (m430 := m430) (cs440 := cs_pa)
        (m476 := m476) (cs486 := cs_rt) (m546 := m546) (cs556 := cs_fu)
        (m684 := m646) (cs686 := cs_sg) (cs695 := cs_rec) (v708 := v670)
        (ev49 := ev_cprj) (ld43 := ld_ctor) (ev154 := ev_aeq)
        (heq261 := heq_nl) (heq289 := heq_np)
        (ev331 := ev_ws) (hm395 := hm387) (ev368 := ev_es) (ev412 := ev_saf)
        (ev442 := ev_pa) (ev488 := ev_rt) (ev558 := ev_fu) (sg691 := sg_pos)
        (op792 := op_add) (ev697 := ev_rec) (hc794 := hc) .. =>
      obtain ⟨c_j, cvCa₀, hc_j, hcA_j, hvs_j, hload_j⟩ := hcload.2 j (by omega)
      have hc_mem : c_j ∈ ctors := List.mem_of_getElem? hc_j
      have hc_nf_lt : c_j.2 < 2147483648 := hnF_lt c_j hc_mem
      have hsub_cprj : ∀ x ∈ cs_cprj, x ∈ cs_root := fun x hx => hsub x (by simp [hc, hx])
      have hsub_rec : ∀ x ∈ cs_rec, x ∈ cs_root := fun x hx => hsub x (by simp [hc, hx])
      obtain ⟨nl', cty', cblk', cnp', cnf', _, ld_c', _, _, hraw_rep, hci_rep⟩ :=
        hload_j bp p41 h m34 cs_cprj hsub_cprj hbp ev_cprj
      rw [ld_c'] at ld_ctor
      injection ld_ctor with hval; injection hval with _ _ h1
      injection h1 with hnl_eq h1; injection h1 with hcty_eq h1; injection h1 with hcblk_eq h1
      injection h1 with _ h1; injection h1 with _ h1; injection h1 with hcnp_eq h1
      injection h1 with hcnf_eq _
      cases hnl_eq.symm; cases hcty_eq.symm; cases hcblk_eq.symm
      cases hcnp_eq.symm; cases hcnf_eq.symm
      obtain ⟨hv_rep, hnp_f, hnf_f⟩ := CIRepExact.ctor_inv hci_rep
      · subst heq_nl heq_np
        have e_cprj := ev_cprj.heap_extends
        have e_aeq := ev_aeq.heap_extends
        have e_ws := ev_ws.heap_extends
        have e_nil : Heap.Extends m319 m387 := by rw [hm387]; exact Heap.Extends.snoc m319 _
        have e_to_es := e_cprj.trans (e_aeq.trans (e_ws.trans e_nil))
        have hg_es : Good c₁ cs_es := hgood.sub (fun x hx => by simp [hc, hx])
        have hg_pa : Good c₁ cs_pa := hgood.sub (fun x hx => by simp [hc, hx])
        have hg_rt : Good c₁ cs_rt := hgood.sub (fun x hx => by simp [hc, hx])
        have hg_fu : Good c₁ cs_fu := hgood.sub (fun x hx => by simp [hc, hx])
        have hg_rec : Good c₁ cs_rec := hgood.sub (fun x hx => by simp [hc, hx])
        have hlps_cj : cvCa₀.levelParams = List.range lps.length := by
          rw [hvs_j.2.1, hlps_ctors c_j hc_mem]
          exact hlps
        have hpos_lift : PosSortLift c₁.env cvCa₀ := PosSortLift.of_range hlps_cj
        have hv_m144 : ValRepExact c₁.κ m144 (.field (lps.length : F)) xcty cvCa₀ :=
          ⟨hv_rep.1, hv_rep.2.1, hv_rep.2.2.1, hv_rep.2.2.2.mono e_aeq⟩
        have hty_nil : TypesRep c₁.κ (fun _ => default) m387 0
            (.ptr (.enum kexprListEnum) m319.length) := by
          rw [hm387]; exact typesRep_alloc_nil c₁.κ (fun _ => default) m319
        obtain ⟨hcvC_chk, sty₀, u₀, _, hinf₀, hred₀, _, _⟩ :=
          constantValCheckJ_of_checked hCore (Γ := fun _ => default) hvs_j hv_m144
            (hlbd_ctors c_j hc_mem) (hfv_ctors c_j hc_mem)
            (hfresh_ctors c_j hc_mem) (hbasis_ctors c_j hc_mem) (hshape_ctors c_j hc_mem)
            hstore₁ hpos_lift ev_ws (e_ws.trans e_nil)
            (hrc.mono e_to_es) hty_nil hef₁ hlf₁ hg_es ev_es
        rw [hlps_cj, posOf_range] at hinf₀
        have hfv_ca : cvCa₀.type.hasFvar = false :=
          annotates_hasFvar_false hvs_j.2.2 (hfv_ctors c_j hc_mem)
        have hnp_ca : noProjAt T cvCa₀.type = true :=
          noProjAt_of_infer_full hno_proj_T hinf₀ hfv_ca
        have e_es := ev_es.heap_extends
        have e_saf := ev_saf.heap_extends
        have e_to_pa := e_to_es.trans (e_es.trans e_saf)
        have hcty_raw_m34 :
            RawTmExact c₁.κ 0 (fun _ => default) m34 0
              (ctorRawTypes.getD j default) cvCa₀.type xcty := by
          have h0 := hraw_rep 0 (fun _ => default)
          rwa [hlps_cj, posOf_range] at h0
        have hcty_exact_m34 : TmExact c₁.κ 0 (fun _ => default) m34 0 cvCa₀.type xcty :=
          hcty_raw_m34.toTmExact
        have hcty_pa : Tm c₁.κ 0 (fun _ => default) m400 0 cvCa₀.type xcty :=
          (hcty_exact_m34.mono (e_aeq.trans (e_ws.trans (e_nil.trans (e_es.trans e_saf))))).toTm
        have hdoms_sh : StructDomsShared c₁.env ta cvCa₀.type nP :=
          check_param_agreement_spec hCore (by omega) (hrc.mono e_to_pa) hef₁ hlf₁ hg_pa
            (hta.mono e_to_pa) hcty_pa ev_pa
        have e_pa := ev_pa.heap_extends
        have e_from_m34_to_m430 :=
          e_aeq.trans (e_ws.trans (e_nil.trans (e_es.trans (e_saf.trans e_pa))))
        have e_to_rt := e_cprj.trans e_from_m34_to_m430
        rw [hnf_f] at ev_rt
        obtain ⟨hnt_476, rcbs, rargs, cbs, es, hstR_c, hrcbs_len, hstrip_c, hcbs_len,
            hes_len, hes_noT⟩ :=
          check_ctor_return_type_spec hlps hlps_lt (by omega) (by omega) hpeer₁ hlf₁ hg_rt
            (hcty_raw_m34.mono e_from_m34_to_m430) hnp_ca
            (Bytes.repAddressRef_heapMono₂ addrTy e_to_rt hbp) ev_rt
        obtain ⟨fvsP, crest, xFvs, idxArgs, hopP, hopF, hopAll, hidx_len⟩ :=
          ctor_openPis_residual hstrip_c hes_len
        have hres_ca : cvCa₀.type.constsResolve c₁.env = true := by
          obtain ⟨ty', ⟨_, _, _, _, _, _, _, _, hcr, _⟩, hcv⟩ := hcvC_chk
          have hty_eq : cvCa₀.type = ty' := by rw [hcv]
          rwa [hty_eq]
        obtain ⟨hfvs_res, happ_res⟩ := openPisAtFvars_constsResolve (nP + c_j.2) hres_ca hopAll
        have hxFvs_res : ∀ x ∈ xFvs, x.fvarTypeD.constsResolve c₁.env = true :=
          fun x hx => hfvs_res x (List.mem_append_right _ hx)
        have hidx_res : ∀ e ∈ idxArgs, e.constsResolve c₁.env = true := by
          intro e he
          have hga_res := (constsResolve_getApp happ_res).2
          rw [getAppArgs_mkAppN_const] at hga_res
          exact hga_res e (List.mem_append_right _ he)
        have e_rt := ev_rt.heap_extends
        have e_from_m34_to_m476 := e_from_m34_to_m430.trans e_rt
        have e_to_fu := e_cprj.trans e_from_m34_to_m476
        obtain ⟨sorts_j, hfsorts_j⟩ :=
          check_field_universes_spec hLevels hCore (by omega) hlveq hinf₀ hopP hopF hopAll
            (hrc.mono e_to_fu) hef₁ hlf₁ hg_fu
            (repKLevel_heapMono₂ e_to_fu hpind)
            (hcty_exact_m34.mono e_from_m34_to_m476).toTm hnt_476 ev_fu
        have e_fu := ev_fu.heap_extends
        have e_from_m34_to_m546 := e_from_m34_to_m476.trans e_fu
        have e_to_pos := e_cprj.trans e_from_m34_to_m546
        have hpos_ext :
            (∀ i < c_j.2,
              (Ix.Kernel.recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1 ≠ .negative ∧
               Ix.Kernel.recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1 ≠ .unsupported) ∧
              ((cbs.getD (nP + i) default).1.mentionsConst T = false ∨
               RawRecSpine T (rcbs.getD (nP + i) default).1 (cbs.getD (nP + i) default).1)) ∧
            Heap.Extends m546 m646 := by
          cases sg_pos with
          | other hne _ _ _ => exact absurd rfl hne
          | n0 _ _ _ cs_pos _ ev_params ev_pos hc_sg =>
            have hg_pos : Good c₁ cs_pos :=
              hgood.sub (fun x hx => by simp [hc, hc_sg, hx])
            have e_params := ev_params.heap_extends
            exact ⟨check_positivity_spec hlps hlps_lt (by omega) (by omega) hpeer₁ hlf₁ hg_pos
              (hcty_raw_m34.mono (e_from_m34_to_m546.trans e_params)) hnp_ca hstR_c hstrip_c
              (Bytes.repAddressRef_heapMono₂ addrTy (e_to_pos.trans e_params) hbp) ev_pos,
              e_params.trans ev_pos.heap_extends⟩
        have e_to_rec := e_to_pos.trans hpos_ext.2
        rw [evalBinOp_add_nat j 1 op_add] at ev_rec
        obtain ⟨sortss_rest, hlen_rest, hrest_out⟩ :=
          check_inductive_shape_ctors_go hLevels hCore hlps hlps_lt hnP_lt hnIdx_lt hnCtors_lt
            hnF_lt hlveq hcload hlps_ctors hlbd_ctors hfv_ctors hfresh_ctors hbasis_ctors
            hshape_ctors hno_proj_T hstore₁ hef₁ hlf₁ hpeer₁
            m (j + 1) (by omega) hsub_rec hg_rec
            (hrc.mono e_to_rec) (hta.mono e_to_rec)
            (Bytes.repAddressRef_heapMono₂ addrTy e_to_rec hbp)
            (repKLevel_heapMono₂ e_to_rec hpind) ev_rec
        refine ⟨sorts_j :: sortss_rest, by simp [hlen_rest], fun t_idx ht => ?_⟩
        cases t_idx with
        | zero =>
          rw [Nat.add_zero]
          exact ⟨c_j, (cvCa₀, c_j.2), sorts_j, hc_j, hcA_j, rfl,
            { nF_eq := rfl
              stored := hvs_j
              cvCheck := hcvC_chk
              noProj := hnp_ca
              inferSort := ⟨sty₀, u₀, hinf₀, hred₀⟩
              residual := ⟨rcbs, rargs, cbs, es, hstR_c, hrcbs_len, hstrip_c, hcbs_len,
                hes_len, hes_noT, (fun i hi => (hpos_ext.1 i hi).1),
                (fun i hi => (hpos_ext.1 i hi).2)⟩
              domsShared := hdoms_sh
              opened := ⟨fvsP, crest, xFvs, idxArgs, hopP, hopF, hidx_len,
                hxFvs_res, hidx_res, hfsorts_j⟩ }⟩
        | succ t' =>
          obtain ⟨c', cA', sorts', hc', hcA', hs', hout'⟩ := hrest_out t' (by omega)
          rw [show j + 1 + t' = j + (t' + 1) by omega] at hc' hcA' hout'
          exact ⟨c', cA', sorts', hc', hcA', hs', hout'⟩

/-- Shared front-end witness for a 1-type unpinned native inductive block `p₀` checked on the
non-modeled `Induct` arm of `KernelCheck::check_const`. Reused by both `NativeFront` (no recursor)
and `NativeRec` (with recursor). -/
structure OneTypeBlockWitness (calls : List (Call F)) (env : Ix.Kernel.Env .anon)
    (p₀ : Ix.Kernel.NativeParts .anon) where
  E₀ : Ixon.Env
  E₁ : Ixon.Env
  t : Ix.Kernel.RoleTable
  lim₀ : Option Nat
  b₀ : Bytes.Address
  a_ind : Bytes.Address
  cvTa₀ : KConstantVal
  ctorsA : List (KConstantVal × Nat)
  ctorRawTypes : List KExpr
  rc₀ : SourceValue F
  nl₀ : SourceValue F
  pty₀ : SourceValue F
  bp₀ : SourceValue F
  ap₀ : SourceValue F
  r₀ : SourceValue F
  h_ind : Heap F
  h_ind' : Heap F
  cs_ind : List (Call F)
  twf : t.wf = true
  roles₀ : CtxRoleFacts ⟨E₀, env, t, lim₀⟩
  roles₁ : CtxRoleFacts ⟨E₁, ⟨.indInfo cvTa₀ {} :: env.consts⟩, t, lim₀⟩
  ctors_nodup : (p₀.ctors.map (·.1.name)).Nodup
  T_not_in_ctors : p₀.cvT.name ∉ p₀.ctors.map (·.1.name)
  fresh_T : env.find? p₀.cvT.name = none
  fresh_ctors : ∀ c ∈ p₀.ctors, env.find? c.1.name = none
  fresh_projFn : ∀ j, env.find? (Ix.Kernel.projFnName p₀.cvT.name j) = none
  fresh_projTbl : env.find? (Ix.Kernel.projTableName p₀.cvT.name) = none
  basis_T : Ix.Kernel.reservedBasisNames.contains p₀.cvT.name = false
  basis_ctors : ∀ c ∈ p₀.ctors, Ix.Kernel.reservedBasisNames.contains c.1.name = false
  shape_ctors : ∀ c ∈ p₀.ctors, c.1.name.isProjFnShape = false
  lps_T : p₀.cvT.levelParams = List.range p₀.cvT.levelParams.length
  lps_ctors : ∀ c ∈ p₀.ctors, c.1.levelParams = p₀.cvT.levelParams
  lbd_T : p₀.cvT.type.looseBVarsBounded 0 = true
  fv_T : p₀.cvT.type.hasFvar = false
  lbd_ctors : ∀ c ∈ p₀.ctors, c.1.type.looseBVarsBounded 0 = true
  fv_ctors : ∀ c ∈ p₀.ctors, c.1.type.hasFvar = false
  counts_lt :
    p₀.cvT.levelParams.length < 4294967296 ∧
    p₀.nP < 2147483648 ∧
    p₀.nIdx < 2147483648 ∧
    p₀.ctors.length < 4294967296 ∧
    ∀ c ∈ p₀.ctors, c.2 < 2147483648
  T_iprj : p₀.cvT.name = keyOf t (iprjAddr (ixAddr b₀) 0)
  valStored_T : IxVM.Consistency.ValStored cvTa₀ p₀.cvT
  valRep_T : ValRepExact (keyOf t) h_ind nl₀ pty₀ cvTa₀
  rcRep₀ : RCRep t lim₀ h_ind rc₀
  bpRep₀ : Bytes.RepAddressRef addrTy h_ind b₀ bp₀
  apRep₀ : Bytes.RepAddressRef addrTy h_ind a_ind ap₀
  ev_ind : ObsFn W "KernelCheck::check_const"
    [rc₀, .construct kciEnum "Induct"
      [nl₀, pty₀, .field (p₀.nP : F), .field (p₀.nIdx : F),
        .field (p₀.ctors.length : F), .field 0, bp₀, .field 0], ap₀]
    h_ind r₀ h_ind' cs_ind
  sub_ind : ∀ x ∈ cs_ind, x ∈ calls
  unmodeled : ∀ m r h' cs,
    ObsFn W "KernelModeled::block_is_modeled" [bp₀] m r h' cs →
    (∀ x ∈ cs, x ∈ cs_ind) → r = .field 0
  lf₀ : LoadFacts ⟨E₀, env, t, lim₀⟩
  good₀ : Good ⟨E₀, env, t, lim₀⟩ cs_ind
  peer₀ : OneTypePeerFacts ⟨E₀, env, t, lim₀⟩ b₀ p₀.cvT.name
    p₀.cvT.levelParams.length p₀.nP p₀.nIdx p₀.ctors.length
  lf₁ : LoadFacts ⟨E₁, ⟨.indInfo cvTa₀ {} :: env.consts⟩, t, lim₀⟩
  good₁ : Good ⟨E₁, ⟨.indInfo cvTa₀ {} :: env.consts⟩, t, lim₀⟩ cs_ind
  peer₁ : OneTypePeerFacts ⟨E₁, ⟨.indInfo cvTa₀ {} :: env.consts⟩, t, lim₀⟩ b₀ p₀.cvT.name
    p₀.cvT.levelParams.length p₀.nP p₀.nIdx p₀.ctors.length
  cload : CtorLoadAt t b₀ p₀.nP cs_ind p₀.ctors ctorsA ctorRawTypes

/-- Output of the shared front-end pass (`nativeFront_pass`) on `KernelCheck::check_const` (`Induct`). -/
structure NativeFrontOut (env : Ix.Kernel.Env .anon) (p₀ : Ix.Kernel.NativeParts .anon)
    (cvTa₀ : KConstantVal) (ctorsA : List (KConstantVal × Nat))
    (ctorRawTypes : List KExpr) (ind_lvl : KLevel) (sortss : List (List KLevel)) : Prop where
  storeInv₁ : DeclStoreInv ⟨.indInfo cvTa₀ {} :: env.consts⟩
  cvT_check : ConstantValCheckJ rulesJ env p₀.cvT cvTa₀
  ta_noT : cvTa₀.type.mentionsConst p₀.cvT.name = false
  sort_lveq : ∀ bs s,
    cvTa₀.type.stripPis (p₀.nP + p₀.nIdx) = some (bs, .sort s) → LvEq s ind_lvl
  former_ok :
    (∀ cA ∈ ctorsA, ∀ cbsP cbodyP,
      cA.1.type.stripPis p₀.nP = some (cbsP, cbodyP) →
      ∀ p < p₀.nP, (cbsP.getD p default).1.mentionsConst p₀.cvT.name = false) →
    (∃ bs s, cvTa₀.type.stripPis (p₀.nP + p₀.nIdx) = some (bs, .sort s) ∧
      bs.length = p₀.nP + p₀.nIdx) ∨
    (p₀.nIdx ≠ 0 ∧ ∀ k < ctorsA.length, ∀ cA, ctorsA[k]? = some cA →
      ctorZeroOk p₀.cvT.name ind_lvl.zeronessOf cA.1.type = true)
  sortss_len : sortss.length = p₀.ctors.length
  ctors_out : ∀ j < p₀.ctors.length, ∃ c cA sorts,
    p₀.ctors[j]? = some c ∧
    ctorsA[j]? = some cA ∧
    sortss[j]? = some sorts ∧
    NativeCtorOut ⟨.indInfo cvTa₀ {} :: env.consts⟩
      p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx ind_lvl cvTa₀.type
      (ctorRawTypes.getD j default) c cA sorts

/-- Execute the non-modeled `Induct` arm of `KernelCheck::check_const`, establishing
`ConstantValCheckJ` on the former, `former_decl_ok`, and `NativeCtorOut` for all constructors. -/
theorem nativeFront_pass (hLevels : IxVM.Consistency.Levels) (hCore : IxVM.Consistency.Core S₀)
    {calls : List (Call F)} {env : Ix.Kernel.Env .anon} {p₀ : Ix.Kernel.NativeParts .anon}
    (hS : DeclStoreInv env) (w : OneTypeBlockWitness calls env p₀) :
    ∃ (ind_lvl : KLevel) (sortss : List (List KLevel)),
      NativeFrontOut env p₀ w.cvTa₀ w.ctorsA w.ctorRawTypes ind_lvl sortss := by
  let c₀ : Ctx := ⟨w.E₀, env, w.t, w.lim₀⟩
  let c₁ : Ctx := ⟨w.E₁, ⟨.indInfo w.cvTa₀ {} :: env.consts⟩, w.t, w.lim₀⟩
  obtain ⟨hlps_lt, hnP_lt, hnIdx_lt, hnCtors_lt, hnF_lt⟩ := w.counts_lt
  have hshape_T : p₀.cvT.name.isProjFnShape = false := by
    rw [w.T_iprj]
    exact nat_keyOf_isProjFnShape_false w.t _
  have hlps_Ta₀ : w.cvTa₀.levelParams = List.range p₀.cvT.levelParams.length := by
    rw [w.valStored_T.1 |> fun _ => w.valStored_T.2.1]
    exact w.lps_T
  match Obs.«KernelCheck::check_const».obs w.ev_ind with
  | .Axiom_n1 (hv37 := hv) .. => injection hv with _ hc _; exact absurd hc (by decide)
  | .Axiom_other_n0 (hv37 := hv) .. => injection hv with _ hc _; exact absurd hc (by decide)
  | .Axiom_other_other (hv37 := hv) .. => injection hv with _ hc _; exact absurd hc (by decide)
  | .Defn (hv269 := hv) .. => injection hv with _ hc _; exact absurd hc (by decide)
  | .Thm (hv526 := hv) .. => injection hv with _ hc _; exact absurd hc (by decide)
  | .Opaque (hv825 := hv) .. => injection hv with _ hc _; exact absurd hc (by decide)
  | .Quot (hv1076 := hv) .. => injection hv with _ hc _; exact absurd hc (by decide)
  | .Ctor_n0_n0 (hne1879 := hne) .. => exact absurd rfl (hne [_, _, _, _, _, _, _, _] rfl)
  | .Ctor_n0_other (hne1879 := hne) .. => exact absurd rfl (hne [_, _, _, _, _, _, _, _] rfl)
  | .Ctor_other_n0 (hne1879 := hne) .. => exact absurd rfl (hne [_, _, _, _, _, _, _, _] rfl)
  | .Ctor_other_other (hne1879 := hne) .. => exact absurd rfl (hne [_, _, _, _, _, _, _, _] rfl)
  | .Rec_n0 (hne1879 := hne) .. => exact absurd rfl (hne [_, _, _, _, _, _, _, _] rfl)
  | .Rec_other (hne1879 := hne) .. => exact absurd rfl (hne [_, _, _, _, _, _, _, _] rfl)
  | .Induct_other_n0 (x_ind_block := xblk) (v1491 := vmod) (cs1503 := cs_mod)
      (hv1240 := hv_ind) (ev1505 := ev_mod) (hne1635 := hne_mod) (hc1869 := hc) .. =>
    injection hv_ind with _ _ hxs
    injection hxs with _ hxs; injection hxs with _ hxs; injection hxs with _ hxs
    injection hxs with _ hxs; injection hxs with _ hxs; injection hxs with _ hxs
    injection hxs with hblk_eq _
    subst hblk_eq
    exact absurd (w.unmodeled _ _ _ _ ev_mod (fun x hx => by simp [hc, hx])) hne_mod
  | .Induct_other_other (x_ind_block := xblk) (v1491 := vmod) (cs1503 := cs_mod)
      (hv1240 := hv_ind) (ev1505 := ev_mod) (hne1635 := hne_mod) (hc1878 := hc) .. =>
    injection hv_ind with _ _ hxs
    injection hxs with _ hxs; injection hxs with _ hxs; injection hxs with _ hxs
    injection hxs with _ hxs; injection hxs with _ hxs; injection hxs with _ hxs
    injection hxs with hblk_eq _
    subst hblk_eq
    exact absurd (w.unmodeled _ _ _ _ ev_mod (fun x hx => by simp [hc, hx])) hne_mod
  | .Induct_n0 (m2 := m2) (x_nlvls := xnl) (x_ty := xty)
      (x_n_params := xnp) (x_n_indices := xni) (x_num_ctors := xnc)
      (x_ind_is_unsafe := xiu) (x_ind_block := xblk) (x_ind_idx := xidx)
      (m1283 := m1283) (cs1293 := cs_ws) (v1330 := v_emb) (m1333 := m1333)
      (cs1341 := cs_emb) (m1354 := m1354) (m1376 := m1376)
      (m1396 := m1396) (cs1406 := cs_es) (m1427 := m1427)
      (m1440 := m1440) (m1470 := m1470) (m1492 := m1492)
      (cs1529 := cs_sh)
      (ev14 := ev_iu) (hv1240 := hv_ind) (ev1295 := ev_ws)
      (hm1362 := hm1354) (hm1384 := hm1376) (ev1343 := ev_emb) (heq1394 := hv_emb)
      (hm1435 := hm1427) (ev1408 := ev_es) (ev1452 := ev_saf)
      (ev1482 := ev_mk) (ev1505 := ev_mod) (ev1531 := ev_sh) (hc1634 := hc) .. =>
    injection hv_ind with _ _ hxs
    injection hxs with hnl hxs; injection hxs with hty hxs; injection hxs with hnp hxs
    injection hxs with hni hxs; injection hxs with hnc hxs; injection hxs with hiu hxs
    injection hxs with hblk hxs; injection hxs with hidx _
    subst hnl hty hnp hni hnc hiu hblk hidx
    have hef₀ : EnvFacts c₀ := hS.toEnvFacts w.twf w.roles₀
    have hg₀_emb : Good c₀ cs_emb := w.good₀.sub (fun x hx => by simp [hc, hx])
    have hg₀_es : Good c₀ cs_es := w.good₀.sub (fun x hx => by simp [hc, hx])
    have e_iu := ev_iu.heap_extends
    have e_ws := ev_ws.heap_extends
    have e_1376 : Heap.Extends m1283 m1376 := by rw [hm1376]; exact Heap.Extends.snoc m1283 _
    have e_1354 : Heap.Extends m1376 m1354 := by rw [hm1354]; exact Heap.Extends.snoc m1376 _
    have e_emb := ev_emb.heap_extends
    have e_1427 : Heap.Extends m1333 m1427 := by rw [hm1427]; exact Heap.Extends.snoc m1333 _
    have e_m2_to_1427 := e_ws.trans (e_1376.trans (e_1354.trans (e_emb.trans e_1427)))
    have e_to_1427 := e_iu.trans e_m2_to_1427
    have hv_m2 : ValRepExact c₀.κ m2 w.nl₀ w.pty₀ w.cvTa₀ :=
      ⟨w.valRep_T.1, w.valRep_T.2.1, w.valRep_T.2.2.1, w.valRep_T.2.2.2.mono e_iu⟩
    have hty_nil_es : TypesRep c₀.κ (fun _ => default) m1427 0
        (.ptr (.enum kexprListEnum) m1333.length) := by
      rw [hm1427]; exact typesRep_alloc_nil c₀.κ (fun _ => default) m1333
    obtain ⟨hcvT_chk, styT, _, _, hinfT, _, _, _⟩ :=
      constantValCheckJ_of_checked hCore (c := c₀) (Γ := fun _ => default)
        w.valStored_T hv_m2 w.lbd_T w.fv_T w.fresh_T w.basis_T hshape_T
        hS.store (PosSortLift.of_range hlps_Ta₀) ev_ws e_m2_to_1427
        (w.rcRep₀.mono e_to_1427) hty_nil_es hef₀ w.lf₀ hg₀_es ev_es
    rw [hlps_Ta₀, posOf_range] at hinfT
    have hno_proj₀ : ∀ i, env.findProj? p₀.cvT.name i = none := by
      intro i
      unfold Ix.Kernel.Env.findProj?
      rw [w.fresh_projTbl]
    have hfv_Ta₀ : w.cvTa₀.type.hasFvar = false :=
      annotates_hasFvar_false w.valStored_T.2.2 w.fv_T
    have hnp_Ta₀ : noProjAt p₀.cvT.name w.cvTa₀.type = true :=
      noProjAt_of_infer_full hno_proj₀ hinfT hfv_Ta₀
    have hpty_exact₀ : TmExact c₀.κ 0 (fun _ => default) w.h_ind 0 w.cvTa₀.type w.pty₀ := by
      have h0 := w.valRep_T.2.2.2 0 (fun _ => default)
      rwa [hlps_Ta₀, posOf_range] at h0
    have e_to_1354 := e_iu.trans (e_ws.trans (e_1376.trans e_1354))
    have hnil_bas : RepList addrListEnum (Bytes.RepAddressRef addrTy) m1354 []
        (.ptr (.enum addrListEnum) m1283.length) :=
      RepLinkedList.nil (e_1354.getElem?_eq (by rw [hm1376]; simp))
    have hbas_1354 : RepList addrListEnum (Bytes.RepAddressRef addrTy) m1354 [w.b₀]
        (.ptr (.enum addrListEnum) m1376.length) :=
      RepLinkedList.cons (by rw [hm1354]; simp)
        (Bytes.repAddressRef_heapMono₂ addrTy e_to_1354 w.bpRep₀) hnil_bas
    rw [hv_emb] at ev_emb
    have hta_noT : w.cvTa₀.type.mentionsConst p₀.cvT.name = false :=
      expr_mentions_block_zero_spec w.peer₀ w.lf₀ hg₀_emb
        (hpty_exact₀.mono e_to_1354) hnp_Ta₀ hbas_1354 ev_emb
    have hfresh_Ta₀ : env.find? w.cvTa₀.name = none := by
      rw [w.valStored_T.1]; exact w.fresh_T
    have hshape_Ta₀ : w.cvTa₀.name.isProjFnShape = false := by
      rw [w.valStored_T.1]; exact hshape_T
    have hwf_Ta₀ :
        w.cvTa₀.type.hasFvar = false ∧
        w.cvTa₀.type.allLevelParamsDefined w.cvTa₀.levelParams = true ∧
        w.cvTa₀.type.constsResolve env = true ∧
        w.cvTa₀.type.looseBVarsBounded 0 = true := by
      obtain ⟨ty', ⟨_, _, _, _, hlbd₀, _, _, hlpd', hcr', _⟩, hcv⟩ := hcvT_chk
      have hty_eq : w.cvTa₀.type = ty' := by rw [hcv]
      have hlps_eq : w.cvTa₀.levelParams = p₀.cvT.levelParams := w.valStored_T.2.1
      rw [hty_eq, hlps_eq]
      exact ⟨by rw [← hty_eq]; exact hfv_Ta₀, hlpd', hcr',
        by rw [← hty_eq]; exact annotates_looseBVarsBounded w.valStored_T.2.2 0 w.lbd_T⟩
    have hS₁ : DeclStoreInv ⟨.indInfo w.cvTa₀ {} :: env.consts⟩ :=
      hS.consIndEmpty hfresh_Ta₀ (ne_projTableName_of_isProjFnShape_false hshape_Ta₀) hwf_Ta₀
    have hef₁ : EnvFacts c₁ := hS₁.toEnvFacts w.twf w.roles₁
    have e_es := ev_es.heap_extends
    have e_saf := ev_saf.heap_extends
    have e_mk := ev_mk.heap_extends
    have e_mod := ev_mod.heap_extends
    have e_to_sh := e_to_1427.trans (e_es.trans (e_saf.trans (e_mk.trans e_mod)))
    have hnl₀_eq : w.nl₀ = .field (p₀.cvT.levelParams.length : F) := by
      rw [w.valRep_T.1, w.valStored_T.2.1]
    rw [hnl₀_eq] at ev_sh
    have hsub_sh : ∀ x ∈ cs_sh, x ∈ w.cs_ind := fun x hx => by simp [hc, hx]
    have hg₁_sh : Good c₁ cs_sh := w.good₁.sub hsub_sh
    match Obs.«KernelCheck::check_inductive_shape».obs ev_sh with
    | .run (v1 := v_ind_lvl) (m2 := m2_sh) (cs12 := cs_grs) (v17 := v_pi)
        (m50 := m50_sh) (m63 := m63_sh) (cs73 := cs_fdo) (cs135 := cs_ctors)
        (op46 := op_pi) (hm58 := hm50_sh) (ev14 := ev_grs) (ev75 := ev_fdo)
        (ev137 := ev_ctors) (hc225 := hc_sh) .. =>
      rw [evalBinOp_add_nat p₀.nP p₀.nIdx op_pi] at ev_grs
      have e_50 : Heap.Extends m1492 m50_sh := by rw [hm50_sh]; exact Heap.Extends.snoc m1492 _
      have e_to_50 := e_to_sh.trans e_50
      have hty_nil_grs : TypesRep c₁.κ (fun _ => default) m50_sh 0
          (.ptr (.enum kexprListEnum) m1492.length) := by
        rw [hm50_sh]; exact typesRep_alloc_nil c₁.κ (fun _ => default) m1492
      have hg₁_grs : Good c₁ cs_grs := hg₁_sh.sub (fun x hx => by simp [hc_sh, hx])
      have hg₁_fdo : Good c₁ cs_fdo := hg₁_sh.sub (fun x hx => by simp [hc_sh, hx])
      have hg₁_ctors : Good c₁ cs_ctors := hg₁_sh.sub (fun x hx => by simp [hc_sh, hx])
      have hsub_fdo : ∀ x ∈ cs_fdo, x ∈ w.cs_ind :=
        fun x hx => hsub_sh x (by simp [hc_sh, hx])
      have hsub_ctors : ∀ x ∈ cs_ctors, x ∈ w.cs_ind :=
        fun x hx => hsub_sh x (by simp [hc_sh, hx])
      have hpty_exact₁ : TmExact c₁.κ 0 (fun _ => default) w.h_ind 0 w.cvTa₀.type w.pty₀ :=
        hpty_exact₀
      obtain ⟨ind_lvl, hpind, hsort_lveq⟩ :=
        get_result_sort_level_spec hCore (c := c₁) (p₀.nP + p₀.nIdx) (by omega)
          (w.rcRep₀.mono e_to_50) hty_nil_grs (ghostScoped_zero _) hef₁ w.lf₁ hg₁_grs
          (hpty_exact₁.mono e_to_50).toTm ev_grs
      have e_grs := ev_grs.heap_extends
      have e_fdo := ev_fdo.heap_extends
      have e_to_m2_sh := e_to_50.trans e_grs
      have e_to_m63_sh := e_to_m2_sh.trans e_fdo
      have hfresh_ctors₁ : ∀ c ∈ p₀.ctors, c₁.env.find? c.1.name = none := by
        intro c hc
        have hne : w.cvTa₀.name ≠ c.1.name := by
          rw [w.valStored_T.1]
          intro heq
          exact w.T_not_in_ctors (by rw [heq]; exact List.mem_map.mpr ⟨c, hc, rfl⟩)
        show (Ix.Kernel.Env.mk (.indInfo w.cvTa₀ {} :: env.consts)).find? c.1.name = none
        rw [find?_cons_indInfo_ne _ _ _ hne]
        exact w.fresh_ctors c hc
      have hno_proj₁ : ∀ i, c₁.env.findProj? p₀.cvT.name i = none := by
        intro i
        have hne : w.cvTa₀.name ≠ Ix.Kernel.projTableName p₀.cvT.name :=
          ne_projTableName_of_isProjFnShape_false hshape_Ta₀ _
        dsimp only [Ix.Kernel.Env.findProj?, c₁]
        rw [find?_cons_indInfo_ne _ _ _ hne, w.fresh_projTbl]
      obtain ⟨sortss, hsortss_len, hctors_go⟩ :=
        check_inductive_shape_ctors_go hLevels hCore (c₁ := c₁)
          w.lps_T hlps_lt hnP_lt hnIdx_lt hnCtors_lt hnF_lt (fun _ => rfl)
          w.cload w.lps_ctors w.lbd_ctors w.fv_ctors hfresh_ctors₁ w.basis_ctors
          w.shape_ctors hno_proj₁ hS₁.store hef₁ w.lf₁ w.peer₁
          p₀.ctors.length 0 (by omega) hsub_ctors hg₁_ctors
          (w.rcRep₀.mono e_to_m63_sh) (hpty_exact₁.mono e_to_m63_sh).toTm
          (Bytes.repAddressRef_heapMono₂ addrTy e_to_m63_sh w.bpRep₀)
          (repKLevel_heapMono₂ e_fdo hpind) ev_ctors
      have hlps_ctors_range : ∀ cb ∈ p₀.ctors,
          cb.1.levelParams = List.range cb.1.levelParams.length := by
        intro cb hcb
        rw [w.lps_ctors cb hcb]
        exact w.lps_T
      have hfdo :
          (∀ cA ∈ w.ctorsA, ∀ cbsP cbodyP,
            cA.1.type.stripPis p₀.nP = some (cbsP, cbodyP) →
            ∀ p < p₀.nP, (cbsP.getD p default).1.mentionsConst p₀.cvT.name = false) →
          (∃ bs s, w.cvTa₀.type.stripPis (p₀.nP + p₀.nIdx) = some (bs, .sort s) ∧
            bs.length = p₀.nP + p₀.nIdx) ∨
          (p₀.nIdx ≠ 0 ∧ ∀ k < w.ctorsA.length, ∀ cA, w.ctorsA[k]? = some cA →
            ctorZeroOk p₀.cvT.name ind_lvl.zeronessOf cA.1.type = true) := by
        intro hpdom_noT
        have hctor_sp : ∀ k < p₀.ctors.length, ∀ c cvCa₀,
            p₀.ctors[k]? = some c →
            w.ctorsA[k]? = some (cvCa₀, c.2) →
            ∃ rcbs rargs cbs eargs us₀,
              (w.ctorRawTypes.getD k default).stripPis (p₀.nP + c.2) =
                some (rcbs, Expr.mkAppN (.const p₀.cvT.name us₀) rargs) ∧
              cvCa₀.type.stripPis (p₀.nP + c.2) =
                some (cbs, Expr.mkAppN (.const p₀.cvT.name us₀) eargs) ∧
              ∀ idx < p₀.nP + c.2,
                (cbs.getD idx default).1.mentionsConst p₀.cvT.name = false ∨
                RawRecSpine p₀.cvT.name (rcbs.getD idx default).1 (cbs.getD idx default).1 := by
          intro k hk c cvCa₀ hc hcA
          obtain ⟨c', cA', _, hc', hcA', _, hout⟩ := hctors_go k hk
          simp only [Nat.zero_add] at hc' hcA' hout
          rw [hc] at hc'; injection hc' with hc_eq; cases hc_eq
          rw [hcA] at hcA'; injection hcA' with hcA_eq; cases hcA_eq
          obtain ⟨rcbs, rargs, cbs, es, hstR_c, _, hstrip_c, hcbs_len, _, _, _, hsp_c⟩ :=
            hout.residual
          obtain ⟨cbsP, cbodyP, _, hst_c_P, _, hcbs_app, hlenP⟩ :=
            stripPis_split p₀.nP c.2 hstrip_c
          have hcA_mem : (cvCa₀, c.2) ∈ w.ctorsA := List.mem_of_getElem? hcA
          refine ⟨rcbs, rargs, cbs, Ix.Kernel.structPsAt c.2 p₀.nP ++ es,
            p₀.cvT.levelParams.map .param, hstR_c, hstrip_c, fun idx hidx => ?_⟩
          by_cases hp : idx < p₀.nP
          · left
            have hp₁ : idx < cbsP.length := by omega
            have hp₂ : idx < cbs.length := by omega
            have hq : cbs[idx]? = cbsP[idx]? := by
              rw [← hcbs_app, List.getElem?_append_left hp₁]
            rw [List.getD_eq_getElem?_getD, hq, ← List.getD_eq_getElem?_getD]
            exact hpdom_noT (cvCa₀, c.2) hcA_mem cbsP cbodyP hst_c_P idx hp
          · have hi : idx - p₀.nP < c.2 := by omega
            have heq_idx : idx = p₀.nP + (idx - p₀.nP) := by omega
            rw [heq_idx]
            exact hsp_c (idx - p₀.nP) hi
        exact former_decl_ok_spec (c := c₁) w.twf (by omega) hnCtors_lt
          w.T_iprj hlps_ctors_range w.cload hctor_sp hsub_fdo hg₁_fdo
          (hpty_exact₁.mono e_to_m2_sh)
          (Bytes.repAddressRef_heapMono₂ addrTy e_to_m2_sh w.bpRep₀)
          hpind ev_fdo
      refine ⟨ind_lvl, sortss,
        { storeInv₁ := hS₁
          cvT_check := hcvT_chk
          ta_noT := hta_noT
          sort_lveq := hsort_lveq
          former_ok := hfdo
          sortss_len := hsortss_len
          ctors_out := fun j hj => ?_ }⟩
      obtain ⟨c, cA, sorts, hc, hcA, hs, hout⟩ := hctors_go j hj
      simp only [Nat.zero_add] at hc hcA hout
      exact ⟨c, cA, sorts, hc, hcA, hs, hout⟩

/-- Hypothesis bundle for the recursor-less native one-type inductive slice (`L5-N` no-recursor). -/
structure NativeNoRecExtra (calls : List (Call F)) (env : Ix.Kernel.Env .anon)
    (p₀ : Ix.Kernel.NativeParts .anon) where
  witness : OneTypeBlockWitness calls env p₀
  doms_bridge :
    ∀ cA ∈ witness.ctorsA,
      StructDomsShared ⟨.indInfo witness.cvTa₀ {} :: env.consts⟩
        witness.cvTa₀.type cA.1.type p₀.nP →
      ∀ fvsP crest tfvs trest cbs cbody tbs tbody,
        Ix.Kernel.openPisAtFvars p₀.nP cA.1.type 0 = some (fvsP, crest) →
        Ix.Kernel.openPisAtFvars p₀.nP witness.cvTa₀.type 0 = some (tfvs, trest) →
        witness.cvTa₀.type.stripPis p₀.nP = some (tbs, tbody) →
        cA.1.type.stripPis p₀.nP = some (cbs, cbody) →
        (¬ ∀ i < p₀.nP, (cbs.getD i default).1 = (tbs.getD i default).1) →
        StructDomsJ rulesJ ⟨.indInfo witness.cvTa₀ {} :: env.consts⟩
          0 fvsP (tfvs.map Expr.fvarTypeD) p₀.nP ∧
          (∀ p < p₀.nP, (cbs.getD p default).1.mentionsConst p₀.cvT.name = false)
  unused_later :
    ∀ cA ∈ witness.ctorsA, ∀ cbs body,
      cA.1.type.stripPis (p₀.nP + cA.2) = some (cbs, body) →
      ∀ i < cA.2,
        (Ix.Kernel.recFieldKind p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx i
           (cbs.getD (p₀.nP + i) default).1 = .recursive ∨
         Ix.Kernel.recFieldKind p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx i
           (cbs.getD (p₀.nP + i) default).1 = .reflexive) →
        Ix.Kernel.structUsedLater cA.1.type p₀.nP i = false

/-- **Deliverable 2 (`L5` Recursor-Less Native One-Type Block)**:
Refines an unpinned `.indDecl block nP` with `nativePartsNoRec? nP block = some p₀` to
`InstallStep env (.indDecl block nP) env₂` and `DeclNativeNoRecRunJ rulesJ env p₀ env₂`. -/
theorem nativeNoRec_step (hLevels : IxVM.Consistency.Levels) (hCore : IxVM.Consistency.Core S₀)
    {calls : List (Call F)} {env : Ix.Kernel.Env .anon}
    {block : List KConstantInfo} {nP : Nat} {p₀ : Ix.Kernel.NativeParts .anon}
    (hpin : Ix.Kernel.basisPinHit block = none)
    (hparts : nativePartsNoRec? nP block = some p₀)
    (hS : DeclStoreInv env)
    (extra : NativeNoRecExtra calls env p₀) :
    ∃ env₂,
      IxVM.Consistency.InstallStep env (.indDecl block nP) env₂ ∧
      DeclNativeNoRecRunJ rulesJ env p₀ env₂ := by
  obtain ⟨caps₀, hblk, hnP_eq, hlarge, hbasis_T, _, ⟨bs₀, hst_raw⟩, hisProp⟩ :=
    nativePartsNoRec?_inv hparts
  let w := extra.witness
  obtain ⟨ind_lvl, sortss, fout⟩ := nativeFront_pass hLevels hCore hS w
  let envI₀ : Ix.Kernel.Env .anon := ⟨.indInfo w.cvTa₀ {} :: env.consts⟩
  obtain ⟨bsT, hst_Ta₀, _⟩ :=
    stripPis_sort_of_annotates (p₀.nP + p₀.nIdx) w.valStored_T.2.2 hst_raw
  obtain ⟨tbs, tbody, _, hst_Ta₀_P, _, _, _⟩ := stripPis_split p₀.nP p₀.nIdx hst_Ta₀
  obtain ⟨tfvsP, trestP, hopT_P⟩ :=
    Ix.Kernel.Model.openPisAtFvars_of_stripPis_isSome p₀.nP 0 (by rw [hst_Ta₀_P]; rfl)
  have hlveq : LvEq p₀.resSort ind_lvl := fout.sort_lveq bsT p₀.resSort hst_Ta₀
  have hbasis_Ta₀ : Ix.Kernel.reservedBasisNames.contains w.cvTa₀.name = false := by
    rw [w.valStored_T.1]; exact hbasis_T
  -- Per-constructor classification & `SumCtorRunJ` in `envI₀`
  have hctor_stage :
      ∀ (j : Nat) (c cA : KConstantVal × Nat),
        p₀.ctors[j]? = some c → w.ctorsA[j]? = some cA →
        cA.2 = c.2 ∧ ∃ sorts ks,
          sortss[j]? = some sorts ∧
          SumCtorRunJ rulesJ envI₀ envI₀ p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx
            p₀.resSort p₀.isProp false c.1 c.2 w.cvTa₀ cA.1 sorts ∧
          Ix.Kernel.recCtorKinds p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx cA = some ks ∧
          ks.length = cA.2 ∧
          (∀ k ∈ ks, k ≠ .negative ∧ k ≠ .unsupported) ∧
          Ix.Kernel.nativeOpenedOk env p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx
            cA.1.type cA.2 ks = true := by
    intro j c cA hc hcA
    have hj : j < p₀.ctors.length := by
      by_contra hge
      rw [List.getElem?_eq_none (by omega)] at hc
      exact nomatch hc
    obtain ⟨c', cA', sorts, hc', hcA', hsorts, hout⟩ := fout.ctors_out j hj
    rw [hc] at hc'; injection hc' with hc_eq; cases hc_eq
    rw [hcA] at hcA'; injection hcA' with hcA_eq; cases hcA_eq
    have hcA_mem : cA ∈ w.ctorsA := List.mem_of_getElem? hcA
    obtain ⟨_, _, cbs, es, _, _, hstrip_c, hcbs_len, hes_len, hes_noT, hpos_c, _⟩ := hout.residual
    obtain ⟨fvsP, crest, xFvs, idxArgs, hopP, hopF, hidx_len, hxFvs_res, hidx_res, hfsorts₀⟩ :=
      hout.opened
    obtain ⟨cbsP, cbodyP, _, hst_c_P, _, _, _⟩ := stripPis_split p₀.nP c.2 hstrip_c
    have hcbs_get_eq : ∀ i < p₀.nP, (cbsP.getD i default).1 = (cbs.getD i default).1 := by
      obtain ⟨cbs₁, _, cbs₂, hstP₁, _, hcbs_app, hlen₁⟩ := stripPis_split p₀.nP c.2 hstrip_c
      rw [hst_c_P] at hstP₁; injection hstP₁ with h1
      simp only [Prod.mk.injEq] at h1
      rcases h1 with ⟨rfl, _⟩
      intro i hi
      have hi₁ : i < cbsP.length := by omega
      have hi₂ : i < cbs.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi₁,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi₂]
      simp only [Option.getD_some]
      have hq : cbs[i]? = cbsP[i]? := by
        rw [← hcbs_app, List.getElem?_append_left hi₁]
      rw [List.getElem?_eq_getElem hi₂, List.getElem?_eq_getElem hi₁, Option.some.injEq] at hq
      exact congrArg Prod.fst hq.symm
    have hdoms_and_noT :
        StructDomsJ rulesJ envI₀ 0 fvsP (tfvsP.map Expr.fvarTypeD) p₀.nP ∧
          (∀ p < p₀.nP, (cbs.getD p default).1.mentionsConst p₀.cvT.name = false) := by
      by_cases hsame : ∀ i < p₀.nP, (cbsP.getD i default).1 = (tbs.getD i default).1
      · obtain ⟨hdj, hnoT⟩ :=
          structDomsJ_and_noT_of_same_doms hopP hopT_P hst_Ta₀_P hst_c_P fout.ta_noT hsame
        exact ⟨hdj, fun p hp => by rw [← hcbs_get_eq p hp]; exact hnoT p hp⟩
      · obtain ⟨hdj, hnoT⟩ :=
          extra.doms_bridge cA hcA_mem hout.domsShared fvsP crest tfvsP trestP cbsP cbodyP
            tbs tbody hopP hopT_P hst_Ta₀_P hst_c_P hsame
        exact ⟨hdj, fun p hp => by rw [← hcbs_get_eq p hp]; exact hnoT p hp⟩
    have hfsorts :
        FieldSortsJ rulesJ envI₀ p₀.isProp false p₀.resSort p₀.nP xFvs idxArgs c.2 sorts := by
      rw [hisProp]
      exact fieldSortsJ_congr_sort hlveq.symm hfsorts₀
    have hsum_c :
        SumCtorRunJ rulesJ envI₀ envI₀ p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx
          p₀.resSort p₀.isProp false c.1 c.2 w.cvTa₀ cA.1 sorts :=
      ⟨⟨cA.1, hout.cvCheck, Or.inl rfl⟩,
        ⟨cbs, es, hstrip_c, hes_len⟩,
        fvsP, crest, tfvsP, trestP, xFvs, idxArgs,
        hopP, hopT_P, Or.inr (hout.domsShared.toSharedPins hopT_P hopP hst_Ta₀_P hst_c_P
          (annotates_hasFvar_false hout.stored.2.2 (w.fv_ctors c (List.mem_of_getElem? hc)))),
        hopF, hidx_len, hxFvs_res, hidx_res, hfsorts⟩
    obtain ⟨sty_c, _, hinf_c, _⟩ := hout.inferSort
    have hfv_c : cA.1.type.hasFvar = false :=
      annotates_hasFvar_false hout.stored.2.2 (w.fv_ctors c (List.mem_of_getElem? hc))
    have hres_c : cA.1.type.constsResolve envI₀ = true := by
      obtain ⟨ty', ⟨_, _, _, _, _, _, _, _, hcr, _⟩, hcv⟩ := hout.cvCheck
      have hty_eq : cA.1.type = ty' := by rw [hcv]
      rwa [hty_eq]
    have hlit_c : litResolve env cA.1.type = true :=
      litResolve_of_infer_cons_former (ci := .indInfo w.cvTa₀ {}) hS.store rfl hbasis_Ta₀
        ⟨p₀.nP + p₀.nIdx, bsT, p₀.resSort, hst_Ta₀⟩ hinf_c hfv_c
    have hstrip_c' :
        cA.1.type.stripPis (p₀.nP + cA.2) =
          some (cbs, Expr.mkAppN (.const p₀.cvT.name (p₀.cvT.levelParams.map .param))
            (Ix.Kernel.structPsAt cA.2 p₀.nP ++ es)) := by
      rwa [hout.nF_eq]
    have hpos_c' : ∀ i < cA.2,
        Ix.Kernel.recFieldKind p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx i
          (cbs.getD (p₀.nP + i) default).1 ≠ .negative ∧
        Ix.Kernel.recFieldKind p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx i
          (cbs.getD (p₀.nP + i) default).1 ≠ .unsupported := by
      rw [hout.nF_eq]; exact hpos_c
    have hunused_c := extra.unused_later cA hcA_mem cbs _ hstrip_c'
    obtain ⟨ks, hrck, hks_len, hks_ok, hopen_ok⟩ :=
      recCtorKinds_and_nativeOpenedOk (ci := .indInfo w.cvTa₀ {})
        rfl w.valStored_T.1 hstrip_c' hes_len hes_noT hfv_c hres_c hlit_c
        hdoms_and_noT.2 hpos_c' hunused_c
    exact ⟨hout.nF_eq, sorts, ks, hsorts, hsum_c, hrck, hks_len, hks_ok, hopen_ok⟩
  -- Build `kinds` list via `Fin w.ctorsA.length`
  have hk_ex : ∀ idx : Fin w.ctorsA.length, ∃ ks,
      Ix.Kernel.recCtorKinds p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx w.ctorsA[idx.1] = some ks ∧
      ks.length = w.ctorsA[idx.1].2 ∧
      (∀ k ∈ ks, k ≠ .negative ∧ k ≠ .unsupported) ∧
      Ix.Kernel.nativeOpenedOk env p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx
        w.ctorsA[idx.1].1.type w.ctorsA[idx.1].2 ks = true := by
    intro ⟨j, hjA⟩
    have hj : j < p₀.ctors.length := by rwa [← w.cload.1]
    obtain ⟨_, _, _, _, _, hrck, hkl, hkok, hopok⟩ :=
      hctor_stage j p₀.ctors[j] w.ctorsA[j]
        (List.getElem?_eq_getElem hj) (List.getElem?_eq_getElem hjA)
    exact ⟨_, hrck, hkl, hkok, hopok⟩
  let kinds : List (List Ix.Kernel.RecFieldKind) :=
    (List.finRange w.ctorsA.length).map fun i => Classical.choose (hk_ex i)
  have hall_kinds :
      List.Forall₂
        (fun cA ks =>
          Ix.Kernel.recCtorKinds p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx cA = some ks ∧
          ks.length = cA.2 ∧
          (∀ k ∈ ks, k ≠ .negative ∧ k ≠ .unsupported) ∧
          Ix.Kernel.nativeOpenedOk env p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx
            cA.1.type cA.2 ks = true)
        w.ctorsA kinds := by
    rw [List.forall₂_iff_get]
    refine ⟨by simp [kinds], fun j hj₁ hj₂ => ?_⟩
    have hspec := Classical.choose_spec (hk_ex ⟨j, hj₁⟩)
    have hget : kinds[j] = Classical.choose (hk_ex ⟨j, hj₁⟩) := by
      simp [kinds]
    simpa [hget] using hspec
  obtain ⟨hclassify, hfields_ok⟩ := classifyFixKinds_and_nativeFieldsOk hall_kinds
  -- Assemble `p₁`, `isRec`, `p`, `env₁`, and upgrade `SumCtorsRunJ` via `CapsUpgradeAt`
  let p₁ : Ix.Kernel.InductiveShape .anon := p₀.toInductiveShape.withSort p₀.resSort
  have hp₁_eq : p₁ = p₀.toInductiveShape := Ix.Kernel.InductiveShape.withSort_self _ hisProp
  let isRec : Bool := Ix.Kernel.nativeIsRec kinds
  let p : Ix.Kernel.NativeParts .anon := (p₀.complete p₁).withKinds kinds
  let caps : Ix.Kernel.IndCaps .anon := Ix.Kernel.nativeCapsAt p₁ isRec
  let env₁ : Ix.Kernel.Env .anon := ⟨.indInfo w.cvTa₀ caps :: env.consts⟩
  have hfresh_Ta₀ : env.find? w.cvTa₀.name = none := by
    rw [w.valStored_T.1]; exact w.fresh_T
  have hup₀ : CapsUpgradeAt w.cvTa₀.name w.cvTa₀ caps envI₀ env₁ :=
    CapsUpgradeAt.of_fresh_ind caps hS.store hfresh_Ta₀ hbasis_Ta₀
  have hsum_ctors₀ :
      SumCtorsRunJ rulesJ envI₀ envI₀ p₀.cvT.name p₀.cvT.levelParams p₀.nP p₀.nIdx
        p₀.resSort p₀.isProp false w.cvTa₀ p₀.ctors w.ctorsA sortss := by
    refine ⟨w.cload.1, fout.sortss_len, fun j c cA hc hcA => ?_⟩
    obtain ⟨hnF, sorts, _, hsorts, hsc, _⟩ := hctor_stage j c cA hc hcA
    exact ⟨hnF, sorts, hsorts, hsc⟩
  have hsum_ctors₁ :
      SumCtorsRunJ rulesJ env₁ env₁ p.cvT.name p.cvT.levelParams p.nP p.nIdx
        p.resSort p.isProp p.large w.cvTa₀ p.ctors w.ctorsA sortss := by
    have hup_sc := hup₀.sumCtorsRunJ hsum_ctors₀
    simpa [p, p₁, hlarge, hisProp] using hup_sc
  have hshape_Ta₀ : w.cvTa₀.name.isProjFnShape = false := by
    rw [w.valStored_T.1, w.T_iprj]
    exact nat_keyOf_isProjFnShape_false w.t _
  have hext_env₁ : Ix.Kernel.EnvExt env env₁ :=
    envExt_cons_nonProj hfresh_Ta₀ (ne_projTableName_of_isProjFnShape_false hshape_Ta₀)
  obtain ⟨tfvs_all, isorts, hop_all, hisorts⟩ :=
    index_fieldSortsJ_of_former fout.cvT_check hst_Ta₀ hext_env₁
  -- Prepare `checkNativeTable_ok` on `env_base = consSumCtors p.nP w.ctorsA env₁`
  let env_base := Ix.Kernel.consSumCtors p.nP w.ctorsA env₁
  have hctorsA_names : w.ctorsA.map (·.1.name) = p₀.ctors.map (·.1.name) := by
    apply List.ext_getElem?
    intro j
    by_cases hj : j < p₀.ctors.length
    · obtain ⟨c, cvCa₀, hc, hcA, hvs, _⟩ := w.cload.2 j hj
      simp [hc, hcA, hvs.1]
    · have hjA : ¬ j < w.ctorsA.length := by rw [w.cload.1]; exact hj
      simp [List.getElem?_eq_none (Nat.le_of_not_lt hj),
        List.getElem?_eq_none (Nat.le_of_not_lt hjA)]
  have hnd_ctorsA : (w.ctorsA.map (·.1.name)).Nodup := by
    rw [hctorsA_names]; exact w.ctors_nodup
  have hshape_ctorsA : ∀ cA ∈ w.ctorsA, cA.1.name.isProjFnShape = false := by
    intro cA hcA
    obtain ⟨j, hjA, rfl⟩ := List.getElem_of_mem hcA
    have hj : j < p₀.ctors.length := by rwa [← w.cload.1]
    obtain ⟨c, cvCa₀, hc, hcA', hvs, _⟩ := w.cload.2 j hj
    rw [List.getElem?_eq_getElem hjA] at hcA'
    injection hcA' with heq
    have hn : w.ctorsA[j].1.name = c.1.name := by rw [heq]; exact hvs.1
    rw [hn]
    exact w.shape_ctors c (List.mem_of_getElem? hc)
  have hfresh_ctorsA_env₁ : ∀ cA ∈ w.ctorsA, env₁.find? cA.1.name = none := by
    intro cA hcA
    have hc_mem_names : cA.1.name ∈ p₀.ctors.map (·.1.name) := by
      rw [← hctorsA_names]; exact List.mem_map.mpr ⟨cA, hcA, rfl⟩
    obtain ⟨c, hc_mem, hname_eq⟩ := List.mem_map.mp hc_mem_names
    have hne : w.cvTa₀.name ≠ cA.1.name := by
      rw [w.valStored_T.1, ← hname_eq]
      exact fun heq => w.T_not_in_ctors (by rw [heq]; exact List.mem_map.mpr ⟨c, hc_mem, rfl⟩)
    show (Ix.Kernel.Env.mk (.indInfo w.cvTa₀ caps :: env.consts)).find? cA.1.name = none
    rw [find?_cons_indInfo_ne _ _ _ hne, ← hname_eq]
    exact w.fresh_ctors c hc_mem
  have hext_ctors : Ix.Kernel.EnvExt env₁ env_base :=
    envExt_consSumCtors p.nP w.ctorsA hnd_ctorsA hfresh_ctorsA_env₁ hshape_ctorsA
  have hT_ne_ctorsA : ∀ cA ∈ w.ctorsA, cA.1.name ≠ p.cvT.name := by
    intro cA hcA heq
    have hm : p₀.cvT.name ∈ p₀.ctors.map (·.1.name) := by
      rw [← hctorsA_names]
      have hpT : p.cvT.name = p₀.cvT.name := rfl
      rw [← hpT, ← heq]
      exact List.mem_map.mpr ⟨cA, hcA, rfl⟩
    exact w.T_not_in_ctors hm
  have hT_in_base : (env_base.find? p.cvT.name).isSome = true := by
    rw [find?_consSumCtors_ne p.nP w.ctorsA env₁ hT_ne_ctorsA]
    have hpT : p.cvT.name = w.cvTa₀.name := w.valStored_T.1.symm
    rw [hpT, hup₀.find_self_b]
    rfl
  have hc_wf_base : ∀ cA ∈ w.ctorsA,
      (cA.1.type.stripPis (p.nP + cA.2)).isSome = true ∧
      cA.1.type.hasFvar = false ∧
      cA.1.type.allLevelParamsDefined p.cvT.levelParams = true ∧
      cA.1.type.constsResolve env_base = true ∧
      cA.1.type.looseBVarsBounded 0 = true := by
    intro cA hcA
    obtain ⟨j, hjA, rfl⟩ := List.getElem_of_mem hcA
    have hj : j < p₀.ctors.length := by rwa [← w.cload.1]
    obtain ⟨c, cA', _, hc, hcA', _, hout⟩ := fout.ctors_out j hj
    rw [List.getElem?_eq_getElem hjA] at hcA'; injection hcA' with hcA_eq; cases hcA_eq
    obtain ⟨_, _, cbs, es, _, _, hstrip_c, _⟩ := hout.residual
    have hst_some : (w.ctorsA[j].1.type.stripPis (p.nP + w.ctorsA[j].2)).isSome = true := by
      have hpN : p.nP = p₀.nP := rfl
      rw [hpN, hout.nF_eq, hstrip_c]; rfl
    obtain ⟨ty', ⟨_, _, _, _, hlbd₀, hfv₀, _, hlpd', hcr₀, _⟩, hcv⟩ := hout.cvCheck
    have hty_eq : w.ctorsA[j].1.type = ty' := by rw [hcv]
    have hfv' : w.ctorsA[j].1.type.hasFvar = false :=
      annotates_hasFvar_false hout.stored.2.2 hfv₀
    have hlbd' : w.ctorsA[j].1.type.looseBVarsBounded 0 = true :=
      annotates_looseBVarsBounded hout.stored.2.2 0 hlbd₀
    have hlpd'' : w.ctorsA[j].1.type.allLevelParamsDefined p.cvT.levelParams = true := by
      have hpL : p.cvT.levelParams = c.1.levelParams :=
        (w.lps_ctors c (List.mem_of_getElem? hc)).symm
      rwa [hpL, hty_eq]
    have hcr₁ : w.ctorsA[j].1.type.constsResolve env₁ = true := by
      rw [hup₀.constsResolve_eq, hty_eq]; exact hcr₀
    have hcr_base : w.ctorsA[j].1.type.constsResolve env_base = true :=
      Ix.Kernel.Expr.constsResolve_le
        (fun k hk => by
          obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hk
          rw [hext_ctors.find hci]; rfl)
        hcr₁
    exact ⟨hst_some, hfv', hlpd'', hcr_base, hlbd'⟩
  have hfn_fresh_base : ∀ j, env_base.find? (Ix.Kernel.projFnName p.cvT.name j) = none := by
    intro j
    rw [find?_consSumCtors_ne p.nP w.ctorsA env₁
      (fun cA hcA => ne_projFnName_of_isProjFnShape_false (hshape_ctorsA cA hcA) _ _)]
    show (Ix.Kernel.Env.mk (.indInfo w.cvTa₀ caps :: env.consts)).find?
      (Ix.Kernel.projFnName p₀.cvT.name j) = none
    rw [find?_cons_indInfo_ne _ _ _ (ne_projFnName_of_isProjFnShape_false hshape_Ta₀ _ _)]
    exact w.fresh_projFn j
  have htbl_fresh_base : env_base.find? (Ix.Kernel.projTableName p.cvT.name) = none := by
    rw [find?_consSumCtors_ne p.nP w.ctorsA env₁
      (fun cA hcA => ne_projTableName_of_isProjFnShape_false (hshape_ctorsA cA hcA) _)]
    show (Ix.Kernel.Env.mk (.indInfo w.cvTa₀ caps :: env.consts)).find?
      (Ix.Kernel.projTableName p₀.cvT.name) = none
    rw [find?_cons_indInfo_ne _ _ _ (ne_projTableName_of_isProjFnShape_false hshape_Ta₀ _)]
    exact w.fresh_projTbl
  obtain ⟨env₂, htable_ok, henv₂_cases⟩ :=
    checkNativeTable_ok hT_in_base hc_wf_base hfn_fresh_base htbl_fresh_base
  -- Prove `DeclNativeNoRecRunJ rulesJ env p₀ env₂`
  have hNoRecRun : DeclNativeNoRecRunJ rulesJ env p₀ env₂ := by
    refine ⟨w.ctors_nodup, isRec, env₁, w.cvTa₀, p₁, p, w.ctorsA, sortss, kinds,
      tfvs_all, .sort p₀.resSort, isorts, ?_, rfl, hsum_ctors₁, ?_, rfl, ?_, ?_, ?_,
      htable_ok, ?_⟩
    · exact ⟨w.cvTa₀, p₀.resSort, bsT, w.cvTa₀, fout.cvT_check, Or.inl rfl, hst_Ta₀,
        Or.inl rfl, rfl, rfl⟩
    · simpa [p, p₁] using hclassify
    · simpa [p, p₁] using hop_all
    · simpa [p, p₁] using hisorts
    · simpa [p, p₁] using hfields_ok
    · refine Or.inl ⟨caps, ?_⟩
      have hpT : p.cvT.name = w.cvTa₀.name := w.valStored_T.1.symm
      rw [hpT]
      exact hup₀.find_self_b
  -- Prove `InstallStep env (.indDecl block nP) env₂` via `installStep_of_perm_and_optTable`
  let ciT : KConstantInfo := .indInfo w.cvTa₀ caps
  let ctors_ci : List KConstantInfo :=
    w.ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 p₀.nP c.2)
  let blockA : List KConstantInfo := ciT :: ctors_ci
  let new_base : List KConstantInfo := ctors_ci.reverse ++ [ciT]
  have hbase_consts : env_base.consts = new_base ++ env.consts := by
    show (Ix.Kernel.consSumCtors p₀.nP w.ctorsA ⟨ciT :: env.consts⟩).consts =
      (ctors_ci.reverse ++ [ciT]) ++ env.consts
    rw [consts_consSumCtors_eq, List.append_assoc]
    rfl
  have hperm : new_base.Perm blockA :=
    (perm_append_singleton ctors_ci.reverse ciT).trans (List.Perm.cons ciT (perm_reverse ctors_ci))
  have hstored_ctors :
      List.Forall₂ IxVM.Consistency.StoredAs ctors_ci
        (p₀.ctors.map (fun c => ConstantInfo.ctorInfo c.1 p₀.nP c.2)) := by
    rw [List.forall₂_iff_get]
    refine ⟨by simp [ctors_ci, w.cload.1], fun j hj₁ hj₂ => ?_⟩
    simp only [List.get_eq_getElem, ctors_ci, List.getElem_map]
    have hj : j < p₀.ctors.length := by simpa [ctors_ci] using hj₂
    obtain ⟨c, cvCa₀, hc, hcA, hvs, _⟩ := w.cload.2 j hj
    rw [List.getElem?_eq_getElem hj] at hc; injection hc with hc_eq
    have hjA : j < w.ctorsA.length := by rwa [w.cload.1]
    rw [List.getElem?_eq_getElem hjA] at hcA; injection hcA with hcA_eq
    rw [hc_eq, hcA_eq]
    exact ⟨hvs, rfl, rfl⟩
  have hstored_block : List.Forall₂ IxVM.Consistency.StoredAs blockA block := by
    rw [hblk]
    exact List.Forall₂.cons ⟨w.valStored_T, trivial⟩ hstored_ctors
  have hnd_block : (block.map (·.name)).Nodup := by
    rw [hblk, List.map_cons, List.map_map]
    exact List.nodup_cons.mpr ⟨w.T_not_in_ctors, w.ctors_nodup⟩
  have hfresh_block : ∀ ci₀ ∈ block, env.find? ci₀.name = none := by
    intro ci₀ hci₀
    rw [hblk] at hci₀
    rcases List.mem_cons.mp hci₀ with rfl | hci₀
    · exact w.fresh_T
    · obtain ⟨c, hc_mem, rfl⟩ := List.mem_map.mp hci₀
      exact w.fresh_ctors c hc_mem
  have henv₂_step :
      env₂ = ⟨new_base ++ env.consts⟩ ∨
      ∃ tbl : Ix.Kernel.ProjTable .anon,
        (⟨new_base ++ env.consts⟩ : Ix.Kernel.Env .anon).find?
          (Ix.Kernel.projTableName tbl.structName) = none ∧
        env₂ = ⟨.projInfo tbl :: new_base ++ env.consts⟩ := by
    have heq_env : env_base = ⟨new_base ++ env.consts⟩ := by
      show ⟨env_base.consts⟩ = (⟨new_base ++ env.consts⟩ : Ix.Kernel.Env .anon)
      rw [hbase_consts]
    rcases henv₂_cases with rfl | ⟨tbl, hfr, hsn, rfl⟩
    · exact Or.inl heq_env
    · refine Or.inr ⟨tbl, ?_, ?_⟩
      · rw [hsn, ← heq_env]
        exact hfr
      · simp [hbase_consts]
  have hinst : IxVM.Consistency.InstallStep env (.indDecl block nP) env₂ :=
    installStep_of_perm_and_optTable hpin hnd_block hfresh_block hstored_block hperm henv₂_step
  exact ⟨env₂, hinst, hNoRecRun⟩

/-- `DeclInv`-preserving wrapper for Deliverable 2 (`nativeNoRec_step`). -/
theorem nativeNoRec_declInv_step (hLevels : IxVM.Consistency.Levels)
    (hCore : IxVM.Consistency.Core S₀)
    {calls : List (Call F)} {env : Ix.Kernel.Env .anon}
    {block : List KConstantInfo} {nP : Nat} {p₀ : Ix.Kernel.NativeParts .anon}
    (hchk : S0.Checked calls env (.indDecl block nP))
    (hpin : Ix.Kernel.basisPinHit block = none)
    (hparts : nativePartsNoRec? nP block = some p₀)
    (extra : NativeNoRecExtra calls env p₀) :
    ∃ env₂,
      IxVM.Consistency.InstallStep env (.indDecl block nP) env₂ ∧
      ∀ (V : Type u) [Ix.Kernel.SetTheory V], DeclInv V env → DeclInv V env₂ := by
  obtain ⟨caps₀, hblk, _⟩ := nativePartsNoRec?_inv hparts
  have hinst_eq : IxVM.Consistency.installs (.indDecl block nP) = block := by
    simp [IxVM.Consistency.installs, hpin]
  have hnd : ((IxVM.Consistency.installs (.indDecl block nP)).map (·.name)).Nodup := by
    rw [hinst_eq, hblk, List.map_cons, List.map_map]
    exact List.nodup_cons.mpr ⟨extra.witness.T_not_in_ctors, extra.witness.ctors_nodup⟩
  have hfresh : ∀ ci₀ ∈ IxVM.Consistency.installs (.indDecl block nP),
      env.find? ci₀.name = none := by
    rw [hinst_eq, hblk]
    intro ci₀ hci₀
    rcases List.mem_cons.mp hci₀ with rfl | hci₀
    · exact extra.witness.fresh_T
    · obtain ⟨c, hc_mem, rfl⟩ := List.mem_map.mp hci₀
      exact extra.witness.fresh_ctors c hc_mem
  refine decls_step_of_store hchk hnd hfresh (fun hS => ?_)
  obtain ⟨env₂, hstep, hrun⟩ := nativeNoRec_step hLevels hCore hpin hparts hS extra
  exact ⟨env₂, hstep, declRunJ_of_nativeNoRec hpin hparts hrun⟩

end IxVM.Refinement.Decl
