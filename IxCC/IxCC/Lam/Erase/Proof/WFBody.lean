import IxCC.Lam.Erase.Proof.WFTerm

/-! # Erased globals are closed and well formed

Every body `BodyR` describes (a δ body or its by-name variant, `r⋆`, a
wrapper) is well formed at depth 0 (`bodyR_wf`), given `WFEnv` and that
its constructor keys have rows. -/

set_option autoImplicit false

namespace IxCC.Lam.Erase.Proof

open IxCC.Src (CId Head Profile Levels)

theorem cxOk_nil (q : Profile) (d : Nat) (minors : List (Nat × List Mode)) :
    CxOk { prof := q, ctx := [], depth := d, minors } := fun _ _ h => by simp at h

theorem ruleCx_ok {q : Profile} {pre depth : Nat} {minors : List (Nat × List Mode)}
    {fields : List (Option Nat)} (hpre : pre ≤ depth) (hf : ∀ l, some l ∈ fields → l < depth) :
    CxOk (ruleCx q pre depth minors fields) := by
  unfold ruleCx
  refine (cxOk_nil q depth minors).under fun l hl => ?_
  rcases List.mem_append.1 hl with hl | hl
  · obtain ⟨i, hi, e⟩ := List.mem_map.1 hl
    cases e
    exact Nat.lt_of_lt_of_le (List.mem_range.1 hi) hpre
  · exact hf l hl

theorem wrapCx_ok (q : Profile) (a : Nat) : CxOk (wrapCx q a) := by
  intro i l hi
  simp only [wrapCx, List.getElem?_map, Option.map_eq_some_iff, Option.some.injEq] at hi
  obtain ⟨l', hl', rfl⟩ := hi
  exact List.mem_range.1 (List.mem_reverse.1 (List.mem_of_getElem? hl'))

theorem recModes_length (I : Input) (r : CId) (q : Profile) (np nmot nmin ni : Nat) :
    (recModes I r q np nmot nmin ni).length = np + nmot + nmin + ni + 1 := by
  simp [recModes]

section

set_option linter.unusedSectionVars false

variable {I : Input} {G : Key.GKey → GlobalId → Prop} {S : Sig} {T : CTab} (E : WFEnv I G S T)
include E

theorem ruleArgsR_wf : ∀ {cx : Cx} {args : List Src.Term.Arg} {args' : List (Term × Mode)},
    RuleArgsR I G cx args args' → CxOk cx → (∀ a ∈ args', RegT T a.1) →
    ∀ a ∈ args', Term.WF S cx.depth a.1
  | _, _, _, .nil, _, _ => fun _ h => by cases h
  | _, _, _, .irr _ hrest, hcx, hr => fun a ha => by
    rcases List.mem_cons.1 ha with e | ha
    · rw [e]; trivial
    · exact ruleArgsR_wf hrest hcx (fun b hb => hr b (List.mem_cons_of_mem _ hb)) a ha
  | _, _, _, .name _ ht hrest, hcx, hr => fun a ha => by
    rcases List.mem_cons.1 ha with e | ha
    · rw [e]; exact tr_wf E ht hcx (hr _ List.mem_cons_self)
    · exact ruleArgsR_wf hrest hcx (fun b hb => hr b (List.mem_cons_of_mem _ hb)) a ha
  | _, _, _, .strict _ ht hrest, hcx, hr => fun a ha => by
    rcases List.mem_cons.1 ha with e | ha
    · rw [e]; exact tr_wf E ht hcx (hr _ List.mem_cons_self)
    · exact ruleArgsR_wf hrest hcx (fun b hb => hr b (List.mem_cons_of_mem _ hb)) a ha

theorem ruleBodyR_wf {r : CId} {q : Profile} {pre depth : Nat}
    {minors : List (Nat × List Mode)} {rule : Src.Rule} {fields : List (Option Nat)} {t : Term}
    (h : RuleBodyR I G r q pre depth minors rule fields t) (hpre : pre ≤ depth)
    (hf : ∀ l, some l ∈ fields → l < depth) (hr : RegT T t) : Term.WF S depth t := by
  have hcx := ruleCx_ok (q := q) (minors := minors) hpre hf
  cases h with
  | var _ _ _ hh hargs _ =>
    obtain ⟨hrh, hra⟩ := RegT.apps_inv hr
    exact wf_apps (tr_wf E hh hcx hrh) (ruleArgsR_wf E hargs hcx hra)
  | other _ _ _ ht => exact tr_wf E ht hcx hr

theorem recAltsR_wf {r : CId} {q : Profile} {pre arity : Nat} {minors : List (Nat × List Mode)}
    {ind : CId} (hpre : pre ≤ arity) :
    ∀ {j : Nat} {rules : List Src.Rule} {alts : List Alt},
      RecAltsR I G r q pre arity minors ind j rules alts → (∀ a ∈ alts, AltReg T a) →
      Term.WFAlts S arity alts ∧ (Term.altKeys alts).Nodup ∧ KeysFrom I ind j (Term.altKeys alts)
  | _, _, _, .nil, _ => ⟨trivial, List.nodup_nil, fun _ h => by cases h⟩
  | j, _, _, .cons hra hb hrest, hr => by
    obtain ⟨k, n, b, e, hk, hrb⟩ := hr _ List.mem_cons_self
    cases e
    obtain ⟨ha, hfl, c, sf, lv, np, nf, ty, rfl, hd⟩ := ruleAlt_wf E hra hk
    obtain ⟨h₁, h₂, h₃⟩ := recAltsR_wf hpre hrest fun a ha => hr a (List.mem_cons_of_mem _ ha)
    refine ⟨⟨ha, ruleBodyR_wf E hb (Nat.le_trans hpre (Nat.le_add_right _ _)) hfl hrb, h₁⟩, ?_, ?_⟩
    · refine List.nodup_cons.2 ⟨fun hmem => ?_, h₂⟩
      obtain ⟨c', sf', lv', cidx', np', nf', ty', hk', hd', hle⟩ := h₃ _ hmem
      have := ctorKey_cidx E.wf hd hd' hk'
      omega
    · intro k' hk'
      rcases List.mem_cons.1 hk' with e | hk'
      · rw [e]; exact ⟨c, sf, lv, j, np, nf, ty, rfl, hd, Nat.le_refl _⟩
      · obtain ⟨c', sf', lv', cidx', np', nf', ty', e, hd', hle⟩ := h₃ k' hk'
        exact ⟨c', sf', lv', cidx', np', nf', ty', e, hd', by omega⟩

theorem RegT.case_alts {s : Term} {alts : List Alt} {d : Option Term}
    (h : RegT T (.case s alts d)) : ∀ a ∈ alts, AltReg T a := by
  cases h with
  | case _ hk hb _ =>
    intro a ha
    cases a with
    | mk k n b => exact ⟨k, n, b, rfl, hk k n b ha, hb k n b ha⟩

theorem recStarR_wf {r : CId} {q : Profile} {t : Term} (h : RecStarR I G r q t) (hr : RegT T t) :
    Term.WF S 0 t := by
  cases h with
  | empty hd _ =>
    exact wf_lams trivial
  | @sub sf k lv np nmot nmin ni ind rules ty w srcs rule body hd hk _ hb =>
    refine wf_lams ?_
    rw [Nat.zero_add, recModes_length]
    refine ruleBodyR_wf E hb (by omega) (fun l hl => ?_) (RegT.lams_inv hr)
    obtain ⟨src, hsrc, e⟩ := List.mem_map.1 hl
    cases src with
    | proof => cases e
    | index i =>
      cases e
      have hkind : I.recKind.get? r = some (.subsingleton w srcs) := by
        unfold Input.kindAt at hk
        cases hg : I.recKind.get? r with
        | none => rw [hg] at hk; cases hk
        | some k =>
          rw [hg] at hk
          cases k with
          | subsingleton w' fs =>
            simp only [Option.map_some, Src.RecKind.atProfile] at hk
            split at hk
            · cases hk; rfl
            · cases hk
          | ordinary => cases hk
          | empty => cases hk
      have := E.wf.recKindIdx hd hkind i hsrc
      omega
  | ord hd _ _ halts =>
    refine wf_lams ?_
    rw [Nat.zero_add, recModes_length]
    have hrb := RegT.lams_inv hr
    obtain ⟨h₁, h₂, _⟩ := recAltsR_wf E (by omega) halts (RegT.case_alts E hrb)
    exact ⟨show 0 < _ by omega, h₁, h₂, trivial⟩

theorem wrapR_wf {h : Head} {q : Profile} {t : Term} (hw : WrapR I G h q t) (hr : RegT T t) :
    Term.WF S 0 t := by
  cases hw with
  | prim e =>
    subst e
    refine wf_lams ?_
    rw [Nat.zero_add, List.length_replicate]
    refine ⟨by simp [headArity, prim_arity], (wfList_iff).2 fun a ha => ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
    exact wf_lvl (cx := wrapCx q _) (List.mem_range.1 hi)
  | other _ _ hs =>
    refine wf_lams ?_
    rw [Nat.zero_add, List.length_replicate]
    exact satR_wf E hs (wrapCx_ok q _) (by simp) (RegT.lams_inv hr)

/-- **Every erased body is closed and well formed.** -/
theorem bodyR_wf {key : Key.GKey} {t : Term} (h : BodyR I G key t) (hr : RegT T t) :
    Term.WF S 0 t := by
  cases h with
  | const _ ht => exact tr_wf E ht (cxOk_nil _ 0 []) hr
  | byName _ _ _ ht hs =>
    exact wf_setModes hs (tr_wf E ht (cxOk_nil _ 0 []) (RegT.setModes_inv hs hr))
  | recStar h => exact recStarR_wf E h hr
  | wrapper h => exact wrapR_wf E h hr

end

end IxCC.Lam.Erase.Proof
