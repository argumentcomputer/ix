import IxCC.Lam.Erase.Proof.WFBody
import IxCC.Lam.Erase.Proof.RegBody
import IxCC.Lam.Erase.Proof.Build
import IxCC.Lam.Proof.Program

/-! # Erasure's output is well formed: `erase_wellFormed`

A successful erasure ends in one state (`erase_spec_run` and `erase_reg`
describe the same run). Its key table gives each id below `next` one key,
each key one id, and each id an erased global with a `BodyR` body; its
constructor table lists each row once, keyed by its constructor, with the
kept-field count of a constructor aliased to it. So every global is present
and well formed (`bodyR_wf`), global and constructor keys are distinct,
roots are in range, and the pinned keys have the arities `Nat` peeling and
Boolean primitives need. -/

set_option autoImplicit false

namespace IxCC.Lam.Erase.Proof

open IxCC.Src (CId Head Profile Levels)

/-! ## The constructor table -/

section Table

variable {I : Input} {s : St} (hinv : CtorInv I s)
include hinv

theorem ctors_keys :
    (s.ctorOrder.reverse.filterMap s.ctors.get?).map (·.key) =
      s.ctorOrder.reverse.map Key.CtorKey.src := by
  have : ∀ l : List CId, (∀ c ∈ l, c ∈ s.ctorOrder) →
      (l.filterMap s.ctors.get?).map (·.key) = l.map Key.CtorKey.src := by
    intro l hl
    induction l with
    | nil => rfl
    | cons c l ih =>
      have hc := (hinv.order c).1 (hl c List.mem_cons_self)
      obtain ⟨info, hi⟩ := Option.isSome_iff_exists.1 hc
      rw [List.filterMap_cons, hi]
      simp only [List.map_cons, (hinv.rows c info hi).1]
      rw [ih fun d hd => hl d (List.mem_cons_of_mem _ hd)]
  exact this _ fun c hc => List.mem_reverse.1 hc

theorem ctors_keys_nodup : ((s.ctorOrder.reverse.filterMap s.ctors.get?).map (·.key)).Nodup := by
  rw [ctors_keys hinv]
  exact List.pairwise_map.2 ((List.pairwise_reverse.2 (hinv.nodup.imp Ne.symm)).imp
    fun h e => h (by injection e))

omit hinv in
theorem find?_key {l : List CtorInfo} (hn : (l.map (·.key)).Nodup) {x : CtorInfo} (hx : x ∈ l) :
    l.find? (·.key == x.key) = some x := by
  induction l with
  | nil => cases hx
  | cons y ys ih =>
    rw [List.map_cons, List.nodup_cons] at hn
    by_cases hy : y.key = x.key
    · rw [List.find?_cons_of_pos (by simp [hy])]
      rcases List.mem_cons.1 hx with rfl | hx
      · rfl
      · exact absurd (hy ▸ List.mem_map_of_mem hx) hn.1
    · rw [List.find?_cons_of_neg (by simp [hy])]
      rcases List.mem_cons.1 hx with rfl | hx
      · exact absurd rfl hy
      · exact ih hn.2 hx

/-- The program's arity of a registered key is its row's. -/
theorem sig_arity {L : Program} (hc : L.ctors = s.ctorOrder.reverse.filterMap s.ctors.get?)
    {k : Key.CtorKey} {n : Nat} (h : tabOf s k n) : L.sig.arity? k = some n := by
  obtain ⟨c, info, hi, rfl, rfl⟩ := h
  have hkey := (hinv.rows c info hi).1
  have hmem : info ∈ L.ctors := by
    rw [hc]
    refine List.mem_filterMap.2 ⟨c, List.mem_reverse.2 ((hinv.order c).2 (by rw [hi]; rfl)), hi⟩
  have := find?_key (by rw [hc]; exact ctors_keys_nodup hinv) hmem
  rw [hkey] at this
  simp only [Program.sig, Program.ctor?, this, Option.map_some]

/-- Conversely, a key with an arity is a row of its constructor's shape. -/
theorem sig_arity_row {L : Program} (hc : L.ctors = s.ctorOrder.reverse.filterMap s.ctors.get?)
    {k : Key.CtorKey} {n : Nat} (h : L.sig.arity? k = some n) :
    ∃ c, k = .src c ∧ RowShape I c n := by
  simp only [Program.sig, Program.ctor?, Option.map_eq_some_iff] at h
  obtain ⟨info, hf, rfl⟩ := h
  have hmem := List.mem_of_find?_eq_some hf
  have hk := List.find?_some hf
  rw [hc] at hmem
  obtain ⟨c, _, hi⟩ := List.mem_filterMap.1 hmem
  obtain ⟨hkey, hrow⟩ := hinv.rows c info hi
  refine ⟨c, ?_, hrow⟩
  rw [← hkey]
  exact (beq_iff_eq.1 hk).symm

end Table

/-! ## Well-formedness -/

theorem forall2_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, Forall2 R xs ys → ∀ y ∈ ys, ∃ x ∈ xs, R x y
  | _, _, .nil => fun _ h => by cases h
  | _, _, .cons hab h => fun y hy => by
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨x, hx, hr⟩ := forall2_mem_right h y hy
      exact ⟨x, List.mem_cons_of_mem _ hx, hr⟩

/-- **Erasure's output is well formed.** -/
theorem erase_wellFormed {p : Src.Program} {ch : Src.Relevance.Checked} {L : Program}
    {st : Erase.Stats} (h : erase p ch = .ok (L, st)) : Lam.WellFormed L := by
  have wf := erase_progWF h
  obtain ⟨s, hrun, hids, hprog, hknown, hsucc, hroots⟩ := erase_spec_run h
  obtain ⟨s', hrun', hglob, hsize, hctors, hinv, hsurj, hreg, -⟩ := erase_reg h
  rw [hrun] at hrun'
  injection hrun' with hrun'
  injection hrun' with _ hss
  subst hss
  -- The environment of the term proof.
  have E : WFEnv (Input.ofProgram p ch) (fun key g => keyOf s key = some g) L.sig (tabOf s) :=
    { wf
      glob := fun key g hk => by
        show g < L.size
        rw [hsize]
        exact hids.1 key g hk
      arity := fun k n hk => sig_arity hinv hctors hk
      shape := fun k n ⟨c, info, hi, hk, hn⟩ => ⟨c, hk, hn ▸ (hinv.rows c info hi).2⟩ }
  -- Each global's key.
  have hkeyOf : ∀ g gl, g < L.size → L.global? g = some gl → keyOf s gl.key = some g := by
    intro g gl hg hgl
    obtain ⟨key, hk⟩ := hsurj g (hsize ▸ hg)
    obtain ⟨gl', hgl', hkey, _⟩ := hprog key g hk
    rw [hgl] at hgl'
    cases hgl'
    rw [hkey]
    exact hk
  refine ⟨fun g hg => ?_, ?_, ?_, fun r hr => ?_, ?_⟩
  · obtain ⟨key, hk⟩ := hsurj g (hsize ▸ hg)
    obtain ⟨gl, hgl, _, hB⟩ := hprog key g hk
    exact ⟨gl, hgl, bodyR_wf E hB (hreg g gl hgl)⟩
  · refine List.pairwise_map.2 ((Program.globalList_pairwise L).imp_of_mem
      fun {x y} hx hy hlt e => ?_)
    obtain ⟨g, gl⟩ := x
    obtain ⟨g', gl'⟩ := y
    obtain ⟨hg, hgl⟩ := Program.mem_globalList.1 hx
    obtain ⟨hg', hgl'⟩ := Program.mem_globalList.1 hy
    have h₁ := hkeyOf g gl hg hgl
    have h₂ := hkeyOf g' gl' hg' hgl'
    dsimp only at e hlt
    rw [e, h₂] at h₁
    cases h₁
    exact Nat.lt_irrefl _ hlt
  · rw [hctors]
    exact ctors_keys_nodup hinv
  · obtain ⟨c, _, hrr⟩ := forall2_mem_right hroots r hr
    rw [hsize]
    cases hrr with
    | const _ hk => exact hids.1 _ _ hk
    | wrapper _ hk => exact hids.1 _ _ hk
  · -- The pinned keys: a row keyed by a constructor has its kept-field count.
    have row : ∀ {k : Key.CtorKey} {m : Nat} {c : CId} {sf : Bool} {lv : Nat} {ind : CId}
        {cidx np nf : Nat} {ty : Src.Term},
        (Input.ofProgram p ch).decl? c = some (.ctor sf lv ind cidx np nf ty) →
        k = .src ((Input.ofProgram p ch).alias c) → L.sig.arity? k = some m →
        m = (Input.ofProgram p ch).keptCount c [] nf := by
      intro k m c sf lv ind cidx np nf ty hc hk ha
      obtain ⟨c', hk', c₀, sf₀, lv₀, ind₀, cidx₀, np₀, nf₀, ty₀, hd₀, ha₀, hm⟩ :=
        sig_arity_row hinv hctors ha
      rw [hk] at hk'
      injection hk' with hk'
      rw [hm]
      exact keptCount_alias_eq wf hd₀ hc (ha₀.trans hk'.symm)
    -- A pinned `Bool` constructor is its own key.
    have boolSelf : ∀ {b : CId}, ((Input.ofProgram p ch).known.boolFalse = some b ∨
        (Input.ofProgram p ch).known.boolTrue = some b) →
        (Input.ofProgram p ch).alias b = b := by
      intro b hb
      have hdb : ∃ sf lv B cidx np ty, (Input.ofProgram p ch).decl? b =
          some (.ctor sf lv B cidx np 0 ty) := by
        rcases hb with hb | hb
        · obtain ⟨sf, lv, B, np, ty, h, _⟩ := wf.boolFalse hb
          exact ⟨sf, lv, B, 0, np, ty, h⟩
        · obtain ⟨sf, lv, B, np, ty, h, _⟩ := wf.boolTrue hb
          exact ⟨sf, lv, B, 1, np, ty, h⟩
      obtain ⟨sf, lv, B, cidx, np, ty, hdb⟩ := hdb
      have hne : ∀ d, ((Input.ofProgram p ch).known.decIsFalse = some d ∨
          (Input.ofProgram p ch).known.decIsTrue = some d) → d ≠ b := by
        intro d hd e
        subst e
        exact wf.decOther hd (hb.elim .inl fun h => .inr (.inl h)) hdb hdb rfl
      exact alias_of_notDec (fun d h => hne d (.inl h)) (fun d h => hne d (.inr h))
    rw [hknown]
    unfold Known.consistent
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · split
      · next k hk =>
        cases ha : L.sig.arity? k with
        | none => rfl
        | some m =>
          simp only [Option.all_some, beq_iff_eq]
          simp only [Input.lamKnown, Option.map_eq_some_iff, Function.comp_apply] at hk
          obtain ⟨Z, hZ, rfl⟩ := hk
          obtain ⟨sf, lv, N, cidx, ty, hdZ⟩ := wf.zeroPin hZ
          exact row hdZ rfl ha
      · rfl
    · split
      · next k hk =>
        cases ha : L.sig.arity? k with
        | none => rfl
        | some m =>
          simp only [Option.all_some, beq_iff_eq]
          simp only [Input.lamKnown, Option.map_eq_some_iff, Function.comp_apply] at hk
          obtain ⟨S', hS, rfl⟩ := hk
          obtain ⟨sf, lv, N, cidx, ty, hdS⟩ := wf.succPin hS
          rw [row hdS rfl ha]
          show (Input.ofProgram p ch).rank S' [] 1 = 1
          rw [rank_succ, hsucc S' hS]
          rfl
      · rfl
    · split
      · next k hk =>
        cases ha : L.sig.arity? k with
        | none => rfl
        | some m =>
          simp only [Option.all_some, beq_iff_eq]
          simp only [Input.lamKnown, Option.map_eq_some_iff] at hk
          obtain ⟨b, hb, rfl⟩ := hk
          obtain ⟨sf, lv, B, np, ty, hdb, _⟩ := wf.boolFalse hb
          exact row hdb (by rw [boolSelf (.inl hb)]) ha
      · rfl
    · split
      · next k hk =>
        cases ha : L.sig.arity? k with
        | none => rfl
        | some m =>
          simp only [Option.all_some, beq_iff_eq]
          simp only [Input.lamKnown, Option.map_eq_some_iff] at hk
          obtain ⟨b, hb, rfl⟩ := hk
          obtain ⟨sf, lv, B, np, ty, hdb, _⟩ := wf.boolTrue hb
          exact row hdb (by rw [boolSelf (.inr hb)]) ha
      · rfl

end IxCC.Lam.Erase.Proof
