import IxCC.Own.Plain.Proof.Owned.Joins

/-! # `reset`, `reuse`, and `dropSlot` steps

- `reset_step`: checks constructor metadata, static uniqueness (when `uniq = true`), and projected
  field promotions; handles all three runtime branches of `evalResetMask` (unique in-place shell
  reset + dead-field `dropAll`, shared fallback `incList` + scrutinee `dropAll`, and non-`.loc`
  empty-mask no-op).
- `reuse_step`: consumes a live reset slot and constructor arguments, executing either `reuseCell`
  on a `.loc` shell (using `ReachablePreserved.reuseCell_den` — no `HeapOk` needed!) or fresh
  `Heap.alloc .rc` on `.erased` (only when `uniq = false`), binding a fresh statically unique
  variable.
- `dropSlot_step`: releases a live reset slot via `dropAll` and advances the borrow epoch. -/

set_option autoImplicit false

namespace IxCC.Own.Plain

open Rc
open IxCC.Sem (Result)
open IxCC.Fir (Var Arg)

section

variable {functions : Signatures} {H : Heap} {external : Nat → Nat} {live : List Var}
  {Γ : Ctx} {ρf : Fir.Env} {ρo : Own.Env} {owned : List RVal} {lex : Joins} {Δ : JCtx}
  {Jf : List Fir.JEntry} {Jo : List JEntry} {borrows : BorrowSigs} {uniqs : UniqSigs}
  {retUniq : Bool} {ctors : List Lam.CtorInfo} {K : Lam.Known} {priv : Nat → Prop}
  {slots : Src.NatMap RVal} {slotVals : List RVal}

/-! ## Bitmask and field-partition lemmas -/

theorem fieldsMask_testBit : ∀ (fields : List (Option Var)) (j : Nat),
    Nat.testBit (fieldsMask fields) j =
      match fields[j]? with
      | some (some _) => true
      | _ => false
  | [], j => by simp [fieldsMask]
  | none :: rest, 0 => by simp [fieldsMask]
  | some _ :: rest, 0 => by simp [fieldsMask]
  | none :: rest, j + 1 => by
    simp only [fieldsMask, List.getElem?_cons_succ]
    rw [Nat.testBit_succ, show 2 * fieldsMask rest / 2 = fieldsMask rest by omega]
    exact fieldsMask_testBit rest j
  | some _ :: rest, j + 1 => by
    simp only [fieldsMask, List.getElem?_cons_succ]
    rw [Nat.testBit_succ, show (1 + 2 * fieldsMask rest) / 2 = fieldsMask rest by omega]
    exact fieldsMask_testBit rest j

theorem refsIn_zipIdx_partition (mask : Nat) :
    ∀ (fs : List RVal) (offset : Nat) (k : Nat),
      refsIn k ((fs.zipIdx offset).filterMap fun (u, j) => if Nat.testBit mask j then some u else none) +
      refsIn k ((fs.zipIdx offset).filterMap fun (u, j) => if !Nat.testBit mask j then some u else none) =
      refsIn k fs
  | [], _, _ => by simp [refsIn]
  | u :: us, offset, k => by
    have ih := refsIn_zipIdx_partition mask us (offset + 1) k
    simp only [List.zipIdx_cons, List.filterMap_cons]
    dsimp only at ih ⊢
    cases hbit : Nat.testBit mask offset
    · simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte, refsIn]; omega
    · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, refsIn]; omega

private theorem get?_erase_ne {α : Type} (m : Src.NatMap α) (k k' : Nat) (h : k' ≠ k) :
    (m.erase k).get? k' = m.get? k' := by
  simp [Src.NatMap.get?_erase, h]

private theorem takeArgs_noPriv_reset {Γ Γ₁ : Ctx} {args : List Arg} {vs : List RVal}
    (hpriv : ∀ l, priv l → ∀ x, Γ.avail x = true → ρo.get? x ≠ some (.loc l))
    (hev : Own.evalArgs ρo args = some vs) (ht : Γ.takeArgs args = .ok Γ₁) :
    ∀ l, priv l → ∀ v, v ∈ vs → v ≠ .loc l := by
  induction args generalizing Γ vs with
  | nil => intro _ _ _ hv; simp [Own.evalArgs] at hev; subst hev; cases hv
  | cons a as ih =>
    cases ha : Own.evalArg ρo a with
    | none => simp [Own.evalArgs, ha] at hev
    | some v0 =>
      cases has : Own.evalArgs ρo as with
      | none => simp [Own.evalArgs, ha, has] at hev
      | some vs' =>
        have : v0 :: vs' = vs := by simpa [Own.evalArgs, ha, has] using hev
        subst this
        simp only [Ctx.takeArgs] at ht
        cases hta : Γ.takeArg a with
        | error _ => rw [hta] at ht; cases ht
        | ok Γm =>
          rw [hta] at ht
          have hwm := Ctx.takeArg_weaker hta
          intro l hl v hm
          rcases List.mem_cons.mp hm with rfl | hm
          · cases a with
            | lit _ | erased => simp [Own.evalArg] at ha; subst ha; intro h; cases h
            | var y =>
              have havy : Γ.avail y = true := by
                rcases Ctx.take_ok hta with ⟨hi, _⟩ | ⟨_, n, hn, _⟩
                · simp [Ctx.avail_eq, hi]
                · simp [Ctx.avail_eq, Ctx.tokens_eq, hn]
              intro hEq; subst hEq; exact hpriv l hl y havy ha
          · exact ih (fun l' hl' x hx => hpriv l' hl' x (hwm.avail hx)) has ht l hl v hm

theorem zipIdx_filterMap_mem_fst (p : Nat → Bool) :
    ∀ {fs : List RVal} {offset : Nat} {v : RVal},
      v ∈ (fs.zipIdx offset).filterMap (fun (u, j) => if p j then some u else none) → v ∈ fs
  | [], _, _, h => by simp at h
  | u :: us, offset, v, h => by
    simp only [List.zipIdx_cons, List.filterMap_cons] at h
    cases hb : p offset
    · simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
      exact List.mem_cons_of_mem _ (zipIdx_filterMap_mem_fst p h)
    · simp only [hb, ↓reduceIte, List.mem_cons] at h
      rcases h with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (zipIdx_filterMap_mem_fst p hm)

theorem zipIdx_filterMap_nil_of_false (mask : Nat) :
    ∀ {fs : List RVal} {offset : Nat},
      (∀ j, offset ≤ j → Nat.testBit mask j = false) →
      (fs.zipIdx offset).filterMap (fun (u, j) => if Nat.testBit mask j then some u else none) = []
  | [], _, _ => rfl
  | _ :: us, offset, hf => by
    simp only [List.zipIdx_cons, List.filterMap_cons, hf offset (Nat.le_refl _),
      Bool.false_eq_true, ↓reduceIte]
    exact zipIdx_filterMap_nil_of_false mask (fun j hj => hf j (by omega))

theorem refsIn_replicate_erased (n k : Nat) : refsIn k (List.replicate n RVal.erased) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, refsIn, ih]

theorem validReuseCtor_props {c : Fir.CtorInfo} {cls : Nat}
    (h : Ctx.validReuseCtor c = some cls) :
    0 < c.arity ∧ c.fieldless = false := by
  unfold Ctx.validReuseCtor at h
  split at h
  · rename_i hcond
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    have hpos : 0 < c.arity := hcond.1.1.1.1
    exact ⟨hpos, by simp [Fir.CtorInfo.fieldless]; omega⟩
  · cases h

/-! ## `incList` soundness -/

theorem incList_sound {H : Heap} {external : Nat → Nat} {roots : List RVal}
    {P : Nat → Prop} :
    ∀ (vs : List RVal),
      Balance H external roots →
      (∀ u, u ∈ vs → BorrowVal H u) →
      (∀ l, P l → edgeCount H l = 0) →
      (∀ l, P l → refsIn l vs = 0) →
      ∃ H', incList H vs = some H' ∧
        Balance H' external (vs ++ roots) ∧
        (∀ ext, ReachablePreserved H H' ext) ∧
        (∀ k, edgeCount H' k = edgeCount H k) ∧
        PrivPreserved H H' P
  | [], hb, _, hpe, _ =>
    ⟨H, rfl, hb, fun ext => ReachablePreserved.refl H ext, fun _ => rfl, PrivPreserved.refl hpe⟩
  | u :: us, hb, hbrw, hpe, hpv => by
    have hbu : BorrowVal H u := hbrw u List.mem_cons_self
    obtain ⟨H₁, hi, hb₁, _⟩ := inc_root hb (hbu.canDup hb)
    have hedge₁ : ∀ k, edgeCount H₁ k = edgeCount H k := inc_edgeCount hi
    have hne : ∀ l, P l → u ≠ .loc l := fun l hl hEq => by
      have h0 := hpv l hl
      subst hEq; simp [refsIn] at h0
    have hpriv₁ : PrivPreserved H H₁ P := PrivPreserved.inc hpe hne hi
    have hus_brw : ∀ z, z ∈ us → BorrowVal H₁ z := fun z hz =>
      (hbrw z (List.mem_cons_of_mem _ hz)).inc hi
    have hus_priv : ∀ l, P l → refsIn l us = 0 := fun l hl => by
      have h0 := hpv l hl; simp only [refsIn] at h0; omega
    obtain ⟨H₂, hinc, hb₂, hrp₂, hedge₂, hpriv₂⟩ :=
      incList_sound us hb₁ hus_brw (fun l hl => by rw [hedge₁]; exact hpe l hl) hus_priv
    refine ⟨H₂, by simp only [incList, hi]; exact hinc, ?_, ?_, ?_,
      hpriv₁.trans hpriv₂⟩
    · refine (SameRefs.balance ?_ hb₂)
      intro k; simp only [List.cons_append, refsIn_append, refsIn]; omega
    · intro ext
      exact (ReachablePreserved.inc hi).trans (hrp₂ ext)
    · intro k; rw [hedge₂ k, hedge₁ k]

/-! ## `promoteResetFields` soundness -/

private theorem promoteResetFields_sound
    {Γ0 : Ctx} {x : Var} {key : Key.CtorKey} {bfields : List RVal}
    (hproj : ∀ v j, Γ0.projOf.get? v = some (x, key, j) → Γ0.avail v = true →
      ∃ uv, bfields[j]? = some uv ∧ ρo.get? v = some uv)
    (himm0 : ∀ v, Γ0.isImm v = true → ∃ uv, ρo.get? v = some uv ∧ ImmVal uv)
    (hknown0 : ∀ v, Γ0.avail v = true → v ∈ live) :
    ∀ (idx : Nat) (fields : List (Option Var)) (Γc Γ₂ : Ctx) (toks : List Var) (vals : List RVal),
      (∀ y, Γc.isImm y = Γ0.isImm y) →
      (∀ y, Γc.avail y = true → Γ0.avail y = true) →
      (∀ y, Γc.known y = true → y ∈ live) →
      (∀ y e, Γc.brw.get? y = some e → e ≤ Γc.epoch) →
      Ctx.Tokens Γc toks →
      EnvRoots ρo toks vals →
      Ctx.promoteResetFields Γ0 x key idx fields Γc = .ok Γ₂ →
      ∃ promToks promVals,
        Ctx.Tokens Γ₂ (promToks ++ toks) ∧
        EnvRoots ρo (promToks ++ toks) (promVals ++ vals) ∧
        (∀ y, Γ₂.isImm y = Γc.isImm y) ∧
        Γ₂.pbrw = Γc.pbrw ∧
        Γ₂.epoch = Γc.epoch ∧
        Γ₂.ctorOf = Γc.ctorOf ∧
        Γ₂.projOf = Γc.projOf ∧
        Γ₂.rset = Γc.rset ∧
        (∀ y e, Γ₂.brw.get? y = some e → e ≤ Γ₂.epoch) ∧
        (∀ y, Γ₂.avail y = true → Γ0.avail y = true) ∧
        (∀ y, Γ₂.known y = true → y ∈ live) ∧
        (∀ y, Γ₂.isUniq y = true → Γc.isUniq y = true ∧
          (Γc.isImm y = false → Γ₂.tokens y = Γc.tokens y)) ∧
        (∀ u, u ∈ promVals → u ∈ bfields) ∧
        (∀ k, refsIn k promVals =
          refsIn k (((bfields.drop idx).zipIdx idx).filterMap fun (u, j) =>
            if match fields[j - idx]? with | some (some _) => true | _ => false then some u else none))
  | idx, [], Γc, Γ₂, toks, vals, _, hav0, hkn0, hep0, htok, hroots, hprom => by
    simp only [Ctx.promoteResetFields, Except.ok.injEq] at hprom
    subst hprom
    refine ⟨[], [], htok, hroots, fun _ => rfl, rfl, rfl, rfl, rfl, rfl, hep0, hav0, hkn0,
      fun _ hu => ⟨hu, fun _ => rfl⟩, (fun _ h => by cases h), fun k => ?_⟩
    have hnil : ∀ (fs : List RVal) (off : Nat),
        (fs.zipIdx off).filterMap (fun (u, j) =>
          if (match ([] : List (Option Var))[j - idx]? with | some (some _) => true | _ => false)
          then some u else none) = [] := by
      intro fs; induction fs with
      | nil => intro _; rfl
      | cons _ us ih => intro off; simp only [List.zipIdx_cons, List.filterMap_cons, List.getElem?_nil]; exact ih _
    rw [hnil]
  | idx, none :: rest, Γc, Γ₂, toks, vals, himmC, hav0, hkn0, hep0, htok, hroots, hprom => by
    simp only [Ctx.promoteResetFields] at hprom
    obtain ⟨pt, pv, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ :=
      promoteResetFields_sound hproj himm0 hknown0 (idx + 1) rest Γc Γ₂ toks vals
        himmC hav0 hkn0 hep0 htok hroots hprom
    refine ⟨pt, pv, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, fun k => ?_⟩
    rw [h14 k]
    cases hdrop : bfields.drop idx with
    | nil =>
      have hdrop1 : bfields.drop (idx + 1) = [] := by
        rw [List.drop_eq_nil_iff] at hdrop ⊢; omega
      rw [hdrop1]; simp
    | cons u us =>
      have hdrop1 : bfields.drop (idx + 1) = us := by
        have h' := List.drop_add_one_eq_tail_drop (l := bfields) (i := idx)
        rw [hdrop] at h'; simpa using h'
      rw [hdrop1, List.zipIdx_cons, List.filterMap_cons]
      have h0 : idx - idx = 0 := Nat.sub_self idx
      simp only [h0, List.getElem?_cons_zero, Bool.false_eq_true, ↓reduceIte]
      congr 1
      have hfm : ∀ (ls : List RVal) (off : Nat), idx + 1 ≤ off →
          (ls.zipIdx off).filterMap (fun (u, j) =>
            if match rest[j - (idx + 1)]? with | some (some _) => true | _ => false then some u else none) =
          (ls.zipIdx off).filterMap (fun (u, j) =>
            if match (none :: rest)[j - idx]? with | some (some _) => true | _ => false then some u else none) := by
        intro ls
        induction ls with
        | nil => intro _ _; rfl
        | cons z zs ih =>
          intro off hoff
          simp only [List.zipIdx_cons, List.filterMap_cons]
          have hsub : off - idx = (off - (idx + 1)) + 1 := by omega
          rw [hsub, List.getElem?_cons_succ, ih (off + 1) (by omega)]
      rw [hfm us (idx + 1) (Nat.le_refl _)]
  | idx, some v :: rest, Γc, Γ₂, toks, vals, himmC, hav0, hkn0, hep0, htok, hroots, hprom => by
    simp only [Ctx.promoteResetFields] at hprom
    by_cases hvx : (v == x) = true
    · simp only [hvx, ↓reduceIte] at hprom; cases hprom
    · simp only [hvx, Bool.false_eq_true, ↓reduceIte] at hprom
      cases hpv : (Γ0.projOf.get? v == some (x, key, idx)) with
      | false => simp only [hpv, Bool.false_eq_true, ↓reduceIte] at hprom; cases hprom
      | true =>
        simp only [hpv, ↓reduceIte] at hprom
        have hpv' : Γ0.projOf.get? v = some (x, key, idx) := beq_iff_eq.mp hpv
        cases havv : Γ0.avail v with
        | false => simp only [havv, Bool.false_eq_true, ↓reduceIte] at hprom; cases hprom
        | true =>
          simp only [havv, ↓reduceIte] at hprom
          obtain ⟨uv, hget, huv⟩ := hproj v idx hpv' havv
          have hdrop : bfields.drop idx = uv :: bfields.drop (idx + 1) := by
            have hlt : idx < bfields.length := by
              cases hlt' : Nat.decLt idx bfields.length with
              | isTrue h => exact h
              | isFalse h => rw [List.getElem?_eq_none (Nat.le_of_not_lt h)] at hget; cases hget
            have hcons := List.drop_eq_getElem_cons hlt
            have hget' : bfields[idx] = uv := by
              rw [List.getElem?_eq_getElem hlt] at hget; exact Option.some.inj hget
            rw [hget'] at hcons; exact hcons
          have hfm_tail : ∀ (ls : List RVal) (off : Nat), idx + 1 ≤ off →
              (ls.zipIdx off).filterMap (fun (u, j) =>
                if match rest[j - (idx + 1)]? with | some (some _) => true | _ => false then some u else none) =
              (ls.zipIdx off).filterMap (fun (u, j) =>
                if match (some v :: rest)[j - idx]? with | some (some _) => true | _ => false then some u else none) := by
            intro ls
            induction ls with
            | nil => intro _ _; rfl
            | cons z zs ih =>
              intro off hoff
              simp only [List.zipIdx_cons, List.filterMap_cons]
              have hsub : off - idx = (off - (idx + 1)) + 1 := by omega
              rw [hsub, List.getElem?_cons_succ, ih (off + 1) (by omega)]
          cases hiv : Γc.isImm v with
          | true =>
            simp only [hiv, ↓reduceIte] at hprom
            obtain ⟨uv', huv', himmu⟩ := himm0 v (by rw [← himmC v]; exact hiv)
            have : uv' = uv := Option.some.inj (huv'.symm.trans huv); subst this
            obtain ⟨pt, pv, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ :=
              promoteResetFields_sound hproj himm0 hknown0 (idx + 1) rest Γc Γ₂ toks vals
                himmC hav0 hkn0 hep0 htok hroots hprom
            refine ⟨pt, pv, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, fun k => ?_⟩
            rw [h14 k, hdrop, List.zipIdx_cons, List.filterMap_cons]
            have h0 : idx - idx = 0 := Nat.sub_self idx
            simp only [h0, List.getElem?_cons_zero, ↓reduceIte]
            rw [← hfm_tail (bfields.drop (idx + 1)) (idx + 1) (Nat.le_refl _)]
            simp only [refsIn, show uv' ≠ .loc k from himmu k, ↓reduceIte, Nat.zero_add]
          | false =>
            simp only [hiv, Bool.false_eq_true, ↓reduceIte] at hprom
            let Γm : Ctx := ({ Γc with brw := Γc.brw.erase v, uniq := Γc.uniq.erase v }.addOwn v 1)
            have htokM : Ctx.Tokens Γm (v :: toks) :=
              (htok.same (Γ' := { Γc with brw := Γc.brw.erase v, uniq := Γc.uniq.erase v }) rfl rfl).addOwn v
            have hrootsM : EnvRoots ρo (v :: toks) (uv :: vals) := EnvRoots.cons huv hroots
            have himmM : ∀ y, Γm.isImm y = Γ0.isImm y := fun y => himmC y
            have havM : ∀ y, Γm.avail y = true → Γ0.avail y = true := by
              intro y hy
              by_cases hyv : y = v
              · subst hyv; exact havv
              · simp only [Ctx.avail_eq, Ctx.borrowed_eq, Γm, Ctx.isImm_addOwn, Ctx.isPbrw_addOwn,
                  Ctx.brw_addOwn, Ctx.epoch_addOwn, Ctx.tokens_addOwn, hyv, ↓reduceIte,
                  Src.NatMap.get?_erase] at hy
                exact hav0 y (by simp only [Ctx.avail_eq, Ctx.borrowed_eq]; exact hy)
            have hknM : ∀ y, Γm.known y = true → y ∈ live := by
              intro y hy
              by_cases hyv : y = v
              · subst hyv; exact hknown0 y havv
              · simp only [Ctx.known_eq, Γm, Ctx.isImm_addOwn, Ctx.isPbrw_addOwn, Ctx.brw_addOwn,
                  Ctx.ownHas_addOwn, hyv, decide_false, Bool.false_or] at hy
                simp only [Src.NatMap.contains, Src.NatMap.get?_erase, hyv, ↓reduceIte] at hy
                exact hkn0 y (by simp only [Ctx.known_eq, Src.NatMap.contains]; exact hy)
            have hepM : ∀ y e, Γm.brw.get? y = some e → e ≤ Γm.epoch := by
              intro y e hy
              simp only [Γm, Ctx.brw_addOwn, Ctx.epoch_addOwn, Src.NatMap.get?_erase] at hy ⊢
              split at hy
              · cases hy
              · exact hep0 y e hy
            obtain ⟨pt, pv, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ :=
              promoteResetFields_sound hproj himm0 hknown0 (idx + 1) rest Γm Γ₂ (v :: toks) (uv :: vals)
                himmM havM hknM hepM htokM hrootsM hprom
            have htok2 : Ctx.Tokens Γ₂ ((pt ++ [v]) ++ toks) := by
              simpa [List.append_assoc] using h1
            have hroots2 : EnvRoots ρo ((pt ++ [v]) ++ toks) ((pv ++ [uv]) ++ vals) := by
              simpa [List.append_assoc] using h2
            refine ⟨pt ++ [v], pv ++ [uv], htok2, hroots2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
              fun y hu => ?_, fun u hu => ?_, fun k => ?_⟩
            · obtain ⟨huM, htkM⟩ := h12 y hu
              simp only [Γm, Ctx.isUniq, Ctx.uniq_addOwn, Src.NatMap.contains,
                Src.NatMap.get?_erase] at huM
              by_cases hyv : y = v
              · subst hyv; simp at huM
              · simp only [hyv, ↓reduceIte] at huM
                refine ⟨huM, fun hni => ?_⟩
                have := htkM hni
                simp only [Γm, Ctx.tokens_addOwn, hyv, ↓reduceIte] at this
                exact this
            · rcases List.mem_append.mp hu with h' | h'
              · exact h13 u h'
              · have : u = uv := List.mem_singleton.mp h'; subst this
                exact List.mem_of_getElem? hget
            · rw [refsIn_append, h14 k, hdrop, List.zipIdx_cons, List.filterMap_cons]
              have h0 : idx - idx = 0 := Nat.sub_self idx
              simp only [h0, List.getElem?_cons_zero, ↓reduceIte]
              rw [← hfm_tail (bfields.drop (idx + 1)) (idx + 1) (Nat.le_refl _)]
              simp only [refsIn]; omega

/-! ## `ReuseCell` preservation for any value other than `.loc l` (no `HeapOk` needed) -/

private def extNotL (l : Nat) (sz : Nat) : Nat → Nat :=
  fun k => if k ≠ l ∧ k < sz then 1 else 0

private theorem reachablePreserved_reuseCell_nonL {H H' : Heap} {l : Nat} {b b' : Body} {r : RVal}
    (hc : H.cell? l = some (.live 1 .dyn b)) (hedge : edgeCount H l = 0)
    (hr : Rc.reuseCell H l b' = some (r, H')) :
    ReachablePreserved H H' (extNotL l H.size) := by
  obtain ⟨_, rfl⟩ := reuseCell_of_some hc hr
  have hl : l < H.size := Proof.cell?_some hc
  refine ⟨by rw [reusedHeap_size]; omega, fun k rk mk bk hreach hck => ?_⟩
  have hk : k < H.size := Proof.cell?_some hck
  have hne : l ≠ k := by
    intro hEq; subst hEq
    exact ReachableFrom.not_of_zero (by simp [extNotL]) hedge hreach
  rw [reusedHeap_cell hl b' k, ite_eq_right (Nat.ne_of_lt hk), ite_eq_right hne]
  exact ⟨rk, hck⟩

private theorem reachableFrom_extNotL_of_den {H : Heap} {l : Nat} {v : RVal} {w : Fir.Val}
    (hne : v ≠ .loc l) (hd : Proof.Den H v w) :
    ReachableFrom H (extNotL l H.size) v := by
  cases v with
  | lit _ => exact .imm (fun _ h => by cases h)
  | ctor0 _ => exact .imm (fun _ h => by cases h)
  | erased => exact .imm (fun _ h => by cases h)
  | loc k =>
    have hkl : k ≠ l := fun h => hne (by rw [h])
    cases hck : H.cell? k with
    | none => simp [Proof.Den, Heap.value?, toFir, hck] at hd
    | some _ =>
      have hk : k < H.size := Proof.cell?_some hck
      exact .root (by simp [extNotL, hkl, hk])

private theorem reachableFrom_extNotL_of_asCtor {H : Heap} {K : Lam.Known} {l : Nat}
    {v : RVal} {key : Key.CtorKey} {fs : List RVal}
    (hne : v ≠ .loc l) (hac : v.asCtor K H = some (key, fs)) :
    ReachableFrom H (extNotL l H.size) v := by
  cases v with
  | lit _ => exact .imm (fun _ h => by cases h)
  | ctor0 _ => exact .imm (fun _ h => by cases h)
  | erased => exact .imm (fun _ h => by cases h)
  | loc k =>
    have hkl : k ≠ l := fun h => hne (by rw [h])
    cases hck : H.cell? k with
    | none => simp [RVal.asCtor, hck] at hac
    | some _ =>
      have hk : k < H.size := Proof.cell?_some hck
      exact .root (by simp [extNotL, hkl, hk])

/-! ## Unpacking `Ctx.reset`, `Ctx.reuse`, `Ctx.dropSlot` -/

private theorem reset_inv {s : Nat} {x : Var} {ctor : Fir.CtorInfo}
    {fields : List (Option Var)} {uniq : Bool} {Γ' : Ctx}
    (h : Γ.reset ctors s x ctor fields uniq K = .ok Γ') :
    Fir.CtorInfo.ofKey ctors ctor.key = some ctor ∧
    K.natZero ≠ some ctor.key ∧ K.natSucc ≠ some ctor.key ∧
    (∃ cls, Ctx.validReuseCtor ctor = some cls ∧
      Γ.rset.contains s = false ∧
      Γ.ctorOf.get? x = some ctor.key ∧
      fields.length = ctor.arity ∧
      Γ.isImm x = false ∧
      (uniq = true → Γ.isUniq x = true) ∧
      ∃ Γ₁ Γ₂, Γ.take x = .ok Γ₁ ∧
        Ctx.promoteResetFields Γ x ctor.key 0 fields Γ₁ = .ok Γ₂ ∧
        Γ' = { Γ₂.release with rset := Γ₂.rset.insert s (cls, uniq) }) := by
  unfold Ctx.reset at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  cases hct : (Fir.CtorInfo.ofKey ctors ctor.key == some ctor) with
  | false => simp [hct] at h
  | true =>
    simp only [hct, ↓reduceIte] at h
    have hct' : Fir.CtorInfo.ofKey ctors ctor.key = some ctor := beq_iff_eq.mp hct
    cases hnat : (K.natZero == some ctor.key || K.natSucc == some ctor.key) with
    | true => simp [hnat] at h
    | false =>
      simp only [hnat, Bool.false_eq_true, ↓reduceIte] at h
      have hnz : K.natZero ≠ some ctor.key := by
        intro he; simp [he] at hnat
      have hns : K.natSucc ≠ some ctor.key := by
        intro he; simp [he] at hnat
      cases hvc : Ctx.validReuseCtor ctor with
      | none => simp [hvc] at h
      | some cls =>
        simp only [hvc] at h
        cases hrs : Γ.rset.contains s with
        | true => simp [hrs] at h
        | false =>
          simp only [hrs, Bool.false_eq_true, ↓reduceIte] at h
          cases hco : (Γ.ctorOf.get? x == some ctor.key) with
          | false => simp [hco] at h
          | true =>
            simp only [hco, ↓reduceIte] at h
            have hco' : Γ.ctorOf.get? x = some ctor.key := beq_iff_eq.mp hco
            cases hfl : (fields.length == ctor.arity) with
            | false => simp [hfl] at h
            | true =>
              simp only [hfl, ↓reduceIte] at h
              have hfl' : fields.length = ctor.arity := beq_iff_eq.mp hfl
              cases him : Γ.isImm x with
              | true => simp [him] at h
              | false =>
                simp only [him, Bool.false_eq_true, ↓reduceIte] at h
                cases huq : (uniq && !Γ.isUniq x) with
                | true => simp [huq] at h
                | false =>
                  simp only [huq, Bool.false_eq_true, ↓reduceIte] at h
                  have huq' : uniq = true → Γ.isUniq x = true := by
                    intro hu; subst hu; simpa using huq
                  cases ht : Γ.take x with
                  | error _ => simp [ht] at h
                  | ok Γ₁ =>
                    simp only [ht] at h
                    cases hprom : Ctx.promoteResetFields Γ x ctor.key 0 fields Γ₁ with
                    | error _ => simp [hprom] at h
                    | ok Γ₂ =>
                      simp only [hprom, Except.ok.injEq] at h
                      exact ⟨hct', hnz, hns, cls, rfl, rfl, hco', hfl', rfl, huq', Γ₁, Γ₂, rfl, hprom, h.symm⟩

private theorem reuse_inv {x : Var} {s : Nat} {ctor : Fir.CtorInfo}
    {args : List Arg} {uniq : Bool} {Γ' : Ctx}
    (h : Γ.reuse ctors x s ctor args uniq K = .ok Γ') :
    Γ.known x = false ∧
    Fir.CtorInfo.ofKey ctors ctor.key = some ctor ∧
    K.natZero ≠ some ctor.key ∧ K.natSucc ≠ some ctor.key ∧
    (∃ cls slotUniq, Ctx.validReuseCtor ctor = some cls ∧
      args.length = ctor.arity ∧
      Γ.rset.get? s = some (cls, slotUniq) ∧
      (uniq = true → slotUniq = true) ∧
      ∃ Γ₂, ({ Γ with rset := Γ.rset.erase s } : Ctx).takeArgs args = .ok Γ₂ ∧
        Γ' = Γ₂.addUniqOwn x) := by
  unfold Ctx.reuse at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  cases hkn : Γ.known x with
  | true => simp [hkn] at h
  | false =>
    simp only [hkn, Bool.false_eq_true, ↓reduceIte] at h
    cases hct : (Fir.CtorInfo.ofKey ctors ctor.key == some ctor) with
    | false => simp [hct] at h
    | true =>
      simp only [hct, ↓reduceIte] at h
      have hct' : Fir.CtorInfo.ofKey ctors ctor.key = some ctor := beq_iff_eq.mp hct
      cases hnat : (K.natZero == some ctor.key || K.natSucc == some ctor.key) with
      | true => simp [hnat] at h
      | false =>
        simp only [hnat, Bool.false_eq_true, ↓reduceIte] at h
        have hnz : K.natZero ≠ some ctor.key := by intro he; simp [he] at hnat
        have hns : K.natSucc ≠ some ctor.key := by intro he; simp [he] at hnat
        cases hvc : Ctx.validReuseCtor ctor with
        | none => simp [hvc] at h
        | some cls =>
          simp only [hvc] at h
          cases hal : (args.length == ctor.arity) with
          | false => simp [hal] at h
          | true =>
            simp only [hal, ↓reduceIte] at h
            have hal' : args.length = ctor.arity := beq_iff_eq.mp hal
            cases hrs : Γ.rset.get? s with
            | none => simp [hrs] at h
            | some pair =>
              obtain ⟨slotCls, slotUniq⟩ := pair
              simp only [hrs] at h
              cases hcm : (slotCls == cls) with
              | false => simp [hcm] at h
              | true =>
                simp only [hcm, ↓reduceIte] at h
                have hce : slotCls = cls := beq_iff_eq.mp hcm
                subst hce
                cases huq : (uniq && !slotUniq) with
                | true => simp [huq] at h
                | false =>
                  simp only [huq, Bool.false_eq_true, ↓reduceIte] at h
                  have huq' : uniq = true → slotUniq = true := by
                    intro hu; subst hu; simpa using huq
                  cases ht : ({ Γ with rset := Γ.rset.erase s } : Ctx).takeArgs args with
                  | error _ => simp [ht] at h
                  | ok Γ₂ =>
                    simp only [ht, Except.ok.injEq] at h
                    exact ⟨rfl, hct', hnz, hns, slotCls, slotUniq, rfl, hal', rfl, huq', Γ₂, rfl, h.symm⟩

private theorem dropSlot_inv {s : Nat} {Γ' : Ctx}
    (h : Γ.dropSlot s = .ok Γ') :
    Γ.rset.contains s = true ∧ Γ' = { Γ.release with rset := Γ.rset.erase s } := by
  unfold Ctx.dropSlot at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  cases hc : Γ.rset.contains s with
  | false => simp [hc] at h
  | true =>
    simp only [hc, ↓reduceIte, Except.ok.injEq] at h
    exact ⟨rfl, h.symm⟩

/-! ## `reset_step` -/

theorem reset_step (st : OwnedState functions H external live Γ ρf ρo owned lex Δ Jf Jo
    borrows uniqs retUniq ctors K priv slots slotVals)
    {s : Nat} {x : Var} {ctor : Fir.CtorInfo} {fields : List (Option Var)} {uniq : Bool}
    {Γ' : Ctx} (hreset : Γ.reset ctors s x ctor fields uniq K = .ok Γ') :
    ∃ sv H' owned' slotVals',
      evalResetMask ρo H x ctor (fieldsMask fields) uniq = .ok (sv, H') ∧
      OwnedState functions H' external live Γ' ρf ρo owned' lex Δ Jf Jo
        borrows uniqs retUniq ctors K priv (slots.insert s sv) slotVals' ∧
      ReachablePreserved H H' external ∧ PrivPreserved H H' priv := by
  obtain ⟨hct, hnz, hns, cls, hvc, hsfree, hco, hfl, hnimm, huq, Γ₁, Γ₂, ht, hprom, rfl⟩ :=
    reset_inv hreset
  obtain ⟨hpos, hnotfl⟩ := validReuseCtor_props hvc
  obtain ⟨vx, wx, owned₁, hvx, hwx, hdx, inv₁, hs₁, hwk₁⟩ := take_sem st.takeInv ht
  have havy : Γ.avail x = true := by
    rcases Ctx.take_ok ht with ⟨hi, _⟩ | ⟨_, n, hn, _⟩
    · simp [hi] at hnimm
    · simp [Ctx.avail_eq, Ctx.tokens_eq, hn]
  obtain ⟨vx', bfields, hvx', hac⟩ := st.ctorOfOk x ctor.key havy hco
  have hvv : vx' = vx := Option.some.inj (hvx'.symm.trans hvx); subst vx'
  obtain ⟨toks₁, htok₁, hroots₁⟩ := inv₁.roots
  have hle₁ : ∀ k, refsIn k owned₁ ≤ refsIn k owned := fun k => by
    have := hs₁ k; simp only [refsIn] at this; omega
  have pre₁ := st.pre.weaker hwk₁ ⟨toks₁, htok₁, hroots₁⟩ hle₁
  have hproj : ∀ v j, Γ.projOf.get? v = some (x, ctor.key, j) → Γ.avail v = true →
      ∃ uv, bfields[j]? = some uv ∧ ρo.get? v = some uv := by
    intro v j hp hv
    obtain ⟨vx2, fs2, uv, hvx2, hac2, hget2, huv2⟩ := st.projOfOk v x ctor.key j havy hv hp
    have hvv2 : vx2 = vx := Option.some.inj (hvx2.symm.trans hvx); subst vx2
    rw [hac] at hac2
    obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj hac2)
    exact ⟨uv, hget2, huv2⟩
  obtain ⟨promToks, promVals, htok₂, hroots₂, himm₂, hpbrw₂, hep₂, hco₂, hpo₂, hrs₂,
      hepochs₂, hav₂, hkn₂, huniq₂, hpromMem, hpromRefs⟩ :=
    promoteResetFields_sound hproj st.immOk (fun v hv => st.known v (Ctx.avail_known hv))
      0 fields Γ₁ Γ₂ toks₁ owned₁
      (fun y => hwk₁.isImm y) (fun y hy => hwk₁.avail hy)
      (fun y hy => st.known y (hwk₁.known hy))
      (fun y e hy => by rw [hwk₁.epoch]; exact st.epochs y e (by rw [← hwk₁.brw]; exact hy))
      htok₁ hroots₁ hprom
  have hpromRefs' : ∀ k, refsIn k promVals =
      refsIn k ((bfields.zipIdx).filterMap fun (u, j) =>
        if Nat.testBit (fieldsMask fields) j then some u else none) := by
    intro k
    rw [hpromRefs k]
    simp only [List.drop_zero, Nat.sub_zero]
    congr 1
    have hcongr : ∀ (ls : List RVal) (off : Nat),
        (ls.zipIdx off).filterMap (fun (u, j) =>
          if match fields[j]? with | some (some _) => true | _ => false then some u else none) =
        (ls.zipIdx off).filterMap (fun (u, j) =>
          if Nat.testBit (fieldsMask fields) j then some u else none) := by
      intro ls; induction ls with
      | nil => intro _; rfl
      | cons z zs ih =>
        intro off
        simp only [List.zipIdx_cons, List.filterMap_cons, fieldsMask_testBit, ih (off + 1)]
    exact hcongr bfields 0
  let Γ' : Ctx := { Γ₂.release with rset := Γ₂.rset.insert s (cls, uniq) }
  have hnb' : ∀ y, Γ'.borrowed y = false := by
    intro y
    simp only [Γ', Ctx.borrowed_eq, Ctx.brw_release, Ctx.epoch_release]
    cases hby : Γ₂.brw.get? y with
    | none => rfl
    | some e =>
      have := hepochs₂ y e hby
      have hne : e ≠ Γ₂.epoch + 1 := by omega
      simp [hne]
  have hav' : ∀ y, Γ'.avail y = true → Γ.avail y = true := by
    intro y hy
    simp only [Ctx.avail_eq, hnb' y, Bool.or_false] at hy
    simp only [Γ', Ctx.isImm, Ctx.tokens_eq, Ctx.isPbrw, Ctx.release, Bool.or_eq_true] at hy
    apply hav₂ y
    simp only [Ctx.avail_eq, Ctx.isImm, Ctx.tokens_eq, Ctx.isPbrw, Bool.or_eq_true]
    rcases hy with (h1 | h2) | h3
    · exact Or.inl (Or.inl (Or.inl h1))
    · exact Or.inl (Or.inl (Or.inr h2))
    · exact Or.inr h3
  have hkn' : ∀ y, Γ'.known y = true → y ∈ live := by
    intro y hy
    simp only [Ctx.known_eq, Γ', Ctx.isImm, Ctx.isPbrw, Ctx.release] at hy
    exact hkn₂ y (by simpa [Ctx.known_eq, Ctx.isImm, Ctx.isPbrw] using hy)
  have hep' : ∀ y e, Γ'.brw.get? y = some e → e ≤ Γ'.epoch := by
    intro y e hy
    simp only [Γ', Ctx.brw_release, Ctx.epoch_release] at hy ⊢
    have := hepochs₂ y e hy; omega
  have htok' : Ctx.Tokens Γ' (promToks ++ toks₁) := htok₂.same rfl rfl
  obtain ⟨skeys, hsk, hsroots⟩ := st.slotRoots
  have hrsEq : Γ₂.rset = Γ.rset := hrs₂.trans hwk₁.rset
  have hsfree₂ : Γ₂.rset.contains s = false := by rw [hrsEq]; exact hsfree
  have hsk' : Ctx.SlotKeys Γ' (s :: skeys) :=
    (hsk.same hrsEq).insert hsfree₂ rfl
  have hsnot : s ∉ skeys := fun hm => by
    have := ((hsk.same hrsEq).mem s).mp hm
    rw [hsfree₂] at this; cases this
  -- Common builder for `OwnedState` once the heap transition `(H → H', sv)` is proved.
  have finish : ∀ (sv : RVal) (H' : Heap),
      Balance H' external ((promVals ++ owned₁) ++ (sv :: slotVals)) →
      ReachablePreserved H H' external →
      (∀ y v, Γ'.avail y = true → ρo.get? y = some v →
        (∀ w, Proof.Den H v w → Proof.Den H' v w) ∧
        (∀ key fs, v.asCtor K H = some (key, fs) → v.asCtor K H' = some (key, fs))) →
      PrivPreserved H H' pre₁.localPriv →
      (∀ k, pre₁.localPriv k → refsIn k promVals = 0 ∧ sv ≠ .loc k) →
      ((sv = .erased ∧ uniq = false) ∨
       (∃ l b, sv = .loc l ∧ H'.cell? l = some (.live 1 .dyn b) ∧
         Ctx.validReuseCtor b.ctor = some cls ∧ b.fields = List.replicate b.ctor.arity .erased ∧
         external l = 0 ∧ edgeCount H' l = 0 ∧
         refsIn l ((promVals ++ owned₁) ++ (sv :: slotVals)) = 1)) →
      OwnedState functions H' external live Γ' ρf ρo (promVals ++ owned₁) lex Δ Jf Jo
        borrows uniqs retUniq ctors K priv (slots.insert s sv) (sv :: slotVals) := by
    intro sv H' hbal' hrpExt htransAvail hprivLoc hlocDisj hslotNew
    have hsroots' : EnvRoots (slots.insert s sv) (s :: skeys) (sv :: slotVals) :=
      EnvRoots.cons (Src.NatMap.get?_insert_self ..) (hsroots.insert_fresh s sv hsnot)
    refine ⟨fun y hy => ?_, ⟨promToks ++ toks₁, htok', hroots₂⟩,
      ⟨s :: skeys, hsk', hsroots'⟩, hbal', hkn', st.distinct,
      fun y hy => st.immOk y (by rw [← hwk₁.isImm y, ← himm₂ y]; exact hy),
      fun y hy => absurd hy (by simp [hnb' y]),
      fun y hy => by
        have hp : Γ.isPbrw y = true := by
          simpa [Γ', Ctx.isPbrw, Ctx.pbrw_release, hpbrw₂, hwk₁.pbrw] using hy
        obtain ⟨v, hv, hr⟩ := st.pbrwOk y hp
        exact ⟨v, hv, hr.transport hrpExt⟩,
      hep',
      fun y key hc => st.ctorOfKnown y key (by simpa [Γ', Ctx.ctorOf_release, hco₂, hwk₁.ctorOf] using hc),
      fun v y key idx hp => st.projOfKnown v y key idx (by simpa [Γ', Ctx.projOf_release, hpo₂, hwk₁.projOf] using hp),
      fun y key hy hc => by
        obtain ⟨v, fs, hv, hac'⟩ := st.ctorOfOk y key (hav' y hy)
          (by simpa [Γ', Ctx.ctorOf_release, hco₂, hwk₁.ctorOf] using hc)
        exact ⟨v, fs, hv, (htransAvail y v hy hv).2 key fs hac'⟩,
      fun v y key idx hy hv hp => by
        obtain ⟨vy, fs, uv, hvy, hac', hget', huv⟩ := st.projOfOk v y key idx (hav' y hy) (hav' v hv)
          (by simpa [Γ', Ctx.projOf_release, hpo₂, hwk₁.projOf] using hp)
        exact ⟨vy, fs, uv, hvy, (htransAvail y vy hy hvy).2 key fs hac', hget', huv⟩,
      fun z hz => ?_,
      fun s' cls' u' hrs' => ?_,
      fun l hl => Nat.lt_of_lt_of_le (st.privBound l hl) hrpExt.1,
      fun l hl => (hprivLoc l (Or.inl hl)).2,
      fun l hl y hy => st.privNoVar l hl y (hav' y hy),
      fun l hl s' hs' => ?_,
      by simpa [Γ', Ctx.pbrw_release, hpbrw₂, hwk₁.pbrw] using st.stack, st.scope⟩
    · obtain ⟨v, w, hv, hw, hd⟩ := st.den y (hav' y hy)
      exact ⟨v, w, hv, hw, (htransAvail y v hy hv).1 w hd⟩
    · obtain ⟨hz₁, htkz⟩ := huniq₂ z hz
      obtain ⟨hmeta₁, v, hv, hvu₁⟩ := pre₁.uniqOk z hz₁
      have himmEq : Γ'.isImm z = Γ₁.isImm z := himm₂ z
      refine ⟨fun hni => ?_, v, hv, ?_⟩
      · have hni₁ : Γ₁.isImm z = false := by rw [← himmEq]; exact hni
        obtain ⟨ht1, hpb1⟩ := hmeta₁ hni₁
        refine ⟨by rw [show Γ'.tokens z = Γ₂.tokens z from rfl, htkz hni₁, ht1], ?_⟩
        simpa [Γ', Ctx.isPbrw, Ctx.pbrw_release, hpbrw₂] using hpb1
      · cases v with
        | lit _ | erased => trivial
        | ctor0 c => exact hvu₁
        | loc k =>
          cases hiz : Γ₁.isImm z with
          | true =>
            obtain ⟨u, hu, himm⟩ := pre₁.immOk z hiz
            have : u = .loc k := Option.some.inj (hu.symm.trans hv); subst this
            exact absurd rfl (himm k)
          | false =>
            obtain ⟨bz, hcz, hextz, _, hrefsz⟩ := hvu₁
            have hloc : pre₁.localPriv k := Or.inr (Or.inr ⟨z, hz₁, hiz, hv⟩)
            obtain ⟨hcell', hedge'⟩ := hprivLoc k hloc
            obtain ⟨hnprom, hnsv⟩ := hlocDisj k hloc
            refine ⟨bz, hcell'.trans hcz, hextz, hedge', ?_⟩
            simp only [refsIn_append, refsIn, hnsv, ↓reduceIte, Nat.zero_add, hnprom]
            rw [refsIn_append] at hrefsz; exact hrefsz
    · simp only [Γ', Src.NatMap.get?_insert] at hrs'
      by_cases hss : s' = s
      · subst hss
        simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hrs'
        obtain ⟨rfl, rfl⟩ := hrs'
        exact ⟨sv, Src.NatMap.get?_insert_self .., hslotNew⟩
      · simp only [hss, ↓reduceIte] at hrs'
        have hrs₁ : Γ₁.rset.get? s' = some (cls', u') := by rw [← hrs₂]; exact hrs'
        obtain ⟨sv', hsv', hcase⟩ := pre₁.rsetOk s' cls' u' hrs₁
        refine ⟨sv', by rw [Src.NatMap.get?_insert_ne _ _ hss]; exact hsv', ?_⟩
        rcases hcase with h0 | ⟨k, bk, rfl, hck, hvck, hbfk, hextk, _, hrefsk⟩
        · exact Or.inl h0
        · have hloc : pre₁.localPriv k := Or.inr (Or.inl ⟨s', cls', u', hrs₁, hsv'⟩)
          obtain ⟨hcell', hedge'⟩ := hprivLoc k hloc
          obtain ⟨hnprom, hnsv⟩ := hlocDisj k hloc
          refine Or.inr ⟨k, bk, rfl, hcell'.trans hck, hvck, hbfk, hextk, hedge', ?_⟩
          simp only [refsIn_append, refsIn, hnsv, ↓reduceIte, Nat.zero_add, hnprom]
          rw [refsIn_append] at hrefsk; exact hrefsk
    · by_cases hss : s' = s
      · subst hss
        rw [Src.NatMap.get?_insert_self]
        intro hEq; cases hEq
        exact (hlocDisj l (Or.inl hl)).2 rfl
      · rw [Src.NatMap.get?_insert_ne _ _ hss]
        simp only [Γ', Src.NatMap.contains, Src.NatMap.get?_insert, hss, ↓reduceIte, hrsEq] at hs'
        exact st.privNoSlot l hl s' hs'
  -- Now case-split on `vx`.
  cases vx with
  | lit lit =>
    cases lit with
    | str _ => simp [RVal.asCtor] at hac
    | nat n =>
      cases n with
      | zero =>
        cases hk0 : K.natZero with
        | none => simp [RVal.asCtor, hk0] at hac
        | some k0 =>
          simp only [RVal.asCtor, hk0, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hac
          exact absurd (hac.1 ▸ hk0) hnz
      | succ n =>
        cases hk1 : K.natSucc with
        | none => simp [RVal.asCtor, hk1] at hac
        | some k1 =>
          simp only [RVal.asCtor, hk1, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hac
          exact absurd (hac.1 ▸ hk1) hns
  | erased => simp [RVal.asCtor] at hac
  | ctor0 c =>
    simp only [RVal.asCtor, Option.some.injEq, Prod.mk.injEq] at hac
    obtain ⟨hckey, hbfNil⟩ := hac
    subst hbfNil
    have huqF : uniq = false := by
      cases hu : uniq with
      | false => rfl
      | true =>
        obtain ⟨_, u, hu', hvu⟩ := st.uniqOk x (huq hu)
        have : u = .ctor0 c := Option.some.inj (hu'.symm.trans hvx); subst this
        have har0 := hvu ctor (hckey ▸ hct)
        omega
    have hmask0 : fieldsMask fields = 0 := by
      have hall : ∀ (idx : Nat) (fs : List (Option Var)) (Γc : Ctx),
          Ctx.promoteResetFields Γ x ctor.key idx fs Γc = .ok Γ₂ →
          ∀ ov, ov ∈ fs → ov = none := by
        intro idx fs
        induction fs generalizing idx with
        | nil => intro _ _ _ h; cases h
        | cons ov rest ih =>
          intro Γc hp ov' hm
          cases ov with
          | none =>
            rcases List.mem_cons.mp hm with rfl | hm'
            · rfl
            · exact ih (idx + 1) Γc hp ov' hm'
          | some v =>
            simp only [Ctx.promoteResetFields] at hp
            split at hp
            · cases hp
            · split at hp
              · split at hp
                · rename_i hpf havv
                  obtain ⟨_, hget, _⟩ := hproj v idx (beq_iff_eq.mp hpf) havv
                  simp at hget
                · cases hp
              · cases hp
      have hnilMask : ∀ fs : List (Option Var), (∀ ov, ov ∈ fs → ov = none) → fieldsMask fs = 0 := by
        intro fs; induction fs with
        | nil => intro _; rfl
        | cons ov rest ih =>
          intro h
          have hov := h ov List.mem_cons_self; subst hov
          simp [fieldsMask, ih (fun z hz => h z (List.mem_cons_of_mem _ hz))]
      exact hnilMask fields (hall 0 fields Γ₁ hprom)
    have hpromNil : promVals = [] := by
      cases promVals with
      | nil => rfl
      | cons u _ => exact absurd (hpromMem u List.mem_cons_self) (by simp)
    have hbal' : Balance H external ((promVals ++ owned₁) ++ (.erased :: slotVals)) := by
      refine SameRefs.balance ?_ st.counts
      intro k
      have h1 := hs₁ k
      simp only [hpromNil, List.nil_append, refsIn_append, refsIn, reduceCtorEq, ↓reduceIte] at h1 ⊢
      omega
    have hev : evalResetMask ρo H x ctor (fieldsMask fields) uniq = .ok (.erased, H) := by
      simp [evalResetMask, hnotfl, hvx, huqF, hmask0]
    refine ⟨.erased, H, promVals ++ owned₁, .erased :: slotVals, hev,
      finish .erased H hbal' (ReachablePreserved.refl H external)
        (fun _ _ _ _ => ⟨fun _ h => h, fun _ _ h => h⟩)
        (PrivPreserved.refl (fun l hl => (pre₁.localPriv_facts hl).2))
        (fun k _ => ⟨by simp [hpromNil, refsIn], fun h => by cases h⟩)
        (Or.inl ⟨rfl, huqF⟩),
      ReachablePreserved.refl H external,
      PrivPreserved.refl st.privNoEdge⟩
  | loc l =>
    cases hcl : H.cell? l with
    | none => simp [RVal.asCtor, hcl] at hac
    | some cell =>
      cases cell with
      | dead => simp [RVal.asCtor, hcl] at hac
      | live rc m b =>
        simp only [RVal.asCtor, hcl, Option.some.injEq, Prod.mk.injEq] at hac
        obtain ⟨hbkey, hbfEq⟩ := hac
        subst hbfEq
        by_cases hisU : rc = 1 ∧ m = .dyn
        · -- Unique in-place shell reset + deadFields dropAll
          obtain ⟨rfl, rfl⟩ := hisU
          let deadFields := (b.fields.zipIdx).filterMap fun (u, j) =>
            if !Nat.testBit (fieldsMask fields) j then some u else none
          have hb_loc : Balance H external (.loc l :: (owned₁ ++ slotVals)) := by
            refine SameRefs.balance ?_ st.counts
            intro k; have := hs₁ k
            simp only [refsIn_append, refsIn] at this ⊢; omega
          have hpart : ∀ k, refsIn k b.fields = refsIn k promVals + refsIn k deadFields := by
            intro k
            rw [hpromRefs' k]
            exact (refsIn_zipIdx_partition (fieldsMask fields) b.fields 0 k).symm
          have hmass : ∀ k, refsIn k (b.fields ++ (owned₁ ++ slotVals)) =
              refsIn k ((resetShell ctor).fields ++ (deadFields ++ promVals ++ owned₁ ++ slotVals)) := by
            intro k
            simp only [resetShell, refsIn_append, refsIn_replicate_erased, Nat.zero_add, hpart k]
            omega
          obtain ⟨H₁, hreuse, hb₁⟩ := reuseCell_balance hcl hb_loc hmass
          have hb₁_split : Balance H₁ external (deadFields ++ ((promVals ++ owned₁) ++ (.loc H.size :: slotVals))) := by
            refine SameRefs.balance ?_ hb₁
            intro k; simp only [refsIn_append, refsIn]; omega
          obtain ⟨H₂, hdrop, hb₂, _⟩ := dropAll_retaining H₁ deadFields ((promVals ++ owned₁) ++ (.loc H.size :: slotVals)) hb₁_split
          have hb₁_held : Balance H₁ (holdRoots external ((promVals ++ owned₁) ++ (.loc H.size :: slotVals)))
              deadFields := balance_hold.mp hb₁_split
          have hrp₁ := ReachablePreserved.reuseCell_hold hcl hb_loc hreuse
          have hrp₂ := ReachablePreserved.dropAll H₁ deadFields hb₁_held hdrop
          have hrpExt : ReachablePreserved H H₂ external :=
            hrp₁.of_holdRoots.trans hrp₂.of_holdRoots
          -- `localPriv` avoids `l` and `b.fields`
          obtain ⟨hextL, hrestL, hedgeL, hbfL, hrestSz, hedgeSz, hbfSz⟩ := reuse_exclusive hcl hb_loc
          have hlocFacts : ∀ k, pre₁.localPriv k →
              k < H.size ∧ l ≠ k ∧ edgeCount H k = 0 ∧ refsIn k b.fields = 0 := by
            intro k hk
            obtain ⟨hlt, hed⟩ := pre₁.localPriv_facts hk
            have hbf0 : refsIn k b.fields = 0 := by
              have := refsIn_fields_le hcl k; omega
            have hneL : l ≠ k := by
              intro hEq; subst hEq
              rcases hk with hp | ⟨s', cls', u', hrs', hsl'⟩ | ⟨z, huz, hiz, hvz⟩
              · exact st.privNoVar l hp x havy hvx
              · obtain ⟨sv', hsv', _⟩ := pre₁.rsetOk s' cls' u' hrs'
                have : sv' = .loc l := Option.some.inj (hsv'.symm.trans hsl')
                have hm : RVal.loc l ∈ slotVals :=
                  this ▸ hsroots.member ((hsk.mem s').mpr (by rw [← hwk₁.rset]; simp [Src.NatMap.contains, hrs'])) hsv'
                have hp := refsIn_pos hm
                rw [refsIn_append] at hrestL; omega
              · obtain ⟨hmeta, v', hv', _⟩ := pre₁.uniqOk z huz
                have : v' = .loc l := Option.some.inj (hv'.symm.trans hvz)
                have hm : RVal.loc l ∈ owned₁ :=
                  this ▸ hroots₁.member (htok₁.mem (by rw [(hmeta hiz).1]; omega)) hv'
                have hp := refsIn_pos hm
                rw [refsIn_append] at hrestL; omega
            exact ⟨hlt, hneL, hed, hbf0⟩
          have hpriv₁ : PrivPreserved H H₁ pre₁.localPriv :=
            PrivPreserved.reuseCell hcl hreuse
              (fun k hk => (hlocFacts k hk).1) (fun k hk => (hlocFacts k hk).2.1)
              (fun k hk => (hlocFacts k hk).2.2.1)
              (fun k _ => by simp [resetShell, refsIn_replicate_erased])
          -- Also preserve the new shell location `H.size` across `dropAll H₁ deadFields`
          have hnewCell₁ : H₁.cell? H.size = some (.live 1 .dyn (resetShell ctor)) := by
            obtain ⟨_, rfl⟩ := reuseCell_of_some hcl hreuse
            exact reusedHeap_new H l (resetShell ctor)
          have hnewEdge₁ : edgeCount H₁ H.size = 0 := by
            obtain ⟨_, rfl⟩ := reuseCell_of_some hcl hreuse
            rw [reusedHeap, edgeCount_alloc]
            have hfree := edgeCount_free hcl H.size
            simp only [resetShell, refsIn_replicate_erased]; omega
          have hdeadZero : ∀ k, (pre₁.localPriv k ∨ k = H.size) → refsIn k deadFields = 0 := by
            intro k hk
            have hbf0 : refsIn k b.fields = 0 := by
              rcases hk with h | rfl
              · exact (hlocFacts k h).2.2.2
              · exact hbfSz
            have := hpart k; omega
          have hprivExt₂ : PrivPreserved H₁ H₂ (fun k => pre₁.localPriv k ∨ k = H.size) :=
            PrivPreserved.dropAll H₁ deadFields
              (fun k hk => by
                rcases hk with h | rfl
                · exact (hpriv₁ k h).2
                · exact hnewEdge₁)
              hdeadZero hdrop
          have hprivLoc : PrivPreserved H H₂ pre₁.localPriv :=
            hpriv₁.trans (hprivExt₂.mono (fun _ h => Or.inl h))
          have hlocDisj : ∀ k, pre₁.localPriv k → refsIn k promVals = 0 ∧ RVal.loc H.size ≠ .loc k := by
            intro k hk
            have ⟨hlt, _, _, hbf0⟩ := hlocFacts k hk
            refine ⟨by have := hpart k; omega, fun hEq => by cases hEq; omega⟩
          have hfreshExt : external H.size = 0 := by
            have h0 := st.counts H.size; rw [dynCount_fresh] at h0; omega
          have hnewRefs : refsIn H.size ((promVals ++ owned₁) ++ (.loc H.size :: slotVals)) = 1 := by
            have hp0 : refsIn H.size promVals = 0 := by have := hpart H.size; omega
            rw [refsIn_append] at hrestSz
            simp only [refsIn_append, refsIn, ↓reduceIte]; omega
          have hslotNew : ∃ l' b', RVal.loc H.size = .loc l' ∧ H₂.cell? l' = some (.live 1 .dyn b') ∧
              Ctx.validReuseCtor b'.ctor = some cls ∧ b'.fields = List.replicate b'.ctor.arity .erased ∧
              external l' = 0 ∧ edgeCount H₂ l' = 0 ∧
              refsIn l' ((promVals ++ owned₁) ++ (.loc H.size :: slotVals)) = 1 := by
            obtain ⟨hcell2, hedge2⟩ := hprivExt₂ H.size (Or.inr rfl)
            exact ⟨H.size, resetShell ctor, rfl, hcell2.trans hnewCell₁, hvc, rfl,
              hfreshExt, hedge2, hnewRefs⟩
          -- `htransAvail`: every available variable in `Γ'` is imm, pbrw, or in `promVals ++ owned₁`
          have htransAvail : ∀ y v, Γ'.avail y = true → ρo.get? y = some v →
              (∀ w, Proof.Den H v w → Proof.Den H₂ v w) ∧
              (∀ key fs, v.asCtor K H = some (key, fs) → v.asCtor K H₂ = some (key, fs)) := by
            intro y v hy hv
            simp only [Ctx.avail_eq, hnb', Bool.or_false, Bool.or_eq_true, decide_eq_true_eq] at hy
            rcases hy with (hi | hp) | hpb
            · obtain ⟨u, hu, himm⟩ := st.immOk y (by rw [← hwk₁.isImm y, ← himm₂ y]; exact hi)
              have : u = v := Option.some.inj (hu.symm.trans hv); subst this
              have hr1 : ReachableFrom H (holdRoots external (b.fields ++ (owned₁ ++ slotVals))) u :=
                .imm himm
              have hr2 : ReachableFrom H₁ (holdRoots external ((promVals ++ owned₁) ++ (.loc H.size :: slotVals))) u :=
                .imm himm
              exact ⟨fun w hd => hrp₂.den hr2 (hrp₁.den hr1 hd),
                fun key fs hac' => hrp₂.asCtor hr2 (hrp₁.asCtor hr1 hac')⟩
            · have hm : v ∈ promVals ++ owned₁ := hroots₂.member (htok'.mem hp) hv
              have hm1 : v ∈ b.fields ++ (owned₁ ++ slotVals) := by
                rcases List.mem_append.mp hm with h1 | h1
                · exact List.mem_append_left _ (hpromMem v h1)
                · exact List.mem_append_right _ (List.mem_append_left _ h1)
              have hr1 : ReachableFrom H (holdRoots external (b.fields ++ (owned₁ ++ slotVals))) v :=
                ReachableFrom.of_externalRoot (held_external hm1)
              have hr2 : ReachableFrom H₁ (holdRoots external ((promVals ++ owned₁) ++ (.loc H.size :: slotVals))) v :=
                ReachableFrom.of_externalRoot (held_external (List.mem_append_left _ hm))
              exact ⟨fun w hd => hrp₂.den hr2 (hrp₁.den hr1 hd),
                fun key fs hac' => hrp₂.asCtor hr2 (hrp₁.asCtor hr1 hac')⟩
            · have hpb0 : Γ.isPbrw y = true := by
                simpa [Γ', Ctx.isPbrw, Ctx.pbrw_release, hpbrw₂, hwk₁.pbrw] using hpb
              obtain ⟨u, hu, hreach⟩ := st.pbrwOk y hpb0
              have : u = v := Option.some.inj (hu.symm.trans hv); subst this
              exact ⟨fun w hd => hrpExt.den hreach hd, fun key fs hac' => hrpExt.asCtor hreach hac'⟩
          have hev : evalResetMask ρo H x ctor (fieldsMask fields) uniq = .ok (.loc H.size, H₂) := by
            simp only [evalResetMask, hnotfl, Bool.false_eq_true, ↓reduceIte, hvx, hcl, hreuse]
            simp only [deadFields, hdrop, Option.map_some, Result.ofOption]
          exact ⟨.loc H.size, H₂, promVals ++ owned₁, .loc H.size :: slotVals, hev,
            finish (.loc H.size) H₂ hb₂ hrpExt htransAvail hprivLoc hlocDisj (Or.inr hslotNew),
            hrpExt, hprivLoc.mono (fun _ h => Or.inl h)⟩
        · -- Shared fallback path (`rc ≠ 1 ∨ m ≠ .dyn`)
          have huqF : uniq = false := by
            cases hu : uniq with
            | false => rfl
            | true =>
              obtain ⟨_, u, hu', hvu⟩ := st.uniqOk x (huq hu)
              have : u = .loc l := Option.some.inj (hu'.symm.trans hvx); subst this
              obtain ⟨b', hcl', _, _, _⟩ := hvu
              rw [hcl] at hcl'
              obtain ⟨hrc, hm, _⟩ := Cell.live.inj (Option.some.inj hcl')
              exact absurd ⟨hrc, hm⟩ hisU
          let liveFields := (b.fields.zipIdx).filterMap fun (u, j) =>
            if Nat.testBit (fieldsMask fields) j then some u else none
          have hlive_mem : ∀ u, u ∈ liveFields → u ∈ b.fields :=
            fun _ hm => zipIdx_filterMap_mem_fst (Nat.testBit (fieldsMask fields)) hm
          have hac_loc : (RVal.loc l).asCtor K H = some (ctor.key, b.fields) := by
            simp [RVal.asCtor, hcl, hbkey]
          have hlive_brw : ∀ u, u ∈ liveFields → BorrowVal H u :=
            fun u hm => BorrowVal.asCtor_field hac_loc (hlive_mem u hm)
          have hloc_bf : ∀ k, pre₁.localPriv k → refsIn k b.fields = 0 := fun k hk => by
            have hed := (pre₁.localPriv_facts hk).2
            have hle := refsIn_fields_le hcl k; omega
          have hlive_priv : ∀ k, pre₁.localPriv k → refsIn k liveFields = 0 := fun k hk => by
            have hpart := refsIn_zipIdx_partition (fieldsMask fields) b.fields 0 k
            have := hloc_bf k hk; dsimp only [liveFields] at hpart ⊢; omega
          obtain ⟨H₁, hinc, hb₁, hrp₁, hedge₁, hpriv₁⟩ :=
            incList_sound liveFields st.counts hlive_brw
              (fun k hk => (pre₁.localPriv_facts hk).2) hlive_priv
          have hb₁_split : Balance H₁ external ([.loc l] ++ ((promVals ++ owned₁) ++ slotVals)) := by
            refine SameRefs.balance ?_ hb₁
            intro k
            have h1 := hs₁ k
            have h2 := hpromRefs' k
            simp only [refsIn_append, refsIn] at h1 ⊢; dsimp only [liveFields] at h2 ⊢; omega
          obtain ⟨H₂, hdrop, hb₂_raw, _⟩ := dropAll_retaining H₁ [.loc l] ((promVals ++ owned₁) ++ slotVals) hb₁_split
          have hb₁_held : Balance H₁ (holdRoots external ((promVals ++ owned₁) ++ slotVals)) [.loc l] :=
            balance_hold.mp hb₁_split
          have hb₂ : Balance H₂ external ((promVals ++ owned₁) ++ (.erased :: slotVals)) := by
            refine SameRefs.balance ?_ hb₂_raw
            intro k; simp only [refsIn_append, refsIn, reduceCtorEq, ↓reduceIte]; omega
          have hrp₂ := ReachablePreserved.dropAll H₁ [.loc l] hb₁_held hdrop
          have hrpExt : ReachablePreserved H H₂ external :=
            (hrp₁ external).trans hrp₂.of_holdRoots
          -- `pre₁.localPriv` avoids `l` because `H.cell? l` is NOT `some (.live 1 .dyn _)`!
          have hlocNeL : ∀ k, pre₁.localPriv k → refsIn k [.loc l] = 0 := by
            intro k hk
            have hne : l ≠ k := by
              intro hEq; subst hEq
              rcases hk with hp | ⟨s', cls', u', hrs', hsl'⟩ | ⟨z, huz, _, hvz⟩
              · exact st.privNoVar l hp x havy hvx
              · obtain ⟨sv', hsv', hcase⟩ := pre₁.rsetOk s' cls' u' hrs'
                have : sv' = .loc l := Option.some.inj (hsv'.symm.trans hsl'); subst this
                rcases hcase with ⟨hc, _⟩ | ⟨_, _, hEq', hcl', _, _, _, _, _⟩
                · cases hc
                · cases hEq'; rw [hcl] at hcl'
                  obtain ⟨hrc, hm, _⟩ := Cell.live.inj (Option.some.inj hcl')
                  exact hisU ⟨hrc, hm⟩
              · obtain ⟨_, v', hv', hvu'⟩ := pre₁.uniqOk z huz
                have : v' = .loc l := Option.some.inj (hv'.symm.trans hvz); subst this
                obtain ⟨_, hcl', _, _, _⟩ := hvu'
                rw [hcl] at hcl'
                obtain ⟨hrc, hm, _⟩ := Cell.live.inj (Option.some.inj hcl')
                exact hisU ⟨hrc, hm⟩
            simp [refsIn, hne]
          have hpriv₂ : PrivPreserved H₁ H₂ pre₁.localPriv :=
            PrivPreserved.dropAll H₁ [.loc l] (fun k hk => (hpriv₁ k hk).2) hlocNeL hdrop
          have hprivLoc : PrivPreserved H H₂ pre₁.localPriv := hpriv₁.trans hpriv₂
          have htransAvail : ∀ y v, Γ'.avail y = true → ρo.get? y = some v →
              (∀ w, Proof.Den H v w → Proof.Den H₂ v w) ∧
              (∀ key fs, v.asCtor K H = some (key, fs) → v.asCtor K H₂ = some (key, fs)) := by
            intro y v hy hv
            simp only [Ctx.avail_eq, hnb', Bool.or_false, Bool.or_eq_true, decide_eq_true_eq] at hy
            rcases hy with (hi | hp) | hpb
            · obtain ⟨u, hu, himm⟩ := st.immOk y (by rw [← hwk₁.isImm y, ← himm₂ y]; exact hi)
              have : u = v := Option.some.inj (hu.symm.trans hv); subst this
              have hr1 : ReachableFrom H external u := .imm himm
              exact ⟨fun w hd => hrpExt.den hr1 hd, fun key fs hac' => hrpExt.asCtor hr1 hac'⟩
            · have hm : v ∈ promVals ++ owned₁ := hroots₂.member (htok'.mem hp) hv
              have hr1 : ReachableFrom H (holdRoots external ((promVals ++ owned₁) ++ slotVals)) v :=
                ReachableFrom.of_externalRoot (held_external (List.mem_append_left _ hm))
              have hr2 : ReachableFrom H₁ (holdRoots external ((promVals ++ owned₁) ++ slotVals)) v :=
                hr1.transport (hrp₁ _)
              have hcomp := (hrp₁ (holdRoots external ((promVals ++ owned₁) ++ slotVals))).trans hrp₂
              exact ⟨fun w hd => hcomp.den hr1 hd, fun key fs hac' => hcomp.asCtor hr1 hac'⟩
            · have hpb0 : Γ.isPbrw y = true := by
                simpa [Γ', Ctx.isPbrw, Ctx.pbrw_release, hpbrw₂, hwk₁.pbrw] using hpb
              obtain ⟨u, hu, hreach⟩ := st.pbrwOk y hpb0
              have : u = v := Option.some.inj (hu.symm.trans hv); subst this
              exact ⟨fun w hd => hrpExt.den hreach hd, fun key fs hac' => hrpExt.asCtor hreach hac'⟩
          have hev : evalResetMask ρo H x ctor (fieldsMask fields) uniq = .ok (.erased, H₂) := by
            unfold evalResetMask
            simp only [hnotfl, Bool.false_eq_true, ↓reduceIte, hvx, hcl]
            cases rc with
            | zero =>
              simp only [huqF, Bool.false_eq_true, ↓reduceIte, liveFields, hinc, hdrop,
                Option.map_some, Result.ofOption]
            | succ rc' =>
              cases rc' with
              | zero =>
                cases m with
                | dyn => exact absurd ⟨rfl, rfl⟩ hisU
                | static =>
                  simp only [huqF, Bool.false_eq_true, ↓reduceIte, liveFields, hinc, hdrop,
                    Option.map_some, Result.ofOption]
              | succ _ =>
                simp only [huqF, Bool.false_eq_true, ↓reduceIte, liveFields, hinc, hdrop,
                  Option.map_some, Result.ofOption]
          have hlocDisj : ∀ k, pre₁.localPriv k → refsIn k promVals = 0 ∧ RVal.erased ≠ .loc k := by
            intro k hk
            exact ⟨by rw [hpromRefs' k]; exact hlive_priv k hk, fun h => by cases h⟩
          exact ⟨.erased, H₂, promVals ++ owned₁, .erased :: slotVals, hev,
            finish .erased H₂ hb₂ hrpExt htransAvail hprivLoc hlocDisj (Or.inl ⟨rfl, huqF⟩),
            hrpExt, hprivLoc.mono (fun _ h => Or.inl h)⟩

/-! ## `reuse_step` -/

theorem reuse_step {F : Fir.Program}
    (st : OwnedState functions H external live Γ ρf ρo owned lex Δ Jf Jo
      borrows uniqs retUniq F.ctors F.known priv slots slotVals)
    {x : Var} {s : Nat} {ctor : Fir.CtorInfo} {args : List Arg} {uniq : Bool}
    (hx : x ∉ live) {Γ' : Ctx}
    (hreuse : Γ.reuse F.ctors x s ctor args uniq F.known = .ok Γ')
    {w : Fir.Val} (hw : Fir.evalRhs F ρf (.ctor ctor args) = .ok w) :
    ∃ sv v H' owned' slotVals',
      slots.get? s = some sv ∧
      evalReuseVal ρo H sv ctor args uniq = .ok (v, H') ∧
      OwnedState functions H' external (live ++ [x]) Γ' (ρf.insert x w) (ρo.insert x v) owned'
        lex Δ Jf Jo borrows uniqs retUniq F.ctors F.known priv (slots.erase s) slotVals' ∧
      ReachablePreserved H H' external ∧ PrivPreserved H H' priv := by
  obtain ⟨_, hct, hnz, hns, cls, slotUniq, hvc, halen, hrs, huq, Γ₂, ht, rfl⟩ := reuse_inv hreuse
  obtain ⟨hpos, hnotfl⟩ := validReuseCtor_props hvc
  obtain ⟨sv, hsv, hsvCase⟩ := st.rsetOk s cls slotUniq hrs
  obtain ⟨skeys, hsk, hsroots⟩ := st.slotRoots
  have hscont : Γ.rset.contains s = true := by simp [Src.NatMap.contains, hrs]
  let Γ₁ : Ctx := { Γ with rset := Γ.rset.erase s }
  obtain ⟨hsmem, hsk₁⟩ := hsk.erase hscont (Γ' := Γ₁) rfl
  obtain ⟨slotVals₁, hsroots₁_old, hssame⟩ := EnvRoots.erase hsv hsroots hsmem
  have hsroots₁ : EnvRoots (slots.erase s) (skeys.erase s) slotVals₁ :=
    hsroots₁_old.congr (fun s' hs' => by
      have hne : s' ≠ s := (hsk.nodup.mem_erase_iff.mp hs').1
      exact get?_erase_ne slots s s' hne)
  obtain ⟨toks0, htok0, hroots0⟩ := st.roots
  have htinv₁ : TakeInv H Γ₁ ρf ρo owned := ⟨st.den, ⟨toks0, htok0.same rfl rfl, hroots0⟩, st.immOk⟩
  obtain ⟨vs, ws, owned₁, hvs, hws, hds, inv₂, hs, hwk₂⟩ := takeArgs_sem htinv₁ ht
  have hwlen : ws.length = ctor.arity := by
    have h1 := firEvalArgs_length hws
    omega
  have hvlen : vs.length = ctor.arity := hds.length.trans hwlen
  have hwEq : w = .ctor ctor ws := by
    simp [Fir.evalRhs, hws, hwlen] at hw; exact hw.symm
  subst hwEq
  have hvsNoPriv := takeArgs_noPriv_reset (Γ := Γ₁) st.privNoVar hvs ht
  obtain ⟨toks₂, htok₂, hroots₂⟩ := inv₂.roots
  have hleOwned : ∀ k, refsIn k owned₁ ≤ refsIn k owned := fun k => by
    have := hs k; rw [refsIn_append] at this; omega
  have hleSlot : ∀ k, refsIn k slotVals₁ ≤ refsIn k slotVals := fun k => by
    have := hssame k; simp only [refsIn] at this; omega
  -- Build `pre₂` with `Γ₂`, `owned₁`, `slots.erase s`, `slotVals₁`
  have huniq₂ : ∀ z, Γ₂.isUniq z = true →
      (Γ₂.isImm z = false → Γ₂.tokens z = 1 ∧ Γ₂.isPbrw z = false) ∧
      ∃ v, ρo.get? z = some v ∧ UniqVal F.ctors H external (owned₁ ++ slotVals₁) v := by
    intro z hz
    have hz0 : Γ.isUniq z = true := hwk₂.isUniq z hz
    obtain ⟨hmeta, v, hv, hvu⟩ := st.uniqOk z hz0
    have hmeta' : Γ₂.isImm z = false → Γ₂.tokens z = 1 ∧ Γ₂.isPbrw z = false := fun hni => by
      have hni0 : Γ.isImm z = false := by
        have := hwk₂.isImm z; exact this.symm.trans hni
      have htok1 : Γ₂.tokens z = 1 := by
        have h1 := hwk₂.uniqTok z hz hni
        exact h1.trans (hmeta hni0).1
      have hpb0 : Γ₂.isPbrw z = false := by
        have h1 := hwk₂.isPbrw z
        exact h1.trans (hmeta hni0).2
      exact ⟨htok1, hpb0⟩
    refine ⟨hmeta', v, hv, ?_⟩
    cases v with
    | lit _ | erased => trivial
    | ctor0 c => exact hvu
    | loc k =>
      cases hi : Γ₂.isImm z with
      | true =>
        obtain ⟨u, hu, himm⟩ := st.immOk z ((hwk₂.isImm z).symm.trans hi)
        have : u = .loc k := Option.some.inj (hu.symm.trans hv); subst this
        exact absurd rfl (himm k)
      | false =>
        obtain ⟨bz, hcz, hextz, hedgez, hrefsz⟩ := hvu
        have ht1 : Γ₂.tokens z = 1 := (hmeta' hi).1
        have hmem : RVal.loc k ∈ owned₁ := hroots₂.member (htok₂.mem (by omega)) hv
        have hp := refsIn_pos hmem
        rw [refsIn_append] at hrefsz
        have h1 := hleOwned k; have h2 := hleSlot k
        exact ⟨bz, hcz, hextz, hedgez, by rw [refsIn_append]; omega⟩
  have hrset₂ : ∀ s' cls' u', Γ₂.rset.get? s' = some (cls', u') →
      ∃ sv', (slots.erase s).get? s' = some sv' ∧
        ((sv' = .erased ∧ u' = false) ∨
         (∃ l b, sv' = .loc l ∧ H.cell? l = some (.live 1 .dyn b) ∧
           Ctx.validReuseCtor b.ctor = some cls' ∧ b.fields = List.replicate b.ctor.arity .erased ∧
           external l = 0 ∧ edgeCount H l = 0 ∧ refsIn l (owned₁ ++ slotVals₁) = 1)) := by
    intro s' cls' u' hrs'
    rw [hwk₂.rset] at hrs'
    simp only [Γ₁, Src.NatMap.get?_erase] at hrs'
    by_cases hss : s' = s
    · simp [hss] at hrs'
    · simp only [hss, ↓reduceIte] at hrs'
      obtain ⟨sv', hsv', hcase⟩ := st.rsetOk s' cls' u' hrs'
      refine ⟨sv', by rw [get?_erase_ne slots s s' hss]; exact hsv', ?_⟩
      rcases hcase with h0 | ⟨k, bk, rfl, hck, hvck, hbfk, hextk, hedgek, hrefsk⟩
      · exact Or.inl h0
      · have hs'mem : s' ∈ skeys.erase s :=
          (hsk₁.mem s').mpr (by simp [Γ₁, Src.NatMap.contains, Src.NatMap.get?_erase, hss, hrs'])
        have hmem : RVal.loc k ∈ slotVals₁ :=
          hsroots₁.member hs'mem (by rw [get?_erase_ne slots s s' hss]; exact hsv')
        have hp := refsIn_pos hmem
        rw [refsIn_append] at hrefsk
        have h1 := hleOwned k; have h2 := hleSlot k
        exact Or.inr ⟨k, bk, rfl, hck, hvck, hbfk, hextk, hedgek, by rw [refsIn_append]; omega⟩
  have pre₂ : OwnedPre functions H external live Γ₂ ρf ρo owned₁ lex Δ Jf Jo
      borrows uniqs retUniq F.ctors F.known priv (slots.erase s) slotVals₁ :=
    ⟨fun y hy => st.den y (hwk₂.avail hy), ⟨toks₂, htok₂, hroots₂⟩,
      ⟨skeys.erase s, hsk₁.same hwk₂.rset, hsroots₁⟩,
      fun y hy => st.known y (hwk₂.known hy), st.distinct,
      fun y hy => st.immOk y ((hwk₂.isImm y).symm.trans hy),
      fun y hy => st.borrowed y ((hwk₂.borrowed y).symm.trans hy),
      fun y hy => st.pbrwOk y ((hwk₂.isPbrw y).symm.trans hy),
      fun y e hy => by rw [hwk₂.epoch]; exact st.epochs y e (by rw [← hwk₂.brw]; exact hy),
      fun y key hc => st.ctorOfKnown y key (by rw [← hwk₂.ctorOf]; exact hc),
      fun v y key idx hp => st.projOfKnown v y key idx (by rw [← hwk₂.projOf]; exact hp),
      fun y key hy hc => st.ctorOfOk y key (hwk₂.avail hy) (by rw [← hwk₂.ctorOf]; exact hc),
      fun v y key idx hy hv hp => st.projOfOk v y key idx (hwk₂.avail hy) (hwk₂.avail hv) (by rw [← hwk₂.projOf]; exact hp),
      huniq₂, hrset₂, st.privBound, st.privNoEdge,
      fun l hl y hy => st.privNoVar l hl y (hwk₂.avail hy),
      fun l hl s' hs' => by
        rw [hwk₂.rset] at hs'
        by_cases hss : s' = s
        · subst hss; simp [Γ₁, Src.NatMap.contains, Src.NatMap.get?_erase] at hs'
        · rw [get?_erase_ne slots s s' hss]
          simp only [Γ₁, Src.NatMap.contains, Src.NatMap.get?_erase, hss, ↓reduceIte] at hs'
          exact st.privNoSlot l hl s' hs',
      by rw [hwk₂.pbrw]; exact st.stack, st.scope⟩
  have hloc_vs : ∀ k, pre₂.localPriv k → refsIn k vs = 0 := by
    intro k hk
    rcases hk with hp | ⟨s', cls', u', hrs', hsl'⟩ | ⟨z, huz, hiz, hvz⟩
    · by_cases hnz : refsIn k vs = 0
      · exact hnz
      · exfalso
        exact hvsNoPriv k hp (.loc k) (mem_of_refsIn_pos (by omega)) rfl
    · obtain ⟨sv', hsv', hcase⟩ := pre₂.rsetOk s' cls' u' hrs'
      have : sv' = .loc k := Option.some.inj (hsv'.symm.trans hsl'); subst this
      rcases hcase with ⟨hc, _⟩ | ⟨_, _, hEq, _, _, _, _, _, hrefs⟩
      · cases hc
      · cases hEq
        have hrs0 : Γ.rset.get? s' = some (cls', u') := by
          rw [hwk₂.rset] at hrs'; simp only [Γ₁, Src.NatMap.get?_erase] at hrs'
          split at hrs'
          · cases hrs'
          · exact hrs'
        obtain ⟨sv0, hsv0, hcase0⟩ := st.rsetOk s' cls' u' hrs0
        have hne : s' ≠ s := by
          intro hEq; subst hEq; rw [Src.NatMap.get?_erase] at hsl'; simp at hsl'
        rw [get?_erase_ne slots s s' hne] at hsl'
        have : sv0 = .loc k := Option.some.inj (hsv0.symm.trans hsl'); subst this
        rcases hcase0 with ⟨hc, _⟩ | ⟨_, _, hEq', _, _, _, _, _, hrefs0⟩
        · cases hc
        · cases hEq'
          rw [refsIn_append, hs k, refsIn_append] at hrefs0
          rw [refsIn_append] at hrefs
          have h2 := hleSlot k; omega
    · obtain ⟨_, v0, hv0, hvu0⟩ := st.uniqOk z (hwk₂.isUniq z huz)
      have : v0 = .loc k := Option.some.inj (hv0.symm.trans hvz); subst this
      obtain ⟨_, _, _, _, hrefs0⟩ := hvu0
      obtain ⟨_, v2, hv2, hvu2⟩ := pre₂.uniqOk z huz
      have : v2 = .loc k := Option.some.inj (hv2.symm.trans hvz); subst this
      obtain ⟨_, _, _, _, hrefs2⟩ := hvu2
      rw [refsIn_append, hs k, refsIn_append] at hrefs0
      rw [refsIn_append] at hrefs2
      have h2 := hleSlot k; omega
  have hfresh0 := st.counts H.size
  rw [dynCount_fresh] at hfresh0
  have hfreshExt : external H.size = 0 := by omega
  have hfreshAll : refsIn H.size (owned ++ slotVals) = 0 := by omega
  have hfreshEdge : edgeCount H H.size = 0 := by omega
  have hfreshParts : refsIn H.size vs = 0 ∧ refsIn H.size owned₁ = 0 ∧ refsIn H.size slotVals₁ = 0 := by
    rw [refsIn_append, hs H.size, hssame H.size, refsIn_append] at hfreshAll
    simp only [refsIn] at hfreshAll; omega
  -- Split on `sv = .erased` vs `sv = .loc l`
  rcases hsvCase with ⟨rfl, hsluF⟩ | ⟨l, b, rfl, hcl, _, hbf_erased, hextL, hedgeL, hrefsL⟩
  · -- Fallback allocation on `.erased` (only when `uniq = false`)
    have huqF : uniq = false := by
      cases hu : uniq with
      | false => rfl
      | true => exact absurd (huq hu) (by simp [hsluF])
    have held : Balance H (holdRoots external (owned₁ ++ slotVals₁)) vs := by
      apply balance_hold.mp
      refine SameRefs.balance ?_ st.counts
      intro k
      have h1 := hs k; have h2 := hssame k
      simp only [refsIn_append, refsIn, reduceCtorEq, ↓reduceIte] at h1 h2 ⊢; omega
    obtain ⟨hr, hb, hresult, hpreserve⟩ :=
      evalRhs_alloc_owned (T := { ctors := F.ctors, known := F.known }) hvs hvlen hpos held hds
    have hreach := ReachablePreserved.alloc H external { ctor, fields := vs }
    have hprivLoc : PrivPreserved H (H.alloc .rc { ctor, fields := vs }).2 pre₂.localPriv :=
      PrivPreserved.alloc (fun k hk => (pre₂.localPriv_facts hk).1)
        (fun k hk => (pre₂.localPriv_facts hk).2) hloc_vs
    have pre₃ := pre₂.transport hpreserve (fun v hv => hv.alloc _) hreach
      (fun _ _ _ _ _ _ hac => asCtor_alloc hac) hprivLoc
    have hbal' : Balance (H.alloc .rc { ctor, fields := vs }).2 external
        (((H.alloc .rc { ctor, fields := vs }).1 :: owned₁) ++ slotVals₁) := by
      have hr' := balance_resume hb
      refine SameRefs.balance ?_ hr'
      intro k; simp only [List.cons_append, refsIn_append, refsIn]; omega
    have hvU : UniqVal F.ctors (H.alloc .rc { ctor, fields := vs }).2 external
        (((H.alloc .rc { ctor, fields := vs }).1 :: owned₁) ++ slotVals₁)
        (H.alloc .rc { ctor, fields := vs }).1 := by
      show ∃ b', (H.alloc .rc { ctor, fields := vs }).2.cell? H.size = some (.live 1 .dyn b') ∧
        external H.size = 0 ∧
        edgeCount (H.alloc .rc { ctor, fields := vs }).2 H.size = 0 ∧
        refsIn H.size ((.loc H.size :: owned₁) ++ slotVals₁) = 1
      refine ⟨{ ctor, fields := vs }, ?_, hfreshExt, ?_, ?_⟩
      · simpa [AllocPol.mode] using Proof.alloc_cell .rc H { ctor, fields := vs }
      · simp only [edgeCount_alloc]; omega
      · simp only [List.cons_append, refsIn_append, refsIn, ↓reduceIte]; omega
    have hpvNew : ∀ k, pre₃.localPriv k → (H.alloc .rc { ctor, fields := vs }).1 ≠ .loc k := by
      intro k hk hEq
      have hlt : k < H.size := (pre₂.localPriv_facts hk).1
      simp only [Heap.alloc, Heap.size] at hEq hlt
      cases hEq; omega
    have hev : evalReuseVal ρo H .erased ctor args uniq =
        .ok (Heap.alloc .rc H { ctor, fields := vs }) := by
      simp [evalReuseVal, hvs, hnotfl, hvlen, huqF]
    exact ⟨.erased, (H.alloc .rc { ctor, fields := vs }).1, (H.alloc .rc { ctor, fields := vs }).2,
      (H.alloc .rc { ctor, fields := vs }).1 :: owned₁, slotVals₁, hsv, hev,
      pre₃.bindUniqOwned hx hresult hbal' hvU hpvNew, hreach,
      hprivLoc.mono (fun _ h => Or.inl h)⟩
  · -- In-place `reuseCell` on `.loc l`
    have hb_loc : Balance H external (.loc l :: (vs ++ owned₁ ++ slotVals₁)) := by
      refine SameRefs.balance ?_ st.counts
      intro k; have h1 := hs k; have h2 := hssame k
      simp only [refsIn_append, refsIn] at h1 h2 ⊢; omega
    have hbfZero : ∀ k, refsIn k b.fields = 0 := fun k => by
      rw [hbf_erased]; exact refsIn_replicate_erased b.ctor.arity k
    have hmass : ∀ k, refsIn k (b.fields ++ (vs ++ owned₁ ++ slotVals₁)) =
        refsIn k (vs ++ (owned₁ ++ slotVals₁)) := by
      intro k; simp only [refsIn_append, hbfZero k, Nat.zero_add]; omega
    obtain ⟨H', hrc, hbal'_raw⟩ := reuseCell_balance (b' := { ctor, fields := vs }) hcl hb_loc hmass
    have hbal' : Balance H' external ((.loc H.size :: owned₁) ++ slotVals₁) := by
      refine SameRefs.balance ?_ hbal'_raw
      intro k; simp only [List.cons_append, refsIn_append, refsIn]
    have hresult : Proof.Den H' (.loc H.size) (.ctor ctor ws) := by
      refine ReachablePreserved.reuseCell_den hcl hb_loc hrc hds (fun u hu => ?_)
      cases u with
      | lit _ => exact .imm (fun _ h => by cases h)
      | ctor0 _ => exact .imm (fun _ h => by cases h)
      | erased => exact .imm (fun _ h => by cases h)
      | loc k =>
        have hp := refsIn_pos hu
        dsimp only at hp
        exact .root (by simp only [holdRoots, refsIn_append]; omega)
    have hrpExt : ReachablePreserved H H' external :=
      ReachablePreserved.reuseCell hcl hb_loc hrc
    have hrpNonL : ReachablePreserved H H' (extNotL l H.size) :=
      reachablePreserved_reuseCell_nonL hcl hedgeL hrc
    have hlZeroParts : refsIn l vs = 0 ∧ refsIn l owned₁ = 0 ∧ refsIn l slotVals₁ = 0 := by
      rw [refsIn_append, hs l, hssame l, refsIn_append] at hrefsL
      simp only [refsIn, ↓reduceIte] at hrefsL; omega
    have hlocNeL : ∀ k, pre₂.localPriv k → l ≠ k := by
      intro k hk hEq; subst hEq
      rcases hk with hp | ⟨s', cls', u', hrs', hsl'⟩ | ⟨z, huz, hiz, hvz⟩
      · exact st.privNoSlot l hp s hscont hsv
      · have hs'mem : s' ∈ skeys.erase s :=
          ((hsk₁.same hwk₂.rset).mem s').mpr (by simp [Src.NatMap.contains, hrs'])
        have hp := refsIn_pos (hsroots₁.member hs'mem hsl')
        omega
      · obtain ⟨hmeta, v', hv', _⟩ := pre₂.uniqOk z huz
        have : v' = .loc l := Option.some.inj (hv'.symm.trans hvz)
        have hp := refsIn_pos (this ▸ hroots₂.member (htok₂.mem (by rw [(hmeta hiz).1]; omega)) hv')
        omega
    have hprivLoc : PrivPreserved H H' pre₂.localPriv :=
      PrivPreserved.reuseCell hcl hrc
        (fun k hk => (pre₂.localPriv_facts hk).1) hlocNeL
        (fun k hk => (pre₂.localPriv_facts hk).2) hloc_vs
    -- Every variable available in `Γ₂` is distinct from `.loc l`
    have havailNeL : ∀ y v, Γ₂.avail y = true → ρo.get? y = some v → v ≠ .loc l := by
      intro y v hy hv hEq; subst hEq
      simp only [Ctx.avail_eq, Bool.or_eq_true, decide_eq_true_eq] at hy
      rcases hy with ((hi | hp) | hb) | hpb
      · obtain ⟨u, hu, himm⟩ := pre₂.immOk y hi
        have : u = .loc l := Option.some.inj (hu.symm.trans hv); subst this
        exact himm l rfl
      · have hp' := refsIn_pos (hroots₂.member (htok₂.mem hp) hv)
        omega
      · obtain ⟨u, hu, hbrw⟩ := pre₂.borrowed y hb
        have : u = .loc l := Option.some.inj (hu.symm.trans hv); subst this
        change 0 < edgeCount H l at hbrw; omega
      · obtain ⟨u, hu, hreach⟩ := pre₂.pbrwOk y hpb
        have : u = .loc l := Option.some.inj (hu.symm.trans hv); subst this
        exact ReachableFrom.not_of_zero hextL hedgeL hreach
    have pre₃ : OwnedPre functions H' external live Γ₂ ρf ρo owned₁ lex Δ Jf Jo
        borrows uniqs retUniq F.ctors F.known priv (slots.erase s) slotVals₁ :=
      { pre₂ with
        den := fun y hy => by
          obtain ⟨v, w', hv, hw', hd⟩ := pre₂.den y hy
          exact ⟨v, w', hv, hw',
            hrpNonL.den (reachableFrom_extNotL_of_den (havailNeL y v hy hv) hd) hd⟩
        borrowed := fun y hy => by
          obtain ⟨v, hv, hbv⟩ := pre₂.borrowed y hy
          exact ⟨v, hv, hbv.reuseShell hcl hbfZero hrc⟩
        pbrwOk := fun y hy => by
          obtain ⟨v, hv, hreach⟩ := pre₂.pbrwOk y hy
          exact ⟨v, hv, hreach.transport hrpExt⟩
        ctorOfOk := fun y key hy hc => by
          obtain ⟨v, fs, hv, hac⟩ := pre₂.ctorOfOk y key hy hc
          exact ⟨v, fs, hv,
            hrpNonL.asCtor (reachableFrom_extNotL_of_asCtor (havailNeL y v hy hv) hac) hac⟩
        projOfOk := fun v y key idx hy hv hp => by
          obtain ⟨vy, fs, uv, hvy, hac, hget, huv⟩ := pre₂.projOfOk v y key idx hy hv hp
          exact ⟨vy, fs, uv, hvy,
            hrpNonL.asCtor (reachableFrom_extNotL_of_asCtor (havailNeL y vy hy hvy) hac) hac,
            hget, huv⟩
        uniqOk := fun z hz => by
          obtain ⟨hmeta, v, hv, hvu⟩ := pre₂.uniqOk z hz
          refine ⟨hmeta, v, hv, ?_⟩
          cases v with
          | lit _ | erased => trivial
          | ctor0 c => exact hvu
          | loc k =>
            cases hi : Γ₂.isImm z with
            | true =>
              obtain ⟨u, hu, himm⟩ := pre₂.immOk z hi
              have : u = .loc k := Option.some.inj (hu.symm.trans hv); subst this
              exact absurd rfl (himm k)
            | false =>
              obtain ⟨bz, hcz, hextz, _, hrefsz⟩ := hvu
              obtain ⟨hcell, hedge⟩ := hprivLoc k (Or.inr (Or.inr ⟨z, hz, hi, hv⟩))
              exact ⟨bz, hcell.trans hcz, hextz, hedge, hrefsz⟩
        rsetOk := fun s' cls' u' hrs' => by
          obtain ⟨sv', hsv', hcase⟩ := pre₂.rsetOk s' cls' u' hrs'
          refine ⟨sv', hsv', ?_⟩
          rcases hcase with h0 | ⟨k, bk, rfl, hck, hvck, hbfk, hextk, _, hrefsk⟩
          · exact Or.inl h0
          · obtain ⟨hcell, hedge⟩ := hprivLoc k (Or.inr (Or.inl ⟨s', cls', u', hrs', hsv'⟩))
            exact Or.inr ⟨k, bk, rfl, hcell.trans hck, hvck, hbfk, hextk, hedge, hrefsk⟩
        privBound := fun k hk => Nat.lt_of_lt_of_le (pre₂.privBound k hk) hrpExt.1
        privNoEdge := fun k hk => (hprivLoc k (Or.inl hk)).2 }
    have hvU : UniqVal F.ctors H' external ((.loc H.size :: owned₁) ++ slotVals₁) (.loc H.size) := by
      obtain ⟨_, rfl⟩ := reuseCell_of_some hcl hrc
      refine ⟨{ ctor, fields := vs }, reusedHeap_new H l _, hfreshExt, ?_, ?_⟩
      · rw [reusedHeap, edgeCount_alloc]
        have hfree := edgeCount_free hcl H.size
        simp only; omega
      · simp only [List.cons_append, refsIn_append, refsIn, ↓reduceIte]; omega
    have hpvNew : ∀ k, pre₃.localPriv k → RVal.loc H.size ≠ .loc k := by
      intro k hk hEq
      have hlt : k < H.size := (pre₂.localPriv_facts hk).1
      cases hEq; omega
    have hev : evalReuseVal ρo H (.loc l) ctor args uniq = .ok (.loc H.size, H') := by
      simp [evalReuseVal, hvs, hnotfl, hvlen, hrc, Result.ofOption]
    exact ⟨.loc l, .loc H.size, H', .loc H.size :: owned₁, slotVals₁, hsv, hev,
      pre₃.bindUniqOwned hx hresult hbal' hvU hpvNew, hrpExt,
      hprivLoc.mono (fun _ h => Or.inl h)⟩

/-! ## `dropSlot_step` -/

theorem dropSlot_step (st : OwnedState functions H external live Γ ρf ρo owned lex Δ Jf Jo
    borrows uniqs retUniq ctors K priv slots slotVals)
    {s : Nat} {Γ' : Ctx} (hdrop : Γ.dropSlot s = .ok Γ') :
    ∃ sv H' slotVals',
      slots.get? s = some sv ∧
      evalDropVal H sv = .ok H' ∧
      OwnedState functions H' external live Γ' ρf ρo owned lex Δ Jf Jo
        borrows uniqs retUniq ctors K priv (slots.erase s) slotVals' ∧
      ReachablePreserved H H' external ∧ PrivPreserved H H' priv := by
  obtain ⟨hscont, rfl⟩ := dropSlot_inv hdrop
  cases hrs : Γ.rset.get? s with
  | none => simp [Src.NatMap.contains, hrs] at hscont
  | some pair =>
    obtain ⟨cls, u⟩ := pair
    obtain ⟨sv, hsv, hsvCase⟩ := st.rsetOk s cls u hrs
    obtain ⟨skeys, hsk, hsroots⟩ := st.slotRoots
    let Γ' : Ctx := { Γ.release with rset := Γ.rset.erase s }
    obtain ⟨hsmem, hsk₁⟩ := hsk.erase hscont (Γ' := Γ') rfl
    obtain ⟨slotVals₁, hsroots₁_old, hssame⟩ := EnvRoots.erase hsv hsroots hsmem
    have hsroots₁ : EnvRoots (slots.erase s) (skeys.erase s) slotVals₁ :=
      hsroots₁_old.congr (fun s' hs' => by
        have hne : s' ≠ s := (hsk.nodup.mem_erase_iff.mp hs').1
        exact get?_erase_ne slots s s' hne)
    have hnb' : ∀ y, Γ'.borrowed y = false := by
      intro y
      simp only [Γ', Ctx.borrowed_eq, Ctx.brw_release, Ctx.epoch_release]
      cases hby : Γ.brw.get? y with
      | none => rfl
      | some e =>
        have := st.epochs y e hby
        have hne : e ≠ Γ.epoch + 1 := by omega
        simp [hne]
    have hav' : ∀ y, Γ'.avail y = true → Γ.avail y = true := by
      intro y hy
      simp only [Ctx.avail_eq, hnb' y, Bool.or_false] at hy
      simp only [Γ', Ctx.isImm, Ctx.tokens_eq, Ctx.isPbrw, Ctx.release, Bool.or_eq_true] at hy
      simp only [Ctx.avail_eq, Ctx.isImm, Ctx.tokens_eq, Ctx.isPbrw, Bool.or_eq_true]
      rcases hy with (h1 | h2) | h3
      · exact Or.inl (Or.inl (Or.inl h1))
      · exact Or.inl (Or.inl (Or.inr h2))
      · exact Or.inr h3
    have hleSlot : ∀ k, refsIn k slotVals₁ ≤ refsIn k slotVals := fun k => by
      have := hssame k; simp only [refsIn] at this; omega
    obtain ⟨toks, htok, hroots⟩ := st.roots
    have pre₁ : OwnedPre functions H external live Γ' ρf ρo owned lex Δ Jf Jo
        borrows uniqs retUniq ctors K priv (slots.erase s) slotVals₁ :=
      ⟨fun y hy => st.den y (hav' y hy), ⟨toks, htok.same rfl rfl, hroots⟩,
        ⟨skeys.erase s, hsk₁, hsroots₁⟩,
        fun y hy => st.known y (by simpa [Γ', Ctx.known_eq, Ctx.isImm, Ctx.isPbrw, Ctx.release] using hy), st.distinct,
        st.immOk, fun y hy => absurd hy (by simp [hnb' y]), st.pbrwOk,
        fun y e hy => by
          simp only [Γ', Ctx.brw_release, Ctx.epoch_release] at hy ⊢
          have := st.epochs y e hy; omega,
        st.ctorOfKnown, st.projOfKnown,
        fun y key hy hc => st.ctorOfOk y key (hav' y hy) hc,
        fun v y key idx hy hv hp => st.projOfOk v y key idx (hav' y hy) (hav' v hv) hp,
        fun z hz => by
          obtain ⟨hmeta, v, hv, hvu⟩ := st.uniqOk z hz
          refine ⟨hmeta, v, hv, ?_⟩
          cases v with
          | lit _ | erased => trivial
          | ctor0 c => exact hvu
          | loc k =>
            cases hi : Γ.isImm z with
            | true =>
              obtain ⟨u', hu', himm⟩ := st.immOk z hi
              have : u' = .loc k := Option.some.inj (hu'.symm.trans hv); subst this
              exact absurd rfl (himm k)
            | false =>
              obtain ⟨bz, hcz, hextz, hedgez, hrefsz⟩ := hvu
              have hmem : RVal.loc k ∈ owned :=
                hroots.member (htok.mem (by rw [(hmeta hi).1]; omega)) hv
              have hp := refsIn_pos hmem
              rw [refsIn_append] at hrefsz
              have h2 := hleSlot k
              exact ⟨bz, hcz, hextz, hedgez, by rw [refsIn_append]; omega⟩,
        fun s' cls' u' hrs' => by
          simp only [Γ', Src.NatMap.get?_erase] at hrs'
          by_cases hss : s' = s
          · simp [hss] at hrs'
          · simp only [hss, ↓reduceIte] at hrs'
            obtain ⟨sv', hsv', hcase⟩ := st.rsetOk s' cls' u' hrs'
            refine ⟨sv', by rw [get?_erase_ne slots s s' hss]; exact hsv', ?_⟩
            rcases hcase with h0 | ⟨k, bk, rfl, hck, hvck, hbfk, hextk, hedgek, hrefsk⟩
            · exact Or.inl h0
            · have hs'mem : s' ∈ skeys.erase s :=
                (hsk₁.mem s').mpr (by simp [Γ', Src.NatMap.contains, Src.NatMap.get?_erase, hss, hrs'])
              have hmem : RVal.loc k ∈ slotVals₁ :=
                hsroots₁.member hs'mem (by rw [get?_erase_ne slots s s' hss]; exact hsv')
              have hp := refsIn_pos hmem
              rw [refsIn_append] at hrefsk
              have h2 := hleSlot k
              exact Or.inr ⟨k, bk, rfl, hck, hvck, hbfk, hextk, hedgek, by rw [refsIn_append]; omega⟩,
        st.privBound, st.privNoEdge,
        fun l hl y hy => st.privNoVar l hl y (hav' y hy),
        fun l hl s' hs' => by
          by_cases hss : s' = s
          · subst hss; simp [Γ', Src.NatMap.contains, Src.NatMap.get?_erase] at hs'
          · rw [get?_erase_ne slots s s' hss]
            simp only [Γ', Src.NatMap.contains, Src.NatMap.get?_erase, hss, ↓reduceIte] at hs'
            exact st.privNoSlot l hl s' hs',
        st.stack, st.scope⟩
    have hb_split : Balance H external ([sv] ++ (owned ++ slotVals₁)) := by
      refine SameRefs.balance ?_ st.counts
      intro k; have h2 := hssame k
      simp only [refsIn_append, refsIn] at h2 ⊢; omega
    obtain ⟨H', hd, hb', _⟩ := dropAll_retaining H [sv] (owned ++ slotVals₁) hb_split
    have hb_held : Balance H (holdRoots external (owned ++ slotVals₁)) [sv] := balance_hold.mp hb_split
    have hrp := ReachablePreserved.dropAll H [sv] hb_held hd
    have hsv_priv : ∀ k, pre₁.localPriv k → refsIn k [sv] = 0 := by
      intro k hk
      rcases hsvCase with ⟨rfl, _⟩ | ⟨l, _, rfl, _, _, _, _, _, hrefsL⟩
      · simp [refsIn]
      · have hne : l ≠ k := by
          intro hEq; subst hEq
          rcases hk with hp | ⟨s', cls', u', hrs', hsl'⟩ | ⟨z, huz, hiz, hvz⟩
          · exact st.privNoSlot l hp s hscont hsv
          · have hs'mem : s' ∈ skeys.erase s :=
              (hsk₁.mem s').mpr (by simp [Src.NatMap.contains, hrs'])
            have hp := refsIn_pos (hsroots₁.member hs'mem hsl')
            rw [refsIn_append, hssame l] at hrefsL
            simp only [refsIn, ↓reduceIte] at hrefsL; omega
          · obtain ⟨hmeta, v', hv', _⟩ := pre₁.uniqOk z huz
            have : v' = .loc l := Option.some.inj (hv'.symm.trans hvz)
            have ht1 : Γ.tokens z = 1 := (hmeta hiz).1
            have hp := refsIn_pos (this ▸ hroots.member (htok.mem (by omega)) hv')
            rw [refsIn_append, hssame l] at hrefsL
            simp only [refsIn, ↓reduceIte] at hrefsL; omega
        simp [refsIn, hne]
    have hprivLoc : PrivPreserved H H' pre₁.localPriv :=
      PrivPreserved.dropAll H [sv] (fun k hk => (pre₁.localPriv_facts hk).2) hsv_priv hd
    have pre₂ := pre₁.call hnb' hrp hprivLoc
    have hev : evalDropVal H sv = .ok H' := by simp [evalDropVal, hd, Result.ofOption]
    exact ⟨sv, H', slotVals₁, hsv, hev, pre₂.toState hb', hrp.of_holdRoots,
      hprivLoc.mono (fun _ h => Or.inl h)⟩

end

end IxCC.Own.Plain
