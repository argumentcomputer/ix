import IxCC.Lam.Erase.Proof.Forms

/-! # Erasure's word case (stage W1)

A `word` table entry erases to the Lam word primitive `Prim.word w op` (`Erase.wordForm`, and the
wrapper's body), and SrcEval's rule F6w on towers meets that primitive on their numbers. A tower
`UIntN.ofBitVec (BitVec.ofFin (Fin.mk n _))` erases to the literal `n` when its three constructors
unbox at field 0 (`WordUnboxAt`, which erasure decides with `Input.wordUnboxAtB` at the
operation's width and at its result width before it emits the primitive):

* `wordUnboxAt_of_B`: the check decides the fact;
* `vr_word`: a value F6w reads as the word `n` is related only to the literal `n`;
* `vr_mkWord`: the tower F6w builds for `n` is related to the literal `n`;
* `word_value_sim`: F6w on related arguments and the word primitive on their images agree up to
  `VR`; where F6w is stuck nothing is owed (the analogue of `prim_value_sim`). -/

set_option autoImplicit false

namespace IxCC.Src.WordOp

/-- A word result of `eval` is at the operation's result width. -/
theorem eval_resultWidth {w : Width} {op : WordOp} {a b : Nat} {w' : Width} {n : Nat}
    (h : op.eval w a b = .word w' n) : w' = op.resultWidth w := by
  cases op with
  | convert t =>
    simp only [eval] at h
    split at h <;> (simp only [WordResult.word.injEq] at h; exact h.1.symm)
  | _ =>
    simp only [eval, resultWidth, WordResult.word.injEq, reduceCtorEq] at h ⊢
    try exact h.1.symm

end IxCC.Src.WordOp

namespace IxCC.Lam.Erase.Proof

open IxCC.Src (CId Width WordOp Levels)
open IxCC.Sem (Result SimUpTo)

/-! ## The unboxing fact -/

/-- `unboxesAt0B` decides `UnboxesAt0`. -/
theorem unboxesAt0_of_B {I : Input} {c : CId} {nf : Nat} (h : I.unboxesAt0B c nf = true) :
    UnboxesAt0 I c nf := by
  unfold Input.unboxesAt0B at h
  split at h
  · rename_i sf lv ind cidx np nf' ty hd
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hu⟩ := h
    exact ⟨sf, lv, ind, cidx, np, ty, hd, hu⟩
  · cases h

/-- **The check erasure runs decides the fact.** -/
theorem wordUnboxAt_of_B {I : Input} {w : Width} (h : I.wordUnboxAtB w = true) :
    WordUnboxAt I w := by
  simp only [Input.wordUnboxAtB, Bool.and_eq_true, Option.any_eq_true] at h
  obtain ⟨⟨⟨c₁, h₁, u₁⟩, ⟨c₂, h₂, u₂⟩⟩, ⟨c₃, h₃, u₃⟩⟩ := h
  exact ⟨⟨c₁, h₁, unboxesAt0_of_B u₁⟩, ⟨c₂, h₂, unboxesAt0_of_B u₂⟩, ⟨c₃, h₃, unboxesAt0_of_B u₃⟩⟩

/-! ## Towers and their numbers -/

variable {I : Input} {G : Key.GKey → GlobalId → Prop}

/-- A related value of a constructor that unboxes at field 0 is related through its first
field. -/
theorem VR.unbox0_inv {c : CId} {nf : Nat} (hc : UnboxesAt0 I c nf) {ls : Levels}
    {ps : List Src.Slot} {f : Src.Value} {fs : List Src.Value} {v : Val}
    (h : VR I G (.con c ls ps (f :: fs)) v) : VR I G f v := by
  obtain ⟨sf, lv, ind, cidx, np, ty, hd, hu⟩ := hc
  obtain ⟨_, hr⟩ := VR.con_inv h hd
  rcases hr with ⟨j, a, hj, ha, hva, _⟩ | ⟨hn, _⟩
  · rw [hu] at hj
    cases hj
    simp only [List.getElem?_cons_zero, Option.some.injEq] at ha
    subst ha
    exact hva
  · rw [hu] at hn
    cases hn

/-- A constructor that unboxes at field 0, whose other fields are irrelevant, is related through
its first field. -/
theorem VR.unbox0 {c : CId} {nf : Nat} (hc : UnboxesAt0 I c nf) {ls : Levels} {ps : List Src.Slot}
    {f : Src.Value} {fs : List Src.Value} {v : Val} (hl : (f :: fs).length = nf)
    (hirr : ∀ g ∈ fs, g.isIrr = true) (hf : VR I G f v) : VR I G (.con c ls ps (f :: fs)) v := by
  obtain ⟨sf, lv, ind, cidx, np, ty, hd, hu⟩ := hc
  refine VR.unboxed hd hl hu (j := 0) rfl hf fun i g hi hne => ?_
  cases i with
  | zero => exact absurd rfl hne
  | succ i =>
    simp only [List.getElem?_cons_succ] at hi
    exact hirr g (List.mem_iff_getElem?.2 ⟨i, hi⟩)

/-- What `asWord?` reads: a tower of the pinned constructors of `w` around a number below the
size. -/
theorem asWord?_some {p : Src.Program} {w : Width} {x : Src.Value} {n : Nat}
    (h : p.asWord? w x = some n) :
    n < w.size ∧ ∃ c ls c' ls' s' c'' ls'' s'' f,
      x = .con c ls [] [.con c' ls' [s'] [.con c'' ls'' [s''] [.lit n, f]]] ∧
      p.known.wordCtors.lookup w = some c ∧ p.known.bitVecOfFin = some c' ∧
      p.known.finMk = some c'' := by
  unfold Src.Program.asWord? at h
  split at h
  · rename_i c ls c' ls' s' c'' ls'' s'' m f
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst h
      simp only [Src.Program.wordCtor?, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨h₁, h₂⟩, h₃⟩, hlt⟩ := hc
      exact ⟨hlt, c, ls, c', ls', s', c'', ls'', s'', f, rfl, h₁.symm, h₂.symm, h₃.symm⟩
    · cases h
  · cases h

/-- **A tower is related only to its number**: a value `asWord?` reads as `n` at width `w`
erases to the literal `n`. -/
theorem vr_word {p : Src.Program} (hk : p.known = I.known) {w : Width} (hu : WordUnboxAt I w)
    {x : Src.Value} {n : Nat} (hx : p.asWord? w x = some n) {v : Val} (h : VR I G x v) :
    v = .lit (.nat n) := by
  obtain ⟨⟨c₁, h₁, u₁⟩, ⟨c₂, h₂, u₂⟩, ⟨c₃, h₃, u₃⟩⟩ := hu
  obtain ⟨_, c, ls, c', ls', s', c'', ls'', s'', f, rfl, e₁, e₂, e₃⟩ := asWord?_some hx
  rw [hk, h₁, Option.some.injEq] at e₁
  rw [hk, h₂, Option.some.injEq] at e₂
  rw [hk, h₃, Option.some.injEq] at e₃
  subst e₁ e₂ e₃
  have h3 := VR.unbox0_inv u₃ (VR.unbox0_inv u₂ (VR.unbox0_inv u₁ h))
  cases h3
  rfl

/-- **F6w's tower is related to its number** (at the width it is built at). -/
theorem vr_mkWord {p : Src.Program} (hk : p.known = I.known) {w : Width} (hu : WordUnboxAt I w)
    {n : Nat} {v : Src.Value} (h : p.mkWord? w n = some v) : VR I G v (.lit (.nat n)) := by
  obtain ⟨⟨c₁, h₁, u₁⟩, ⟨c₂, h₂, u₂⟩, ⟨c₃, h₃, u₃⟩⟩ := hu
  simp [Src.Program.mkWord?, Src.Program.wordCtor?, hk, h₁, h₂, h₃] at h
  subst h
  exact VR.unbox0 u₁ rfl (by simp) (VR.unbox0 u₂ rfl (by simp)
    (VR.unbox0 u₃ rfl (by simp [Src.Value.isIrr]) VR.lit))

/-! ## The word primitive against F6w -/

/-- F6w's value for `eval`'s result, against the Lam literal of its number (a decision's result
is stuck in SrcEval, so nothing is owed for it). -/
theorem wordResult_sim (S : Setting) {w : Width} {op : WordOp}
    (hu' : WordUnboxAt S.I (op.resultWidth w)) (a b : Nat) {m : Nat} :
    SimUpTo (VR S.I S.G) m (fun _ => S.p.wordResult (op.eval w a b))
      (fun _ => .ok (.lit (.nat (op.eval w a b).val))) := by
  cases hr : op.eval w a b with
  | word w' n =>
    have e := WordOp.eval_resultWidth hr
    subst e
    simp only [Src.Program.wordResult, Src.WordResult.val]
    cases hm : S.p.mkWord? (op.resultWidth w) n with
    | none => exact SimUpTo.stuck _
    | some v => exact SimUpTo.ok (vr_mkWord rfl hu' hm)
  | nat n => exact SimUpTo.ok VR.lit
  | dec d => exact SimUpTo.stuck _

/-- A decision's result is stuck in SrcEval. -/
theorem wordResult_dec (p : Src.Program) {w : Width} {op : WordOp} (hd : op.isDecision = true)
    (a b : Nat) : p.wordResult (op.eval w a b) = .stuck := by
  cases op <;> simp [WordOp.isDecision] at hd <;> rfl

/-- The word primitive on one literal. -/
theorem primResult_word1 (K : Lam.Known) {w : Width} {op : WordOp} {x : Nat}
    (ha : op.arity = 1) (hd : op.isDecision = false) (hx : op = .ofNat ∨ x < w.size) :
    Lam.primResult K (.word w op) [.lit (.nat x)] = .ok (.lit (.nat (op.eval w x 0).val)) := by
  rcases hx with rfl | hx
  · simp [Lam.primResult, Lam.natArgs, Lam.Prim.sem, wordSem, ha, hd]
  · simp [Lam.primResult, Lam.natArgs, Lam.Prim.sem, wordSem, ha, hd, hx]

/-- The word primitive on two literals. -/
theorem primResult_word2 (K : Lam.Known) {w : Width} {op : WordOp} {x y : Nat}
    (ha : op.arity = 2) (hd : op.isDecision = false) (hx : x < w.size) (hy : y < w.size) :
    Lam.primResult K (.word w op) [.lit (.nat x), .lit (.nat y)] =
      .ok (.lit (.nat (op.eval w x y).val)) := by
  simp [Lam.primResult, Lam.natArgs, Lam.Prim.sem, wordSem, ha, hd, hx, hy]

/-- **Erasure's word case**: F6w on related arguments and the Lam word primitive on their images
agree up to `VR` (where F6w is stuck, nothing is owed). -/
theorem word_value_sim (S : Setting) {w : Width} {op : WordOp}
    (hu : WordUnboxAt S.I w) (hu' : WordUnboxAt S.I (op.resultWidth w)) {m : Nat}
    {xs : List Src.Value} {vs : List Val} (h : Forall2 (VR S.I S.G) xs vs) :
    SimUpTo (VR S.I S.G) m (fun _ => S.p.wordValue w op xs)
      (fun _ => Lam.primResult S.L.known (.word w op) vs) := by
  cases h with
  | nil => exact SimUpTo.stuck _
  | cons ha h =>
    rename_i a v as vs'
    cases h with
    | nil =>
      -- one argument
      by_cases har : op.arity = 1
      · have hdec : op.isDecision = false := by
          cases op <;> first | rfl | exact absurd har (by decide)
        · -- the argument F6w reads, and its image
          have hsrc : ∀ x, (op = .ofNat ∧ a = .lit x) ∨ (op ≠ .ofNat ∧ S.p.asWord? w a = some x) →
              S.p.wordValue w op [a] = S.p.wordResult (op.eval w x 0) := by
            intro x hx
            simp only [Src.Program.wordValue, har, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
            rcases hx with ⟨rfl, rfl⟩ | ⟨hne, hx⟩
            · rfl
            · cases op <;> first | exact absurd rfl hne | simp only [hx]
          by_cases hof : op = .ofNat
          · cases a with
            | lit x =>
              cases ha
              refine (wordResult_sim S hu' x 0).congr (fun _ => hsrc x (.inl ⟨hof, rfl⟩))
                (fun _ => primResult_word1 _ har hdec (.inl hof))
            | _ =>
              subst hof
              exact (SimUpTo.stuck _).congr (fun _ => rfl) (fun _ => rfl)
          · cases hx : S.p.asWord? w a with
            | none =>
              refine (SimUpTo.stuck _).congr (fun _ => ?_) (fun _ => rfl)
              simp only [Src.Program.wordValue, har, bne_self_eq_false, Bool.false_eq_true,
                ↓reduceIte]
              cases op <;> first | exact absurd rfl hof | simp only [hx]
            | some x =>
              have hv := vr_word rfl hu hx ha
              subst hv
              exact (wordResult_sim S hu' x 0).congr (fun _ => hsrc x (.inr ⟨hof, hx⟩))
                (fun _ => primResult_word1 _ har hdec (.inr (asWord?_some hx).1))
      · refine (SimUpTo.stuck _).congr (fun _ => ?_) (fun _ => rfl)
        have : (op.arity != 1) = true := by simp [har]
        simp only [Src.Program.wordValue, this, ↓reduceIte]
    | cons hb h =>
      rename_i b v₂ bs vs''
      cases h with
      | nil =>
        -- two arguments
        by_cases har : op.arity = 2
        · cases hx : S.p.asWord? w a with
          | none =>
            refine (SimUpTo.stuck _).congr (fun _ => ?_) (fun _ => rfl)
            simp only [Src.Program.wordValue, har, bne_self_eq_false, Bool.false_eq_true,
              ↓reduceIte, hx]
          | some x =>
            cases hy : S.p.asWord? w b with
            | none =>
              refine (SimUpTo.stuck _).congr (fun _ => ?_) (fun _ => rfl)
              simp only [Src.Program.wordValue, har, bne_self_eq_false, Bool.false_eq_true,
                ↓reduceIte, hx, hy]
            | some y =>
              have hsrc : S.p.wordValue w op [a, b] = S.p.wordResult (op.eval w x y) := by
                simp only [Src.Program.wordValue, har, bne_self_eq_false, Bool.false_eq_true,
                  ↓reduceIte, hx, hy]
              cases hdec : op.isDecision
              · have hv := vr_word rfl hu hx ha
                have hv₂ := vr_word rfl hu hy hb
                subst hv hv₂
                exact (wordResult_sim S hu' x y).congr (fun _ => hsrc)
                  (fun _ => primResult_word2 _ har hdec (asWord?_some hx).1 (asWord?_some hy).1)
              · exact (SimUpTo.stuck _).congr (fun _ => hsrc.trans (wordResult_dec _ hdec _ _))
                  (fun _ => rfl)
        · refine (SimUpTo.stuck _).congr (fun _ => ?_) (fun _ => rfl)
          have : (op.arity != 2) = true := by simp [har]
          simp only [Src.Program.wordValue, this, ↓reduceIte]
      | cons _ _ => exact SimUpTo.stuck _

end IxCC.Lam.Erase.Proof
