import IxVMRefinement.Core.Steps.DefEq
import IxVMRefinement.Core.Open
import IxC.Kernel.Rules.Derived
import IxC.Kernel.Rules.Inversion

/-! # Shared lemmas of the `KernelDefEq` step lemmas

* **Opening a binder for a comparison.** IxVM compares two binder bodies under the context list
  with the *left* domain pushed (`Cons(ty_a, types)`). That list is a context list one depth
  further in, under the ghost context extended by the left domain (`types_store_cons`), and a
  body under one local binder reads there as its instantiation at the new opened variable
  (`tmk_open`).
* **Binder congruence from bodies opened under the left domain** (`defEq_lam_left`,
  `defEq_forallE_left`): the rules open under the right domain, so the comparison is turned
  around by `DefEq.symm`. Both data are `bmeta` of the stored levels (the default contracts), so
  only the zero-ness of the two levels is compared.
* **The images two comparisons equate**: equal variables (`bvar_images_eq`), sorts at levels
  `level_equal` accepts (`lvEq_of_levelEqual`), literals of equal data (`lit_images_eq`).
* Reduction under a spine (`red_mkAppN_fn`), and the yes/no answers read off exact specs
  (`of_ite_field_ne_zero`). -/

namespace IxVM.Refinement.Core.DefEqAux

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.KernelLevels (RepKLevel)
open Ix.Kernel.Rules (Red DefEq DefEqList)

set_option linter.unusedVariables false

/-! ## Answers -/

/-- An exact yes/no answer other than `0` is a yes. -/
theorem of_ite_field_ne_zero {p : Prop} [Decidable p] {r : SourceValue F}
    (hr : r = .field (if p then 1 else 0)) (hne : r ≠ .field 0) : p := by
  by_contra hp
  rw [ite_eq_right hp] at hr
  exact hne hr

/-- Two fields whose difference is `0` are equal. -/
theorem eq_of_sub_field {x y : SourceValue F} (h : evalBinOp .sub x y = .ok (.field 0)) :
    ∃ i : F, x = .field i ∧ y = .field i := by
  obtain ⟨a, b, rfl, rfl, hr⟩ := evalBinOp_sub_inv' h
  injection hr with hr
  exact ⟨a, rfl, by rw [sub_eq_zero.mp hr.symm]⟩

/-! ## The ghost context and the context list -/

/-- **The context list reads the ghost context below its depth only.** -/
theorem typesRep_congr_ghost {κ : _root_.Address → KKey} {Γ Γ' : Nat → KExpr} {h : Heap F}
    {d : Nat} {p : SourceValue F} (r : TypesRep κ Γ h d p) :
    (∀ j, j < d → Γ' j = Γ j) → TypesRep κ Γ' h d p := by
  induction r with
  | nil cell => intro _; exact .nil cell
  | @cons d addr tp rest cell rt _ ih =>
    intro hΓ
    have e : Γ' d = Γ d := hΓ d (by omega)
    refine .cons cell ?_ (ih fun j hj => hΓ j (by omega))
    rw [e]
    exact rt.congr_ghost fun j hj => hΓ j (by omega)

/-- **Pushing the left domain**: the context list with a represented domain pushed (the `Cons`
cell IxVM stores at the end of the heap) is a context list one depth further in, under the
ghost context giving the new opened variable that domain, which stays scoped. -/
theorem types_store_cons {c : Ctx} {Γ : Nat → KExpr} {h : Heap F} {d : Nat}
    {types ta : SourceValue F} {TA : KExpr} (ht : c.types Γ h d types) (hTA : c.tm d Γ h TA ta) :
    c.types (Ghost.extend Γ d TA) (h ++ [.construct kexprListEnum "Cons" [ta, types]]) (d + 1)
      (.ptr (.enum kexprListEnum) h.length) := by
  have ext : Heap.Extends h (h ++ [.construct kexprListEnum "Cons" [ta, types]]) :=
    Heap.Extends.snoc _ _
  refine ⟨TypesRep.cons (tp := ta) (rest := types) (by simp) ?_ ?_,
    GhostScoped.extend ht.2 (Tm.wscopedB ht.2 hTA)⟩
  · rw [Ghost.extend_at]
    exact (Tm.mono ext hTA).congr_ghost (Ghost.extend_below Γ d TA)
  · exact typesRep_congr_ghost (ht.1.mono ext) (Ghost.extend_below Γ d TA)

/-- **A body read under the opened variable**: a term under one local binder at depth `d` reads,
one depth further in under the extended ghost context, as its instantiation at `.fvar d T`. -/
theorem tmk_open {c : Ctx} {d : Nat} {Γ : Nat → KExpr} {h : Heap F} {T B : KExpr}
    {p : SourceValue F} (hB : c.tmk d Γ 1 h B p) :
    c.tm (d + 1) (Ghost.extend Γ d T) h (B.instantiate1 (.fvar d T)) p :=
  Tm.open_body (Ghost.extend_at Γ d T) (Ghost.extend_below Γ d T) hB

/-- A term at depth `d` reads the same under the ghost context extended at `d`. -/
theorem tm_extend {c : Ctx} {d : Nat} {Γ : Nat → KExpr} {h : Heap F} {k : Nat} {T E : KExpr}
    {p : SourceValue F} (hE : c.tmk d Γ k h E p) : c.tmk d (Ghost.extend Γ d T) k h E p :=
  hE.congr_ghost (Ghost.extend_below Γ d T)

/-- The context list at depth `d` reads the same under the ghost context extended at `d`. -/
theorem types_extend {c : Ctx} {d : Nat} {Γ : Nat → KExpr} {h : Heap F} {T : KExpr}
    {types : SourceValue F} (ht : c.types Γ h d types) (hT : T.wscopedB d = true) :
    TypesRep c.κ (Ghost.extend Γ d T) h d types ∧ GhostScoped (Ghost.extend Γ d T) d :=
  ⟨typesRep_congr_ghost ht.1 (Ghost.extend_below Γ d T),
    fun j hj => by rw [Ghost.extend_below Γ d T j hj]; exact ht.2 j hj⟩

/-! ## Binder congruence -/

/-- **λ-congruence from bodies opened under the left domain** (`DefEq.lam` by symmetry: the rule
opens under the right domain). The data are `bmeta` of the two stored levels. -/
theorem defEq_lam_left {env : Ix.Kernel.Env .anon} {d : Nat} {TA BA TB BB : KExpr}
    {ℓa ℓb : KLevel} (hT : DefEq env d TA TB)
    (hB : DefEq env (d + 1) (BA.instantiate1 (.fvar d TA)) (BB.instantiate1 (.fvar d TA)))
    (hz : ℓa.zeronessOf = ℓb.zeronessOf) :
    DefEq env d (.lam TA BA (bmeta ℓa)) (.lam TB BB (bmeta ℓb)) :=
  .symm (.lam (.symm hT) (.symm hB) (by unfold bmeta; exact hz.symm) rfl)

/-- **∀-congruence from bodies opened under the left domain** (`DefEq.forallE` by symmetry). -/
theorem defEq_forallE_left {env : Ix.Kernel.Env .anon} {d : Nat} {TA BA TB BB : KExpr}
    {ℓa ℓb : KLevel} (hT : DefEq env d TA TB)
    (hB : DefEq env (d + 1) (BA.instantiate1 (.fvar d TA)) (BB.instantiate1 (.fvar d TA)))
    (hz : ℓa.zeronessOf = ℓb.zeronessOf) :
    DefEq env d (.forallE TA BA (bmeta ℓa)) (.forallE TB BB (bmeta ℓb)) :=
  .symm (.forallE (.symm hT) (.symm hB) (by unfold bmeta; exact hz.symm) rfl)

/-! ## The images two comparisons equate -/

/-- **Equal variables have equal images** (at local depth `0` every variable is an opened one,
whose image is determined by its index). -/
theorem bvar_images_eq {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h h' : Heap F}
    {E E' : KExpr} {p p' x y : SourceValue F} (hE : Tm κ d Γ h 0 E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "BVar" [x])) (hE' : Tm κ d Γ h' 0 E' p')
    (hl' : loadValue h' p' = .ok (.construct kexprEnum "BVar" [y])) (hxy : x = y) : E = E' := by
  subst hxy
  obtain ⟨i, rfl, -, hi⟩ := hE.bvar_of_load hl
  obtain ⟨i', hi', -, hj⟩ := hE'.bvar_of_load hl'
  injection hi' with e
  subst e
  rcases hi with ⟨hlt, -⟩ | ⟨-, -, rfl⟩
  · omega
  rcases hj with ⟨hlt, -⟩ | ⟨-, -, rfl⟩
  · omega
  rfl

/-- **Levels `level_equal` accepts are semantically equal**, up to the term seam's semantic
reading of each side. -/
theorem lvEq_of_levelEqual {u v lu lv : KLevel} (hu : LvEq u lu) (hv : LvEq v lv)
    (he : IxVM.Refinement.KernelLevels.levelEqual lu lv = true) : LvEq u v :=
  fun φ => (hu φ).trans
    ((IxVM.Refinement.KernelLevels.levelEqual_eq_true_sound he φ).trans (hv φ).symm)

/-- A literal's data read as one kernel literal only. -/
theorem litReads_det {ld : Specs.Levels.LitData} {l l' : Ix.Kernel.Literal}
    (h : ld.Reads l) (h' : ld.Reads l') : l = l' := by
  cases ld with
  | nat limbs =>
    simp only [Specs.Levels.LitData.Reads] at h h'
    exact h.trans h'.symm
  | str bytes =>
    simp only [Specs.Levels.LitData.Reads] at h h'
    obtain ⟨s, hs, rfl⟩ := h
    obtain ⟨s', hs', rfl⟩ := h'
    unfold StrBytes at hs hs'
    rw [hs] at hs'
    injection hs' with e
    rw [e]

/-- **A literal node's data**: the literal it holds (`LitRep`, what `literal_eq` reads) and the
kernel literal that data reads as, the image. -/
theorem tm_lit_data {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h : Heap F}
    {k : Nat} {E : KExpr} {p x : SourceValue F} (hE : Tm κ d Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "Lit" [x])) :
    ∃ ld, Specs.Levels.LitRep h ld x ∧ ∃ l, ld.Reads l ∧ E = .lit l := by
  rcases hE.lit_of_load hl with ⟨lp, limbs, rfl, hr, -, rfl⟩ | ⟨bp, bytes, s, rfl, hb, hs, rfl⟩
  · refine ⟨.nat limbs, ?_, .natVal (limbsVal limbs), ?_, rfl⟩
    · simp only [Specs.Levels.LitRep]; exact ⟨lp, rfl, hr⟩
    · simp only [Specs.Levels.LitData.Reads]
  · refine ⟨.str bytes, ?_, .strVal s, ?_, rfl⟩
    · simp only [Specs.Levels.LitRep]; exact ⟨bp, rfl, hb⟩
    · simp only [Specs.Levels.LitData.Reads]; exact ⟨s, hs, rfl⟩

/-- One literal value holds one datum. -/
theorem litRep_det {h : Heap F} {v : SourceValue F} {a b : Specs.Levels.LitData}
    (ha : Specs.Levels.LitRep h a v) (hb : Specs.Levels.LitRep h b v) : a = b := by
  cases a with
  | nat la =>
    cases b with
    | nat lb =>
      simp only [Specs.Levels.LitRep] at ha hb
      obtain ⟨p, rfl, ra⟩ := ha
      obtain ⟨q, hq, rb⟩ := hb
      injection hq with _ _ hq'
      injection hq' with e
      subst e
      rw [limbsVal_det ra rb]
    | str _ =>
      simp only [Specs.Levels.LitRep] at ha hb
      obtain ⟨p, rfl, -⟩ := ha
      obtain ⟨q, hq, -⟩ := hb
      injection hq with _ hc
      exact absurd hc (by decide)
  | str ba =>
    cases b with
    | nat _ =>
      simp only [Specs.Levels.LitRep] at ha hb
      obtain ⟨p, rfl, -⟩ := ha
      obtain ⟨q, hq, -⟩ := hb
      injection hq with _ hc
      exact absurd hc (by decide)
    | str bb =>
      simp only [Specs.Levels.LitRep] at ha hb
      obtain ⟨p, rfl, ra⟩ := ha
      obtain ⟨q, hq, rb⟩ := hb
      injection hq with _ _ hq'
      injection hq' with e
      subst e
      rw [bytes_det ra rb]

/-- **Literals of equal data have equal images.** -/
theorem lit_images_eq {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr} {h h' : Heap F}
    {k : Nat} {E E' : KExpr} {p p' x y : SourceValue F} {ld ld' : Specs.Levels.LitData}
    (hE : Tm κ d Γ h k E p) (hl : loadValue h p = .ok (.construct kexprEnum "Lit" [x]))
    (hE' : Tm κ d Γ h' k E' p') (hl' : loadValue h' p' = .ok (.construct kexprEnum "Lit" [y]))
    (hx : Specs.Levels.LitRep h ld x) (hy : Specs.Levels.LitRep h' ld' y) (heq : ld = ld') :
    E = E' := by
  subst heq
  obtain ⟨ld1, h1, l1, hr1, rfl⟩ := tm_lit_data hE hl
  obtain ⟨ld2, h2, l2, hr2, rfl⟩ := tm_lit_data hE' hl'
  have e1 : ld1 = ld := litRep_det h1 hx
  have e2 : ld2 = ld := litRep_det h2 hy
  subst e1 e2
  rw [litReads_det hr1 hr2]

/-! ## Reduction under a spine -/

/-- **Reduction of the head of a spine** (`Red.appFn`, once per argument). -/
theorem red_mkAppN_fn {env : Ix.Kernel.Env .anon} {d : Nat} :
    ∀ (As : List KExpr) {H H' : KExpr}, Red env d H H' →
      Red env d (Ix.Kernel.Expr.mkAppN H As) (Ix.Kernel.Expr.mkAppN H' As)
  | [], _, _, hr => hr
  | _ :: As, _, _, hr => red_mkAppN_fn As (.appFn hr)

end IxVM.Refinement.Core.DefEqAux
