import IxCC.Src.KernelFront.Annotate

/-! # The kernel annotator's classes, as the kernel's answers

The kernel front end's annotator classifies a position by asking the cached
kernel core four questions (`Ctx.classifyTerm`): the annotation pass on the
position's term, inference of its type, inference of that type's type, and
weak head normalisation of the result. These lemmas say, at one position and
in both directions, that a `proof` class is exactly the zero condition of the
sort those runs give:

* **a class is the kernel's answer**: a `proof w` class comes from successful
  runs ending in `Sort u` with `w` the zero condition of `u`
  (`classifyTerm_proof`, `classifyType_proof`);
* **the kernel's answer is the class**: such runs, with `u` zero under some
  condition, give that class (`classifyTerm_of_runs`, `classifyType_of_runs`).

They are about the executed core's runs. With the kernel's simulation of the
specification by the cached core (`Ix.Kernel.Cached.ssimC`) and its bridge from
an accepting run to a derivation (`Ix.Kernel.Rules.inferTypeCore_bridge`,
`whnf_bridge`), the runs are derivations of the relational judgements, which
are sound in every model meeting `RulesInputs` (`IxCC/docs/kernel-front-end-design.md`,
"Statements"). -/

namespace IxCC.Src.KernelFront

open IxCC.Src

/-- A condition other than `never` is the zero condition of a level that is
zero under it. -/
theorem condOfLevel_ne_never {back : Nat → Nat} {u : KLevel} :
    condOfLevel back u ≠ .never ↔ (zeroCond u).isSome := by
  unfold condOfLevel
  cases zeroCond u <;> simp

/-- **A sort condition is the kernel's**: a condition other than `never` comes
from inference of the type's type and its reduction to `Sort u`, and is `u`'s
zero condition. -/
theorem Ctx.sortCond_spec {k : Ctx} {d : Nat} {ty : KTerm} {s s' : Ix.Kernel.Cached.CState .anon}
    {w : PropWhen} (h : k.sortCond d ty s = .ok (w, s')) (hw : w ≠ .never) :
    ∃ t s₁ u, k.core.infer d ty s = .ok (t, s₁) ∧ k.core.whnf d t s₁ = .ok (.sort u, s') ∧
      condOfLevel k.back u = w := by
  unfold Ctx.sortCond at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact absurd h.1.symm hw
  · rename_i t s₁ hi
    split at h
    · rename_i u s₂ hs
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨t, s₁, u, hi, hs, rfl⟩
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact absurd h.1.symm hw
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact absurd h.1.symm hw

/-- **The kernel's sort is the condition**: inference of the type's type and
its reduction to `Sort u` give `u`'s zero condition. -/
theorem Ctx.sortCond_of_runs {k : Ctx} {d : Nat} {ty t : KTerm} {u : KLevel}
    {s s₁ s₂ : Ix.Kernel.Cached.CState .anon}
    (hi : k.core.infer d ty s = .ok (t, s₁)) (hs : k.core.whnf d t s₁ = .ok (.sort u, s₂)) :
    k.sortCond d ty s = .ok (condOfLevel k.back u, s₂) := by
  unfold Ctx.sortCond
  simp only [hi, hs]

/-- A `proof` class of an annotated type is its sort condition. -/
theorem Ctx.classifyAnnotated_proof {k : Ctx} {d : Nat} {ty : KTerm}
    {s s' : Ix.Kernel.Cached.CState .anon} {w : PropWhen}
    (h : k.classifyAnnotated d ty s = .ok (.proof w, s')) :
    k.sortCond d ty s = .ok (w, s') ∧ w ≠ .never := by
  unfold Ctx.classifyAnnotated at h
  split at h
  · cases h
  · rename_i w' s₁ hs
    split at h
    · split at h <;> simp at h
    · rename_i hne
      simp only [Except.ok.injEq, Prod.mk.injEq, Rel.proof.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hs, hne⟩

/-- A sort condition other than `never` is the class. -/
theorem Ctx.classifyAnnotated_of_sortCond {k : Ctx} {d : Nat} {ty : KTerm}
    {s s' : Ix.Kernel.Cached.CState .anon} {w : PropWhen}
    (h : k.sortCond d ty s = .ok (w, s')) (hw : w ≠ .never) :
    k.classifyAnnotated d ty s = .ok (.proof w, s') := by
  unfold Ctx.classifyAnnotated
  simp only [h, hw, ↓reduceIte]

/-- **A position's `proof` class is the kernel's answer**: the annotation
pass gives the position's annotated term `e'`, inference its type `t`,
inference `t`'s type `ty` and reduction `Sort u`, and the class's condition is
`u`'s zero condition, which is not `never`. -/
theorem Ctx.classifyTerm_proof {k : Ctx} {d : Nat} {e : KTerm}
    {s s' : Ix.Kernel.Cached.CState .anon} {w : PropWhen}
    (h : k.classifyTerm d e s = .ok (.proof w, s')) :
    ∃ e' s₁ t s₂ ty s₃ u,
      k.core.annotate d e s = .ok (e', s₁) ∧ k.core.infer d e' s₁ = .ok (t, s₂) ∧
      k.core.infer d t s₂ = .ok (ty, s₃) ∧ k.core.whnf d ty s₃ = .ok (.sort u, s') ∧
      condOfLevel k.back u = w ∧ (zeroCond u).isSome := by
  unfold Ctx.classifyTerm at h
  split at h
  · cases h
  · rename_i e' s₁ ha
    split at h
    · cases h
    · rename_i t s₂ hi
      obtain ⟨hs, hw⟩ := Ctx.classifyAnnotated_proof h
      obtain ⟨ty, s₃, u, hi', hw', rfl⟩ := Ctx.sortCond_spec hs hw
      exact ⟨e', s₁, t, s₂, ty, s₃, u, ha, hi, hi', hw', rfl, condOfLevel_ne_never.mp hw⟩

/-- **The kernel's answer is the position's class**: when the runs succeed
with `Sort u` and `u` is zero under some condition, the position's class is
`proof` under that condition. -/
theorem Ctx.classifyTerm_of_runs {k : Ctx} {d : Nat} {e e' t ty : KTerm} {u : KLevel}
    {s s₁ s₂ s₃ s₄ : Ix.Kernel.Cached.CState .anon}
    (ha : k.core.annotate d e s = .ok (e', s₁)) (hi : k.core.infer d e' s₁ = .ok (t, s₂))
    (hi' : k.core.infer d t s₂ = .ok (ty, s₃)) (hw : k.core.whnf d ty s₃ = .ok (.sort u, s₄))
    (hz : (zeroCond u).isSome) :
    k.classifyTerm d e s = .ok (.proof (condOfLevel k.back u), s₄) := by
  unfold Ctx.classifyTerm
  simp only [ha, hi]
  exact Ctx.classifyAnnotated_of_sortCond (Ctx.sortCond_of_runs hi' hw)
    (condOfLevel_ne_never.mpr hz)

/-- **A binder's or let's `proof` class is the kernel's answer**: the same, for
a position whose type is the read term `ty` (the annotation pass gives the
annotated type, whose type inference and reduction give `Sort u`). -/
theorem Ctx.classifyType_proof {k : Ctx} {d : Nat} {ty : KTerm}
    {s s' : Ix.Kernel.Cached.CState .anon} {w : PropWhen}
    (h : k.classifyType d ty s = .ok (.proof w, s')) :
    ∃ ty' s₁ t s₂ u,
      k.core.annotate d ty s = .ok (ty', s₁) ∧ k.core.infer d ty' s₁ = .ok (t, s₂) ∧
      k.core.whnf d t s₂ = .ok (.sort u, s') ∧
      condOfLevel k.back u = w ∧ (zeroCond u).isSome := by
  unfold Ctx.classifyType at h
  split at h
  · cases h
  · rename_i ty' s₁ ha
    obtain ⟨hs, hw⟩ := Ctx.classifyAnnotated_proof h
    obtain ⟨t, s₂, u, hi, hw', rfl⟩ := Ctx.sortCond_spec hs hw
    exact ⟨ty', s₁, t, s₂, u, ha, hi, hw', rfl, condOfLevel_ne_never.mp hw⟩

/-- **The kernel's answer is the binder's class.** -/
theorem Ctx.classifyType_of_runs {k : Ctx} {d : Nat} {ty ty' t : KTerm} {u : KLevel}
    {s s₁ s₂ s₃ : Ix.Kernel.Cached.CState .anon}
    (ha : k.core.annotate d ty s = .ok (ty', s₁)) (hi : k.core.infer d ty' s₁ = .ok (t, s₂))
    (hw : k.core.whnf d t s₂ = .ok (.sort u, s₃)) (hz : (zeroCond u).isSome) :
    k.classifyType d ty s = .ok (.proof (condOfLevel k.back u), s₃) := by
  unfold Ctx.classifyType
  simp only [ha]
  exact Ctx.classifyAnnotated_of_sortCond (Ctx.sortCond_of_runs hi hw)
    (condOfLevel_ne_never.mpr hz)

end IxCC.Src.KernelFront
