import Ix.Cert.ValueRows

/-! # Coherent value transport from a supplied strong target model

This is the strong-model interface of the final compiler statement
(`Ix.Cert.CompileCorrect`). It keeps one source ValueModel for the entire
source environment, at every universe/variable valuation, for EACH supplied
strong target model. Nothing here proves compilation correct. Reading
totality on the closure is a separate conjunct of the final statement
(`Ix.Cert.ReadingCovers`), since a missing reading leaves a constant
unconstrained here. No equivalence with the older weak-model quantifier is
asserted, and the nominal-quotient link supplies no value-transport premise
here.
-/

namespace Ix.Cert
open Ix.Kernel
universe w

def CommutesStrong
    (read : Ix.Kernel.ConstantInfo .source → Option (Ix.Kernel.Expr .anon))
    (source : Env .source) (target : Env .anon) : Prop :=
  ∀ (V : Type w) [SetTheory V] (M : Cached.StrongModel V target),
    ∃ N : ValueModel V source,
      ∀ c ∈ source.consts, ∀ t, read c = some t →
        ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V),
          Denotes M.model.cval target φ ρ t (N.cval c.name φ)

/-- The older predicate implies the intended restriction. This adapter uses
the given strong model's interpretation, never a different target model. -/
theorem Commutes.toStrong {read source target} (h : Commutes.{w} read source target) :
    CommutesStrong.{w} read source target := by
  intro V _ M
  exact ValueRows.commutes_strong h V M

/-- Alias equalities use the SAME source model as all transported constants. -/
theorem CommutesStrong.alias {read source target}
    (h : CommutesStrong.{w} read source target) (V : Type w) [SetTheory V]
    (M : Cached.StrongModel V target) :
    ∃ N : ValueModel V source,
      (∀ c ∈ source.consts, ∀ t, read c = some t → ∀ φ ρ,
        Denotes M.model.cval target φ ρ t (N.cval c.name φ)) ∧
      ∀ a ∈ source.consts, ∀ b ∈ source.consts, ∀ t,
        read a = some t → read b = some t → ∀ φ, N.cval a.name φ = N.cval b.name φ := by
  obtain ⟨N, values⟩ := h V M
  refine ⟨N, values, fun a ha b hb t ra rb φ => ?_⟩
  let ρ : BVarIdx → V := fun _ => SetTheory.univChain 0
  exact Denotes_functional (values a ha t ra φ ρ) (values b hb t rb φ ρ)

/-- Reference acceptance and strong-model commutation at the SAME admitted
target environment and actual artifact reading context. This keeps the
existing closure/binding policy; supported receipts are not silently promoted
to this predicate without their closure/stream correspondence proof. -/
def IxonCommutesStrongRef (ixe : Ixon.Env) (sub : Ix.Environment)
    (source : Env .source) : Prop :=
  ∃ binding, Admission.defaultBinding = .ok binding ∧
    ∃ limits order target cx,
      IxonAcceptsRef binding limits ixe (Seed ixe sub) order target ∧
      admissionContext binding limits ixe order = some cx ∧
      CommutesStrong.{w} (reading ixe cx) source target

/-- Preserve every witness when moving the old executed predicate to the
reference/strong interface. The reverse direction is not claimed. -/
theorem IxonCommutes.toStrongRef (V : Type w) [SetTheory V] {ixe sub source}
    (h : IxonCommutes.{w} ixe sub source) : IxonCommutesStrongRef.{w} ixe sub source := by
  obtain ⟨binding, pinned, limits, order, target, cx, accepted, context, values⟩ := h
  exact ⟨binding, pinned, limits, order, target, cx, ixonAccepts_ref V accepted,
    context, values.toStrong⟩

end Ix.Cert
