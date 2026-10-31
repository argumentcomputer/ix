import Ix.Cert.ValueRows
import Ix.Cert.SourceLaws

/-! # Coherent value transport from a supplied strong target model

This is the strong-model interface of the final compiler statement
(`Ix.Cert.CompileCorrect`). It keeps one source model for the entire
source environment, at every universe/variable valuation, for EACH supplied
strong target model. The source model is a value model with the Source laws
(`LawModel`): definitions denote their values, and the recursor rules and the
capability laws hold (`Ix.Cert.SourceLaws`); theorem and opaque values and the
quotient's computation rule are not required. Nothing here proves compilation
correct. Reading totality on the closure is a separate conjunct of the final
statement (`Ix.Cert.ReadingCovers`), since a missing reading leaves a constant
unconstrained here.

The older weak predicate (`Commutes`: every target value model, some source value
model) does not give this one: its source model need not satisfy the recursor
rules or the capability laws. -/

namespace Ix.Cert
open Ix.Kernel
universe w

/-- **Strong commutation**: for every strong model `M` of the target environment,
one model of the source environment with the Source laws (`LawModel`) in which
every source constant denotes, at every level assignment and variable valuation,
what its reading denotes in `M`. -/
def CommutesStrong
    (read : Ix.Kernel.ConstantInfo .source → Option (Ix.Kernel.Expr .anon))
    (source : Env .source) (target : Env .anon) : Prop :=
  ∀ (V : Type w) [SetTheory V] (M : Cached.StrongModel V target),
    ∃ N : LawModel V source,
      ∀ c ∈ source.consts, ∀ t, read c = some t →
        ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V),
          Denotes M.model.cval target φ ρ t (N.cval c.name φ)

/-- Alias equalities use the SAME source model as all transported constants. -/
theorem CommutesStrong.alias {read source target}
    (h : CommutesStrong.{w} read source target) (V : Type w) [SetTheory V]
    (M : Cached.StrongModel V target) :
    ∃ N : LawModel V source,
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

end Ix.Cert
