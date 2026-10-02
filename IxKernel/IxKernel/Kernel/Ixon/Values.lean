import IxKernel.Kernel.MainTheorem
import IxKernel.Kernel.Model.Denotes
import IxKernel.Kernel.Verify.Cached.MainC

/-! # Stored definitions denote their constants

The kernel's public `Model` states types only. Its internal invariant
`EnvModelM` also keeps `defn_reads` (`Model/Annot/EnvModelM.lean`,
`AcvalDefnInst` in `Model/Annot/Laws.lean`): the reading of every stored
definition's value is that constant's own leaf. Read through the kernel's
bridge from the internal reading to the public denotation
(`Model.Denotes_of_denoteMeta`), this gives a model of the accepted
environment in which every stored definition's value denotes the constant
(`checkDecls_model_defn_values`).

The value is the stored one, i.e. the checker's annotation of the declared
value (binder regimes computed, `let` reduced). Theorems and opaques keep
no such equation: their values are opaque to reduction and the invariant
records none (upstream's design, `AcvalDefnInst`'s docstring). -/

namespace Ix.Kernel.Cached

open Ix.Kernel Ix.Kernel.Model

universe w

private theorem fvarsBelow_zero_of_not_hasFvar :
    ∀ {e : Expr}, e.hasFvar = false → Expr.fvarsBelow 0 e := by
  intro e
  induction e <;> simp_all [Expr.fvarsBelow, Expr.hasFvar]

/-- **Model existence with definition values.** Every environment the fold
accepts has a model in which every stored definition's value denotes the
constant, at every level assignment and variable environment. -/
theorem checkDecls_model_defn_values (V : Type w) [SetTheory V] (pins : List NatOpPinSet)
    (ds : Array Declaration) (env : Env)
    (accepted : Cached.checkDecls .verified pins ds = .ok env) :
    ∃ M : Ix.Kernel.Model V env, ∀ (cv : ConstantVal) (value : Expr) (hint : ReducibilityHint),
      ConstantInfo.defnInfo cv value hint ∈ env.consts →
      ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V), Denotes M.cval env φ ρ value (M.cval cv.name φ) := by
  obtain ⟨m⟩ := Cached.checkDecls_sound (V := V) rfl accepted
  refine ⟨Model.ofEnvModelM m, fun cv value hint hmem φ ρ => ?_⟩
  have hr := m.defn_reads φ cv value ⟨hint, hmem⟩
  have hv := ((m.base2.wf _ hmem).2.2.2.2.1 cv value hint rfl)
  have hb := Denotes_of_denoteMeta (V := V) m.base2.cval_closedL 0 value hr
    (fvarsBelow_zero_of_not_hasFvar hv.1) hv.2.2.2 ρ
    ⟨m.base2.acval_wellDenoted _ φ ρ, m.acval_validV _ φ ρ⟩
  rw [Expr.closeN_of_hasFvar _ 0 0 hv.1, interp_cvalOf m.base2.cval_closedL] at hb
  exact hb

end Ix.Kernel.Cached
