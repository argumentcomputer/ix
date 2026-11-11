import IxC.Kernel.Denotes
import IxC.Kernel.Semantics.EnvFacts

/-! # The model's laws rule out wrong meanings

`Ix.Kernel.Model` asks more of an interpretation than that every stored
constant inhabit its type: a stored definition must denote what its value
denotes (`Model.defn_value`). Without that law, an environment with

```
def P : Prop := False
theorem bad : P := True.intro
```

would have a model, one in which `P` is true, even though Lean reads `P` as
`False`; so a checker that wrongly accepted `bad` would still be called
consistent. With the law it has none (`no_model_of_false_def`): whatever else
the environment holds and whatever `bad`'s stored value is, `P` denotes what
`False` denotes, the empty set, and `bad` cannot be a member of it. -/

namespace Tests.Ix.Kernel.ModelLaws

open Ix.Kernel SetTheory

universe w

variable {md : Mode} {V : Type w} [SetTheory V]

/-- **A definition of `False` has no model with an inhabitant.** In an
environment that stores `def P : Prop := False` (any reducibility hint) and a
theorem of type `P` (any value), there is no model. -/
theorem no_model_of_false_def {env : Env md} {P bad : Key md} {cvP cvB : ConstantVal md}
    {hint : ReducibilityHint} {v : Expr md}
    (hP : env.find? P = some (.defnInfo cvP (.const falseName []) hint))
    (hbad : env.find? bad = some (.thmInfo cvB v))
    (hty : cvB.type = .const P []) :
    Model V env → False := by
  intro M
  have hPname : cvP.name = P := Ix.Kernel.Semantics.Env.find?_name hP
  obtain ⟨T, hT, hmem⟩ :=
    M.mem _ (Ix.Kernel.Semantics.Env.find?_mem hbad) (fun _ => 0) (fun _ => empty)
  change Denotes M.cval env (fun _ => 0) (fun _ => empty) cvB.type T at hT
  rw [hty] at hT
  cases hT with
  | const hf _ =>
    rw [hP] at hf
    cases hf
    -- `P`'s value is `False`, which denotes the empty set
    have hval := M.defn_value cvP _ hint (Ix.Kernel.Semantics.Env.find?_mem hP)
      (Level.substFn (fun _ => 0) cvP.levelParams []) (fun _ => empty)
    have hempty : M.cval cvP.name (Level.substFn (fun _ => 0) cvP.levelParams []) = empty :=
      M.false_empty _ _ _ hval
    rw [hPname] at hempty
    have hmem' : M.cval cvB.name (fun _ => 0)
        ∈ˢ M.cval P (Level.substFn (fun _ => 0) cvP.levelParams []) := hmem
    rw [hempty] at hmem'
    exact not_mem_empty _ hmem'

end Tests.Ix.Kernel.ModelLaws
