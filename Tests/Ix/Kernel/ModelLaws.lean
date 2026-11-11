import IxC.Kernel.Denotes
import IxC.Kernel.Semantics.EnvFacts
import Ix.IxVM.Consistency.Restrict

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

open _root_.Ix.Kernel _root_.Ix.Kernel.SetTheory

namespace Tests.Ix.Kernel.ModelLaws

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
  have hPname : cvP.name = P := _root_.Ix.Kernel.Semantics.Env.find?_name hP
  obtain ⟨T, hT, hmem⟩ :=
    M.mem _ (_root_.Ix.Kernel.Semantics.Env.find?_mem hbad) (fun _ => 0) (fun _ => empty)
  change Denotes M.cval env (fun _ => 0) (fun _ => empty) cvB.type T at hT
  rw [hty] at hT
  cases hT with
  | const hf _ =>
    rw [hP] at hf
    cases hf
    -- `P`'s value is `False`, which denotes the empty set
    have hval := M.defn_value cvP _ hint (_root_.Ix.Kernel.Semantics.Env.find?_mem hP)
      (Level.substFn (fun _ => 0) cvP.levelParams []) (fun _ => empty)
    have hempty : M.cval cvP.name (Level.substFn (fun _ => 0) cvP.levelParams []) = empty :=
      M.false_empty _ _ _ hval
    rw [hPname] at hempty
    have hmem' : M.cval cvB.name (fun _ => 0)
        ∈ˢ M.cval P (Level.substFn (fun _ => 0) cvP.levelParams []) := hmem
    rw [hempty] at hmem'
    exact not_mem_empty _ hmem'

/--
info: 'Tests.Ix.Kernel.ModelLaws.no_model_of_false_def' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms no_model_of_false_def

/-! ## Stated over what the consistency statement gives

`IxVM.Consistency.ConsistentRead` does not hand over lookups: it gives the reader's
declarations `ds`, an environment they install (`Installs`, each constant stored as
declared, `StoredAs`), and a model of its claimed sub-environment. The examples below are
stated over those. -/

open _root_.IxVM.Consistency in
/-- **Declarations that define `P : Prop` as `False` and prove `P` install no environment
with a model.** If `ds` installs `env`, `ds` holds `def P : Prop := False` and a theorem
of type `P`, and both are at input or role keys, then the claimed sub-environment of `env`
has no model: both are stored as declared, so δ reads `P`'s own value. -/
theorem no_model_of_false_def_installs {ds : List (Declaration .anon)} {env : Env .anon}
    (hI : Installs ds env) {cvP cvB : ConstantVal .anon} {hint : ReducibilityHint}
    {v : Expr .anon}
    (hP : .defnDecl cvP (.const falseName []) hint ∈ ds) (hB : .thmDecl cvB v ∈ ds)
    (hty : cvB.type = .const cvP.name [])
    (hPk : ∀ b t, cvP.name ≠ .aux b t) (hBk : ∀ b t, cvB.name ≠ .aux b t) :
    Model V (claimedEnv env) → False := by
  obtain ⟨ciP, hfP, hsP⟩ :=
    hI.claimed hP (ci₀ := .defnInfo cvP (.const falseName []) hint) (List.mem_singleton_self _) hPk
  obtain ⟨ciB, hfB, hsB⟩ := hI.claimed hB (ci₀ := .thmInfo cvB v) (List.mem_singleton_self _) hBk
  cases ciP with
  | defnInfo cvP' vP hP' =>
    obtain ⟨hav, rfl⟩ := hsP.2
    obtain rfl := hav.const_inv
    cases ciB with
    | thmInfo cvB' vB =>
      have hann : Annotates cvB'.type cvB.type := hsB.1.2.2
      rw [hty] at hann
      exact no_model_of_false_def (P := cvP.name) (bad := cvB.name) hfP hfB hann.const_inv
    | _ => exact False.elim hsB.2
  | _ => exact False.elim hsP.2

open _root_.IxVM.Consistency in
/-- **No `ConsistentRead` reads `def P : Prop := False` with a theorem of type `P`**: in
every set theory, the reading a `ConsistentRead` exhibits holds no such pair at input or
role keys. -/
theorem consistentRead_no_false_def (V : Type w) [SetTheory V]
    {calls : List (Aiur.Generic.SourceSemantics.Call IxVM.F)} {seeds : List _root_.Address}
    (h : ConsistentRead.{w} calls seeds) :
    ∃ (b : _root_.Ix.Kernel.Admission.Binding) (E : _root_.Ixon.Env) (ev : Evidences .anon)
      (ds : Array (Declaration .anon)),
      ReadIn b E (fun a => a ∈ seeds) ev ds ∧
      ∀ (cvP cvB : ConstantVal .anon) (hint : ReducibilityHint) (v : Expr .anon),
        .defnDecl cvP (.const falseName []) hint ∈ ds.toList → .thmDecl cvB v ∈ ds.toList →
        cvB.type = .const cvP.name [] → (∀ b t, cvP.name ≠ .aux b t) →
        (∀ b t, cvB.name ≠ .aux b t) → False := by
  obtain ⟨b, -, E, ev, ds, env, -, -, -, hread, hI, -, hmodel⟩ := h
  obtain ⟨M⟩ := hmodel V
  exact ⟨b, E, ev, ds, hread, fun _ _ _ _ hP hB hty hPk hBk =>
    no_model_of_false_def_installs hI hP hB hty hPk hBk M⟩

/--
info: 'Tests.Ix.Kernel.ModelLaws.consistentRead_no_false_def' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms consistentRead_no_false_def

end Tests.Ix.Kernel.ModelLaws
