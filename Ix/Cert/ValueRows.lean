import Ix.Cert.Quotient

/-! # Strong value models and the meaning of equation rows

A strong target model supplies a ValueModel at the very same interpretation.
An actual stored equation gives equal values under even the public Model,
whose Eq law is already explicit. The endpoint denotations and their common
type's universe/membership facts remain explicit local inputs; neither an
arbitrary well-typed target nor an unrelated row proves a compiler rewrite.
-/

namespace Ix.Cert.ValueRows

open Ix.Kernel Ix.Kernel.SetTheory

universe w
variable {md : Mode}

/-- The strong model's own public interpretation satisfies definition values.
This constructs no new interpretation and promotes no arbitrary ValueModel. -/
noncomputable def ofStrong {V : Type w} [SetTheory V] {env : Env md}
    (M : Cached.StrongModel V env) : ValueModel V env :=
  { M.model with defn_value := fun _ _ _ h φ ρ => M.defn_value h φ ρ }

theorem ofStrong_cval {V : Type w} [SetTheory V] {env : Env md}
    (M : Cached.StrongModel V env) : (ofStrong M).cval = M.model.cval := rfl

/-- Reference admission supplies the strong model in the proposed compiler
contract, relative to the already explicit set-theory model. -/
theorem strongModel_of_acceptsRef (V : Type w) [SetTheory V]
    {binding : Ix.Kernel.Admission.Binding} {limits : Ix.Kernel.Admission.Limits}
    {ixe : Ixon.Env} {seeds : Address → Prop}
    {order : List Address} {envA : Env .anon}
    (accepted : IxonAcceptsRef binding limits ixe seeds order envA) :
    Nonempty (Cached.StrongModel V envA) := by
  obtain ⟨_, _, _, _, _, _, _, _, run⟩ := accepted
  exact run.strongModel V

/-- The older every-ValueModel statement implies its intended restriction
to every strong target model. No reverse implication is asserted. -/
theorem commutes_strong {τ : Ix.Kernel.ConstantInfo .source → Option (Ix.Kernel.Expr .anon)}
    {envQ : Env .source} {envA : Env .anon} (h : Commutes.{w} τ envQ envA)
    (V : Type w) [SetTheory V] (M : Cached.StrongModel V envA) :
    ∃ N : ValueModel V envQ, ∀ c ∈ envQ.consts, ∀ t, τ c = some t →
      ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V),
        Denotes M.model.cval envA φ ρ t (N.cval c.name φ) :=
  h V (ofStrong M)

/-- The exact Eq spine a row must declare. Its universe, type and both
endpoints are part of the predicate, not recovered from a display name. -/
def equationType (u : Ix.Kernel.Level) (type lhs rhs : Ix.Kernel.Expr md) : Ix.Kernel.Expr md :=
  .app (.app (.app (.const eqName [u]) type) lhs) rhs

section Equation

variable {V : Type w} [SetTheory V] {env : Env md}
  {φ : LevelParam → Nat} {ρ : BVarIdx → V}
  {u : Ix.Kernel.Level} {type lhs rhs : Ix.Kernel.Expr md}

/-- Inverting the precise row spine preserves the denotations actually used
by the row's type, including all three argument values. -/
theorem equation_denotes_inv
    {cval : Key md → (LevelParam → Nat) → V} {R : V}
    (h : Denotes cval env φ ρ (equationType u type lhs rhs) R) :
    ∃ E A a b, Denotes cval env φ ρ (.const eqName [u]) E ∧
      Denotes cval env φ ρ type A ∧ Denotes cval env φ ρ lhs a ∧
      Denotes cval env φ ρ rhs b ∧ R = app (app (app E A) a) b := by
  cases h with
  | app h₁ hb =>
    cases h₁ with
    | app h₂ ha =>
      cases h₂ with
      | app hE hA => exact ⟨_, _, _, _, hE, hA, ha, hb, rfl⟩

/-- An actual stored row with the exact equation type equates its endpoints.
Universe and membership premises are the domains of Model.eq_equality;
dropping them would assert equality outside the Eq graph's domain. -/
theorem equation_values (M : Ix.Kernel.Model V env)
    {row : Ix.Kernel.ConstantInfo md} (stored : row ∈ env.consts)
    (shape : row.toConstantVal.type = equationType u type lhs rhs)
    {A a b : V} (ht : Denotes M.cval env φ ρ type A)
    (hl : Denotes M.cval env φ ρ lhs a) (hr : Denotes M.cval env φ ρ rhs b)
    (hA : A ∈ˢ univ (Level.eval φ u)) (ha : a ∈ˢ A) (hb : b ∈ˢ A) : a = b := by
  obtain ⟨R, hR, member⟩ := M.mem row stored φ ρ
  rw [shape] at hR
  obtain ⟨E, A', a', b', hE, ht', hl', hr', rfl⟩ := equation_denotes_inv hR
  have et : A' = A := Denotes_functional ht' ht
  have el : a' = a := Denotes_functional hl' hl
  have er : b' = b := Denotes_functional hr' hr
  subst A'; subst a'; subst b'
  rw [M.eq_equality u φ ρ E A a b hE hA ha hb] at member
  exact mem_eqv member

/-- Lookup in the accepted environment, rather than metadata, supplies the
row constant. No injectivity assumption about row names or addresses occurs. -/
theorem stored_equation_values (M : Ix.Kernel.Model V env)
    {key : Key md} {row : Ix.Kernel.ConstantInfo md}
    (stored : env.find? key = some row)
    (shape : row.toConstantVal.type = equationType u type lhs rhs)
    {A a b : V} (ht : Denotes M.cval env φ ρ type A)
    (hl : Denotes M.cval env φ ρ lhs a) (hr : Denotes M.cval env φ ρ rhs b)
    (hA : A ∈ˢ univ (Level.eval φ u)) (ha : a ∈ˢ A) (hb : b ∈ˢ A) : a = b :=
  equation_values M (List.mem_of_find?_eq_some stored) shape ht hl hr hA ha hb

/-- The same result at the strong model's SAME public interpretation. It
uses no choice of a second model for the row or either endpoint. -/
theorem strong_equation_values (M : Cached.StrongModel V env)
    {key : Key md} {row : Ix.Kernel.ConstantInfo md}
    (stored : env.find? key = some row)
    (shape : row.toConstantVal.type = equationType u type lhs rhs)
    {A a b : V} (ht : Denotes M.model.cval env φ ρ type A)
    (hl : Denotes M.model.cval env φ ρ lhs a) (hr : Denotes M.model.cval env φ ρ rhs b)
    (hA : A ∈ˢ univ (Level.eval φ u)) (ha : a ∈ˢ A) (hb : b ∈ˢ A) : a = b :=
  stored_equation_values M.model stored shape ht hl hr hA ha hb

/-- A row whose right endpoint is the published constant equates the left
value with that constant at the exact supplied universe arguments. -/
theorem equation_to_constant (M : Ix.Kernel.Model V env)
    {rowKey target : Key md} {row ci : Ix.Kernel.ConstantInfo md}
    (stored : env.find? rowKey = some row) (targetStored : env.find? target = some ci)
    {us : List Ix.Kernel.Level} (arity : us.length = ci.toConstantVal.levelParams.length)
    (shape : row.toConstantVal.type = equationType u type lhs (.const target us))
    {A a : V} (ht : Denotes M.cval env φ ρ type A)
    (hl : Denotes M.cval env φ ρ lhs a)
    (hA : A ∈ˢ univ (Level.eval φ u)) (ha : a ∈ˢ A)
    (hb : M.cval target (Level.substFn φ ci.toConstantVal.levelParams us) ∈ˢ A) :
    a = M.cval target (Level.substFn φ ci.toConstantVal.levelParams us) :=
  stored_equation_values M stored shape ht hl (Denotes.const targetStored arity) hA ha hb

/-- At a stored constant's own level parameters, its actual stored type
discharges the right endpoint's membership. This specializes the previous
leaf without assuming a second interpretation or an external typing oracle. -/
theorem equation_to_stored_constant (M : Ix.Kernel.Model V env)
    {rowKey target : Key md} {row ci : Ix.Kernel.ConstantInfo md}
    (stored : env.find? rowKey = some row) (targetStored : env.find? target = some ci)
    (targetType : ci.toConstantVal.type = type)
    (shape : row.toConstantVal.type = equationType u type lhs
      (.const target (ci.toConstantVal.levelParams.map .param)))
    {A a : V} (ht : Denotes M.cval env φ ρ type A)
    (hl : Denotes M.cval env φ ρ lhs a)
    (hA : A ∈ˢ univ (Level.eval φ u)) (ha : a ∈ˢ A) : a = M.cval target φ := by
  obtain ⟨T, hT, member⟩ := M.mem ci (List.mem_of_find?_eq_some targetStored) φ ρ
  rw [targetType] at hT
  have eqT : T = A := Denotes_functional hT ht
  have name : ci.name = target := Semantics.Env.find?_name targetStored
  rw [eqT, name] at member
  have hconst : Denotes M.cval env φ ρ
      (.const target (ci.toConstantVal.levelParams.map .param)) (M.cval target φ) := by
    have h := Denotes.const (cval := M.cval) (φ := φ) (ρ := ρ)
      (us := ci.toConstantVal.levelParams.map .param) targetStored (by simp)
    simpa only [Level.substFn_param_self] using h
  exact stored_equation_values M stored shape ht hl hconst hA ha member

end Equation

end Ix.Cert.ValueRows
