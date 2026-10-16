import Ix.AuxGen.SourceIdentity

/-!
The recognition check supplies agreement of both declaration skeletons,
including the value: both closed, and equal under `exprEqWith` with
universes by position. It does not establish the generator's laws,
generation totality, publication correctness, or what agreement means in the
source semantic model (an erasure lemma over the statements lane's term
model).
-/

namespace Ix.CompileCert.SourceIdentity

open Ix (Name Expr ConstantInfo DefinitionVal)
open Ix.AuxGen (AuxDef)
open Ix.AuxGen.SourceIdentity

/-- Agreement of the actual skeletons: both sides closed, equal up to binder
presentation, with each universe parameter by its position in its own
declaration's list. -/
def ExprAgreement (leftParams rightParams : Array Name) (left right : Expr) : Prop :=
  closed left = true ∧ closed right = true ∧
    Ix.Compile.Image.exprEqWith (levelAgrees leftParams rightParams) left right = true

theorem agrees_agreement {lp rp : Array Name} {left right : Expr}
    (same : agrees lp rp left right = true) : ExprAgreement lp rp left right := by
  simp only [agrees, Bool.and_eq_true] at same
  exact ⟨same.1.1, same.1.2, same.2⟩

/-- The check exposes source kind, exact name, arity, safety and both bodies;
type agreement alone cannot satisfy this contract. -/
theorem definitionMatches_source {expected : AuxDef} {source : ConstantInfo}
    (matched : definitionMatches expected source = true) :
    ∃ actual : DefinitionVal, source = .defnInfo actual ∧
      expected.name = actual.cnst.name ∧
      actual.safety = (if expected.isUnsafe then .unsafe else .safe) ∧
      expected.levelParams.size = actual.cnst.levelParams.size ∧
      ExprAgreement expected.levelParams actual.cnst.levelParams expected.typ actual.cnst.type ∧
      ExprAgreement expected.levelParams actual.cnst.levelParams expected.value actual.value := by
  cases source <;> try contradiction
  case defnInfo actual =>
    simp only [definitionMatches, Bool.and_eq_true] at matched
    obtain ⟨⟨⟨⟨hn, hs⟩, hp⟩, ht⟩, hv⟩ := matched
    refine ⟨actual, rfl, (Ix.Compile.Image.RawExact.nameEq_eq_true _ _).mp hn,
      ?_, beq_iff_eq.mp hp, agrees_agreement ht, agrees_agreement hv⟩
    cases s : actual.safety <;> cases u : expected.isUnsafe <;> simp [s, u] at hs ⊢
    all_goals cases hs

theorem checkedWrapper_source {env : Ix.Environment} {name : Name} {candidate : AuxDef}
    (checked : checkedWrapper? env name = some candidate) :
    wrapper? env name = some candidate ∧
      ∃ actual, env.get? name = some actual ∧ definitionMatches candidate actual = true := by
  unfold checkedWrapper? at checked
  cases hw : wrapper? env name <;> simp only [hw, bind, Option.bind] at checked
  · contradiction
  rename_i expected
  cases ha : env.get? name <;> simp only [ha] at checked
  · contradiction
  rename_i actual
  split at checked
  · rename_i same
    cases Option.some.inj checked
    exact ⟨rfl, actual, rfl, same⟩
  · contradiction

/-- A `casesOn`/`recOn` head is permitted only with a recognized source
wrapper: the generated candidate and the actual declaration it matched. -/
theorem permitsOptimization_source {env : Ix.Environment} {parent : Name} {suffix : String}
    (wrapperName : suffix = "casesOn" ∨ suffix = "recOn")
    (allowed : permitsOptimization env (Name.mkStr parent suffix) = true) :
    ∃ candidate actual,
      wrapper? env (Name.mkStr parent suffix) = some candidate ∧
      env.get? (Name.mkStr parent suffix) = some actual ∧
      definitionMatches candidate actual = true := by
  have recognized : (checkedWrapper? env (Name.mkStr parent suffix)).isSome = true := by
    rcases wrapperName with rfl | rfl
    · change (checkedWrapper? env (Name.mkStr parent "casesOn")).isSome = true at allowed
      exact allowed
    · change (checkedWrapper? env (Name.mkStr parent "recOn")).isSome = true at allowed
      exact allowed
  obtain ⟨candidate, found⟩ := Option.isSome_iff_exists.mp recognized
  obtain ⟨hw, actual, ha, matched⟩ := checkedWrapper_source found
  exact ⟨candidate, actual, hw, ha, matched⟩

end Ix.CompileCert.SourceIdentity
