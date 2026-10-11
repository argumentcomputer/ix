import Ix.AuxGen.SourceIdentity
import Ix.CompileCert.Conv.AlphaEq
import Ix.Compile.Pass.Driver

/-!
The recognition check supplies equality of both declaration skeletons after
positional universe renaming, including the value. It does not establish the
generator's laws, generation totality, publication correctness, or the later
interpretation of positional universe renaming in the source semantic model.
-/

namespace Ix.CompileCert.SourceIdentity

open Ix (Name Expr ConstantInfo DefinitionVal)
open Ix.AuxGen (AuxDef)
open Ix.AuxGen.SourceIdentity

/-- Equality of actual converted skeletons, with successful conversion on
both sides. This does not identify two failed or missing source declarations. -/
def ExprAgreement (leftParams rightParams : Array Name) (left right : Expr) : Prop :=
  ∃ l r, expr leftParams left = some l ∧ expr rightParams right = some r ∧
    Conv.er l = Conv.er r

theorem agrees_er {lp rp : Array Name} {left right : Expr}
    (same : agrees lp rp left right = true) : ExprAgreement lp rp left right := by
  unfold agrees at same
  cases hl : expr lp left <;> cases hr : expr rp right <;> simp only [hl, hr] at same
  all_goals try contradiction
  exact ⟨_, _, hl, hr, Conv.alphaEq_er _ _ same⟩

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
      ?_, beq_iff_eq.mp hp, agrees_er ht, agrees_er hv⟩
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

theorem optLookup_permitted {cenv : Ix.CompileM.CompileEnv}
    {blocks : Std.HashMap Name Ix.Compile.Pass.Opt.OptBlock}
    {site : Option Name} {name : Name} {levels : Array Ix.Level} {args : Array Expr}
    {result : Expr × Array ConstantInfo × Option String}
    (hit : Ix.Compile.Pass.optLookup cenv blocks site name levels args = some result) :
    permitsOptimization cenv.env name = true := by
  unfold Ix.Compile.Pass.optLookup at hit
  split at hit
  · contradiction
  · rename_i allowed
    simpa using allowed

theorem optLookup_casesOn_source {cenv : Ix.CompileM.CompileEnv}
    {blocks : Std.HashMap Name Ix.Compile.Pass.Opt.OptBlock}
    {site : Option Name} {parent : Name} {levels : Array Ix.Level} {args : Array Expr}
    {result : Expr × Array ConstantInfo × Option String}
    (hit : Ix.Compile.Pass.optLookup cenv blocks site (Name.mkStr parent "casesOn") levels args = some result) :
    ∃ candidate actual,
      wrapper? cenv.env (Name.mkStr parent "casesOn") = some candidate ∧
      cenv.env.get? (Name.mkStr parent "casesOn") = some actual ∧
      definitionMatches candidate actual = true := by
  have allowed := optLookup_permitted hit
  change (checkedWrapper? cenv.env (Name.mkStr parent "casesOn")).isSome = true at allowed
  obtain ⟨candidate, found⟩ := Option.isSome_iff_exists.mp allowed
  obtain ⟨hw, actual, ha, matched⟩ := checkedWrapper_source found
  exact ⟨candidate, actual, hw, ha, matched⟩

theorem optLookup_recOn_source {cenv : Ix.CompileM.CompileEnv}
    {blocks : Std.HashMap Name Ix.Compile.Pass.Opt.OptBlock}
    {site : Option Name} {parent : Name} {levels : Array Ix.Level} {args : Array Expr}
    {result : Expr × Array ConstantInfo × Option String}
    (hit : Ix.Compile.Pass.optLookup cenv blocks site (Name.mkStr parent "recOn") levels args = some result) :
    ∃ candidate actual,
      wrapper? cenv.env (Name.mkStr parent "recOn") = some candidate ∧
      cenv.env.get? (Name.mkStr parent "recOn") = some actual ∧
      definitionMatches candidate actual = true := by
  have allowed := optLookup_permitted hit
  change (checkedWrapper? cenv.env (Name.mkStr parent "recOn")).isSome = true at allowed
  obtain ⟨candidate, found⟩ := Option.isSome_iff_exists.mp allowed
  obtain ⟨hw, actual, ha, matched⟩ := checkedWrapper_source found
  exact ⟨candidate, actual, hw, ha, matched⟩

end Ix.CompileCert.SourceIdentity
