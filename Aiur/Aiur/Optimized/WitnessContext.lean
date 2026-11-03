import Aiur.Optimized.ValidationWitness
import Aiur.Circuit.ExpressionWitness

namespace Aiur.Optimized.Compiler

variable {F : Type} [Field F] [DecidableEq F]
open Circuit.Compiler (Bounded LocalsBounded localsEnvironment)

def TargetBound (bound : Nat) (target : Option (WireValue Witness)) : Prop :=
  ∀ candidate, target = some candidate → Bounded (F := F) bound (candidate.map Polynomial.var)

def TargetDecodes (decls : Declarations) (target : Option (WireValue Witness))
    (assignment : Witness → F) (value : Value F) : Prop :=
  ∀ candidate, target = some candidate → (candidate.map assignment).decode decls = some value

theorem TargetBound.mono {target : Option (WireValue Witness)} {before after : Nat}
    (bounded : TargetBound (F := F) before target) (grow : before ≤ after) : TargetBound (F := F) after target :=
  fun candidate found => (bounded candidate found).mono grow

theorem Extension.targetDecode {rom : WireROM F} {calls : Circuit.CallRelation F}
    {before after : State F} {initial assignment : Witness → F}
    (extension : Extension rom calls before after initial assignment)
    {decls : Declarations} {target : Option (WireValue Witness)} {value : Value F}
    (bounded : TargetBound (F := F) before.roles.size target)
    (decoded : TargetDecodes decls target initial value) : TargetDecodes decls target assignment value := by
  intro candidate found
  rw [extension.variables (bounded candidate found)]
  exact decoded candidate found

/-- The induction hypothesis consumed by the branch witness construction. -/
def ExprComplete (program : Program F) (sourceCalls : Aiur.CallRelation F)
    (calls : Circuit.CallRelation F) (function : String) (expr : Expr F) : Prop :=
  ∀ {locals : Locals F} {scope : ScopeId} {target : Option (WireValue Witness)}
    {output : Symbolic F} {before after : State F},
    lower program function locals scope expr target before = .ok (output, after) →
    ∀ {rom : WireROM F} {initial : Witness → F},
    before.toReference.WellFormed → before.Scoped → before.Valid rom calls initial → scope < before.scopes.size →
    LocalsBounded before.roles.size locals → TargetBound (F := F) before.roles.size target →
    (before.activation scope).denote initial = 1 → ∀ {environment : Environment F},
    DecodesEnvironment program.enums (localsEnvironment locals initial) environment → ∀ {value : Value F},
    TargetDecodes program.enums target initial value →
    ROMEvalExprWith program.enums (rom.decode program.enums) sourceCalls environment expr value →
    ∃ assignment, Extension rom calls before after initial assignment ∧ Bounded after.roles.size output ∧
      (output.map (Circuit.ArithExpr.denote assignment)).decode program.enums = some value

end Aiur.Optimized.Compiler
