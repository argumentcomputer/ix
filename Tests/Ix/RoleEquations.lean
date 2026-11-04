module

public import IxC.Kernel.RoleEquations
public import IxC.Kernel.Cached.Installed
public import LSpec

namespace Tests.Ix.RoleEquations

open Ix.Kernel

private abbrev E := Expr .source
private abbrev D := Declaration .source

private def need (label : String) (ok : Bool) : Except String Unit :=
  if ok then .ok () else .error label

private def checked (decls : Array D) : Except String (Env .source) :=
  (Cached.checkDecls .verified [] decls).mapError fun (error, index) =>
    s!"declaration {index}: {error}"

private def checkEquation (env : Env .source) (levels : Nat)
    (equation : Equation .source) (evidence : Evidence (Key .source × E)) : Except String Unit :=
  ((checkRoleEquation (Cached.sharedOpsC .verified (mkFEnv env)) env levels equation evidence) {})
    |>.map (fun _ => ()) |>.mapError toString

private def checkRole (env : Env .source) (role : Role) (evidence : Evidences .source) : Except String Unit :=
  ((eqnsCheck (Cached.sharedOpsC .verified (mkFEnv env)) env role evidence) {})
    |>.map (fun _ => ()) |>.mapError toString

private def proofKey : Key .source := .id (.str .anonymous "equationProof")

private def reflexive (level : Level) : Equation .source :=
  let alpha : E := .fvar 0 (.sort level)
  let value : E := .fvar 1 alpha
  { vars := [.sort level, alpha], hyps := [], level, carrier := alpha, lhs := value, rhs := value }

private def reflexivity (level : Level) : E :=
  .lam (.sort level) (.lam (.bvar 0)
    (.app (.app (.const eqReflName [level]) (.bvar 1)) (.bvar 0)) default) default

/-- Exercise dependent telescopes, proof checking, universe renaming, and
false but well-typed equations through the actual cached kernel operations. -/
def equationChecks : Except String Unit := do
  let basis : Array D := #[.indDecl eqBasis 2, .indDecl natBasis 0]
  let env ← checked basis
  let equation := reflexive (.succ .zero)
  need "dependent definitional equation" (checkEquation env 0 equation .defeq).isOk
  let proofDecl : D := .thmDecl ⟨proofKey, [], equation.statement⟩ (reflexivity (.succ .zero))
  let withProof ← checked (basis.push proofDecl)
  need "checked theorem certifies its equation"
    (checkEquation withProof 0 equation (.proof (proofKey, reflexivity (.succ .zero)))).isOk
  need "a missing theorem cannot certify an equation"
    (!(checkEquation env 0 equation (.proof (proofKey, reflexivity (.succ .zero)))).isOk)
  need "a valid theorem name does not excuse an invalid supplied proof"
    (!(checkEquation withProof 0 equation (.proof (proofKey, .sort .zero))).isOk)
  let wrong : Equation .source := {
    vars := [], hyps := [], level := .succ .zero
    carrier := specNat, lhs := specZero, rhs := specSucc specZero }
  need "a well-typed false equation refuses definitional evidence"
    (!(checkEquation env 0 wrong .defeq).isOk)
  need "an unrelated checked theorem cannot certify a false equation"
    (!(checkEquation withProof 0 wrong (.proof (proofKey, reflexivity (.succ .zero)))).isOk)
  need "ill-typed equality sides refuse"
    (!(checkEquation env 0 { wrong with rhs := .sort .zero } .defeq).isOk)
  need "free variables outside the telescope refuse"
    (!(checkEquation env 0 { wrong with rhs := .fvar 7 specNat } .defeq).isOk)
  need "loose bound variables refuse"
    (!(checkEquation env 0 { wrong with rhs := .bvar 0 } .defeq).isOk)
  need "unknown constants refuse"
    (!(checkEquation env 0 { wrong with rhs := .const proofKey [] } .defeq).isOk)
  let conditional := { equation with hyps := [equation.statement] }
  need "unconditional evidence cannot discharge hypotheses"
    (!(checkEquation env 0 conditional .defeq).isOk)
  let conditionalValue := closeRoleTelescope true (conditional.vars ++ conditional.hyps)
    (.app (.app (.const eqReflName [.succ .zero]) conditional.carrier) conditional.lhs)
  let conditionalEnv ← checked (basis.push (.thmDecl ⟨proofKey, [], conditional.statement⟩ conditionalValue))
  need "a checked proof can discharge a conditional equation"
    (checkEquation conditionalEnv 0 conditional (.proof (proofKey, conditionalValue))).isOk
  let poly := reflexive (.param 0)
  need "a declared universe parameter is accepted" (checkEquation env 1 poly .defeq).isOk
  need "an undeclared universe parameter is refused" (!(checkEquation env 0 poly .defeq).isOk)
  let renamed := reflexive (.param 7)
  let polyProof ← checked (basis.push (.thmDecl ⟨proofKey, [7], renamed.statement⟩ (reflexivity (.param 7))))
  need "theorem universe parameters may be renamed"
    (checkEquation polyProof 1 poly (.proof (proofKey, reflexivity (.param 7)))).isOk
  need "theorem universe arity must match"
    (!(checkEquation polyProof 0 equation (.proof (proofKey, reflexivity (.param 7)))).isOk)

private def definitions (second : Bool) : Array D := #[
  .indDecl eqBasis 2, .indDecl natBasis 0,
  .defnDecl ⟨roleKey .int, [], .sort (.succ .zero)⟩ specNat .opaque,
  .defnDecl ⟨roleKey .intNeg, [], intUnSpecTy⟩ (.lam specInt (.bvar 0) default) .opaque,
  .defnDecl ⟨roleKey .intAdd, [], intBinSpecTy⟩
    (.lam specInt (.lam specInt (.bvar 1) default) default) .opaque,
  .defnDecl ⟨roleKey .intSub, [], intBinSpecTy⟩
    (.lam specInt (.lam specInt (.bvar (if second then 0 else 1)) default) default) .opaque]

/-- Well-typed definitions alone do not establish their role equations. -/
def roleChecks : Except String Unit := do
  let env ← checked (definitions false)
  let evidence : Evidences .source := [(.intSub, [.defeq])]
  need "definition satisfying its actual role equation is accepted" (checkRole env .intSub evidence).isOk
  let wrong ← checked (definitions true)
  need "well-typed definition with wrong behavior is refused" (!(checkRole wrong .intSub evidence).isOk)
  need "missing evidence is refused" (!(checkRole env .intSub []).isOk)
  need "extra evidence is refused" (!(checkRole env .intSub [(.intSub, [.defeq, .defeq])]).isOk)
  need "roles without equations are refused" (!(checkRole env .nat []).isOk)
  let missing ← checked #[.indDecl eqBasis 2, .indDecl natBasis 0]
  need "an absent operation is refused" (!(checkRole missing .intSub evidence).isOk)

private def unit (label : String) (check : Unit → Except String Unit) : LSpec.TestSeq :=
  .individualIO label none (do
    let result ← IO.lazyPure check
    return match result with
      | .ok _ => (true, 0, 0, none)
      | .error message => (false, 0, 0, some message)) .done

public def suite : List LSpec.TestSeq := [
  unit "dependent equation terms and proof evidence pass the real checker" (fun _ => equationChecks),
  unit "definition behavior and evidence count satisfy the role specification" (fun _ => roleChecks)
]

end Tests.Ix.RoleEquations
