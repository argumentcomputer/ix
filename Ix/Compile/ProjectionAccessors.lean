module

public import Ix.Cert.Compile
public import Ix.CanonM
public import Ix.EnvScope
public import Ix.RoleEvidence
public import IxC.Kernel.Ixon.Prelude

public section

namespace Ix.Compile.ProjectionAccessors

open Ix.Kernel.Reader (CExpr State)
open Ix.LeanIngress

/-- The only primitive projection body that IxC's accessor rewrite recognizes. -/
private def owner? : Lean.Expr → Option Lean.Name
  | .lam _ _ body _ => owner? body
  | .proj n _ (.bvar 0) => some n
  | _ => none

private def candidate (env : Lean.Environment) (ci : Lean.ConstantInfo) : Bool := Id.run do
  let .defnInfo d := ci | return false
  unless d.safety == .safe && (d.all.isEmpty || d.all == [d.name]) do return false
  let some n := owner? d.value | return false
  let some (.inductInfo ind) := env.find? n | return false
  return ind.all.length > 1 || ind.numNested != 0

private def sourceName (key : Ix.Kernel.Key .source) : Except String Lean.Name :=
  match key with
  | .id _ | .role _ => pure (Ix.RoleEvidence.toLeanName key)
  | .aux .. => throw s!"accessor contains a generated kernel key {key}"

private def sourceLevel (lps : List Lean.Name) : Ix.Kernel.Level → Except String Lean.Level
  | .zero => pure .zero
  | .succ u => return .succ (← sourceLevel lps u)
  | .max u v => return .max (← sourceLevel lps u) (← sourceLevel lps v)
  | .imax u v => return .imax (← sourceLevel lps u) (← sourceLevel lps v)
  | .param i => match lps[i]? with
    | some n => pure (.param n)
    | none => throw s!"accessor universe parameter {i} is out of bounds"

private def sourceExpr (lps : List Lean.Name) : CExpr .source → Except String Lean.Expr
  | .bvar i => pure (.bvar i)
  | .fvar .. => throw "accessor contains a free variable"
  | .sort u => return .sort (← sourceLevel lps u)
  | .const n us => return .const (← sourceName n) (← us.mapM (sourceLevel lps))
  | .app f a => return .app (← sourceExpr lps f) (← sourceExpr lps a)
  | .lam t b _ => return .lam .anonymous (← sourceExpr lps t) (← sourceExpr lps b) .default
  | .forallE t b _ => return .forallE .anonymous (← sourceExpr lps t) (← sourceExpr lps b) .default
  | .letE t v b m =>
    return .letE .anonymous (← sourceExpr lps t) (← sourceExpr lps v) (← sourceExpr lps b) m.nonDep
  | .lit (.natVal n) => pure (.lit (.natVal n))
  | .lit (.strVal s) => pure (.lit (.strVal s))
  | .proj n i e => return .proj (← sourceName n) i (← sourceExpr lps e)

/-- The accessor's outer lambdas retain their source names, binder information and domains. -/
private def replaceBody (lps : List Lean.Name) : Lean.Expr → CExpr .source → Except String Lean.Expr
  | .lam n t b bi, .lam _ b' _ => return .lam n t (← replaceBody lps b b') bi
  | .proj _ _ (.bvar 0), e => sourceExpr lps e
  | _, _ => throw "accessor telescope differs from the reader's"

private def readDefinition (st : State .source) (d : Lean.DefinitionVal) :=
  convertDefinitions #[(Ix.CanonM.canonConst (.defnInfo d)).run' {}] >>= lower st

/-- The original and emitted source definitions lower to the same IxC declarations
in the field owner's reader state. This includes the declared type and hint. -/
private def materialize (st : State .source) (d : Lean.DefinitionVal) :
    Except String { d' : Lean.DefinitionVal //
      (readDefinition st d).map (·.decls) = (readDefinition st d').map (·.decls) } := do
  match before : readDefinition st d with
  | .error e => throw s!"{d.name}: {e}"
  | .ok r =>
    if r.projRewrites == 0 then return ⟨d, rfl⟩
    let #[.defnDecl _ body _] := r.decls | throw s!"{d.name}: expected one rewritten definition"
    let value ← (replaceBody d.levelParams d.value body).mapError (fun e => s!"{d.name}: {e}")
    let d' := { d with value }
    match after : readDefinition st d' with
    | .error e => throw s!"{d.name}: {e}"
    | .ok r' =>
      if h : r.decls = r'.decls then
        return ⟨d', by simp [before, after, Except.map, h]⟩
      else throw s!"{d.name}: normalized definition differs from IxC"

/-- Compute the modeled field data over the owners' dependency closure. -/
private def fieldState (source : Lean.Environment) (input : List (Lean.Name × Lean.ConstantInfo))
    (owners : List Lean.Name) :
    Except String (State .source) := do
  let deps := Ix.EnvScope.collectDeps source owners { recursors := true }
  let support := Std.HashMap.ofList deps
  let support := input.foldl (fun m (n, ci) => if m.contains n then m.insert n ci else m) support
  let env : Ix.Environment := { consts := Std.HashMap.ofList (Ix.CanonM.canonChunk support.toArray).toList }
  let graph := Ix.LeanIngress.graph env (Ix.Cert.blocksOf env)
  let pre : Ix.Kernel.Reader.Prelude .source ← Ix.Kernel.Reader.builtinPrelude
  let mut st := pre.state
  for (_, converted) in scheduleOf graph do
    if let .ok r := converted >>= lower st then st := st.commit r
  return st

/-- Publish the same recursor body IxC selects, so a use of the accessor unfolds
to that body in Ixon. Check the materialized source term by reading it back. -/
def prepare (source : Lean.Environment) (input : List (Lean.Name × Lean.ConstantInfo)) :
    Except String (List (Lean.Name × Lean.ConstantInfo)) := do
  let candidates := input.filter fun (_, ci) => candidate source ci
  if candidates.isEmpty then return input
  let owners := candidates.filterMap fun (_, ci) => ci.value?.bind owner?
  let st ← fieldState source input owners
  let mut replacements : Std.HashMap Lean.Name Lean.ConstantInfo := {}
  let mut refs : Lean.NameSet := {}
  for (name, ci) in candidates do
    let .defnInfo d := ci | continue
    let ⟨updated, _⟩ ← materialize st d
    if updated.value == d.value then continue
    replacements := replacements.insert name (.defnInfo updated)
    let previous := ci.getUsedConstantsAsSet
    for n in updated.value.getUsedConstantsAsSet do
      unless previous.contains n do refs := refs.insert n
  if replacements.isEmpty then return input
  let present := input.foldl (fun (s : Lean.NameSet) (n, _) => s.insert n) {}
  let missing := refs.toList.filter (!present.contains ·)
  let extra := if missing.isEmpty then [] else
    (Ix.EnvScope.collectDeps source missing { recursors := true }).filter (!present.contains ·.1)
  return (input.map fun (n, ci) => (n, replacements.getD n ci)) ++ extra

end Ix.Compile.ProjectionAccessors
