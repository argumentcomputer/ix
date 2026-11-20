module

public import Ix.Cert.Compile
public import Ix.CanonM
public import Ix.EnvScope
public import Ix.RoleEvidence
public import IxC.Kernel.Ixon.Prelude

/-! IxC reads a supported modeled accessor as a recursor application. Preparing that
definition before compilation makes the recursor part of the authenticated Ixon
record and follows its ordinary dependency edges. A use of the accessor therefore
unfolds the same definition that IxC checked. -/

public section

namespace Ix.Compile.ProjectionAccessors

open Ix.Kernel.Reader (CExpr State)
open Ix.LeanIngress

/-- The only primitive projection body that IxC's accessor rewrite recognizes. -/
private def owner? : Lean.Expr → Option Lean.Name
  | .lam _ _ body _ => owner? body
  | .proj n _ (.bvar 0) => some n
  | _ => none

private def candidateOwner? (env : Lean.Environment) (d : Lean.DefinitionVal) : Option Lean.Name := do
  guard (d.safety == .safe && (d.all.isEmpty || d.all == [d.name]))
  let n ← owner? d.value
  let .inductInfo ind ← env.find? n | none
  guard (ind.all.length > 1 || ind.numNested != 0)
  return n

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
  -- Only a successfully read block can supply an owner and its field iota level.
  for (_, converted) in scheduleOf graph do
    if let .ok r := converted >>= lower st then st := st.commit r
  return st

/-- Publish the same recursor body IxC selects, so a use of the accessor unfolds
to that body in Ixon. Check the materialized source term by reading it back. -/
def prepare (source : Lean.Environment) (input : List (Lean.Name × Lean.ConstantInfo)) :
    Except String (List (Lean.Name × Lean.ConstantInfo)) := do
  let owners := input.filterMap fun (_, ci) => match ci with
    | .defnInfo d => candidateOwner? source d
    | _ => none
  if owners.isEmpty then return input
  let st ← fieldState source input owners
  let mut prepared := input.toArray
  let mut present := input.foldl (fun (s : Lean.NameSet) (n, _) => s.insert n) {}
  -- Dependencies appended while walking the input are distinct names from the source.
  let sourceSize := source.constants.map₂.foldl (fun count _ _ => count + 1) source.constants.map₁.size
  for i in [:prepared.size + sourceSize + 1] do
    let some (name, ci) := prepared[i]? | return prepared.toList
    let .defnInfo d := ci | continue
    if (candidateOwner? source d).isNone then continue
    let ⟨updated, _⟩ ← materialize st d
    if updated.value == d.value then continue
    prepared := prepared.set! i (name, .defnInfo updated)
    let previous := ci.getUsedConstantsAsSet
    let missing := updated.value.getUsedConstants.toList.filter fun n =>
      !present.contains n && !previous.contains n
    unless missing.isEmpty do
      for (n, extra) in Ix.EnvScope.collectDeps source missing { recursors := true } do
        unless present.contains n do
          present := present.insert n
          prepared := prepared.push (n, extra)
  throw "accessor dependencies exceed the source environment"

end Ix.Compile.ProjectionAccessors
