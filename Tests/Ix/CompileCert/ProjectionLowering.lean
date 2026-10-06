import Tests.Ix.CompileCert.SourceModels
import Tests.Ix.CompileCert.LoweringDefs

/-! # The projection lowering receipt (`SourceProjectionLowering`)

Positive: every projection function of a mutual and of a nested structure-like
fixture gets a Lean-kernel-accepted lowering equation and a receipt; the
normalised source installation of a mutual and a nested projection goes
through the verified fold with the receipts. Negative: a wrong binder domain, a
wrong field index, a wrong elimination level (consistent, and recursor only), a
witness for another function and a receipt for a non-structure-like are each
refused, each next to its valid neighbour. -/

namespace Tests.Ix.CompileCert.ProjectionLowering

open _root_.Ix.CompileCert
open _root_.Ix.CompileCert.LoweringLean

def fixture : Lean.Name := `Tests.Ix.CompileCert.LoweringDefs

def failIf (condition : Bool) (message : String) : IO Unit :=
  if condition then throw (IO.userError message) else pure ()

def isError : Except String α → Bool
  | .error _ => true
  | .ok _ => false

def errorText : Except String α → String
  | .error why => why
  | .ok _ => ""

/-- The valid neighbour: Lean's kernel accepts the equation and the receipt is decided. -/
def accepted (env : Lean.Environment) (f : Lean.Name) : IO LoweringOutcome := do
  let outcome ← IO.ofExcept (← lowerProjection env f)
  if let .error why := outcome.kernel then
    throw (IO.userError s!"{f}: Lean's kernel refused the lowering equation: {why}")
  if let .error why := outcome.receipt then
    throw (IO.userError s!"{f}: receipt refused: {why}")
  return outcome

def run : IO Unit := do
  let env ← getCompileEnv #[fixture, Compiled.prefixName]
  -- positive: every projection function of the fixtures
  let mutualFns := [`Sized.n, `Sized.vec, `Sized.ok, `Sized.rest].map (fixture ++ ·)
  let nestedFns := ([`Rose.root, `Rose.children].map (fixture ++ ·)) ++
    ([`Node.val, `Node.kids, `PolyNode.val, `PolyNode.kids].map (Compiled.prefixName ++ ·))
  let mut positives := 0
  for f in mutualFns ++ nestedFns do
    let outcome ← accepted env f
    positives := positives + 1
    IO.println s!"PASS: {f}: Lean-kernel-checked {outcome.witness.name}, receipt accepted, ℓ = {outcome.level}"
  failIf (positives != 10) "positive coverage changed"
  -- positive: the normalised source installation with the receipts (mutual and nested)
  let mut installs := 0
  for root in [fixture ++ `Sized.vec, fixture ++ `Sized.ok, fixture ++ `Rose.children] do
    let captured ← IO.ofExcept (captureCone env.find? [root] 256)
    let witnesses ← sourceWitnesses env captured.source
    match installSourceNormalized captured.source [root] witnesses with
    | .error why => throw (IO.userError s!"normalised installation {root}: {SourceModels.label why}")
    | .ok installed =>
      let some originalCI := captured.source.find root | throw (IO.userError "root absent")
      let some original := entryDeclaration (← IO.ofExcept (exportSourceEntry originalCI))
        | throw (IO.userError "root is not a definition or theorem")
      let some (header, _) := declarationParts original | throw (IO.userError "root parts")
      let some replacement := installed.declarations.find? fun declaration =>
          match declarationParts declaration with
          | some (h, _) => decide (h.name = header.name)
          | none => false
        | throw (IO.userError "replacement absent")
      failIf (decide (replacement = original)) s!"{root} was not lowered"
      let _ ← IO.ofExcept (checkSourceProjectionLowering captured.source installed.witnesses
        original replacement)
      installs := installs + 1
      IO.println s!"PASS: {root}: normalised source installed by the verified fold ({installed.declarations.length} declarations, {witnesses.length} lowering receipts)"
      -- the same installation without the Lean equations: nothing is lowered and the fold refuses
      match installSourceNormalized captured.source [root] [] with
      | .ok _ => throw (IO.userError s!"{root}: raw projection installed without a lowering")
      | .error why => IO.println s!"PASS: {root}: without lowering equations the raw projection is refused ({SourceModels.label why})"
  failIf (installs != 3) "installation coverage changed"
  -- negative controls, each beside its valid neighbour
  let mut negatives := 0
  for f in [fixture ++ `Sized.vec, fixture ++ `Rose.children] do
    let _ ← accepted env f
    -- wrong binder domain: convertible, so Lean's kernel accepts; the syntactic check refuses
    let domain ← IO.ofExcept (← lowerProjection env f .domain)
    failIf (isError domain.kernel) s!"{f}: convertible domain refused by Lean's kernel: {errorText domain.kernel}"
    failIf (!(errorText domain.receipt).startsWith "projection lowering binder domains")
      s!"{f}: wrong binder domain not refused by the receipt: {errorText domain.receipt}"
    IO.println s!"PASS: {f}: wrong binder domain (id (T p)) refused: {errorText domain.receipt}"
    negatives := negatives + 1
    -- wrong field index: Lean's kernel and the receipt both refuse
    let wrongField ← IO.ofExcept (← lowerProjection env f (.field 0))
    failIf (!isError wrongField.kernel) s!"{f}: wrong field accepted by Lean's kernel"
    failIf (!(errorText wrongField.receipt).startsWith "projection lowering replacement is not the recursor form")
      s!"{f}: wrong field not refused by the receipt: {errorText wrongField.receipt}"
    IO.println s!"PASS: {f}: wrong field index refused by Lean's kernel and by the receipt"
    negatives := negatives + 1
    -- wrong elimination level, consistently in the recursor and in Eq: only inference sees it
    let level ← IO.ofExcept (← lowerProjection env f .level)
    failIf (!isError level.kernel) s!"{f}: wrong elimination level accepted by Lean's kernel"
    IO.println s!"PASS: {f}: wrong elimination level refused by Lean's kernel (receipt syntax alone: {if isError level.receipt then "refused" else "accepted"})"
    negatives := negatives + 1
    -- wrong elimination level in the recursor only: the receipt refuses as well
    let recLevel ← IO.ofExcept (← lowerProjection env f .recLevel)
    failIf (!isError recLevel.kernel) s!"{f}: recursor-only level accepted by Lean's kernel"
    failIf (!(errorText recLevel.receipt).startsWith "projection lowering equation does not state")
      s!"{f}: recursor-only level not refused by the receipt: {errorText recLevel.receipt}"
    IO.println s!"PASS: {f}: recursor level differing from R's sort refused by Lean's kernel and by the receipt"
    negatives := negatives + 1
  -- a witness for another function
  let vec := fixture ++ `Sized.vec
  let other ← accepted env (fixture ++ `Sized.n)
  let source ← IO.ofExcept (receiptSource env vec)
  let some vecCI := env.find? vec | throw (IO.userError "absent")
  let .defn header body hint ← IO.ofExcept (exportSourceEntry vecCI) | throw (IO.userError "kind")
  let original := Ix.Kernel.Declaration.defnDecl header body hint
  failIf ((← IO.ofExcept (proposeSourceProjection source [other.witness] original)).isSome)
    "lowering proposed from another function's equation"
  let good ← accepted env vec
  let some (replacement, _) ← IO.ofExcept (proposeSourceProjection source [good.witness] original)
    | throw (IO.userError "no proposal")
  match checkSourceProjectionLowering source [other.witness] original replacement with
  | .ok _ => throw (IO.userError "receipt accepted another function's equation")
  | .error why => IO.println s!"PASS: another function's equation refused: {why}"
  negatives := negatives + 1
  -- a receipt for a non-structure-like: a projection-shaped definition over `List`
  let fake : Lean.Name := `Tests.fakeListProjection
  let listType := Lean.mkApp (.const ``List [.zero]) (.const ``Nat [])
  let fakeDefinition : Lean.DefinitionVal := {
    name := fake, levelParams := [], type := .forallE `self listType (.const ``Nat []) .default,
    value := .lam `self listType (.proj ``List 0 (.bvar 0)) .default,
    hints := .abbrev, safety := .safe }
  let some listCI := env.find? ``List | throw (IO.userError "List absent")
  let ctorCIs := [``List.nil, ``List.cons].filterMap env.find?
  let some listRec := env.find? ``List.rec | throw (IO.userError "List.rec absent")
  let fakeSource : Source := ⟨[.defnInfo fakeDefinition, listCI] ++ ctorCIs ++ [listRec]⟩
  let .defn fakeHeader fakeBody fakeHint ← IO.ofExcept (exportSourceEntry (.defnInfo fakeDefinition))
    | throw (IO.userError "kind")
  let fakeWitness : Lean.TheoremVal := { good.witness with name := loweringEquationName fake }
  match checkSourceProjectionLowering fakeSource [fakeWitness] (.defnDecl fakeHeader fakeBody fakeHint)
      (.defnDecl fakeHeader fakeBody fakeHint) with
  | .ok _ => throw (IO.userError "receipt accepted for a non-structure-like")
  | .error why =>
    failIf (why != "source projection owner does not have exactly one constructor")
      s!"non-structure-like refused for another reason: {why}"
    IO.println s!"PASS: receipt for a non-structure-like (List) refused: {why}"
  negatives := negatives + 1
  failIf (negatives != 10) "negative coverage changed"
  IO.println s!"projection lowering: {positives} receipts with Lean-kernel-checked equations ({mutualFns.length} mutual, {nestedFns.length} nested), {installs}/3 normalised installations (a mutual definition, a mutual proof field, a nested definition), {negatives} negative controls each beside its valid neighbour"

end Tests.Ix.CompileCert.ProjectionLowering
