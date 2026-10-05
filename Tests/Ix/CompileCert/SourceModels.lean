import Tests.Ix.CompileCert.SourceInstall

namespace Tests.Ix.CompileCert.SourceModels

open _root_.Ix.CompileCert

def label : SourceModelError → String
  | .incomplete => "incomplete"
  | .exportFailure why => s!"source export: {why}"
  | .proposalFailure why => s!"model proposal: {why}"
  | .changedOriginal => "original declaration stream changed"
  | .correspondence => "source correspondence"
  | .supportMismatch => "model support receipt mismatch"
  | .checking error position => s!"checking at {position}: {error}"

/-- Diagnostic proposal census; the direct source gate retains its separate
strict outcomes until this source-only preparation is independently gated. -/
def run : IO Unit := do
  let env ← getCompileEnv #[Compiled.prefixName]
  -- Original constructor metadata, including the parameter/field offset.
  -- These exercise the source computation relation, not target reduction.
  for (owner, params, fields) in
      [(Compiled.prefixName ++ `Pair, [Lean.Expr.sort .zero],
          [Lean.Expr.bvar 7, Lean.Expr.bvar 11]),
       (Compiled.prefixName ++ `Node, [], [Lean.Expr.bvar 13, Lean.Expr.bvar 17])] do
    let captured ← IO.ofExcept (captureCone env.find? [owner] 128)
    for field in [:2] do
      let site ← IO.ofExcept (sourceProjectionSite captured.source owner field)
      let operand := sourceApps (.const site.ctorName []) (params ++ fields)
      let actual ← IO.ofExcept (sourceProjectionCompute captured.source (.proj owner field operand))
      unless some actual == fields[field]? do
        throw (IO.userError "source projection selected the wrong constructor field")
      IO.println s!"PASS: original constructor projection {owner}.{field} with {params.length} parameters"
    for expression in
        [Lean.Expr.proj owner 2 (.bvar 0),
         .proj owner 0 (sourceApps (.const `Unrelated.constructor []) (params ++ fields)),
         .proj owner 0 (.bvar 0)] do
      match sourceProjectionCompute captured.source expression with
      | .error _ => pure ()
      | .ok _ => throw (IO.userError "malformed source projection was accepted")
    let site ← IO.ofExcept (sourceProjectionSite captured.source owner 0)
    for arguments in [params, params ++ fields ++ [.bvar 19]] do
      match sourceProjectionCompute captured.source
          (.proj owner 0 (sourceApps (.const site.ctorName []) arguments)) with
      | .error _ => pure ()
      | .ok _ => throw (IO.userError "wrong-arity source constructor projection was accepted")
  IO.println "source constructor computation: 4 positive and 10 malformed controls passed"
  let mut installedCount := 0
  let mut unsupportedCount := 0
  for root in Compiled.roots do
    let captured ← IO.ofExcept (captureCone env.find? [root] 128)
    match installSourceModels captured.source [root] with
    | .ok installed =>
      if root == Compiled.prefixName ++ `Node.val || root == Compiled.prefixName ++ `Node.kids then
        throw (IO.userError s!"unexpected source projection support change: {root}")
      installedCount := installedCount + 1
      IO.println s!"SOURCE-MODEL-INSTALLED {root}: original={installed.original.size} checked={installed.proposal.declarations.size} blocks={installed.proposal.blocks.length} support={repr installed.proposal.basisSupport}"
    | .error reason =>
      match reason with
      | .checking (.notImplemented "projection on a non-structure-like type") _ =>
        unless root == Compiled.prefixName ++ `Node.val || root == Compiled.prefixName ++ `Node.kids do
          throw (IO.userError s!"unexpected unsupported root: {root}")
        unsupportedCount := unsupportedCount + 1
      | _ => throw (IO.userError s!"unexpected model failure: {root}: {label reason}")
      IO.println s!"SOURCE-MODEL-UNSUPPORTED {root}: {label reason}"
  unless installedCount == 6 && unsupportedCount == 2 do
    throw (IO.userError "source model outcome coverage changed")
  let node := Compiled.prefixName ++ `Node
  for support in [[], [`Eq], [`Eq, `PUnit]] do
    let captured ← IO.ofExcept (captureCone env.find? (node :: support) 128)
    match installSourceModels captured.source [node] with
    | .error reason => throw (IO.userError s!"nested source block installation failed: {label reason}")
    | .ok installed =>
      let expected := if support.isEmpty then [Ix.Kernel.BasisKind.eqK, .punitK]
        else if support.contains `PUnit then [] else [.punitK]
      unless decide (installed.proposal.basisSupport = expected) do
        throw (IO.userError "source-owned basis support was replaced or duplicated")
      IO.println s!"PASS: nested source Node installed with original support={support}; added={repr expected}"
      let mut tampered := installed.proposal.declarations
      let mut changed := false
      for i in [:tampered.size] do
        if let some declaration@(.defnDecl header _ hint) := tampered[i]? then
          unless decide (declaration ∈ installed.original.toList) || changed do
            tampered := tampered.setIfInBounds i (.defnDecl header (.bvar 1000) hint)
            changed := true
      unless changed do throw (IO.userError "model tamper control found no generated definition")
      match Ix.Kernel.Cached.checkDecls .verified [] tampered with
      | .ok _ => throw (IO.userError "generated model body tamper was accepted")
      | .error (error, position) => IO.println s!"PASS: generated model body tamper refused at {position}: {error}"
  let raw ← IO.ofExcept (captureCone env.find? [node] 128)
  let conflict : Lean.ConstantInfo := .axiomInfo {
    name := `Eq, levelParams := [], type := .sort (.succ .zero), isUnsafe := false }
  let conflicting : Source := ⟨raw.source.declarations ++ [conflict]⟩
  let original ← IO.ofExcept (exportSourceDeclarations conflicting)
  let proposal ← IO.ofExcept (proposeSourceModels conflicting original)
  unless !proposal.basisSupport.contains .eqK && decide (original.toList.Sublist proposal.declarations.toList) do
    throw (IO.userError "conflicting source Eq was replaced by fixed support")
  match installSourceModels conflicting [node] with
  | .error (.checking error position) => IO.println s!"PASS: conflicting source Eq preserved and refused at {position}: {error}"
  | _ => throw (IO.userError "conflicting source Eq was not explicitly refused by the fold")
  IO.println "source models: 8/8 original roots covered; 3 nested-block support controls and 3 generated-model tamper controls passed"

end Tests.Ix.CompileCert.SourceModels
