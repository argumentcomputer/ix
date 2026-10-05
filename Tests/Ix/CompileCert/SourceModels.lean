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

def runNormalized : IO Unit := do
  let env ← getCompileEnv #[Compiled.prefixName]
  let mut installedCount := 0
  for root in Compiled.roots do
    let captured ← IO.ofExcept (captureCone env.find? [root] 128)
    match installSourceNormalized captured.source [root] with
    | .error reason => throw (IO.userError s!"source normalization failed {root}: {label reason}")
    | .ok installed =>
      installedCount := installedCount + 1
      let laws := installed.declarations.filter fun
        | .thmDecl header _ => header.name.toString.endsWith "._source_constructor_equation"
        | _ => false
      IO.println s!"SOURCE-NORMALIZED {root}: original={installed.original.size} model={installed.modelProposal.declarations.size} checked={installed.declarations.length} constructorEquations={laws.length}"
      if root == Compiled.prefixName ++ `Node.val || root == Compiled.prefixName ++ `Node.kids then
        unless laws.length > 0 do throw (IO.userError "nested projection lacks a checked constructor equation")
        let some original := installed.modelProposal.declarations.toList.find?
            (fun declaration => decide (declaration.names = [sourceName root]))
          | throw (IO.userError "original projection missing from model proposal")
        let some replacement := installed.declarations.find?
            (fun declaration => decide (declaration.names = [sourceName root]))
          | throw (IO.userError "replacement projection missing from normalized stream")
        let some equation := laws.head? | throw (IO.userError "projection equation missing")
        let receipt ← IO.ofExcept (checkSourceProjectionReceipt captured.source original replacement equation)
        let wrongHint := if decide (receipt.hint = .opaque) then Ix.Kernel.ReducibilityHint.abbrev else .opaque
        for (why, input, candidate, law) in
            [("original body", Ix.Kernel.Declaration.defnDecl receipt.header (.bvar 1000) receipt.hint,
                replacement, equation),
             ("replacement type", original,
                .defnDecl { receipt.header with type := .sort .zero } receipt.value receipt.hint, equation),
             ("replacement hint", original,
                .defnDecl receipt.header receipt.value wrongHint, equation),
             ("equation proof", original, replacement,
                match equation with
                | .thmDecl header _ => .thmDecl header (.bvar 1000)
                | declaration => declaration)] do
          match checkSourceProjectionReceipt captured.source input candidate law with
          | .ok _ => throw (IO.userError s!"independent source receipt accepted tampered {why}")
          | .error _ => IO.println s!"PASS: independent source receipt rejects {why} for {root}"
        if root == Compiled.prefixName ++ `Node.val then
          let otherSite ← IO.ofExcept (sourceProjectionSite captured.source receipt.ownerName 1)
          let otherEquation ← IO.ofExcept (sourceProjectionEquation otherSite receipt.header receipt.level)
          match checkSourceProjectionReceipt captured.source original replacement otherEquation with
          | .ok _ => throw (IO.userError "source receipt accepted another original constructor field")
          | .error _ => IO.println "PASS: independent source receipt rejects another constructor field"
        let tampered := installed.declarations.map fun
          | .thmDecl header value =>
            if header.name.toString.endsWith "._source_constructor_equation" then
              .thmDecl header (.bvar 1000)
            else .thmDecl header value
          | declaration => declaration
        match Ix.Kernel.Cached.checkDecls .verified [] tampered.toArray with
        | .ok _ => throw (IO.userError "tampered source constructor equation accepted")
        | .error (error, position) => IO.println s!"PASS: constructor equation tamper refused at {position}: {error}"
      if root == Compiled.prefixName ++ `Node.val then
        let wrongValue := installed.declarations.map fun
          | declaration@(.defnDecl header (.lam domain _ binder) hint) =>
            if decide (header.name = sourceName root) then
              .defnDecl header (.lam domain (.const (sourceName `Nat.zero) []) binder) hint
            else declaration
          | declaration => declaration
        let withoutLaws := wrongValue.filter fun
          | .thmDecl header _ => !header.name.toString.endsWith "._source_constructor_equation"
          | _ => true
        match Ix.Kernel.Cached.checkDecls .verified [] withoutLaws.toArray with
        | .error (error, position) =>
          throw (IO.userError s!"wrong-value control was not well typed at {position}: {error}")
        | .ok _ => IO.println "PASS: wrong constant-zero projection is independently well typed without its equation"
        match Ix.Kernel.Cached.checkDecls .verified [] wrongValue.toArray with
        | .ok _ => throw (IO.userError "well-typed wrong projection passed its constructor equation")
        | .error (error, position) => IO.println s!"PASS: constructor equation rejects well-typed wrong projection at {position}: {error}"
        let collision : Lean.ConstantInfo := .axiomInfo {
          name := root.str "_source_constructor_equation", levelParams := [],
          type := .sort (.succ .zero), isUnsafe := false }
        let conflicting : Source := ⟨captured.source.declarations ++ [collision]⟩
        match installSourceNormalized conflicting [root] with
        | .error (.proposalFailure "source projection equation name conflicts with an existing declaration") =>
          IO.println "PASS: original-source constructor-equation name collision refused"
        | .error why => throw (IO.userError s!"unexpected name-collision refusal: {label why}")
        | .ok _ => throw (IO.userError "source projection equation overwrote an original declaration")
  unless installedCount == 8 do throw (IO.userError "normalized source root coverage changed")
  IO.println "source normalization: 8/8 original roots installed"

def runCoverage : IO Unit := do
  let env ← getCompileEnv #[Compiled.prefixName]
  for (root, owner, support) in
      [(Compiled.prefixName ++ `Node.val, Compiled.prefixName ++ `Node, []),
       (Compiled.prefixName ++ `Pair, Compiled.prefixName ++ `Pair, [`Eq]),
       (`Subtype, `Subtype, [`Eq])] do
    let captured ← IO.ofExcept (captureCone env.find? (root :: support) 256)
    let installed ← match installSourceNormalized captured.source (root :: support) with
      | .ok installed => pure installed
      | .error why => throw (IO.userError s!"coverage source install {owner}: {label why}")
    let site ← IO.ofExcept (sourceProjectionSite captured.source owner 0)
    match checkSourceConstructorCover installed site with
    | .error why => throw (IO.userError s!"source constructor coverage {owner}: {label why}")
    | .ok coverage =>
      IO.println s!"COVERAGE-CHECKED {owner}: params={site.owner.numParams} fields={site.ctor.numFields} declarations={installed.declarations.length + 1}"
      let receipt ← IO.ofExcept (checkSourceCoverInstalledShape coverage)
      IO.println s!"COVERAGE-SHAPE {owner}: exact installed dependent field domains"
      let badFields := { receipt.data with coverageFields := [] }
      if decide (SourceCoverShape site coverage.header badFields) then
        throw (IO.userError "missing installed coverage fields passed structural relation")
      let badOwner := { receipt.data with owner := { receipt.data.owner with name := .anonymous } }
      if decide (SourceCoverShape site coverage.header badOwner) then
        throw (IO.userError "wrong original owner identity passed structural relation")
      let badEquation := { receipt.data with equalityType := .bvar 999 }
      if decide (SourceCoverShape site coverage.header badEquation) then
        throw (IO.userError "wrong installed constructor equation passed structural relation")
      if site.owner.numParams > 0 then
        let unshifted := { receipt.data with coverageFields := receipt.data.fields }
        if decide (SourceCoverShape site coverage.header unshifted) then
          throw (IO.userError "unshifted dependent parameter references passed structural relation")
      IO.println "PASS: missing fields, wrong owner, wrong Eq type and applicable unshifted domains refused"
      let tampered := installed.declarations ++ [Ix.Kernel.Declaration.thmDecl coverage.header (.bvar 1000)]
      match Ix.Kernel.Cached.checkDecls .verified [] tampered.toArray with
      | .ok _ => throw (IO.userError "malformed source coverage proof accepted")
      | .error (error, position) => IO.println s!"PASS: source coverage proof tamper refused at {position}: {error}"

end Tests.Ix.CompileCert.SourceModels
