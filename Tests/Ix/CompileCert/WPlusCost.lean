import Tests.Ix.CompileCert.Changed

/-! # Package C: the costs of W+ (C-cutsat)

On `Tests.Ix.CompileCert.ChangedDefs` compiled in-process under Pass 3 (as the
`changed` mode does), with the certifier's own functions:

* **C-cutsat (the universe of a row).** With the admitted environment's index,
  `proposeRows` states a type row and an `rfl` row at the universe the certified
  checker infers for Lean's exported type (`checkerSortLevel`), which is also the
  one it infers for the compiled type: typing the row compares the two sorts by
  syntactic equality instead of `Level.leq` (exponential on the nested `imax`
  chain of a long telescope: the Cutsat `brecOn(_k).go` of Lean's core).
  **Valid neighbour:** both rows of `Reord.Even.brecOn.go` at that universe are
  accepted by the certified fold; **negative:** the type row at the successor of
  that universe is refused. -/

namespace Tests.Ix.CompileCert.WPlusCost

open _root_.Ix.CompileCert
open _root_.Ix.CompileCert.Certifier
open Tests.Ix.CompileCert.Changed

def run : IO Unit := do
  let (env, captured, compiled) ← compile
  let b ← build env captured compiled.env
  let sc1 := prefixName ++ `SC1
  let source : Source := ⟨captured.declarations.filter fun ci => !sc1.isPrefixOf ci.name⟩
  let input := inputOf b source
  let artifact ← match prepareArtifact input.toArtifactInput with
    | .ok a => pure a
    | .error _ => throw (IO.userError "the admission failed")
  -- C-cutsat: the rows of `Reord.Even.brecOn.go` at the checker's universe
  let sh0 := SharedW.ofArtifact input (fun n => b.images.contains n) artifact #[]
  let hints0 := buildHintsW input sh0 (entryPositions sh0.entries) (queriesFor env b.refs) 4 (fun _ => [])
  let fe := _root_.Ix.Kernel.mkFEnv artifact.env
  let goName := prefixName ++ `Reord.Even.brecOn.go
  let some goCi := env.find? goName | throw (IO.userError "missing Reord.Even.brecOn.go")
  let pg ← proposeRows env sh0 hints0 goCi (some fe)
  let some (_, typeRow) := pg.rows.find? (·.1 == "type")
    | throw (IO.userError s!"brecOn.go: no type row ({pg.failure})")
  let some (_, rflRow) := pg.rows.find? (·.1 == "rfl")
    | throw (IO.userError s!"brecOn.go: no rfl row ({pg.failure})")
  let .thmDecl tcv _ := typeRow | throw (IO.userError "brecOn.go: the type row is not a theorem")
  let some (_, .sort level, ixType, leanType) := eqParts tcv.type
    | throw (IO.userError "brecOn.go: the type row is not an equation of sorts")
  unless (checkerSortLevel fe leanType).toOption == some level &&
      (checkerSortLevel fe ixType).toOption == some level do
    throw (IO.userError "brecOn.go: the type row is not at the universe the checker infers")
  let .thmDecl rcv _ := rflRow | throw (IO.userError "brecOn.go: the rfl row is not a theorem")
  let some (rflLevel, _, _, _) := eqParts rcv.type | throw (IO.userError "brecOn.go: the rfl row is not an equation")
  unless rflLevel == level do throw (IO.userError "brecOn.go: the rfl row is not at the checker's universe")
  let (_, rowsOk) ← decideW env b input b.images artifact (#[typeRow, rflRow].map (renameRow 200000))
  match rowsOk with
  | .ok () => pure ()
  | .error e => throw (IO.userError s!"brecOn.go: the rows at the checker's universe were refused: {declineLabel e}")
  let some above := supportRow tcv.name tcv.levelParams
      (kernelEq (.succ (.succ level)) (.sort (.succ level)) ixType leanType)
    | throw (IO.userError "brecOn.go: no type row at the successor universe")
  let (_, aboveResult) ← decideW env b input b.images artifact #[renameRow 200001 above]
  expectRefused "the type row of Reord.Even.brecOn.go at the successor of the checker's universe" aboveResult isFold
  IO.println s!"PASS: checker universe: the type and rfl rows of Reord.Even.brecOn.go at the universe the \
    checker infers for both types ({kernelLevelNodes level} nodes) accepted (valid neighbour)"
  IO.println "wplus-cost: rows at the checker's universe accepted, one above it refused"

end Tests.Ix.CompileCert.WPlusCost
