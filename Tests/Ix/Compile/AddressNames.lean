import Ix.CompileDriver
import Ix.AuxGen.Nested
import Ix.Compile.Canon
import Ix.Meta
import Tests.Ix.Compile.Twins

namespace Tests.Ix.Compile.AddressNames
open Ix.Compile.Canon

def require (ok : Bool) (why : String) : IO Unit :=
  unless ok do throw (IO.userError s!"nested address identity: {why}")

def packRoots : List Lean.Name := [`PProd, `PProd.mk, `And, `And.intro, `True, `True.intro, `Eq, `Eq.refl]

def closure (le : Lean.Environment) (seeds : List Lean.Name) : List (Lean.Name × Lean.ConstantInfo) :=
  Tests.Ix.Compile.Twins.closeWithRecursors le (Ix.EnvScope.collectDeps le (seeds ++ packRoots))

/-- Exact canonical payload, including the complete owning mutual block
when the selected declaration is a projection. Named/source metadata is separate. -/
def payload (out : Ix.CompileM.LeanPipelineOut) (n : Ix.Name) : Option (ByteArray × Option ByteArray) := do
  let named ← out.env.getNamed? n
  let loaded ← out.env.consts.get? named.addr
  let c ← loaded.get.toOption
  let block := match c.info with
    | .iPrj p => some p.block
    | .cPrj p => some p.block
    | .rPrj p => some p.block
    | .dPrj p => some p.block
    | _ => none
  let owner ← match block with
    | none => some none
    | some a => do pure (some (← out.env.consts.get? a).rawBytes)
  return (loaded.rawBytes, owner)

/-- A checked member may literally spell a compiled address. It must remain
separate from that external reference at every nested-key occurrence. -/
def run : IO Unit := do
  let file := "Tests/Ix/Compile/Fixtures/AddressName.lean"
  let le ← getFileEnv file
  let deps ← IO.ofExcept ((Ix.Compile.compileInputFromEnv le (closure le [`List, `Prod])).mapError toString)
  let dep ← IO.ofExcept (← Ix.CompileM.compileLeanInput deps (numWorkers := 1))
  require (dep.ungroundedCount == 0 && dep.cenv.ungrounded.isEmpty) "actual dependency compile refused"
  let list := Ix.Name.fromLeanName `List
  let some address := dep.cenv.nameToAddr.get? list | throw (IO.userError "actual List address missing")
  for queried in [list, Ix.Name.fromLeanName `Prod] do
    let some classes := dep.cenv.blocks.get? queried | throw (IO.userError "actual dependency registry missing")
    require (classes.any (·.contains queried)) s!"actual registry omits queried dependency: {queried.pretty}"
  let collision := Ix.Name.mkStr .mkAnon s!"#{address}"
  let neighbour := Ix.Name.fromLeanName `L2cAddressNameNeighbour
  require ((le.find? (keyName collision)).isSome) "checked fixture does not spell actual List address"
  let seedsOf := fun root => le.constants.toList.filterMap fun (n,_) =>
    if (keyName root).isPrefixOf n then some n else none
  let collisionSeeds := seedsOf collision
  let neighbourSeeds := seedsOf neighbour
  require (collisionSeeds.length == 39 && neighbourSeeds.length == 39) "source seed coverage changed"
  let (raw,_) := StateT.run (Ix.CanonM.canonEnv le) {}
  let penv := { dep.cenv with env := raw }
  let sourceEnv : SourceEnv := { source := raw, addr? := penv.nameToAddr.get?, groupOf := sourceGroupsOfBlocks penv.blocks }
  let env := Env.ofSource sourceEnv
  for root in [collision,neighbour] do
    let some (.inductInfo v) := raw.get? root | throw (IO.userError "checked root missing")
    require (v.numNested == 2 && !v.isUnsafe) "checked fixture kernel shape/safety changed"
    let (classes,_) ← IO.ofExcept <| v.all.toList.mapM (mutConstOf env) >>= sortClasses Rules.compiler env.addr?
    let aliases := aliasesOf (classNames classes)
    let ordered := (classNames classes).filterMap (·[0]?)
    let src ← IO.ofExcept (expandSource raw .lean ordered)
    let canon ← IO.ofExcept (expandSource raw .lean ordered aliases sourceEnv.groupOf (some env.addr?))
    let benv : Ix.CompileM.BlockEnv := {
      all := v.all.foldl (fun s n => s.insert n) {}
      current := root
      mutCtx := Ix.MutConst.ctx classes
      univCtx := v.cnst.levelParams.toList }
    let ((prod,sorted),_) ← IO.ofExcept <|
      (Ix.CompileM.CompileM.run penv benv {} do
        let x ← Ix.AuxGen.expandNestedBlock ordered aliases true
        let (y,_) ← Ix.AuxGen.sortAuxByPartitionRefinement x
        pure (x,y)).mapError toString
    require (src.aux.size == 2 && canon.aux.size == 2 &&
        prod.types.size - prod.nOriginals == 2 && sorted.types.size - sorted.nOriginals == 2)
      s!"{root.pretty}: source/canonical/production/post-order lost an auxiliary"
  let seeds := collisionSeeds ++ neighbourSeeds
  let entries := closure le seeds
  for runId in [1, 2] do
    let input ← IO.ofExcept ((Ix.Compile.compileInputFromEnv le entries).mapError toString)
    let out ← IO.ofExcept (← Ix.CompileM.compileLeanInput input (numWorkers := 1))
    require (out.ungroundedCount == 0 && out.cenv.ungrounded.isEmpty)
      s!"default-pass3 run={runId}: compiler refused checked declarations: {out.cenv.ungrounded.toArray.map (fun (n,e) => (n.pretty,e))}"
    for n in seeds do
      require ((out.env.getNamed? (Ix.Name.fromLeanName n)).isSome) s!"default-pass3 run={runId}: omitted {n}"
    for n in collisionSeeds do
      let source := Ix.Name.fromLeanName n
      let target := nameReplacePrefix source collision neighbour
      require ((le.find? (keyName target)).isSome && neighbourSeeds.contains (keyName target))
        s!"no corresponding checked neighbour for {n}"
      let a := payload out source
      let b := payload out target
      require (a.isSome && b.isSome && a == b)
        s!"default-pass3 run={runId}: canonical declaration/owner bytes differ for {n}/{target.pretty}"
    let constants ← IO.ofExcept input.prepare
    let dir ← IO.FS.createTempDir
    let path := dir / "rust.ixe"
    try
      let status ← Ix.CompileM.rsCompileEnvBytesFFI constants path.toString true
      let bytes ← IO.FS.readBinFile path
      require (status.ungrounded.isEmpty && bytes == out.bytes)
        s!"default-pass3 run={runId}: complete Rust/Lean bytes/refusal sets differ"
    finally
      IO.FS.removeDirAll dir
    IO.println s!"[nested-address-identity] default-pass3 run={runId}: collision=39/39; neighbour=39/39; auxiliaries=2/2; refusals=0; all-canonical-payloads-identical; Lean/Rust BYTE-IDENTICAL"

end Tests.Ix.Compile.AddressNames
