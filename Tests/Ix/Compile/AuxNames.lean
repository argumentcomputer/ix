import Ix.CompileDriver
import Ix.AuxGen.Nested
import Ix.Compile.Canon
import Ix.CanonM
import Ix.Meta
import Tests.Ix.Compile.Twins

namespace Tests.Ix.Compile.AuxNames
open Ix.Compile.Canon

def require (ok : Bool) (why : String) : IO Unit :=
  unless ok do throw (IO.userError s!"auxiliary names: {why}")

def familyControls : IO Unit := do
  let parent := Ix.Name.fromLeanName `Root._nested
  let ordinary := parent.mkStr "List_1"
  require (keyName (freshFamily [] parent "List_1") == keyName ordinary)
    "an unused historical root changed"
  for suffix in [none, some "rec", some "below", some "brecOn"] do
    let collision := match suffix with
      | none => ordinary
      | some s => ordinary.mkStr s
    let fresh := freshFamily [keyName collision] parent "List_1"
    require (!((keyName fresh).isPrefixOf (keyName collision)) && keyName fresh != keyName ordinary)
      "fresh root still captures a source spelling or suffix"
  let ctor := ordinary.mkStr "mk"
  require (keyName (freshCtorFamily [] ordinary ctor 0) == keyName ctor)
    "an unused historical constructor changed"
  let child := ctor.mkStr "child"
  for (candidate, reserved) in [(child, ctor), (ctor, child), (ordinary.mkStr "rec", ordinary.mkStr "rec")] do
    let fresh := freshCtorFamily [] ordinary candidate 1 [keyName reserved]
    require (!((keyName fresh).isPrefixOf (keyName reserved)) &&
        !((keyName reserved).isPrefixOf (keyName fresh)))
      "constructor families overlap"
  let big := Ix.Name.mkNat .mkAnon (2^80)
  require (numeralBound [keyName big] == 2^80 + 1) "numeric bound was truncated"

/-- Query keys, rather than a stored record's spelling, select the compiled
group. This raw API control documents the exact finite lookup contract. -/
def sourceQueryControl (raw : Ix.Environment) : IO Unit := do
  let nat := Ix.Name.fromLeanName `Nat
  let some (.inductInfo v) := raw.get? nat | throw (IO.userError "Nat missing from checked fixture")
  let query := Ix.Name.fromLeanName `AllocatorQuery
  let record := Ix.Name.fromLeanName `DifferentRecordName
  let sibling := Ix.Name.fromLeanName `RegistrySibling
  let consts := ({} : Std.HashMap Ix.Name Ix.ConstantInfo)
    |>.insert query (.inductInfo { v with cnst := { v.cnst with name := record }, all := #[query], ctors := #[] })
    |>.insert sibling (.inductInfo { v with cnst := { v.cnst with name := sibling }, all := #[sibling], ctors := #[] })
  let source : Ix.Environment := { consts }
  let groups := ({} : Std.HashMap Ix.Name (Array (Array Ix.Name))).insert query #[#[sibling]]
  let some view := IndView.ofConst? source.get? query | throw (IO.userError "query view missing")
  let closure := sourceContext source #[query] groups
  require (keyName view.name == keyName query && query != record &&
      (closure.declarations.get? sibling).isSome)
    "source closure and expansion used different compiled-group lookup keys"

/-- Retain the checked collision and renamed neighbour through complete
Lean/Rust compiles. Metadata may differ across the two source presentations;
their corresponding serialized canonical projections and owning payloads
must agree in full. -/
def run : IO Unit := do
  familyControls
  let file := "Tests/Ix/Compile/Fixtures/AuxNameCapture.lean"
  let le ← getFileEnv file
  let fixturePrefix := `Tests.Ix.Compile.Fixtures.AuxNameCapture
  let seeds := le.constants.toList.filterMap fun (n, _) =>
    if fixturePrefix.isPrefixOf n then some n else none
  require (!seeds.isEmpty) "checked fixture has no source declarations"
  let (raw, _) := StateT.run (Ix.CanonM.canonEnv le) {}
  sourceQueryControl raw
  for (family, changed) in [(`Collision, true), (`Neighbour, false)] do
    let root := Ix.Name.fromLeanName (fixturePrefix ++ family ++ `Root)
    let some (.inductInfo v) := raw.get? root | throw (IO.userError "checked root missing")
    let expanded ← IO.ofExcept (expandSource raw .lean v.all)
    let names := expanded.types.map (fun m => keyName m.name)
    let allNames := expanded.types.toList.flatMap fun m =>
      keyName m.name :: m.ctors.toList.map (fun c => keyName c.name)
    require (expanded.nOriginals == 2 && expanded.aux.size == 1 &&
        names.toList.eraseDups.length == names.size &&
        allNames.eraseDups.length == allNames.length)
      s!"{family}: source and generated names are not distinct"
    let some aux := expanded.aux[0]? | throw (IO.userError "auxiliary missing")
    let historical := (root.mkStr "_nested").mkStr "List_1"
    require ((keyName aux.name != keyName historical) == changed)
      s!"{family}: changed an unused candidate or retained the captured candidate"
  let closure := Tests.Ix.Compile.Twins.closeWithRecursors le <|
    Ix.EnvScope.collectDeps le (seeds ++ [`PProd, `PProd.mk, `And, `And.intro,
      `True, `True.intro, `Eq, `Eq.refl])
  for runId in [1, 2] do
    let input ← IO.ofExcept ((Ix.Compile.compileInputFromEnv le closure).mapError toString)
    let out ← IO.ofExcept (← Ix.CompileM.compileLeanInput input (numWorkers := 1))
    require (out.ungroundedCount == 0 && out.cenv.ungrounded.isEmpty)
      s!"default-pass3 run={runId}: ungrounded/refused names: {out.cenv.ungrounded.toArray.map (fun (n,e) => (n.pretty,e))}"
    for n in seeds do
      require ((out.env.getNamed? (Ix.Name.fromLeanName n)).isSome)
        s!"default-pass3 run={runId}: source declaration omitted: {n}"
    let payload := fun n => do
      let named ← out.env.getNamed? (Ix.Name.fromLeanName n)
      let lc ← out.env.consts.get? named.addr
      let c ← lc.get.toOption
      let block ← match c.info with
        | .iPrj p => some p.block
        | .cPrj p => some p.block
        | _ => none
      let owner ← out.env.consts.get? block
      pure (lc.rawBytes, owner.rawBytes)
    for (collision, neighbour) in [
        (`Root, `Root), (`Root.nil, `Root.nil), (`Root.mk, `Root.mk),
        (`Root._nested.List_1, `Node), (`Root._nested.List_1.nil, `Node.nil),
        (`Root._nested.List_1.mk, `Node.mk)] do
      let a := payload (fixturePrefix ++ `Collision ++ collision)
      let b := payload (fixturePrefix ++ `Neighbour ++ neighbour)
      require (a.isSome && b.isSome && a == b)
        s!"default-pass3 run={runId}: canonical payload bytes changed under renaming: {collision}/{neighbour}"
    let constants ← IO.ofExcept input.prepare
    let dir ← IO.FS.createTempDir
    let path := dir / "rust.ixe"
    try
      let status ← Ix.CompileM.rsCompileEnvBytesFFI constants path.toString true
      let bytes ← IO.FS.readBinFile path
      require (status.ungrounded.isEmpty && bytes == out.bytes)
        s!"default-pass3 run={runId}: complete Rust/Lean fixture bytes or refusal sets differ"
    finally
      IO.FS.removeDirAll dir
    IO.println s!"[auxiliary-names] default-pass3 run={runId}: checked-seeds={seeds.length}; emitted-all; refusals=0; canonical-payloads-identical; Lean/Rust BYTE-IDENTICAL"

end Tests.Ix.Compile.AuxNames
