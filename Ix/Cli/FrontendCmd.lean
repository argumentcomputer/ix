/-
  `ix frontend <subcommand>`: CLI interface to the pure, certified Ix Frontend:
  - `ix frontend compile`: Parse, elaborate, canonicalize, and compile `.ix` / `.lean`
    source file(s) directly to a `.ixe` artifact (without invoking Lake).
  - `ix frontend check`: Parse, elaborate, typecheck, and run substructural resource
    checking on `.ix` / `.lean` source file(s).
  - `ix frontend merge`: Run the 2-way or 3-way AST & type-aware `IxVCS` module merge
    engine (`mergeSource2` / `mergeSource3` / `resolveConflictVariant`), formatting
    and/or compiling the merged module.
  - `ix frontend format`: Pretty-print `.ix` / `.lean` source files via `formatSyntax`
    and optionally verify round-trip parsing.
-/
module

public import Cli
public import Ix.Frontend
public import Ix.Store

public section

open System (FilePath)
open Ix.Frontend
open Ix.Frontend.Parser
open Ix.Frontend.Elab

namespace Ix.Cli.FrontendCmd

/-- Derive a module `Ix.Name` from a file path stem (e.g. `"Foo/Bar.ix"` -> `Bar`). -/
private def moduleNameOfPath (pathStr : String) : Ix.Name :=
  let fp := FilePath.mk pathStr
  let stem := fp.fileStem.getD (fp.fileName.getD "Main")
  Name.fromComponents (stem.splitOn ".")

/-- Default `.ixe` output path for a source path. -/
private def defaultIxePath (pathStr : String) : String :=
  let fp := FilePath.mk pathStr
  let stem := fp.fileStem.getD (fp.fileName.getD pathStr)
  stem.toLower ++ ".ixe"

/-! ## `ix frontend compile` -/

def runFrontendCompile (p : Cli.Parsed) : IO UInt32 := do
  let files := (p.variableArgsAs! String).toList
  if files.isEmpty then
    p.printError "error: must specify one or more .ix / .lean source files"
    return 1
  let outPath := (p.flag? "out").map (·.as! String) |>.getD (defaultIxePath (files.headD "out"))
  let useCertified := p.hasFlag "certified"
  let checkRes := p.hasFlag "check-resources"

  let mut initElabEnv := IxElabEnv.empty
  if let some ixeFlag := p.flag? "import-ixe" then
    let ixePath := ixeFlag.as! String
    let ixeBytes ← IO.FS.readBinFile ⟨ixePath⟩
    match Ixon.deEnv ixeBytes with
    | .ok baseIxe =>
      initElabEnv := IxElabEnv.ofIxonEnv baseIxe
    | .error e =>
      p.printError s!"error: failed to decode --import-ixe '{ixePath}': {e}"
      return 1

  let (elabEnv, ixonEnv) ←
    match files with
    | [singlePath] =>
      let src ← IO.FS.readFile ⟨singlePath⟩
      if useCertified then
        match compileSourceCertified src singlePath initElabEnv with
        | .ok (_, eEnv, ixe, _) => pure (eEnv, ixe)
        | .error e =>
          p.printError s!"error: {e}"
          return 1
      else
        match compileSourceToIxon src singlePath initElabEnv with
        | .ok (_, eEnv, ixe, _) => pure (eEnv, ixe)
        | .error e =>
          p.printError s!"error: {e}"
          return 1
    | _ =>
      let mut modList : List (Ix.Name × String) := []
      for fPath in files do
        let src ← IO.FS.readFile ⟨fPath⟩
        modList := modList ++ [(moduleNameOfPath fPath, src)]
      if useCertified then
        match compileModuleDAGCertified modList initElabEnv with
        | .ok (eEnv, _, ixe, _) => pure (eEnv, ixe)
        | .error e =>
          p.printError s!"error: {e}"
          return 1
      else
        match compileModuleDAGToIxon modList initElabEnv with
        | .ok (eEnv, _, ixe, _) => pure (eEnv, ixe)
        | .error e =>
          p.printError s!"error: {e}"
          return 1

  if checkRes then
    match Ix.Resource.Addressed.checkResources ixonEnv {} with
    | .ok _ => pure ()
    | .error e =>
      p.printError s!"error: resource check failed: {e}"
      return 1

  let bytes ← match Ixon.serEnv ixonEnv with
    | .ok bs => pure bs
    | .error e =>
      p.printError s!"error: failed to serialize Ixon.Env: {e}"
      return 1
  IO.FS.writeBinFile ⟨outPath⟩ bytes
  let envAddr := Address.admissionHash bytes
  IO.println s!"[frontend compile] {elabEnv.constOrder.length} elaborated decl(s), {ixonEnv.consts.size} Ixon constant(s) → {outPath} ({bytes.size} bytes, env={envAddr})"
  return 0

def frontendCompileCmd : Cli.Cmd := `[Cli|
  compile VIA runFrontendCompile;
  "Parse, elaborate, canonicalize, and compile .ix/.lean source file(s) directly to a .ixe artifact"

  FLAGS:
    o, out : String; "Output .ixe file path (default: <first-file-stem>.ixe)."
    "import-ixe" : String; "Hydrate initial elaboration environment from an existing .ixe artifact."
    certified; "Compile through the formally certified Ix.Cert.compileReport pipeline."
    "check-resources"; "Run substructural resource admission checking (checkResources) on the compiled Ixon.Env."

  ARGS:
    ...files : String; "Input .ix or .lean source file(s)."
]

/-! ## `ix frontend check` -/

def runFrontendCheck (p : Cli.Parsed) : IO UInt32 := do
  let files := (p.variableArgsAs! String).toList
  if files.isEmpty then
    p.printError "error: must specify one or more .ix / .lean source files"
    return 1
  let useHints := p.hasFlag "verify-hints"
  match files with
  | [singlePath] =>
    let src ← IO.FS.readFile ⟨singlePath⟩
    match checkSourceResources src {} singlePath with
    | .error e =>
      p.printError s!"error: {e}"
      return 1
    | .ok (_, elabEnv, ixonEnv, _) =>
      if useHints then
        let hints ← match generateElabHints src singlePath with
          | .ok h => pure h
          | .error e => p.printError s!"error generating hints: {e}"; return 1
        match elabSourceWithHints src hints singlePath with
        | .ok _ => pure ()
        | .error e => p.printError s!"error verifying hints: {e}"; return 1
      IO.println s!"[frontend check] ok: {singlePath} ({elabEnv.constOrder.length} decls, {ixonEnv.consts.size} Ixon constants)"
      return 0
  | _ =>
    let mut modList : List (Ix.Name × String) := []
    for fPath in files do
      let src ← IO.FS.readFile ⟨fPath⟩
      modList := modList ++ [(moduleNameOfPath fPath, src)]
    match compileModuleDAGToIxon modList with
    | .error e =>
      p.printError s!"error: {e}"
      return 1
    | .ok (elabEnv, _, ixonEnv, _) =>
      match Ix.Resource.Addressed.checkResources ixonEnv {} with
      | .error e =>
        p.printError s!"error: resource check failed: {e}"
        return 1
      | .ok _ =>
        IO.println s!"[frontend check] ok: {files.length} modules ({elabEnv.constOrder.length} decls, {ixonEnv.consts.size} Ixon constants)"
        return 0

def frontendCheckCmd : Cli.Cmd := `[Cli|
  check VIA runFrontendCheck;
  "Parse, elaborate, compile to Ixon, and verify substructural resource contracts on .ix/.lean source file(s)"

  FLAGS:
    "verify-hints"; "Also generate and verify O(|stx|) ElabHints certificate checking on single-file input."

  ARGS:
    ...files : String; "Input .ix or .lean source file(s)."
]

/-! ## `ix frontend merge` -/

def runFrontendMerge (p : Cli.Parsed) : IO UInt32 := do
  let some leftArg := p.positionalArg? "left"
    | p.printError "error: must specify <left.ix>"; return 1
  let some rightArg := p.positionalArg? "right"
    | p.printError "error: must specify <right.ix>"; return 1
  let leftPath := leftArg.as! String
  let rightPath := rightArg.as! String
  let leftSrc ← IO.FS.readFile ⟨leftPath⟩
  let rightSrc ← IO.FS.readFile ⟨rightPath⟩

  let outcome ← match p.flag? "base" with
    | some baseFlag =>
      let baseSrc ← IO.FS.readFile ⟨baseFlag.as! String⟩
      match mergeSource3 baseSrc leftSrc rightSrc with
      | .ok o => pure o
      | .error e => p.printError s!"error in 3-way merge: {e}"; return 1
    | none =>
      match mergeSource2 leftSrc rightSrc with
      | .ok o => pure o
      | .error e => p.printError s!"error in 2-way merge: {e}"; return 1

  let finalSched ← match p.flag? "resolve" with
    | none => pure outcome.sched
    | some resFlag =>
      let spec := resFlag.as! String
      match spec.splitOn "=" with
      | [origStr, tagStr] =>
        let origName := Name.fromComponents (origStr.splitOn ".")
        match resolveConflictVariant outcome.sched origName tagStr with
        | .ok s => pure s
        | .error e => p.printError s!"error resolving conflict '{spec}': {e}"; return 1
      | _ =>
        p.printError s!"error: --resolve expects <DeclName>=<tag> (e.g. foo=_1), got '{spec}'"
        return 1

  let elabEnv ← match elabModuleSchedule finalSched with
    | .ok env => pure env
    | .error e => p.printError s!"error elaborating merged module: {e}"; return 1

  let formatted := formatModuleSchedule finalSched
  if let some outFlag := p.flag? "out" then
    let outPath := outFlag.as! String
    IO.FS.writeFile ⟨outPath⟩ (formatted ++ "\n")
    IO.println s!"[frontend merge] wrote merged source to {outPath} ({finalSched.modIdx.decls.size} decls, {outcome.conflicts.size} conflict(s), {elabEnv.constOrder.length} elaborated constants)"
  else
    IO.println formatted
    IO.eprintln s!"[frontend merge] {finalSched.modIdx.decls.size} decls, {outcome.conflicts.size} conflict(s), {elabEnv.constOrder.length} elaborated constants"
  return 0

def frontendMergeCmd : Cli.Cmd := `[Cli|
  merge VIA runFrontendMerge;
  "Run 2-way or 3-way AST & type-aware IxVCS module merge on .ix/.lean source files"

  FLAGS:
    base : String; "Optional common ancestor <base.ix> for 3-way type-contract-preserving merge."
    resolve : String; "Resolve a .#merge conflict variant via <DeclName>=<tag> (e.g. compute=_1)."
    o, out : String; "Write formatted merged module source to <out.ix> (prints to stdout if omitted)."

  ARGS:
    left  : String; "Left branch .ix/.lean source file."
    right : String; "Right branch .ix/.lean source file."
]

/-! ## `ix frontend format` -/

def runFrontendFormat (p : Cli.Parsed) : IO UInt32 := do
  let some fileArg := p.positionalArg? "file"
    | p.printError "error: must specify <file.ix>"; return 1
  let filePath := fileArg.as! String
  let src ← IO.FS.readFile ⟨filePath⟩
  let (stx, pEnv) ← match parseSource src filePath with
    | .ok r => pure r
    | .error e => p.printError s!"error parsing '{filePath}': {e}"; return 1
  let formatted := formatModule stx
  if p.hasFlag "check" then
    match parseSource formatted "<formatted>" pEnv with
    | .ok (stx2, _) =>
      if cmpSyntaxPure 512 stx stx2 != .eq then
        p.printError "error: round-trip AST mismatch after formatting"
        return 1
    | .error e =>
      p.printError s!"error re-parsing formatted output: {e}"
      return 1
  if let some outFlag := p.flag? "out" then
    IO.FS.writeFile ⟨outFlag.as! String⟩ (formatted ++ "\n")
  else
    IO.println formatted
  return 0

def frontendFormatCmd : Cli.Cmd := `[Cli|
  format VIA runFrontendFormat;
  "Pretty-print a .ix/.lean source file via Ix.Frontend.Format"

  FLAGS:
    o, out : String; "Write formatted output to file instead of stdout."
    check; "Verify that re-parsing the formatted output yields an identical AST."

  ARGS:
    file : String; "Input .ix or .lean source file."
]

/-! ## Top-level `ix frontend` -/

def runFrontend (p : Cli.Parsed) : IO UInt32 := do
  p.printHelp
  return 0

end Ix.Cli.FrontendCmd

open Ix.Cli.FrontendCmd in
def frontendCmd : Cli.Cmd := `[Cli|
  frontend VIA runFrontend;
  "Pure, certified Ix Frontend (compile, check, merge, format)"

  SUBCOMMANDS:
    frontendCompileCmd;
    frontendCheckCmd;
    frontendMergeCmd;
    frontendFormatCmd
]

end
