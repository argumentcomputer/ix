/-
  `rust-compile`: the Rust compiler's compile → serialize → decompile
  roundtrip over the test binary's ordinary declarations. Annotated fixtures
  and their two harness wrappers are explicitly excluded; all remaining
  input must be grounded and covered by the roundtrip.
-/
import Ix.Compile.SourceContract
import Lean

namespace Tests.Ix.RustCompile

/-- Runs the full compile → serialize → decompile roundtrip over the given
    constants and returns the number of failures (0 = clean): decompile
    mismatches, or a non-zero constant count if a phase aborted. -/
@[extern "rs_tmp_decode_const_map"]
opaque tmpDecodeConstMap : @& List (Lean.Name × Lean.ConstantInfo) → USize

structure Selection where
  constants : List (Lean.Name × Lean.ConstantInfo)
  total : Nat
  sourceContractExcluded : Nat

/-- The whole test input, excluding annotated fixtures and their two registry
wrappers. No other ungrounded declaration may be silently skipped by the gate. -/
def selectInput (env : Lean.Environment) : Except String Selection := do
  let all := env.constants.toList
  -- Source binder annotations are the subject of the `source-contract`
  -- suite, whose modules (`Tests.Ix.SourceContract.*`) declare annotated
  -- fixtures; the Rust compiler's Phase 1 refuses them for the whole input.
  -- Those modules are left out of this roundtrip, and an annotated constant
  -- of any other module fails the suite rather than being dropped.
  let sourceContract := `Tests.Ix.SourceContract
  let moduleNames := env.allImportedModuleNames
  let inSourceContract (n : Lean.Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some i => match moduleNames[i]? with
      | some m => sourceContract.isPrefixOf m
      | none => false
    | none => false
  -- Tests.Main's registry mentions the excluded suite and main mentions that
  -- registry. They were previously dropped by grounding, while the roundtrip
  -- omitted ungrounded inputs from its comparison. Name and module must both
  -- match: this does not exclude another input's ordinary `main` declaration.
  let harness : Array Lean.Name := #[`registry, `main]
  for name in harness do
    let some idx := env.getModuleIdxFor? name
      | throw s!"[rust-compile] missing Tests.Main harness declaration {name}"
    unless moduleNames[idx]? == some `Tests.Main do
      throw s!"[rust-compile] {name} is not a Tests.Main harness declaration"
  let withoutContracts := all.filter fun (n, _) => !inSourceContract n
  let consts := withoutContracts.filter fun (n, _) => !harness.contains n
  let annotated := consts.filter fun (_, c) => Ix.Compile.sourceHasAnnotations c
  unless annotated.isEmpty do
    throw s!"[rust-compile] FAILED: {annotated.length} constant(s) outside \
      {sourceContract}.* carry source binder annotations: \
      {(annotated.take 10).map (·.1)}"
  return ⟨consts, all.length, all.length - withoutContracts.length⟩

def run (env : Lean.Environment) : IO UInt32 := do
  let selection ← IO.ofExcept (selectInput env)
  IO.println s!"Loaded environment with {selection.total} constants"
  IO.println s!"[rust-compile] left out {selection.sourceContractExcluded} constants of \
    Tests.Ix.SourceContract.* and exactly Tests.Main's registry/main wrappers"
  let failures := tmpDecodeConstMap selection.constants
  if failures != 0 then
    IO.eprintln s!"[rust-compile] FAILED: {failures} compile/decompile roundtrip failure(s)"
    return 1
  IO.println "[rust-compile] OK: compile → decompile roundtrip clean"
  return 0

/-- Exercise the real gate with a valid closed declaration and a missing
dependency. The latter must not disappear behind the grounding filter. -/
def coverageControl : IO UInt32 := do
  let validName := `Tests.Ix.RustCompile.Coverage.valid
  let invalidName := `Tests.Ix.RustCompile.Coverage.invalid
  let mk (name : Lean.Name) (type : Lean.Expr) : Lean.ConstantInfo :=
    .axiomInfo { name, levelParams := [], type, isUnsafe := false }
  let valid := tmpDecodeConstMap [(validName, mk validName (.sort (.succ .zero)))]
  let invalid := tmpDecodeConstMap [(invalidName,
    mk invalidName (.const `Tests.Ix.RustCompile.Coverage.missing []))]
  unless valid == 0 && invalid != 0 do
    IO.eprintln s!"[rust-compile-coverage] expected closed=0 and missing-dependency>0, got {valid}/{invalid}"
    return 1
  IO.println "[rust-compile-coverage] closed declaration passes; missing dependency fails the actual gate"
  return 0

end Tests.Ix.RustCompile
