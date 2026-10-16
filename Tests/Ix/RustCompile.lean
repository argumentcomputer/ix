/-
  `rust-compile`: the Rust compiler's compile → serialize → decompile
  roundtrip over every constant of the test binary's environment (moved from
  the special case in `Tests/Main.lean`, unchanged, so that it is an ordinary
  registry entry and can be named with other entries).
-/
import Ix.Compile.SourceContract
import Lean

namespace Tests.Ix.RustCompile

/-- Runs the full compile → serialize → decompile roundtrip over the given
    constants and returns the number of failures (0 = clean): decompile
    mismatches, or a non-zero constant count if a phase aborted. -/
@[extern "rs_tmp_decode_const_map"]
opaque tmpDecodeConstMap : @& List (Lean.Name × Lean.ConstantInfo) → USize

def run (env : Lean.Environment) : IO UInt32 := do
  let all := env.constants.toList
  IO.println s!"Loaded environment with {all.length} constants"
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
  let consts := all.filter fun (n, _) => !inSourceContract n
  let annotated := consts.filter fun (_, c) => Ix.Compile.sourceHasAnnotations c
  unless annotated.isEmpty do
    IO.eprintln s!"[rust-compile] FAILED: {annotated.length} constant(s) outside \
      {sourceContract}.* carry source binder annotations: \
      {(annotated.take 10).map (·.1)}"
    return 1
  IO.println s!"[rust-compile] left out the {all.length - consts.length} constants of \
    {sourceContract}.*"
  let failures := tmpDecodeConstMap consts
  if failures != 0 then
    IO.eprintln s!"[rust-compile] FAILED: {failures} compile/decompile roundtrip failure(s)"
    return 1
  IO.println "[rust-compile] OK: compile → decompile roundtrip clean"
  return 0

end Tests.Ix.RustCompile
