/-
  `ix validate --path <file>`: run the 8-phase aux_gen validation pipeline
  against the Lean environment for any file.

  This is the CLI counterpart to the `validate-aux` test runner. Both funnel
  into the same Rust FFI (`rs_compile_validate_aux` in `src/ffi/lean_env.rs`),
  which performs:

    1. Compilation succeeds (every input constant gets an address)
    2. Aux_gen congruence (post-compile: decompiled aux_gen ≡ Lean's)
    3. No ephemeral leaks in the Ixon env
    4. Alpha-equivalence group canonicity
    5. Decompilation with debug info
    6. Aux congruence roundtrip (no-debug decompile ≡ Lean's)
    7. Decompilation without debug info (serialize → deserialize)
    7b. Per-constant roundtrip fidelity
    8. Nested inductive detection verification

  Separate from `ix compile` because validation is expensive (runs compile
  twice, decompile twice, and alpha-equivalence checks) and primarily useful
  as a correctness gate. The `compile` command is the fast production path.

  Separate from the `lake test` binary because we don't want Mathlib (or any
  large file's transitive imports) to be a compile-time dep of the test
  suite — it'd force the test binary to rebuild on every Mathlib update.
-/
module
public import Cli
public import Ix.Common
public import Ix.CompileM
public import Ix.Meta

public section

open System (FilePath)

/-- Collect the transitive closure of constants referenced by a set of seed
names. Mirrors the identically-named helper in `Tests/Ix/Compile/ValidateAux.lean`
so the CLI and test runner share the same dep-discovery semantics.

Walks each seed's type + value + recursor rules + ctor/all links until no
new names are discovered. The returned list preserves the source environment's
iteration order over the computed name set. -/
partial def collectDeps (env : Lean.Environment) (seeds : List Lean.Name)
    : List (Lean.Name × Lean.ConstantInfo) := Id.run do
  let mut needed : Std.HashSet Lean.Name := {}
  let mut worklist := seeds
  while !worklist.isEmpty do
    match worklist with
    | [] => break
    | n :: rest =>
      worklist := rest
      if needed.contains n then continue
      needed := needed.insert n
      if let some ci := env.constants.find? n then
        let mut refs : Lean.NameSet := ci.type.getUsedConstantsAsSet
        match ci with
        | .defnInfo v =>
          for r in v.value.getUsedConstantsAsSet do refs := refs.insert r
        | .thmInfo v =>
          for r in v.value.getUsedConstantsAsSet do refs := refs.insert r
        | .opaqueInfo v =>
          for r in v.value.getUsedConstantsAsSet do refs := refs.insert r
        | .inductInfo v =>
          for ctorName in v.ctors do
            refs := refs.insert ctorName
            if let some ctorCi := env.constants.find? ctorName then
              for r in ctorCi.type.getUsedConstantsAsSet do refs := refs.insert r
          for mutName in v.all do
            refs := refs.insert mutName
        | .ctorInfo v =>
          refs := refs.insert v.induct
        | .recInfo v =>
          for mutName in v.all do
            refs := refs.insert mutName
          for rule in v.rules do
            for r in rule.rhs.getUsedConstantsAsSet do refs := refs.insert r
        | _ => pure ()
        for r in refs do
          if !needed.contains r then
            worklist := r :: worklist
  env.constants.toList.filter fun (n, _) => needed.contains n

/-- Strip ASCII whitespace from both ends of `s`. We roll our own because
`String.trim` was deprecated in favor of slice-returning variants, and we
need a `String → String` shape for `.toName`. -/
private def asciiTrim (s : String) : String :=
  let cs := s.toList.dropWhile Char.isWhitespace
  String.ofList (cs.reverse.dropWhile Char.isWhitespace).reverse

/-- Parse a comma-separated namespace filter like `"Aesop,SetTheory.PGame"` into
a list of `Lean.Name` prefixes. Empty entries are dropped. -/
def parsePrefixes (s : String) : List Lean.Name :=
  (s.splitOn ",").filterMap fun raw =>
    let trimmed := asciiTrim raw
    if trimmed.isEmpty then none else some trimmed.toName

def runValidateCmd (p : Cli.Parsed) : IO UInt32 := do
  let some path := p.flag? "path"
    | p.printError "error: must specify --path"
      return 1
  let pathStr := path.as! String

  -- `buildFile` also runs `lake exe cache get` if the target depends on
  -- Mathlib, so large-env validation (`Benchmarks/Compile/CompileMathlib.lean`)
  -- works out of the box without a prior `lake build`.
  buildFile pathStr
  let leanEnv ← getFileEnv pathStr

  -- Apply optional namespace filter — mirrors `Tests/Ix/Compile/ValidateAux.lean`.
  -- When `--prefix Aesop,Nat` is given, only constants whose name starts with
  -- one of those prefixes seed the dependency walk. The full transitive closure
  -- is still validated (so aux_gen's cross-module deps resolve correctly); the
  -- filter just narrows the "interesting" surface.
  let constList ← match p.flag? "ns" with
    | none => pure leanEnv.constants.toList
    | some flag =>
      let raw := flag.as! String
      let prefixes := parsePrefixes raw
      if prefixes.isEmpty then
        IO.println s!"[validate] warning: --ns '{raw}' parsed to empty list; validating full env"
        pure leanEnv.constants.toList
      else
        let seeds := leanEnv.constants.toList.filterMap fun (n, _) =>
          if prefixes.any (·.isPrefixOf n) then some n else none
        IO.println s!"[validate] filter: {prefixes.length} namespace(s), {seeds.length} seed constants"
        let closed := collectDeps leanEnv seeds
        IO.println s!"[validate] filter: {closed.length} constants after transitive-dep closure"
        pure closed

  IO.println s!"Running Ix validator on {pathStr}"
  IO.println s!"Total constants: {constList.length}"

  let start ← IO.monoMsNow
  let failures := Ix.CompileM.rsCompileValidateAuxFFI constList
  let elapsed := (← IO.monoMsNow) - start

  IO.println s!"[validate] total failures: {failures} (in {elapsed.formatMs})"
  return if failures == 0 then 0 else 1

def validateCmd : Cli.Cmd := `[Cli|
  validate VIA runValidateCmd;
  "Validate a Lean file through the full compile → decompile → roundtrip pipeline"

  FLAGS:
    path : String; "Path to file whose env should be validated"
    ns   : String; "Comma-separated Lean name prefixes to filter on (e.g. 'Aesop,SetTheory.PGame'). When set, only seeds matching any prefix are validated; transitive deps are pulled in automatically."
]

end
