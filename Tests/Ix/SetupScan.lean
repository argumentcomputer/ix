/-
  The compile's setup scan over the Lean objects (`crates/ffi/src/lean_env/scan.rs`)
  against the decoding scan (`ix_compile::graph::setup_scan`), on `Init` plus
  constructed constants that exercise every error the scan detects.

  `rsSetupScanCompare` compares each constant's scan (references,
  source-contract flag, semantic result, groundedness result, inductive group)
  and then every assembled output (both directions of the reference graph, the
  immediately-ungrounded set with each error, the inductive groups, the source
  contracts and the semantic sources). It fails if the fast scan accepts a
  constant the decoding scan rejects, or gives up on one the decoding scan
  accepts.
-/
module

public import LSpec
public import Ix.Meta
public import Ix.SemanticContract

public section

open LSpec

namespace Tests.Ix.SetupScan

@[extern "rs_setup_scan_compare"]
opaque rsSetupScanCompare : @& List (Lean.Name × Lean.ConstantInfo) → IO String

open Lean in
private def ax (n : Name) (type : Expr) (lps : List Name := []) : Name × ConstantInfo :=
  (n, .axiomInfo { name := n, levelParams := lps, type := type, isUnsafe := false })

open Lean in
private def defn (n : Name) (type value : Expr) : Name × ConstantInfo :=
  (n, .defnInfo {
    name := n, levelParams := [], type := type, value := value, hints := .opaque
    safety := .safe, all := [n] })

open Lean in
private def induct (n : Name) (ctors : List Name) (type : Expr := .sort 1) :
    Name × ConstantInfo :=
  (n, .inductInfo {
    name := n, levelParams := [], type := type, numParams := 0, numIndices := 0
    all := [n], ctors := ctors, numNested := 0, isRec := false, isUnsafe := false
    isReflexive := false })

private def semantic : Ix.SemanticContract.Contract :=
  { kind := .all, binder := .many }

open Lean in
/-- One constant per check the scan makes, failing or passing. -/
private def cases : List (Name × ConstantInfo) :=
  let nat := Expr.const `Nat []
  -- Structurally equal subterms at different addresses.
  let twice (e : Unit → Expr) : Expr := .app (.app (.const `Nat.add []) (e ())) (e ())
  let natArrow (_ : Unit) : Expr := .forallE `x nat nat .default
  [ ax `SetupScanTest.missingRef (.const `SetupScanTest.Absent [])
  , ax `SetupScanTest.missingProj (.proj `SetupScanTest.AbsentStruct 0 (.sort 0))
  , ax `SetupScanTest.projOk (.proj `Prod 0 (.sort 0))
  , ax `SetupScanTest.looseBVar (.bvar 0)
  , ax `SetupScanTest.looseUnderBinder (.forallE `x (.sort 0) (.bvar 1) .default)
  , ax `SetupScanTest.looseInLet (.letE `x nat (.bvar 0) (.bvar 0) false)
  , ax `SetupScanTest.boundOk (.forallE `x (.sort 0) (.bvar 0) .default)
  , ax `SetupScanTest.fvar (.fvar ⟨`x⟩)
  , ax `SetupScanTest.mvar (.mvar ⟨`m⟩)
  , ax `SetupScanTest.undeclaredParam (.sort (.param `u))
  , ax `SetupScanTest.declaredParam (.sort (.max (.param `u) (.succ .zero))) [`u]
  , ax `SetupScanTest.levelMVar (.sort (.imax .zero (.mvar ⟨`l⟩)))
  , ax `SetupScanTest.constLevel (.const `List [.param `v]) [`w]
  , defn `SetupScanTest.shared (natArrow ()) (.lam `n nat (twice natArrow) .default)
  , defn `SetupScanTest.letOk nat (.letE `x nat (.lit (.natVal 3)) (.bvar 0) true)
  , ax `SetupScanTest.sourceContract
      (.mdata (({} : MData).setBool `ix.source.binder true) (.sort 0))
  , ax `SetupScanTest.otherMData
      (.mdata (({} : MData).setBool `borrowed true) (natArrow ()))
  , ax `SetupScanTest.semanticOk (semantic.attach (natArrow ()))
  , induct `SetupScanTest.MissingCtor [`SetupScanTest.MissingCtor.mk]
  , induct `SetupScanTest.WrongCtor [`SetupScanTest.boundOk]
  , induct `SetupScanTest.Ind [`SetupScanTest.Ind.mk]
  , (`SetupScanTest.Ind.mk, .ctorInfo {
      name := `SetupScanTest.Ind.mk, levelParams := []
      type := .const `SetupScanTest.Ind [], induct := `SetupScanTest.Ind, cidx := 0
      numParams := 0, numFields := 0, isUnsafe := false })
  , (`SetupScanTest.Ind.rec, .recInfo {
      name := `SetupScanTest.Ind.rec, levelParams := []
      type := .forallE `t (.const `SetupScanTest.Ind []) nat .default
      all := [`SetupScanTest.Ind], numParams := 0, numIndices := 0, numMotives := 1
      numMinors := 0, k := false, isUnsafe := false
      rules := [{ ctor := `SetupScanTest.Ind.mk, nfields := 0, rhs := .const `Nat.zero [] }] })
  , (`SetupScanTest.BadRec, .recInfo {
      name := `SetupScanTest.BadRec, levelParams := []
      type := nat, all := [], numParams := 0, numIndices := 0, numMotives := 0
      numMinors := 0, k := false, isUnsafe := false
      rules := [{ ctor := `SetupScanTest.Ind.mk, nfields := 0, rhs := .bvar 2 }] })
  ]

/-- Run the comparison on `consts`; `expect` checks the summary. -/
private def compare (label : String) (consts : List (Lean.Name × Lean.ConstantInfo))
    (expect : String → Option String) : IO (Bool × Nat × Nat × Option String) := do
  try
    let summary ← rsSetupScanCompare consts
    IO.println s!"[setup-scan] {label}: {summary}"
    match expect summary with
    | some err => return (false, 0, 0, some s!"{label}: {err}")
    | none => return (true, 0, 0, none)
  catch e =>
    return (false, 0, 0, some s!"{label}: {e}")

private def initTest : TestSeq :=
  .individualIO "setup scan over Lean objects = decoding scan (Init + cases)" none (do
    let env ← getCompileEnv #[`Init]
    compare "Init + cases" (cases ++ env.constants.toList) fun summary =>
      if (summary.splitOn ", 13 with errors").length != 2 then
        some s!"expected 13 constants with errors: {summary}"
      else if (summary.splitOn ", 1 source contracts").length != 2 then
        some s!"expected 1 source contract: {summary}"
      else if (summary.splitOn "semantic sources Ok(1)").length != 2 then
        some s!"expected 1 semantic source: {summary}"
      else none) .done

/-- Exactly one semantic error per run, so the old fold reports it
deterministically. -/
private def semanticErrorTests : TestSeq :=
  let nat := Lean.Expr.const `Nat []
  let base := [ax `Nat (.sort 1), ax `SetupScanTest.semanticOk
    (semantic.attach (.forallE `x nat nat .default))]
  .individualIO "setup scan: detached semantic frame" none
    (compare "detached frame"
      (ax `SetupScanTest.detached (semantic.attach (.sort 0)) :: base)
      fun s => if (s.splitOn "Err(").length == 2 then none else some s) .done ++
  .individualIO "setup scan: malformed semantic frame" none
    (compare "malformed frame"
      (ax `SetupScanTest.malformed (.mdata (({} : Lean.MData).setNat `ix.contract 2)
        (.forallE `x nat nat .default)) :: base)
      fun s => if (s.splitOn "Err(").length == 2 then none else some s) .done ++
  .individualIO "setup scan: semantic frame on an inductive" none
    (compare "annotated inductive"
      (induct `SetupScanTest.Annotated [] (semantic.attach (.forallE `x nat (.sort 1) .default))
        :: base)
      fun s => if (s.splitOn "Err(").length == 2 then none else some s) .done

def suite : List TestSeq := [initTest ++ semanticErrorTests]

end Tests.Ix.SetupScan
