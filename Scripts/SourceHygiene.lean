import Lean

/-! Check current compiler terminology without a grandfather baseline.
The rules cover retired compiler names and private planning references;
they deliberately leave mathematical names, dependency pins and dates alone.
-/

namespace SourceHygiene

def has (text pattern : String) : Bool := (text.splitOn pattern).length > 1

def retiredNames : List String :=
  ["sourceClasses", "source_classes", "compileExprNoSurgery", "compileEquivalentMutConsts",
   "compileMutConstClass", "Ix.Tc.PrimAddrs", "Ix.Tc.primAddrSet", "Ix.Tc.reservedMarkerName",
   "compileEnvStreamed", "compileEnvWithRust", "compileLeanWithRust", "checkRsCmd", "validateRsCmd",
   "crates/kernel/", "crates/compile/", "check-rs", "ix_compile::", "rs_compile_env",
   "resourcePostStep"]

def privatePlans : List String := ["IXC-PLAN", "PRIMITIVES-DESIGN"]

def bannedSubstrings : List String :=
  ["ALPHA-COLLAPSE", "LOCALITY", "TRUST-CLOSURE", "AUX-CERT", "AuxGen",
   "SurgAlias", "HANDOFF-", "ix-certified-v3", "coordinator decision",
   "owner decision"]

def hasQueueLabel (text : String) : Bool :=
  (text.splitOn "CQ").tail.any fun suffix =>
    match suffix.toList with
    | c :: d :: _ => c.isDigit || (c.isUpper && (d == '.' || d.isDigit))
    | c :: [] => c.isDigit
    | [] => false

def hasRetiredOpen (text : String) : Bool :=
  (text.splitOn "\n").any fun line =>
    let words := line.trimAscii.toString.splitOn " "
    words.head? == some "open" && words.any fun word =>
      let opened := ((word.dropPrefix? "_root_.").map (·.toString)).getD word
      opened == "Ix.Tc" || opened.startsWith "Ix.Tc."

def violations (text : String) : List String :=
  (if hasQueueLabel text then ["numbered private work queue"] else []) ++
    (if hasRetiredOpen text then ["open of retired typechecker namespace"] else []) ++
    (privatePlans ++ bannedSubstrings ++ retiredNames).filter (has text)

def selfCheck : IO Unit := do
  for bad in ["-- CQ2.8 exact cache", "-- CQP.3 wrapper", "-- CQX.8 field test",
      "IXC-PLAN §12", "PRIMITIVES-DESIGN", "ALPHA-COLLAPSE.md §8.4",
      "LOCALITY.md", "TRUST-CLOSURE", "AUX-CERT", "AuxGen helper",
      "SurgAlias", "HANDOFF-2026", "ix-certified-v3",
      "coordinator decision, 2026-10-20", "owner decision",
      "Ix.Tc.PrimAddrs.canonical",
      "compileEnvStreamed", "compileEnvWithRust", "checkRsCmd",
      "Mirror crates/kernel/src/inductive.rs", "crates/compile/src/compile.rs", "ix check-rs --anon",
      "ix_compile::decompile", "[rs_compile_env]", "Ix.CompileM.resourcePostStep",
      "sourceClasses members", "compileEquivalentMutConsts sources", "open LSpec Ix.Tc",
      "open LSpec _root_.Ix.Tc", "open _root_.Ix.Tc.PrimAddrs"] do
    if (violations bad).isEmpty then throw <| IO.userError s!"scanner missed control: {bad}"
  for good in ["S3 object storage", "R1 and R2 are relations", "2026-10-28", "CQRS architecture",
      "sourceMembers members", "compileMutConstMembers sources", "fae62ca5", "#guard !allowedData `Ix.Tc",
      "open LSpec _root_.Ix", "open _root_.Ix.CompileM", "crates/ixon/src/shard.rs",
      "ix check-lean --anon", "crates/common/src/prim_addrs.rs"] do
    unless (violations good).isEmpty do throw <| IO.userError s!"scanner rejected ordinary text: {good}"

def sourceFile (path : System.FilePath) : Bool :=
  ["lean", "rs", "md"].contains (path.extension.getD "")

def files : IO (Array System.FilePath) := do
  let mut result : Array System.FilePath :=
    #["Ix.lean", "Main.lean", "Tests.lean", "Apps.lean", "MultiStark.lean", "README.md", "lakefile.lean"]
  for root in ["Ix", "IxC", "IxSharingVerify", "Tests", "crates", "docs", "Benchmarks", "Apps", "MultiStark"] do
    for path in ← System.FilePath.walkDir root (fun p =>
        pure (!([".lake", "target", ".git"].contains (p.fileName.getD "")))) do
      if sourceFile path then result := result.push path
  pure result

def check (paths : Array System.FilePath) : IO UInt32 := do
  let mut failures := 0
  for path in paths do
    let source ← IO.FS.readFile path
    if (violations source).isEmpty then continue
    for (line, index) in (source.splitOn "\n").zipIdx do
      for problem in violations line do
        IO.eprintln s!"{path}:{index + 1}: {problem}"
        failures := failures + 1
  if failures == 0 then
    IO.println s!"Source terminology: {paths.size} files checked."
    pure 0
  else
    IO.eprintln s!"Source terminology: {failures} violations."
    pure 1

end SourceHygiene

def main (args : List String) : IO UInt32 := do
  SourceHygiene.selfCheck
  if args == ["--self-test"] then
    IO.println "Source terminology scanner controls passed."
    return 0
  let paths ← if args.isEmpty then SourceHygiene.files else pure (args.toArray.map System.FilePath.mk)
  SourceHygiene.check paths
