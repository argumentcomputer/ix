import CompilatrixTests.Corpus.Manifest
import CompilatrixTests.Recheck.Artifact

/-! The corpus's kernel-recheck sample (MT.2): a few small corpus closures as
`Recheck.run`'s input, printed as Lean modules by the recheck artifact
printer (`CompilatrixTests.Recheck.Artifact`) into
`CompilatrixTests/Corpus/Artifacts/`, for the `decide +kernel` claims of
`CompilatrixTests.Corpus.Kernel.*` (the manual aggregate
`CompilatrixTests.Corpus.KernelSample`). `corpus kernel-artifacts` writes them;
with `--check` it compares the committed modules with a fresh ingress,
`produce` and native run. -/

namespace CompilatrixTests.Corpus.KernelGen

open System CompilatrixTests.Recheck

/-- The sample: manifest, fixture, root and module name. Small closures
covering mutual recursion (even-odd), an allocated tuple, shifts and a
`Bool` result. -/
def sample : List (FilePath × String × String × String) :=
  [("fixtures/ixon-v3/bench-k1/corpus.json", "even-odd", "entry", "CorpusEvenOdd"),
   ("fixtures/corpus/phase1-scalar/corpus.json", "tuple", "entry", "CorpusTuple"),
   ("fixtures/corpus/phase1-scalar/corpus.json", "natShiftr", "entry", "CorpusNatShiftr"),
   ("fixtures/corpus/phase1-scalar/corpus.json", "strictAndOr", "entryStrictAnd", "CorpusStrictAnd")]

def path (modName : String) : FilePath :=
  "CompilatrixTests/Corpus/Artifacts" / s!"{(modName.drop 6).toString}.lean"

def load (manifest : FilePath) (fixture root modName : String) : IO Artifact.Input := do
  let m ← Family.read manifest
  let some f := m.fixtures.find? (·.name == fixture) | throw (IO.userError s!"{manifest}: no fixture {fixture}")
  let dir : FilePath := m.directory
  let inp ← CompilatrixTests.Pipeline.ingressFile (dir / f.closure.path) (dir / f.equations.path) [root]
  Artifact.loadFrom s!"{fixture}/{root}" modName inp
    (some s!"The root `{root}` of the `{m.family}/{fixture}` corpus closure (`{m.directory}/{f.closure.path}`)")

def main (check : Bool) : IO UInt32 := do
  let mut stale := 0
  for (manifest, fixture, root, modName) in sample do
    let a ← load manifest fixture root modName
    let (text, stats) := Artifact.render a
    let file := path modName
    if check then
      if (← (IO.FS.readFile file).toBaseIO).toOption == some text then IO.println s!"{file}: current"
      else
        IO.eprintln s!"{file}: stale (run lake exe corpus kernel-artifacts)"
        stale := stale + 1
    else
      IO.FS.writeFile file text
      IO.println s!"{file}: {stats}"
  return if stale == 0 then 0 else 1

end CompilatrixTests.Corpus.KernelGen
