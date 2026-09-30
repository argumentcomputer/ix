import CompilatrixTests.Lam.Support
import CompilatrixTests.Src.Relevance.Mutation

/-! Annotation mutation through erasure (design note 02 §13 item 2): the
relevance suite's mutant generator flips one tag or record of an accepted
annotation of each bench-k1 closure. Every mutant the checker accepts is
erased; an erased mutant must be `WellFormed` and `ModesOk`, and SrcEval and
Lam must agree on it at the same clock (a value with the same Lam-domain
observation, a trap, or a timeout), unless SrcEval is stuck, which imposes
nothing. A decline is counted by its code; a different observation fails. -/

namespace CompilatrixTests.Lam.Mutation

open Compilatrix Compilatrix.Src Compilatrix.Src.Relevance CompilatrixTests.Src
open CompilatrixTests.Lam
open CompilatrixTests.Src.Relevance.Mutation (mutant smallArgs)
open CompilatrixTests.Src.Rules (Gen)

structure MTally where
  mutants : Nat := 0
  rejected : Nat := 0
  erased : Nat := 0
  declines : Array (String × Nat) := #[]
  runs : Tally := {}

def bump (xs : Array (String × Nat)) (k : String) : Array (String × Nat) :=
  match xs.findIdx? (·.1 == k) with
  | some i => xs.modify i fun (k, n) => (k, n + 1)
  | none => xs.push (k, 1)

def MTally.render (t : MTally) : String :=
  let declines := t.declines.toList.map fun (k, n) => s!"{k} {n}"
  s!"{t.mutants} mutants: rejected by the checker {t.rejected}, erased {t.erased}, declined \
    {t.declines.foldl (· + ·.2) 0} {declines}; runs of erased mutants: {t.runs.render}"

def clock : Nat := 1000000

def fixture (a : Assert) (name : String) (count seed : Nat) : IO MTally := do
  let bytes ← IO.FS.readBinFile (fixtures / "bench-k1" / s!"{name}.ixe")
  let json ← IO.ofExcept (Lean.Json.parse
    (← IO.FS.readFile (fixtures / "bench-k1" / s!"{name}.equations.json")))
  let hints ← IO.ofExcept (Hints.ofK1Json json)
  let env ← IO.ofExcept (Ixon.V3.decodeAnonymousEnv bytes)
  let cfg : LoadConfig := { typecheck := false }
  let (p0, _, _) ← IO.ofExcept ((prepare cfg env hints).mapError toString)
  let ann ← IO.ofExcept (annotate env p0)
  let pI ← IO.ofExcept (install p0 ann)
  let args := smallArgs name
  let some root := p0.roots[0]?.map (·.2) | throw (IO.userError s!"{name}: no root")
  let mut g : Gen := { seed }
  let mut t : MTally := {}
  for _ in [0:count] do
    let (m, what, g1) := mutant pI ann g
    g := g1
    if what == "none" then continue
    t := { t with mutants := t.mutants + 1 }
    match finish cfg hints p0 m with
    | .error _ => t := { t with rejected := t.rejected + 1 }
    | .ok (pm, ch, _) =>
      match erase pm ch with
      | .error msg =>
        -- Every mutant the checker accepts is expected to erase.
        let code := ((msg.drop 1).takeWhile (· != ']')).toString
        expect a false s!"{name}: accepted mutant {what} is declined: {msg}"
        t := { t with declines := bump t.declines code }
      | .ok e =>
        t := { t with erased := t.erased + 1 }
        checkStatic a e s!"{name} mutant {what}"
        let runs ← compareRun a e root args clock s!"{name} mutant {what}" t.runs
        t := { t with runs }
  return t

def run (a : Assert) (count : Nat := 400) : IO (Array String) := do
  let mut out := #[]
  for (name, i) in benchNames.zipIdx do
    let t ← fixture a name count (1000 + i)
    out := out.push s!"{name}: {t.render}"
  return out

end CompilatrixTests.Lam.Mutation
