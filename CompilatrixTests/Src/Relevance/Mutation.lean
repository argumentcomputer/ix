import CompilatrixTests.Src.Support
import CompilatrixTests.Src.Rules
import CompilatrixTests.Src.StuckEval

/-! Annotation mutation (design note 02 §13.2): flip one tag or record of an
accepted annotation. Tier S rejects what violates S1–S4 and tier C most of
the rest. For every accepted mutant SrcEval gives the original observation or
none (stuck, trap, timeout, or a value without readback); a *different*
observation fails the test. Every mutant also runs without the checker, which
tests the stronger claim that a wrong annotation only makes SrcEval stuck. -/

namespace CompilatrixTests.Src.Relevance.Mutation

open Compilatrix Compilatrix.Src Compilatrix.Src.Relevance CompilatrixTests.Src
open CompilatrixTests.Src.Rules (Gen)
open Compilatrix.Sem (Result Obs)

def flipRel : Rel → Rel
  | .rel => Rel.prf
  | _ => .rel

/-- Flip the annotation of the `target`-th tagged node, in `tagOrder`.
`variant` picks between a λ's class and its `propWhen`. -/
def mutateCounting (variant : Bool) (target : Nat) : Term → StateM Nat Term
  | .lam b d t => do
    let i ← get
    set (i + 1)
    if i == target then
      let b := if variant then { b with propWhen := match b.propWhen with
          | .never => .allZero []
          | .allZero _ => .never }
        else { b with rel := flipRel b.rel }
      return .lam b d t
    return .lam b d (← mutateCounting variant target t)
  | .app f a m r => do
    let f ← mutateCounting variant target f
    let i ← get
    set (i + 1)
    if i == target then return .app f a m (flipRel r)
    if r.alwaysIrr then return .app f a m r
    return .app f (← mutateCounting variant target a) m r
  | .letE c r ty v body => do
    let i ← get
    set (i + 1)
    if i == target then return .letE c (flipRel r) ty v body
    let v ← if r.alwaysIrr then pure v else mutateCounting variant target v
    return .letE c r ty v (← mutateCounting variant target body)
  | .proj s i e => return .proj s i (← mutateCounting variant target e)
  | t => pure t

def mutateNode (variant : Bool) (target : Nat) (t : Term) : Term :=
  ((mutateCounting variant target t).run 0).1

/-- One random mutant of an accepted annotation, read against the installed
program `pI`. -/
def mutant (pI : Program) (ann : Ann) (g : Gen) : Ann × String × Gen := Id.run do
  let (kind, g) := g.next 10
  if kind < 7 && !ann.nodes.isEmpty then
    let (ki, g) := g.next ann.nodes.size
    let (key, tags) := ann.nodes[ki]!
    if tags.isEmpty then return (ann, "none", g)
    let (ti, g) := g.next tags.size
    let (v, g) := g.next 2
    let some t := pI.termOf key | return (ann, "none", g)
    let t' := mutateNode (v == 1) ti t
    let nodes := ann.nodes.set! ki (key, t'.tagOrder #[])
    return ({ ann with nodes }, s!"node {repr key} #{ti}{if v == 1 then " propWhen" else ""}", g)
  else if kind < 9 then
    let cs := (Array.range ann.consts.size).filter fun c => (ann.constRel? c).isSome
    if cs.isEmpty then return (ann, "none", g)
    let (ci, g) := g.next cs.size
    let c := cs[ci]!
    let rel := (ann.constRel? c).get!
    let (pi, g) := g.next (rel.params.size + 1)
    let rel := if pi == rel.params.size then { rel with result := flipRel rel.result }
      else { rel with params := rel.params.modify pi flipRel }
    return ({ ann with consts := ann.consts.set! c (some rel) }, s!"ConstRel {pI.short c} #{pi}", g)
  else
    let cs := (Array.range ann.ctors.size).filter fun c =>
      match ann.ctorRel? c with
      | some r => !r.fields.isEmpty
      | none => false
    if cs.isEmpty then return (ann, "none", g)
    let (ci, g) := g.next cs.size
    let c := cs[ci]!
    let rel := (ann.ctorRel? c).get!
    let (fi, g) := g.next rel.fields.size
    let fields := rel.fields.modify fi fun
      | .keep => FieldClass.prf
      | _ => .keep
    return ({ ann with ctors := ann.ctors.set! c (some { fields }) }, s!"CtorRel {pI.short c} #{fi}", g)

/-- An outcome as an observation, if it has one. -/
def observe (p : Program) (keep : CId → Levels → Nat → Bool) : Result Value → Option Obs
  | .ok v => readback p keep v
  | _ => none

structure Tally where
  mutants : Nat := 0
  rejectedS : Nat := 0
  rejectedC : Nat := 0
  rejectedOther : Nat := 0
  acceptedSame : Nat := 0
  acceptedNone : Nat := 0
  uncheckedSame : Nat := 0
  uncheckedNone : Nat := 0
  /-- Accepted mutants with no observation, by outcome and stuck cause group. -/
  acceptedWhy : Array (String × Nat) := #[]
  /-- The mutations behind the first few accepted stuck runs. -/
  stuckExamples : Array String := #[]

/-- Why a run has no observation: its outcome, or its stuck cause group. -/
def why : StuckEval.Out Value → String
  | .ok _ => "no readback"
  | .error .timeout => "timeout"
  | .error .trap => "trap"
  | .error (.stuck c) => s!"stuck {c.group}: {c.name}"

def bump (xs : Array (String × Nat)) (k : String) : Array (String × Nat) :=
  match xs.findIdx? (·.1 == k) with
  | some i => xs.modify i fun (k, n) => (k, n + 1)
  | none => xs.push (k, 1)

def Tally.render (t : Tally) : String :=
  let why := (t.acceptedWhy.qsort (fun a b => a.1 < b.1)).toList.map fun (k, n) => s!"{k} {n}"
  s!"{t.mutants} mutants: rejected S {t.rejectedS}, C {t.rejectedC}, other {t.rejectedOther}; " ++
  s!"accepted with the same result {t.acceptedSame}, with no observation {t.acceptedNone} " ++
  s!"({String.intercalate ", " why}); " ++
  s!"unchecked same {t.uncheckedSame}, none {t.uncheckedNone}" ++
  (if t.stuckExamples.isEmpty then "" else s!"; e.g. {t.stuckExamples.toList}")

/-- Small inputs per fixture. -/
def smallArgs : String → List Nat
  | "fib" => [10]
  | "sum-loop" => [20]
  | "ackermann" => [2, 2]
  | "tak" => [6, 4, 2, 1]
  | "gcd" => [30, 12]
  | _ => []

def clock : Nat := 1000000

def fixture (a : Assert) (name : String) (count : Nat) (seed : Nat) : IO Tally := do
  let bytes ← IO.FS.readBinFile (fixtures / "bench-k1" / s!"{name}.ixe")
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (fixtures / "bench-k1" / s!"{name}.equations.json")))
  let hints ← IO.ofExcept (Hints.ofK1Json json)
  let env ← IO.ofExcept (Ixon.V3.decodeAnonymousEnv bytes)
  let cfg : LoadConfig := { typecheck := false }
  let (p0, _, _) ← IO.ofExcept ((prepare cfg env hints).mapError toString)
  let ann ← IO.ofExcept (annotate env p0)
  let (p1, checked, _) ← IO.ofExcept ((finish cfg hints p0 ann).mapError toString)
  let pI ← IO.ofExcept (install p0 ann)
  let args := smallArgs name
  let some root := p0.roots[0]?.map (·.2) | throw (IO.userError s!"{name}: no root")
  let original := observe p1 checked.keeps (run p1 clock root (args.map .lit))
  expect a original.isSome s!"{name}: the unmutated run has an observation"
  let mut g : Gen := { seed }
  let mut t : Tally := {}
  for _ in [0:count] do
    let (m, what, g1) := mutant pI ann g
    g := g1
    if what == "none" then continue
    t := { t with mutants := t.mutants + 1 }
    -- Through the checker.
    match finish cfg hints p0 m with
    | .error d =>
      if d.code.startsWith "relevance-S" then t := { t with rejectedS := t.rejectedS + 1 }
      else if d.code.startsWith "relevance-C" then t := { t with rejectedC := t.rejectedC + 1 }
      else t := { t with rejectedOther := t.rejectedOther + 1 }
    | .ok (pm, ch, _) =>
      let r := run pm clock root (args.map .lit)
      match observe pm ch.keeps r with
      | none =>
        let s := StuckEval.run pm clock root (args.map .lit)
        expect a (outcome r == s.outcome) s!"{name}: StuckEval disagrees with SrcEval on {what}"
        t := { t with acceptedNone := t.acceptedNone + 1, acceptedWhy := bump t.acceptedWhy (why s) }
        if s matches .error (.stuck _) && t.stuckExamples.size < 3 then
          t := { t with stuckExamples := t.stuckExamples.push s!"{what}: {why s}" }
      | some o =>
        expect a (some o == original) s!"{name}: accepted mutant {what} changed the result"
        t := { t with acceptedSame := t.acceptedSame + 1 }
    -- Without the checker: install, Lazify, run.
    match install p0 m with
    | .error _ => pure ()
    | .ok pm =>
      let pm := Lazify.run pm (m.nodes.map (·.1))
      let keep := fun (c : CId) (ls : Levels) (i : Nat) => match m.ctorRel? c with
        | some r => (r.fields[i]?.map fun cls => !cls.dropP (profileOf ls)).getD false
        | none => true
      match observe pm keep (run pm clock root (args.map .lit)) with
      | none => t := { t with uncheckedNone := t.uncheckedNone + 1 }
      | some o =>
        expect a (some o == original) s!"{name}: unchecked mutant {what} changed the result"
        t := { t with uncheckedSame := t.uncheckedSame + 1 }
  return t

def run (a : Assert) (count : Nat := 400) : IO (Array String) := do
  let mut out := #[]
  for (name, i) in benchNames.zipIdx do
    let t ← fixture a name count (1000 + i)
    out := out.push s!"{name}: {t.render}"
  return out

end CompilatrixTests.Src.Relevance.Mutation
