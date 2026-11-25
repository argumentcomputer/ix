import IxCCTests.Anf.Support
import IxCC.Anf.Pipeline.Closures
import IxCC.Fir.Lower

/-! The array primitives end to end, below erasure (`plans/ONE-PIPELINE.md`, lane prims-core,
stage A). A hand-written Lam program whose roots (`Nat → Nat`) use `Lam.Prim.arr`:

* at Lam, every root on every argument gives what the list model says (`Src.ArrOp.eval`'s
  meaning on `List`, computed here independently with `List` functions), a trap for an
  out-of-range `get` or `set`;
* after ANF conversion, after every step of the middle end and after the closures step (P8 and
  the post-P8 steps; one root keeps a closure in an array), Anf agrees with Lam
  (`compareRun`: readback, traps, the timeout clause, tick dominance), so a dead `get` that would
  trap is kept by the shrink walk and a dead `push` may go;
* `Fir.lower` refuses the program with `fir.arrays`. -/

namespace IxCCTests.Anf.ArrayPrims

open IxCC IxCCTests.Src IxCCTests.Lam IxCCTests.Anf
open IxCC.Lam (Term)

def natZ : Key.CtorKey := .src 100
def natS : Key.CtorKey := .src 101
def bF : Key.CtorKey := .src 200
def bT : Key.CtorKey := .src 201

def arr (op : Src.ArrOp) (args : List Term) : Term := .prim (.arr op) args
def lit (n : Nat) : Term := .lit (.nat n)
def fn (b : Term) : Term := .lam .strict .many b
def n0 : Term := .var 0

/-- The roots, each `fun n => …`, with their list-model meaning (`none`: a trap). -/
def roots : List (String × Term × (Nat → Option Nat)) :=
  [("size (replicate n 3 ++ [n])",
      arr .size [arr .append [arr .replicate [n0, lit 3], arr .push [arr .empty [lit 0], n0]]],
      fun n => some (List.replicate n 3 ++ [n]).length),
   ("get (replicate n 5 ++ [n, 9]) n",
      arr .get [arr .push [arr .push [arr .replicate [n0, lit 5], n0], lit 9], n0],
      fun n => (List.replicate n 5 ++ [n, 9])[n]?),
   ("get (set (replicate 3 0) 1 n) 1",
      arr .get [arr .set [arr .replicate [lit 3, lit 0], lit 1, n0], lit 1],
      fun n => ((List.replicate 3 0).set 1 n)[1]?),
   ("get (replicate n 7) n (out of range)",
      arr .get [arr .replicate [n0, lit 7], n0],
      fun _ => none),
   ("a dead get out of range",
      .letE Anf.freshLet (arr .get [arr .empty [lit 0], n0]) (lit 42),
      fun _ => none),
   ("a dead push",
      .letE Anf.freshLet (arr .push [arr .empty [lit 0], n0]) (lit 42),
      fun _ => some 42),
   ("a closure stored in an array, read and applied",
      .app (arr .get [arr .push [arr .empty [lit 0], fn (.prim .natAdd [n0, lit 1])], lit 0]) n0 .strict,
      fun n => some (n + 1)),
   ("size (extract (replicate 10 1) n 7)",
      arr .size [arr .extract [arr .replicate [lit 10, lit 1], n0, lit 7]],
      fun n => some (Src.ArraySpec.extractList (List.replicate 10 1) n 7).length),
   ("get (set (replicate 2 0) n 1) 0",
      arr .get [arr .set [arr .replicate [lit 2, lit 0], n0, lit 1], lit 0],
      fun n => if n < 2 then ((List.replicate 2 0).set n 1)[0]? else none)]

def program : LProgram :=
  let gs : List IxCC.Lam.Global :=
    roots.zipIdx.map fun ((_, body, _), i) => { key := .const i [], body := fn body }
  { globals := Src.NatMap.ofList (gs.zipIdx.map fun (g, i) => (i, g)), size := gs.length
    roots := List.range gs.length
    ctors := [{ key := natZ, tag := 0, arity := 0 }, { key := natS, tag := 1, arity := 1 },
              { key := bF, tag := 0, arity := 0 }, { key := bT, tag := 1, arity := 0 }]
    known := { natZero := natZ, natSucc := natS, boolFalse := bF, boolTrue := bT } }

def args : List Nat := [0, 1, 2, 5, 9]

def clock : Nat := 200

def run (a : Assert) : IO (Array String) := do
  let L := program
  expect a (IxCC.Lam.wellFormed L) "the array program is not well formed"
  -- Lam against the list model
  let mut atLam := 0
  for ((label, _, meaning), r) in roots.zipIdx do
    for n in args do
      let got ← runLam L clock r [n]
      let ok := match meaning n, got with
        | some m, .ok (.lit (.nat m')) => m == m'
        | none, .trap => true
        | _, _ => false
      expect a ok s!"Lam: {label} at {n}: {lamOutcome got}, the list model says {meaning n}"
      atLam := atLam + 1
  -- Anf after conversion, every step of the middle end, and the closures step
  let P1 ← IO.ofExcept ((IxCC.Anf.convert L).mapError ("convert: " ++ ·))
  let tr ← IO.ofExcept ((IxCC.Anf.Pipeline.produce {} L).mapError ("produce: " ++ ·))
  let final := (tr.stages.getLast?.map (·.2)).getD P1
  let closed ← IO.ofExcept (IxCC.Anf.Pipeline.closures (L.roots.map fun _ => 1) final)
  let stages := [("P1", P1)] ++ tr.stages ++ [("closures", closed)]
  let mut t : Tally := {}
  for (name, A) in stages do
    checkScoped a A s!"arrays {name}"
    for (r, (label, _, _)) in (List.range roots.length).zip roots do
      for n in args do
        t ← compareRun a L A r [n] clock s!"arrays {name}: {label}" t
  expect a (t.trap > 0 && t.ok > 0) s!"arrays: no trap or no value among the runs ({t.render})"
  -- the dead `get` survives the walk; Fir declines array primitives
  let refused := match IxCC.Fir.lower closed with
    | .error (.arrays _) => true
    | _ => false
  expect a refused "Fir.lower does not refuse the array program with fir.arrays"
  let code := match IxCC.Fir.lower closed with
    | .error e => (e.render.splitOn ":").head!
    | .ok _ => "accepted"
  expect a (code == "fir.arrays") s!"Fir.lower's refusal code is {code}"
  return #[s!"arrays: {roots.length} roots × {args.length} arguments agree with the list model at Lam ({atLam} runs)",
    s!"arrays: Anf agrees with Lam after {stages.length} stages: {t.render}",
    s!"arrays: Fir.lower refuses with {code}"]

end IxCCTests.Anf.ArrayPrims
