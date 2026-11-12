import IxCCTests.Src.Steps

/-! F6w, the fixed-width word rule of SrcEval (stage W1), on Lean 4.34.1's own word operations
(`fixtures/ixon-v4/src-words`, every operation of every width, compiled with
`ix compile --equations`).

* **The meaning lemma as a tested property** (`fireWord_refines_delta` of the data-types plan):
  for every primitive operation of every width, on every pair (or every one) of the boundary
  numbers below the width's size (`0`, `1`, around the shift widths, the top bit, the maximum),
  and `ofNat` on literals around every size, the rule's result (`Program.wordValue`) and SrcEval's
  own δ-run of the pinned constant's stored reference body under today's rules (no word entry in
  the table) are values SrcEval cannot tell apart: two towers of one width with one number, or one
  literal. Every case of the harness, not a sample.
* **The table**: with words enabled, the front end makes every primitive operation the root
  reaches a `word` entry (the producer finds each stored equation and `checkWord` accepts it);
  with words off, none. Erasure declines a word entry (`erase-word`) until the lowering
  exists.
* **Runs**: every root on every operation and boundary pair returns the same value with words on
  and off, that value is `WordOp.eval`'s (which `Words` compares with Lean's C implementations),
  and the run with words on makes fewer SrcEval steps than the reference bodies. -/

namespace IxCCTests.Src.WordRules

open IxCC IxCC.Src IxCCTests.Src
open IxCC.Sem (Result)

def dir : System.FilePath := fixtures / "src-words"

/-- The roots, one per width (the relevance annotation covers what a root reaches, so each run
loads the closure with its own root). -/
def roots : List (String × Width) :=
  [("Words.u8", .w8), ("Words.u16", .w16), ("Words.u32", .w32), ("Words.u64", .w64)]

/-- Boundary numbers below the width's size. -/
def bnd (w : Width) : List Nat :=
  ([0, 1, 2, 7, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64, 65, 127, 128, 255, 256, 65535, 65536,
    0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 0x100000000, 0x7FFFFFFFFFFFFFFF, 0x8000000000000000,
    0xFFFFFFFFFFFFFFFE, 0xFFFFFFFFFFFFFFFF] : List Nat).filter (· < w.size)

/-- `ofNat`'s literals, around every size. -/
def ofNatArgs : List Nat :=
  [0, 1, 255, 256, 65536, 0xFFFFFFFF, 0x100000000, 0xFFFFFFFFFFFFFFFF, 0x10000000000000000,
    0x10000000000000001]

/-- Values SrcEval cannot tell apart, for words: two towers of one width with one number, or
one literal (parameters and proofs are never read). -/
def wordEq (p : Program) (v v' : Value) : Bool :=
  (Width.all.any fun w => match p.asWord? w v, p.asWord? w v' with
    | some n, some n' => n == n'
    | _, _ => false) ||
  (match v, v' with
    | .lit n, .lit n' => n == n'
    | _, _ => false)

/-- SrcEval's δ-run of constant `c` on argument values, under the program's table. -/
def deltaRun (p : Program) (k : Nat) (c : CId) (args : List Value) : Result Value :=
  match evalConst p k [] c with
  | .ok f => applyAll p k f (args.map .val)
  | r => r

/-- The argument lists of an operation. -/
def cases (p : Program) (w : Width) (op : WordOp) : List (List Value) :=
  let word := fun n => (p.mkWord? w n).getD (.lit n)
  if op == .ofNat then ofNatArgs.map fun a => [.lit a]
  else if op.arity == 1 then (bnd w).map fun a => [word a]
  else (bnd w).flatMap fun a => (bnd w).map fun b => [word a, word b]

/-- The harness at one width: the number of cases, and the first mismatches. -/
def harness (p : Program) (w : Width) (clock : Nat) : Nat × List String := Id.run do
  let mut n := 0
  let mut bad : List String := []
  for op in WordOp.primitives w do
    match Table.wordOpId p w op with
    | none => bad := bad ++ [s!"{op.leanName w}: not in the closure"]
    | some c =>
      for args in cases p w op do
        n := n + 1
        let ok := match p.wordValue w op args, deltaRun p clock c args with
          | .ok v, .ok v' => wordEq p v v'
          | _, _ => false
        if !ok && bad.length < 5 then
          bad := bad ++ [s!"{op.leanName w} {args.map (fun v => (p.asWord? w v, v.shape))}"]
  return (n, bad)

/-- A root's value on `(op, a, b)` with words on and off, and the value `eval` gives. -/
def opNumber : WordOp → Width → Option Nat
  | .add, _ => some 0 | .sub, _ => some 1 | .mul, _ => some 2 | .div, _ => some 3
  | .mod, _ => some 4 | .land, _ => some 5 | .lor, _ => some 6 | .xor, _ => some 7
  | .shiftLeft, _ => some 8 | .shiftRight, _ => some 9 | .complement, _ => some 10
  | .neg, _ => some 11 | .decEq, _ => some 12 | .decLt, _ => some 13 | .decLe, _ => some 14
  | .convert t, w =>
    let others := Width.all.filter (· ≠ w)
    (others.idxOf? t).map (15 + ·)
  | _, _ => none

def run (a : Assert) : IO (List String) := do
  let mut lines : List String := []
  let mut total := 0
  for (root, w) in roots do
    let off ← loadPack (dir / "words.ixe") (dir / "words.equations.json")
    let on ← loadPack (dir / "words.ixe") (dir / "words.equations.json") { table := { words := true } }
    let rootOff ← rootNamed off root
    let rootOn ← rootNamed on root
    -- the harness, on the program without word entries
    expect a ((List.range off.program.size).all fun c =>
        !(off.program.table.resolveOf c matches some (.word ..)))
      s!"{root}: words off, no word entry"
    let (n, bad) := harness off.program w 100000
    expect a bad.isEmpty s!"{root}: F6w against the reference bodies: {bad}"
    total := total + n
    -- the table with words on: every primitive operation the root reaches
    let entries := (List.range on.program.size).filterMap fun c =>
      match on.program.table.resolveOf c with
      | some (.word w' op _) => some (w', op)
      | _ => none
    for op in WordOp.primitives w do
      expect a (entries.contains (w, op)) s!"{root}: {op.leanName w} is a word entry"
    -- until the lowering exists, erasure declines a word entry (and accepts the program without)
    expect a (match IxCC.Lam.erase on.program on.checked with
        | .error e => e.code == "erase-word"
        | .ok _ => false) s!"{root}: erasure declines a word entry"
    expect a (IxCC.Lam.erase off.program off.checked).toOption.isSome
      s!"{root}: erasure accepts the program without word entries"
    -- runs, on and off, against eval, at a few boundary pairs per operation
    let mut stepsOn := 0
    let mut stepsOff := 0
    for op in WordOp.ofWidth w do
      let some k := opNumber op w | continue
      for x in [0, 1, (bnd w).getLast!, w.size - 2] do
        for y in [0, 1, w.bits, (bnd w).getLast!] do
          let expected := (op.eval w x y).val
          let rOn ← runRoot on.program 100000 rootOn [k, x, y]
          let rOff ← runRoot off.program 100000 rootOff [k, x, y]
          expectEq a (natOf rOn) (some expected) s!"{root} {op.leanName w} {x} {y}, words on"
          expectEq a (natOf rOff) (some expected) s!"{root} {op.leanName w} {x} {y}, words off"
          let (_, tOn) := Steps.run on.program 100000 rootOn ([k, x, y].map .lit)
          let (_, tOff) := Steps.run off.program 100000 rootOff ([k, x, y].map .lit)
          stepsOn := stepsOn + tOn.charged
          stepsOff := stepsOff + tOff.charged
    expect a (stepsOn < stepsOff) s!"{root}: fewer steps with words on ({stepsOn} < {stepsOff})"
    lines := lines ++ [s!"{root}: {n} harness cases, {entries.length} word entries; " ++
      s!"steps {stepsOn} with words, {stepsOff} with the reference bodies"]
  expectEq a total 21996 "the harness's case count"
  return lines

end IxCCTests.Src.WordRules
