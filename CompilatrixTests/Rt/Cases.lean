import CompilatrixTests.Rt.Support

/-! Hand-written programs for `Rt.lower` (design note 04 §13, tests 1 and
6; M1.F6):

* **primitive sequences** (04 §2): every `Lam.Prim` on variables and on
  literals in either position, at 0, 1, small values, 2^31, 2^32, 2^62 ± 1
  and 2^63 − 1 (and shift counts and exponents around 63), against
  `Prim.sem`: the exact result `2r + 1`, or `fail natOverflow` exactly where
  the result (or a literal operand) is at least 2^63; comparisons also as
  the branch of a fused `Bool` switch;
* **values and control**: pairs, options, lists and a three-field tree built
  by the immortal bump and read back by type; `switch` on `Nat` keys (with a
  default), on an enumeration without a default, on cells only, and on mixed
  types; a critical edge; a literal too large for a word on one arm only; a
  dead block; each compared with Cfg (`compare`) and with its expected
  observation;
* **declines**: a string literal, a Nat constructor cell, a tag or field
  count beyond the header, a Fir form, an edge against the label order, no
  export;
* **`cx_init`**: a misaligned, too small or wrapping region fails with
  `heap`. -/

namespace CompilatrixTests.Rt.Cases

open Compilatrix CompilatrixTests.Src CompilatrixTests.Fir
open Compilatrix.Fir (Code Rhs Arg Rep)
open Compilatrix.Sem (Obs)

def natZ : Key.CtorKey := .src 100
def natS : Key.CtorKey := .src 101
def bF : Key.CtorKey := .src 200
def bT : Key.CtorKey := .src 201
def pairK : Key.CtorKey := .src 300
def noneK : Key.CtorKey := .src 400
def someK : Key.CtorKey := .src 401
def nilK : Key.CtorKey := .src 500
def consK : Key.CtorKey := .src 501
def aK : Key.CtorKey := .src 600
def bK : Key.CtorKey := .src 601
def cK : Key.CtorKey := .src 602
def leafK : Key.CtorKey := .src 700
def nodeK : Key.CtorKey := .src 701
/-- Beyond the header's limits (04 §3). -/
def wideK : Key.CtorKey := .src 800
def manyK : Key.CtorKey := .src 801

def ctors : List Lam.CtorInfo :=
  [{ key := natZ, tag := 0, arity := 0 }, { key := natS, tag := 1, arity := 1 },
   { key := bF, tag := 0, arity := 0 }, { key := bT, tag := 1, arity := 0 },
   { key := pairK, tag := 0, arity := 2 },
   { key := noneK, tag := 0, arity := 0 }, { key := someK, tag := 1, arity := 1 },
   { key := nilK, tag := 0, arity := 0 }, { key := consK, tag := 1, arity := 2 },
   { key := aK, tag := 0, arity := 0 }, { key := bK, tag := 1, arity := 0 }, { key := cK, tag := 2, arity := 0 },
   { key := leafK, tag := 0, arity := 0 }, { key := nodeK, tag := 1, arity := 3 },
   { key := wideK, tag := 0x7F00, arity := 1 }, { key := manyK, tag := 0, arity := 255 }]

def known : Lam.Known := { natZero := natZ, natSucc := natS, boolFalse := bF, boolTrue := bT }

def info (c : Key.CtorKey) : Fir.CtorInfo := (Fir.CtorInfo.ofKey ctors c).getD default

def v (x : Nat) : Arg := .var x
def n (k : Nat) : Arg := .lit (.nat k)

/-- A Fir program from functions (parameters, body); `exports` are roots. -/
def prog (fs : List (List Nat × Code)) (exports : List Nat := [0]) : FProgram :=
  let funs := fs.zipIdx.map fun ((ps, body), i) =>
    (i, ({ key := .const i [], params := ps.map (·, Rep.tobj), body, vars := 64, joins := 8 } : Fir.Fun))
  { funs := Src.NatMap.ofList funs, size := fs.length, exports, ctors, known }

def cfgOf (F : FProgram) : CProgram := Cfg.lower (Own.immortal F)

/-- Lowered to Lir with `cx_init` run. -/
def lirOf (C : CProgram) : IO (Compilatrix.Rt.Lowered × X86.Memory) := do
  let l ← IO.ofExcept ((Rt.lower {} C).mapError (·.render))
  let m ← IO.ofExcept (initRegion l)
  pure (l, m)

/-! ## Primitive sequences -/

def natMax : Nat := 2 ^ 63 - 1

def values : List Nat :=
  [0, 1, 2, 3, 5, 62, 63, 64, 65, 2 ^ 31, 2 ^ 32, 2 ^ 62 - 1, 2 ^ 62, 2 ^ 62 + 1, natMax - 1, natMax]

/-- Second operands of `natShl` and `natPow` (the exact oracle computes
`a · 2^b` and `a^b`). -/
def smallValues : List Nat := [0, 1, 2, 3, 5, 31, 32, 61, 62, 63, 64, 65, 100]

/-- Literals past the last word. -/
def bigLits : List Nat := [2 ^ 63, 2 ^ 64 + 3]

def allPrims : List Lam.Prim :=
  [.natAdd, .natSub, .natMul, .natDiv, .natMod, .natPow, .natGcd, .natBeq, .natBle, .natLand, .natLor,
   .natXor, .natShl, .natShr, .natPred, .natBlt]

/-- What Lir must give for `p` on these operands (`none`: an operand or the
result has no word, so `fail natOverflow`). -/
def expected (p : Lam.Prim) (args : List Nat) : Option Word :=
  if args.any (· ≥ Rt.natLimit) then none else
  match p.sem args with
  | some (.nat r) => Rt.natWord r
  | some (.bool b) => some (Rt.ctor0Word (if b then 1 else 0))
  | none => none

def outcomeWord : Lir.Outcome → Option (Option Word)
  | .ok ([w], _) => some (some w)
  | .resource .natOverflow => some none
  | _ => none

/-- One primitive program: operands as variables (`none`) or literals. -/
def primProg (p : Lam.Prim) (ops : List (Option Nat)) (fused : Bool) : FProgram :=
  let args := (ops.zipIdx).map fun (o, i) => match o with
    | some k => n k
    | none => v i
  let params := ops.zipIdx.filterMap fun (o, i) => if o.isNone then some i else none
  let body : Code :=
    if fused then .bind 10 (.prim p args) (.case 10 [.mk bF (.ret (n 0)), .mk bT (.ret (n 1))] none)
    else .bind 10 (.prim p args) (.ret (v 10))
  prog [(params, body)]

def secondValues (p : Lam.Prim) : List Nat :=
  if p == .natShl || p == .natPow then smallValues else values

/-- Every primitive at every operand shape and boundary value. -/
def prims (a : Assert) : IO (Array String) := do
  let mut runs := 0
  let mut overflows := 0
  for p in allPrims do
    let seconds := secondValues p
    let firsts := values
    let fusedToo := p == .natBeq || p == .natBle || p == .natBlt
    for fused in (if fusedToo then [false, true] else [false]) do
      -- a Bool from the fused switch is the literal 0 or 1
      let want := fun (xs : List Nat) =>
        if fused then (expected p xs).map fun w => if w == Rt.ctor0Word 1 then tag 1 else tag 0 else expected p xs
      let arity := p.arity
      -- variables in both positions
      let vv := primProg p (List.replicate arity none) fused
      let (l, m) ← lirOf (cfgOf vv)
      checkLir a l s!"{p.name} vv"
      let pairs := if arity == 1 then firsts.map ([·]) else firsts.flatMap fun x => seconds.map ([x, ·])
      for xs in pairs do
        let r ← runLir l 0 1000 xs m
        expect a (outcomeWord r == some (want xs)) s!"{p.name} {xs} (vv{if fused then ", fused" else ""}): Lir {lirOutcome r}, expected {want xs}"
        runs := runs + 1
        if want xs == none then overflows := overflows + 1
      -- a literal in one position (and big literals)
      for pos in (List.range arity) do
        let lits := (if pos == 0 then firsts else seconds) ++ bigLits
        for k in lits do
          let ops := (List.range arity).map fun i => if i == pos then some k else none
          let F := primProg p ops fused
          let (l, m) ← lirOf (cfgOf F)
          checkLir a l s!"{p.name} literal {k} at {pos}"
          let others := if pos == 0 then (if arity == 1 then [[]] else seconds.map ([·])) else firsts.map ([·])
          for ys in others do
            let xs := if pos == 0 then k :: ys else ys ++ [k]
            let r ← runLir l 0 1000 ys m
            expect a (outcomeWord r == some (want xs)) s!"{p.name} {xs} (literal at {pos}): Lir {lirOutcome r}, expected {want xs}"
            runs := runs + 1
            if want xs == none then overflows := overflows + 1
      -- both literals
      if arity == 2 then
        for x in [0, 3, natMax, 2 ^ 63] do
          for y in [0, 2, 63, 2 ^ 63] do
            if (p == .natShl || p == .natPow) && y > 100 then continue
            let (l, m) ← lirOf (cfgOf (primProg p [some x, some y] fused))
            let r ← runLir l 0 1000 [] m
            expect a (outcomeWord r == some (want [x, y])) s!"{p.name} {[x, y]} (literals): Lir {lirOutcome r}"
            runs := runs + 1
  return #[s!"{allPrims.length} primitives, {runs} runs at the boundaries ({overflows} natOverflow)"]

/-! ## Values and control -/

/-- `f0 a b = (a, b)`; `f1 n = if n = 0 then none else some n`; `f2 n =
list [n, …, 1]` (a loop consing onto an accumulator); `f3 n = sum (list n)`
(a mixed switch on the list); `f4 n = node leaf n (node leaf n leaf)` with
`f5` counting the node's third field through a cells-only switch with a
default; `f6 n` an enumeration switched without a default; `f7 n = if n is
a successor then n - 1 else 99`; `f8 a b = a < b` as a `Bool`. -/
def values' : FProgram := prog
  [ ([0, 1], .bind 2 (.ctor (info pairK) [v 0, v 1]) (.ret (v 2))),
    ([0], .case 0 [.mk natZ (.bind 1 (.ctor (info noneK) []) (.ret (v 1)))]
        (some (.bind 2 (.ctor (info someK) [v 0]) (.ret (v 2))))),
    ([0], .bind 1 (.ctor (info nilK) [])
        (.jp 0 [2, 3] true
          (.case 2 [.mk natZ (.ret (v 3)),
                    .mk natS (.bind 4 (.proj 2 natS 0) (.bind 5 (.ctor (info consK) [v 2, v 3])
                      (.jmp 0 [v 4, v 5])))] none)
          (.jmp 0 [v 0, v 1]))),
    ([0], .bind 1 (.call 2 [v 0])
        (.jp 0 [2, 3] true
          (.case 2 [.mk nilK (.ret (v 3)),
                    .mk consK (.bind 4 (.proj 2 consK 0) (.bind 5 (.proj 2 consK 1)
                      (.bind 6 (.prim .natAdd [v 3, v 4]) (.jmp 0 [v 5, v 6]))))] none)
          (.jmp 0 [v 1, n 0]))),
    ([0], .bind 1 (.ctor (info leafK) []) (.bind 2 (.ctor (info nodeK) [v 1, v 0, v 1])
        (.bind 3 (.ctor (info nodeK) [v 1, v 0, v 2]) (.ret (v 3))))),
    ([0], .bind 1 (.call 4 [v 0])
        (.jp 0 [2, 3] true
          (.case 2 [.mk nodeK (.bind 4 (.proj 2 nodeK 2) (.bind 5 (.prim .natAdd [v 3, n 1])
            (.jmp 0 [v 4, v 5])))] (some (.ret (v 3))))
          (.jmp 0 [v 1, n 0]))),
    ([0], .bind 1 (.prim .natMod [v 0, n 3])
        (.case 1 [.mk natZ (.bind 2 (.ctor (info aK) []) (.ret (v 2)))]
          (some (.bind 3 (.prim .natBeq [v 1, n 1])
            (.case 3 [.mk bT (.bind 4 (.ctor (info bK) []) (.ret (v 4)))]
              (some (.bind 5 (.ctor (info cK) []) (.ret (v 5))))))))),
    ([0], .case 0 [.mk natS (.bind 1 (.proj 0 natS 0) (.ret (v 1)))] (some (.ret (n 99)))),
    ([0, 1], .bind 2 (.prim .natBlt [v 0, v 1]) (.ret (v 2))),
    -- f9 x = case (f6 x) of a => 10 | b => 20 | c => 30, no default
    ([0], .bind 1 (.call 6 [v 0])
        (.case 1 [.mk aK (.ret (n 10)), .mk bK (.ret (n 20)), .mk cK (.ret (n 30))] none))]
  (List.range 10)

/-- Readback types: `Nat × Nat` (0), `Option Nat` (1), `List Nat` (2), a
tree (3), the enumeration (4), `Bool` (5). -/
def sig : Rt.Sig :=
  { inds := [[[.nat, .nat]], [[], [.nat]], [[], [.nat, .ind 2]], [[], [.ind 3, .nat, .ind 3]], [[], [], []], [[], []]] }

def cases : List (Nat × List Nat × Rt.FoTy × Option Obs) :=
  let list := fun (k : Nat) => (List.range k).foldl (fun acc i => Obs.ctor 1 [.nat (k - i), acc]) (Obs.ctor 0 [])
  [(0, [3, 4], .ind 0, some (.ctor 0 [.nat 3, .nat 4])),
   (0, [natMax, 0], .ind 0, some (.ctor 0 [.nat natMax, .nat 0])),
   (1, [0], .ind 1, some (.ctor 0 [])), (1, [7], .ind 1, some (.ctor 1 [.nat 7])),
   (2, [0], .ind 2, some (list 0)), (2, [1], .ind 2, some (list 1)), (2, [5], .ind 2, some (list 5)),
   (3, [0], .nat, some (.nat 0)), (3, [10], .nat, some (.nat 55)),
   (4, [6], .ind 3, some (.ctor 1 [.ctor 0 [], .nat 6, .ctor 1 [.ctor 0 [], .nat 6, .ctor 0 []]])),
   (5, [2], .nat, some (.nat 2)),
   (6, [3], .ind 4, some (.ctor 0 [])), (6, [4], .ind 4, some (.ctor 1 [])), (6, [5], .ind 4, some (.ctor 2 [])),
   (7, [0], .nat, some (.nat 99)), (7, [8], .nat, some (.nat 7)),
   (8, [2, 3], .ind 5, some (.ctor 1 [])), (8, [3, 2], .ind 5, some (.ctor 0 [])),
   (9, [3], .nat, some (.nat 10)), (9, [4], .nat, some (.nat 20)), (9, [8], .nat, some (.nat 30))]

def run (C : CProgram) (l : Compilatrix.Rt.Lowered) (m : X86.Memory) (f : Nat) (xs : List Nat)
    (ty : Option Rt.FoTy) (label : String) : Run :=
  { label, cfg := C, lir := l, root := f, args := xs, mem := m, ty := ty.map (sig, ·) }

/-- The Lir word and memory of a run, read back. -/
def lirObs (l : Compilatrix.Rt.Lowered) (m : X86.Memory) (f : Nat) (xs : List Nat) (ty : Rt.FoTy) :
    IO (Option Obs) := do
  match ← runLir l f 100000 xs m with
  | .ok ([w], m') => pure (Rt.readback sig ((limitOf defaultSize - base).toNat / 8) m' ty w)
  | _ => pure none

/-! ## Direct Cfg -/

def psig : Own.PSig := Own.PSig.plain .tobj

def cfgFun (i : Nat) (blocks : List Cfg.Block) : Cfg.Fun :=
  let arity := ((blocks.head?.map (·.params.length)).getD 0)
  { key := .const i [], sig := { params := List.replicate arity psig, result := .shared }, blocks, vars := 64 }

def cfgProg (fs : List (List Cfg.Block)) : CProgram :=
  { funs := Src.NatMap.ofList (fs.zipIdx.map fun (bs, i) => (i, cfgFun i bs)), size := fs.length
    exports := [0], ctors, known }

def ps (xs : List Nat) : List (Nat × Own.PSig) := xs.map (·, psig)
def e (t : Nat) (args : List Arg := []) (back := false) : Cfg.Edge := { target := t, args, back }

/-- A switch whose false arm reaches the join block directly while the true
arm goes through a block: the edge from the switch into the join is critical
(split by `Lir.SplitEdges`). And a switch with both arms into one block. -/
def critical : CProgram := cfgProg
  [[{ params := ps [0, 1], body := [.bind 2 (.fir (.prim .natBle [v 0, v 1]))], term := .switch 2 [(bF, e 2 [v 0]), (bT, e 1)] none },
    { term := .jump (e 2 [v 1]) },
    { params := ps [3], body := [.bind 4 (.fir (.prim .natAdd [v 3, n 100]))], term := .ret (v 4) }],
   [{ params := ps [0], term := .switch 0 [(natZ, e 1 [n 1]), (natS, e 1 [n 2])] none },
    { params := ps [1], term := .ret (v 1) }]]

/-- A literal past the last word on one edge only; a dead block. -/
def bigEdge : CProgram := cfgProg
  [[{ params := ps [0], term := .switch 0 [(natZ, e 1 [n (2 ^ 63)]), (natS, e 1 [n 5])] none },
    { params := ps [1], term := .ret (v 1) },
    { term := .ret (n 0) }]]

def declines : List (String × CProgram × String) :=
  [("a string literal", cfgOf (prog [([0], .bind 1 (.arg (.lit (.str "s"))) (.ret (v 1)))]), "rt.string"),
   ("a Nat constructor cell", cfgOf (prog [([0], .bind 1 (.ctor (info natS) [v 0]) (.ret (v 1)))]), "rt.layout"),
   ("a tag beyond 0x7EFF", cfgOf (prog [([0], .bind 1 (.ctor (info wideK) [v 0]) (.ret (v 1)))]), "rt.layout"),
   ("255 fields", cfgOf (prog [([0], .bind 1 (.ctor (info manyK) (List.replicate 255 (v 0))) (.ret (v 1)))]), "rt.layout"),
   ("a Fir constructor in Cfg", cfgProg [[{ params := ps [0], body := [.bind 1 (.fir (.ctor (info pairK) [v 0, v 0]))], term := .ret (v 1) }]], "rt.form"),
   ("a back edge to a later block", cfgProg [[{ params := ps [0], term := .jump (e 1 [] true) }, { term := .ret (v 0) }]], "rt.edge"),
   ("a forward edge to an earlier block", cfgProg [[{ params := ps [0], term := .jump (e 1) }, { term := .jump (e 1) }]], "rt.edge"),
   ("no export", { cfgOf (prog [([0], .ret (v 0))]) with exports := [] }, "rt.exports")]

def handWritten (a : Assert) : IO (Array String) := do
  let mut out := #[]
  -- values and control
  let C := cfgOf values'
  match Cfg.check C with
  | .ok () => expect a true ""
  | .error err => expect a false s!"values: Cfg not WellFormed: {err}"
  let (l, m) ← lirOf C
  checkLir a l "values"
  let mut t : Tally := {}
  for (f, xs, ty, want) in cases do
    t ← compare a (run C l m f xs (some ty) s!"f{f}") 100000 t
    let got ← lirObs l m f xs ty
    expect a (got == want) s!"f{f} {xs}: Lir reads back {repr got}, expected {repr want}"
  -- lists on object areas of every size up to the one that fits
  let need := Compilatrix.Rt.cellBytes 2 * 5
  for cap in (List.range (need / 8 + 1)).map (8 * ·) do
    t ← compare a { run C l (withLimit m cap) 2 [5] (some (.ind 2)) s!"list 5 in {cap} bytes" with capacity := cap } 100000 t
  out := out.push s!"values and control: {t.render}"
  -- a critical edge and a literal past the last word
  for (label, C, runs) in [("critical", critical, [(0, [2, 3]), (0, [3, 2]), (1, [0]), (1, [4])]),
                           ("big literal on one edge", bigEdge, [(0, [0]), (0, [3])])] do
    match Cfg.check C with
    | .ok () => expect a true ""
    | .error err => expect a false s!"{label}: Cfg not WellFormed: {err}"
    let (l, m) ← lirOf C
    checkLir a l label
    let mut u : Tally := {}
    for (f, xs) in runs do
      u ← compare a (run C l m f xs (some .nat) label) 100000 u
    out := out.push s!"{label}: {u.render}"
  -- the literal fails only on its edge; the dead block is gone
  let (l, m) ← lirOf bigEdge
  expect a ((← runLir l 0 10 [0] m) matches .resource .natOverflow) "bigEdge 0: not natOverflow"
  expect a (outcomeWord (← runLir l 0 10 [3] m) == some (some (tag 5))) "bigEdge 3: not 5"
  let f0 := l.program.funcs[0]!
  expect a (f0.blocks.size == 3 && f0.blocks.toList.any (·.term == .fail .natOverflow))
    s!"bigEdge: {f0.blocks.size} blocks, expected the head, the fail block and the join (the dead block dropped)"
  -- critical edges were split: more blocks than Cfg's, and the output has none left
  let (lc, _) ← lirOf critical
  expect a (lc.program.funcs[1]!.blocks.size == 4) s!"critical: f1 has {lc.program.funcs[1]!.blocks.size} blocks, expected 4 (two split edges)"
  -- declines
  for (label, C, code) in declines do
    match Rt.lower {} C with
    | .error err => expect a (err.render.startsWith code) s!"{label}: declined with {err.render}, expected {code}"
    | .ok _ => expect a false s!"{label}: not declined"
  out := out.push s!"{declines.length} declines with their codes"
  -- cx_init's checks
  expect a (initFails l 0x10004 4096) "cx_init accepts a misaligned region"
  expect a (initFails l 0x10000 4095) "cx_init accepts a region below 4 KiB"
  expect a (initFails l 0x7FFFFFFFFFFFF000 0x2000) "cx_init accepts a region past 2^63"
  expect a (initFails l 0xFFFFFFFFFFFFF000 0x2000) "cx_init accepts a wrapping region"
  expect a (!initFails l 0x10000 4096) "cx_init rejects a 4 KiB region"
  expect a ((initRegion l 4096).isOk) "cx_init on 4 KiB"
  out := out.push "cx_init: misaligned, small, past 2^63 and wrapping regions fail with heap"
  return out

end CompilatrixTests.Rt.Cases
