import IxCCTests.Pipeline.Levels
import IxCC.Lam.Erase.Input

/-! Fixed-width words end to end (stage W1): the words fixture (`fixtures/ixon-v4/src-words`,
every operation of every width, compiled with `ix compile --equations --word-equations`), **each
root compiled alone** as `ixcc compile --root` compiles it, so the program holds only what that
root reaches.

* **The unboxing facts** (`facts`): in each root's program, every word entry's tower
  constructors (`UIntN.ofBitVec` at the operation's width and at its result width,
  `BitVec.ofFin`, `Fin.mk`) unbox at field 0, which erasure checks before it emits the word
  primitive (`Lam.Erase.Input.wordUnboxAtB`). The relevance annotation covers them because a
  word entry lists them as its runtime references (`Src.Program.runtimeRefs`); before that, a
  root's program annotated only the constructors its decisions match on, and the check failed on
  every root. Control: `Fin.mk` taken with one field is refused.
* **Every level** (`levels`): each root on 18 operations and 11 × 11 inputs at SrcEval, Lam,
  every Anf stage, Fir, Own, Cfg, Lir, Xv, Xl (the machines, the typed x86 machine and ByteEval,
  on every `machineEvery`-th case), against Lean's own `UIntN` operations (`oracle`, compiled to
  Lean's C implementations), and natively (with `--native`) on every case. Owed exceptions, at
  the word levels and natively only: a `UInt64` result at or above `2^63` fails with
  `natOverflow` (W1's tagged representation; `docs/roadmap.md`). `x < y` at `x = 2^63 − 1` is
  owed Lean's result: `UInt64.decLt`'s reference body computes `Nat.ble (x + 1) y`, which the
  shrink walk turns into `natBlt x y` (`Anf.Walk.succBle`), so no `x + 1` is built.
* **The routes** (`routes`, natively): `<` and `≤` at the tagged boundary under `--rc off`, `on`
  and `auto`.
* **The hint** (`cliHints`): `ixcc compile` prints one `hint:` line on standard error for the word
  operations a program reaches at run time without word entries, and none otherwise. -/

namespace IxCCTests.Pipeline.Words

open IxCC IxCC.Recheck IxCCTests.Src
open IxCC.Src (Width WordOp)
open IxCC.Sem (Obs)
open System

def ixe : FilePath := fixtures / "src-words" / "words.ixe"
def eqs : FilePath := fixtures / "src-words" / "words.equations.json"

/-- Lean's own operations (the fixture's source, compiled to Lean's C implementations). -/
def oracle : Width → Nat → Nat → Nat → Nat
  | .w8, op, a, b =>
    let x := a.toUInt8; let y := b.toUInt8
    match op with
    | 0 => (x + y).toNat | 1 => (x - y).toNat | 2 => (x * y).toNat | 3 => (x / y).toNat
    | 4 => (x % y).toNat | 5 => (x &&& y).toNat | 6 => (x ||| y).toNat | 7 => (x ^^^ y).toNat
    | 8 => (x <<< y).toNat | 9 => (x >>> y).toNat | 10 => (~~~x).toNat | 11 => (-x).toNat
    | 12 => if x = y then 1 else 0 | 13 => if x < y then 1 else 0 | 14 => if x ≤ y then 1 else 0
    | 15 => x.toUInt16.toNat | 16 => x.toUInt32.toNat | _ => x.toUInt64.toNat
  | .w16, op, a, b =>
    let x := a.toUInt16; let y := b.toUInt16
    match op with
    | 0 => (x + y).toNat | 1 => (x - y).toNat | 2 => (x * y).toNat | 3 => (x / y).toNat
    | 4 => (x % y).toNat | 5 => (x &&& y).toNat | 6 => (x ||| y).toNat | 7 => (x ^^^ y).toNat
    | 8 => (x <<< y).toNat | 9 => (x >>> y).toNat | 10 => (~~~x).toNat | 11 => (-x).toNat
    | 12 => if x = y then 1 else 0 | 13 => if x < y then 1 else 0 | 14 => if x ≤ y then 1 else 0
    | 15 => x.toUInt8.toNat | 16 => x.toUInt32.toNat | _ => x.toUInt64.toNat
  | .w32, op, a, b =>
    let x := a.toUInt32; let y := b.toUInt32
    match op with
    | 0 => (x + y).toNat | 1 => (x - y).toNat | 2 => (x * y).toNat | 3 => (x / y).toNat
    | 4 => (x % y).toNat | 5 => (x &&& y).toNat | 6 => (x ||| y).toNat | 7 => (x ^^^ y).toNat
    | 8 => (x <<< y).toNat | 9 => (x >>> y).toNat | 10 => (~~~x).toNat | 11 => (-x).toNat
    | 12 => if x = y then 1 else 0 | 13 => if x < y then 1 else 0 | 14 => if x ≤ y then 1 else 0
    | 15 => x.toUInt8.toNat | 16 => x.toUInt16.toNat | _ => x.toUInt64.toNat
  | .w64, op, a, b =>
    let x := a.toUInt64; let y := b.toUInt64
    match op with
    | 0 => (x + y).toNat | 1 => (x - y).toNat | 2 => (x * y).toNat | 3 => (x / y).toNat
    | 4 => (x % y).toNat | 5 => (x &&& y).toNat | 6 => (x ||| y).toNat | 7 => (x ^^^ y).toNat
    | 8 => (x <<< y).toNat | 9 => (x >>> y).toNat | 10 => (~~~x).toNat | 11 => (-x).toNat
    | 12 => if x = y then 1 else 0 | 13 => if x < y then 1 else 0 | 14 => if x ≤ y then 1 else 0
    | 15 => x.toUInt8.toNat | 16 => x.toUInt16.toNat | _ => x.toUInt32.toNat

def rootName : Width → String
  | .w8 => "Words.u8" | .w16 => "Words.u16" | .w32 => "Words.u32" | .w64 => "Words.u64"

def inputs : List Nat := [0, 1, 2, 8, 63, 64, 255, 256, 65536, 2 ^ 32 + 3, 2 ^ 63 - 1]

/-- The levels that run the tagged lowering (and natively). -/
def wordLevel (level : String) : Bool := ["lir", "xv", "xl", "x86", "bytes", "native"].contains level

/-- What a level owes on `(op, x, y)` at width `w`: Lean's value, or, at a word level, a failure
(`natOverflow`) where W1's tagged representation cannot hold the result. -/
def owed (w : Width) (level : String) (op x y : Nat) : Option Nat :=
  let r := oracle w op x y
  if wordLevel level && w == .w64 && r ≥ 2 ^ 63 then none
  else some r

/-- The root's program alone, as `ixcc compile --root` makes it. -/
def input (w : Width) : IO Input := ingressFile ixe eqs [rootName w]

/-- **The unboxing facts** in each root's program (see the module note). -/
def facts (a : Assert) : IO (Array String) := do
  let mut out := #[]
  for w in Width.all do
    let inp ← input w
    let s ← IO.ofExcept ((Recheck.produceSource {} inp).mapError (·.render))
    let I := Lam.Erase.Input.ofProgram s.src s.checked
    let entries := (List.range s.src.size).filterMap fun c =>
      match s.src.table.resolveOf c with
      | some (.word w' op _) => some (w', op)
      | _ => none
    let bad := entries.filter fun (w', op) => !(I.wordUnboxAtB w' && I.wordUnboxAtB (op.resultWidth w'))
    expect a (!entries.isEmpty) s!"{rootName w}: the program has word entries"
    expect a bad.isEmpty s!"{rootName w}: the unboxing check fails at {bad.map fun (w', op) => op.leanName w'}"
    let fin := I.known.finMk.getD 0
    expect a (I.known.finMk.isSome && !I.unboxesAt0B fin 1) s!"{rootName w}: Fin.mk taken with one field is refused"
    let widths := Width.all.filter fun w' => I.wordUnboxAtB w'
    out := out.push s!"{rootName w} alone: {entries.length} word entries, the check holds at each; \
      towers that erase to their number at {widths.map (·.name)}"
  return out

/-- **Every level**, and natively, for each root compiled alone (see the module note). -/
def levels (a : Assert) (native : Option Rt.Native.Tools) (machineEvery : Nat) : IO (Array String) := do
  let mut out := #[]
  for w in Width.all do
    let (c, ms) ← timed (Levels.compileFrom (rootName w) (← input w))
    let art := c.art
    let prims := (art.cfg.funList.flatMap fun (_, fd) => fd.blocks.flatMap fun b => b.body.filterMap fun
      | .bind _ (.fir (.prim op _)) => if op.isWord then some op.name else none
      | _ => none).eraseDups
    expect a (!prims.isEmpty) s!"{rootName w}: the compiled program applies word primitives"
    let levelNames := Levels.levelNames c
    let mut runs := 0
    let mut fails := 0
    let mut i := 0
    let mut cases : Array (List Nat) := #[]
    for op in List.range 18 do
      for x in inputs do
        for y in inputs do
          i := i + 1
          cases := cases.push [op, x, y]
          for level in levelNames do
            if (level == "x86" || level == "bytes") && i % machineEvery != 0 then continue
            let (shape, obs) ← Levels.runLevel c level [op, x, y]
            runs := runs + 1
            match owed w level op x y with
            | some r =>
              expect a (shape == "ok" && obs == some (.nat r))
                s!"{rootName w} op {op} {x} {y} at {level}: {shape} {repr obs}, Lean {r}"
            | none =>
              fails := fails + 1
              expect a (shape != "ok") s!"{rootName w} op {op} {x} {y} at {level}: ok, owed natOverflow"
    let mut line := s!"{rootName w} alone: compiled in {ms} ms, word primitives {prims.length}, \
      {levelNames.length} levels, {runs} level runs ({fails} owed natOverflow at word levels)"
    if let some nt := native then
      let some root := art.roots.head? | throw (IO.userError s!"{rootName w}: no root")
      let exe ← link nt s!"words_{rootName w}" art.object root.symbol
      let lines ← Rt.Native.run exe { ty := root.ty } cases.toList
      expectEq a lines.length cases.size s!"{rootName w} natively: one line per case"
      let mut nfail := 0
      for (l, xs) in lines.zip cases.toList do
        let (op, x, y) := (xs.getD 0 0, xs.getD 1 0, xs.getD 2 0)
        match owed w "native" op x y with
        | some r =>
          expect a (l.status == 0 && l.ok && l.obs == some (toString r))
            s!"{rootName w} op {op} {x} {y} natively: status {l.status} {l.obs}, Lean {r}"
        | none =>
          nfail := nfail + 1
          expect a (l.status != 0) s!"{rootName w} op {op} {x} {y} natively: status 0, owed natOverflow"
      line := line ++ s!"; natively {lines.length} cases ({nfail} owed natOverflow)"
    out := out.push line
  return out

/-- The comparisons at the tagged boundary. -/
def boundary : List Nat := [0, 1, 2 ^ 62, 2 ^ 63 - 2, 2 ^ 63 - 1]

/-- **`<` and `≤` at the boundary on every route, natively**: `Words.u64` compiled by `ixcc
compile` under `--rc off`, `on` and `auto`, its `lt` (op 13) and `le` (op 14) on every pair of
`boundary` in both orders, each giving Lean's result. `x < y` is `Nat.ble (x + 1) y` in
`UInt64.decLt`'s reference body; the shrink walk's `succBle` makes it `natBlt x y`, which compares
the tagged words and never builds `x + 1` (before it, `x = 2^63 − 1` failed with `natOverflow`). -/
def routes (a : Assert) (tools : Rt.Native.Tools) (work : FilePath) : IO (Array String) := do
  let c ← Levels.compileFrom (rootName .w64) (← input .w64)
  let some root := c.art.roots.head? | throw (IO.userError "Words.u64: no root")
  let cases := [13, 14].flatMap fun op => boundary.flatMap fun x => boundary.map fun y => [op, x, y]
  let mut out := #[]
  for rc in ["off", "on", "auto"] do
    let obj := work / s!"words-u64-rc-{rc}.o"
    let (_, code) ← IO.FS.withIsolatedStreams (IxCC.Cli.main
      ["compile", ixe.toString, "--equations", eqs.toString, "--root", "Words.u64", "--rc", rc, "-o", obj.toString])
    expect a (code == 0) s!"Words.u64 --rc {rc}: exit {code}"
    let exe ← link tools s!"words_u64_rc_{rc}" (← IO.FS.readBinFile obj) root.symbol
    let lines ← Rt.Native.run exe { ty := root.ty } cases
    expectEq a lines.length cases.length s!"Words.u64 --rc {rc}: one line per case"
    for (l, xs) in lines.zip cases do
      let (op, x, y) := (xs.getD 0 0, xs.getD 1 0, xs.getD 2 0)
      let r := oracle .w64 op x y
      expect a (l.status == 0 && l.ok && l.obs == some (toString r))
        s!"Words.u64 --rc {rc} op {op} {x} {y}: status {l.status} {l.obs}, Lean {r}"
    out := out.push s!"Words.u64 --rc {rc}: {lines.length} comparisons at the boundary, each Lean's"
  return out

/-- The `hint:` lines `ixcc compile` prints (in process, without `--stats`, so only the one line on
standard error can start so), and its exit code. -/
def hintLines (args : List String) : IO (UInt32 × List String) := do
  let (out, rc) ← IO.FS.withIsolatedStreams (IxCC.Cli.main args)
  return (rc, (out.splitOn "\n").filter (·.startsWith "hint:"))

/-- **The hint on the command line**: one `hint:` line on standard error when the program reaches
word operations at run time without word entries (the words fixture with its sidecar's `theorems`
emptied: `Words.u8` reaches 20), none when every one is an entry (the fixture as it is) or none is
reached (bench-k1's `fib`, a registered root); the exit code is 0 each time. -/
def cliHints (a : Assert) (work : FilePath) : IO (Array String) := do
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile eqs))
  let bare := work / "words-no-theorems.equations.json"
  IO.FS.writeFile bare (json.setObjVal! "theorems" (Lean.Json.arr #[])).compress
  let obj := (work / "words-hint.o").toString
  let (rc, lines) ← hintLines ["compile", ixe.toString, "--equations", bare.toString, "--root", "Words.u8", "-o", obj]
  expect a (rc == 0) s!"Words.u8 without word equations: exit {rc}"
  expectEq a lines [s!"hint: 20 word operations are reached at run time without an accepted word \
    equation and run their reference bodies (UInt8.toNat, UInt16.toNat, UInt8.toUInt16 and 17 more): \
    {Src.Table.wordEquationsAdvice}"]
    s!"Words.u8 without word equations: one hint line"
  let (rc, full) ← hintLines ["compile", ixe.toString, "--equations", eqs.toString, "--root", "Words.u8", "-o", obj]
  expect a (rc == 0 && full.isEmpty) s!"Words.u8 with its word equations: exit {rc}, no hint line ({full})"
  let (rc, fib) ← hintLines ["compile", (benchIxe "fib").toString, "--equations", (benchEqs "fib").toString, "-o", obj]
  expect a (rc == 0 && fib.isEmpty) s!"bench-k1 fib: exit {rc}, no hint line ({fib})"
  return #[s!"Words.u8 without word equations: {lines.headD ""}",
    "Words.u8 with them, and bench-k1 fib: no hint line"]

end IxCCTests.Pipeline.Words
