import IxCCTests.Src.Steps
import IxCCTests.Support.Bound

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
* **Out-of-range towers are stuck** (`outOfRange`): F6w reads a tower only when its number is
  below the width's size, so on a tower at or above it (which only a false proof builds) every
  primitive operation is stuck, where the reference body would compute.
* **The table**: with words enabled, the front end makes every primitive operation the root
  reaches a `word` entry (the sidecar's `theorems` list names each stored equation and
  `checkWord` accepts it; `proposals` checks that nothing else makes one); with words off, none.
  Erasure declines a word entry (`erase-word`) until the lowering exists.
* **A tampered word theorem is refused** (`tampered`), and where: the closure re-encoded with
  `UInt64.add`'s proposal naming a new record whose proof is ill-typed, whose proof is a
  non-standard axiom, or whose statement has its two sides swapped, is refused at ingress (the
  certified kernel's acceptance of the whole closure, stage `kernel`); a theorem with the right
  statement whose proof reaches a non-standard axiom, put past the kernel at the Src level, is
  refused by `checkWord` (its `checkAxiomClosure` walks the proof); another operation's theorem is
  refused by `checkWord`'s statement comparison (`proposals`).
* **Runs**: every root on every operation and boundary pair returns the same value with words on
  and off, that value is `WordOp.eval`'s (which `Words` compares with Lean's C implementations),
  and the run with words on makes fewer SrcEval steps than the reference bodies. -/

namespace IxCCTests.Src.WordRules

open IxCC IxCC.Src IxCCTests.Src
open IxCC.Sem (Result)

def dir : System.FilePath := fixtures / "src-words"

/-- The roots, one per width. -/
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

/-- Numbers at or above a width's size (a tower around one is built only by a false proof of
`Fin.mk`'s bound), and in-range partners. -/
def outs (w : Width) : List Nat := [w.size, w.size + 1, 2 * w.size - 1, 2 ^ 65 + 3]
def ins (w : Width) : List Nat := [0, 1, w.size - 1]

/-- **F6w is stuck on an out-of-range tower** (`asWord?` reads a tower only below its width's
size): every primitive operation but `ofNat` (whose argument is a literal, reduced at any size),
with an out-of-range tower in any argument position and the other argument in range or not, is
stuck; `asWord?` reads none of those towers and reads each in-range partner. Returns the number of
cases, how many of them SrcEval's δ-run of the reference body (no word entry) evaluates to a value
(the body does not look at the bound, so the rule is stuck where the body computes, never
different where the rule fires), and the first failures. -/
def outOfRange (p : Program) (w : Width) (clock : Nat) : Nat × Nat × List String := Id.run do
  let word := fun n => (p.mkWord? w n).getD (.lit n)
  let mut n := 0
  let mut delta := 0
  let mut bad : List String := []
  for x in outs w do
    if p.asWord? w (word x) != none then bad := bad ++ [s!"{w.name}: asWord? reads {x}"]
  for x in ins w do
    if p.asWord? w (word x) != some x then bad := bad ++ [s!"{w.name}: asWord? does not read {x}"]
  for op in (WordOp.primitives w).filter (· != .ofNat) do
    match Table.wordOpId p w op with
    | none => bad := bad ++ [s!"{op.leanName w}: not in the closure"]
    | some c =>
      let args : List (List Value) :=
        if op.arity == 1 then (outs w).map fun x => [word x]
        else (outs w).flatMap fun x =>
          [[word x, word x]] ++ (ins w).flatMap fun y => [[word x, word y], [word y, word x]]
      for as in args do
        n := n + 1
        if !(p.wordValue w op as matches .stuck) && bad.length < 5 then
          bad := bad ++ [s!"{op.leanName w} {as.map (·.shape)}: not stuck"]
        if deltaRun p clock c as matches .ok _ then delta := delta + 1
  return (n, delta, bad)

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

/-- The word entries of a table. -/
def wordEntries (p : Program) (t : Table) : List (CId × Width × WordOp × CId) :=
  (List.range p.size).filterMap fun c =>
    match t.resolveOf c with
    | some (.word w op thm) => some (c, w, op, thm)
    | _ => none

/-- **Where a word entry comes from: the sidecar's `theorems` list** (kind `word`), never a search
of the closure. The fixture's sidecar names every primitive operation of every width with its
theorem (68); with them the table has 68 word entries, without them none (and a diagnostic per
pinned operation); a proposal whose theorem is another operation's, or whose subject is not a
pinned word operation, is refused with a diagnostic; the reader refuses an unknown kind. -/
def proposals (a : Assert) (p : Program) (props : Array Proposal) : IO Unit := do
  let words := props.filter (·.kind == .word)
  expectEq a words.size 68 "the sidecar names 68 word theorems"
  let cfg : Table.Config := { words := true }
  let (t, _, _) := Table.build cfg p props
  expectEq a (wordEntries p t).length 68 "with the sidecar's proposals, 68 word entries"
  let others := props.filter (·.kind != .word)
  let (t0, d0, _) := Table.build cfg p others
  expectEq a (wordEntries p t0).length 0 "without word proposals, no word entry"
  expectEq a (d0.filter (·.message.startsWith "word: no accepted equation")).size 68
    "without word proposals, a diagnostic per pinned operation"
  -- the theorem of UInt64.add proposed for UInt64.sub, and the root proposed as a word operation
  let byName := fun (n : String) => words.find? (·.name? == some n)
  match byName "UInt64.add", byName "UInt64.sub" with
  | some add, some sub =>
    let swapped := others.push { sub with theorem? := add.theorem? } |>.push add
    let (t1, d1, _) := Table.build cfg p swapped
    let subId := (Table.addrIndex p)[sub.subject]?
    expect a (subId.isSome && (wordEntries p t1).all (some ·.1 != subId))
      "another operation's theorem is refused"
    expect a (d1.any (·.message.startsWith "word: the theorem does not state")) "with a diagnostic"
    let bogus := others.push { add with subject := add.theorem?.getD add.subject }
    let (t2, d2, _) := Table.build cfg p bogus
    expectEq a (wordEntries p t2).length 0 "a subject that is not a pinned word operation is refused"
    expect a (d2.any (·.message == "word: the subject is not a pinned word operation"))
      "with a diagnostic"
  | _, _ => expect a false "the sidecar names UInt64.add and UInt64.sub"
  let entry := fun (k : String) => Lean.Json.mkObj [("kind", k), ("subject", "x"),
    ("subject_address", toString add0), ("theorem", "y"), ("theorem_address", toString add0)]
  let sidecar := fun (k : String) => Lean.Json.mkObj [("format", "ixcc/k1-equations/1"),
    ("roots", Lean.Json.arr #[]), ("equations", Lean.Json.arr #[]),
    ("theorems", Lean.Json.arr #[entry k]), ("failures", Lean.Json.arr #[])]
  expect a ((Hints.ofK1Json (sidecar "word")).toOption.map (·.proposals.size) == some 1)
    "the reader takes a word theorem"
  expect a (Hints.ofK1Json (sidecar "csimp")).toOption.isNone "the reader refuses an unknown kind"
where
  add0 : Ixon.Address := Ixon.Address.replicate 7

/-! ### A tampered word theorem -/

/-- A `share` node resolved through the constant's sharing table (one level). -/
def unshare (c : Ixon.V3.Constant) : Ixon.V3.Expr → Ixon.V3.Expr
  | .share i => c.sharing[i.toNat]?.getD (.share i)
  | e => e

/-- The statement with its equation's two sides swapped: under the binders, `Eq T l r` becomes
`Eq T r l`. -/
partial def swapEq (c : Ixon.V3.Constant) (e : Ixon.V3.Expr) : Option Ixon.V3.Expr :=
  match unshare c e with
  | .all bc vc d b => (swapEq c b).map (.all bc vc d ·)
  | .app f r =>
    match unshare c f with
    | .app g l => some (.app (.app g r) l)
    | _ => none
  | _ => none

/-- A replacement of a theorem record: the records to store first, and the new theorem. -/
abbrev Tamper := Ixon.V3.Constant → Ixon.V3.Env → Option (Ixon.V3.Env × Ixon.V3.Constant)

/-- The record itself (the control: re-stored, the same address). -/
def same : Tamper := fun c env => some (env, c)

/-- The proof replaced by the statement (a proposition, not a proof of itself). -/
def illTypedProof : Tamper := fun c env =>
  match c.info with
  | .defn d => some (env, { c with info := .defn { d with value := d.typ } })
  | _ => none

/-- The proof replaced by a non-standard axiom of the same statement. -/
def axiomProof : Tamper := fun c env =>
  match c.info with
  | .defn d =>
    let (env, ax) := IxCCTests.IxonV3.Builder.store env { c with info := .axio ⟨false, d.lvls, d.typ⟩ }
    some (env, { c with info := .defn { d with value := .ref c.refs.size.toUInt64 #[] }
                        refs := c.refs.push ax })
  | _ => none

/-- The statement's two sides swapped, the proof kept. -/
def swappedStatement : Tamper := fun c env =>
  match c.info with
  | .defn d => (swapEq c d.typ).map fun t => (env, { c with info := .defn { d with typ := t } })
  | _ => none

/-- The words closure with `subject`'s word theorem replaced by `t`'s record (stored under its
own address, the original kept), re-encoded by the suites' envelope writer and decoded again, and
the hints with `subject`'s word proposal naming the new record. -/
def tamper (env : Ixon.V3.Env) (hints : Hints) (subject : String) (t : Tamper) :
    IO (Ixon.V3.Env × Hints × Bool) := do
  let some i := hints.proposals.findIdx? (fun p => p.kind == .word && p.name? == some subject)
    | throw (IO.userError s!"no word proposal for {subject}")
  let prop := hints.proposals[i]!
  let some ta := prop.theorem? | throw (IO.userError s!"{subject}: no theorem")
  let some raw := env.consts[ta]? | throw (IO.userError s!"{subject}: theorem not stored")
  let c ← IO.ofExcept ((Ixon.V3.decodeConstant raw).map (·.value))
  let some (env, c') := t c env | throw (IO.userError s!"{subject}: the tamper does not apply")
  let (env, a') := IxCCTests.IxonV3.Builder.store env c'
  let some bytes := IxCCTests.Support.Bound.bytes env
    | throw (IO.userError "the words closure is not role-bound")
  let env ← IO.ofExcept (Ixon.V3.decodeAnonymousEnv bytes)
  return (env, { hints with proposals := hints.proposals.set! i { prop with theorem? := some a' } },
    a' == ta)

/-- **A word theorem is read with its proof, and a tampered one is refused**, at the stage each
assertion names. The control (the record re-stored) loads with 68 word entries, each theorem read
with its proof (a proposal's theorem is a proof seed once its subject is reached), and the unread
marker in its place (the theorem recorded as read by statement) gets no entry; with `Words.u8`
the only root, `UInt64.add` and its theorem are not read at all. The three tampered closures are
refused by the kernel's acceptance at ingress; at the Src level, past the kernel, a theorem with
`UInt64.add`'s statement whose proof is a non-standard axiom gets no word entry, `checkWord`'s
`checkAxiomClosure` naming the axiom. -/
def tampered (a : Assert) : IO Unit := do
  let bytes ← IO.FS.readBinFile (dir / "words.ixe")
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (dir / "words.equations.json")))
  let env ← IO.ofExcept (Ixon.V3.decodeAnonymousEnv bytes)
  let hints ← IO.ofExcept (Hints.ofK1Json json)
  let cfg : LoadConfig := { table := { words := true } }
  let load := fun (env : Ixon.V3.Env) (hints : Hints) => loadEnv cfg env hints
  -- the control: the same record, the same address, 68 word entries
  let (env0, hints0, sameAddr) ← tamper env hints "UInt64.add" same
  expect a sameAddr "tamper control: the re-stored record keeps its address"
  let control := load env0 hints0
  match control with
  | .ok l =>
    let p := l.program
    let entries := wordEntries p p.table
    expectEq a entries.length 68 "tamper control: the re-encoded closure has 68 word entries"
    -- every word entry's theorem was read with its proof (a proposal's theorem is a proof seed
    -- once its subject is reached), so `checkWord`'s `checkAxiomClosure` walked a proof, never
    -- the unread marker
    expect a (entries.all fun (_, _, _, thm) => !p.byStatement.contains thm &&
        match p.decl? thm with
        | some (.defn .thm _ _ _ v) => v != Term.unreadProof
        | _ => false)
      "every word entry's theorem is read with its proof"
    -- the unread marker, were a word theorem read by statement, is refused by `checkWord`
    match entries.find? fun (f, _, _, _) => some (p.addr f) == ((hints.proposals.find? fun q =>
        q.kind == .word && q.name? == some "UInt64.add").map (·.subject)) with
    | some (f, _, _, thm) =>
      let pb := { p with byStatement := p.byStatement.insert thm }
      let (t, d, _) := Table.build cfg.table pb hints.proposals
      expect a ((wordEntries pb t).all (·.1 != f))
        "a word theorem read by statement gets no word entry"
      expect a (d.any (·.message.startsWith "word: the equation was read by its statement"))
        "with checkWord's diagnostic"
      -- and `checkAxiomClosure` alone refuses it too (both of its branches)
      expect a (Table.checkAxiomClosure pb thm matches .error _)
        "checkAxiomClosure refuses a theorem read by statement"
      expect a (Table.checkAxiomClosure p thm matches .ok _)
        "checkAxiomClosure accepts the theorem read with its proof"
    | none => expect a false "UInt64.add is a word entry"
  | .error d => expect a false s!"tamper control: refused ({d.code}: {d.message})"
  -- a word proposal whose subject is not reached is not read: with `Words.u8` the only root,
  -- `UInt64.add`'s theorem is not in the program, `UInt8.add`'s is, read with its proof
  let u8 := { hints with roots := hints.roots.filter (·.2 == some "Words.u8") }
  expectEq a u8.roots.size 1 "the sidecar names the root Words.u8"
  match load env u8 with
  | .ok l =>
    let p := l.program
    let index := Table.addrIndex p
    let thmOf := fun (n : String) => (hints.proposals.find? fun q =>
      q.kind == .word && q.name? == some n).bind (·.theorem?)
    let subjOf := fun (n : String) => (hints.proposals.find? fun q =>
      q.kind == .word && q.name? == some n).map (·.subject)
    expect a ((subjOf "UInt64.add").all (index[·]?.isNone) &&
        (thmOf "UInt64.add").all (index[·]?.isNone))
      "Words.u8 alone: UInt64.add and its theorem are not read"
    expect a ((thmOf "UInt8.add").any fun x => match index[x]? with
        | some c => !p.byStatement.contains c
        | none => false)
      "Words.u8 alone: UInt8.add's theorem is read with its proof"
    let entries := wordEntries p p.table
    expect a ((WordOp.primitives .w8).all fun op => entries.any fun e => e.2.1 == .w8 && e.2.2.1 == op)
      "Words.u8 alone: every UInt8 primitive operation is a word entry"
    expect a (entries.all fun e => !(e.2.1 == .w64 && e.2.2.1 == .add))
      "Words.u8 alone: UInt64.add is not a word entry"
  | .error d => expect a false s!"Words.u8 alone: refused ({d.code}: {d.message})"
  let cases : List (String × Tamper) := [("an ill-typed proof", illTypedProof),
    ("a non-standard axiom as proof", axiomProof), ("the statement's sides swapped", swappedStatement)]
  for (label, t) in cases do
    let (env', hints', _) ← tamper env hints "UInt64.add" t
    match load env' hints' with
    | .ok _ => expect a false s!"tamper ({label}): accepted"
    | .error d =>
      expect a (d.code == "kernel")
        s!"tamper ({label}): refused at {d.code}, not at the kernel: {d.message}"
  -- past the kernel, at the Src level: `UInt64.add`'s statement, proved by a non-standard axiom
  match control with
  | .error _ => pure ()
  | .ok l =>
    let p := l.program
    let some add := hints.proposals.find? (fun q => q.kind == .word && q.name? == some "UInt64.add")
      | expect a false "the sidecar names UInt64.add"
    let index := Table.addrIndex p
    let some thm := add.theorem?.bind fun x => index[x]?
      | expect a false "UInt64.add's theorem read"
    match p.decl? thm with
    | some (.defn .thm .safe 0 ty _) =>
      let push := fun (p : Program) (d : Decl) =>
        let c := p.size
        let ad := IxCCTests.Src.Builder.fakeAddr (c + 1000000)
        (p.push { ref := .member ad 0, addr := ad, decl := d }, c)
      let (p1, ax) := push p (.axio false 0 ty)
      let (p2, bad) := push p1 (.defn .thm .safe 0 ty (.const ax []))
      let props := hints.proposals.map fun q =>
        if q.kind == .word && q.name? == some "UInt64.add" then { q with theorem? := some (p2.addr bad) }
        else q
      let (t, d, _) := Table.build cfg.table p2 props
      let addId := (Table.addrIndex p2)[add.subject]?
      expect a (addId.isSome && (wordEntries p2 t).all (some ·.1 != addId))
        "checkWord refuses a proof by a non-standard axiom"
      expect a (d.any (·.message.startsWith "theorem depends on a non-standard axiom"))
        s!"with checkAxiomClosure's diagnostic: {(d.map (·.message)).toList.take 3}"
    | _ => expect a false "UInt64.add's theorem is a safe level-monomorphic theorem"

def run (a : Assert) (verbose : Bool := false) : IO (List String) := do
  let mut lines : List String := []
  let t0 ← IO.monoMsNow
  let note := fun (s : String) => do
    if verbose then
      IO.println s!"    [{(← IO.monoMsNow) - t0} ms] {s}"
      (← IO.getStdout).flush
  let mut total := 0
  let mut totalOut := 0
  -- one load each way: the sidecar names the four roots, so the annotation covers every width
  let off ← loadPack (dir / "words.ixe") (dir / "words.equations.json")
  note "loaded, words off"
  let on ← loadPack (dir / "words.ixe") (dir / "words.equations.json") { table := { words := true } }
  note "loaded, words on"
  -- until the lowering exists, erasure declines a word entry (and accepts the program without)
  expect a (match IxCC.Lam.erase on.program on.checked with
      | .error e => e.code == "erase-word"
      | .ok _ => false) "erasure declines a word entry"
  expect a (IxCC.Lam.erase off.program off.checked).toOption.isSome
    "erasure accepts the program without word entries"
  proposals a off.program off.hints.proposals
  note "the sidecar's word proposals"
  tampered a
  note "tampered word theorems"
  for (root, w) in roots do
    let rootOff ← rootNamed off root
    let rootOn ← rootNamed on root
    -- the harness, on the program without word entries
    expect a ((List.range off.program.size).all fun c =>
        !(off.program.table.resolveOf c matches some (.word ..)))
      s!"{root}: words off, no word entry"
    let (n, bad) := harness off.program w 100000
    expect a bad.isEmpty s!"{root}: F6w against the reference bodies: {bad}"
    note s!"{root}: harness"
    total := total + n
    -- an out-of-range tower: F6w stuck, at every operation and argument position
    let (no, nd, badOut) := outOfRange off.program w 100000
    expect a badOut.isEmpty s!"{root}: F6w on out-of-range towers: {badOut}"
    note s!"{root}: out-of-range towers"
    totalOut := totalOut + no
    lines := lines ++ [s!"{root}: {no} out-of-range cases stuck ({nd} evaluated by the reference body)"]
    -- the table with words on: every primitive operation the root reaches
    let entries := (List.range on.program.size).filterMap fun c =>
      match on.program.table.resolveOf c with
      | some (.word w' op _) => some (w', op)
      | _ => none
    for op in WordOp.primitives w do
      expect a (entries.contains (w, op)) s!"{root}: {op.leanName w} is a word entry"
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
  expectEq a totalOut 1216 "the out-of-range case count"
  return lines

end IxCCTests.Src.WordRules
