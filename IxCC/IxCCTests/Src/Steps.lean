import IxCCTests.Src.Support
import IxCC.Recheck.Produce

/-! # SrcEval step counts

A test-only counting form of SrcEval (`IxCC.Src.Semantics`): it mirrors the
evaluator rule for rule and counts what each rule does, without changing what
it computes. The unit it measures is defined in `docs/source-steps.md`:

* a **charged step** is an event that spends one unit of `Src.run`'s clock:
  δ through an `eqn` or `csimp` entry, a safe definition's body or an
  allowlisted opaque (E8); β (A1); a recursor firing (F2, F3, F4); a `case`
  firing (F5); forcing a by-name slot (E1); `Quot.lift` (F8);
* the uncharged rule applications are counted beside them: constructors (F1),
  primitives (F6, and F6w, the fixed-width word operations), `Quot.mk` (F7), projections (E6) and partial applications
  accumulated (A2); irrelevant positions are never evaluated and cost
  nothing; a by-name slot costs one charged step and its term's steps each
  time it is forced (SrcEval does not memoise).

`Src.run`'s clock is a depth bound, not a step budget: a charged step runs
the rest of its computation at `k - 1`, and sequenced computations each run
at `k`. The counting form also records the smallest clock left at any charged
step of the run, from which the least clock at which `Src.run` reaches the
same outcome follows (`Measured.leastClock`).

**Agreement with SrcEval is checked, not proved.** The functions are `partial`
(measurement only, off every checked path, like `IxCCTests.Src.StuckEval`).
`measure` runs `Src.run` itself at the same clock and requires the same outcome,
then requires `Src.run` to reach it at the least clock and to time out one
below; a transcription error therefore fails the run instead of reporting a
count. -/

namespace IxCCTests.Src.Steps

open IxCC IxCC.Src
open IxCC.Sem (Result)

/-- Rule applications of one run, and the smallest clock left at a charge. -/
structure Tally where
  /-- E8: δ through `eqn`, `csimp`, a definition's body or an allowlisted opaque. -/
  delta : Nat := 0
  /-- A1: β. -/
  beta : Nat := 0
  /-- F2, F3, F4: recursor firings. -/
  iota : Nat := 0
  /-- F5: `case` firings. -/
  cases : Nat := 0
  /-- E1: by-name slots forced. -/
  force : Nat := 0
  /-- F8: `Quot.lift` firings. -/
  quotLift : Nat := 0
  /-- F1: constructors built (`Nat.zero` and `Nat.succ` give literals). -/
  ctor : Nat := 0
  /-- F7: `Quot.mk`. -/
  quotMk : Nat := 0
  /-- F6 and F6w: primitive applications. -/
  prim : Nat := 0
  /-- E6: projections. -/
  proj : Nat := 0
  /-- A2: arguments accumulated into partial applications. -/
  pap : Nat := 0
  /-- Calls of `eval` (term nodes visited). -/
  nodes : Nat := 0
  /-- The smallest clock left at a charged step (before its decrement). -/
  minClock : Option Nat := none
  deriving Repr, Inhabited

namespace Tally

/-- The charged steps: the events that spend `Src.run`'s clock. -/
def charged (t : Tally) : Nat := t.delta + t.beta + t.iota + t.cases + t.force + t.quotLift

end Tally

abbrev M := StateM Tally

instance [Inhabited α] : Inhabited (M α) := ⟨pure default⟩

/-- Record a charge at clock `k` (its value before the decrement). -/
def charge (k : Nat) (f : Tally → Tally) : M Unit :=
  modify fun t => { f t with minClock := some (match t.minClock with | some m => min m k | none => k) }

/-- A non-`ok` outcome at another type. -/
def bail : Result α → Result β
  | .ok _ => .stuck
  | .timeout => .timeout
  | .resource r => .resource r
  | .trap => .trap
  | .stuck => .stuck

mutual

partial def eval (p : Program) (k : Nat) (ls : Levels) (ρ : Env) (t : Term) : M (Result Value) := do
  modify fun c => { c with nodes := c.nodes + 1 }
  match t with
  | .var i =>
    match ρ[i]? with
    | some s => force p k s
    | none => return .stuck
  | .sort _ | .pi .. => return .ok (.irr (some t) ρ ls)
  | .natLit n => return .ok (.lit n)
  | .strLit s => return .ok (.str s)
  | .lam b d body => return .ok (.clo b d body ρ ls)
  | .letE _ r _ v body =>
    if r.irrAt ls then eval p k ls (.val (.irr (some v) ρ ls) :: ρ) body
    else
      match ← eval p k ls ρ v with
      | .ok x => eval p k ls (.val x :: ρ) body
      | o => return bail o
  | .proj s i e =>
    match ← eval p k ls ρ e with
    | .ok v =>
      modify fun c => { c with proj := c.proj + 1 }
      return p.projectField s i v
    | o => return bail o
  | .app f a m r =>
    match ← eval p k ls ρ f with
    | .ok fv =>
      if r.irrAt ls then apply p k fv (.val (.irr (some a) ρ ls))
      else
        match m with
        | .strict =>
          match ← eval p k ls ρ a with
          | .ok x => apply p k fv (.val x)
          | o => return bail o
        | .byName => apply p k fv (.name a ρ ls)
    | o => return bail o
  | .const c us => evalConst p k (us.map (evalUniv ls)) c

/-- E8's charged δ to `t` at the empty environment. -/
partial def delta (p : Program) (k : Nat) (ls : Levels) (t : Term) : M (Result Value) := do
  match k with
  | 0 => return .timeout
  | k + 1 =>
    charge (k + 1) fun c => { c with delta := c.delta + 1 }
    eval p k ls [] t

partial def evalConst (p : Program) (k : Nat) (ls : Levels) (c : CId) : M (Result Value) := do
  match p.table.resolveOf c with
  | some (.prim op) => headValue p k ls (.prim op)
  | some (.word w op _) => headValue p k ls (.word w op)
  | some (.csimp g vs _) => delta p k ls (.const g vs)
  | some (.eqn _ body) => delta p k ls body
  | some (.case _) => headValue p k ls (.cases c)
  | none =>
    match p.decl? c with
    | some (.ctor ..) => headValue p k ls (.ctor c)
    | some (.recr ..) => headValue p k ls (.recr c)
    | some (.quot .ctor ..) => headValue p k ls (.quotMk c)
    | some (.quot .lift ..) => headValue p k ls (.quotLift c)
    | some (.defn .defn .safe _ _ v) => delta p k ls v
    | some (.defn .opaq .safe _ _ v) =>
      if p.table.isOpaqueByValue c then delta p k ls v else return .stuck
    | _ => return .stuck

partial def headValue (p : Program) (k : Nat) (ls : Levels) (h : Head) : M (Result Value) :=
  if p.headArity h == 0 then fire p k h ls [] else return .ok (.pap h ls [])

partial def apply (p : Program) (k : Nat) (f : Value) (s : Slot) : M (Result Value) := do
  match f with
  | .clo b _ body ρ ls =>
    if b.propWhen.allowsBeta ls then
      match k with
      | 0 => return .timeout
      | k + 1 =>
        charge (k + 1) fun c => { c with beta := c.beta + 1 }
        eval p k ls (s :: ρ) body
    else return .stuck
  | .pap h ls args =>
    let args := args ++ [s]
    let arity := p.headArity h
    if args.length == arity then fire p k h ls args
    else if args.length < arity then
      modify fun c => { c with pap := c.pap + 1 }
      return .ok (.pap h ls args)
    else return .stuck
  | _ => return .stuck

partial def applyAll (p : Program) (k : Nat) (f : Value) (ss : List Slot) : M (Result Value) := do
  match ss with
  | [] => return .ok f
  | s :: rest =>
    match ← apply p k f s with
    | .ok v => applyAll p k v rest
    | o => return bail o

/-- The rule and field slots F2 and F5 choose: from the forced major for an
ordinary recursor, from index slots for a subsingleton one. -/
partial def choose (p : Program) (k : Nat) (kind : RecKind) (ind np : CId) (major : Slot)
    (fields : List FieldSrc → List Slot) : M (Result (Nat × List Slot)) := do
  match kind with
  | .empty => return .trap
  | .ordinary =>
    match ← force p k major with
    | .ok v => return Result.ofOption (p.selectRule ind np v)
    | o => return bail o
  | .subsingleton _ srcs => return .ok (0, fields srcs)

partial def fire (p : Program) (k : Nat) (h : Head) (ls : Levels) (args : List Slot) : M (Result Value) := do
  match h with
  | .ctor c =>
    match p.decl? c with
    | some (.ctor _ _ _ _ np _ _) =>
      match ← forceAll p k (args.drop np) with
      | .ok fields =>
        modify fun t => { t with ctor := t.ctor + 1 }
        if some c == p.known.natZero then return .ok (.lit 0)
        else if some c == p.known.natSucc then
          match fields with
          | [.lit n] => return .ok (.lit (n + 1))
          | _ => return .stuck
        else return .ok (.con c ls (args.take np) fields)
      | o => return bail o
    | _ => return .stuck
  | .quotMk c =>
    match args with
    | [α, r, a] =>
      match ← force p k a with
      | .ok v =>
        modify fun t => { t with quotMk := t.quotMk + 1 }
        return .ok (.con c ls [α, r] [v])
      | o => return bail o
    | _ => return .stuck
  | .quotLift _ =>
    match k with
    | 0 => return .timeout
    | k + 1 =>
      charge (k + 1) fun t => { t with quotLift := t.quotLift + 1 }
      match args with
      | [_, _, _, f, _, q] =>
        match ← force p k q with
        | .ok (.con c' _ _ [a]) =>
          if p.isQuotCtor c' then
            match ← force p k f with
            | .ok fv => apply p k fv (.val a)
            | o => return bail o
          else return .stuck
        | .ok _ => return .stuck
        | o => return bail o
      | _ => return .stuck
  | .recr r =>
    match k with
    | 0 => return .timeout
    | k + 1 =>
      charge (k + 1) fun t => { t with iota := t.iota + 1 }
      match p.decl? r, (p.table.recKindOf r).map (·.atLevels ls) with
      | some (.recr _ _ _ np nmot nmin ni ind rules _), some kind =>
        let pre := args.take (np + nmot + nmin)
        let indices := (args.drop (np + nmot + nmin)).take ni
        let chosen ← choose p k kind ind np (args.getD (np + nmot + nmin + ni) default)
          fun srcs => srcs.map fun
            | .index i => indices.getD i (Slot.irrNone ls)
            | .proof => Slot.irrNone ls
        match chosen with
        | .ok (j, fields) =>
          match rules[j]? with
          | some rule =>
            let slots := pre ++ fields
            match peelLams slots.length rule.rhs with
            | some body => eval p k ls slots.reverse body
            | none => return .stuck
          | none => return .stuck
        | o => return bail o
      | _, _ => return .stuck
  | .cases c =>
    match k with
    | 0 => return .timeout
    | k + 1 =>
      charge (k + 1) fun t => { t with cases := t.cases + 1 }
      match p.table.resolveOf c with
      | some (.case r) =>
        match p.decl? r, (p.table.recKindOf r).map (·.atLevels ls) with
        | some (.recr _ _ _ np _ _ ni ind _ _), some kind =>
          let chosen ← choose p k kind ind np (args.getD (np + 1 + ni) default)
            fun srcs => srcs.map fun
              | .index i => args.getD (np + 1 + i) (Slot.irrNone ls)
              | .proof => Slot.irrNone ls
          match chosen with
          | .ok (j, fields) =>
            match ← force p k (args.getD (np + 1 + ni + 1 + j) default) with
            | .ok minor => applyAll p k minor fields
            | o => return bail o
          | o => return bail o
        | _, _ => return .stuck
      | _ => return .stuck
  | .prim op =>
    match ← forceAll p k args with
    | .ok vs =>
      modify fun t => { t with prim := t.prim + 1 }
      match litArgs vs with
      | some ns =>
        match op.evalLits ns with
        | some (.nat n) => return .ok (.lit n)
        | some (.bool b) => return p.boolValue b
        | none => return .stuck
      | none => return .stuck
    | o => return bail o
  | .word w op =>
    match ← forceAll p k args with
    | .ok vs =>
      modify fun t => { t with prim := t.prim + 1 }
      return p.wordValue w op vs
    | o => return bail o

partial def force (p : Program) (k : Nat) (s : Slot) : M (Result Value) := do
  match s with
  | .val v => return .ok v
  | .name t ρ ls =>
    match k with
    | 0 => return .timeout
    | k + 1 =>
      charge (k + 1) fun c => { c with force := c.force + 1 }
      eval p k ls ρ t

partial def forceAll (p : Program) (k : Nat) (ss : List Slot) : M (Result (List Value)) := do
  match ss with
  | [] => return .ok []
  | s :: rest =>
    match ← force p k s with
    | .ok v =>
      match ← forceAll p k rest with
      | .ok vs => return .ok (v :: vs)
      | o => return bail o
    | o => return bail o

end

/-- `Src.run` with its rule applications counted. -/
def run (p : Program) (k : Nat) (root : CId) (xs : List Value) : Result Value × Tally :=
  let go : M (Result Value) := do
    match ← evalConst p k [] root with
    | .ok f => applyAll p k f (xs.map .val)
    | o => return o
  go.run {}

/-- A measured run: SrcEval's outcome at `clock`, the counts, and the least
clock at which `Src.run` reaches that outcome (none when it timed out). -/
structure Measured where
  clock : Nat
  result : Result Value
  tally : Tally
  leastClock : Option Nat

/-- Run root `root` on `Nat` arguments at `clock` with counts, and check the
counting form against `Src.run`: the same outcome at `clock`, the same outcome
at the least clock the counts give, and a timeout one below it. -/
def measure (p : Program) (root : CId) (args : List Nat) (clock : Nat) : Except String Measured := do
  let xs := args.map Value.lit
  let (counted, tally) := run p clock root xs
  let reference := IxCC.Src.run p clock root xs
  unless sameOutcome p counted reference do
    throw s!"the counting form disagrees with Src.run at clock {clock}: {outcome counted} against {outcome reference}"
  match reference with
  | .timeout => return { clock, result := reference, tally, leastClock := none }
  | _ =>
    -- With `m` the smallest clock left at a charge, every charge still has a
    -- unit to spend at `clock - m + 1` and the first to reach `m` has none at
    -- `clock - m`.
    let least := match tally.minClock with
      | some m => clock - m + 1
      | none => 0
    unless sameOutcome p (IxCC.Src.run p least root xs) reference do
      throw s!"Src.run does not reach its outcome at the counted least clock {least}"
    if least > 0 then
      unless IxCC.Src.run p (least - 1) root xs matches .timeout do
        throw s!"Src.run does not time out below the counted least clock {least}"
    return { clock, result := reference, tally, leastClock := some least }

/-! ## The front end, as `ixcc` runs it -/

/-- `ixcc`'s front end up to the source SrcEval runs: ingress (with the kernel's
acceptance), then the producer's front half
(`Recheck.produceSource`). A decline is the front end's own error. -/
def front (bytes : ByteArray) (equations : Lean.Json) (roots : List String) :
    Except Recheck.Err (Recheck.Input × Recheck.ProducedSource) := do
  let inp ← Recheck.ingress bytes equations roots
  return (inp, ← Recheck.produceSource (Recheck.Config.forInput {} inp) inp)

/-- The source constant of the root named `name` (the sidecar's name). -/
def rootOf (inp : Recheck.Input) (src : Program) (name : String) : Except String CId := do
  match (inp.names.zip src.roots).find? (·.1 == name) with
  | some (_, (_, c)) => return c
  | none => throw s!"no root named {name} (the selected roots are {inp.names})"

/-! ## JSON -/

open Lean (Json)

def obsJson : Sem.Obs → Json
  | .nat n => Json.mkObj [("nat", (n : Json))]
  | .word w => Json.mkObj [("word", (w.toNat : Json))]
  | .ctor tag fs => Json.mkObj [("ctor", (tag : Json)), ("fields", Json.arr (fs.map obsJson).toArray)]
  | .bytes bs => Json.mkObj [("bytes", Json.arr (bs.map fun (b : UInt8) => (b.toNat : Json)).toArray)]

/-- An outcome: `{"outcome": "ok", "value": …}` with the value read back as
`Src.readback` reads it (a constructor by its index), or the failure. -/
def resultJson (p : Program) (checked : Relevance.Checked) : Result Value → Json
  | .ok v => Json.mkObj [("outcome", "ok"), ("value", match readback p checked.keeps v with
    | some o => obsJson o
    | none => Json.mkObj [("shape", (v.shape : Json))])]
  | .timeout => Json.mkObj [("outcome", "timeout")]
  | .resource r => Json.mkObj [("outcome", "resource"), ("failure", (reprStr r : Json))]
  | .trap => Json.mkObj [("outcome", "trap")]
  | .stuck => Json.mkObj [("outcome", "stuck")]

def tallyJson (t : Tally) : Json :=
  Json.mkObj [("charged", (t.charged : Json)), ("delta", (t.delta : Json)), ("beta", (t.beta : Json)),
    ("iota", (t.iota : Json)), ("case", (t.cases : Json)), ("force", (t.force : Json)),
    ("quotLift", (t.quotLift : Json)), ("ctor", (t.ctor : Json)), ("quotMk", (t.quotMk : Json)),
    ("prim", (t.prim : Json)), ("proj", (t.proj : Json)), ("pap", (t.pap : Json)),
    ("nodes", (t.nodes : Json))]

/-- The format of every line the tool prints. -/
def format : String := "ixcc/src-steps/1"

def runJson (closure root : String) (args : List Nat) (p : Program) (checked : Relevance.Checked)
    (m : Measured) : Json :=
  Json.mkObj [("format", (format : Json)), ("closure", (closure : Json)), ("root", (root : Json)),
    ("args", Json.arr (args.map fun (n : Nat) => (n : Json)).toArray), ("clock", (m.clock : Json)),
    ("result", resultJson p checked m.result), ("steps", tallyJson m.tally),
    ("leastClock", match m.leastClock with | some c => (c : Json) | none => Json.null)]

def declinedJson (closure root : String) (e : Recheck.Err) : Json :=
  Json.mkObj [("format", (format : Json)), ("closure", (closure : Json)), ("root", (root : Json)),
    ("declined", Json.mkObj [("stage", (e.stage.name : Json)), ("code", (e.code : Json)),
      ("message", (e.message : Json))])]

end IxCCTests.Src.Steps
