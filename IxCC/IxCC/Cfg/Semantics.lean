import IxCC.Cfg.Syntax
import IxCC.Own.Semantics
import IxCC.Sem.Clock

/-! # Cfg semantics

A clocked **small-step** semantics (design note 03 §7) over Own's heap and
values, run by the shared runner `Sem.runClocked` with a **total** clock:
every charge spends one unit, whatever the nesting (Src through Own count
depth). It is the big-step → small-step bridge's target (`Sim.ofStar`,
m2-1 status): a depth-`k` Own timeout gives more than `k` Cfg charges, so
the timeout clause keeps the identity clock map, while a successful Own run
at depth `k` needs some larger Cfg clock `k'`.

States: about to enter a function (`call`), running a frame (`run`), or
returning a value to the stack (`ret`). A frame holds its function, block,
the rest of the block's body (the program counter) and one environment per
activation (variables are unique per function, so block parameters and
instruction results never clash; a back edge rebinds a block's parameters).

**Charges** (03 C6): entering a function (every `call` state: the entry of
a run, a non-tail call, a tail call) and taking a back edge. Everything else
is free: instructions, forward edges, `switch`, returns. Instructions run as
in Own (`Own.evalRhs`), so allocation follows the policy; `case` selection,
□ and dead cells are stuck exactly as in Own (03 C5). Cfg never produces
`resource`.

The step bound (`fuelFor`) is structural: between two charges a frame runs
at most one forward path of its function, and returns are bounded by calls,
so `(2k + 6)·(size + 1)` steps always outlast clock `k` (tested; the proof is
M2.4's `Potential`). Never evaluated on the recheck path (D17). -/

namespace IxCC.Cfg

open IxCC.Sem (Result)
open IxCC.Own (RVal Heap AllocPol Env Tables)
open IxCC.Fir (Var FunId)

structure Frame where
  fn : FunId
  blk : BlockId
  /-- The rest of the block's body. -/
  rest : List Instr
  env : Env

inductive State where
  /-- Enter `f` with `args` (charged); `stk` holds the suspended callers and
  the variable each result goes to. -/
  | call (f : FunId) (args : List RVal) (stk : List (Frame × Var)) (H : Heap)
  | run (fr : Frame) (stk : List (Frame × Var)) (H : Heap)
  | ret (v : RVal) (stk : List (Frame × Var)) (H : Heap)

def Program.tables (P : Program) : Tables := { ctors := P.ctors, known := P.known }

/-- Take an edge from a frame: bind the target's parameters (arguments
evaluated in the source frame). -/
def takeEdge (fd : Fun) (fr : Frame) (stk : List (Frame × Var)) (H : Heap) (e : Edge) :
    Sem.Step State (RVal × Heap) :=
  match fd.block? e.target, Own.evalArgs fr.env e.args with
  | some b, some vs =>
    if vs.length = b.params.length then
      .next (.run { fr with blk := e.target, rest := b.body
                            env := Own.bindAll fr.env (b.params.map (·.1)) vs } stk H) e.back
    else .stuck
  | _, _ => .stuck

/-- The first edge of `alts` with `key`, else the default. -/
def selectEdge (key : Key.CtorKey) : List (Key.CtorKey × Edge) → Option Edge → Option Edge
  | [], d => d
  | (k, e) :: rest, d => if k = key then some e else selectEdge key rest d

def step (pol : AllocPol) (P : Program) : State → Sem.Step State (RVal × Heap)
  | .call f args stk H =>
    match P.fun? f with
    | some fd =>
      match fd.block? 0 with
      | some b =>
        if args.length = b.params.length then
          .next (.run { fn := f, blk := 0, rest := b.body
                        env := Own.bindAll .leaf (b.params.map (·.1)) args } stk H) true
        else .stuck
      | none => .stuck
    | none => .stuck
  | .ret v [] H => .done (v, H)
  | .ret v ((fr, x) :: stk) H => .next (.run { fr with env := fr.env.insert x v } stk H) false
  | .run fr stk H =>
    match fr.rest with
    | .bind x (.fir (.call f as)) :: is =>
      match Own.evalArgs fr.env as with
      | some vs => .next (.call f vs (({ fr with rest := is }, x) :: stk) H) false
      | none => .stuck
    | .bind x r :: is =>
      match Own.evalRhs pol P.tables fr.env H r with
      | .ok (v, H') => .next (.run { fr with rest := is, env := fr.env.insert x v } stk H') false
      | .resource r => .fail r
      | .trap => .trap
      | .timeout | .stuck => .stuck
    | [] =>
      match P.fun? fr.fn with
      | some fd =>
        match fd.block? fr.blk with
        | some b =>
          match b.term with
          | .jump e => takeEdge fd fr stk H e
          | .switch x alts d =>
            match fr.env.get? x with
            | some v =>
              match v.asCtor P.known H with
              | some (key, _) =>
                match selectEdge key alts d with
                | some e => takeEdge fd fr stk H e
                | none => .stuck
              | none => .stuck
            | none => .stuck
          | .ret a =>
            match Own.evalArg fr.env a with
            | some v => .next (.ret v stk H) false
            | none => .stuck
          | .tcall f as =>
            match Own.evalArgs fr.env as with
            | some vs => .next (.call f vs stk H) false
            | none => .stuck
          | .trap => .trap
        | none => .stuck
      | none => .stuck

/-- A step bound that outlasts clock `k`. -/
def fuelFor (P : Program) (k : Nat) : Nat := (2 * k + 6) * (P.instrs + 1)

/-- Run function `f` on argument values over heap `H` with total clock
`k`. -/
def run (pol : AllocPol) (P : Program) (k : Nat) (f : FunId) (args : List RVal)
    (H : Heap := {}) : Result (RVal × Heap) :=
  Sem.runClocked (step pol P) (fuelFor P k) k (.call f args [] H)

/-- `run` with an explicit step bound (tests check the bound is never the
reason a run stops). -/
def runFuel (pol : AllocPol) (P : Program) (fuel k : Nat) (f : FunId) (args : List RVal)
    (H : Heap := {}) : Result (RVal × Heap) :=
  Sem.runClocked (step pol P) fuel k (.call f args [] H)

end IxCC.Cfg
