import Ix.Compiler.IxIR1.Eval

/-!
# Hand-written IxIR₁ programs

The lowering targets, written by hand ahead of the lowering — exactly
the discipline that worked for IxIR₀. Everything is pure, so the
suite runs as elaboration-time `#guard`s, and the store counters turn
the memory claims into checked facts:

- **FBIP reversal**: reversing a unique 3-list performs 3 in-place
  reuses, 1 free (the input's nil), and **zero allocations** beyond
  building the inputs.
- **Unique addition**: unary `add` consumes its recursion argument by
  reuse — again no allocation beyond the inputs.
- **Shared world**: Perceus-style deep drop reclaims a shared list to
  `live = 0` (leak-freedom as a `#guard`); `dup` defers reclamation
  exactly one drop.
- **eval/apply**: pap under-fill, saturation, and over-fill chains.
- **The dynamic discipline**: `dup`/`drop` on unique, `free` on
  shared, and use-after-free all fault as `Err.mem`.
-/

namespace Ix.Compiler.IxIR1.Examples

open Ix.Compiler.Ixon (Address Owned)
open Ix.Compiler.IxIR0 (Literal)

private def addrOf (n : UInt8) : Address :=
  Address.replicate n

private def aListBlock := addrOf 0x60
private def aNatBlock := addrOf 0x61
private def aRev := addrOf 0x62
private def aAdd := addrOf 0x63
private def aAddLit := addrOf 0x64
private def aIsZero := addrOf 0x65
private def aKonstAdd := addrOf 0x66
private def aNatAdd := addrOf 0x67
private def aDirectOnly := addrOf 0x69

private def nilId : CtorId := ⟨aListBlock, 0, 0⟩
private def consId : CtorId := ⟨aListBlock, 0, 1⟩
private def zeroId : CtorId := ⟨aNatBlock, 0, 0⟩
private def succId : CtorId := ⟨aNatBlock, 0, 1⟩

private def lets : List Op → Code → Code
  | [], c => c
  | op :: rest, c => .letOp op (lets rest c)

/-- `rev (acc, xs)`: in-place list reversal. Entry env `[xs, acc]`. -/
private def revBody : Code :=
  .case (.var 0) false #[
    -- nil: free the terminator, return acc
    .mk 0 0 (lets [.free (.var 0)] (.ret (.var 2))),
    -- cons(h, t): env [t, h, xs, acc]; reuse xs as cons(h, acc)
    .mk 1 2 (lets
      [ .reuse (.var 2) consId #[.var 1, .var 3],
        .callSelf #[.var 0, .var 1] ]
      (.ret (.var 0)))]

/-- `add (m, n)`: unary addition, recursing and reusing on `n`.
Entry env `[n, m]`. -/
private def addBody : Code :=
  .case (.var 0) false #[
    -- zero: free it, return m
    .mk 0 0 (lets [.free (.var 0)] (.ret (.var 2))),
    -- succ(p): env [p, n, m]; r := add(m, p); reuse n as succ(r)
    .mk 1 1 (lets
      [ .callSelf #[.var 2, .var 0],
        .reuse (.var 2) succId #[.var 0] ]
      (.ret (.var 0)))]

/-- `addLit (a, b)`: scalar addition through the extern oracle.
Entry env `[b, a]`. -/
private def addLitBody : Code :=
  lets [.extern aNatAdd #[.var 1, .var 0]] (.ret (.var 0))

/-- `isZero (x)`: nat-literal peeling. Entry env `[x]`. -/
private def isZeroBody : Code :=
  .case (.var 0) true #[
    .mk 0 0 (.ret (.lit (.nat 1))),
    .mk 1 1 (.ret (.lit (.nat 0)))]

/-- `konstAdd (a)`: returns a pap — over-fill test material. -/
private def konstAddBody : Code :=
  lets [.papp aAddLit #[.var 0]] (.ret (.var 0))

private def decls : List (Address × Decl) :=
  [(aRev, .fn ⟨2, .unique, false, revBody⟩),
   (aAdd, .fn ⟨2, .unique, false, addBody⟩),
   (aAddLit, .fn ⟨2, .shared, true, addLitBody⟩),
   (aIsZero, .fn ⟨1, .shared, true, isZeroBody⟩),
   (aKonstAdd, .fn ⟨1, .shared, true, konstAddBody⟩),
   (aDirectOnly, .fn ⟨1, .shared, false, .ret (.var 0)⟩),
   (aNatAdd, .extern 2)]

private def oracle : Address → List RVal → Option RVal := fun a args =>
  if a == aNatAdd then
    match args with
    | [.lit (.nat m), .lit (.nat n)] => some (.lit (.nat (m + n)))
    | _ => none
  else none

private def ctx : Ctx := { decls := Env.ofList decls, oracle }

private def heapResultCtx : Ctx :=
  { decls := Env.ofList decls, oracle := fun _ _ => some (.loc 0) }

private def run (c : Code) : Except Err (Store × RVal) := runMain ctx c

/-! ## Decoders and guard helpers -/

private def natOf? (s : Store) : Nat → RVal → Option Nat
  | 0, _ => none
  | _, .lit (.nat n) => some n
  | f + 1, .loc l =>
    match s.get? l with
    | some box =>
      match box.node with
      | .ctorN cid fields =>
        match cid.cidx, fields.toList with
        | 0, [] => some 0
        | 1, [v] => (natOf? s f v).map (· + 1)
        | _, _ => none
      | _ => none
    | none => none
  | _, _ => none

private def natsOf? (s : Store) : Nat → RVal → Option (List Nat)
  | 0, _ => none
  | f + 1, .loc l =>
    match s.get? l with
    | some box =>
      match box.node with
      | .ctorN cid fields =>
        match cid.cidx, fields.toList with
        | 0, [] => some []
        | 1, [h, t] => do
          let n ← natOf? s f h
          let rest ← natsOf? s f t
          pure (n :: rest)
        | _, _ => none
      | _ => none
    | none => none
  | _, _ => none

private def checkRun (r : Except Err (Store × RVal))
    (p : Store → RVal → Bool) : Bool :=
  match r with
  | .ok (s, v) => p s v
  | .error _ => false

private def errMem : Except Err (Store × RVal) → Bool
  | .error (.mem _) => true
  | _ => false

private def errStuck : Except Err (Store × RVal) → Bool
  | .error (.stuck _) => true
  | _ => false

/-! ## FBIP: reversal of a unique list allocates nothing -/

private def revDemo : Code := lets
  [ .alloc .unique nilId #[],
    .alloc .unique consId #[.lit (.nat 3), .var 0],
    .alloc .unique consId #[.lit (.nat 2), .var 0],
    .alloc .unique consId #[.lit (.nat 1), .var 0],
    .alloc .unique nilId #[],
    .call aRev #[.var 0, .var 1] ]
  (.ret (.var 0))

#guard checkRun (run revDemo) fun s v =>
  natsOf? s 1000 v == some [3, 2, 1]
  && s.allocs == 5    -- 4 building the input + 1 accumulator nil
  && s.reuses == 3    -- every cons flipped in place
  && s.frees == 1     -- the input's nil terminator
  && s.live == 4      -- exactly the result list

/-! ## Unique unary addition: reuse along the recursion spine -/

private def addDemo : Code := lets
  [ .alloc .unique zeroId #[],
    .alloc .unique succId #[.var 0],
    .alloc .unique succId #[.var 0],          -- m = 2̂
    .alloc .unique zeroId #[],
    .alloc .unique succId #[.var 0],
    .alloc .unique succId #[.var 0],
    .alloc .unique succId #[.var 0],          -- n = 3̂
    .call aAdd #[.var 4, .var 0] ]
  (.ret (.var 0))

#guard checkRun (run addDemo) fun s v =>
  natOf? s 1000 v == some 5
  && s.allocs == 7 && s.reuses == 3 && s.frees == 1 && s.live == 6

/-! ## Shared world: deep drop is leak-free; dup defers it -/

private def sharedDrop : Code := lets
  [ .alloc .shared nilId #[],
    .alloc .shared consId #[.lit (.nat 2), .var 0],
    .alloc .shared consId #[.lit (.nat 1), .var 0],
    .drop (.var 0) ]
  (.ret .erased)

#guard checkRun (run sharedDrop) fun s _ =>
  s.live == 0 && s.frees == 3 && s.rcops == 3

private def sharedDupDrop : Code := lets
  [ .alloc .shared nilId #[],
    .alloc .shared consId #[.lit (.nat 2), .var 0],
    .alloc .shared consId #[.lit (.nat 1), .var 0],
    .dup (.var 0),
    .drop (.var 0),                            -- rc 2 → 1: still live
    .drop (.var 1) ]                           -- rc 1 → 0: deep free
  (.ret .erased)

#guard checkRun (run sharedDupDrop) fun s _ =>
  s.live == 0 && s.frees == 3 && s.rcops == 5

-- After only the first drop, everything must still be live.
private def sharedDupHold : Code := lets
  [ .alloc .shared nilId #[],
    .alloc .shared consId #[.lit (.nat 2), .var 0],
    .alloc .shared consId #[.lit (.nat 1), .var 0],
    .dup (.var 0),
    .drop (.var 0) ]
  (.ret (.var 1))

#guard checkRun (run sharedDupHold) fun s v =>
  s.live == 3 && natsOf? s 1000 v == some [1, 2]

/-! ## eval/apply: under-fill, saturation, over-fill -/

private def papDemo : Code := lets
  [ .papp aAddLit #[.lit (.nat 20)],
    .apply (.var 0) #[.lit (.nat 22)] ]
  (.ret (.var 0))

#guard checkRun (run papDemo) fun _ v => v == .lit (.nat 42)

private def papChain : Code := lets
  [ .papp aAddLit #[],
    .apply (.var 0) #[.lit (.nat 20)],         -- under-fill: new pap
    .apply (.var 0) #[.lit (.nat 22)] ]        -- saturates
  (.ret (.var 0))

#guard checkRun (run papChain) fun s v =>
  v == .lit (.nat 42) && s.allocs == 2

private def papOverfill : Code := lets
  [ .papp aKonstAdd #[],
    .apply (.var 0) #[.lit (.nat 20), .lit (.nat 22)] ]
  (.ret (.var 0))

#guard checkRun (run papOverfill) fun _ v => v == .lit (.nat 42)

-- Direct entry remains available for declarations that do not opt into the
-- shared PAP calling convention.
#guard checkRun (run (lets
  [.call aDirectOnly #[.lit (.nat 42)]] (.ret (.var 0)))) fun _ v =>
    v == .lit (.nat 42)

-- The same declaration cannot be entered through a saturated PAP.
#guard
  match run (lets
      [.papp aDirectOnly #[], .apply (.var 0) #[.lit (.nat 42)]]
      (.ret (.var 0))) with
  | .error (.stuck "shared pap targets a non-pap-safe declaration") => true
  | _ => false

-- `apply` consumes its pap: the chain's intermediates are reclaimed
-- without caller-side drops…
#guard checkRun (run papChain) fun s _ => s.frees == 2 && s.live == 0

-- …so re-applying a consumed pap is a memory fault…
#guard errMem (run (lets
  [ .papp aAddLit #[.lit (.nat 1)],
    .apply (.var 0) #[.lit (.nat 2)],
    .apply (.var 1) #[.lit (.nat 3)] ]
  (.ret (.var 0))))

-- …and `dup` is how a pap survives one application: rc 2 → 1 at the
-- first apply, consumed for real at the second, leak-free overall.
#guard checkRun (run (lets
  [ .papp aAddLit #[.lit (.nat 1)],
    .dup (.var 0),
    .apply (.var 0) #[.lit (.nat 2)],
    .apply (.var 2) #[.lit (.nat 3)] ]
  (.ret (.var 0)))) fun s v => v == .lit (.nat 4) && s.live == 0

/-! ## Nat-literal peeling -/

#guard checkRun (run (lets [.call aIsZero #[.lit (.nat 0)]]
  (.ret (.var 0)))) fun _ v => v == .lit (.nat 1)
#guard checkRun (run (lets [.call aIsZero #[.lit (.nat 7)]]
  (.ret (.var 0)))) fun _ v => v == .lit (.nat 0)
#guard errStuck (run (.case (.lit (.nat 3)) false #[]))

/-! ## `dropU`: deep free of a unique tree -/

-- Three unique nodes reclaimed with zero refcount traffic.
#guard checkRun (run (lets
  [ .alloc .unique nilId #[],
    .alloc .unique consId #[.lit (.nat 2), .var 0],
    .alloc .unique consId #[.lit (.nat 1), .var 0],
    .dropU (.var 0) ]
  (.ret .erased))) fun s _ =>
  s.live == 0 && s.frees == 3 && s.rcops == 0

-- dropU demands the unique world…
#guard errMem (run (lets
  [.alloc .shared nilId #[], .dropU (.var 0)] (.ret .erased)))

-- …and whole-value modes: a shared child under a unique node faults
-- (symmetric to deep drop's unique-under-shared check).
#guard errMem (run (lets
  [ .alloc .shared nilId #[],
    .alloc .unique consId #[.lit (.nat 1), .var 0],
    .dropU (.var 0) ]
  (.ret .erased)))

/-! ## The dynamic memory discipline -/

#guard errMem (run (lets
  [.alloc .unique nilId #[], .dup (.var 0)] (.ret .erased)))
#guard errMem (run (lets
  [.alloc .unique nilId #[], .drop (.var 0)] (.ret .erased)))
#guard errMem (run (lets
  [.alloc .shared nilId #[], .free (.var 0)] (.ret .erased)))
#guard errMem (run (lets
  [.alloc .shared nilId #[], .reuse (.var 0) nilId #[]] (.ret .erased)))
#guard errMem (run (lets
  [.alloc .unique nilId #[], .free (.var 0), .fetch (.var 1) 0]
  (.ret .erased)))
#guard errMem (run (lets
  [.alloc .unique nilId #[], .free (.var 0), .free (.var 1)]
  (.ret .erased)))

-- Function result signatures are checked at the dynamic call boundary too:
-- malformed hand-written code cannot return a unique node as `.shared`.
private def aBadResult := addrOf 0x68
private def badResultCtx : Ctx :=
  { decls := Env.ofList [(aBadResult, .fn ⟨0, .shared, false,
      lets [.alloc .unique nilId #[]] (.ret (.var 0))⟩)] }

#guard
  match invoke badResultCtx 10 aBadResult [] {} with
  | .error (.mem "function result ownership mismatch") => true
  | _ => false

-- Structural stuckness stays distinct from memory faults.
#guard errStuck (run (.case .erased false #[]))
#guard errStuck (run (lets
  [.papp aAddLit #[.lit (.nat 1), .lit (.nat 2)]] (.ret .erased)))

/-! Externs are a scalar-only ownership boundary in v1. A location may
neither be passed to an oracle nor be manufactured by one. -/

#guard errMem (run (lets
  [ .alloc .shared nilId #[],
    .extern aNatAdd #[.var 0, .lit (.nat 1)] ]
  (.ret .erased)))

#guard errMem (runMain heapResultCtx (lets
  [ .alloc .shared nilId #[],
    .extern aNatAdd #[.lit (.nat 1), .lit (.nat 2)] ]
  (.ret .erased)))

-- Fuel: self-application-free divergence via callSelf at top level.
#guard (match runMain ctx (lets [.callSelf #[]] (.ret (.var 0))) 100 with
  | .error .fuel => true
  | _ => false)

end Ix.Compiler.IxIR1.Examples
