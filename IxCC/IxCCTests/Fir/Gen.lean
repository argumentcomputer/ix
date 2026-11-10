import IxCCTests.Fir.Support
import IxCCTests.Support.LamGen
import IxCC.Anf.Pipeline

/-! Generated programs through Fir, Own and Cfg:

* **First-order Anf**, generated directly (`FoGen`), because the K1 pipeline
  never produces join points or allocation: typed (`Nat`, `Bool`, pairs,
  options) and well scoped, with primitives, constructors (allocation),
  projections, `case` on every type (defaults included), known calls down the
  call graph and self calls on a decreasing argument, tail calls, CAFs,
  non-recursive join points jumped to from several tails, recursive join
  points (loops) with jumps from nested join points, `tick`, `trap`, and a
  few ill-typed operations (stuck runs). Each program is lowered to every
  level, checked well formed, and compared level by level on five inputs.
* **LamGen programs** (the Anf suite's generator, with closures) through the
  Phase 1 pipeline: every stage is either lowered (then compared, with Lam's
  readback) or declined with `fir.closures` naming exactly the residual. -/

namespace IxCCTests.Fir.Gen

open IxCC IxCCTests.Src IxCCTests.Lam IxCCTests.Anf
open IxCCTests.Support IxCCTests.Support.RngM
open IxCCTests.Support.LamGen (natZ natS bF bT pairK noneK someK)
open IxCC.Anf (Exp Bind Atom Alt GDef)

inductive Ty where
  | nat | bool | pair | opt
  deriving BEq, Inhabited

/-- The generator's scope, by level (index = depth − 1 − level). -/
structure Env where
  vars : Array Ty := #[]
  /-- Join points by level: their arity, or `none` where jumping would not
  terminate (a loop's exit arm). -/
  joins : Array (Option Nat) := #[]
  self : Nat
  /-- The level of a variable holding a decreased first argument: self calls
  may pass it. -/
  selfArg : Option Nat := none
  /-- Each global's arity and result type. -/
  sigs : Array (Nat × Ty)

def Env.push (E : Env) (τ : Ty) : Env := { E with vars := E.vars.push τ }
def Env.pushN (E : Env) (τs : List Ty) : Env := τs.foldl Env.push E
def Env.var (E : Env) (level : Nat) : Atom := .var (E.vars.size - 1 - level)
def Env.levels (E : Env) (τ : Ty) : Array Nat :=
  (Array.range E.vars.size).filter fun l => E.vars[l]! == τ

def b (bd : Bind) (e : Exp) : Exp := .bind Anf.freshLet bd e

def natAtom (E : Env) : RngM Atom := do
  let ls := E.levels .nat
  if ls.isEmpty || (← chance 25) then return .lit (.nat (← below 6))
  return E.var (← pick ls)

def natAtoms (E : Env) : Nat → RngM (List Atom)
  | 0 => pure []
  | n + 1 => do return (← natAtom E) :: (← natAtoms E n)

/-- A result of type `τ`. -/
def ret (E : Env) (τ : Ty) : RngM Exp := do
  let ls := E.levels τ
  if !ls.isEmpty && (← chance 60) then return .ret (E.var (← pick ls))
  match τ with
  | .nat => return .ret (← natAtom E)
  | .bool => return b (.con (if ← chance 50 then bT else bF) []) (.ret (.var 0))
  | .pair => return b (.con pairK [← natAtom E, ← natAtom E]) (.ret (.var 0))
  | .opt =>
    if ← chance 30 then return b (.con noneK []) (.ret (.var 0))
    return b (.con someK [← natAtom E]) (.ret (.var 0))

/-- A jump to a join point in scope, if any. -/
def jump? (E : Env) : RngM (Option Exp) := do
  let js := (Array.range E.joins.size).filterMap fun l => E.joins[l]!.map (l, ·)
  if js.isEmpty then return none
  let (l, n) ← pick js
  return some (.jump (E.joins.size - 1 - l) (← natAtoms E n))

/-- Globals `E` may call: later ones (the call graph is a DAG), with their
arity and result type. -/
def callees (E : Env) : Array (Nat × Nat × Ty) :=
  (Array.range E.sigs.size).filterMap fun g =>
    if g > E.self then some (g, E.sigs[g]!.1, E.sigs[g]!.2) else none

partial def exp (E : Env) (τ : Ty) (depth : Nat) : RngM Exp := do
  if depth == 0 then
    if let some j ← jump? E then if ← chance 40 then return j
    return ← ret E τ
  let sub := fun (E : Env) (τ : Ty) => exp E τ (depth - 1)
  match ← weighted [4, 2, 3, 2, 5, 3, 1, 2, 2, 1, 1, 3, 2] with
  | 0 => -- arithmetic
    let p ← pick #[Lam.Prim.natAdd, .natSub, .natMul, .natDiv, .natMod]
    return b (.prim p [← natAtom E, ← natAtom E]) (← sub (E.push .nat) τ)
  | 1 => -- comparison
    let p ← pick #[Lam.Prim.natBeq, .natBle, .natBlt]
    return b (.prim p [← natAtom E, ← natAtom E]) (← sub (E.push .bool) τ)
  | 2 => -- allocation
    if ← chance 60 then return b (.con pairK [← natAtom E, ← natAtom E]) (← sub (E.push .pair) τ)
    if ← chance 50 then return b (.con someK [← natAtom E]) (← sub (E.push .opt) τ)
    return b (.con noneK []) (← sub (E.push .opt) τ)
  | 3 => -- projection (rarely of a Nat: stuck)
    let ps := E.levels .pair
    if ps.isEmpty || (← chance 3) then
      return b (.proj pairK 0 (← natAtom E)) (← sub (E.push .nat) τ)
    return b (.proj pairK (← below 2) (E.var (← pick ps))) (← sub (E.push .nat) τ)
  | 4 => -- case
    match ← below 4 with
    | 0 =>
      let s ← natAtom E
      if ← chance 20 then
        return .case s [.mk natS 1 (← sub (E.push .nat) τ)] (some (← sub E τ))
      return .case s [.mk natZ 0 (← sub E τ), .mk natS 1 (← sub (E.push .nat) τ)] none
    | 1 =>
      let ls := E.levels .bool
      if ls.isEmpty then return ← sub E τ
      let s := E.var (← pick ls)
      if ← chance 25 then return .case s [.mk bT 0 (← sub E τ)] (some (← sub E τ))
      return .case s [.mk bF 0 (← sub E τ), .mk bT 0 (← sub E τ)] none
    | 2 =>
      let ls := E.levels .opt
      if ls.isEmpty then return ← sub E τ
      return .case (E.var (← pick ls))
        [.mk noneK 0 (← sub E τ), .mk someK 1 (← sub (E.push .nat) τ)] none
    | _ =>
      let ls := E.levels .pair
      if ls.isEmpty then return ← sub E τ
      return .case (E.var (← pick ls)) [.mk pairK 2 (← sub (E.pushN [.nat, .nat]) τ)] none
  | 5 => -- a known call or a CAF
    let cs := callees E
    if cs.isEmpty then return ← sub E τ
    let (g, n, σ) ← pick cs
    let as ← natAtoms E n
    let bd := if n == 0 then Bind.glob g else .call g as
    if σ == τ && (← chance 30) then return b bd (.ret (.var 0))   -- a tail call
    return b bd (← sub (E.push σ) τ)
  | 6 => -- a self call on the decreased argument
    match E.selfArg with
    | some l =>
      let (n, σ) := E.sigs[E.self]!
      let rest ← natAtoms E (n - 1)
      let bd := Bind.call E.self (E.var l :: rest)
      if σ == τ && (← chance 50) then return b bd (.ret (.var 0))
      return b bd (← sub (E.push σ) τ)
    | none => sub E τ
  | 7 => -- a non-recursive join point, jumped to from the tails of its scope
    let n ← range 1 2
    let body ← sub (E.pushN (List.replicate n .nat)) τ
    let E' := { E with joins := E.joins.push (some n) }
    return .join n false body (← sub E' τ)
  | 8 => -- a loop: a recursive join point over a counter and an accumulator
    let d := E.vars.size
    let jl := E.joins.size
    let Ebody := (E.pushN [.nat, .nat])
    let exitE := { Ebody with joins := E.joins.push none }
    let exit ← sub exitE τ
    let loopE := { (Ebody.push .nat).push .nat with joins := E.joins.push (some 2) }
    -- `m` at level d + 2, acc' at d + 3; the recursive jump sometimes comes
    -- from a nested join point
    let step ← pick #[Lam.Prim.natAdd, .natMul, .natSub]
    let again : Exp := .jump (loopE.joins.size - 1 - jl) [loopE.var (d + 2), loopE.var (d + 3)]
    let inc ← range 1 3
    let nested ← chance 30
    let succArm : Exp :=
      if nested then
        b (.prim step [Ebody.push .nat |>.var (d + 1), .lit (.nat inc)])
          -- the nested join point is not in scope in its own body, where the
          -- loop is join point 0
          (.join 2 false (.jump 0 [.var 1, .var 0]) (.jump 0 [loopE.var (d + 2), loopE.var (d + 3)]))
      else b (.prim step [Ebody.push .nat |>.var (d + 1), .lit (.nat inc)]) again
    let body : Exp :=
      .case (Ebody.var d) [.mk natZ 0 exit, .mk natS 1 succArm] none
    let body := if ← chance 50 then Exp.tick body else body
    let E' := { E with joins := E.joins.push (some 2) }
    let counter ← natAtom E
    let scope : Exp :=
      b (.prim .natMod [counter, .lit (.nat 8)]) (.jump 0 [.var 0, ← natAtom (E'.push .nat)])
    return .join 2 true body scope
  | 9 => return .tick (← sub E τ)
  | 10 => if ← chance 30 then return .trap else sub E τ
  | 11 => ret E τ
  | _ => do
    if let some j ← jump? E then return j
    ret E τ

/-- A program of 2–6 globals: global 0 the root (one `Nat` parameter), the
others of arity 0–3 (0: a CAF); a global of arity ≥ 1 is sometimes recursive
on its first parameter. With the root's result type. -/
def programTy : RngM (AProgram × Ty) := do
  let n ← range 2 6
  let tys := #[Ty.nat, .nat, .bool, .pair, .opt]
  let mut sigs : Array (Nat × Ty) := #[(1, ← pick tys)]
  for _ in [1:n] do
    let caf ← chance 25
    let arity ← range 1 3
    let ty ← pick tys
    sigs := sigs.push ((if caf then 0 else arity), ty)
  let mut gs : Array GDef := #[]
  for g in [0:n] do
    let (arity, τ) := sigs[g]!
    let E : Env := { self := g, sigs, vars := Array.replicate arity .nat }
    let body ← if arity ≥ 1 && (← chance 40) then do
        -- case on the first parameter; the successor arm may call itself on it
        let zero ← exp E τ 3
        let succ ← exp { E.push .nat with selfArg := some arity } τ 3
        pure (Exp.case (E.var 0) [.mk natZ 0 zero, .mk natS 1 succ] none)
      else exp E τ 4
    gs := gs.push { key := .const g [], ps := List.replicate arity {}, body }
  return ({ globals := Src.NatMap.ofList (gs.toList.zipIdx.map fun (gd, i) => (i, gd))
            size := n, roots := [0], ctors := LamGen.ctors, known := LamGen.known }, sigs[0]!.2)

def program : RngM AProgram := Prod.fst <$> programTy

/-- A seed's program and its root's result type. -/
def ofSeedTy (seed : Nat) : AProgram × Ty :=
  programTy.run' (Rng.ofSeed (UInt64.ofNat (seed * 104729 + 7))) |>.run

def ofSeed (seed : Nat) : AProgram := (ofSeedTy seed).1

/-- Counts over the generated programs. -/
structure Stats where
  programs : Nat := 0
  joins : Nat := 0
  loops : Nat := 0
  cells : Nat := 0
  backEdges : Nat := 0
  blocks : Nat := 0
  tally : Tally := {}

mutual
partial def countJoins : Exp → Nat × Nat
  | .bind _ _ e | .tick e => countJoins e
  | .join _ r bd e =>
    let (a, c) := countJoins bd
    let (a', c') := countJoins e
    (a + a' + (if r then 0 else 1), c + c' + (if r then 1 else 0))
  | .case _ alts d =>
    (alts.map (countJoins ·.body) ++ (d.map countJoins).toList).foldl
      (fun (x, y) (p, q) => (x + p, y + q)) (0, 0)
  | _ => (0, 0)
end

def firstOrder (a : Assert) (count : Nat) : IO (Array String) := do
  let mut s : Stats := {}
  for seed in [0:count] do
    let A := ofSeed seed
    let label := s!"generated seed {seed}"
    expect a (Anf.wellScoped A) s!"{label}: not WellScoped\n{A.render}"
    expect a (Anf.firstOrder A) s!"{label}: not FirstOrder"
    let L ← IO.ofExcept ((lower A).mapError (s!"{label}: " ++ ·))
    checkLevels a L label
    let mut t := s.tally
    for xs in [[0], [1], [2], [3], [5]] do
      t ← compareRun a L none 0 xs 3000 label t
      -- allocation under the immortal policy
      if let .ok (_, H) ← runOwn .immortal L.own 3000 0 xs then
        s := { s with cells := s.cells + H.cells.size }
    let (js, ls) := A.globalList.foldl (fun (x, y) (_, gd) =>
      let (p, q) := countJoins gd.body; (x + p, y + q)) (0, 0)
    s := { s with programs := s.programs + 1, tally := t, joins := s.joins + js, loops := s.loops + ls
                  backEdges := s.backEdges + IxCC.Cfg.backEdges L.cfg
                  blocks := s.blocks + L.cfg.blocks }
  return #[s!"{s.programs} first-order Anf programs: {s.joins} join points, {s.loops} loops, " ++
    s!"{s.blocks} Cfg blocks, {s.backEdges} back edges, {s.cells} immortal cells allocated",
    s!"  {s.tally.render}"]

/-- LamGen programs through the Phase 1 pipeline: each stage lowered or
declined. -/
def lamGen (a : Assert) (count : Nat) : IO (Array String) := do
  let mut lowered := 0
  let mut declined := 0
  let mut t : Tally := {}
  let mut programs := 0
  for seed in [0:count] do
    let LP := LamGen.ofSeed seed
    unless Lam.wellFormed LP && Lam.modesOk LP do continue
    programs := programs + 1
    let tr ← IO.ofExcept ((Anf.Pipeline.produce {} LP).mapError (s!"lamgen {seed}: " ++ ·))
    for (stage, A) in tr.stages do
      let r := Anf.Pipeline.residual A
      match IxCC.Fir.lower A with
      | .error (.closures fns apps globs) =>
        expect a (fns == r.fns && apps == r.apps && globs == r.globs)
          s!"lamgen {seed} {stage}: declined naming {fns} {apps} {globs}, residual {r.fns} {r.apps} {r.globs}"
        declined := declined + 1
      | .error e => expect a false s!"lamgen {seed} {stage}: {e.render}"
      | .ok _ =>
        expect a (r.fns.isEmpty && r.apps.isEmpty && r.globs.isEmpty)
          s!"lamgen {seed} {stage}: lowered with closures left"
        let L ← IO.ofExcept ((lower A).mapError (s!"lamgen {seed} {stage}: " ++ ·))
        checkLevels a L s!"lamgen {seed} {stage}"
        let some ar := anfRoot LP A 0 | throw (IO.userError s!"lamgen {seed}: no Anf root")
        for xs in [[0], [2], [5]] do
          t ← compareRun a L (some (LP, 0)) ar xs 3000 s!"lamgen {seed} {stage}" t
        lowered := lowered + 1
  return #[s!"{programs} LamGen programs through the pipeline: {lowered} stages lowered, " ++
    s!"{declined} declined for closures", s!"  {t.render}"]

end IxCCTests.Fir.Gen
