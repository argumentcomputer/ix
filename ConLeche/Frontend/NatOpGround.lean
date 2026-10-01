module

public import Std.Data.HashSet.Basic
public import ConLeche.Kernel.Core

@[expose] public section

/-!
# Hoisting a pinned `Nat` operation's stream-certified ground (task #191)

The second half of the order-insensitivity fix, beside the built-in
prelude (`ConLeche/Frontend/Prelude.lean`).

A pin-certified operation's certificate *statements* are spelled over
the structural `Nat` operations (`natOpDeps`: `Nat.shiftLeft`'s over
`Nat.ble` and `Nat.sub`, `Nat.land`'s over `Nat.mul`, …), and the
install guard `divModEnvGuard` requires those stored — they are what
the model reads the statements through.  They are NOT in the
operation's own dependency closure, so an export that orders
declarations by a DFS from arbitrary roots (`lean4export` walks
`env.constants` in hash order; the raw export of
`tests/e2e/src/natop_order.lean` emits `Nat.shiftLeft` before
`Nat.ble`/`Nat.sub`/`Bool`) declined at the install.

They cannot go into the prelude: the structural operations are
certified at install by *definitional* recurrence equations
(`certifyNatEqs`) — deliberately not by a syntactic pin, so that a
stream from another toolchain still installs them (`Nat.add` gained a
separate `._f` functional between the 4.29 fixtures and the 4.33
build; a syntactic prelude copy would decline every 4.29 stream,
`good/init-prelude` included).  So instead the parsed stream is
REORDERED: for every pinned operation record whose `natOpDeps` ground
is declared LATER in the stream, the ground's transitive dependency
closure (within the stream) is moved ahead of the operation.  A
dependency-closed set moved earlier is still a valid stream — every
record still follows everything it references, and the moved records
see exactly their own closure (plus the prelude) — so the checker's
verdict on a valid stream is the official kernel's, whatever order the
export chose.  Like the prelude prepend it sits beside, this is a pure transformation
of the parsed list below the verified fold — a step of
`preparePrelude` (`ConLeche/Frontend/Prepare.lean`), not of the parse:
nothing in the kernel or the proofs knows it happened.

The pass is a no-op — the array is returned as it is, no sort — on
every stream whose ground precedes its operations (the toolchain's own
export order: `init-full`, Mathlib), so it costs one name-index build
and nothing else there.
-/

namespace ConLeche.Frontend

open ConLeche

/-- The constants an `Expr` DAG references, each node visited once
(`Std.HashSet Expr`: pointer-first equality, computed hash). -/
def usedConstsGo (seen : Std.HashSet Expr) (acc : Array Name) (e : Expr) :
    Std.HashSet Expr × Array Name :=
  if seen.contains e then (seen, acc) else
  let seen := seen.insert e
  match e with
  | .const n _ .. => (seen, acc.push n)
  | .app f a .. =>
    let (seen, acc) := usedConstsGo seen acc f
    usedConstsGo seen acc a
  | .lam ty b _ .. =>
    let (seen, acc) := usedConstsGo seen acc ty
    usedConstsGo seen acc b
  | .forallE ty b _ .. =>
    let (seen, acc) := usedConstsGo seen acc ty
    usedConstsGo seen acc b
  | .letE ty v b .. =>
    let (seen, acc) := usedConstsGo seen acc ty
    let (seen, acc) := usedConstsGo seen acc v
    usedConstsGo seen acc b
  | .proj sn _ x .. => usedConstsGo seen (acc.push sn) x
  | .fvar _ ty .. => usedConstsGo seen acc ty
  | _ => (seen, acc)

/-- The constants a parsed record references (types, values, recursor
rule right-hand sides; a basis block references nothing the stream
declares). -/
def _root_.ConLeche.Declaration.usedConsts : Declaration → Array Name
  | .axiomDecl cv => (usedConstsGo {} #[] cv.type).2
  | .defnDecl cv v _ | .thmDecl cv v | .opaqueDecl cv v =>
    let (seen, acc) := usedConstsGo {} #[] cv.type
    (usedConstsGo seen acc v).2
  | .indDecl block _ =>
    (block.foldl (init := (({} : Std.HashSet Expr), (#[] : Array Name)))
      fun (seen, acc) ci =>
        let (seen, acc) := usedConstsGo seen acc ci.toConstantVal.type
        match ci with
        | .recInfo _ _ _ rules =>
          rules.foldl (fun (seen, acc) r => usedConstsGo seen acc r.rhs) (seen, acc)
        | _ => (seen, acc)).2
  | .basisDecl _ | .quotDecl .. => #[]

/-- The pinned `Nat` operation records whose ground the pass serves:
the pin-certified WF operations and the structural ones (whose
`natOpDeps` are in their own closures already — kept uniform). -/
def isNatOpRecord : Declaration → Option Name
  | .defnDecl cv .. =>
    if natDivModNames.contains cv.name || natOpNames.contains cv.name then some cv.name
    else none
  | _ => none

/-- **Which records must move, and how far**: the map from a record's
index to the earliest pinned-operation index it must precede.  Empty —
and then the hoist is the identity — on every stream whose ground
precedes its operations. -/
def hoistTargets (ds : Array Declaration) : Std.HashMap Nat Nat := Id.run do
  -- name ↦ the index of the record declaring it (the first, on a
  -- duplicate — the fold rejects the second anyway)
  let mut idx : Std.HashMap Name Nat := {}
  for i in [0:ds.size] do
    for n in ds[i]!.names do
      if !idx.contains n then idx := idx.insert n i
  -- moved record ↦ the earliest operation index it must precede
  let mut target : Std.HashMap Nat Nat := {}
  for i in [0:ds.size] do
    let some c := isNatOpRecord ds[i]! | continue
    for g in natOpDeps c do
      let some j := idx[g]? | continue
      unless j > i do continue
      -- the closure of `j` within the records after `i`
      let mut stack : Array Nat := #[j]
      while h : stack.size > 0 do
        let k := stack[stack.size - 1]
        stack := stack.pop
        match target[k]? with
        | some t => if t ≤ i then continue
        | none => pure ()
        target := target.insert k i
        for n in ds[k]!.usedConsts do
          if let some m := idx[n]? then
            if m > i && m != k then stack := stack.push m
  return target

/-- **The reorder**: a moved record sorts at its target, just ahead of
the operation record there (key `(t, 0, k)` against the operation's
`(t, 1, t)`); everything else keeps its position (`(k, 1, k)`).  Moved
records with the same target keep their relative order, which is
dependency order.

The sort is `List.mergeSort` and not `Array.qsort` for one reason: the
result is a PERMUTATION of the input, and that is a property the
prepared list's shape lemma states (`mergeSort_perm`,
`ConLeche/Verify/Frontend/Prepare.lean`).  The keys are pairwise
distinct (each carries its own index), so the order is the same one
`qsort` produced. -/
def applyHoist (ds : Array Declaration) (target : Std.HashMap Nat Nat) :
    Array Declaration × Array Name :=
  let key : Nat → Nat × Nat × Nat := fun k =>
    match target[k]? with
    | some t => (t, 0, k)
    | none => (k, 1, k)
  let lt : Nat → Nat → Bool := fun a b =>
    let (ta, sa, ka) := key a
    let (tb, sb, kb) := key b
    ta < tb || (ta == tb && (sa < sb || (sa == sb && ka < kb)))
  let order := (List.range ds.size).mergeSort (fun a b => !lt b a)
  let moved := (Array.range ds.size).filter (target.contains ·)
  ((order.map (ds[·]!)).toArray, moved.flatMap fun k => (ds[k]!.names).toArray)

/-- **The hoist.**  Returns the reordered records and the names of the
records moved (empty, and the array untouched, when no operation's
ground is declared after it). -/
def hoistNatOpGround (ds : Array Declaration) : Array Declaration × Array Name :=
  let target := hoistTargets ds
  if target.isEmpty then (ds, #[]) else applyHoist ds target

end ConLeche.Frontend
