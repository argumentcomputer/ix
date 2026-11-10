import IxCC.Src.Runtime
import Std.Data.HashSet

/-! # Src.Admit

The relevant closure and its rejection diagnostics:
reachability from the roots through the relevant positions of the runtime
view (resolved bodies, `eqn` bodies, `csimp` targets, the rules of reached
recursors, and the recursor under each reached `case` key). Reachability is
per universe profile (D18): a constant is reached as an instance
`(constant, profile)`, and a position is followed only where its class is
relevant at that profile, so a sort-polymorphic body instantiated at
`Sort 0` never reaches the proofs in its proof positions. `Admit` is not on
the recheck path, so it keeps its hash set and queue array. Every
reached reference is classified:

| Code | Condition | Outcome |
| --- | --- | --- |
| `relevant-axiom` | an axiom | reject |
| `relevant-theorem` | a theorem | reject (annotation error) |
| `relevant-type` | an inductive type or `Quot`/`Quot.ind` | reject (annotation error) |
| `unsafe` / `partial` | an unsafe or partial constant | reject; use `partial_fixpoint`, `termination_by` or fuel |
| `opaque` | an opaque outside `opaqueByValue` | reject |
| `unsupported` | a string literal before K4 | decline |
| `budget` | closure or term-size limits | decline |

A diagnostic carries the code, the address, the reference path from the
root and an optional untrusted name. `Admit` is not a stage-S soundness
premise: SrcEval is stuck on everything it rejects. It also reports the
runtime primitive set: the `prim` entries, eliminators, `case` keys, `lazy`
constants and quotient heads the closure reaches. -/

namespace IxCC.Src

open IxCC.Ixon

structure AdmitConfig where
  maxConsts : Nat := 1 <<< 14
  maxNodes : Nat := 1 <<< 22
  deriving Inhabited

/-- What the relevant closure contains, for the census and the backend. -/
structure Admitted where
  /-- Reached constants, in discovery order. -/
  reached : Array CId
  /-- Every instance `(constant, profile)` of the closure, in discovery order
  (a constant reached at two profiles appears twice). -/
  instances : Array Inst
  /-- The runtime terms of the closure. -/
  keys : Array TermKey
  prims : Array (CId × PrimOp)
  cases : Array CId
  /-- Each reached recursor instance with its kind at that profile. -/
  recursors : Array (CId × RecKind)
  lazy : Array CId
  quotHeads : Array CId
  eqns : Array CId
  csimps : Array CId
  /-- Safe definitions evaluated through their kernel body. -/
  bodies : Array CId
  deriving Inhabited

def isRejection (code : String) : Bool :=
  code != "unsupported" && code != "budget"

namespace Admit

def classify (p : Program) (c : CId) : Option (String × String) :=
  match p.table.resolveOf c with
  | some _ => none
  | none =>
    match p.decl? c with
    | some (.defn .thm _ ..) => some ("relevant-theorem", "a theorem in a relevant position")
    | some (.defn _ .unsaf ..) => some ("unsafe", "an unsafe definition; use a safe definition")
    | some (.defn _ .part ..) =>
      some ("partial", "a partial definition; use partial_fixpoint, termination_by or fuel")
    | some (.defn .opaq _ ..) =>
      if p.table.isOpaqueByValue c then none
      else some ("opaque", "an opaque constant outside the opaque-by-value allowlist")
    | some (.axio false _ _) => some ("unsafe", "an unsafe axiom")
    | some (.axio true _ _) => some ("relevant-axiom", "an axiom in a relevant position")
    | some (.induct _ _ _ _ _ _) => some ("relevant-type", "an inductive type in a relevant position")
    | some (.ctor false ..) => some ("unsafe", "an unsafe constructor")
    | some (.recr false ..) => some ("unsafe", "an unsafe recursor")
    | some (.quot .type ..) | some (.quot .ind ..) =>
      some ("relevant-type", "Quot or Quot.ind in a relevant position")
    | some _ => none
    | none => some ("unsupported", "a reference without a declaration")

/-- Whether a runtime term has a string literal in a position relevant at
`prof`. -/
def hasRelevantString (prof : Profile) : Term → Bool
  | .strLit _ => true
  | .app f a _ r => hasRelevantString prof f || (!r.irrP prof && hasRelevantString prof a)
  | .lam b _ t => !b.propWhen.holdsP prof && hasRelevantString prof t
  | .letE _ r _ v b =>
    (!r.irrP prof && hasRelevantString prof v) || hasRelevantString prof b
  | .proj _ _ e => hasRelevantString prof e
  | _ => false

end Admit

open Admit in
/-- Compute and classify the relevant closure. `names` supplies untrusted
names (from a sidecar) for diagnostics. -/
def admit (p : Program) (names : Address → Option String := fun _ => none)
    (cfg : AdmitConfig := {}) : Except (Array Diag) Admitted := Id.run do
  let n := p.size
  let mut parent : Array (Option CId) := .replicate n none
  let mut reached : Array Bool := .replicate n false
  let mut order : Array CId := #[]
  let mut keys : Array TermKey := #[]
  let mut diags : Array Diag := #[]
  let mut nodes := 0
  let mut seen : Std.HashSet Inst := {}
  let mut instances : Array Inst := #[]
  let mut queue : Array (Inst × Option CId) :=
    p.roots.toArray.map fun (_, c) => (p.instOf c [], none)
  let mut qi := 0
  let pathOf := fun (parent : Array (Option CId)) (c : CId) => Id.run do
    let mut path : List Address := []
    let mut cur := some c
    for _ in [0:n] do
      match cur with
      | some x =>
        path := p.addr x :: path
        cur := (parent[x]?).join
      | none => break
    return path
  while qi < queue.size do
    let ((c, prof), from_) := queue[qi]!
    qi := qi + 1
    if c ≥ n || seen.contains (c, prof) then continue
    seen := seen.insert (c, prof)
    instances := instances.push (c, prof)
    let first := !(reached[c]?.getD true)
    if first then
      reached := reached.set! c true
      parent := parent.set! c from_
      order := order.push c
      if order.size > cfg.maxConsts then
        diags := diags.push (Diag.of "budget" s!"more than {cfg.maxConsts} runtime constants" (some (p.addr c)))
        break
      if let some (code, message) := classify p c then
        diags := diags.push (Diag.of code message (some (p.addr c)) (pathOf parent c) (names (p.addr c)))
        continue
    else if (classify p c).isSome then continue
    for key in p.runtimeKeys c do
      let some t := p.termOf key | continue
      if first then
        keys := keys.push key
        nodes := nodes + t.nodes
      if hasRelevantString prof t then
        diags := diags.push (Diag.of "unsupported"
          "a string literal in a relevant position (strings are declined before K4)"
          (some (p.addr c)) (pathOf parent c) (names (p.addr c)))
    for (d, q) in p.instRefs c prof do queue := queue.push (p.instOf d q, some c)
  if nodes > cfg.maxNodes then
    diags := diags.push (Diag.of "budget" s!"runtime terms exceed {cfg.maxNodes} nodes")
  if !diags.isEmpty then return .error diags
  let recursors := instances.filterMap fun (c, prof) =>
    match p.table.resolveOf c, p.decl? c with
    | none, some (.recr ..) => some (c, ((p.table.recKindOf c).getD .ordinary).atProfile prof)
    | _, _ => none
  let mut out : Admitted := { reached := order, instances, keys, prims := #[], cases := #[]
                              recursors, lazy := #[], quotHeads := #[], eqns := #[], csimps := #[]
                              bodies := #[] }
  for c in order do
    if (p.table.lazyOf c).isSome then out := { out with lazy := out.lazy.push c }
    match p.table.resolveOf c with
    | some (.prim op) => out := { out with prims := out.prims.push (c, op) }
    | some (.case _) => out := { out with cases := out.cases.push c }
    | some (.eqn ..) => out := { out with eqns := out.eqns.push c }
    | some (.csimp ..) => out := { out with csimps := out.csimps.push c }
    | none =>
      match p.decl? c with
      | some (.quot ..) => out := { out with quotHeads := out.quotHeads.push c }
      | some (.defn ..) => out := { out with bodies := out.bodies.push c }
      | _ => pure ()
  return .ok out

end IxCC.Src
