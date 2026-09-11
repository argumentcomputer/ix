import Ix.Compiler.Ixon.Uses
import Ix.Compiler.AddressEnv

/-!
# IxIR₀: the erased core IR

The first IR after erasure and the semantic anchor of the backend
pipeline: every later stage (IxIR₀ˢ, IxIR₁, IxIR₂) refines IxIR₀'s
big-step semantics (`Eval.lean`), and the first theorem target is the
erasure simulation Ixon → IxIR₀.

Shape: an untyped, pure, **curried** λ-calculus (environment
semantics, no store — the heap appears at IxIR₁) with literals and
content-addressed globals: definitions, constructors, recursors, and
trusted externs. The IR boundaries are recorded in `docs/compiler/compiler-design.md`;
the key choices encoded here are:

- **Functional big-step + fuel** (CakeML-style): executable and
  proof-ergonomic; relational wrappers are derived, and termination
  claims are ∃-fuel statements.
- **CBV, strict lets**; left-to-right application order.
- **Curried** application mirroring Ixon; saturation/arity analysis
  arrives at IxIR₁ (the `papp`/`apply` vocabulary).
- **Recursor ι from day one**: recursors are declarations carrying
  rules; see `RecRule` for the environment convention that replaces
  self-reference.
- **Externs as oracle**: an extern declaration is just an arity; its
  semantics is a parametric oracle keyed by address — the
  trusted-extern ledger's formal hook (`docs/compiler/trusted-extern-ledger.md`).
- **No cost model here**: cost instrumentation attaches to IxIR₁
  memory ops, never to IxIR₀ steps or fuel.

## The erasure contract

What the erasure pass Ixon → IxIR₀ (`Ix/Compiler/Erase.lean`) must
produce; hand-written examples must obey the same discipline:

- 0-mode (`Uses.erased`) binders and arguments are **dropped**, not
  boxed. Sound because 0-positions must be kernel-total (gate decision
  (a): references to opaque/`partial`/extern constants at mode 0 are
  rejected upstream).
- Types, sorts, Pi's, motives, and index arguments are erased. A
  type-valued *occurrence* in a relevant position becomes
  `Expr.erased` (Coq extraction's ◻); it absorbs application and
  projection.
- **Constructor values carry kept fields only** — never parameters.
  Params are not projectable, so they need no runtime representation
  (Lean's own object model agrees). A `Decl.ctor`'s arity is its
  kept-field count; erasure drops param arguments at application
  sites.
- Quotients are compiled away (`Quot.mk r a ↦ a`, `Quot.lift f h q ↦
  f q`) — no IxIR₀ support needed.
- Binder modes (`Uses` on `lam`/`letE`) survive erasure with the
  invariant uses ≠ erased. They are **semantically inert** at this
  level — the interpreter ignores them — and exist so IxIR₁'s
  mode-directed memory lowering never re-runs usage analysis. (Ixon
  lets carry no mode; the erasure pass synthesizes it.)

## Deliberately absent (recorded, not forgotten)

- Mutual blocks / Ixon `rec_`: self-recursive recursors (`Nat.rec`,
  `List.rec`) are covered by the `RecRule` environment convention;
  *mutually-inductive* recursor families need block references and
  arrive when real corpora do (via the ix merge — the standalone
  importer is skipped, JCB 2026-08-12).
- Literal↔constructor coherence beyond `natLit` major-peeling. The source
  evaluator has opt-in, address-configured String constructor expansion, but
  certified erasure disables it until this target has a representation-aware
  counterpart. The GMP-extern vs unary-ctor story remains a separate gate.
- K-like reduction, structure eta, and `False.rec`-style
  unreachability (erasure will need an answer; candidates: `erased`,
  or an explicit `unreachable` extern on the ledger).
- Canonical declaration preimages and BLAKE3 address APIs live in
  `IxIR0/Serialize.lean`; strict declaration decoding lives in `Decode.lean`,
  and the cycle-safe symbolic block envelope plus final-key materializer live
  in `MutualBlock.lean`. Threading that block map through erasure and its
  simulations remains active before cached fixpoints can consume every key.
-/

namespace Ix.Compiler.IxIR0

open Ix.Compiler.Ixon (Uses Address Owned)

/-- Scalar literals surviving erasure (Ixon `natl`/`strl`). Machine
scalars (`UInt64`, …) appear only from IxIR₀ˢ on, as unboxings of
these. -/
inductive Literal where
  | nat (n : Nat)
  | str (s : String)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- IxIR₀ expressions: nameless (de Bruijn), erased, curried. -/
inductive Expr where
  /-- de Bruijn index into the evaluation environment. -/
  | var (idx : Nat)
  /-- Reference to a global declaration by content address. -/
  | ref (adr : Address)
  | app (fn arg : Expr)
  /-- One binder; `uses ≠ erased` (erased binders are dropped by
  erasure). The mode is semantically inert here. -/
  | lam (uses : Uses) (body : Expr)
  /-- Strict let. Not sugar for a β-redex because IxIR₁'s
  let-normalized (GRIN-style) world wants it explicit. -/
  | letE (uses : Uses) (val body : Expr)
  /-- Projection of the `idx`-th **kept** field of a structure value. -/
  | proj (idx : Nat) (struct : Expr)
  | lit (l : Literal)
  /-- ◻: an erased occurrence in a relevant position. Absorbs
  application and projection. -/
  | erased
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- One ι-rule of a recursor, selected by the major premise's
constructor tag. `rhs` is an open term evaluated in the environment

    fields.reverse ++ preMajor.reverse ++ [recursorValue]

i.e. de Bruijn 0 is the **last** constructor field, then earlier
fields, then the recursor's pre-major arguments last-to-first, and
finally (deepest) the recursor itself as an unapplied value — the
content-addressing-safe replacement for a self-`ref`, since a
recursor's rules cannot address the recursor without a hash cycle.

A kernel rule `fun params motives minors fields => …` erases to this
shape by dropping motives (and erased params/fields) and mapping
recursive occurrences of the recursor constant to the deepest
variable. `fields` is the kept-field count of the matching
constructor, checked at ι-time. -/
structure RecRule where
  fields : Nat
  rhs : Expr
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- Global declarations, keyed by content address in an `Env`. The
inductive *type* itself has no declaration — types are erased; only
its constructors and recursor survive. -/
inductive Decl where
  /-- A definition whose returned heap value lives in `result`;
  scalars are ownership-polymorphic. `body` must be closed. Evaluated
  at each `ref` (call-by-name at globals — spec-grade; the backend
  compiles, it never interprets). -/
  | defn (result : Owned) (body : Expr)
  /-- A constructor: `tag` is its index in the inductive, `arity` its
  kept-field count (params are never stored). -/
  | ctor (tag arity : Nat)
  /-- A recursor: `numArgs` kept arguments *before* the major premise
  (post-erasure: kept params + minors; motives and indices are
  erased), so the firing arity is `numArgs + 1`. `natLit` enables
  Nat-literal peeling of the major (`0 ↦ tag 0 []`, `n+1 ↦ tag 1
  [lit n]`) — set only on `Nat.rec` by the lowering; general
  literal↔ctor coherence is a recorded gate. `rules` is indexed by
  constructor tag. -/
  | recursor (numArgs : Nat) (natLit : Bool) (rules : Array RecRule)
  /-- A trusted extern of the given arity; semantics supplied by the
  evaluation oracle (the ledger's formal hook). -/
  | extern (arity : Nat)
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- The closed world: a Merkle-DAG of declarations as a partial map. The
kernel-facing representation stays a proof-friendly function; its list
constructor has a proved hash-index implementation for generated code. -/
abbrev Env := Address → Option Decl

def Env.empty : Env := fun _ => none

def Env.ofList (l : List (Address × Decl)) : Env :=
  fun a => (l.find? (fun p => p.1 == a)).map (·.2)

namespace Env

/-- The explicitly staged runtime representation of an environment. -/
abbrev Index := AddressEnv.Index Decl

def Index.ofList (l : List (Address × Decl)) : Index :=
  AddressEnv.build l

def Index.toEnv (index : Index) : Env :=
  AddressEnv.lookup index

/-- The runtime index implements the transparent first-binding-wins model. -/
@[simp] theorem Index.toEnv_ofList (l : List (Address × Decl)) :
    (Index.ofList l).toEnv = Env.ofList l := by
  exact AddressEnv.lookup_build l

end Env

end Ix.Compiler.IxIR0
