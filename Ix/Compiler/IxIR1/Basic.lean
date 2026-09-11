import Ix.Compiler.IxIR0.Basic

/-!
# IxIR₁: the first-order, store-based IR

The level where memory becomes explicit and modes start paying rent
(`docs/compiler/compiler-design.md`, architecture and proof boundaries). Shape, per
the recorded gate decisions:

- **Let-normalized and saturated** (gate C): code is a sequence of
  primitive operations binding one variable each, ending in `ret` or a
  `case`. Known calls carry exact arities; partial application is a
  reified `pap` node; unknown calls go through `apply` — the GRIN
  eval/apply vocabulary, with the interpreter as its semantic
  specification (generated closed-world dispatchers must refine it).
- **First-order**: no lambdas. Functions are top-level declarations;
  recursors are *gone* — the IxIR₀ → IxIR₁ lowering compiles their ι
  to `case` plus `callSelf` (content-addressing-safe self-reference,
  the recSelf idea one level down). Mutual blocks are deferred exactly
  as at IxIR₀.
- **Explicit store** (gate A): values are scalars or locations; nodes
  live in a heap. Every allocation, projection, in-place reuse,
  deallocation, and refcount operation is an instruction.
- **Mode-directed memory ops**: the unique world gets `reuse`/`free`
  (moves are implicit — a location is just consumed); the shared
  world gets `dup`/`drop` with Perceus-style deep drop at refcount
  zero. `dup`/`drop` on unique values and `reuse`/`free` on shared
  ones are *memory errors* — the interpreter is a dynamic checker for
  the discipline the static judgment will later prove unnecessary.
  Arena/locality ops arrive with the regions axis (frozen-deferred);
  reuse-token *pairing* is IxIR₂'s optimization — the `reuse`
  instruction itself is IxIR₁'s, since `reuse_sound` is an IxIR₁
  statement.
- **Cost lives here** (gate A): the store carries instruction-level
  counters (allocations, reuses, frees, RC ops), so claims like
  "reversal of a unique list allocates nothing" are `#guard`s in
  `Examples.lean`, and the zk cost model has its hook.

De Bruijn conventions: `letOp` binds one variable (index 0 in the
rest); a `case` alternative pushes the scrutinee's fields in order
(index 0 = *last* field, matching IxIR₀'s ι environment); a function
body starts with its arguments pushed in order (index 0 = last
argument).
-/

namespace Ix.Compiler.IxIR1

open Ix.Compiler.Ixon (Address Owned)
open Ix.Compiler.IxIR0 (Literal)

/-- Operands: everything is a variable, a scalar literal, or ◻.
Locations are runtime values only — code never names a location. -/
inductive Atom where
  | var (idx : Nat)
  | lit (l : Literal)
  | erased
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

/-- Constructor identity: the inductive's block address + member
index, and the constructor index — matching the source-side `ctorV`. -/
structure CtorId where
  block : Address
  indIdx : Nat
  cidx : Nat
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr, Inhabited

mutual

/-- One primitive operation; each binds exactly one variable. -/
inductive Op where
  /-- Rebind an atom (lowering convenience). -/
  | pure (a : Atom)
  /-- Allocate a constructor node in the given world. -/
  | alloc (world : Owned) (cid : CtorId) (args : Array Atom)
  /-- Overwrite a **live, unique** node in place: the FBIP payoff.
  Returns the same location; counts as a reuse, not an allocation. -/
  | reuse (target : Atom) (cid : CtorId) (args : Array Atom)
  /-- Shallow-free a **live, unique** node. -/
  | free (target : Atom)
  /-- Increment a **shared** node's refcount (no-op on scalars). -/
  | dup (target : Atom)
  /-- Decrement a **shared** node's refcount; at zero, free and
  recursively drop the fields (Perceus-style deep drop). -/
  | drop (target : Atom)
  /-- Deep-free a **live, unique** tree: kill the node and recurse
  into its fields (which must be unique — whole-value modes, gate B).
  The unique dual of `drop`'s rc-zero path, and the compilation of
  affine death; no refcounts are touched. No-op on scalars. -/
  | dropU (target : Atom)
  /-- Project field `i` of a constructor node (non-consuming). -/
  | fetch (target : Atom) (field : Nat)
  /-- Saturated call of a known function (exact arity). -/
  | call (f : Address) (args : Array Atom)
  /-- Saturated self-call: recursion without an address cycle. -/
  | callSelf (args : Array Atom)
  /-- Build a partial-application node: known `f`, strictly fewer
  arguments than its arity. -/
  | papp (f : Address) (args : Array Atom)
  /-- Apply an unknown function value (a `pap` node) to further
  arguments; may saturate (call), under-fill (new `pap`), or
  over-fill (call, then apply the rest to the result). Consumes the
  function value: the pap's stored arguments are dup'd for their new
  owner and the pap itself is dropped. -/
  | apply (f : Atom) (args : Array Atom)
  /-- Trusted extern. The v1 boundary is scalar-only in both directions:
  heap locations are rejected before or after consulting the oracle. -/
  | extern (f : Address) (args : Array Atom)

/-- A case alternative: constructor index, its field count, and the
continuation with the fields bound. -/
inductive Alt where
  | mk (cidx : Nat) (fields : Nat) (body : Code)

/-- Code: a let-sequence ending in a return or a branch. -/
inductive Code where
  | ret (a : Atom)
  | letOp (op : Op) (rest : Code)
  /-- Branch on a constructor node's tag. `peelNat` additionally
  accepts `Nat` literals (`0 ↦ cidx 0`, `n+1 ↦ cidx 1` binding
  `lit n`) — the IxIR₀ `natLit` story at this level. Non-consuming:
  frees and drops are explicit instructions. -/
  | case (scrut : Atom) (peelNat : Bool) (alts : Array Alt)

end

/-- A saturated top-level function. -/
structure FnDef where
  arity : Nat
  /-- Ownership world of a returned heap location. Scalars satisfy
  either result world. -/
  result : Owned
  /-- Whether this declaration may be entered through a shared PAP. The
  production lowerer sets this exactly when the result and every parameter
  live in the shared world; saturated direct calls remain valid either way. -/
  papSafe : Bool
  body : Code

/-- Top-level declarations. No constructor declarations (`alloc`
carries identity; first-class constructor use is eta-expanded by the
lowering) and no recursors (lowered to `case` + `callSelf`). -/
inductive Decl where
  | fn (d : FnDef)
  | extern (arity : Nat)

/-- The closed world of declarations. The transparent list model is retained
for proofs and compiled through the proved hash-index implementation below. -/
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

end Ix.Compiler.IxIR1
