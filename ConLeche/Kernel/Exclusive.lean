module

@[expose] public section

/-!
# `withExclusive`: the reference-count read behind the walk memo

**What it is.**  `withExclusive a k h` runs the continuation `k` on
whether the object `a` is *exclusive* — single-threaded with reference
count exactly 1, so that no other reference to it exists.  In the logic
it is `k false` ("not known to be exclusive", the conservative answer);
in compiled code `@[implemented_by]` substitutes `k
(isExclusiveUnsafe a)`, the real count read off the object header
(`Init/Util.lean`, `@[extern "lean_is_exclusive_obj"]`, a BORROWED
parameter; `lean_is_exclusive` in `lean.h`).  A multi-threaded object
(count `< 0`) and a persistent one (count `0` — the installed
environment after the driver's `Runtime.markPersistent`) answer
`false`, which is the safe side.

**What licenses the substitution** is the obligation

```
h : k true = k false
```

— the continuation's value does not depend on the answer, so the
compiled program computes the very value the definition names.  A
caller may use the answer to choose *how* to compute a value, never
*which* value.  `Init.Util`'s `withPtrAddr` is the same arrangement
(`k 0` in the model, the address in the binary, the continuation
address-blind by obligation), and `Bool` being two-valued makes
`k true = k false` the whole of `∀ b₁ b₂, k b₁ = k b₂`.

**What it is for.**  The per-walk memo tables of the substitution walks
(`ConLeche/Cached/ExprOpsC.lean`) exist for one reason: a node reached
twice — a shared sub-DAG — must be rebuilt once, so that the walk is
`O(DAG)` and its OUTPUT stays shared.  A node with exactly one
reference cannot be reached twice, so recording it is pure loss: the
key, the entry, the probe.  The official kernel's `replace_fn`
(`src/kernel/replace_fn.cpp`) therefore caches a node's replacement
only when `!is_likely_unshared(e)` — the same read.  The walks memoise
exactly the nodes this primitive reports shared.

**How the walks discharge `h`.**  Their result is a `Squash` — a
`Subsingleton`, exactly as `Expr.beqGoX`'s `BeqOut` is — carrying the
rebuilt term with its proof of correctness beside an unobservable
memo, so `h` is `Subsingleton.elim` (`withExcl` below).

**The obligation cannot be weakened to the visible component.**  A
continuation returning the term beside a *bare* memo has
`k true ≠ k false` (the memo differs), and an obligation on the term
alone would leave the compiled memo — which later nodes probe —
outside the theorem.  The quotient is what makes the proof honest: the
memo's content is invisible to the type, its correctness is carried in
the memo's own type (`ConLeche/Cached/ExprOpsC.lean`: each entry
carries its proof), and the result's term is fixed by its subtype.

**The borrowed-parameter requirement.**  An owned parameter, a `let`
keeping the object alive across the call, a closure capturing it or a
`Prod` holding it is a second reference, and the read then answers
`false` for every node.  This module is `@[inline]` all the way to the
`@[extern]` call with the borrowed parameter, and the walks pass their
node BORROWED (`@&`) so that the count read is the count of references
*inside the term*.  The check is the IR audit of the tasks #314 and
#316 records (DESIGN.md): the generated C of every walk must show no
`lean_inc_ref` of the node before `lean_is_exclusive_obj`.

**Trust.**  This is the ONE `unsafe`-implemented primitive of the
substitution walks, and the only escape they add to the trust surface:
`tests/trust-surface.sh` allowlists this file for `unsafe` and
`implemented_by`, and that entry's justification is this docstring.
Nothing here is taken on faith beyond what `withPtrAddr` already asks —
the runtime's promise that `lean_is_exclusive_obj` returns a `Bool` and
has no other effect.  *Which* `Bool` is irrelevant to every theorem,
by `h`.

**Upstream.**  The primitive is proposed for `Init/Util.lean` in the
Lean RFC <https://github.com/leanprover/lean4/issues/15235>; the two
definitions below are written to be lifted there verbatim and have no
dependency on this tree.  When upstream ships it, this module becomes a
re-export.
-/

namespace ConLeche

set_option linter.unusedVariables.funArgs false in
/-- The compiled `withExclusive`: the continuation on the object's real
exclusivity.  Inlined into its caller, so the object reaches the
`@[extern]` check as the caller's own variable — BORROWED by the
check's signature — and the call adds no reference; the continuation
receives only the `Bool`.  (`implemented_by` demands the exact type of
`withExclusive`, so `a` carries no `@&` here; the borrow that matters
is `isExclusiveUnsafe`'s.) -/
@[inline] unsafe def withExclusiveUnsafe {α : Type u} {β : Type v} (a : α)
    (k : Bool → β) (h : k true = k false) : β :=
  k (isExclusiveUnsafe a)

/-- Run `k` on whether `a` is an exclusive object — single-threaded
with reference count 1, so that no other reference to it exists — in
compiled code; in the logic, on `false`.

The obligation `h : k true = k false` says the continuation's value does
not depend on the answer, so the substitution is invisible: a caller
may use the answer only to choose *how* to compute a value, never
*which* value — typically to skip a memo probe for an object that
cannot be reached again.  The pattern of `withPtrAddr`. -/
@[implemented_by withExclusiveUnsafe]
def withExclusive {α : Type u} {β : Type v} (a : α) (k : Bool → β)
    (h : k true = k false) : β :=
  k false

/-- `withExclusive` into a subsingleton: the obligation is
`Subsingleton.elim` (the `Expr.withAddr` shape). -/
@[inline] def withExcl {α : Type u} {β : Type v} [Subsingleton β] (a : α)
    (k : Bool → β) : β :=
  withExclusive a k (Subsingleton.elim _ _)

end ConLeche
