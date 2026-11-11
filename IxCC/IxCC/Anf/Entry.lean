import IxCC.Anf.Syntax

/-! # Root entries at the declared parameter count

A root is called with exactly its declared number of parameters (the
leading arrows of its declared type; `docs/closures-design.md`, "Proof
obligation", the decisions of 2026-11-13 and 2026-11-14), and the compiler
makes the entry at that count, as Lean does for an exported definition. A
root's Anf global takes the leading λs of the body the unfolding table gives
it, which can be fewer (a point-free definition, a `csimp` target) or more
(a result type that is a definition of a function type) than the declared
count `n`.

`Entry.run decl P` gives each root whose Anf parameter count is not its
declared count (`decl`, by position) an entry: a new global of `n`
parameters (key `GKey.entry k n`, `k` the root's key) whose body is the
root's value applied to them,

```text
x ← glob r ; z ← app x [p₀ … pₙ₋₁] ; ret z
```

appended after the program's globals, and points the root's position at it.
A root whose counts agree is untouched. On an input of exactly `n`
arguments the entry runs what the root runs (`Anf.run` is the root's value,
then one application of all the arguments), one charge later
(`Anf.Entry.Proof.run_refines`). P8, which follows, turns the `glob` into the
root's closure cell and the `app` into a call of a dispatcher: an
under-applied root becomes a call through its closure, an over-applied one
returns a closure cell.

Deterministic, no certificate data. Kernel-evaluable: lists, `Src.NatMap`,
structural recursion. -/

namespace IxCC.Anf.Entry

/-- Inputs of exactly the declared count of the root at their position. -/
def DeclExact (decl : List Nat) (i : Nat × List Nat) : Prop :=
  ∀ n, decl[i.1]? = some n → i.2.length = n

/-- The entry's body over its `n` parameters (parameter `j` at index
`n - 1 - j`, so at `n - j` under the root's value): the root's value, applied
to all of them. -/
def body (r : GlobalId) (n : Nat) : Exp :=
  .bind freshLet (.glob r)
    (.bind freshLet (.app (.var 0) ((List.range n).map fun j => .var (n - j))) (.ret (.var 0)))

/-- Root `r`'s entry at `n` parameters. -/
def entryDef (P : Program) (r : GlobalId) (n : Nat) : GDef :=
  { key := .entry (((P.global? r).map (·.key)).getD (.dispatch 0)) n
    ps := List.replicate n {}, body := body r n }

/-- Each root by position: itself when its parameter count is its declared
count, else a new entry numbered from `next`; and the entries. -/
def plan (P : Program) : GlobalId → List (GlobalId × Nat) → List GlobalId × List (GlobalId × GDef)
  | _, [] => ([], [])
  | next, (r, n) :: rest =>
    if P.arity? r = some n then
      let p := plan P next rest
      (r :: p.1, p.2)
    else
      let p := plan P (next + 1) rest
      (next :: p.1, (next, entryDef P r n) :: p.2)

/-- The entries after the program's globals, and the roots pointed at them;
refused unless there is one declared count per root. -/
def run (decl : List Nat) (P : Program) : Except String Program :=
  if P.roots.length = decl.length then
    let p := plan P P.size (P.roots.zip decl)
    .ok { P with globals := p.2.foldl (fun m e => m.insert e.1 e.2) P.globals
                 size := P.size + p.2.length, roots := p.1 }
  else .error s!"the program has {P.roots.length} roots and {decl.length} declared counts"

end IxCC.Anf.Entry
