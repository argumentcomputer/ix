module

public import Ix.Tc.Mode
public import Ix.Address

/-!
Mirror: crates/kernel/src/id.rs (plus `FVarId`, hoisted from expr.rs to break
definition ordering).
-/

public section
@[expose] section

namespace Ix.Tc

/-- Kernel identifier: bundles a content address with a metadata name.
    In meta mode both fields participate in equality; in anon mode the name
    is `Unit` so only the address matters. -/
structure KId (m : Mode) where
  addr : Address
  name : m.F Name

namespace KId

/-- Equality compares `addr` and (meta mode) `name` — `KId` is a hash-map key
    and Rust's `PartialEq` does both. Anon names are `Unit` and always agree. -/
instance : BEq (KId m) where
  beq a b := a.addr == b.addr && Mode.F.beq a.name b.name

/-- Hash by address only. Sound with the `BEq` above: equal ids share an
    address, hence a hash. -/
instance : Hashable (KId m) where
  hash a := hash a.addr

/-- Address-major ordering; ties broken by name in meta mode.

    Divergence note vs Rust `Ord for KId`: Rust breaks ties by comparing
    `blake3(name.get_hash())` digests (`meta_cmp` re-hashes the `MetaHash`
    serialization); we compare the stored `name.getHash` bytes directly.
    Same equivalence classes, potentially different order between distinct
    names sharing an address. In anon mode (the v1 kernel) both orderings
    are pure address comparison, so canonical-sort agreement is unaffected. -/
def cmp (a b : KId m) : Ordering :=
  match a.addr.cmpBytes b.addr with
  | .eq => Mode.F.cmpBy (fun x y : Name => x.getHash.cmpBytes y.getHash) a.name b.name
  | o => o

instance : Ord (KId m) := ⟨cmp⟩

instance : Inhabited (KId m) := ⟨{ addr := default, name := Mode.F.mkDefault }⟩

/-- Meta mode: `Nat.add@a1b2c3d4`. Anon mode: `a1b2c3d4`. -/
def render (id : KId m) : String :=
  let hex := toString id.addr
  let short := (hex.take 8).toString
  if MetaDisplay.hasMeta id.name then
    s!"{MetaDisplay.metaFmt id.name}@{short}"
  else
    short

instance : ToString (KId m) := ⟨render⟩

instance : Repr (KId m) := ⟨fun id _ => .text id.render⟩

instance : MetaDisplay (KId m) where
  hasMeta id := MetaDisplay.hasMeta id.name
  metaFmt := render

end KId

/-- Per-`TypeChecker` unique identifier for a free variable. Embedded into the
    Blake3 content hash of `KExpr.fvar` nodes so distinct fvars hash
    distinctly — the soundness lever that lets cache keys be the expression
    hash alone (no separate local-context key). -/
structure FVarId where
  id : UInt64
  deriving BEq, Hashable, Repr, DecidableEq, Ord, Inhabited

instance : ToString FVarId := ⟨fun f => s!"fv${f.id}"⟩

end Ix.Tc

end
end
