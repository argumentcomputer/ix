module

public import Ix.Tc.Mode
public import Ix.Address
public import Ix.Unsigned
public import Batteries.Data.RBMap

/-!
Mirror: crates/kernel/src/level.rs

Universe levels with optional metadata and Géran's canonical-form comparison.

`KUniv m` carries a Blake3 Merkle address at every node. `param` additionally
carries `m.F Name` — the parameter name in meta mode, erased in anon mode.
Parameter *identity* is the positional index; names are display-only and never
hashed, so anon and meta levels of the same structure share addresses.

`normalizeLevel` is a port of the Rust port of Lean4Lean's `Level.Normalize`
(Yoan Géran, "A Canonical Form for Universe Levels in Impredicative Type
Theory"). `NormLevel` maps sorted param-index paths (the imax conditioning
chain) to nodes tracking constant offsets and variable contributions.

Divergence inherited from Rust (see level.rs `norm_level_le` doc): the `≤`
check splits constant and variable coverage into independent searches
(`coversConst` / `coversVar`), strictly more complete than Lean4Lean's
single-witness `NormLevel.le`. `univEq` matches Lean4Lean's `isEquiv'`.
-/

public section
@[expose] section

namespace Ix.Tc

open Blake3.Rust (Hasher)

/-- Universe level. Each variant carries its Blake3 Merkle address.
    Variants are raw; use the `mk*` smart constructors, which perform
    Lean-style simplification for `max`/`imax` (reduced-term addresses must
    match the Rust kernel node-for-node). -/
inductive KUniv (m : Mode) where
  | zero (addr : Address)
  | succ (u : KUniv m) (addr : Address)
  | max (a b : KUniv m) (addr : Address)
  | imax (a b : KUniv m) (addr : Address)
  | param (idx : UInt64) (name : m.F Name) (addr : Address)

namespace KUniv

def addr : KUniv m → Address
  | .zero a
  | .succ _ a
  | .max _ _ a
  | .imax _ _ a
  | .param _ _ a => a

/-- Structural equality by Merkle address (Rust `hash_eq`). -/
instance : BEq (KUniv m) where
  beq a b := a.addr == b.addr

instance : Hashable (KUniv m) where
  hash u := hash u.addr

/-- True if this level is definitionally zero (Prop). -/
def isZero : KUniv m → Bool
  | .zero _ => true
  | _ => false

/-- True if this level is an explicit numeral: `succ^n zero` for some `n ≥ 0`. -/
def isExplicit : KUniv m → Bool
  | .zero _ => true
  | .succ u _ => u.isExplicit
  | _ => false

/-- True if this level is nonzero under every parameter assignment. -/
def isNeverZero : KUniv m → Bool
  | .succ _ _ => true
  | .max a b _ => a.isNeverZero || b.isNeverZero
  | .imax _ b _ => b.isNeverZero
  | _ => false

/-- Peel the outermost constant offset: returns `(base, n)` where
    `u = succ^n base` and `base` is not `succ`. -/
def offset : KUniv m → KUniv m × UInt64
  | .succ u _ => let (base, n) := u.offset; (base, n + 1)
  | u => (u, 0)

/-- `zero`, hashed as `blake3 [UZERO]`. -/
def mkZero : KUniv m :=
  .zero <| Address.blake3 ⟨#[Ix.TAG_UZERO]⟩

instance : Inhabited (KUniv m) := ⟨mkZero⟩

/-- `succ u`, hashed as `blake3 ([USUCC] ++ u.addr)`. -/
def mkSucc (u : KUniv m) : KUniv m := Id.run do
  let mut h := Hasher.init ()
  h := h.update ⟨#[Ix.TAG_USUCC]⟩
  h := h.update u.addr.hash
  return .succ u ⟨(h.finalizeWithLength 32).val⟩

/-- Raw `max` node without simplification; used by `mkMax` after all
    simplification opportunities are exhausted. -/
def mkMaxRaw (a b : KUniv m) : KUniv m := Id.run do
  let mut h := Hasher.init ()
  h := h.update ⟨#[Ix.TAG_UMAX]⟩
  h := h.update a.addr.hash
  h := h.update b.addr.hash
  return .max a b ⟨(h.finalizeWithLength 32).val⟩

/-- Raw `imax` node without simplification; used by `mkIMax`. -/
def mkIMaxRaw (a b : KUniv m) : KUniv m := Id.run do
  let mut h := Hasher.init ()
  h := h.update ⟨#[Ix.TAG_UIMAX]⟩
  h := h.update a.addr.hash
  h := h.update b.addr.hash
  return .imax a b ⟨(h.finalizeWithLength 32).val⟩

/-- `param idx`, hashed as `blake3 ([UPARAM] ++ idx.toLEBytes)` (8-byte LE).
    The name is display-only metadata and is NOT hashed. -/
def mkParam (idx : UInt64) (name : m.F Name) : KUniv m := Id.run do
  let mut h := Hasher.init ()
  h := h.update ⟨#[Ix.TAG_UPARAM]⟩
  h := h.update idx.toLEBytes
  return .param idx name ⟨(h.finalizeWithLength 32).val⟩

/-- Construct `max a b` with Lean-style simplifications (matches Lean's
    `mk_max`, `kernel/level.cpp:81-103`, and Rust `KUniv::max`):

    - both explicit numerals → the larger
    - `max a a = a`
    - `max 0 a = a`, `max a 0 = a`
    - `max a (max a b) = max a b` and variants (absorption)
    - `max (succ^n x) (succ^m x) = succ^(max n m) x` (same-base offset) -/
def mkMax (a b : KUniv m) : KUniv m :=
  if a.isExplicit && b.isExplicit then
    let (_, na) := a.offset
    let (_, nb) := b.offset
    if na ≥ nb then a else b
  else if a == b then a
  else if a.isZero then b
  else if b.isZero then a
  else
    -- max(a, max(a, b')) = max(a, b'); max(a, max(b', a)) = max(b', a)
    let absorbB := match b with
      | .max bl br _ => bl == a || br == a
      | _ => false
    if absorbB then b
    else
      -- max(max(a', b), b) = max(a', b); max(max(b, a'), b) = max(b, a')
      let absorbA := match a with
        | .max al ar _ => al == b || ar == b
        | _ => false
      if absorbA then a
      else
        let (baseA, offA) := a.offset
        let (baseB, offB) := b.offset
        if baseA == baseB then
          if offA ≥ offB then a else b
        else
          mkMaxRaw a b

/-- Construct `imax a b` with Lean-style simplifications (matches Lean's
    `mk_imax`, `kernel/level.cpp:112-120`, and Rust `KUniv::imax`):

    - `imax a b = max a b` when `b` is never zero
    - `imax a 0 = 0`
    - `imax 0 b = b`, `imax 1 b = b`
    - `imax a a = a` -/
def mkIMax (a b : KUniv m) : KUniv m :=
  if b.isNeverZero then mkMax a b
  else if b.isZero then b
  else if a.isZero then b
  else
    let aIsOne := match a with
      | .succ inner _ => inner.isZero
      | _ => false
    if aIsOne then b
    else if a == b then a
    else mkIMaxRaw a b

/-- Meta mode shows names when available; anon mode shows positional
    parameter indices. Diagnostics only. -/
partial def render : KUniv m → String
  | .zero _ => "0"
  | u@(.succ _ _) =>
    let (base, n) := u.offset
    if base.isZero then toString n.toNat
    else s!"{base.render}+{n.toNat}"
  | .max a b _ => s!"max({a.render}, {b.render})"
  | .imax a b _ => s!"imax({a.render}, {b.render})"
  | .param idx name _ =>
    if MetaDisplay.hasMeta name then MetaDisplay.metaFmt name
    else s!"u{idx.toNat}"

instance : ToString (KUniv m) := ⟨render⟩

instance : Repr (KUniv m) := ⟨fun u _ => .text u.render⟩

end KUniv

/-! ## Géran's canonical-form normalization and comparison -/

namespace Level

/-- A variable contribution: parameter index with a constant offset. -/
structure VarNode where
  idx : UInt64
  offset : UInt64
  deriving BEq, Repr, Inhabited

instance : Ord VarNode where
  compare a b := match compare a.idx b.idx with
    | .eq => compare a.offset b.offset
    | o => o

/-- Per-path node: a constant offset plus variable contributions sorted by
    ascending `idx`. -/
structure NormNode where
  constant : UInt64 := 0
  vars : Array VarNode := #[]
  deriving BEq, Repr, Inhabited

/-- Insert `(idx, k)` into the sorted var list, taking the max of offsets when
    `idx` is already present. `k` must be the current succ-accumulator from
    `normalizeAux` — an earlier Rust port dropped it and silently
    mis-normalized `succ^n(imax(u, param v))` for `n > 0`. -/
def NormNode.addVar (n : NormNode) (idx k : UInt64) : NormNode :=
  match n.vars.findIdx? (fun v => idx ≤ v.idx) with
  | some p =>
    let v := n.vars[p]!
    if v.idx == idx then
      { n with vars := n.vars.set! p { v with offset := max v.offset k } }
    else
      { n with vars := n.vars.insertIdx! p ⟨idx, k⟩ }
  | none => { n with vars := n.vars.push ⟨idx, k⟩ }

/-- An imax-conditioning chain: sorted param indices. -/
abbrev Path := List UInt64

/-- Canonical form: map from imax-paths to nodes. Rust `BTreeMap<Vec<u64>,
    Node>`; `Ord Path` is lexicographic in both. -/
abbrev NormLevel := Batteries.RBMap Path NormNode compare

instance : Inhabited NormLevel := ⟨.empty⟩

def NormLevel.addVar (s : NormLevel) (idx k : UInt64) (path : Path) : NormLevel :=
  s.insert path ((s.findD path {}).addVar idx k)

def NormLevel.addConst (s : NormLevel) (k : UInt64) (path : Path) : NormLevel :=
  if k == 0 || (k == 1 && !path.isEmpty) then s
  else
    let n := s.findD path {}
    s.insert path { n with constant := max n.constant k }

/-- Insert into a sorted list, returning `none` if already present. -/
def orderedInsert (a : UInt64) : Path → Option Path
  | [] => some [a]
  | x :: xs =>
    if a < x then some (a :: x :: xs)
    else if a == x then none
    else (x :: ·) <$> orderedInsert a xs

mutual

/-- Recursively flatten a level into canonical form, accumulating into `acc`.
    `path` tracks the imax-conditioning chain, `k` the accumulated succ offset.
    Mirrors level.rs `normalize_aux`. -/
partial def normalizeAux (l : KUniv m) (path : Path) (k : UInt64)
    (acc : NormLevel) : NormLevel :=
  match l with
  | .zero _ => acc.addConst k path
  | .succ inner _ => normalizeAux inner path (k + 1) acc
  | .max a b _ => normalizeAux b path k (normalizeAux a path k acc)
  | .imax u b _ =>
    match b with
    | .zero _ => acc.addConst k path
    | .succ v _ => normalizeAux v path (k + 1) (normalizeAux u path k acc)
    | .max v w _ => normalizeImaxMax u v w path k acc
    | .imax v w _ => normalizeImaxImax u v w path k acc
    | .param idx _ _ =>
      match orderedInsert idx path with
      | some newPath =>
        -- When param(idx) = 0, imax(u, 0) = 0, contributing k from outer succs.
        let acc := acc.addConst k path
        let acc := acc.addVar idx k newPath
        normalizeAux u newPath k acc
      | none =>
        -- idx already in path (fixed > 0 along this chain); the outer k succs
        -- still contribute. Matches Lean4Lean's `acc.addVar v k path`.
        let acc := if k != 0 then acc.addVar idx k path else acc
        normalizeAux u path k acc
  | .param idx _ _ =>
    match orderedInsert idx path with
    | some newPath => ((acc.addConst k path).addVar idx k newPath)
    | none => if k != 0 then acc.addVar idx k path else acc

/-- `imax(u, max(v, w)) = max(imax(u, v), imax(u, w))`. -/
partial def normalizeImaxMax (u v w : KUniv m) (path : Path) (k : UInt64)
    (acc : NormLevel) : NormLevel :=
  normalizeImaxDispatch u w path k (normalizeImaxDispatch u v path k acc)

/-- `imax(u, imax(v, w)) = max(imax(u, w), imax(v, w))`. -/
partial def normalizeImaxImax (u v w : KUniv m) (path : Path) (k : UInt64)
    (acc : NormLevel) : NormLevel :=
  normalizeImaxDispatch v w path k (normalizeImaxDispatch u w path k acc)

/-- Dispatch `imax(a, b)` normalization based on `b`'s shape. -/
partial def normalizeImaxDispatch (a b : KUniv m) (path : Path) (k : UInt64)
    (acc : NormLevel) : NormLevel :=
  match b with
  | .zero _ => acc.addConst k path
  | .succ v _ => normalizeAux v path (k + 1) (normalizeAux a path k acc)
  | .max v w _ => normalizeImaxMax a v w path k acc
  | .imax v w _ => normalizeImaxImax a v w path k acc
  | .param idx _ _ =>
    match orderedInsert idx path with
    | some newPath =>
      let acc := acc.addConst k path
      let acc := acc.addVar idx k newPath
      normalizeAux a newPath k acc
    | none =>
      let acc := if k != 0 then acc.addVar idx k path else acc
      normalizeAux a path k acc

end

/-! ### Subsumption (Phase 2) -/

/-- Keep only the `xs` entries not dominated by a `ys` entry (merge-walk over
    sorted var lists). Mirrors level.rs `subsume_vars`. -/
def subsumeVars (xs ys : Array VarNode) : Array VarNode := Id.run do
  let mut result : Array VarNode := #[]
  let mut xi := 0
  let mut yi := 0
  while xi < xs.size do
    if yi ≥ ys.size then
      result := result ++ xs.extract xi xs.size
      break
    let x := xs[xi]!
    let y := ys[yi]!
    if x.idx < y.idx then
      result := result.push x
      xi := xi + 1
    else if x.idx == y.idx then
      if x.offset > y.offset then
        result := result.push x
      xi := xi + 1
      yi := yi + 1
    else
      yi := yi + 1
  return result

/-- Sorted-list subset check. -/
def isSubset : Path → Path → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
    if y < x then isSubset (x :: xs) ys
    else if y == x then isSubset xs ys
    else false

/-- Drop contributions dominated by entries at sub-paths. Iterates entries and
    the pre-pass snapshot in ascending key order, exactly like Rust's
    `BTreeMap` traversal (in-loop `n1` mutations are order-sensitive). -/
def subsumption (acc : NormLevel) : NormLevel := Id.run do
  let snapshot := acc.toList
  let mut result := acc
  for (p1, n1₀) in snapshot do
    let mut n1 := n1₀
    for (p2, n2) in snapshot do
      if isSubset p2 p1 then
        let same := p1.length == p2.length
        if n1.constant != 0 then
          let maxVarOffset := n1.vars.foldl (fun acc v => max acc v.offset) 0
          let keepConst := (same || n1.constant > n2.constant)
            && (n2.vars.isEmpty || n1.constant > maxVarOffset + 1)
          if !keepConst then
            n1 := { n1 with constant := 0 }
        if !same && !n2.vars.isEmpty then
          n1 := { n1 with vars := subsumeVars n1.vars n2.vars }
    result := result.insert p1 n1
  return result

/-! ### Comparison -/

/-- Does some `(p2, n2) ∈ l2` with `p2 ⊆ p1` dominate the constant `c` along
    every assignment activating `p1`? A `p2` entry contributes `n2.constant`
    unconditionally in that branch, and each `v ∈ n2.vars` contributes at
    least `v.offset + 1` (its index is in `p2 ⊆ p1`, so `u_v ≥ 1`). -/
def coversConst (l2 : NormLevel) (p1 : Path) (c : UInt64) : Bool :=
  l2.toList.any fun (p2, n2) =>
    isSubset p2 p1
    && (c ≤ n2.constant || n2.vars.any (fun v => c ≤ v.offset + 1))

/-- Does some `(p2, n2) ∈ l2` with `p2 ⊆ p1` contain a variable node
    dominating `(w, off)`? -/
def coversVar (l2 : NormLevel) (p1 : Path) (w off : UInt64) : Bool :=
  l2.toList.any fun (p2, n2) =>
    isSubset p2 p1 && n2.vars.any (fun v => v.idx == w && v.offset ≥ off)

/-- Semantic `l1 ≤ l2` on canonical forms. Each ingredient of every `l1`
    entry must be covered by *some* `l2` entry at a sub-path — constant and
    variable coverage searched independently (see module doc: intentionally
    stronger than Lean4Lean's single-witness `NormLevel.le`). -/
def normLevelLe (l1 l2 : NormLevel) : Bool :=
  l1.toList.all fun (p1, n1) =>
    if n1.constant == 0 && n1.vars.isEmpty then true
    else
      (n1.constant == 0 || coversConst l2 p1 n1.constant)
      && n1.vars.all (fun v => coversVar l2 p1 v.idx v.offset)

def normLevelEq (l1 l2 : NormLevel) : Bool :=
  l1.size == l2.size
  && l1.toList.all fun (k, v1) =>
    match l2.find? k with
    | some v2 => v1.constant == v2.constant && v1.vars == v2.vars
    | none => false

/-- Normalize a universe level to Géran's canonical form. -/
def normalizeLevel (l : KUniv m) : NormLevel :=
  subsumption (normalizeAux l [] 0 ((∅ : NormLevel).insert [] {}))

end Level

/-- Semantic universe equality: `u ≡ v` for all parameter assignments. -/
def univEq (u v : KUniv m) : Bool :=
  u == v || Level.normLevelEq (Level.normalizeLevel u) (Level.normalizeLevel v)

/-- Check `u ≥ v` for all parameter assignments. -/
def univGeq (u v : KUniv m) : Bool :=
  u == v || v.isZero
  || Level.normLevelLe (Level.normalizeLevel v) (Level.normalizeLevel u)

end Ix.Tc

end
end
