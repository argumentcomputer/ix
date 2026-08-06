module

public import Ix.Ixon
public import Batteries.Data.RBMap

/-!
Universe-level canonicalization (canonicity §10.6).

Mirror: crates/ixon/src/canon_univ.rs

`canonUniv = linearize ∘ subsumption ∘ normalizeAux` — a total,
deterministic canonical representative of a stored level's Géran
semantic-equality class, kernel-free and next to the wire type so
`Ix.CompileM`, the Tc egress, and probes can all use it. The Géran
machinery is the transliteration of `Ix/Tc/Level.lean:227-472` onto
`Ixon.Univ` (positional `var` indices; no metadata); the three kernel
`NormLevel` implementations stay untouched and serve as the P4 oracle.

The frozen kernel `mk*` rule set (M1–M8 / I1–I6) is kept with its
kernel-rebuild role: `reduceUniv` is the stage-1 decoration-presence
test and the P6 oracle, and P3 (canonical forms are `mk*` fixpoints) is
what makes kernel ingress the identity on canonical content.
(`Ix.Tc.reduceIxonUniv` computes the same closure by rounding through
the actual kernel constructors; `tc-unit` pins their agreement.)

Property set (tested in `Tests/Ix/Tc/Unit.lean` and the Rust twin;
Verify-layer proofs are the D7 follow-up): P1 idempotence; P2
roundtrip-fixpoint (`normalize (linearize L) = L`, exact on non-empty
entries — `subsumption` can leave EMPTY entries which `linearize`
cannot and should not re-express); P3 `mk*`-fixpoint; P4 soundness vs
kernel `univEq` (modulo the same empty-entry caveat — 3 of 3,253,373
whole-Mathlib entries sit in classes distinguished only by the
artifact); P5 byte parity with the Rust twin (FFI cross-check); P6
`mk*` absorption.
-/

public section
@[expose] section

namespace Ixon

namespace Univ

/-- Constructor count — termination measure for the normalization
    family (mirrors `Ix.Tc.KUniv.size`). -/
def size : Univ → Nat
  | .zero => 1
  | .succ u => u.size + 1
  | .max a b => a.size + b.size + 1
  | .imax a b => a.size + b.size + 1
  | .var _ => 1

theorem size_pos (u : Univ) : 0 < u.size := by
  cases u <;> simp [size]

/-- True if this level is an explicit numeral `succ^n zero`. -/
def isExplicit : Univ → Bool
  | .zero => true
  | .succ u => u.isExplicit
  | _ => false

/-- True if this level is nonzero under every parameter assignment. -/
def isNeverZero : Univ → Bool
  | .succ _ => true
  | .max a b => a.isNeverZero || b.isNeverZero
  | .imax _ b => b.isNeverZero
  | _ => false

/-- Peel the outermost constant offset: `(base, n)` with
    `u = succ^n base`, `base` not a `succ`. -/
def offset : Univ → Univ × UInt64
  | .succ u => let (base, n) := u.offset; (base, n + 1)
  | u => (u, 0)

/-- `succ^n u`. -/
def addSuccs (u : Univ) : Nat → Univ
  | 0 => u
  | n + 1 => .succ (addSuccs u n)

end Univ

/-- `mkMax` of the frozen kernel rule set (M1–M8), on `Ixon.Univ`:
    numerals → the larger (ties → `a`); `max a a = a`; zero sides;
    absorption; same-base offsets; raw. Mirrors `Ix.Tc.KUniv.mkMax` /
    Rust `canon_univ::n_max`. -/
def nMax (a b : Univ) : Univ :=
  if a.isExplicit && b.isExplicit then
    let (_, na) := a.offset
    let (_, nb) := b.offset
    if na ≥ nb then a else b
  else if a == b then a
  else if a matches .zero then b
  else if b matches .zero then a
  else
    let absorbB := match b with
      | .max bl br => bl == a || br == a
      | _ => false
    if absorbB then b
    else
      let absorbA := match a with
        | .max al ar => al == b || ar == b
        | _ => false
      if absorbA then a
      else
        let (baseA, offA) := a.offset
        let (baseB, offB) := b.offset
        if baseA == baseB then
          if offA ≥ offB then a else b
        else .max a b

/-- `mkIMax` of the frozen kernel rule set (I1–I6), on `Ixon.Univ`. -/
def nIMax (a b : Univ) : Univ :=
  if b.isNeverZero then nMax a b
  else if b matches .zero then b
  else if a matches .zero then b
  else
    let aIsOne := match a with
      | .succ .zero => true
      | _ => false
    if aIsOne then b
    else if a == b then a
    else .imax a b

/-- The kernel-rebuild closure on stored trees: bottom-up rebuild through
    the simplifying constructors — exactly what anon/meta ingress does.
    A non-fixpoint entry reaches the kernel changed (the stage-1
    decoration-presence test); P6 pins that this rebuild refines into
    the Géran classes. `tc-unit` pins agreement with
    `Ix.Tc.reduceIxonUniv` (the same closure via the kernel's own
    constructors). -/
def reduceUniv : Univ → Univ
  | .zero => .zero
  | .var i => .var i
  | .succ i => .succ (reduceUniv i)
  | .max a b => nMax (reduceUniv a) (reduceUniv b)
  | .imax a b => nIMax (reduceUniv a) (reduceUniv b)

namespace CanonUniv

/-- An imax-conditioning chain: sorted param indices. -/
abbrev CPath := List UInt64

/-- Per-path node: constant plus `(idx, offset)` var contributions
    sorted by ascending idx. Normalizer invariant: every var's idx is a
    member of its own path (self-gating is free). -/
structure CNode where
  constant : UInt64 := 0
  vars : Array (UInt64 × UInt64) := #[]
  deriving BEq, Repr, Inhabited

def CNode.isEmpty (n : CNode) : Bool :=
  n.constant == 0 && n.vars.isEmpty

/-- Canonical form: map from imax-paths to nodes (lexicographic). -/
abbrev CNorm := Batteries.RBMap CPath CNode compare

instance : Inhabited CNorm := ⟨.empty⟩

/-- Insert `(idx, k)` into the sorted var list, max-merging offsets.
    `k` must be the current succ-accumulator (`Ix/Tc/Level.lean:249-252`
    — dropping it is the classic port bug). -/
def CNode.addVar (n : CNode) (idx k : UInt64) : CNode :=
  match n.vars.findIdx? (fun v => idx ≤ v.1) with
  | some p =>
    let v := n.vars[p]!
    if v.1 == idx then
      { n with vars := n.vars.set! p (v.1, max v.2 k) }
    else
      { n with vars := n.vars.insertIdx! p (idx, k) }
  | none => { n with vars := n.vars.push (idx, k) }

def CNorm.addVar (s : CNorm) (idx k : UInt64) (path : CPath) : CNorm :=
  s.insert path ((s.findD path {}).addVar idx k)

def CNorm.addConst (s : CNorm) (k : UInt64) (path : CPath) : CNorm :=
  if k == 0 || (k == 1 && !path.isEmpty) then s
  else
    let n := s.findD path {}
    s.insert path { n with constant := max n.constant k }

/-- Insert into a sorted list, `none` if already present. -/
def orderedInsert (a : UInt64) : CPath → Option CPath
  | [] => some [a]
  | x :: xs =>
    if a < x then some (a :: x :: xs)
    else if a == x then none
    else (x :: ·) <$> orderedInsert a xs

/-!
Termination mirrors `Ix/Tc/Level.lean:289-296`: the measure is
`3·Σ Univ.size + {0,1,2}` ordering the equal-size hops between the
mutual members.
-/
mutual

/-- Flatten a level into canonical form (`Ix.Tc.Level.normalizeAux` on
    `Ixon.Univ`). `path` is the imax-conditioning chain, `k` the
    accumulated succ offset. -/
def normalizeAux (l : Univ) (path : CPath) (k : UInt64) (acc : CNorm) :
    CNorm :=
  match l with
  | .zero => acc.addConst k path
  | .succ inner => normalizeAux inner path (k + 1) acc
  | .max a b => normalizeAux b path k (normalizeAux a path k acc)
  | .imax u b =>
    match b with
    | .zero => acc.addConst k path
    | .succ v => normalizeAux v path (k + 1) (normalizeAux u path k acc)
    | .max v w => normalizeImaxMax u v w path k acc
    | .imax v w => normalizeImaxImax u v w path k acc
    | .var idx =>
      match orderedInsert idx path with
      | some newPath =>
        let acc := acc.addConst k path
        let acc := acc.addVar idx k newPath
        normalizeAux u newPath k acc
      | none =>
        let acc := if k != 0 then acc.addVar idx k path else acc
        normalizeAux u path k acc
  | .var idx =>
    match orderedInsert idx path with
    | some newPath => ((acc.addConst k path).addVar idx k newPath)
    | none => if k != 0 then acc.addVar idx k path else acc
termination_by 3 * l.size
decreasing_by all_goals simp [Univ.size] <;> omega

/-- `imax(u, max(v, w)) = max(imax(u, v), imax(u, w))`. -/
def normalizeImaxMax (u v w : Univ) (path : CPath) (k : UInt64)
    (acc : CNorm) : CNorm :=
  normalizeImaxDispatch u w path k (normalizeImaxDispatch u v path k acc)
termination_by 3 * (u.size + v.size + w.size) + 1
decreasing_by
  all_goals have hv := Univ.size_pos v
  all_goals have hw := Univ.size_pos w
  all_goals omega

/-- `imax(u, imax(v, w)) = max(imax(u, w), imax(v, w))`. -/
def normalizeImaxImax (u v w : Univ) (path : CPath) (k : UInt64)
    (acc : CNorm) : CNorm :=
  normalizeImaxDispatch v w path k (normalizeImaxDispatch u w path k acc)
termination_by 3 * (u.size + v.size + w.size) + 1
decreasing_by
  all_goals have hu := Univ.size_pos u
  all_goals have hv := Univ.size_pos v
  all_goals omega

/-- Dispatch `imax(a, b)` on `b`'s shape. -/
def normalizeImaxDispatch (a b : Univ) (path : CPath) (k : UInt64)
    (acc : CNorm) : CNorm :=
  match b with
  | .zero => acc.addConst k path
  | .succ v => normalizeAux v path (k + 1) (normalizeAux a path k acc)
  | .max v w => normalizeImaxMax a v w path k acc
  | .imax v w => normalizeImaxImax a v w path k acc
  | .var idx =>
    match orderedInsert idx path with
    | some newPath =>
      let acc := acc.addConst k path
      let acc := acc.addVar idx k newPath
      normalizeAux a newPath k acc
    | none =>
      let acc := if k != 0 then acc.addVar idx k path else acc
      normalizeAux a path k acc
termination_by 3 * (a.size + b.size) + 2
decreasing_by all_goals simp [Univ.size]; omega

end

/-- Sorted-list subset check. -/
def isSubset : CPath → CPath → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
    if y < x then isSubset (x :: xs) ys
    else if y == x then isSubset xs ys
    else false

/-- Keep only the `xs` entries not dominated by a `ys` entry
    (merge-walk over sorted var lists — `Ix.Tc.Level.subsumeVars`). -/
def subsumeVars (xs ys : Array (UInt64 × UInt64)) :
    Array (UInt64 × UInt64) :=
  go 0 0 #[]
where
  go (xi yi : Nat) (result : Array (UInt64 × UInt64)) :
      Array (UInt64 × UInt64) :=
    if _hx : xi < xs.size then
      if _hy : yi ≥ ys.size then
        result ++ xs.extract xi xs.size
      else
        let x := xs[xi]!
        let y := ys[yi]!
        if x.1 < y.1 then
          go (xi + 1) yi (result.push x)
        else if x.1 == y.1 then
          go (xi + 1) (yi + 1)
            (if x.2 > y.2 then result.push x else result)
        else
          go xi (yi + 1) result
    else
      result
  termination_by (xs.size - xi) + (ys.size - yi)
  decreasing_by all_goals omega

/-- Drop contributions dominated by entries at sub-paths
    (`Ix.Tc.Level.subsumption` — the in-loop `n1` mutations are
    order-sensitive). -/
def subsumption (acc : CNorm) : CNorm := Id.run do
  let snapshot := acc.toList
  let mut result := acc
  for (p1, n1₀) in snapshot do
    let mut n1 := n1₀
    for (p2, n2) in snapshot do
      if isSubset p2 p1 then
        let same := p1.length == p2.length
        if n1.constant != 0 then
          let maxVarOffset := n1.vars.foldl (fun m v => max m v.2) 0
          let keepConst := (same || n1.constant > n2.constant)
            && (n2.vars.isEmpty || n1.constant > maxVarOffset + 1)
          if !keepConst then
            n1 := { n1 with constant := 0 }
        if !same && !n2.vars.isEmpty then
          n1 := { n1 with vars := subsumeVars n1.vars n2.vars }
    result := result.insert p1 n1
  return result

/-- Normalize a stored level to Géran's canonical form. -/
def normalize (u : Univ) : CNorm :=
  subsumption (normalizeAux u [] 0 ((∅ : CNorm).insert [] {}))

/-- Canonical-form equality modulo EMPTY entries (value-free subsumption
    artifacts; the kernels' `normLevelLe` is already empty-insensitive,
    strict `normLevelEq` is not — the module-doc O1 note). -/
def normEqSemantic (a b : CNorm) : Bool :=
  let strip (m : CNorm) := m.toList.filter (fun (_, n) => !n.isEmpty)
  strip a == strip b

/-! ### Linearization (§3.2 — the O1 construction)

Mirrors `canon_univ.rs::linearize` — see its doc comment for the
inversion rules (self-strip with domination coverage, gate-order
recovery, marker consumption, emission order). -/

/-- Context-group accumulator. -/
structure CGroup where
  constant : UInt64 := 0
  atoms : Batteries.RBMap UInt64 UInt64 compare := .empty
  deriving Inhabited

/-- Is a `u_i = 0` fallout of `k` dominated under `ctx`? Some entry at
    a subset path must guarantee ≥ k whenever `ctx` is active. -/
def covered (norm : CNorm) (k : UInt64) (ctx : CPath) : Bool :=
  k == 0 || norm.toList.any fun (q, n) =>
    q.all (fun x => ctx.contains x)
      && (n.constant ≥ k || n.vars.any (fun v => v.2 + 1 ≥ k))

/-- Gate-nesting order for a context (outermost first): greedily the
    smallest remaining gate with a `(g, ·)` atom at some map path inside
    `chosen ∪ {g}` — its creation site / leak absorber; falls back to
    the smallest remaining for totality on unreachable inputs. -/
def gateOrder (norm : CNorm) (ctx : CPath) : List UInt64 := Id.run do
  let mut order : List UInt64 := []
  let mut remaining := ctx
  while h : !remaining.isEmpty do
    let pick := (remaining.find? fun g =>
      norm.toList.any fun (p, n) =>
        !p.isEmpty
          && p.all (fun x => x == g || order.contains x)
          && n.vars.any (fun v => v.1 == g)).getD
      (remaining.head (by simpa using h))
    order := order ++ [pick]
    remaining := remaining.filter (· != pick)
  return order

/-- Right-nested max chain of terms (in order), or `zero` when empty. -/
def maxChain (terms : List Univ) : Univ :=
  match terms.reverse with
  | [] => .zero
  | last :: rest => rest.foldl (fun acc t => .max t acc) last

/-- The canonical representative of a canonical form, by per-atom gate
    inversion (see the Rust twin's doc for the full construction). -/
def linearize (norm : CNorm) : Univ := Id.run do
  let cRoot := (norm.findD [] {}).constant
  -- Explode into per-atom items; self-strip under domination coverage.
  let mut groups : Batteries.RBMap CPath CGroup compare := .empty
  for (path, node) in norm.toList do
    if !path.isEmpty && node.constant > 0 then
      let g := groups.findD path {}
      groups := groups.insert path
        { g with constant := max g.constant node.constant }
    for (i, k) in node.vars do
      let ctx := path.filter (· != i)
      let home := if covered norm k ctx then ctx else path
      let g := groups.findD home {}
      let slot := max (g.atoms.findD i 0) k
      groups := groups.insert home { g with atoms := g.atoms.insert i slot }
  -- Marker consumption along each group's recovered gate order.
  let mut consumed : List (CPath × UInt64) := []
  for (ctx, g) in groups.toList do
    if ctx.isEmpty || (g.constant == 0 && g.atoms.isEmpty) then
      continue
    let order := gateOrder norm ctx
    for j in [0:order.length] do
      let p := order[j]!
      let mctx := (order.take j).mergeSort (· ≤ ·)
      if (groups.find? mctx).any (fun sg => sg.atoms.find? p == some 0) then
        consumed := (mctx, p) :: consumed
  -- Emission.
  let mut terms : List Univ := []
  let mut rootCAbsorbed := false
  if let some top := groups.find? [] then
    for (i, k) in top.atoms.toList do
      if k == 0 && consumed.contains ([], i) then
        continue
      terms := terms ++ [Univ.addSuccs (.var i) k.toNat]
      if k ≥ cRoot then
        rootCAbsorbed := true
  for (ctx, g) in groups.toList do
    if ctx.isEmpty then
      continue
    let mut atoms : List Univ := []
    for (i, k) in g.atoms.toList do
      if k == 0 && consumed.contains (ctx, i) then
        continue
      atoms := atoms ++ [Univ.addSuccs (.var i) k.toNat]
    if g.constant > 0 then
      atoms := atoms ++ [Univ.addSuccs .zero g.constant.toNat]
    if atoms.isEmpty then
      continue
    let body := maxChain atoms
    let order := gateOrder norm ctx
    let term := order.reverse.foldl (fun acc p => Univ.imax acc (.var p)) body
    terms := terms ++ [term]
  if cRoot > 0 && !rootCAbsorbed then
    terms := terms ++ [Univ.addSuccs .zero cRoot.toNat]
  return maxChain terms

end CanonUniv

/-- The canonical representative of `u`'s Géran class (canonicity
    §10.6). Total and deterministic; stage 2 applies it at the
    compile-time univ-intern boundary. -/
def canonUniv (u : Univ) : Univ :=
  CanonUniv.linearize (CanonUniv.normalize u)

end Ixon

end
end
