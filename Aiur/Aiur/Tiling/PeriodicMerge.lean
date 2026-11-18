import Aiur.Tiling.Basic
import Aiur.Tiling.Poly

/-!
# Merged lookups and unrolled bodies

Two circuit transformations that the v2 lowering applies before tiling:

* **Merging.** Lookups with identical argument polynomials are one lookup
  whose multiplicity is the sum of theirs (LogUp is additive in the
  multiplicity of a tuple), and lookups whose multiplicity polynomial is zero
  are dropped. `Circuit.mergeBy C groups` lists one lookup per group of
  original lookup indices; `Circuit.checkMerge` decides that the groups are
  disjoint, cover every lookup of nonzero multiplicity and have identical
  arguments, and `rowLedger_mergeBy` shows that the row ledger is unchanged.
* **Unrolling.** `Unroll.circuit` places `n` copies (*bodies*) of a circuit
  side by side. Body `b` reads its own block of columns, except columns fixed
  to constants and columns *aliased* to an argument of a lookup of body
  `b − 1`; some lookups of each body are dropped.
-/

namespace Aiur.Tiling

open Aiur.Scalar.Circuit (ArithExpr Var)

variable {F : Type}

/-- Replace every variable `c` by `σ c`. -/
def substVars (σ : Var → ArithExpr F) : ArithExpr F → ArithExpr F
  | .const k => .const k
  | .var c => σ c
  | .add x y => .add (substVars σ x) (substVars σ y)
  | .sub x y => .sub (substVars σ x) (substVars σ y)
  | .mul x y => .mul (substVars σ x) (substVars σ y)

theorem denote_substVars [Field F] (σ : Var → ArithExpr F) (a : Var → F) :
    ∀ e : ArithExpr F, (substVars σ e).denote a = e.denote fun c => (σ c).denote a
  | .const _ => rfl
  | .var _ => rfl
  | .add x y => by simp [substVars, ArithExpr.denote, denote_substVars σ a x, denote_substVars σ a y]
  | .sub x y => by simp [substVars, ArithExpr.denote, denote_substVars σ a x, denote_substVars σ a y]
  | .mul x y => by simp [substVars, ArithExpr.denote, denote_substVars σ a x, denote_substVars σ a y]

/-! ## Merging -/

section Merge

variable [Zero F]

def Circuit.lookupAt (C : Circuit F) (j : Nat) : Lookup F := C.lookups.getD j ⟨.const 0, []⟩

/-- The sum of the multiplicities of lookups `js`. -/
def Circuit.multSum (C : Circuit F) : List Nat → ArithExpr F
  | [] => .const 0
  | [j] => (C.lookupAt j).multiplicity
  | j :: js => .add (C.lookupAt j).multiplicity (C.multSum js)

/-- One lookup per group: the arguments of its first member and the sum of
its members' multiplicities. -/
def Circuit.mergeBy (C : Circuit F) (groups : List (List Nat)) : Circuit F :=
  { C with lookups := groups.map fun g => ⟨C.multSum g, (C.lookupAt (g.headD 0)).args⟩ }

end Merge

section CheckMerge

variable [CommRing F] [DecidableEq F]

def argsIdentical (xs ys : List (ArithExpr F)) : Bool :=
  xs.length == ys.length && (xs.zip ys).all fun (x, y) => Poly.Identical (Poly.ofExpr x) (Poly.ofExpr y)

/-- The groups are nonempty and disjoint, every lookup outside them has a zero
multiplicity polynomial, and the members of a group have identical arguments. -/
def Circuit.checkMerge (C : Circuit F) (groups : List (List Nat)) : Bool :=
  let members := groups.flatten
  decide members.Nodup && members.all (· < C.lookups.length) &&
    groups.all (fun g => !g.isEmpty && g.all fun j =>
      argsIdentical (C.lookupAt j).args (C.lookupAt (g.headD 0)).args) &&
    (List.range C.lookups.length).all fun j =>
      members.contains j || (Poly.norm (Poly.ofExpr (C.lookupAt j).multiplicity)).isEmpty

end CheckMerge

/-! ## Unrolling -/

/-- Body `b`: columns fixed to constants, columns `(col, lookup, arg)` equal
to argument `arg` of lookup `lookup` of the previous body, and dropped
lookups. -/
structure Body (F : Type) where
  subst : List (Nat × F)
  aliases : List (Nat × Nat × Nat)
  drop : List Nat
  deriving Repr

structure Unroll (F : Type) where
  width : Nat
  bodies : List (Body F)
  deriving Repr

section Unroll

variable [Zero F]

def Unroll.body (U : Unroll F) (b : Nat) : Body F := U.bodies.getD b ⟨[], [], []⟩

/-- The expression of column `c` of body `b` over the unrolled columns. -/
def Unroll.sigma (U : Unroll F) (C : Circuit F) : Nat → Var → ArithExpr F
  | 0, c =>
      match (U.body 0).subst.lookup c with
      | some k => .const k
      | none => .var c
  | b + 1, c =>
      match (U.body (b + 1)).subst.lookup c with
      | some k => .const k
      | none =>
          match (U.body (b + 1)).aliases.lookup c with
          | some (l, a) => substVars (U.sigma C b) ((C.lookupAt l).args.getD a (.const 0))
          | none => .var ((b + 1) * U.width + c)

def Unroll.lookups (U : Unroll F) (C : Circuit F) (b : Nat) : List (Lookup F) :=
  C.lookups.zipIdx.filterMap fun (l, j) =>
    if j ∈ (U.body b).drop then none
    else some ⟨substVars (U.sigma C b) l.multiplicity, l.args.map (substVars (U.sigma C b))⟩

def Unroll.circuit (U : Unroll F) (C : Circuit F) : Circuit F where
  width := U.bodies.length * U.width
  constraints := (List.range U.bodies.length).flatMap fun b => C.constraints.map (substVars (U.sigma C b))
  lookups := (List.range U.bodies.length).flatMap (U.lookups C)

end Unroll

end Aiur.Tiling

namespace Aiur.Tiling

open Aiur.Scalar.Circuit (ArithExpr Var)

section MergeSound

variable {F : Type} [Field F] [DecidableEq F]

theorem lookupAt_eq {C : Circuit F} {j : Nat} (hj : j < C.lookups.length) : C.lookupAt j = C.lookups[j] := by
  simp [Circuit.lookupAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem argsIdentical_tuple {xs ys : List (ArithExpr F)} (h : argsIdentical xs ys = true) (a : Var → F) :
    xs.map (·.denote a) = ys.map (·.denote a) := by
  simp only [argsIdentical, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨len, same⟩ := h
  apply List.ext_getElem (by simp [len])
  intro n h1 h2
  simp only [List.getElem_map]
  have hx : n < xs.length := by simpa using h1
  have hy : n < ys.length := by simpa using h2
  have mem : (xs[n], ys[n]) ∈ xs.zip ys := by
    rw [← List.getElem_zip (h := by simp [hx, hy])]
    exact List.getElem_mem _
  have := Poly.Identical.denote (a := a) (same _ mem)
  rwa [Poly.denote_ofExpr, Poly.denote_ofExpr] at this

/-- A group whose members all have tuple `t` contributes `t` with the sum of
their multiplicities. -/
theorem single_multSum (C : Circuit F) (a : Var → F) (t : List F) :
    ∀ (g : List Nat), (∀ j ∈ g, (C.lookupAt j).tuple a = t) →
      Finsupp.single t ((C.multSum g).denote a) = (g.map fun j => (C.lookupAt j).entry a).sum
  | [], _ => by simp [Circuit.multSum, ArithExpr.denote]
  | [j], h => by simp [Circuit.multSum, Lookup.entry, h j (by simp)]
  | j :: j' :: js, h => by
      rw [show C.multSum (j :: j' :: js) = .add (C.lookupAt j).multiplicity (C.multSum (j' :: js)) from rfl,
        ArithExpr.denote, Finsupp.single_add, single_multSum C a t (j' :: js) (fun i hi => h i (by simp_all)),
        List.map_cons, List.sum_cons]
      simp [Lookup.entry, h j (by simp)]

/-- **Merging is sound.** Accepted merge groups leave the row ledger unchanged. -/
theorem rowLedger_mergeBy {C : Circuit F} {groups : List (List Nat)} (ok : C.checkMerge groups = true)
    (a : Var → F) : (C.mergeBy groups).rowLedger a = C.rowLedger a := by
  simp only [Circuit.checkMerge, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    List.contains_iff_mem, Bool.not_eq_true', List.isEmpty_eq_false_iff] at ok
  obtain ⟨⟨⟨nodup, lt⟩, shaped⟩, zero⟩ := ok
  set members := groups.flatten
  have entry : ∀ j, (C.lookupAt j).entry a = (fun j => (C.lookupAt j).entry a) j := fun _ => rfl
  have perGroup : ∀ g ∈ groups, Lookup.entry a ⟨C.multSum g, (C.lookupAt (g.headD 0)).args⟩ =
      (g.map fun j => (C.lookupAt j).entry a).sum := by
    intro g hg
    rw [Lookup.entry]
    apply single_multSum C a
    intro j hj
    exact argsIdentical_tuple ((shaped g hg).2 j hj) a
  have merged : (C.mergeBy groups).rowLedger a = (members.map fun j => (C.lookupAt j).entry a).sum := by
    simp only [Circuit.rowLedger, Circuit.mergeBy, List.map_map, members, List.map_flatten, List.sum_flatten]
    congr 1
    apply List.map_congr_left
    intro g hg
    exact perGroup g hg
  have whole : C.rowLedger a = ((List.range C.lookups.length).map fun j => (C.lookupAt j).entry a).sum := by
    simp only [Circuit.rowLedger]
    congr 1
    apply List.ext_getElem (by simp)
    intro n h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [lookupAt_eq (by simpa using h1)]
  have perm : List.Perm (List.range C.lookups.length)
      ((List.range C.lookups.length).filter (· ∈ members) ++
        (List.range C.lookups.length).filter (fun j => !decide (j ∈ members))) :=
    (List.filter_append_perm _ _).symm
  have permMembers : List.Perm ((List.range C.lookups.length).filter (· ∈ members)) members := by
    apply (List.perm_ext_iff_of_nodup ((List.nodup_range).filter _) nodup).mpr
    intro j
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨lt j h, h⟩⟩
  rw [merged, whole, (perm.map _).sum_eq, List.map_append, List.sum_append, (permMembers.map _).sum_eq]
  suffices hz : (((List.range C.lookups.length).filter (fun j => !decide (j ∈ members))).map
      (fun j => (C.lookupAt j).entry a)).sum = 0 by rw [hz, add_zero]
  apply List.sum_eq_zero
  intro e he
  simp only [List.mem_map, List.mem_filter, List.mem_range, Bool.not_eq_true', decide_eq_false_iff_not] at he
  obtain ⟨j, ⟨hj, nj⟩, rfl⟩ := he
  rcases zero j (List.mem_range.mpr hj) with h | h
  · exact absurd h nj
  · have := Poly.denote_norm a (Poly.ofExpr (C.lookupAt j).multiplicity)
    rw [List.isEmpty_iff.mp h, Poly.denote_nil, Poly.denote_ofExpr] at this
    simp [Lookup.entry, ← this]

/-- Merging keeps the constraints. -/
theorem mergeBy_constraints (C : Circuit F) (groups : List (List Nat)) :
    (C.mergeBy groups).constraints = C.constraints := rfl

end MergeSound

end Aiur.Tiling
