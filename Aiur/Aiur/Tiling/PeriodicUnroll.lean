import Aiur.Tiling.PeriodicMerge
import Aiur.Tiling.Refinement

/-!
# Unrolled circuits refine the circuit they unroll

`Unroll.circuit U C` places `n` bodies of `C` side by side. Body `b` reads
column `c` as `U.sigma C b c`, so a row `w` of the unrolled circuit determines
`n` rows `U.row C b w` of `C`. `Unroll.check` decides the shape of a
*self-call chain*:

* body 0 drops only the self-call `s` (some lookup other than the receive 0);
  every later body drops the self-call and the receive;
* the receive of body `b + 1` and the self-call of body `b` have identical
  arguments and multiplicities summing to the zero polynomial;
* the self-call of the last body has the zero multiplicity polynomial.

Then every body row satisfies `C` (`Unroll.holds`), and the unrolled row's
ledger is the sum of the body rows' ledgers (`Unroll.rowLedger_circuit`): the
dropped lookups cancel in pairs along the chain.

The multiplicity condition is what fixes the receive multiplicity of bodies
`b > 0`: with a receive `push(−X_m, …)` and a self-call multiplicity fixed to
1 in body `b`, the receive multiplicity column `m` must be fixed to 1 in
body `b + 1`.
-/

namespace Aiur.Tiling

open Aiur.Scalar.Circuit (ArithExpr Var Satisfies)

variable {F : Type}

section Check

variable [Field F] [DecidableEq F]

/-- Column `c` of body `b` over the unrolled row. -/
def Unroll.row (U : Unroll F) (C : Circuit F) (b : Nat) (w : Var → F) : Var → F :=
  fun c => (U.sigma C b c).denote w

def Unroll.selfCall (U : Unroll F) : Nat := (U.body 0).drop.headD 0

def zeroPoly (e : ArithExpr F) : Bool := (Poly.norm (Poly.ofExpr e)).isEmpty

/-- The dropped lookups form a self-call chain (module docstring). -/
def Unroll.check (U : Unroll F) (C : Circuit F) : Bool :=
  let n := U.bodies.length
  let s := U.selfCall
  let sub (b : Nat) (e : ArithExpr F) := substVars (U.sigma C b) e
  0 < n && 0 < s && s < C.lookups.length &&
    (List.range n).all (fun b => (U.body b).drop == if b = 0 then [s] else [s, 0]) &&
    (List.range (n - 1)).all (fun b =>
      argsIdentical ((C.lookupAt 0).args.map (sub (b + 1))) ((C.lookupAt s).args.map (sub b)) &&
        zeroPoly (.add (sub (b + 1) (C.lookupAt 0).multiplicity) (sub b (C.lookupAt s).multiplicity))) &&
    zeroPoly (sub (n - 1) (C.lookupAt s).multiplicity)

end Check

section Sound

variable [Field F] [DecidableEq F]

theorem zeroPoly_denote {e : ArithExpr F} (h : zeroPoly e = true) (a : Var → F) : e.denote a = 0 := by
  have := Poly.denote_norm a (Poly.ofExpr e)
  rw [List.isEmpty_iff.mp h, Poly.denote_nil, Poly.denote_ofExpr] at this
  exact this.symm

theorem Unroll.denote_sub (U : Unroll F) (C : Circuit F) (b : Nat) (w : Var → F) (e : ArithExpr F) :
    (substVars (U.sigma C b) e).denote w = e.denote (U.row C b w) :=
  denote_substVars _ _ e

/-- **Constraints.** Every body row of an unrolled row satisfies `C`. -/
theorem Unroll.holds (U : Unroll F) (C : Circuit F) {w : Var → F} (h : (U.circuit C).Holds w)
    {b : Nat} (hb : b < U.bodies.length) : C.Holds (U.row C b w) := by
  intro c hc
  have := h (substVars (U.sigma C b) c)
    (List.mem_flatMap.mpr ⟨b, List.mem_range.mpr hb, List.mem_map.mpr ⟨c, hc, rfl⟩⟩)
  rwa [Unroll.denote_sub] at this

theorem sum_filterMap_map {α β M : Type} [AddCommMonoid M] (xs : List α) (φ : α → Option β) (h : β → M) :
    ((xs.filterMap φ).map h).sum = (xs.map fun x => ((φ x).map h).getD 0).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.filterMap_cons]
      cases hx : φ x <;> simp [ih, hx]

theorem sum_zipIdx {α M : Type} [AddCommMonoid M] (L : List α) (d : α) (g : α × Nat → M) :
    (L.zipIdx.map g).sum = ((List.range L.length).map fun j => g (L.getD j d, j)).sum := by
  congr 1
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp only [List.getElem_map, List.getElem_zipIdx, List.getElem_range]
  have hn : n < L.length := by simpa using h1
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]

/-- Removing the indices `D` from a sum over `range n`. -/
theorem sum_range_drop {M : Type} [AddCommGroup M] (n : Nat) (f : Nat → M) (D : List Nat) (nd : D.Nodup)
    (lt : ∀ j ∈ D, j < n) :
    ((List.range n).map fun j => if j ∈ D then 0 else f j).sum = ((List.range n).map f).sum - (D.map f).sum := by
  have split : ∀ j, f j = (if j ∈ D then 0 else f j) + (if j ∈ D.toFinset then f j else 0) := by
    intro j; by_cases h : j ∈ D <;> simp [h]
  rw [eq_sub_iff_add_eq, ← System.finset_sum_range_list, ← System.finset_sum_range_list,
    ← List.sum_toFinset f nd]
  conv_rhs => rw [Finset.sum_congr rfl (fun j _ => split j)]
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.inter_eq_right.mpr]
  intro j hj
  simpa using lt j (List.mem_toFinset.mp hj)

/-- Body `b`'s lookups of the unrolled circuit, as a sum over `C`'s lookups
outside the dropped ones. -/
theorem Unroll.lookups_ledger (U : Unroll F) (C : Circuit F) (b : Nat) (w : Var → F) :
    ((U.lookups C b).map (·.entry w)).sum =
      ((List.range C.lookups.length).map fun j =>
        if j ∈ (U.body b).drop then 0 else (C.lookupAt j).entry (U.row C b w)).sum := by
  rw [Unroll.lookups, sum_filterMap_map, sum_zipIdx _ ⟨.const 0, []⟩]
  congr 1
  apply List.map_congr_left
  intro j _
  by_cases hj : j ∈ (U.body b).drop
  · simp [hj]
  · simp only [hj, if_false, Option.map_some, Option.getD_some, Lookup.entry, Lookup.tuple, List.map_map,
      Function.comp_def, Unroll.denote_sub]
    rfl

theorem Circuit.rowLedger_range (C : Circuit F) (a : Var → F) :
    C.rowLedger a = ((List.range C.lookups.length).map fun j => (C.lookupAt j).entry a).sum := by
  simp only [Circuit.rowLedger]
  congr 1
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [lookupAt_eq (by simpa using h1)]

theorem entry_pair {l l' : Lookup F} {a a' : Var → F} (same : l.tuple a = l'.tuple a')
    (sum : l.multiplicity.denote a + l'.multiplicity.denote a' = 0) : l.entry a + l'.entry a' = 0 := by
  rw [Lookup.entry, Lookup.entry, same, ← Finsupp.single_add, sum, Finsupp.single_zero]

/-- **Ledger.** Under `Unroll.check`, the unrolled row's ledger is the sum of
the body rows' ledgers. -/
theorem Unroll.rowLedger_circuit {U : Unroll F} {C : Circuit F} (ok : U.check C = true) (w : Var → F) :
    (U.circuit C).rowLedger w = ((List.range U.bodies.length).map fun b => C.rowLedger (U.row C b w)).sum := by
  simp only [Unroll.check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    beq_iff_eq] at ok
  obtain ⟨⟨⟨⟨⟨npos, spos⟩, slt⟩, drops⟩, pairs⟩, lastZ⟩ := ok
  set n := U.bodies.length
  set s := U.selfCall
  set e : Nat → Nat → Ledger F := fun b j => (C.lookupAt j).entry (U.row C b w)
  have body : ∀ b < n, ((U.lookups C b).map (·.entry w)).sum =
      C.rowLedger (U.row C b w) - ((U.body b).drop.map (e b)).sum := by
    intro b hb
    rw [Unroll.lookups_ledger, Circuit.rowLedger_range]
    apply sum_range_drop
    · rw [drops b hb]; split <;> simp; omega
    · rw [drops b hb]; split <;> simp <;> omega
  have dropped : ((List.range n).map fun b => ((U.body b).drop.map (e b)).sum).sum = 0 := by
    have tele : ∀ m, m + 1 ≤ n →
        ((List.range (m + 1)).map fun b => ((U.body b).drop.map (e b)).sum).sum = e m s := by
      intro m hm
      induction m with
      | zero => simp [drops 0 (by omega), e]
      | succ m ih =>
          rw [List.range_succ, List.map_append, List.sum_append, ih (by omega)]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          rw [drops (m + 1) (by omega)]
          simp only [Nat.add_one_ne_zero, if_false, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
            add_zero]
          obtain ⟨args, mult⟩ := pairs m (by omega)
          have pair : e (m + 1) 0 + e m s = 0 := by
            apply entry_pair
            · have := argsIdentical_tuple args w
              simpa [Lookup.tuple, List.map_map, Function.comp_def, Unroll.denote_sub] using this
            · have := zeroPoly_denote mult w
              simpa [ArithExpr.denote, Unroll.denote_sub] using this
          rw [add_comm (e (m + 1) s), ← add_assoc, add_comm (e m s), pair, zero_add]
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [hm, tele m (by omega)]
    have := zeroPoly_denote lastZ w
    rw [hm, Nat.add_sub_cancel, Unroll.denote_sub] at this
    simp [e, Lookup.entry, this]
  rw [Circuit.rowLedger, Unroll.circuit, System.sum_map_flatMap]
  rw [← sub_zero ((List.range n).map fun b => C.rowLedger (U.row C b w)).sum, ← dropped, eq_sub_iff_add_eq,
    ← List.sum_map_add]
  congr 1
  apply List.map_congr_left
  intro b hb
  rw [body b (List.mem_range.mp hb), sub_add_cancel]

end Sound

end Aiur.Tiling
