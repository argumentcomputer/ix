import Aiur.Circuit.Entry
import Aiur.LayoutComposition

namespace Aiur.Circuit

theorem mapM_ok_iff {f : α → Except ε β} {xs : List α} {ys : List β} :
    xs.mapM f = .ok ys ↔ List.Forall₂ (fun x y => f x = .ok y) xs ys := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
      cases hx : f x with
      | error e => simp [List.mapM_cons, hx, List.forall₂_cons_left_iff, bind, Except.bind]
      | ok y =>
          cases ht : xs.mapM f with
          | error e => simp [List.mapM_cons, hx, ht, List.forall₂_cons_left_iff, ← ih, bind, Except.bind]
          | ok rest => simp [List.mapM_cons, hx, ht, List.forall₂_cons_left_iff, ← ih, eq_comm, bind, Except.bind, pure, Except.pure]

theorem mapM_unit_succeeds {f : α → Except ε Unit} {xs : List α} :
    (∃ ys, xs.mapM f = .ok ys) ↔ ∀ x ∈ xs, f x = .ok () := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.forall_mem_cons, ← ih]
      cases hx : f x with
      | error e => simp [List.mapM_cons, hx, bind, Except.bind]
      | ok y =>
          cases y
          cases ht : xs.mapM f with
          | error e => simp [List.mapM_cons, hx, ht, bind, Except.bind]
          | ok rest => simp [List.mapM_cons, hx, ht, bind, Except.bind]

theorem zipIdx_forall {xs : List α} {p : α → Prop} :
    (∀ x ∈ xs.zipIdx, p x.1) ↔ ∀ x ∈ xs, p x := by
  simpa using (List.forall_mem_map (f := Prod.fst) (l := xs.zipIdx) (P := p)).symm

theorem zipIdx_forall_pair {xs : List α} {p : α → Prop} :
    (∀ a b, (a, b) ∈ xs.zipIdx → p a) ↔ ∀ a ∈ xs, p a := by
  simpa only [Prod.forall] using (zipIdx_forall (xs := xs) (p := p))

variable {F : Type} [Field F] [DecidableEq F]

theorem Chip.checkRow_iff {chip : Chip F} {rom : WireROM F} {row : Row F}
    {claims : RuleClaims (Message F)} :
    chip.checkRow rom row = .ok claims ↔
      chip.ValidRow rom row ∧ claims = (chip.receive row, chip.premises row) := by
  by_cases formed : chip.wellFormed = true
  · by_cases size : row.values.length = chip.numVars
    · simp only [Chip.checkRow, formed, Bool.not_true, Bool.false_eq_true, if_false,
        size, bne_self_eq_false]
      simp only [except_bind_ok]
      simp [mapM_unit_succeeds, Chip.ValidRow, formed, size, pure, Except.pure, bind, Except.bind,
        Satisfies, Scalar.Circuit.Satisfies, MemoryLookup.Valid, zipIdx_forall_pair, and_assoc]
      simp [eq_comm]
    · simp [Chip.checkRow, Chip.ValidRow, formed, size, bind, Except.bind, pure, Except.pure]
  · simp [Chip.checkRow, Chip.ValidRow, Bool.eq_false_iff.mpr formed, bind, Except.bind]

theorem System.inspectRow_iff {system : System F} {rom : WireROM F} {row : Row F}
    {claims : RuleClaims (Message F)} :
    system.inspectRow rom row = .ok claims ↔ ∃ chip,
      system.findChip? row.chip = some chip ∧ chip.ValidRow rom row ∧
        claims = (chip.receive row, chip.premises row) := by
  unfold System.inspectRow
  cases system.findChip? row.chip <;> simp [Chip.checkRow_iff]

theorem System.check_iff {system : System F} {rom : WireROM F} {root : Message F} {rows : List (Row F)} :
    system.check rom root rows = .ok () ↔ system.checkContext rom root = .ok () ∧
      ∃ rules, system.inspectRows rom rows = .ok rules ∧
        (Balance.required (fun c => decide (system.MapClaim c)) root rules).Perm (rules.map Prod.fst) := by
  have unit (rules : List (RuleClaims (Message F))) :
      (Balance.accumulator (fun c => decide (system.MapClaim c)) root
        (rules.map fun rule => (rule, 1))).isZero = true ↔
        (Balance.required (fun c => decide (system.MapClaim c)) root rules).Perm (rules.map Prod.fst) := by
    simpa [Balance.accumulator, Accumulator.requires, List.map_map,
      Function.comp_def] using
      (Accumulator.unit_balance_iff (Balance.required (fun c => decide (system.MapClaim c)) root rules)
        (rules.map Prod.fst))
  cases ctx : system.checkContext rom root with
  | error e => simp [System.check, ctx, bind, Except.bind]
  | ok u =>
      cases u
      cases inspected : system.inspectRows rom rows with
      | error e => simp [System.check, ctx, inspected, bind, Except.bind]
      | ok rules => simp [System.check, ctx, inspected, bind, Except.bind, pure, Except.pure, unit]

theorem System.checkMemo_iff {system : System F} {rom : WireROM F} {root : Message F}
    {rows : List (WeightedRow F)} :
    system.checkMemo rom root rows = .ok () ↔ system.checkContext rom root = .ok () ∧
      ∃ rules, system.inspectWeightedRows rom rows = .ok rules ∧
        (Balance.accumulator (fun c => decide (system.MapClaim c)) root rules).isZero = true := by
  cases ctx : system.checkContext rom root with
  | error e => simp [System.checkMemo, ctx, bind, Except.bind]
  | ok u =>
      cases u
      cases inspected : system.inspectWeightedRows rom rows with
      | error e => simp [System.checkMemo, ctx, inspected, bind, Except.bind]
      | ok rules => simp [System.checkMemo, ctx, inspected, bind, Except.bind, pure, Except.pure]

end Aiur.Circuit
