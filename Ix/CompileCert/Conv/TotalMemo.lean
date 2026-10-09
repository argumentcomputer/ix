import Ix.CompileCert.Conv.Core
import Ix.Compile.Image.TotalMemo

/-! Exact first-slice runtime/core bridge. These statements quantify over
arbitrary raw expressions and all internally certified total-cache states.
They do not establish the separate hereditary/fixed-fuel refinement. -/

namespace Ix.CompileCert.Conv.TotalMemoBridge

open Ix (Expr)
open Ix.Compile.Image

theorem range_spec (e : Expr) : TotalSpec.looseRangeP e = looseRangeP e := by
  induction e
  all_goals rw [TotalSpec.looseRangeP.eq_def, looseRangeP.eq_def]
  all_goals simp only [*]

theorem lift_spec (e : Expr) (n c : Nat) : TotalSpec.liftP e n c = liftP e n c := by
  induction e generalizing n c
  all_goals rw [TotalSpec.liftP.eq_def, liftP.eq_def, range_spec]
  all_goals split
  all_goals first | rfl | skip
  all_goals split
  all_goals first | rfl | simp only [*]

theorem lower_spec (e : Expr) (n c : Nat) : TotalSpec.lowerP e n c = lowerP e n c := by
  induction e generalizing n c
  all_goals rw [TotalSpec.lowerP.eq_def, lowerP.eq_def, range_spec]
  all_goals split
  all_goals first | rfl | skip
  all_goals split
  all_goals first | rfl | simp only [*]

theorem occurs_spec (e : Expr) (k : Nat) : TotalSpec.occursP e k = occursP e k := by
  induction e generalizing k
  all_goals rw [TotalSpec.occursP.eq_def, occursP.eq_def, range_spec]
  all_goals split
  all_goals first | rfl | simp only [*]

/-! These compiler-simplifier equations retain the original pure-core
declarations. Importing this bridge makes their exact implementations
available; the runtime itself imports no proof aggregator. -/

@[csimp] theorem looseRangeP_eq_memo : @looseRangeP = @TotalMemo.rangeFast := by
  funext e
  exact ((TotalMemo.rangeGo hash e {}).correct.trans (range_spec e)).symm

@[csimp] theorem liftP_eq_memo : @liftP = @TotalMemo.liftFast := by
  funext e n c
  exact ((TotalMemo.liftGo hash hash e n c {}).correct.trans (lift_spec e n c)).symm

@[csimp] theorem lowerP_eq_memo : @lowerP = @TotalMemo.lowerFast := by
  funext e n c
  exact ((TotalMemo.lowerGo hash hash e n c {}).correct.trans (lower_spec e n c)).symm

@[csimp] theorem occursP_eq_memo : @occursP = @TotalMemo.occursFast := by
  funext e k
  exact ((TotalMemo.occursGo hash hash e k {}).correct.trans (occurs_spec e k)).symm

def TotalTablesValid (st : DevState) : Prop :=
  TotalMemo.Valid TotalSpec.looseRangeP st.range ∧
  TotalMemo.Valid TotalMemo.liftAt st.lifted ∧
  TotalMemo.Valid TotalMemo.lowerAt st.lowered ∧
  TotalMemo.Valid TotalMemo.occursAt st.occurs

/-- This is established internally for every state, not an extra caller
premise. `insts` remains arbitrary and is not asserted valid here. -/
theorem tables_valid (st : DevState) : TotalTablesValid st :=
  ⟨TotalMemo.valid _ _, TotalMemo.valid _ _, TotalMemo.valid _ _, TotalMemo.valid _ _⟩

theorem tables_empty : TotalTablesValid ({} : DevState) := tables_valid {}

theorem tables_clear_insts (st : DevState) :
    TotalTablesValid { st with insts := {} } := tables_valid _

/-- Full Except and final-state equation, including all untouched fields. -/
theorem looseRange_run (e : Expr) (st : DevState) :
    (looseRange e).run st =
      .ok (looseRangeP e,
        { st with range := (TotalMemo.rangeGo hash e st.range).state }) := by
  change Except.ok ((TotalMemo.rangeGo hash e st.range).value, _) = _
  rw [TotalMemo.rangeGo_result, range_spec]

theorem liftM_run (e : Expr) (n c : Nat) (st : DevState) :
    (liftM e n c).run st =
      .ok (liftP e n c,
        { st with
          range := (TotalMemo.liftGo hash hash e n c ⟨st.range, st.lifted⟩).state.range
          lifted := (TotalMemo.liftGo hash hash e n c ⟨st.range, st.lifted⟩).state.values }) := by
  change Except.ok ((TotalMemo.liftGo hash hash e n c ⟨st.range, st.lifted⟩).value, _) = _
  rw [TotalMemo.liftGo_result, lift_spec]

theorem lowerM_run (e : Expr) (n c : Nat) (st : DevState) :
    (lowerM e n c).run st =
      .ok (lowerP e n c,
        { st with
          range := (TotalMemo.lowerGo hash hash e n c ⟨st.range, st.lowered⟩).state.range
          lowered := (TotalMemo.lowerGo hash hash e n c ⟨st.range, st.lowered⟩).state.values }) := by
  change Except.ok ((TotalMemo.lowerGo hash hash e n c ⟨st.range, st.lowered⟩).value, _) = _
  rw [TotalMemo.lowerGo_result, lower_spec]

theorem occursM_run (e : Expr) (k : Nat) (st : DevState) :
    (occursM e k).run st =
      .ok (occursP e k,
        { st with
          range := (TotalMemo.occursGo hash hash e k ⟨st.range, st.occurs⟩).state.range
          occurs := (TotalMemo.occursGo hash hash e k ⟨st.range, st.occurs⟩).state.values }) := by
  change Except.ok ((TotalMemo.occursGo hash hash e k ⟨st.range, st.occurs⟩).value, _) = _
  rw [TotalMemo.occursGo_result, occurs_spec]

/-- A complete frame: the hereditary table is never modified by these
four total helpers, even when its contents are arbitrary. -/
theorem looseRange_insts (e : Expr) (st : DevState) (value : Nat) (out : DevState)
    (run : (looseRange e).run st = .ok (value, out)) : out.insts = st.insts := by
  rw [looseRange_run] at run
  cases run
  rfl

theorem liftM_frame (e : Expr) (n c : Nat) (st : DevState) (value : Expr) (out : DevState)
    (run : (liftM e n c).run st = .ok (value, out)) :
    out.lowered = st.lowered ∧ out.occurs = st.occurs ∧ out.insts = st.insts := by
  rw [liftM_run] at run
  cases run
  exact ⟨rfl, rfl, rfl⟩

theorem lowerM_frame (e : Expr) (n c : Nat) (st : DevState) (value : Expr) (out : DevState)
    (run : (lowerM e n c).run st = .ok (value, out)) :
    out.lifted = st.lifted ∧ out.occurs = st.occurs ∧ out.insts = st.insts := by
  rw [lowerM_run] at run
  cases run
  exact ⟨rfl, rfl, rfl⟩

theorem occursM_frame (e : Expr) (k : Nat) (st : DevState) (value : Bool) (out : DevState)
    (run : (occursM e k).run st = .ok (value, out)) :
    out.lifted = st.lifted ∧ out.lowered = st.lowered ∧ out.insts = st.insts := by
  rw [occursM_run] at run
  cases run
  exact ⟨rfl, rfl, rfl⟩

end Ix.CompileCert.Conv.TotalMemoBridge
