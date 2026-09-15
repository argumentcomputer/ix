import Compilatrix.Aiur.OracleEval.Local

namespace Compilatrix.Aiur.OracleEval

open _root_.Aiur.Bytecode (Toplevel)

/-- Concrete bytecode facts for one provider. Memory and gadget providers
are leaves in this projection. Heap agreement is supplied by trace coherence. -/
def RowFact (toplevel : Toplevel) (oracle : AdviceOracle) (row : Row) : Prop :=
  match row.provides with
  | .function function inputs outputs =>
      ∃ advice, Body toplevel function inputs outputs row.demands advice ∧ AdviceAllowed oracle advice
  | .memory bucket _ values => values.length = bucket ∧ row.demands = []
  | .gadget channel payload => Gadget.check channel payload = true ∧ row.demands = []

def Rows (toplevel : Toplevel) (oracle : AdviceOracle) (trace : Trace) : Prop :=
  ∀ id : trace.RowId, (trace.row id).active = true →
    (trace.row id).multiplicity ≠ 0 → RowFact toplevel oracle (trace.row id)

def checkRow (toplevel : Toplevel) (oracle : AdviceOracle) (limits : Limits)
    (replies : List Values) (row : Row) : Bool :=
  if row.active = true ∧ row.multiplicity ≠ 0 then
    match row.provides with
    | .function function inputs outputs =>
        match runFunction toplevel limits function inputs replies with
        | .error _ => false
        | .ok result =>
            decide (result.outputs = outputs ∧ result.demands = row.demands) &&
            result.advice.all (fun observation => oracle observation.request observation.answer)
    | .memory bucket _ values =>
        decide (values.length = bucket ∧ row.demands = [] ∧ replies = [])
    | .gadget channel payload =>
        Gadget.check channel payload && decide (row.demands = [] ∧ replies = [])
  else true

theorem checkRow_sound (toplevel : Toplevel) (oracle : AdviceOracle) (limits : Limits)
    (replies : List Values) (row : Row) (checked : checkRow toplevel oracle limits replies row = true)
    (active : row.active = true) (nonzero : row.multiplicity ≠ 0) : RowFact toplevel oracle row := by
  unfold checkRow at checked
  rw [if_pos ⟨active, nonzero⟩] at checked
  cases provided : row.provides with
  | function function inputs outputs =>
      simp only [provided] at checked
      cases replay : runFunction toplevel limits function inputs replies with
      | error error => simp [replay] at checked
      | ok result =>
          rw [replay] at checked
          have parts := Bool.and_eq_true_iff.mp checked
          have same := of_decide_eq_true parts.1
          simp only [RowFact, provided]
          refine ⟨result.advice, ⟨limits, replies, result, replay, same.1, same.2, rfl⟩, ?_⟩
          exact List.all_eq_true.mp parts.2
  | memory bucket pointer values =>
      simp only [provided] at checked
      have facts := of_decide_eq_true checked
      simp only [RowFact, provided]
      exact ⟨facts.1, facts.2.1⟩
  | gadget channel payload =>
      simp only [provided] at checked
      have parts := Bool.and_eq_true_iff.mp checked
      simp only [RowFact, provided]
      exact ⟨parts.1, (of_decide_eq_true parts.2).1⟩

def checkRows (toplevel : Toplevel) (oracle : AdviceOracle) (trace : Trace) (limits : Limits)
    (replies : Array (List Values)) : Bool :=
  decide (replies.size = trace.rows.length) &&
    (List.finRange trace.rows.length).all (fun id =>
      checkRow toplevel oracle limits (replies[id.val]?.getD []) (trace.row id))

theorem checkRows_sound (toplevel : Toplevel) (oracle : AdviceOracle) (trace : Trace)
    (limits : Limits) (replies : Array (List Values))
    (checked : checkRows toplevel oracle trace limits replies = true) : Rows toplevel oracle trace := by
  have every := (Bool.and_eq_true_iff.mp checked).2
  intro id active nonzero
  exact checkRow_sound toplevel oracle limits _ _
    (List.all_eq_true.mp every id (by simp)) active nonzero

structure CheckedRows (toplevel : Toplevel) (oracle : AdviceOracle) (trace : Trace) : Type where
  rows : Rows toplevel oracle trace

def validateRows (toplevel : Toplevel) (oracle : AdviceOracle) (trace : Trace) (limits : Limits)
    (replies : Array (List Values)) : Except Error (CheckedRows toplevel oracle trace) :=
  if checked : checkRows toplevel oracle trace limits replies = true then
    .ok ⟨checkRows_sound toplevel oracle trace limits replies checked⟩
  else if replies.size != trace.rows.length then .error .rowWitnessCount
  else .error .rowsRejected

end Compilatrix.Aiur.OracleEval
