import IxCC.Aiur.CounterAnalysis.Effects

namespace IxCC.Aiur.CounterAnalysis

open _root_.Aiur (G)
open OracleEval (Values State Error)

theorem read_spec {state : State} {index : Nat} {value : G}
    (success : OracleEval.read state index = .ok value) : state.values[index]? = some value := by
  unfold OracleEval.read at success
  split at success
  next value read => cases success; exact read
  next read => cases success

theorem map_reads {state : State} {indices : List Nat} {inputs : Values}
    (success : indices.mapM (OracleEval.read state) = .ok inputs) :
    ReadList state.values indices inputs := by
  induction indices generalizing inputs with
  | nil => cases success; exact .nil
  | cons index rest ih =>
      simp only [List.mapM_cons] at success
      obtain ⟨value, read, success⟩ := bind_success success
      obtain ⟨values, reads, success⟩ := bind_success success
      cases success
      exact .cons (read_spec read) (ih reads)

theorem readMany_spec {maxValues : Nat} {state : State} {indices : Array Nat} {inputs : Values}
    (success : OracleEval.readMany maxValues state indices = .ok inputs) :
    Reads state.values indices inputs := by
  unfold OracleEval.readMany at success
  split at success
  · cases success
  · exact map_reads success

theorem appendValues_spec {maxValues : Nat} {before after : State} {outputs : Values}
    (success : OracleEval.appendValues maxValues before outputs = .ok after) :
    after.values = before.values ++ outputs.toArray ∧ after.demandsRev = before.demandsRev := by
  unfold OracleEval.appendValues at success
  split at success
  · cases success
  · cases success; exact ⟨rfl, rfl⟩

theorem takeReply_spec {before after : State} {count : Nat} {outputs : Values}
    (success : OracleEval.takeReply before count = .ok (outputs, after)) :
    outputs.length = count ∧ after.values = before.values ∧ after.demandsRev = before.demandsRev := by
  unfold OracleEval.takeReply at success
  split at success
  · cases success
  · split at success
    next equal => cases success; exact ⟨equal, rfl, rfl⟩
    next different => cases success

theorem chargeFields_spec {before after : State} {count : Nat}
    (success : OracleEval.chargeFields before count = .ok after) :
    after.values = before.values ∧ after.demandsRev = before.demandsRev := by
  unfold OracleEval.chargeFields at success
  split at success
  · cases success
  · cases success; exact ⟨rfl, rfl⟩

theorem demand_spec {before after : State} {message : Message}
    (success : OracleEval.demand before message = .ok after) :
    after.values = before.values ∧ after.demandsRev = message :: before.demandsRev := by
  obtain ⟨charged, charge, success⟩ := bind_success success
  have ⟨values, demands⟩ := chargeFields_spec charge
  cases success
  exact ⟨values, congrArg (message :: ·) demands⟩

theorem recordAdvice_spec {before after : State} {request : OracleEval.AdviceRequest} {answer : Values}
    (success : OracleEval.recordAdvice before request answer = .ok after) :
    after.values = before.values ∧ after.demandsRev = before.demandsRev := by
  obtain ⟨charged, charge, success⟩ := bind_success success
  have effect := chargeFields_spec charge
  cases success
  exact effect

theorem hint_spec {maxValues size : Nat} {before after : State} {request : OracleEval.AdviceRequest}
    (success : OracleEval.hint maxValues before request size = .ok after) :
    ∃ outputs : Values, outputs.length = size ∧ after.values = before.values ++ outputs.toArray ∧
      after.demandsRev = before.demandsRev := by
  obtain ⟨⟨outputs, replied⟩, reply, success⟩ := bind_success success
  obtain ⟨advised, advice, success⟩ := bind_success success
  have ⟨arity, values₁, demands₁⟩ := takeReply_spec reply
  have ⟨values₂, demands₂⟩ := recordAdvice_spec advice
  have ⟨values₃, demands₃⟩ := appendValues_spec success
  exact ⟨outputs, arity, by rw [values₃, values₂, values₁], by rw [demands₃, demands₂, demands₁]⟩

theorem fieldBinary_spec {maxValues left right : Nat} {before after : State} {operation : G → G → G}
    (success : OracleEval.fieldBinary maxValues before left right operation = .ok after) :
    ∃ a b, before.values[left]? = some a ∧ before.values[right]? = some b ∧
      after.values = before.values ++ #[operation a b] ∧ after.demandsRev = before.demandsRev := by
  obtain ⟨a, leftRead, success⟩ := bind_success success
  obtain ⟨b, rightRead, success⟩ := bind_success success
  have ⟨values, demands⟩ := appendValues_spec success
  exact ⟨a, b, read_spec leftRead, read_spec rightRead, values, demands⟩

theorem gadgetStep_spec {maxValues : Nat} {before after : State} {gadget : OracleEval.Gadget} {inputs : Values}
    (success : OracleEval.gadgetStep maxValues before gadget inputs = .ok after) :
    ∃ outputs : Values, outputs.length = gadget.outputSize ∧ after.values = before.values ++ outputs.toArray ∧
      calls after.demandsRev = calls before.demandsRev := by
  obtain ⟨⟨outputs, replied⟩, reply, success⟩ := bind_success success
  obtain ⟨demanded, demand, success⟩ := bind_success success
  have ⟨arity, values₁, demands₁⟩ := takeReply_spec reply
  have ⟨values₂, demands₂⟩ := demand_spec demand
  have ⟨values₃, demands₃⟩ := appendValues_spec success
  refine ⟨outputs, arity, by rw [values₃, values₂, values₁], ?_⟩
  rw [demands₃, demands₂, demands₁]
  rfl

theorem unaryGadget_spec {maxValues index : Nat} {before after : State} {gadget : OracleEval.Gadget}
    (success : OracleEval.unaryGadget maxValues before gadget index = .ok after) :
    ∃ outputs : Values, outputs.length = gadget.outputSize ∧ after.values = before.values ++ outputs.toArray ∧
      calls after.demandsRev = calls before.demandsRev := by
  obtain ⟨_, _, success⟩ := bind_success success
  exact gadgetStep_spec success

theorem binaryGadget_spec {maxValues left right : Nat} {before after : State} {gadget : OracleEval.Gadget}
    (success : OracleEval.binaryGadget maxValues before gadget left right = .ok after) :
    ∃ outputs : Values, outputs.length = gadget.outputSize ∧ after.values = before.values ++ outputs.toArray ∧
      calls after.demandsRev = calls before.demandsRev := by
  obtain ⟨_, _, success⟩ := bind_success success
  obtain ⟨_, _, success⟩ := bind_success success
  exact gadgetStep_spec success

theorem u32Hint_spec {maxValues : Nat} {before after : State} {request : OracleEval.AdviceRequest} {sum : G}
    (success : OracleEval.u32Hint maxValues before request sum = .ok after) :
    ∃ outputs : Values, outputs.length = 5 ∧ after.values = before.values ++ outputs.toArray ∧
      after.demandsRev = before.demandsRev := by
  obtain ⟨⟨bytes, replied⟩, reply, success⟩ := bind_success success
  obtain ⟨advised, advice, success⟩ := bind_success success
  have ⟨arity, values₁, demands₁⟩ := takeReply_spec reply
  have ⟨values₂, demands₂⟩ := recordAdvice_spec advice
  have ⟨values₃, demands₃⟩ := appendValues_spec success
  refine ⟨_, ?_, by rw [values₃, values₂, values₁], by rw [demands₃, demands₂, demands₁]⟩
  simp [arity]

end IxCC.Aiur.CounterAnalysis
