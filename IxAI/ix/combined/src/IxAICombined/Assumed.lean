import IxAICombined

/-! # The combined certificate's environment with the refinement theorem assumed

The closure of `IxAICombined.blockRun` holds the proof of `train_of_deployed_blocks_enc`: the
generated path lemmas of `IxAIRefine` and the correctness of the Aiur compiler. The binding below
names the same statement through an axiom, so its closure holds only what the statement mentions:
the specification, the program's source and the definitions of the Aiur compiler and its
semantics.

An Ix claim over this environment lists the axiom in its context (`ClaimContext.axioms`), so a
certificate built on it says in its own claim that the refinement theorem is assumed. The theorem
itself is `IxAICombined.train_of_deployed_blocks_enc`, checked by Lean's kernel; the axiom's type
is that theorem's type, which a consumer can compare by address. -/

namespace IxAICombined.Assumed

/-- The statement of `IxAICombined.train_of_deployed_blocks_enc`, assumed. -/
axiom train_of_deployed_blocks_enc : type_of% @IxAICombined.train_of_deployed_blocks_enc

/-- `IxAICombined.blockRun` with its refinement assumed: the same program key, entry, execution
count and statement. -/
def blockRun : AiurBinding where
  programKey := "d46caf1e358f9e28744a1163b2d25b2ea4de331870fcc78e1625119edfa1da58"
  entry := "Fixed::train_block"
  entryIndex := 0
  executions := 30
  statement := type_of% @IxAICombined.train_of_deployed_blocks_enc
  refinement := @train_of_deployed_blocks_enc

/-- The two bindings differ only in how their statement is justified. -/
theorem blockRun_agrees :
    blockRun.programKey = IxAICombined.blockRun.programKey ∧
      blockRun.entry = IxAICombined.blockRun.entry ∧
      blockRun.entryIndex = IxAICombined.blockRun.entryIndex ∧
      blockRun.executions = IxAICombined.blockRun.executions ∧
      blockRun.statement = IxAICombined.blockRun.statement :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end IxAICombined.Assumed
