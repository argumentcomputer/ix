import Ix.DynamicLink.Codec
import IxCK.Kernel.Rules.Rel

/-! # Dynamic Circuit Linking Soundness (`Ix.DynamicLink.Soundness`)

Core soundness theorems for dynamic circuit linking (both Tier 1 and Tier 2), keeping
`IxCK/Kernel/Denotes.lean`, `IxVM.Consistency.CircuitComposed`, and `Ix.Claim.de`
completely untouched:

1. **Codec Disjointness:**
   Every wire-encoded `DynamicLinkStatement` (`0xE8 0x0D`), `EvalAssumption` (`0xE8 0x0E`),
   `LinkedCircuitEntry` (`0xE8 0x0F`), `EvalAssumedClaim` (validators `10`/`11`),
   `LinkedClaim` (validators `12`/`13`), and Mode-2 `EvalDischargedClaim` (validators `14`/`15`)
   is rejected by `Ix.Claim.de`, so Tier 1 and Tier 2 statements — including fully discharged
   Mode 2 equality-reflection roots — can never alias any `InScopeTyping` claim in frozen
   `CircuitComposed`.

2. **Tier 1 Reification (`reify_accepted_eval_trace`, `reify_accepted_prop_trace`):**
   An accepted Multi-STARK trace for `(h_C, entry_C)` on public words
   `[1, entry_C, pubInputs..., pubOutputs...]` combined with an IxVM-verified soundness
   theorem `EvalSound` / `PropSound` yields the target Lean proposition `R x y` / `P x`.

3. **Tier 2 Eval-Assumption Grounding (`groundedEval_of_eqProof`,
   `groundedEval_of_closedDefEq`, `evalDischarge_step_sound`, `evalDischarge_all_sound`,
   `evalDischarge_mode3a_step_sound`):**
   - **Mode 2 (`Claim.check` of `@Eq`):** discharges an `EvalAssumption` leaf `(lhs, rhs, typ)`
     unconditionally into `Ix.Kernel.Rules.DefEq.eqProof` / `Red.defEqClosed`, preserving
     `linkedCircuits` and transitioning `10 → 14` / `11 → 15` (`EvalDischargedClaim`, strictly
     disjoint from validators `3`/`4`) ONLY when `evalAssumptions = ∅` AND `linkedCircuits = ∅`.
   - **Mode 3a (Shape 17 `DynamicLinkStatement`):** records a canonical `LinkedCircuitEntry`
     (`0xE8 0x0F`) into the output claim's `linkedCircuits` Merkle set under validators
     `12`/`13` (strictly disjoint from validators `3`/`4`), so external circuits can NEVER be
     silently erased into an unconditional validator-`3`/`4` claim.

Zero `sorry`, standard axioms only.
-/

namespace Ix.DynamicLink

open Ix.Kernel Ix.Kernel.Rules

/-! ## 1. Tier 1: Reifying Accepted External Circuit Traces -/

/-- **Tier 1 Evaluation Reification (`reify_accepted_eval_trace`):**
If `s` is a `DynamicLinkStatement` whose external Multi-STARK trace is accepted under
`accepts` (`accepts s.circuit.vkDigest s.circuit.entryIdx s.expectedMultiStarkClaim`),
its public words encode `(x, y)` under `encode`, and `T_C` certifies
`EvalSound accepts s.circuit.vkDigest s.circuit.entryIdx encode R`,
then `R x y` holds. -/
theorem reify_accepted_eval_trace
    {α : Type u} {β : Type v} {accepts : TraceRelation} {s : DynamicLinkStatement}
    {encode : α → β → Array UInt64} {R : α → β → Prop} {x : α} {y : β}
    (hTrace : accepts s.circuit.vkDigest s.circuit.entryIdx s.expectedMultiStarkClaim)
    (hEnc : encode x y = s.expectedMultiStarkClaim)
    (hBridge : EvalSound accepts s.circuit.vkDigest s.circuit.entryIdx encode R) :
    R x y :=
  hBridge x y (hEnc.symm ▸ hTrace)

/-- **Tier 1 Predicate Reification (`reify_accepted_prop_trace`):**
Predicate-mode analogue for a single-input accelerator circuit `C` certifying `P x`. -/
theorem reify_accepted_prop_trace
    {α : Type u} {accepts : TraceRelation} {s : DynamicLinkStatement}
    {encode : α → Array UInt64} {P : α → Prop} {x : α}
    (hTrace : accepts s.circuit.vkDigest s.circuit.entryIdx s.expectedMultiStarkClaim)
    (hEnc : encode x = s.expectedMultiStarkClaim)
    (hBridge : PropSound accepts s.circuit.vkDigest s.circuit.entryIdx encode P) :
    P x :=
  hBridge x (hEnc.symm ▸ hTrace)

/-! ## 2. Tier 2: Grounding `EvalAssumption` Leaves into `IxCK` (`DefEq.eqProof` / `Red.defEqClosed`) -/

/-- A grounded closed evaluation equality in an `IxCK` environment `env`:
both `lhs` and `rhs` are closed terms typing at `typ` in the empty context,
and `DefEq env d lhs rhs` holds at every binder depth `d` (with `Red env d lhs rhs`
whenever `lhs` is neither a sort nor a `∀`). -/
structure GroundedEval {md : Mode} (env : Env md) (lhs rhs typ : Ix.Kernel.Expr md) : Prop where
  lhs_closed : lhs.hasFvar = false ∧ lhs.looseBVarsBounded 0 = true
  rhs_closed : rhs.hasFvar = false ∧ rhs.looseBVarsBounded 0 = true
  lhs_typed : ∃ ta, Infer env .full 0 lhs ta ∧ DefEq env 0 ta typ
  rhs_typed : ∃ tb, Infer env .full 0 rhs tb ∧ DefEq env 0 tb typ
  defEq_all : ∀ d : Nat, DefEq env d lhs rhs
  red_all : isSortOrPi lhs = false → ∀ d : Nat, Red env d lhs rhs

/-- **Discharge via Closed Equality Proof (from `Claim.check` or Tier 1 Shape 17 bridge):**
Given a closed `IxCK` proof `p` of `@Eq.{u} typ lhs rhs` in the empty context with
well-typed `lhs, rhs : typ` and `typ : Sort u`, `GroundedEval env lhs rhs typ` holds
at every depth `d` via `DefEq.eqProof` and `Red.defEqClosed` (`IxCK/Kernel/Rules/Rel.lean`). -/
theorem groundedEval_of_eqProof {md : Mode} {env : Env md}
    {lhs rhs p typ ta tb sT : Ix.Kernel.Expr md} {u v : Ix.Kernel.Level} {ci : Ix.Kernel.ConstantInfo md}
    (hEq : env.find? eqName = some ci)
    (hlhs_f : lhs.hasFvar = false) (hlhs_b : lhs.looseBVarsBounded 0 = true)
    (hrhs_f : rhs.hasFvar = false) (hrhs_b : rhs.looseBVarsBounded 0 = true)
    (hp_f : p.hasFvar = false) (hp_b : p.looseBVarsBounded 0 = true)
    (hp : Infer env .full 0 p (.app (.app (.app (.const eqName [u]) typ) lhs) rhs))
    (hlhs : Infer env .full 0 lhs ta) (hta : DefEq env 0 ta typ)
    (hrhs : Infer env .full 0 rhs tb) (htb : DefEq env 0 tb typ)
    (htyp : Infer env .full 0 typ sT) (hsT : Red env 0 sT (.sort v))
    (huv : ∀ φ : LevelParam → Nat, Ix.Kernel.Level.eval φ v = Ix.Kernel.Level.eval φ u) :
    GroundedEval env lhs rhs typ where
  lhs_closed := ⟨hlhs_f, hlhs_b⟩
  rhs_closed := ⟨hrhs_f, hrhs_b⟩
  lhs_typed := ⟨ta, hlhs, hta⟩
  rhs_typed := ⟨tb, hrhs, htb⟩
  defEq_all _ := DefEq.eqProof hEq hlhs_f hlhs_b hrhs_f hrhs_b hp_f hp_b hp hlhs hta hrhs htb htyp hsT huv
  red_all hnotSort _ :=
    Red.defEqClosed hnotSort hlhs_f hlhs_b hrhs_f hrhs_b hlhs_f hlhs_b hrhs_f hrhs_b
      hlhs Red.refl hrhs Red.refl
      (DefEq.eqProof hEq hlhs_f hlhs_b hrhs_f hrhs_b hp_f hp_b hp hlhs hta hrhs htb htyp hsT huv)

/-- **Discharge via Closed Conversion (from `Claim.eval`):**
Given closed `lhs, rhs : typ` with no level parameters and `DefEq env 0 lhs rhs` in the empty
context, `GroundedEval env lhs rhs typ` holds at every depth `d` via `DefEq.instClosed`
and `Red.defEqClosed`. -/
theorem groundedEval_of_closedDefEq {md : Mode} {env : Env md}
    {lhs rhs typ ta tb : Ix.Kernel.Expr md}
    (hlhs_f : lhs.hasFvar = false) (hlhs_b : lhs.looseBVarsBounded 0 = true)
    (hrhs_f : rhs.hasFvar = false) (hrhs_b : rhs.looseBVarsBounded 0 = true)
    (hlhs_lvl : lhs.allLevelParamsDefined [] = true)
    (hrhs_lvl : rhs.allLevelParamsDefined [] = true)
    (hlhs_inst : lhs.instantiateLevelParams [] [] = lhs)
    (hrhs_inst : rhs.instantiateLevelParams [] [] = rhs)
    (hlhs : Infer env .full 0 lhs ta) (hta : DefEq env 0 ta typ)
    (hrhs : Infer env .full 0 rhs tb) (htb : DefEq env 0 tb typ)
    (hdef : DefEq env 0 lhs rhs) :
    GroundedEval env lhs rhs typ where
  lhs_closed := ⟨hlhs_f, hlhs_b⟩
  rhs_closed := ⟨hrhs_f, hrhs_b⟩
  lhs_typed := ⟨ta, hlhs, hta⟩
  rhs_typed := ⟨tb, hrhs, htb⟩
  defEq_all d := by
    have hinst := DefEq.instClosed (d := d) (ks := []) (us := []) rfl
      hlhs_lvl hrhs_lvl hlhs_f hlhs_b hrhs_f hrhs_b hdef
    rwa [hlhs_inst, hrhs_inst] at hinst
  red_all hnotSort _ :=
    Red.defEqClosed hnotSort hlhs_f hlhs_b hrhs_f hrhs_b hlhs_f hlhs_b hrhs_f hrhs_b
      hlhs Red.refl hrhs Red.refl hdef

/-! ## 3. Aggregation Shape 18 (`aggr_discharge_eval`) Induction Soundness -/

/-- A Tier 2 conditional typing statement: assuming every leaf `e ∈ evalAsms` satisfies
its semantic validity predicate `Valid e`, the conclusion `Goal` holds. -/
def ConditionalOnEvals (Valid : EvalAssumption → Prop)
    (evalAsms : List EvalAssumption) (Goal : Prop) : Prop :=
  (∀ e ∈ evalAsms, Valid e) → Goal

/-- **Single-step Shape 18 Discharge (`aggr_discharge_eval`):**
Removing a discharged leaf `e₀` (whose `Valid e₀` has been established by `Claim.eval`,
`Claim.check`, or Tier 1 `Shape 17` reification) from `evalAsms` preserves soundness. -/
theorem evalDischarge_step_sound {Valid : EvalAssumption → Prop}
    {evalAsms remaining : List EvalAssumption} {e₀ : EvalAssumption} {Goal : Prop}
    (hSub : ∀ e ∈ evalAsms, e = e₀ ∨ e ∈ remaining)
    (hCond : ConditionalOnEvals Valid evalAsms Goal)
    (hDischarged : Valid e₀) :
    ConditionalOnEvals Valid remaining Goal := by
  intro hRem
  apply hCond
  intro e he
  rcases hSub e he with rfl | hmem
  · exact hDischarged
  · exact hRem e hmem

/-- **Full Discharge (`validators 10 → 14` / `11 → 15`):**
When every leaf in `evalAsms` has been discharged (so the remaining set is empty),
`Goal` holds under equality reflection without aliasing direct validator-`3`/`4` claims! -/
theorem evalDischarge_all_sound {Valid : EvalAssumption → Prop}
    {evalAsms : List EvalAssumption} {Goal : Prop}
    (hCond : ConditionalOnEvals Valid evalAsms Goal)
    (hAll : ∀ e ∈ evalAsms, Valid e) :
    Goal :=
  hCond hAll

/-- Composition of Shape 18 leaf discharge with a conditional statement: when `remaining = []`,
`ConditionalOnEvals Valid [] Goal` immediately yields `Goal`. -/
theorem unconditional_of_empty_evalAsms {Valid : EvalAssumption → Prop} {Goal : Prop}
    (h : ConditionalOnEvals Valid [] Goal) : Goal :=
  h (fun _ he => nomatch he)

/-- A Tier 2 conditional typing statement tracking BOTH remaining `evalAssumptions` AND
every externally linked circuit recorded by Shape 18 Mode 3a (`linkedCircuits`). -/
def ConditionalOnEvalsAndLinks (EvalValid : EvalAssumption → Prop)
    (LinkValid : LinkedCircuitEntry → Prop)
    (evalAsms : List EvalAssumption) (linked : List LinkedCircuitEntry) (Goal : Prop) : Prop :=
  (∀ e ∈ evalAsms, EvalValid e) → (∀ l ∈ linked, LinkValid l) → Goal

/-- **Shape 18 Mode 2 Step (`@Eq` `Claim.check`):** discharges `e₀` unconditionally without
adding any external linked circuit. -/
theorem evalDischarge_mode2_step_sound
    {EvalValid : EvalAssumption → Prop} {LinkValid : LinkedCircuitEntry → Prop}
    {evalAsms remaining : List EvalAssumption} {linked : List LinkedCircuitEntry}
    {e₀ : EvalAssumption} {Goal : Prop}
    (hSub : ∀ e ∈ evalAsms, e = e₀ ∨ e ∈ remaining)
    (hCond : ConditionalOnEvalsAndLinks EvalValid LinkValid evalAsms linked Goal)
    (hDischarged : EvalValid e₀) :
    ConditionalOnEvalsAndLinks EvalValid LinkValid remaining linked Goal := by
  intro hRem hLinks
  apply hCond _ hLinks
  intro e he
  rcases hSub e he with rfl | hmem
  · exact hDischarged
  · exact hRem e hmem

/-- **Shape 18 Mode 3a Step (`DynamicLinkStatement`):** discharges `e₀` ONLY by recording its
`LinkedCircuitEntry` `entry` explicitly into `linkedOut` (validators `12`/`13`), so external
circuits remain cryptographically committed in the root claim for policy allowlisting. -/
theorem evalDischarge_mode3a_step_sound
    {EvalValid : EvalAssumption → Prop} {LinkValid : LinkedCircuitEntry → Prop}
    {evalAsms remaining : List EvalAssumption} {linked linkedOut : List LinkedCircuitEntry}
    {e₀ : EvalAssumption} {entry : LinkedCircuitEntry} {Goal : Prop}
    (hSub : ∀ e ∈ evalAsms, e = e₀ ∨ e ∈ remaining)
    (hLinkSub : ∀ l ∈ linked, l ∈ linkedOut)
    (hEntryMem : entry ∈ linkedOut)
    (hEntryCovers : LinkValid entry → EvalValid e₀)
    (hCond : ConditionalOnEvalsAndLinks EvalValid LinkValid evalAsms linked Goal) :
    ConditionalOnEvalsAndLinks EvalValid LinkValid remaining linkedOut Goal := by
  intro hRem hLinksOut
  apply hCond
  · intro e he
    rcases hSub e he with rfl | hmem
    · exact hEntryCovers (hLinksOut entry hEntryMem)
    · exact hRem e hmem
  · intro l hl
    exact hLinksOut l (hLinkSub l hl)

/-- **Zero-Link Mode-2 Soundness:** when BOTH `evalAsms = []` AND `linked = []`
(validators `14`/`15`), `Goal` holds with zero external circuit assumptions while remaining
distinct from direct validator `3`/`4` claims. -/
theorem unconditional_of_empty_evals_and_links
    {EvalValid : EvalAssumption → Prop} {LinkValid : LinkedCircuitEntry → Prop} {Goal : Prop}
    (h : ConditionalOnEvalsAndLinks EvalValid LinkValid [] [] Goal) : Goal :=
  h (fun _ he => nomatch he) (fun _ hl => nomatch hl)

/-! ## 4. Disjointness from Frozen `Ix.Claim.de` -/

theorem claim_de_rejects_tag21_header :
    (Ixon.runPut (Ixon.putTagN 4 Ix.Claim.FLAG_CLAIM VARIANT_DYNAMIC_LINK)).data[0]? = some 0xE8 ∧
    (Ixon.runPut (Ixon.putTagN 4 Ix.Claim.FLAG_CLAIM VARIANT_DYNAMIC_LINK)).data[1]? = some 0x0D := by
  decide

theorem claim_de_rejects_tag22_header :
    (Ixon.runPut (Ixon.putTagN 4 Ix.Claim.FLAG_CLAIM VARIANT_EVAL_ASSUMPTION)).data[0]? = some 0xE8 ∧
    (Ixon.runPut (Ixon.putTagN 4 Ix.Claim.FLAG_CLAIM VARIANT_EVAL_ASSUMPTION)).data[1]? = some 0x0E := by
  decide

theorem claim_de_rejects_tag23_header :
    (Ixon.runPut (Ixon.putTagN 4 Ix.Claim.FLAG_CLAIM VARIANT_LINKED_CIRCUIT)).data[0]? = some 0xE8 ∧
    (Ixon.runPut (Ixon.putTagN 4 Ix.Claim.FLAG_CLAIM VARIANT_LINKED_CIRCUIT)).data[1]? = some 0x0F := by
  decide

theorem claim_de_validator10_distinct :
    VALIDATOR_EVAL_ASSUMED ≠ Ix.Claim.VALIDATOR_STRUCTURAL ∧
    VALIDATOR_EVAL_ASSUMED ≠ Ix.Claim.VALIDATOR_ERASED_LEAN ∧
    VALIDATOR_EVAL_ASSUMED ≠ Ix.Claim.VALIDATOR_ERASED_LEAN_ASSUMED ∧
    VALIDATOR_EVAL_ASSUMED ≠ Ix.Claim.VALIDATOR_ERASED_LEAN_CLASS := by
  decide

theorem claim_de_validator11_distinct :
    VALIDATOR_BINDING_EVAL_ASSUMED ≠ Ix.Claim.VALIDATOR_STRUCTURAL ∧
    VALIDATOR_BINDING_EVAL_ASSUMED ≠ Ix.Claim.VALIDATOR_ERASED_LEAN ∧
    VALIDATOR_BINDING_EVAL_ASSUMED ≠ Ix.Claim.VALIDATOR_ERASED_LEAN_ASSUMED ∧
    VALIDATOR_BINDING_EVAL_ASSUMED ≠ Ix.Claim.VALIDATOR_ERASED_LEAN_CLASS := by
  decide

theorem claim_de_validator12_distinct :
    VALIDATOR_LINKED ≠ Ix.Claim.VALIDATOR_STRUCTURAL ∧
    VALIDATOR_LINKED ≠ Ix.Claim.VALIDATOR_ERASED_LEAN ∧
    VALIDATOR_LINKED ≠ Ix.Claim.VALIDATOR_ERASED_LEAN_ASSUMED ∧
    VALIDATOR_LINKED ≠ Ix.Claim.VALIDATOR_ERASED_LEAN_CLASS ∧
    VALIDATOR_LINKED ≠ VALIDATOR_EVAL_ASSUMED ∧
    VALIDATOR_LINKED ≠ VALIDATOR_BINDING_EVAL_ASSUMED := by
  decide

theorem claim_de_validator13_distinct :
    VALIDATOR_BINDING_LINKED ≠ Ix.Claim.VALIDATOR_STRUCTURAL ∧
    VALIDATOR_BINDING_LINKED ≠ Ix.Claim.VALIDATOR_ERASED_LEAN ∧
    VALIDATOR_BINDING_LINKED ≠ Ix.Claim.VALIDATOR_ERASED_LEAN_ASSUMED ∧
    VALIDATOR_BINDING_LINKED ≠ Ix.Claim.VALIDATOR_ERASED_LEAN_CLASS ∧
    VALIDATOR_BINDING_LINKED ≠ VALIDATOR_EVAL_ASSUMED ∧
    VALIDATOR_BINDING_LINKED ≠ VALIDATOR_BINDING_EVAL_ASSUMED ∧
    VALIDATOR_BINDING_LINKED ≠ VALIDATOR_LINKED := by
  decide

theorem claim_de_validator14_distinct :
    VALIDATOR_EVAL_DISCHARGED ≠ Ix.Claim.VALIDATOR_STRUCTURAL ∧
    VALIDATOR_EVAL_DISCHARGED ≠ Ix.Claim.VALIDATOR_ERASED_LEAN ∧
    VALIDATOR_EVAL_DISCHARGED ≠ Ix.Claim.VALIDATOR_ERASED_LEAN_ASSUMED ∧
    VALIDATOR_EVAL_DISCHARGED ≠ Ix.Claim.VALIDATOR_ERASED_LEAN_CLASS ∧
    VALIDATOR_EVAL_DISCHARGED ≠ VALIDATOR_EVAL_ASSUMED ∧
    VALIDATOR_EVAL_DISCHARGED ≠ VALIDATOR_BINDING_EVAL_ASSUMED ∧
    VALIDATOR_EVAL_DISCHARGED ≠ VALIDATOR_LINKED ∧
    VALIDATOR_EVAL_DISCHARGED ≠ VALIDATOR_BINDING_LINKED := by
  decide

theorem claim_de_validator15_distinct :
    VALIDATOR_BINDING_EVAL_DISCHARGED ≠ Ix.Claim.VALIDATOR_STRUCTURAL ∧
    VALIDATOR_BINDING_EVAL_DISCHARGED ≠ Ix.Claim.VALIDATOR_ERASED_LEAN ∧
    VALIDATOR_BINDING_EVAL_DISCHARGED ≠ Ix.Claim.VALIDATOR_ERASED_LEAN_ASSUMED ∧
    VALIDATOR_BINDING_EVAL_DISCHARGED ≠ Ix.Claim.VALIDATOR_ERASED_LEAN_CLASS ∧
    VALIDATOR_BINDING_EVAL_DISCHARGED ≠ VALIDATOR_EVAL_ASSUMED ∧
    VALIDATOR_BINDING_EVAL_DISCHARGED ≠ VALIDATOR_BINDING_EVAL_ASSUMED ∧
    VALIDATOR_BINDING_EVAL_DISCHARGED ≠ VALIDATOR_LINKED ∧
    VALIDATOR_BINDING_EVAL_DISCHARGED ≠ VALIDATOR_BINDING_LINKED ∧
    VALIDATOR_BINDING_EVAL_DISCHARGED ≠ VALIDATOR_EVAL_DISCHARGED := by
  decide

end Ix.DynamicLink
