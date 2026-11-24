import Ix.Cert.Aggr.EndToEnd

/-! # Certified Aggregation & Dynamic-Linking Audit Surface (`Ix.Cert.Aggr.Audit`)

Pins both the **exact theorem types** (`#guard_msgs` around every `#check`) and the
**exact axiom footprint** (`[propext, Classical.choice, Quot.sound]`, zero `sorry`,
zero `native_decide`, zero `bv_decide`, zero custom axioms) of the `Ix.Cert.Aggr` stack.

### Scope boundary (honest accounting)
`AcceptedAggrTree` and the `aggregated_root_*` theorems prove soundness of the
**stage-isolated** 19-shape aggregation tree (paired with `AggregateProgramAstPinned`
on `MultiStark.aggregateProgram`, `RecursionVerifierAstPinned` on
`MultiStark.recursionProgram`, per-child `verifyBatchBytes` soundness, `SecurityEnvelopeOk`
with per-`logBlowup` provable UD query floors, and explicit `LinkedCircuitEntry`
preservation for Shape 18 Mode 3a). Full observation-level lowering of each individual
`Aggregation::*` Aiur body into `AcceptedAggrTree` constructors is tracked separately.
-/

-- 1. Deployed MultiStark.aggregateProgram 19-shape AST & digest pins
/-- info: Ix.Cert.Aggr.aggregateSource_exact_19_shape_arms : (match
    Ix.Cert.MultiStarkRefinement.findModuleFunction? MultiStark.aggregateSource "MultiStark" "ix_aggr" with
  | some fdecl => Ix.Cert.MultiStarkRefinement.exprMatchLitArms fdecl.body
  | none => []) =
  List.range 19 -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.aggregateSource_exact_19_shape_arms
/-- info: Ix.Cert.Aggr.aggregateSource_discharge_eval_exact_arms : (match
    Ix.Cert.MultiStarkRefinement.findModuleFunction? MultiStark.aggregateSource "Aggregation" "aggr_discharge_eval" with
  | some fdecl => Ix.Cert.MultiStarkRefinement.exprMatchLitArms fdecl.body
  | none => []) =
  [228, 232] -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.aggregateSource_discharge_eval_exact_arms
/-- info: Ix.Cert.Aggr.aggregateSource_bridge_cert_exact_arms : (match
    Ix.Cert.MultiStarkRefinement.findModuleFunction? MultiStark.aggregateSource "Aggregation"
      "aggr_verify_bridge_cert" with
  | some fdecl => Ix.Cert.MultiStarkRefinement.exprMatchLitArms fdecl.body
  | none => []) =
  [228, 229] -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.aggregateSource_bridge_cert_exact_arms
/-- info: Ix.Cert.Aggr.aggregateSource_eval_assumed_exact_arms : (match
    Ix.Cert.MultiStarkRefinement.findModuleFunction? MultiStark.aggregateSource "Aggregation"
      "aggr_parse_eval_assumed" with
  | some fdecl => Ix.Cert.MultiStarkRefinement.exprMatchLitArms fdecl.body
  | none => []) =
  [10, 11, 12, 13] -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.aggregateSource_eval_assumed_exact_arms
/-- info: Ix.Cert.Aggr.aggregateSource_parse_eval_absent : Ix.Cert.MultiStarkRefinement.hasModuleFunction MultiStark.aggregateSource "Aggregation" "aggr_parse_eval" = false -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.aggregateSource_parse_eval_absent
/-- info: Ix.Cert.Aggr.aggregateSource_security_envelope_literals_pinned : (match
    Ix.Cert.MultiStarkRefinement.findModuleFunction? MultiStark.aggregateSource "Aggregation"
      "aggr_assert_security_envelope" with
  | some fdecl =>
    have lits := Ix.Cert.Aggr.exprLiterals fdecl.body;
    Ix.Cert.Aggr.securityEnvelopeRequiredLiterals.all fun n => lits.contains n
  | none => false) =
  true -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.aggregateSource_security_envelope_literals_pinned
/-- info: Ix.Cert.Aggr.aggregateSource_core_helpers_present : (Ix.Cert.Aggr.aggregationCoreFunctions.all fun fnName =>
    Ix.Cert.MultiStarkRefinement.hasModuleFunction MultiStark.aggregateSource "Aggregation" fnName) =
  true -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.aggregateSource_core_helpers_present
/-- info: Ix.Cert.Aggr.aggregateDigest_eq : MultiStark.aggregateDigest = Ix.Cert.Aggr.pinnedAggregateDigest -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.aggregateDigest_eq
/-- info: Ix.Cert.Aggr.aggregateSource_ast_pinned : Ix.Cert.Aggr.AggregateProgramAstPinned MultiStark.aggregateSource = true -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.aggregateSource_ast_pinned
/-- info: Ix.Cert.Aggr.aggregateProgram_ast_pinned : Ix.Cert.Aggr.AggregateProgramAstPinned MultiStark.aggregateProgram = true -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.aggregateProgram_ast_pinned
/-- info: 'Ix.Cert.Aggr.aggregateSource_exact_19_shape_arms' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.aggregateSource_exact_19_shape_arms
/-- info: 'Ix.Cert.Aggr.aggregateSource_discharge_eval_exact_arms' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.aggregateSource_discharge_eval_exact_arms
/-- info: 'Ix.Cert.Aggr.aggregateSource_bridge_cert_exact_arms' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.aggregateSource_bridge_cert_exact_arms
/-- info: 'Ix.Cert.Aggr.aggregateSource_eval_assumed_exact_arms' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.aggregateSource_eval_assumed_exact_arms
/-- info: 'Ix.Cert.Aggr.aggregateSource_parse_eval_absent' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.aggregateSource_parse_eval_absent
/-- info: 'Ix.Cert.Aggr.aggregateSource_security_envelope_literals_pinned' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.aggregateSource_security_envelope_literals_pinned
/-- info: 'Ix.Cert.Aggr.aggregateDigest_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.aggregateDigest_eq
/-- info: 'Ix.Cert.Aggr.aggregateProgram_ast_pinned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.aggregateProgram_ast_pinned

-- 2. Range telescoping, Shape 17 security envelope (with UD floor), and M-node ROM union bound
/-- info: Ix.Cert.Aggr.aggr_range_telescoping : ∀ (f : ℕ → Ix.Cert.MultiStark.K) {lo mid hi : ℕ},
  lo ≤ mid →
    mid ≤ hi →
      Aggr.rangeSum Ix.Cert.Aggr.kResidualMonoid f lo mid + Aggr.rangeSum Ix.Cert.Aggr.kResidualMonoid f mid hi =
        Aggr.rangeSum Ix.Cert.Aggr.kResidualMonoid f lo hi -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.aggr_range_telescoping
/-- info: Ix.Cert.Aggr.securityEnvelopeOk_iff : ∀ (p : Ix.Cert.MultiStark.StarkParams),
  Ix.Cert.Aggr.SecurityEnvelopeOk p ↔
    Ix.Cert.MultiStark.checkParams p = true ∧
      Aiur.meetsSecurityFloor (Ix.Cert.Aggr.toAiurParams p).1 (Ix.Cert.Aggr.toAiurParams p).2 = true ∧
        Ix.Cert.Aggr.minProvableUdMillibits ≤ Ix.Cert.Aggr.udQueryMillibits p.logBlowup p.numQueries p.queryPowBits ∧
          Ix.Cert.Aggr.minJohnson128Millibits ≤
            Ix.Cert.Aggr.johnsonQueryMillibits p.logBlowup p.numQueries p.queryPowBits -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.securityEnvelopeOk_iff
/-- info: Ix.Cert.Aggr.tree_rom_error_bound : ∀ (probs : List ℝ) {ε : ℝ}, (∀ p ∈ probs, p ≤ ε) → probs.sum ≤ ↑probs.length * ε -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.tree_rom_error_bound
/-- info: Ix.Cert.Aggr.tree_rom_error_merge : ∀ (M₁ M₂ : ℕ) (ε : ℝ), ↑(M₁ + M₂ + 1) * ε = ↑M₁ * ε + ↑M₂ * ε + ε -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.tree_rom_error_merge
/-- info: 'Ix.Cert.Aggr.aggr_range_telescoping' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.aggr_range_telescoping
/-- info: 'Ix.Cert.Aggr.securityEnvelopeOk_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.securityEnvelopeOk_iff
/-- info: 'Ix.Cert.Aggr.tree_rom_error_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.tree_rom_error_bound

-- 3. Conditional shard companion (`A7` axioms, Shape 18 discharge & explicit `LinkedCircuitEntry` tracking)
/-- info: @Ix.Cert.Aggr.evalLeafSound_of_eqProof : ∀ {env : Ix.Kernel.Env Ix.Kernel.Mode.anon}
  {interpExpr : Address → Ix.Kernel.Expr Ix.Kernel.Mode.anon} {e : Ix.DynamicLink.EvalAssumption}
  {p ta tb sT : Ix.Kernel.Expr Ix.Kernel.Mode.anon} {lvlU lvlV : Ix.Kernel.Level}
  {ci : Ix.Kernel.ConstantInfo Ix.Kernel.Mode.anon},
  env.find? Ix.Kernel.eqName = some ci →
    (interpExpr e.lhs).hasFvar = false →
      Ix.Kernel.Expr.looseBVarsBounded 0 (interpExpr e.lhs) = true →
        (interpExpr e.rhs).hasFvar = false →
          Ix.Kernel.Expr.looseBVarsBounded 0 (interpExpr e.rhs) = true →
            p.hasFvar = false →
              Ix.Kernel.Expr.looseBVarsBounded 0 p = true →
                Ix.Kernel.Rules.Infer env Ix.Kernel.Rules.Grade.full 0 p
                    ((((Ix.Kernel.Expr.const Ix.Kernel.eqName [lvlU]).app (interpExpr e.typ)).app
                          (interpExpr e.lhs)).app
                      (interpExpr e.rhs)) →
                  Ix.Kernel.Rules.Infer env Ix.Kernel.Rules.Grade.full 0 (interpExpr e.lhs) ta →
                    Ix.Kernel.Rules.DefEq env 0 ta (interpExpr e.typ) →
                      Ix.Kernel.Rules.Infer env Ix.Kernel.Rules.Grade.full 0 (interpExpr e.rhs) tb →
                        Ix.Kernel.Rules.DefEq env 0 tb (interpExpr e.typ) →
                          Ix.Kernel.Rules.Infer env Ix.Kernel.Rules.Grade.full 0 (interpExpr e.typ) sT →
                            Ix.Kernel.Rules.Red env 0 sT (Ix.Kernel.Expr.sort lvlV) →
                              (∀ (φ : Ix.Kernel.LevelParam → ℕ),
                                  Ix.Kernel.Level.eval φ lvlV = Ix.Kernel.Level.eval φ lvlU) →
                                Ix.Cert.Aggr.EvalLeafSound env interpExpr e -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.evalLeafSound_of_eqProof
/-- info: @Ix.Cert.Aggr.evalLeafSound_of_closedDefEq : ∀ {env : Ix.Kernel.Env Ix.Kernel.Mode.anon}
  {interpExpr : Address → Ix.Kernel.Expr Ix.Kernel.Mode.anon} {e : Ix.DynamicLink.EvalAssumption}
  {ta tb : Ix.Kernel.Expr Ix.Kernel.Mode.anon},
  (interpExpr e.lhs).hasFvar = false →
    Ix.Kernel.Expr.looseBVarsBounded 0 (interpExpr e.lhs) = true →
      (interpExpr e.rhs).hasFvar = false →
        Ix.Kernel.Expr.looseBVarsBounded 0 (interpExpr e.rhs) = true →
          Ix.Kernel.Expr.allLevelParamsDefined [] (interpExpr e.lhs) = true →
            Ix.Kernel.Expr.allLevelParamsDefined [] (interpExpr e.rhs) = true →
              Ix.Kernel.Expr.instantiateLevelParams [] [] (interpExpr e.lhs) = interpExpr e.lhs →
                Ix.Kernel.Expr.instantiateLevelParams [] [] (interpExpr e.rhs) = interpExpr e.rhs →
                  Ix.Kernel.Rules.Infer env Ix.Kernel.Rules.Grade.full 0 (interpExpr e.lhs) ta →
                    Ix.Kernel.Rules.DefEq env 0 ta (interpExpr e.typ) →
                      Ix.Kernel.Rules.Infer env Ix.Kernel.Rules.Grade.full 0 (interpExpr e.rhs) tb →
                        Ix.Kernel.Rules.DefEq env 0 tb (interpExpr e.typ) →
                          Ix.Kernel.Rules.DefEq env 0 (interpExpr e.lhs) (interpExpr e.rhs) →
                            Ix.Cert.Aggr.EvalLeafSound env interpExpr e -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.evalLeafSound_of_closedDefEq
/-- info: @Ix.Cert.Aggr.evalLeafSound_of_dynamicLink : ∀ {accepts : Ix.DynamicLink.TraceRelation}
  {env : Ix.Kernel.Env Ix.Kernel.Mode.anon} {interpExpr : Address → Ix.Kernel.Expr Ix.Kernel.Mode.anon}
  {s : Ix.DynamicLink.DynamicLinkStatement} {e : Ix.DynamicLink.EvalAssumption}
  {encode : Address → Address → Array UInt64},
  accepts s.circuit.vkDigest s.circuit.entryIdx s.expectedMultiStarkClaim →
    encode e.lhs e.rhs = s.expectedMultiStarkClaim →
      (Ix.DynamicLink.EvalSound accepts s.circuit.vkDigest s.circuit.entryIdx encode fun lhs rhs =>
          Ix.DynamicLink.GroundedEval env (interpExpr lhs) (interpExpr rhs) (interpExpr e.typ)) →
        Ix.Cert.Aggr.EvalLeafSound env interpExpr e -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.evalLeafSound_of_dynamicLink
/-- info: @Ix.Cert.Aggr.conditionalChecked_mono_ax : ∀ {AxHolds : Address → Address → Prop}
  {EvalHolds : Address → Ix.DynamicLink.EvalAssumption → Prop} {TargetValid : Address → Address → Prop} {b : Address}
  {Ax₁ Ax₂ : Address → Prop} {EvalA : Ix.DynamicLink.EvalAssumption → Prop} {x : Address},
  (∀ (a : Address), Ax₁ a → Ax₂ a) →
    Ix.Cert.Aggr.ConditionalChecked AxHolds EvalHolds TargetValid b Ax₁ EvalA x →
      Ix.Cert.Aggr.ConditionalChecked AxHolds EvalHolds TargetValid b Ax₂ EvalA x -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.conditionalChecked_mono_ax
/-- info: @Ix.Cert.Aggr.conditionalChecked_discharge_eval : ∀ {AxHolds : Address → Address → Prop}
  {EvalHolds : Address → Ix.DynamicLink.EvalAssumption → Prop} {TargetValid : Address → Address → Prop} {b : Address}
  {Ax : Address → Prop} {EvalBefore EvalAfter : Ix.DynamicLink.EvalAssumption → Prop}
  {e₀ : Ix.DynamicLink.EvalAssumption} {x : Address},
  Aggr.EvalRemoveRel EvalBefore EvalAfter e₀ →
    Ix.Cert.Aggr.ConditionalEvalValid AxHolds EvalHolds b Ax e₀ →
      Ix.Cert.Aggr.ConditionalChecked AxHolds EvalHolds TargetValid b Ax EvalBefore x →
        Ix.Cert.Aggr.ConditionalChecked AxHolds EvalHolds TargetValid b Ax EvalAfter x -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.conditionalChecked_discharge_eval
/-- info: @Ix.Cert.Aggr.conditionalChecked_unconditional : ∀ {AxHolds : Address → Address → Prop}
  {EvalHolds : Address → Ix.DynamicLink.EvalAssumption → Prop} {TargetValid : Address → Address → Prop} {b x : Address},
  Ix.Cert.Aggr.ConditionalChecked AxHolds EvalHolds TargetValid b (fun x => False) (fun x => False) x → TargetValid b x -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.conditionalChecked_unconditional
/-- info: @Ix.Cert.Aggr.conditionalCheckedWithLinks_discharge_via_link : ∀ {AxHolds : Address → Address → Prop}
  {EvalHolds : Address → Ix.DynamicLink.EvalAssumption → Prop}
  {LinkHolds : Address → Ix.DynamicLink.LinkedCircuitEntry → Prop} {TargetValid : Address → Address → Prop}
  {b : Address} {Ax : Address → Prop} {EvalBefore EvalAfter : Ix.DynamicLink.EvalAssumption → Prop}
  {LinkedBefore LinkedAfter : Ix.DynamicLink.LinkedCircuitEntry → Prop} {e₀ : Ix.DynamicLink.EvalAssumption}
  {entry : Ix.DynamicLink.LinkedCircuitEntry} {x : Address},
  Aggr.EvalRemoveRel EvalBefore EvalAfter e₀ →
    Aggr.LinkedMergeRel LinkedBefore entry LinkedAfter →
      (LinkHolds b entry → EvalHolds b e₀) →
        Ix.Cert.Aggr.ConditionalCheckedWithLinks AxHolds EvalHolds LinkHolds TargetValid b Ax EvalBefore LinkedBefore
            x →
          Ix.Cert.Aggr.ConditionalCheckedWithLinks AxHolds EvalHolds LinkHolds TargetValid b Ax EvalAfter LinkedAfter x -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.conditionalCheckedWithLinks_discharge_via_link
/-- info: @Ix.Cert.Aggr.conditionalCheckedWithLinks_unconditional : ∀ {AxHolds : Address → Address → Prop}
  {EvalHolds : Address → Ix.DynamicLink.EvalAssumption → Prop}
  {LinkHolds : Address → Ix.DynamicLink.LinkedCircuitEntry → Prop} {TargetValid : Address → Address → Prop}
  {b x : Address},
  Ix.Cert.Aggr.ConditionalCheckedWithLinks AxHolds EvalHolds LinkHolds TargetValid b (fun x => False) (fun x => False)
      (fun x => False) x →
    TargetValid b x -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.conditionalCheckedWithLinks_unconditional
/-- info: @Ix.Cert.Aggr.composedModelConclusion_of_composedSpec : ∀
  {callsA callsB : List (Aiur.Generic.SourceSemantics.Call IxVM.F)} {dA dB : IxVM.Refinement.Digest},
  IxVM.Consistency.ComposedSpec callsA callsB dA dB →
    ∀ {bytesB : ByteArray} {spec a : Address},
      Ix.Claim.de bytesB = Except.ok (Ix.Claim.binding spec a) →
        IxVM.Refinement.packDigest (Address.blake3Pure bytesB) = dB →
          ∀ {bytesA : ByteArray} {cA : Ix.Claim},
            Ix.Claim.de bytesA = Except.ok cA →
              IxVM.Refinement.packDigest (Address.blake3Pure bytesA) = dA →
                IxVM.Consistency.InScopeTyping cA →
                  ∀ {ctx : Ix.ClaimContext},
                    cA.context? = some ctx →
                      ctx.binding = a →
                        ∀ {V : IxVM.Refinement.View} {seeds : List Address},
                          IxVM.Consistency.ClaimSeeds cA V seeds →
                            Ix.Cert.Aggr.ComposedModelConclusion callsA callsB bytesA bytesB V a seeds -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.composedModelConclusion_of_composedSpec
/-- info: Ix.Cert.Aggr.composedModelConclusion_no_false : ∀ (W : Type u_1) [Ix.Kernel.SetTheory W]
  {callsA callsB : List (Aiur.Generic.SourceSemantics.Call IxVM.F)} {bytesA bytesB : ByteArray}
  {V : IxVM.Refinement.View} {a : Address} {seeds : List Address},
  Ix.Cert.Aggr.ComposedModelConclusion callsA callsB bytesA bytesB V a seeds →
    V.HashedCollision (bytesA :: bytesB :: IxVM.Consistency.committedFootprint) (callsA ++ callsB) ∨
      IxVM.Consistency.ComposedWith (fun t R x => IxVM.Consistency.SeedsNotFalse callsA t R seeds) callsB a -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.composedModelConclusion_no_false
/-- info: 'Ix.Cert.Aggr.evalLeafSound_of_eqProof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.evalLeafSound_of_eqProof
/-- info: 'Ix.Cert.Aggr.composedModelConclusion_no_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.composedModelConclusion_no_false

-- 4. Stage-Isolated 19-Shape Tree Refinement & End-to-End `aggregated_root_*` Headlines
/-- info: @Ix.Cert.Aggr.acceptedAggrTree_refines_derivation19 : ∀
  {sem :
    Aggr.AggrSemantics Address Address Ix.DynamicLink.EvalAssumption Address Ix.Cert.MultiStark.K
      Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry}
  {batchClaim :
    ℕ →
      Aggr.ValidatorMode Address →
        (Address → Prop) → (Address → Prop) → (Address → Prop) → (Ix.DynamicLink.EvalAssumption → Prop) → Prop}
  {stmt :
    Aggr.AggrNodeStmt Address Address Ix.DynamicLink.EvalAssumption Address Ix.Cert.MultiStark.K
      Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry}
  (t : Ix.Cert.Aggr.AcceptedAggrTree sem batchClaim stmt),
  Aggr.AggrDerivation19 sem batchClaim stmt ∧
    (t.HasTreeCollision ∨
      ∀ vp ∈ t.childProofs,
        ∃ proofBytes, Ix.Cert.MultiStark.verifyBatchBytes vp.vkBytes vp.claimsBytes proofBytes = true) -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.acceptedAggrTree_refines_derivation19
/-- info: @Ix.Cert.Aggr.acceptedAggrTree_unlinked_zero_dynamicLinkDischarges : ∀
  {sem :
    Aggr.AggrSemantics Address Address Ix.DynamicLink.EvalAssumption Address Ix.Cert.MultiStark.K
      Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry}
  {batchClaim :
    ℕ →
      Aggr.ValidatorMode Address →
        (Address → Prop) → (Address → Prop) → (Address → Prop) → (Ix.DynamicLink.EvalAssumption → Prop) → Prop}
  {mode : Aggr.ValidatorMode Address} {S A Ax : Address → Prop} {EvalA : Ix.DynamicLink.EvalAssumption → Prop}
  {Linked : Ix.DynamicLink.LinkedCircuitEntry → Prop},
  mode.isLinked = false →
    ∀ (t : Ix.Cert.Aggr.AcceptedAggrTree sem batchClaim (Aggr.AggrNodeStmt.checkEnv mode S A Ax EvalA Linked)),
      t.dynamicLinkDischarges = 0 -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.acceptedAggrTree_unlinked_zero_dynamicLinkDischarges
/-- info: Ix.Cert.Aggr.aggregated_root_sound : ∀ (prepared : Aiur.Modules.Prepared MultiStark.aggregateProgram)
  (compiled : Aiur.Optimized.ModulesArtifact prepared)
  (physical : Aiur.Optimized.Physical.Prepared compiled.circuit.artifact) {cfg : Aiur.Optimized.Depth.Config},
  Aiur.Optimized.Physical.Prepared.DepthCertified compiled.circuit physical cfg →
    cfg.bits ≤ 24 →
      ∀ {id : String → Except String ℕ}
        (plan : Aiur.Optimized.Grouping.Plan (Aiur.Optimized.Depth.system cfg physical.system) id),
        plan.WellFormedActivation →
          ∀ {entry : Aiur.Modules.Selection MultiStark.aggregateProgram prepared.environment.assembly.instances},
            prepared.find? Ix.Cert.Aggr.ixAggrEntry = some entry →
              ∀ {rom : Aiur.WidthROM Ix.Cert.MultiStark.Fp} (ivlsOf : ℕ → List (ℕ × ℕ)),
                (∀ (w : ℕ), Ix.Cert.MultiStark.DisjointIntervals (ivlsOf w)) →
                  (∀ (w : ℕ),
                      ∑ x, (List.filter (fun e => decide (e.2.length = w ∧ e.1 = x)) rom.entries).length + 1 <
                        CertiFri.P3.Goldilocks.order) →
                    (∀ (w : ℕ) (x : Ix.Cert.MultiStark.Fp),
                        ↑(List.filter (fun e => decide (e.2.length = w ∧ e.1 = x)) rom.entries).length -
                              ↑(List.filter (fun e => decide (e.2.length = w ∧ e.1 = x - 1)) rom.entries).length +
                            Ix.Cert.MultiStark.memsegBoundary (ivlsOf w) x =
                          0) →
                      ∀ (allowedDig outClaimDig : Fin 8 → Ix.Cert.MultiStark.Fp)
                        {result : Aiur.Value Ix.Cert.MultiStark.Fp}
                        {wires : List (Aiur.WireValue Ix.Cert.MultiStark.Fp)}
                        {output : Aiur.WireValue Ix.Cert.MultiStark.Fp},
                        Aiur.Circuit.Erasure.Signed compiled.circuit.system
                            { channel := entry.resolved.name, args := wires, result := output } →
                          ∀ {root : Aiur.Circuit.Message Ix.Cert.MultiStark.Fp},
                            Aiur.Optimized.Depth.erase cfg root =
                                Aiur.Circuit.Erasure.message compiled.circuit.system
                                  { channel := entry.resolved.name, args := wires, result := output } →
                              root.channel ∉ cfg.names →
                                ∀ (rows : List (Aiur.Circuit.Row Ix.Cert.MultiStark.Fp)),
                                  rows.length ≤ 2 ^ 39 →
                                    ∀
                                      (inspected :
                                        List
                                          (Option
                                            (Aiur.Circuit.RuleClaims (Aiur.Circuit.Message Ix.Cert.MultiStark.Fp)))),
                                      (Aiur.Optimized.Depth.system cfg physical.system).checkContext
                                            (Aiur.Circuit.Erasure.rawROM rom) root =
                                          Except.ok () →
                                        List.mapM (plan.inspectRow (Aiur.Circuit.Erasure.rawROM rom)) rows =
                                            Except.ok inspected →
                                          (Aiur.Circuit.Balance.required
                                                  (fun c =>
                                                    decide
                                                      ((Aiur.Optimized.Depth.system cfg physical.system).MapClaim c))
                                                  root (Aiur.Optimized.Grouping.activeRules inspected)).length <
                                              CertiFri.P3.Goldilocks.order →
                                            ∀
                                              (provWeight :
                                                Aiur.Circuit.RuleClaims (Aiur.Circuit.Message Ix.Cert.MultiStark.Fp) →
                                                  Ix.Cert.MultiStark.Fp),
                                              (∀
                                                  claim ∈
                                                    Aiur.Circuit.Balance.required
                                                      (fun c =>
                                                        decide
                                                          ((Aiur.Optimized.Depth.system cfg physical.system).MapClaim
                                                            c))
                                                      root (Aiur.Optimized.Grouping.activeRules inspected),
                                                  (List.map provWeight
                                                        (List.filter (fun r => decide (r.1 = claim))
                                                          (Aiur.Optimized.Grouping.activeRules inspected))).sum =
                                                    ↑(List.countP (fun x => decide (x = claim))
                                                        (Aiur.Circuit.Balance.required
                                                          (fun c =>
                                                            decide
                                                              ((Aiur.Optimized.Depth.system cfg
                                                                    physical.system).MapClaim
                                                                c))
                                                          root (Aiur.Optimized.Grouping.activeRules inspected)))) →
                                                Aiur.DecodesValues compiled.specialized.program.enums wires
                                                    (Aiur.entryValues
                                                      [Ix.Cert.MultiStarkRefinement.digest8SourceValue allowedDig,
                                                        Ix.Cert.MultiStarkRefinement.digest8SourceValue outClaimDig]) →
                                                  Aiur.WireValue.decode compiled.specialized.program.enums output =
                                                      some result →
                                                    ∀
                                                      {sem :
                                                        Aggr.AggrSemantics Address Address Ix.DynamicLink.EvalAssumption
                                                          Address Ix.Cert.MultiStark.K
                                                          Ix.DynamicLink.DynamicLinkStatement
                                                          Ix.DynamicLink.LinkedCircuitEntry}
                                                      {batchClaim :
                                                        ℕ →
                                                          Aggr.ValidatorMode Address →
                                                            (Address → Prop) →
                                                              (Address → Prop) →
                                                                (Address → Prop) →
                                                                  (Ix.DynamicLink.EvalAssumption → Prop) → Prop}
                                                      {rootStmt :
                                                        Aggr.AggrNodeStmt Address Address Ix.DynamicLink.EvalAssumption
                                                          Address Ix.Cert.MultiStark.K
                                                          Ix.DynamicLink.DynamicLinkStatement
                                                          Ix.DynamicLink.LinkedCircuitEntry}
                                                      (t : Ix.Cert.Aggr.AcceptedAggrTree sem batchClaim rootStmt)
                                                      (nodeProbs : List ℝ) {ε : ℝ},
                                                      nodeProbs.length = t.verificationCount →
                                                        (∀ p ∈ nodeProbs, p ≤ ε) →
                                                          Ix.Cert.MultiStarkRefinement.RecursionVerifierAstPinned
                                                                MultiStark.recursionProgram =
                                                              true ∧
                                                            Ix.Cert.Aggr.AggregateProgramAstPinned
                                                                  MultiStark.aggregateProgram =
                                                                true ∧
                                                              (∃ value heap calls,
                                                                  prepared.ObsFn Ix.Cert.Aggr.ixAggrEntry
                                                                      [Ix.Cert.MultiStarkRefinement.digest8SourceValue
                                                                          allowedDig,
                                                                        Ix.Cert.MultiStarkRefinement.digest8SourceValue
                                                                          outClaimDig]
                                                                      value heap calls ∧
                                                                    Aiur.Represents (compiled.traceROM rom) heap value
                                                                        result ∧
                                                                      Aiur.Generic.SourceSemantics.CallsInROM
                                                                        (compiled.traceROM rom) calls) ∧
                                                                nodeProbs.sum ≤ ↑t.verificationCount * ε ∧
                                                                  Aggr.AggrNodeHolds sem rootStmt ∧
                                                                    (t.HasTreeCollision ∨
                                                                      ∀ vp ∈ t.childProofs,
                                                                        ∃ proofBytes,
                                                                          Ix.Cert.MultiStark.verifyBatchBytes vp.vkBytes
                                                                              vp.claimsBytes proofBytes =
                                                                            true) -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.aggregated_root_sound
/-- info: @Ix.Cert.Aggr.aggregated_root_checkEnv_sound : ∀
  {sem :
    Aggr.AggrSemantics Address Address Ix.DynamicLink.EvalAssumption Address Ix.Cert.MultiStark.K
      Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry}
  {batchClaim :
    ℕ →
      Aggr.ValidatorMode Address →
        (Address → Prop) → (Address → Prop) → (Address → Prop) → (Ix.DynamicLink.EvalAssumption → Prop) → Prop}
  {Valid : Address → (Address → Prop) → Address → Prop},
  (WellFounded fun y x => sem.Dep x y) →
    (∀ (b : Address) (Ax : Address → Prop) (x : Address),
        sem.Checked b Ax (fun x => False) (fun x => False) x →
          (∀ (y : Address), sem.Dep x y → Valid b Ax y) → Valid b Ax x) →
      ∀ {mode : Aggr.ValidatorMode Address} {S Ax : Address → Prop},
        mode.isBindingDischarged = true →
          ∀
            (t :
              Ix.Cert.Aggr.AcceptedAggrTree sem batchClaim
                (Aggr.AggrNodeStmt.checkEnv mode S (fun x => False) Ax (fun x => False) fun x => False)),
            (∀ (x : Address), S x → Valid mode.bindingOf Ax x) ∧
              t.dynamicLinkDischarges = 0 ∧
                (t.HasTreeCollision ∨
                  ∀ vp ∈ t.childProofs,
                    ∃ proofBytes, Ix.Cert.MultiStark.verifyBatchBytes vp.vkBytes vp.claimsBytes proofBytes = true) -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.aggregated_root_checkEnv_sound
/-- info: Ix.Cert.Aggr.aggregated_root_checkEnv_no_axioms_model : ∀ (W : Type u_1) [Ix.Kernel.SetTheory W]
  {sem :
    Aggr.AggrSemantics Address Address Ix.DynamicLink.EvalAssumption Address Ix.Cert.MultiStark.K
      Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry}
  {batchClaim :
    ℕ →
      Aggr.ValidatorMode Address →
        (Address → Prop) → (Address → Prop) → (Address → Prop) → (Ix.DynamicLink.EvalAssumption → Prop) → Prop}
  {b : Address} {S : Address → Prop} {callsA callsB : List (Aiur.Generic.SourceSemantics.Call IxVM.F)}
  {dA dB : IxVM.Refinement.Digest},
  IxVM.Consistency.ComposedSpec callsA callsB dA dB →
    ∀ {bytesB : ByteArray} {spec : Address},
      Ix.Claim.de bytesB = Except.ok (Ix.Claim.binding spec b) →
        IxVM.Refinement.packDigest (Address.blake3Pure bytesB) = dB →
          ∀ {bytesA : ByteArray} {cA : Ix.Claim},
            Ix.Claim.de bytesA = Except.ok cA →
              IxVM.Refinement.packDigest (Address.blake3Pure bytesA) = dA →
                IxVM.Consistency.InScopeTyping cA →
                  ∀ {ctx : Ix.ClaimContext},
                    cA.context? = some ctx →
                      ctx.binding = b →
                        ∀ {V : IxVM.Refinement.View} {seeds : List Address},
                          IxVM.Consistency.ClaimSeeds cA V seeds →
                            (∀ (x : Address), S x ↔ x ∈ seeds) →
                              ∀
                                (t :
                                  Ix.Cert.Aggr.AcceptedAggrTree sem batchClaim
                                    (Aggr.AggrNodeStmt.checkEnv (Aggr.ValidatorMode.validated b) S (fun x => False)
                                      (fun x => False) (fun x => False) fun x => False)),
                                (∀ (x : Address),
                                    S x →
                                      sem.Checked b (fun x => False) (fun x => False) (fun x => False) x) ∧
                                  (∀ (x y : Address), S x → sem.Dep x y → S y) ∧
                                    (∀ (x : Address), S x ↔ x ∈ seeds) ∧
                                      t.dynamicLinkDischarges = 0 ∧
                                        (t.HasTreeCollision ∨
                                            ∀ vp ∈ t.childProofs,
                                              ∃ proofBytes,
                                                Ix.Cert.MultiStark.verifyBatchBytes vp.vkBytes vp.claimsBytes
                                                    proofBytes =
                                                  true) ∧
                                          (V.HashedCollision (bytesA :: bytesB :: IxVM.Consistency.committedFootprint)
                                              (callsA ++ callsB) ∨
                                            IxVM.Consistency.ComposedWith
                                              (fun tRole R x => IxVM.Consistency.SeedsNotFalse callsA tRole R seeds)
                                              callsB b) -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.aggregated_root_checkEnv_no_axioms_model
/-- info: @Ix.Cert.Aggr.aggregated_root_linked_checkEnv_sound : ∀
  {sem :
    Aggr.AggrSemantics Address Address Ix.DynamicLink.EvalAssumption Address Ix.Cert.MultiStark.K
      Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry}
  {batchClaim :
    ℕ →
      Aggr.ValidatorMode Address →
        (Address → Prop) → (Address → Prop) → (Address → Prop) → (Ix.DynamicLink.EvalAssumption → Prop) → Prop}
  {Valid : Address → (Address → Prop) → (Ix.DynamicLink.LinkedCircuitEntry → Prop) → Address → Prop},
  (WellFounded fun y x => sem.Dep x y) →
    (∀ (b : Address) (Ax : Address → Prop) (Linked : Ix.DynamicLink.LinkedCircuitEntry → Prop) (x : Address),
        sem.Checked b Ax (fun x => False) Linked x →
          (∀ (y : Address), sem.Dep x y → Valid b Ax Linked y) → Valid b Ax Linked x) →
      ∀ {b : Address} {S Ax : Address → Prop} {Linked : Ix.DynamicLink.LinkedCircuitEntry → Prop}
        (t :
          Ix.Cert.Aggr.AcceptedAggrTree sem batchClaim
            (Aggr.AggrNodeStmt.checkEnv (Aggr.ValidatorMode.linked b) S (fun x => False) Ax (fun x => False) Linked)),
        (∀ (x : Address), S x → Valid b Ax Linked x) ∧
          (t.HasTreeCollision ∨
            ∀ vp ∈ t.childProofs,
              ∃ proofBytes, Ix.Cert.MultiStark.verifyBatchBytes vp.vkBytes vp.claimsBytes proofBytes = true) -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.aggregated_root_linked_checkEnv_sound
/-- info: @Ix.Cert.Aggr.aggregated_root_catalog_sound : ∀
  {sem :
    Aggr.AggrSemantics Address Address Ix.DynamicLink.EvalAssumption Address Ix.Cert.MultiStark.K
      Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry}
  {batchClaim :
    ℕ →
      Aggr.ValidatorMode Address →
        (Address → Prop) → (Address → Prop) → (Address → Prop) → (Ix.DynamicLink.EvalAssumption → Prop) → Prop}
  {Valid : Address → (Address → Prop) → Address → Prop},
  (WellFounded fun y x => sem.Dep x y) →
    (∀ (b : Address) (Ax : Address → Prop) (x : Address),
        sem.Checked b Ax (fun x => False) (fun x => False) x →
          (∀ (y : Address), sem.Dep x y → Valid b Ax y) → Valid b Ax x) →
      ∀ {members : Address × (Address → Prop) × (Address → Prop) → Prop}
        (t : Ix.Cert.Aggr.AcceptedAggrTree sem batchClaim (Aggr.AggrNodeStmt.catalogStmt members)),
        (∀ (b : Address) (S Ax : Address → Prop), members (b, S, Ax) → ∀ (x : Address), S x → Valid b Ax x) ∧
          (t.HasTreeCollision ∨
            ∀ vp ∈ t.childProofs,
              ∃ proofBytes, Ix.Cert.MultiStark.verifyBatchBytes vp.vkBytes vp.claimsBytes proofBytes = true) -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.aggregated_root_catalog_sound
/-- info: @Ix.Cert.Aggr.aggregated_root_dynamicLink_sound : ∀ {α β : Type} {accepts : Ix.DynamicLink.TraceRelation}
  {sem :
    Aggr.AggrSemantics Address Address Ix.DynamicLink.EvalAssumption Address Ix.Cert.MultiStark.K
      Ix.DynamicLink.DynamicLinkStatement Ix.DynamicLink.LinkedCircuitEntry}
  {batchClaim :
    ℕ →
      Aggr.ValidatorMode Address →
        (Address → Prop) → (Address → Prop) → (Address → Prop) → (Ix.DynamicLink.EvalAssumption → Prop) → Prop}
  {s : Ix.DynamicLink.DynamicLinkStatement},
  (sem.DynamicLinkValid s → accepts s.circuit.vkDigest s.circuit.entryIdx s.expectedMultiStarkClaim) →
    ∀ {encode : α → β → Array UInt64} {R : α → β → Prop} {x : α} {y : β},
      encode x y = s.expectedMultiStarkClaim →
        Ix.DynamicLink.EvalSound accepts s.circuit.vkDigest s.circuit.entryIdx encode R →
          ∀ (t : Ix.Cert.Aggr.AcceptedAggrTree sem batchClaim (Aggr.AggrNodeStmt.dynamicLinkStmt s)),
            R x y ∧
              (t.HasTreeCollision ∨
                ∀ vp ∈ t.childProofs,
                  ∃ proofBytes, Ix.Cert.MultiStark.verifyBatchBytes vp.vkBytes vp.claimsBytes proofBytes = true) -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.aggregated_root_dynamicLink_sound
/-- info: 'Ix.Cert.Aggr.acceptedAggrTree_refines_derivation19' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.acceptedAggrTree_refines_derivation19
/-- info: 'Ix.Cert.Aggr.acceptedAggrTree_unlinked_zero_dynamicLinkDischarges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.acceptedAggrTree_unlinked_zero_dynamicLinkDischarges
/-- info: 'Ix.Cert.Aggr.aggregated_root_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.aggregated_root_sound
/-- info: 'Ix.Cert.Aggr.aggregated_root_checkEnv_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.aggregated_root_checkEnv_sound
/-- info: 'Ix.Cert.Aggr.aggregated_root_checkEnv_no_axioms_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.aggregated_root_checkEnv_no_axioms_model
/-- info: 'Ix.Cert.Aggr.aggregated_root_linked_checkEnv_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.aggregated_root_linked_checkEnv_sound
/-- info: 'Ix.Cert.Aggr.aggregated_root_catalog_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.aggregated_root_catalog_sound
/-- info: 'Ix.Cert.Aggr.aggregated_root_dynamicLink_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.aggregated_root_dynamicLink_sound

-- 5. Negative Controls (Weak Envelope, Deceptive High-Blowup UD Envelope, `A7` Dropped Axiom,
--    Shape 18 Undischarged Eval, Shape 18 Mode 3a No Erasure)
/-- info: Ix.Cert.Aggr.negative_control_weak_security_envelope : ¬Ix.Cert.Aggr.SecurityEnvelopeOk
    Ix.Cert.Aggr.weakExternalStarkParams -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.negative_control_weak_security_envelope
/-- info: Ix.Cert.Aggr.negative_control_deceptive_high_blowup_envelope : ¬Ix.Cert.Aggr.SecurityEnvelopeOk
    Ix.Cert.Aggr.deceptiveHighBlowupParams -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.negative_control_deceptive_high_blowup_envelope
/-- info: Ix.Cert.Aggr.negative_control_a7_dropped_axiom : ∀ (a₀ : Address),
  ¬Aggr.AxiomMergeRel (fun a => a = a₀) (fun x => False) fun x => False -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.negative_control_a7_dropped_axiom
/-- info: @Ix.Cert.Aggr.negative_control_shape18_undischarged_eval : ∀ {e₀ e₁ : Ix.DynamicLink.EvalAssumption},
  e₁ ≠ e₀ → ¬Aggr.EvalRemoveRel (fun e => e = e₀ ∨ e = e₁) (fun x => False) e₀ -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.negative_control_shape18_undischarged_eval
/-- info: Ix.Cert.Aggr.negative_control_mode3a_cannot_erase_linked : ∀ (LinkedBefore : Ix.DynamicLink.LinkedCircuitEntry → Prop)
  (entry : Ix.DynamicLink.LinkedCircuitEntry),
  (¬Aggr.LinkedMergeRel LinkedBefore entry fun x => False) ∧
    ∀ (m out : Aggr.ValidatorMode Address),
      m.toLinkedMode = some out → out.isLinked = true ∧ out.validatorCode ≠ 3 ∧ out.validatorCode ≠ 4 -/
#guard_msgs (whitespace := lax) in #check @Ix.Cert.Aggr.negative_control_mode3a_cannot_erase_linked
/-- info: 'Ix.Cert.Aggr.negative_control_weak_security_envelope' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.negative_control_weak_security_envelope
/-- info: 'Ix.Cert.Aggr.negative_control_deceptive_high_blowup_envelope' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.negative_control_deceptive_high_blowup_envelope
/-- info: 'Ix.Cert.Aggr.negative_control_a7_dropped_axiom' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.negative_control_a7_dropped_axiom
/-- info: 'Ix.Cert.Aggr.negative_control_shape18_undischarged_eval' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.negative_control_shape18_undischarged_eval
/-- info: 'Ix.Cert.Aggr.negative_control_mode3a_cannot_erase_linked' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Ix.Cert.Aggr.negative_control_mode3a_cannot_erase_linked
