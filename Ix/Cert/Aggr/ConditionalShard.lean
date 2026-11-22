import Ix.IxVM.Consistency.TableValid
import Ix.DynamicLink.Soundness
import Ix.Aggr.Verification

/-! # Conditional Shard Soundness Companion (`Ix.Cert.Aggr.ConditionalShard`)

Companion generalization of frozen `IxVM.Consistency.CircuitComposed` (leaving every
frozen file in `Ix/IxVM/` and `IxC/Kernel/` completely untouched!) that tracks:
- assumed dependency leaves `A : Address → Prop` (discharged by aggregation Shapes `2–9`, `15`),
- explicit user axiom sets `Ax : Address → Prop` (merged monotonically via `A7` across
  pair/wrap/cross-binding/discharge shapes), and
- Tier 2 `evalAssumptions` `EvalA : Ix.DynamicLink.EvalAssumption → Prop` (discharged leaf by
  leaf via aggregation Shape `18` using Mode 2 `@Eq` `Claim.check` or Mode 3a Shape `17`
  `DynamicLinkStatement` recording `LinkedCircuitEntry` under validators `12`/`13`; Mode 1
  `Claim.eval` is disabled in 0.4).

When `A = ∅`, `Ax = ∅`, and `EvalA = ∅`, `ConditionalChecked` yields unconditional `TargetValid`,
specializing directly to frozen `IxVM.Consistency.ComposedSpec` / `ConsistentReadOver` — giving
a model in every set theory `∀ W [Ix.Kernel.SetTheory W], Nonempty (Ix.Kernel.Model W (claimedEnv env))`
and guaranteeing no claimed constant has type `False`.

Zero `sorry`, zero `native_decide`, zero `bv_decide`, standard axioms only.
-/

universe u

namespace Ix.Cert.Aggr

open IxVM.Consistency IxVM.Refinement
open Ix.DynamicLink
open _root_.Aggr

/-! ## 1. Grounded `EvalAssumption` Dischargers (Shape-18 Mode 2, Mode 1 Helper, & Mode 3a) -/

/-- Semantic validity of an `EvalAssumption` leaf `e` in a kernel environment `env`:
`e` is grounded into `Ix.DynamicLink.GroundedEval env` (`DefEq` and `Red` at every depth). -/
structure EvalLeafSound (env : Ix.Kernel.Env .anon)
    (interpExpr : Address → Ix.Kernel.Expr .anon) (e : EvalAssumption) : Prop where
  grounded : GroundedEval env (interpExpr e.lhs) (interpExpr e.rhs) (interpExpr e.typ)

/-- **Mode-2 Discharge (`@Eq` `Claim.check`, tag `228`):** a closed kernel proof `p` of
`@Eq.{u} typ lhs rhs` establishes `EvalLeafSound` via `Ix.DynamicLink.groundedEval_of_eqProof`. -/
theorem evalLeafSound_of_eqProof
    {env : Ix.Kernel.Env .anon} {interpExpr : Address → Ix.Kernel.Expr .anon}
    {e : EvalAssumption} {p ta tb sT : Ix.Kernel.Expr .anon}
    {lvlU lvlV : Ix.Kernel.Level} {ci : Ix.Kernel.ConstantInfo .anon}
    (hEq : env.find? Ix.Kernel.eqName = some ci)
    (hlhs_f : (interpExpr e.lhs).hasFvar = false)
    (hlhs_b : (interpExpr e.lhs).looseBVarsBounded 0 = true)
    (hrhs_f : (interpExpr e.rhs).hasFvar = false)
    (hrhs_b : (interpExpr e.rhs).looseBVarsBounded 0 = true)
    (hp_f : p.hasFvar = false) (hp_b : p.looseBVarsBounded 0 = true)
    (hp : Ix.Kernel.Rules.Infer env .full 0 p
      (.app (.app (.app (.const Ix.Kernel.eqName [lvlU]) (interpExpr e.typ))
        (interpExpr e.lhs)) (interpExpr e.rhs)))
    (hlhs : Ix.Kernel.Rules.Infer env .full 0 (interpExpr e.lhs) ta)
    (hta : Ix.Kernel.Rules.DefEq env 0 ta (interpExpr e.typ))
    (hrhs : Ix.Kernel.Rules.Infer env .full 0 (interpExpr e.rhs) tb)
    (htb : Ix.Kernel.Rules.DefEq env 0 tb (interpExpr e.typ))
    (htyp : Ix.Kernel.Rules.Infer env .full 0 (interpExpr e.typ) sT)
    (hsT : Ix.Kernel.Rules.Red env 0 sT (.sort lvlV))
    (huv : ∀ φ : Ix.Kernel.LevelParam → Nat,
      Ix.Kernel.Level.eval φ lvlV = Ix.Kernel.Level.eval φ lvlU) :
    EvalLeafSound env interpExpr e :=
  ⟨groundedEval_of_eqProof hEq hlhs_f hlhs_b hrhs_f hrhs_b hp_f hp_b
    hp hlhs hta hrhs htb htyp hsT huv⟩

/-- **Mode-1 Helper (`Claim.eval`, tag `227` — disabled in 0.4):** a closed conversion
`DefEq env 0 lhs rhs` establishes `EvalLeafSound` via `Ix.DynamicLink.groundedEval_of_closedDefEq`. -/
theorem evalLeafSound_of_closedDefEq
    {env : Ix.Kernel.Env .anon} {interpExpr : Address → Ix.Kernel.Expr .anon}
    {e : EvalAssumption} {ta tb : Ix.Kernel.Expr .anon}
    (hlhs_f : (interpExpr e.lhs).hasFvar = false)
    (hlhs_b : (interpExpr e.lhs).looseBVarsBounded 0 = true)
    (hrhs_f : (interpExpr e.rhs).hasFvar = false)
    (hrhs_b : (interpExpr e.rhs).looseBVarsBounded 0 = true)
    (hlhs_lvl : (interpExpr e.lhs).allLevelParamsDefined [] = true)
    (hrhs_lvl : (interpExpr e.rhs).allLevelParamsDefined [] = true)
    (hlhs_inst : (interpExpr e.lhs).instantiateLevelParams [] [] = interpExpr e.lhs)
    (hrhs_inst : (interpExpr e.rhs).instantiateLevelParams [] [] = interpExpr e.rhs)
    (hlhs : Ix.Kernel.Rules.Infer env .full 0 (interpExpr e.lhs) ta)
    (hta : Ix.Kernel.Rules.DefEq env 0 ta (interpExpr e.typ))
    (hrhs : Ix.Kernel.Rules.Infer env .full 0 (interpExpr e.rhs) tb)
    (htb : Ix.Kernel.Rules.DefEq env 0 tb (interpExpr e.typ))
    (hdef : Ix.Kernel.Rules.DefEq env 0 (interpExpr e.lhs) (interpExpr e.rhs)) :
    EvalLeafSound env interpExpr e :=
  ⟨groundedEval_of_closedDefEq hlhs_f hlhs_b hrhs_f hrhs_b
    hlhs_lvl hrhs_lvl hlhs_inst hrhs_inst hlhs hta hrhs htb hdef⟩

/-- **Mode-3a Reification Helper (Shape 17 `DynamicLinkStatement`, tag `232`):** an accepted
external Multi-STARK accelerator trace plus its IxVM-verified soundness bridge `EvalSound`
reifies directly to `EvalLeafSound` via `Ix.DynamicLink.reify_accepted_eval_trace`. -/
theorem evalLeafSound_of_dynamicLink {accepts : TraceRelation}
    {env : Ix.Kernel.Env .anon} {interpExpr : Address → Ix.Kernel.Expr .anon}
    {s : DynamicLinkStatement} {e : EvalAssumption}
    {encode : Address → Address → Array UInt64}
    (hTrace : accepts s.circuit.vkDigest s.circuit.entryIdx s.expectedMultiStarkClaim)
    (hEnc : encode e.lhs e.rhs = s.expectedMultiStarkClaim)
    (hBridge : EvalSound accepts s.circuit.vkDigest s.circuit.entryIdx encode
      (fun lhs rhs => GroundedEval env (interpExpr lhs) (interpExpr rhs) (interpExpr e.typ))) :
    EvalLeafSound env interpExpr e :=
  ⟨reify_accepted_eval_trace
    (R := fun lhs rhs => GroundedEval env (interpExpr lhs) (interpExpr rhs) (interpExpr e.typ))
    hTrace hEnc hBridge⟩

/-! ## 2. Conditional Shard Judgment (`ConditionalChecked`) & Axiom/Eval Laws -/

/-- A conditional `EvalAssumption` discharger under binding/class `b` and user axioms `Ax`:
whenever every user axiom in `Ax` holds under `AxHolds b`, `EvalHolds b e` holds. -/
def ConditionalEvalValid (AxHolds : Address → Address → Prop)
    (EvalHolds : Address → EvalAssumption → Prop)
    (b : Address) (Ax : Address → Prop) (e : EvalAssumption) : Prop :=
  (∀ a, Ax a → AxHolds b a) → EvalHolds b e

/-- A conditional validity judgment for a subject constant `x : Address` under:
- binding / literal-class key `b : Address`,
- explicit user axiom set `Ax : Address → Prop`, and
- Tier 2 `evalAssumptions` `EvalA : EvalAssumption → Prop`.

Whenever every axiom in `Ax` satisfies `AxHolds b` and every eval assumption in `EvalA`
satisfies `EvalHolds b`, the subject `x` satisfies `TargetValid b x`. -/
def ConditionalChecked (AxHolds : Address → Address → Prop)
    (EvalHolds : Address → EvalAssumption → Prop)
    (TargetValid : Address → Address → Prop)
    (b : Address) (Ax : Address → Prop) (EvalA : EvalAssumption → Prop) (x : Address) : Prop :=
  (∀ a, Ax a → AxHolds b a) →
  (∀ e, EvalA e → EvalHolds b e) →
  TargetValid b x

/-- `A7` Axiom Monotonicity for `ConditionalEvalValid`. -/
theorem conditionalEvalValid_mono_ax
    {AxHolds : Address → Address → Prop}
    {EvalHolds : Address → EvalAssumption → Prop}
    {b : Address} {Ax₁ Ax₂ : Address → Prop} {e : EvalAssumption}
    (hSub : ∀ a, Ax₁ a → Ax₂ a)
    (hE : ConditionalEvalValid AxHolds EvalHolds b Ax₁ e) :
    ConditionalEvalValid AxHolds EvalHolds b Ax₂ e :=
  fun hAx2 => hE (fun a ha => hAx2 a (hSub a ha))

/-- `A7` Axiom Monotonicity for `ConditionalChecked`. -/
theorem conditionalChecked_mono_ax
    {AxHolds : Address → Address → Prop}
    {EvalHolds : Address → EvalAssumption → Prop}
    {TargetValid : Address → Address → Prop}
    {b : Address} {Ax₁ Ax₂ : Address → Prop} {EvalA : EvalAssumption → Prop} {x : Address}
    (hSub : ∀ a, Ax₁ a → Ax₂ a)
    (hC : ConditionalChecked AxHolds EvalHolds TargetValid b Ax₁ EvalA x) :
    ConditionalChecked AxHolds EvalHolds TargetValid b Ax₂ EvalA x :=
  fun hAx2 hEvals => hC (fun a ha => hAx2 a (hSub a ha)) hEvals

/-- Shape 18 Single-Leaf Discharge for `ConditionalChecked`: removing a valid `EvalAssumption`
leaf `e₀` via `EvalRemoveRel` preserves `ConditionalChecked`. -/
theorem conditionalChecked_discharge_eval
    {AxHolds : Address → Address → Prop}
    {EvalHolds : Address → EvalAssumption → Prop}
    {TargetValid : Address → Address → Prop}
    {b : Address} {Ax : Address → Prop}
    {EvalBefore EvalAfter : EvalAssumption → Prop} {e₀ : EvalAssumption} {x : Address}
    (hRem : EvalRemoveRel EvalBefore EvalAfter e₀)
    (hE : ConditionalEvalValid AxHolds EvalHolds b Ax e₀)
    (hC : ConditionalChecked AxHolds EvalHolds TargetValid b Ax EvalBefore x) :
    ConditionalChecked AxHolds EvalHolds TargetValid b Ax EvalAfter x := by
  intro hAx hAfter
  apply hC hAx
  intro e he
  rcases (hRem.before_iff e).mp he with rfl | hmem
  · exact hE hAx
  · exact hAfter e hmem

/-- **Unconditional Specialization (`Ax = ∅`, `EvalA = ∅`):**
When both user axioms and eval assumptions are empty, `ConditionalChecked` immediately
yields unconditional `TargetValid b x`! -/
theorem conditionalChecked_unconditional
    {AxHolds : Address → Address → Prop}
    {EvalHolds : Address → EvalAssumption → Prop}
    {TargetValid : Address → Address → Prop}
    {b x : Address}
    (hC : ConditionalChecked AxHolds EvalHolds TargetValid b (fun _ => False) (fun _ => False) x) :
    TargetValid b x :=
  hC (fun _ h => h.elim) (fun _ h => h.elim)

/-- Conditional validity judgment tracking user axioms `Ax`, remaining `evalAssumptions` `EvalA`,
AND Mode-3a `linkedCircuits` (`Linked : LinkedCircuitEntry → Prop`). -/
def ConditionalCheckedWithLinks (AxHolds : Address → Address → Prop)
    (EvalHolds : Address → EvalAssumption → Prop)
    (LinkHolds : Address → LinkedCircuitEntry → Prop)
    (TargetValid : Address → Address → Prop)
    (b : Address) (Ax : Address → Prop) (EvalA : EvalAssumption → Prop)
    (Linked : LinkedCircuitEntry → Prop) (x : Address) : Prop :=
  (∀ a, Ax a → AxHolds b a) →
  (∀ e, EvalA e → EvalHolds b e) →
  (∀ l, Linked l → LinkHolds b l) →
  TargetValid b x

/-- Shape 18 Mode 3a discharge for `ConditionalCheckedWithLinks`: discharging `e₀` via
a dynamically linked circuit `entry` records `entry` into `LinkedAfter` (`LinkedMergeRel`)
without any unverified `DynamicLinkValid → EvalValid` implication. -/
theorem conditionalCheckedWithLinks_discharge_via_link
    {AxHolds : Address → Address → Prop}
    {EvalHolds : Address → EvalAssumption → Prop}
    {LinkHolds : Address → LinkedCircuitEntry → Prop}
    {TargetValid : Address → Address → Prop}
    {b : Address} {Ax : Address → Prop}
    {EvalBefore EvalAfter : EvalAssumption → Prop}
    {LinkedBefore LinkedAfter : LinkedCircuitEntry → Prop}
    {e₀ : EvalAssumption} {entry : LinkedCircuitEntry} {x : Address}
    (hRem : EvalRemoveRel EvalBefore EvalAfter e₀)
    (hMerge : LinkedMergeRel LinkedBefore entry LinkedAfter)
    (hEntryCovers : LinkHolds b entry → EvalHolds b e₀)
    (hC : ConditionalCheckedWithLinks AxHolds EvalHolds LinkHolds TargetValid b Ax EvalBefore LinkedBefore x) :
    ConditionalCheckedWithLinks AxHolds EvalHolds LinkHolds TargetValid b Ax EvalAfter LinkedAfter x := by
  intro hAx hAfter hLinkedAfter
  apply hC hAx _ (fun l hl => hLinkedAfter l (hMerge.prev_sub hl))
  intro e he
  rcases (hRem.before_iff e).mp he with rfl | hmem
  · exact hEntryCovers (hLinkedAfter entry hMerge.entry_mem)
  · exact hAfter e hmem

/-- **Unconditional Zero-Link Specialization (`Ax = ∅`, `EvalA = ∅`, `Linked = ∅`):**
When user axioms, eval assumptions, and linked circuits are all empty (validators `3`/`5`),
`ConditionalCheckedWithLinks` yields unconditional `TargetValid b x` with zero external circuits. -/
theorem conditionalCheckedWithLinks_unconditional
    {AxHolds : Address → Address → Prop}
    {EvalHolds : Address → EvalAssumption → Prop}
    {LinkHolds : Address → LinkedCircuitEntry → Prop}
    {TargetValid : Address → Address → Prop}
    {b x : Address}
    (hC : ConditionalCheckedWithLinks AxHolds EvalHolds LinkHolds TargetValid b
      (fun _ => False) (fun _ => False) (fun _ => False) x) :
    TargetValid b x :=
  hC (fun _ h => h.elim) (fun _ h => h.elim) (fun _ h => h.elim)

/-! ## 3. Companion Bridge to Frozen `IxVM.Consistency.ComposedSpec` (`CircuitComposed`) -/

/-- Set-theoretic model conclusion for a set of claimed seeds `seeds : List Address` under
binding `a : Address`, extracted directly from frozen `IxVM.Consistency.ComposedSpec`.
Either a BLAKE3 collision occurred in `callsA ++ callsB`, OR there exists a verified role table
`t` at `a` and a consistent environment extending `envT` that covers `seeds` and has a model in
every set theory `∀ W [Ix.Kernel.SetTheory W], Nonempty (Ix.Kernel.Model W (claimedEnv env))`
(so no claimed seed has type `False`). -/
def ComposedModelConclusion (callsA callsB : List (Aiur.Generic.SourceSemantics.Call IxVM.F))
    (bytesA bytesB : ByteArray) (V : View) (a : Address) (seeds : List Address) : Prop :=
  V.HashedCollision (bytesA :: bytesB :: committedFootprint) (callsA ++ callsB) ∨
    ∃ (tb : ByteArray) (t : Ix.Kernel.RoleTable) (R : Ixon.Env)
      (envT : Ix.Kernel.Env .anon),
      Hashed callsB tb ∧
      Ix.Kernel.Admission.admitBinding Address.admissionHash ⟨a, tb⟩ = .ok t ∧
      AllBound t ∧ LoadedBy callsB R ∧ TableShape.{u} t (fun _ => True) R envT ∧
      ConsistentReadOver.{u} callsA t R envT seeds

/-- **Specialization Theorem (`composedModelConclusion_of_composedSpec`):**
Any unconditional in-scope `check`/`checkEnv` claim (no user axioms, no assumed leaves, no eval
assumptions) paired with its `binding` claim under frozen `IxVM.Consistency.ComposedSpec`
immediately satisfies `ComposedModelConclusion` — and hence `∀ W [SetTheory W], Nonempty (Model W _)`
and `seeds_not_false`! -/
theorem composedModelConclusion_of_composedSpec
    {callsA callsB : List (Aiur.Generic.SourceSemantics.Call IxVM.F)} {dA dB : Digest}
    (hComp : ComposedSpec.{u} callsA callsB dA dB)
    {bytesB : ByteArray} {spec a : Address}
    (hdeB : Ix.Claim.de bytesB = .ok (.binding spec a))
    (hdB : packDigest (Address.blake3Pure bytesB) = dB)
    {bytesA : ByteArray} {cA : Ix.Claim}
    (hdeA : Ix.Claim.de bytesA = .ok cA)
    (hdA : packDigest (Address.blake3Pure bytesA) = dA)
    (hsc : InScopeTyping cA)
    {ctx : Ix.ClaimContext} (hctx : cA.context? = some ctx) (hba : ctx.binding = a)
    {V : View} {seeds : List Address} (hseeds : ClaimSeeds cA V seeds) :
    ComposedModelConclusion.{u} callsA callsB bytesA bytesB V a seeds :=
  hComp bytesB spec a hdeB hdB bytesA cA hdeA hdA hsc ctx hctx hba V seeds hseeds

/-- **No Claimed Constant Has Type `False` (via frozen `ConsistentReadOver.seeds_not_false`):**
From `ComposedModelConclusion` (in the no-collision branch), every set theory `W` models the
claimed environment and `SeedsNotFalse callsA t R seeds` holds. -/
theorem composedModelConclusion_no_false (W : Type u) [Ix.Kernel.SetTheory W]
    {callsA callsB : List (Aiur.Generic.SourceSemantics.Call IxVM.F)}
    {bytesA bytesB : ByteArray} {V : View} {a : Address} {seeds : List Address}
    (h : ComposedModelConclusion.{u} callsA callsB bytesA bytesB V a seeds) :
    V.HashedCollision (bytesA :: bytesB :: committedFootprint) (callsA ++ callsB) ∨
      ComposedWith.{u} (fun t R _ => SeedsNotFalse callsA t R seeds) callsB a := by
  rcases h with hcol | ⟨tb, t, R, envT, htb, ht, hall, hload, hshape, hread⟩
  · exact Or.inl hcol
  · exact Or.inr ⟨tb, t, R, envT, htb, ht, hall, hload, hshape,
      ConsistentReadOver.seeds_not_false W hread⟩

/-- **Every Claimed Constant's Stored Type Is Inhabited in Every Model:**
Via frozen `ConsistentReadOver.seeds_inhabited`. -/
theorem composedModelConclusion_seeds_inhabited
    {callsA callsB : List (Aiur.Generic.SourceSemantics.Call IxVM.F)}
    {bytesA bytesB : ByteArray} {V : View} {a : Address} {seeds : List Address}
    (h : ComposedModelConclusion.{u} callsA callsB bytesA bytesB V a seeds) :
    V.HashedCollision (bytesA :: bytesB :: committedFootprint) (callsA ++ callsB) ∨
      ComposedWith.{u} (fun t R _ => SeedsInhabited.{u} callsA t R seeds) callsB a := by
  rcases h with hcol | ⟨tb, t, R, envT, htb, ht, hall, hload, hshape, hread⟩
  · exact Or.inl hcol
  · exact Or.inr ⟨tb, t, R, envT, htb, ht, hall, hload, hshape,
      ConsistentReadOver.seeds_inhabited hread⟩

end Ix.Cert.Aggr
