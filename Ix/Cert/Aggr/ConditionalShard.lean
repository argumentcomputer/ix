import Ix.IxVM.Consistency.TableValid
import Ix.DynamicLink.Soundness
import Ix.Aggr.Verification

/-! # Conditional Shard Predicate Companion & Sharded Model Composition (`Ix.Cert.Aggr.ConditionalShard`)

Predicate companion and public conditional-shard composition interface (leaving every file in
`Ix/IxVM/` and `IxCK/Kernel/` untouched):
1. Grounded `EvalAssumption` dischargers (Shape `18` Mode 2 `@Eq` `Claim.check`, Mode 1 helper,
   and Mode 3a Shape `17` `DynamicLinkStatement`),
2. Implication-level combinators (`ConditionalChecked`, `ConditionalCheckedWithLinks`) tracking
   explicit user axiom sets `Ax`, Tier 2 `evalAssumptions`, and Mode-3a `linkedCircuits`,
3. Companion bridge to single-run `IxVM.Consistency.ComposedSpec` (`ComposedModelConclusion`), and
4. **Closed conditional-shard partition composition (`ShardedComposedSpec`, `CircuitShardedComposed`)**:
   generalizes `ComposedSpec` / `CircuitComposed` from a single monolithic `asm = none` typing run
   to an arbitrary finite topologically ordered DAG (`ClosedShardPartition`) of conditional `check`
   and `checkEnv` shard runs (each carrying an arbitrary optional assumption tree `asm : Option Address`
   discharged by earlier shards in the partition, with no user axioms, no literal class, and uniform
   table-validation mode under binding `a`), concluding `ConsistentReadOver` — i.e., a set-theoretic
   `Ix.Kernel.Model W` in every `SetTheory W`, `SeedsNotFalse`, and `SeedsInhabited` — over the
   union of all shards' claimed seeds. Proved unconditionally in
   `IxVMRefinement.Endpoint.ConditionalShards`.

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

/-! ## 4. Conditional-Shard Partition Composition to a Set-Theoretic Model -/

/-- **Conditional typing claims covered by shard partition composition:**
`check` or `checkEnv` claims with no user axioms (`ctx.axioms = none`), not a literal class
(`ctx.literalClass = false`), uniform table-validation mode (`ctx.bindingAssumed = assumed`,
matching validator `3` when `assumed = false` or validator `4` when `assumed = true`), and an
arbitrary optional assumption tree (`asm : Option Address`). -/
def InScopeConditionalTyping (assumed : Bool) : Ix.Claim → Prop
  | .check ctx _ _ =>
    ctx.axioms = none ∧ ctx.literalClass = false ∧ ctx.bindingAssumed = assumed
  | .checkEnv ctx _ _ =>
    ctx.axioms = none ∧ ctx.literalClass = false ∧ ctx.bindingAssumed = assumed
  | _ => False

/-- Every unconditional in-scope typing claim (`InScopeTyping`) is an in-scope conditional
typing claim at its context's validation mode. -/
theorem inScopeConditionalTyping_of_inScopeTyping {c : Ix.Claim} {ctx : Ix.ClaimContext}
    (hsc : InScopeTyping c) (hctx : c.context? = some ctx) :
    InScopeConditionalTyping ctx.bindingAssumed c := by
  cases c with
  | check ctx' _ _ =>
    simp only [Ix.Claim.context?, Option.some.injEq] at hctx
    subst hctx
    exact ⟨hsc.1, hsc.2.2, rfl⟩
  | checkEnv ctx' _ _ =>
    simp only [Ix.Claim.context?, Option.some.injEq] at hctx
    subst hctx
    exact ⟨hsc.1, hsc.2.2, rfl⟩
  | _ => cases hsc

/-- **A shard claim's claimed seeds in a shared multi-tree view `V`:**
- for `.check _ a _`, `seeds = [a]`;
- for `.checkEnv _ root _`, `V.trees` holds a tree `t` with `treeRoot t = root` and
  `seeds = treeLeaves t`. -/
def ShardClaimSeeds : Ix.Claim → View → List Address → Prop
  | .check _ a _, _, seeds => seeds = [a]
  | .checkEnv _ root _, V, seeds =>
    ∃ t ∈ V.trees, treeRoot t = root ∧ seeds = treeLeaves t
  | _, _, _ => False

/-- Single-tree `ClaimSeeds` implies multi-tree `ShardClaimSeeds`. -/
theorem shardClaimSeeds_of_claimSeeds {c : Ix.Claim} {V : View} {seeds : List Address}
    (h : ClaimSeeds c V seeds) : ShardClaimSeeds c V seeds := by
  cases c with
  | check _ _ _ => exact h.2
  | checkEnv _ _ _ =>
    obtain ⟨t, ht, hroot, hleaves⟩ := h
    exact ⟨t, by rw [ht]; exact List.mem_singleton_self t, hroot, hleaves⟩
  | _ => cases h

/-- **A shard claim's assumed leaves in a shared multi-tree view `V`:**
- when `asm = none`, `asms = []`;
- when `asm = some root`, `V.trees` holds a tree `t` with `treeRoot t = root` and
  `asms = treeLeaves t`. -/
def ShardClaimAssumptions : Ix.Claim → View → List Address → Prop
  | .check _ _ none, _, asms => asms = []
  | .check _ _ (some root), V, asms =>
    ∃ t ∈ V.trees, treeRoot t = root ∧ asms = treeLeaves t
  | .checkEnv _ _ none, _, asms => asms = []
  | .checkEnv _ _ (some root), V, asms =>
    ∃ t ∈ V.trees, treeRoot t = root ∧ asms = treeLeaves t
  | _, _, _ => False

/-- Decoded metadata for a single conditional shard claim in a sharded verification partition. -/
structure ShardClaimEntry where
  bytes : ByteArray
  claim : Ix.Claim
  ctx : Ix.ClaimContext
  seeds : List Address
  asms : List Address

/-- Union of all claimed seeds across a list of shard entries. -/
def ShardClaimEntry.allSeeds (entries : List ShardClaimEntry) : List Address :=
  entries.flatMap (·.seeds)

/-- Union of all assumed leaves across a list of shard entries. -/
def ShardClaimEntry.allAsms (entries : List ShardClaimEntry) : List Address :=
  entries.flatMap (·.asms)

/-- Claim byte strings of all shards in a partition. -/
def ShardClaimEntry.allBytes (entries : List ShardClaimEntry) : List ByteArray :=
  entries.map (·.bytes)

/-- Validity of one conditional shard entry against digest `d`, binding table address `a`,
validation mode `assumed`, and shared view `V`. -/
def ShardEntryValid (d : Digest) (a : Address) (assumed : Bool) (V : View)
    (e : ShardClaimEntry) : Prop :=
  Ix.Claim.de e.bytes = .ok e.claim ∧
  packDigest (Address.blake3Pure e.bytes) = d ∧
  InScopeConditionalTyping assumed e.claim ∧
  e.claim.context? = some e.ctx ∧
  e.ctx.binding = a ∧
  ShardClaimSeeds e.claim V e.seeds ∧
  ShardClaimAssumptions e.claim V e.asms

/-- **A closed, topologically ordered partition (DAG) of conditional shards** under table
address `a`, uniform validation mode `assumed`, and shared view `V`, aligned 1-to-1 with shard
digests `ds`:
1. `entries.length = ds.length` and every `entries[k]` satisfies `ShardEntryValid ds[k] a assumed V`;
2. **DAG discharge closure:** every assumed leaf `x ∈ entries[k].asms` is claimed as a seed of
   some strictly earlier shard `j < k` (`x ∈ entries[j].seeds`). -/
structure ClosedShardPartition (ds : List Digest) (a : Address) (assumed : Bool)
    (V : View) (entries : List ShardClaimEntry) : Prop where
  length_eq : entries.length = ds.length
  valid : ∀ (k : Nat) (hk : k < entries.length),
    ShardEntryValid (ds[k]'(length_eq ▸ hk)) a assumed V entries[k]
  dagClosed : ∀ (k : Nat) (hk : k < entries.length),
    ∀ x ∈ entries[k].asms, ∃ (j : Nat) (hj : j < k),
      x ∈ (entries[j]'(Nat.lt_trans hj hk)).seeds

/-- **No assumed mutual block is used as a direct constant reference (`usedRefIdxs`):**
Because `KernelClaim::env_walk_refs` skips `assert_not_block_ref` on addresses in `asm`, this
condition records that no hashed record references an assumed `Muts` block at a constant-use
index (`usedRefIdxs`). Projection `block_addr` owners (`ownerOf`) are not in `usedRefIdxs`, so
assumed `Muts` blocks remain permitted as projection owners; and when `asms = []` (no assumptions),
this holds vacuously (`noBlockAssumedRef_nil`). -/
def NoBlockAssumedRef (calls : List (Aiur.Generic.SourceSemantics.Call IxVM.F))
    (asms : List Address) : Prop :=
  ∀ (bytes : ByteArray) (c : Ixon.Constant),
    Hashed calls bytes → Ixon.deConstantExact bytes = .ok c →
    ∀ i ∈ usedRefIdxs c, ∀ x, c.refs[i]? = some x → x ∈ asms →
      ∀ (xBytes : ByteArray) (cx : Ixon.Constant),
        Hashed calls xBytes → Address.blake3Pure xBytes = x →
        Ixon.deConstantExact xBytes = .ok cx →
        ∀ ms : Array Ixon.MutConst, cx.info ≠ .muts ms

/-- `NoBlockAssumedRef` holds vacuously when there are no assumed leaves. -/
theorem noBlockAssumedRef_nil (calls : List (Aiur.Generic.SourceSemantics.Call IxVM.F)) :
    NoBlockAssumedRef calls [] := by
  intro _ _ _ _ _ _ _ _ hx
  cases hx

/-- `NoBlockAssumedRef` holds immediately whenever no assumed address decodes to a `Muts` block. -/
theorem noBlockAssumedRef_of_asms_nonBlock
    {calls : List (Aiur.Generic.SourceSemantics.Call IxVM.F)} {asms : List Address}
    (h : ∀ x ∈ asms, ∀ (xBytes : ByteArray) (cx : Ixon.Constant),
      Hashed calls xBytes → Address.blake3Pure xBytes = x →
      Ixon.deConstantExact xBytes = .ok cx → ∀ ms : Array Ixon.MutConst, cx.info ≠ .muts ms) :
    NoBlockAssumedRef calls asms :=
  fun _ _ _ _ _ _ x _ hx xBytes cx hxb hblk hde ms => h x hx xBytes cx hxb hblk hde ms

/-- **Set-theoretic model conclusion for a closed conditional-shard partition:**
Either a BLAKE3 collision occurred across `allCalls ++ callsB` (against `V`, the shard claim
bytes, `bytesB`, or `committedFootprint`), OR the binding run hashed table bytes admitting as a
valid `Ix.Kernel.RoleTable` `t` at `a` (`AllBound t`, `TableShape t (fun _ => True) R envT`) and
the combined shard calls `allCalls` satisfy `ConsistentReadOver allCalls t R envT seeds` — giving
an `Ix.Kernel.Model W` in every `SetTheory W` covering every constant across every shard. -/
def ShardedModelConclusion
    (allCalls callsB : List (Aiur.Generic.SourceSemantics.Call IxVM.F))
    (shardBytes : List ByteArray) (bytesB : ByteArray)
    (V : View) (a : Address) (seeds : List Address) : Prop :=
  V.HashedCollision (shardBytes ++ bytesB :: committedFootprint) (allCalls ++ callsB) ∨
    ComposedWith.{u} (fun t R envT => ConsistentReadOver.{u} allCalls t R envT seeds) callsB a

/-- **Source/call-level composition statement for a finite closed partition of conditional
shards paired with a `binding` claim.** -/
def ShardedComposedSpec
    (shardCalls : List (List (Aiur.Generic.SourceSemantics.Call IxVM.F)))
    (callsB : List (Aiur.Generic.SourceSemantics.Call IxVM.F))
    (ds : List Digest) (dB : Digest) : Prop :=
  ∀ (bytesB : ByteArray) (spec a : Address),
    Ix.Claim.de bytesB = .ok (.binding spec a) →
    packDigest (Address.blake3Pure bytesB) = dB →
    ∀ (assumed : Bool) (V : View) (entries : List ShardClaimEntry),
      ClosedShardPartition ds a assumed V entries →
      NoBlockAssumedRef shardCalls.flatten (ShardClaimEntry.allAsms entries) →
      ShardedModelConclusion.{u} shardCalls.flatten callsB
        (ShardClaimEntry.allBytes entries) bytesB V a (ShardClaimEntry.allSeeds entries)

/-- An accepted `IxVM::verify_claim` circuit execution for public claim digest `d`, carrying the
exact verifier hypotheses of `IxVM.Refinement.CircuitSound`. -/
structure AcceptedCircuitRun (d : Digest) where
  id : String → Except String Nat
  specialized : Aiur.Generic.Specialized IxVM.source [verifyClaim]
  compiled : Aiur.Optimized.GenericArtifact specialized
  physical : Aiur.Optimized.Physical.Prepared compiled.artifact
  cfg : Aiur.Optimized.Depth.Config
  certified : Aiur.Optimized.Physical.Prepared.DepthCertified compiled physical cfg
  bits : cfg.bits ≤ 24
  plan : Aiur.Optimized.Grouping.Plan (Aiur.Optimized.Depth.system cfg physical.system) id
  activated : plan.WellFormedActivation
  rom : Aiur.WidthROM IxVM.F
  valid : rom.Valid
  small : rom.entries.length ≤ 2 ^ 39
  wires : List (Aiur.WireValue IxVM.F)
  output : Aiur.WireValue IxVM.F
  result : Aiur.Value IxVM.F
  signed : Aiur.Circuit.Erasure.Signed compiled.system
    { channel := verifyClaim, args := wires, result := output }
  root : Aiur.Circuit.Message IxVM.F
  rooted : Aiur.Optimized.Depth.erase cfg root =
    Aiur.Circuit.Erasure.message compiled.system
      { channel := verifyClaim, args := wires, result := output }
  outside : root.channel ∉ cfg.names
  rows : List (Aiur.Circuit.WeightedRow IxVM.F)
  bound : rows.length ≤ 2 ^ 39
  checked : plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ()
  arguments : Aiur.DecodesValues specialized.program.enums wires (Aiur.entryValues [digestValue d])
  decoded : Aiur.WireValue.decode specialized.program.enums output = some result

/-- **Circuit-level conditional-shard partition composition (`CircuitShardedComposed`):**
For any accepted `IxVM::verify_claim` binding run (`CircuitSound` on `dB`) and any finite list of
accepted conditional shard runs `shardRuns` whose combined width-ROM entries fit within `2 ^ 39`:
there exist observed `IxVM::verify_claim` derivations for every shard run (carried by each shard's
trace ROM) such that `ShardedComposedSpec` holds over `(shardCalls, callsB, ds, dB)` — so for any
closed DAG partition of conditional shards under the binding claim's table `a`, either a BLAKE3
collision occurred across the runs or the union of all shards' claimed environments satisfies
`ConsistentReadOver` (has a set-theoretic `Ix.Kernel.Model W` in every `SetTheory W`). -/
def CircuitShardedComposed : Prop :=
  CircuitSound fun callsB dB =>
    ∀ (shardRuns : List (Sigma AcceptedCircuitRun)),
      (shardRuns.map fun r => r.2.rom.entries.length).sum ≤ 2 ^ 39 →
      ∃ shardCalls : List (List (Aiur.Generic.SourceSemantics.Call IxVM.F)),
        List.Forall₂ (fun (run : Sigma AcceptedCircuitRun) calls =>
          ∃ (value : Aiur.SourceValue IxVM.F) (heap : Aiur.Heap IxVM.F),
            Aiur.Generic.SourceSemantics.ObsFn IxVM.source.world verifyClaim
              [digestValue run.1] [] value heap calls ∧
            Aiur.Generic.SourceSemantics.CallsInROM
              (run.2.compiled.traceROM run.2.rom) calls)
          shardRuns shardCalls ∧
        ShardedComposedSpec.{u} shardCalls callsB (shardRuns.map (·.1)) dB

/-- Apply `ShardedComposedSpec` to a binding claim and a closed conditional-shard partition. -/
theorem shardedModelConclusion_of_shardedComposedSpec
    {shardCalls : List (List (Aiur.Generic.SourceSemantics.Call IxVM.F))}
    {callsB : List (Aiur.Generic.SourceSemantics.Call IxVM.F)}
    {ds : List Digest} {dB : Digest}
    (hComp : ShardedComposedSpec.{u} shardCalls callsB ds dB)
    {bytesB : ByteArray} {spec a : Address}
    (hdeB : Ix.Claim.de bytesB = .ok (.binding spec a))
    (hdB : packDigest (Address.blake3Pure bytesB) = dB)
    {assumed : Bool} {V : View} {entries : List ShardClaimEntry}
    (hPart : ClosedShardPartition ds a assumed V entries)
    (hNoBlk : NoBlockAssumedRef shardCalls.flatten (ShardClaimEntry.allAsms entries)) :
    ShardedModelConclusion.{u} shardCalls.flatten callsB
      (ShardClaimEntry.allBytes entries) bytesB V a (ShardClaimEntry.allSeeds entries) :=
  hComp bytesB spec a hdeB hdB assumed V entries hPart hNoBlk

/-- **Explicit Set-Theoretic Model Extraction (`shardedModelConclusion_has_model`):**
In the collision-free branch of `ShardedModelConclusion`, there exist loaded records `E₀` across
all shard runs and a consistent kernel environment `env` extending `envT` covering every constant
across every shard in the partition such that `∀ (W : Type u) [Ix.Kernel.SetTheory W],
Nonempty (Ix.Kernel.Model W (claimedEnv env))`. -/
theorem shardedModelConclusion_has_model
    {allCalls callsB : List (Aiur.Generic.SourceSemantics.Call IxVM.F)}
    {shardBytes : List ByteArray} {bytesB : ByteArray}
    {V : View} {a : Address} {seeds : List Address}
    (h : ShardedModelConclusion.{u} allCalls callsB shardBytes bytesB V a seeds) :
    V.HashedCollision (shardBytes ++ bytesB :: committedFootprint) (allCalls ++ callsB) ∨
      ComposedWith.{u}
        (fun t R envT =>
          ∃ (E₀ : Ixon.Env) (env : Ix.Kernel.Env .anon),
            LoadedBy allCalls E₀ ∧
            (∀ ci ∈ envT.consts, ci ∈ env.consts) ∧
            (∀ s ∈ seeds, ∀ s', SeedConstant E₀ s s' →
              ∃ ci, env.find? (keyOf t s') = some ci ∧
                (PinnedBasis ci ∨ KeptIn t (storeOver E₀ R) (blobOver E₀ R) s' ci)) ∧
            ∀ (W : Type u) [Ix.Kernel.SetTheory W],
              Nonempty (Ix.Kernel.Model W (claimedEnv env)))
        callsB a := by
  rcases h with hcol | ⟨tb, t, R, envT, htb, ht, hall, hload, hshape, hread⟩
  · exact Or.inl hcol
  · obtain ⟨E₀, env, hloadE, _, hsub, _, hcov, hmod⟩ := hread
    exact Or.inr ⟨tb, t, R, envT, htb, ht, hall, hload, hshape, E₀, env, hloadE, hsub, hcov, hmod⟩

/-- **No Claimed Constant Across Any Shard Has Type `False` (`shardedModelConclusion_no_false`):**
Under any inhabited `Ix.Kernel.SetTheory W`, in the collision-free branch `SeedsNotFalse` holds
across the union of all shards' claimed seeds. -/
theorem shardedModelConclusion_no_false (W : Type u) [Ix.Kernel.SetTheory W]
    {allCalls callsB : List (Aiur.Generic.SourceSemantics.Call IxVM.F)}
    {shardBytes : List ByteArray} {bytesB : ByteArray}
    {V : View} {a : Address} {seeds : List Address}
    (h : ShardedModelConclusion.{u} allCalls callsB shardBytes bytesB V a seeds) :
    V.HashedCollision (shardBytes ++ bytesB :: committedFootprint) (allCalls ++ callsB) ∨
      ComposedWith.{u} (fun t R _ => SeedsNotFalse allCalls t R seeds) callsB a :=
  h.elim Or.inl fun hok =>
    Or.inr (ComposedWith.imp (fun _ _ _ hr => ConsistentReadOver.seeds_not_false W hr) hok)

/-- **Every Claimed Constant Across Every Shard Is Inhabited in Every Model:**
Via `ConsistentReadOver.seeds_inhabited`. -/
theorem shardedModelConclusion_seeds_inhabited
    {allCalls callsB : List (Aiur.Generic.SourceSemantics.Call IxVM.F)}
    {shardBytes : List ByteArray} {bytesB : ByteArray}
    {V : View} {a : Address} {seeds : List Address}
    (h : ShardedModelConclusion.{u} allCalls callsB shardBytes bytesB V a seeds) :
    V.HashedCollision (shardBytes ++ bytesB :: committedFootprint) (allCalls ++ callsB) ∨
      ComposedWith.{u} (fun t R _ => SeedsInhabited.{u} allCalls t R seeds) callsB a :=
  h.elim Or.inl fun hok =>
    Or.inr (ComposedWith.imp (fun _ _ _ hr => ConsistentReadOver.seeds_inhabited hr) hok)

/-- **Upgrade to `GenuineCollision` over a `SelfHashed` view (`shardedModelConclusion_selfHashed`):** -/
theorem shardedModelConclusion_selfHashed
    {allCalls callsB : List (Aiur.Generic.SourceSemantics.Call IxVM.F)}
    {shardBytes : List ByteArray} {bytesB : ByteArray}
    {V : View} {a : Address} {seeds : List Address}
    (hV : SelfHashed V)
    (h : ShardedModelConclusion.{u} allCalls callsB shardBytes bytesB V a seeds) :
    GenuineCollision V (shardBytes ++ bytesB :: committedFootprint) (allCalls ++ callsB) ∨
      ComposedWith.{u} (fun t R envT => ConsistentReadOver.{u} allCalls t R envT seeds) callsB a :=
  h.elim (fun hcol => Or.inl (hashedCollision_genuine hV hcol)) Or.inr

end Ix.Cert.Aggr
