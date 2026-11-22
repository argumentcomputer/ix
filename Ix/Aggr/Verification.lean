module
public import Ix.Aggr.Host
public import Ix.Aggr.Protocol
public import Ix.Ixon
public import Ix.IxVM.ClaimSeeds

/-! Content-addressed aggregate wrappers and their environment interpretation. -/

public section
namespace Aggr

/-- Decode a proof wrapper only after checking that its bytes reproduce the
content address supplied by the caller. `Store.read` selects a path by address
but deliberately does not re-hash ordinary store objects. -/
def decodeAggregateWrapperAt (proofAddr : Address) (bytes : ByteArray) :
    Except String Ixon.Proof := do
  let actual := Address.blake3 bytes
  if actual != proofAddr then
    throw s!"aggregate proof store object {proofAddr} hashes to {actual}"
  Ixon.Proof.de bytes

/-- Establish the per-constant interpretation of an aggregate root. A valid
proof of `CheckEnv(subjects.root, none)` certifies every subject leaf, so this
single linear audit checks that those leaves are exactly the constants of the
supplied environment a claim may name (`IxVM.ClaimHarness.claimableConsts`): no
omissions, foreign leaves, or duplicates. The unsafe and partial constants, and
those that use an inert axiom, are no claim's subjects
(`KernelClaim::assert_claimable`); a leaf among them counts as foreign. -/
def auditAggregateConstants (env : Ixon.Env) (statement : Aggr.CheckEnvTrees) :
    Except String Nat := do
  if let some assumptions := statement.assumptions then
    throw s!"aggregate root retains undischarged assumptions {assumptions.root}"
  let leaves := statement.subjects.leaves
  let claimable := IxVM.ClaimHarness.claimableConsts env
  let claimableSet : Std.HashSet Address := claimable.foldl (·.insert ·) {}
  let mut seen : Std.HashSet Address := {}
  let mut duplicates := 0
  let mut foreign := 0
  let mut firstDuplicate : Option Address := none
  let mut firstForeign : Option Address := none
  for address in leaves do
    if seen.contains address then
      duplicates := duplicates + 1
      if firstDuplicate.isNone then firstDuplicate := some address
    else
      seen := seen.insert address
    if !claimableSet.contains address then
      foreign := foreign + 1
      if firstForeign.isNone then firstForeign := some address
  let mut missing := 0
  let mut firstMissing : Option Address := none
  for address in claimable do
    if !seen.contains address then
      missing := missing + 1
      if firstMissing.isNone then firstMissing := some address
  if duplicates != 0 || foreign != 0 || missing != 0 then
    let sample (address : Option Address) := address.map toString |>.getD "none"
    throw s!"aggregate constant audit failed: {missing} missing \
      (first {sample firstMissing}), {foreign} foreign or unclaimable \
      (first {sample firstForeign}), {duplicates} duplicate occurrence(s) \
      (first {sample firstDuplicate}); environment has {claimable.size} claimable \
      constants ({env.consts.size} in all), subject tree has {leaves.size} leaves"
  if leaves.size != claimable.size then
    throw s!"aggregate constant audit cardinality mismatch: environment has \
      {claimable.size} constants in Lean's logic, subject tree has {leaves.size} leaves"
  pure claimable.size

/-! ## Set-discharge composition soundness

Formalization of the abstract set-discharge invariant across `CheckEnv` leaf
claims and recursive `ix_aggr` pair folds (flat, structural, and cross-binding):

1. Every base leaf claim `(S, A)` in the abstract model satisfies `S ∩ A = ∅`
   (`disjoint`), checks every owned subject `x ∈ S` under its dependencies
   (`checked`), and ensures every direct dependency `y` of an owned subject
   `x ∈ S` lies in `S ∪ A` (`closed`). (In the Aiur circuit, `env_walk_leaves`
   guards `S ∩ A = ∅` by interned store pointer, which holds under honest
   content-addressed interning; note that `aggrDerivation_sound`'s root closure
   and validity conclusions use only `checked` and `closed`, not `disjoint`.)
2. Every binary join `(S_L, A_L), (S_R, A_R) ↦ (S_out, A_out)` unions the
   subject sets (`S_out = S_L ∪ S_R`) and discharges an assumption only
   against the opposite child's subjects (`A_L ∖ A_out ⊆ S_R` and
   `A_R ∖ A_out ⊆ S_L`).
3. By induction over any aggregate derivation tree, every subject `x ∈ S` at
   any node was checked at some base leaf, every discharged assumption belongs
   to `S` and was checked at some base leaf, and when `A = ∅` at the root the
   subject set `S` is closed under dependencies so well-founded induction along
   the acyclic content-addressed dependency relation yields unconditional
   validity for every `x ∈ S`.
-/

/-- The abstract base-leaf obligations modeled for `IxVM`'s `run_check_env` on a
`CheckEnv` claim with subject set `S` and assumption set `A`. -/
structure LeafValid (Checked : α → Prop) (Dep : α → α → Prop)
    (S A : α → Prop) : Prop where
  /-- Owned subjects and assumptions are disjoint (modeled at the set level;
  checked by interned store pointer in `env_walk_leaves` for honest provers, and
  not required by `aggrDerivation_sound`'s root closure/validity proof). -/
  disjoint : ∀ x, S x → ¬ A x
  /-- Every owned subject is typechecked by `run_check` / `check_muts_all`. -/
  checked : ∀ x, S x → Checked x
  /-- Every direct dependency of an owned subject is either owned or assumed. -/
  closed : ∀ x y, S x → Dep x y → S y ∨ A y

/-- The binary cross-discharge relation verified by `aggr_pair`,
`aggr_pair_structural`, and `aggr_cross_binding`. -/
structure JoinRel (SL AL SR AR Sout Aout : α → Prop) : Prop where
  /-- Output subjects are the union of the children's subjects. -/
  subjects_iff : ∀ x, Sout x ↔ SL x ∨ SR x
  /-- A left assumption absent from `Aout` must be discharged by `SR`. -/
  discharge_left : ∀ x, AL x → ¬ Aout x → SR x
  /-- A right assumption absent from `Aout` must be discharged by `SL`. -/
  discharge_right : ∀ x, AR x → ¬ Aout x → SL x
  /-- Every output assumption originates from at least one child. -/
  assumptions_sub : ∀ x, Aout x → AL x ∨ AR x

/-- An aggregate derivation tree built from `IxVM` leaves, pass-through wraps,
and binary set-discharge joins. -/
inductive AggrDerivation (Checked : α → Prop) (Dep : α → α → Prop) :
    (α → Prop) → (α → Prop) → Prop where
  | leaf {S A : α → Prop} :
      LeafValid Checked Dep S A →
      AggrDerivation Checked Dep S A
  | wrap {S A : α → Prop} :
      AggrDerivation Checked Dep S A →
      AggrDerivation Checked Dep S A
  | join {SL AL SR AR Sout Aout : α → Prop} :
      AggrDerivation Checked Dep SL AL →
      AggrDerivation Checked Dep SR AR →
      JoinRel SL AL SR AR Sout Aout →
      AggrDerivation Checked Dep Sout Aout

/-- Every subject of any aggregate derivation was checked by some base leaf. -/
theorem aggrDerivation_subject_checked
    {Checked : α → Prop} {Dep : α → α → Prop} {S A : α → Prop}
    (h : AggrDerivation Checked Dep S A) :
    ∀ x, S x → Checked x := by
  induction h with
  | leaf hLeaf =>
    intro x hx
    exact hLeaf.checked x hx
  | wrap _ ih =>
    exact ih
  | join _ _ hJoin ihL ihR =>
    intro x hx
    rcases (hJoin.subjects_iff x).mp hx with hxL | hxR
    · exact ihL x hxL
    · exact ihR x hxR

/-- Every assumption discharged at a binary join belongs to the joined subject
set and was checked by some base leaf. -/
theorem join_discharged_subject_checked
    {Checked : α → Prop} {Dep : α → α → Prop}
    {SL AL SR AR Sout Aout : α → Prop}
    (hL : AggrDerivation Checked Dep SL AL)
    (hR : AggrDerivation Checked Dep SR AR)
    (hJoin : JoinRel SL AL SR AR Sout Aout) :
    ∀ x, (AL x ∨ AR x) → ¬ Aout x → Sout x ∧ Checked x := by
  intro x hAsm hNotOut
  rcases hAsm with hAL | hAR
  · have hSR : SR x := hJoin.discharge_left x hAL hNotOut
    exact ⟨(hJoin.subjects_iff x).mpr (.inr hSR),
      aggrDerivation_subject_checked hR x hSR⟩
  · have hSL : SL x := hJoin.discharge_right x hAR hNotOut
    exact ⟨(hJoin.subjects_iff x).mpr (.inl hSL),
      aggrDerivation_subject_checked hL x hSL⟩

/-- At every node of an aggregate derivation, every direct dependency of a
subject is either in the node's subject set or in its assumption set. -/
theorem aggrDerivation_closed_union
    {Checked : α → Prop} {Dep : α → α → Prop} {S A : α → Prop}
    (h : AggrDerivation Checked Dep S A) :
    ∀ x y, S x → Dep x y → S y ∨ A y := by
  induction h with
  | leaf hLeaf =>
    exact hLeaf.closed
  | wrap _ ih =>
    exact ih
  | join _ _ hJoin ihL ihR =>
    intro x y hx hDep
    rcases (hJoin.subjects_iff x).mp hx with hxL | hxR
    · rcases ihL x y hxL hDep with hSL | hAL
      · exact .inl ((hJoin.subjects_iff y).mpr (.inl hSL))
      · rcases Classical.em _ with hAout | hAout
        · exact .inr hAout
        · exact .inl ((hJoin.subjects_iff y).mpr
            (.inr (hJoin.discharge_left y hAL hAout)))
    · rcases ihR x y hxR hDep with hSR | hAR
      · exact .inl ((hJoin.subjects_iff y).mpr (.inr hSR))
      · rcases Classical.em _ with hAout | hAout
        · exact .inr hAout
        · exact .inl ((hJoin.subjects_iff y).mpr
            (.inl (hJoin.discharge_right y hAR hAout)))

/-- When an aggregate root has no remaining assumptions (`∀ x, ¬ A x`), its
subject set `S` is closed under the dependency relation `Dep`. -/
theorem aggrDerivation_unconditional_closed
    {Checked : α → Prop} {Dep : α → α → Prop} {S A : α → Prop}
    (h : AggrDerivation Checked Dep S A)
    (hEmpty : ∀ x, ¬ A x) :
    ∀ x y, S x → Dep x y → S y := by
  intro x y hx hDep
  rcases aggrDerivation_closed_union h x y hx hDep with hS | hA
  · exact hS
  · exact False.elim (hEmpty y hA)

/-- End-to-end set-discharge soundness: if the dependency relation `Dep` is
well-founded (acyclic by Blake3 content addressing) and checking `x` given
valid dependencies establishes `Valid x`, then every subject of an
unconditional aggregate root (`∀ x, ¬ A x`) is valid. -/
theorem aggrDerivation_sound
    {Checked Valid : α → Prop} {Dep : α → α → Prop} {S A : α → Prop}
    (hWf : WellFounded (fun y x => Dep x y))
    (hStep : ∀ x, Checked x → (∀ y, Dep x y → Valid y) → Valid x)
    (hDeriv : AggrDerivation Checked Dep S A)
    (hEmpty : ∀ x, ¬ A x) :
    ∀ x, S x → Valid x := by
  have hClosed := aggrDerivation_unconditional_closed hDeriv hEmpty
  have hChecked := aggrDerivation_subject_checked hDeriv
  intro x
  induction x using hWf.induction with
  | h x ih =>
    intro hx
    exact hStep x (hChecked x hx) (fun y hDep => ih y hDep (hClosed x y hx hDep))

/-- Cross-discharge forbids self-discharging a duplicated conditional claim
`join(q, q)` whenever `S ∩ A = ∅`: if `x ∈ A`, then `x` cannot be discharged
into `Aout = ∅`. -/
theorem joinRel_rejects_duplicate_discharge
    {S A Sout Aout : α → Prop}
    (hDisjoint : ∀ x, S x → ¬ A x)
    (hJoin : JoinRel S A S A Sout Aout)
    {x : α} (hx : A x) :
    Aout x := by
  apply Classical.byContradiction
  intro hNotOut
  have hS : S x := hJoin.discharge_left x hx hNotOut
  exact hDisjoint x hS hx

/-! ## All 19 Aggregation Shapes (`0..18`) + `A7` Axiom-Set Matching

Extends the core binary set-discharge model above to cover every shape implemented
in `MultiStark/MultiStark/Modules/{Aggregate,Aggregation}.lean`:
- Shapes `0–1`: wrap (`aggr_wrap`)
- Shapes `2–5`: flat canonical pair fold with `A7` axiom-set merge (`aggr_pair`)
- Shapes `6–9`: structural Merkle pair fold with `A7` axiom-set merge (`aggr_pair_structural`)
- Shapes `10–12`: sharded range-sum recursion with telescoping LogUp residuals
  (`aggr_range_leaf`, `aggr_range_join`, `aggr_range_root`)
- Shapes `13–14`: role-binding discharge (`validator 4 → 3`, `aggr_discharge_binding`)
- Shape `15`: cross-binding structural join under the 13-role literal class with `A7`
  axiom-set merge (`validator {3, 5} → 5`, `aggr_cross_binding`)
- Shape `16`: catalog union over unconditional `CheckEnv` / `Catalog` children (`aggr_catalog_join`)
- Shape `17`: Tier 1 dynamic circuit linking (`aggr_dynamic_link`, `0xE8 0x0D`)
- Shape `18`: Tier 2 eval-assumption leaf discharge (`aggr_discharge_eval`, `0xE8 0x0E`)
  with `A7` axiom-set merge: Mode 2 (`@Eq` `Claim.check`) transitions `10 → 3` / `11 → 4`
  only when `evalAssumptions = none` and `linkedCircuits = none`, whereas Mode 3a
  (`DynamicLinkStatement`) always commits a canonical `LinkedCircuitEntry` (`0xE8 0x0F`)
  under linked validators `12`/`13` (never emitting validators `3`/`4`).
-/

/-- Canonical enumeration of all 19 aggregation shapes (`0..18`) in `MultiStark::ix_aggr`. -/
inductive AggrShape where
  | wrapIxvm
  | wrapAggr
  | pairFlatIxvmIxvm
  | pairFlatIxvmAggr
  | pairFlatAggrIxvm
  | pairFlatAggrAggr
  | pairStructIxvmIxvm
  | pairStructIxvmAggr
  | pairStructAggrIxvm
  | pairStructAggrAggr
  | rangeLeaf
  | rangeJoin
  | rangeRoot
  | dischargeBindingIxvm
  | dischargeBindingAggr
  | crossBinding
  | catalogJoin
  | dynamicLink
  | dischargeEval
  deriving BEq, DecidableEq, Repr, Inhabited

@[expose] def AggrShape.code : AggrShape → Nat
  | .wrapIxvm => 0
  | .wrapAggr => 1
  | .pairFlatIxvmIxvm => 2
  | .pairFlatIxvmAggr => 3
  | .pairFlatAggrIxvm => 4
  | .pairFlatAggrAggr => 5
  | .pairStructIxvmIxvm => 6
  | .pairStructIxvmAggr => 7
  | .pairStructAggrIxvm => 8
  | .pairStructAggrAggr => 9
  | .rangeLeaf => 10
  | .rangeJoin => 11
  | .rangeRoot => 12
  | .dischargeBindingIxvm => 13
  | .dischargeBindingAggr => 14
  | .crossBinding => 15
  | .catalogJoin => 16
  | .dynamicLink => 17
  | .dischargeEval => 18

@[expose] def AggrShape.ofCode? : Nat → Option AggrShape
  | 0 => some .wrapIxvm
  | 1 => some .wrapAggr
  | 2 => some .pairFlatIxvmIxvm
  | 3 => some .pairFlatIxvmAggr
  | 4 => some .pairFlatAggrIxvm
  | 5 => some .pairFlatAggrAggr
  | 6 => some .pairStructIxvmIxvm
  | 7 => some .pairStructIxvmAggr
  | 8 => some .pairStructAggrIxvm
  | 9 => some .pairStructAggrAggr
  | 10 => some .rangeLeaf
  | 11 => some .rangeJoin
  | 12 => some .rangeRoot
  | 13 => some .dischargeBindingIxvm
  | 14 => some .dischargeBindingAggr
  | 15 => some .crossBinding
  | 16 => some .catalogJoin
  | 17 => some .dynamicLink
  | 18 => some .dischargeEval
  | _ => none

@[expose] def AggrShape.all : List AggrShape :=
  [.wrapIxvm, .wrapAggr, .pairFlatIxvmIxvm, .pairFlatIxvmAggr, .pairFlatAggrIxvm,
   .pairFlatAggrAggr, .pairStructIxvmIxvm, .pairStructIxvmAggr, .pairStructAggrIxvm,
   .pairStructAggrAggr, .rangeLeaf, .rangeJoin, .rangeRoot, .dischargeBindingIxvm,
   .dischargeBindingAggr, .crossBinding, .catalogJoin, .dynamicLink, .dischargeEval]

theorem AggrShape.all_length : AggrShape.all.length = 19 := rfl

theorem AggrShape.ofCode?_code (s : AggrShape) : AggrShape.ofCode? s.code = some s := by
  cases s <;> rfl

theorem AggrShape.code_lt_19 (s : AggrShape) : s.code < 19 := by
  cases s <;> decide

theorem AggrShape.shapeCode_matches :
    AggrShape.dynamicLink.code = Aggr.dynamicLinkShapeCode ∧
    AggrShape.dischargeEval.code = Aggr.dischargeEvalShapeCode ∧
    AggrShape.catalogJoin.code = Aggr.catalogShapeCode ∧
    AggrShape.crossBinding.code = Aggr.crossBindingShapeCode ∧
    AggrShape.rangeLeaf.code = Aggr.rangeLeafShape ∧
    AggrShape.rangeJoin.code = Aggr.rangeJoinShape ∧
    AggrShape.rangeRoot.code = Aggr.rangeRootShape := by
  decide

/-! ### `A7` Axiom-Set Merge & Eval-Discharge Relations -/

/-- `A7` user-axiom merge relation verified by `aggr_assert_axioms_merge`:
the output claim's axiom set is the exact set union of its two children's axiom sets. -/
def AxiomMergeRel (AxL AxR AxOut : β → Prop) : Prop :=
  ∀ a, AxOut a ↔ AxL a ∨ AxR a

theorem AxiomMergeRel.left_sub {AxL AxR AxOut : β → Prop}
    (h : AxiomMergeRel AxL AxR AxOut) {a : β} (ha : AxL a) : AxOut a :=
  (h a).mpr (.inl ha)

theorem AxiomMergeRel.right_sub {AxL AxR AxOut : β → Prop}
    (h : AxiomMergeRel AxL AxR AxOut) {a : β} (ha : AxR a) : AxOut a :=
  (h a).mpr (.inr ha)

theorem AxiomMergeRel.of_eq {Ax : β → Prop} : AxiomMergeRel Ax Ax Ax :=
  fun _ => ⟨fun h => .inl h, fun h => h.elim id id⟩

theorem AxiomMergeRel.of_empty_left {Ax : β → Prop} :
    AxiomMergeRel (fun _ => False) Ax Ax :=
  fun _ => ⟨fun h => .inr h, fun h => h.elim False.elim id⟩

theorem AxiomMergeRel.of_empty_right {Ax : β → Prop} :
    AxiomMergeRel Ax (fun _ => False) Ax :=
  fun _ => ⟨fun h => .inl h, fun h => h.elim id False.elim⟩

/-- Negative control for `A7`: dropping any user axiom present in either child
cannot satisfy `AxiomMergeRel`. -/
theorem axiomMergeRel_rejects_dropped_axiom {AxL AxR AxOut : β → Prop}
    (h : AxiomMergeRel AxL AxR AxOut) {a : β} (ha : AxL a ∨ AxR a) : AxOut a :=
  (h a).mpr ha

/-- Single-leaf removal relation on `evalAssumptions` verified by
`aggr_extract_removed_leaf` in Shape 18 (`aggr_discharge_eval`). -/
structure EvalRemoveRel (EvalBefore EvalAfter : γ → Prop) (e₀ : γ) : Prop where
  removed_mem : EvalBefore e₀
  removed_not_after : ¬ EvalAfter e₀
  before_iff : ∀ e, EvalBefore e ↔ e = e₀ ∨ EvalAfter e

/-- Negative control for Shape 18: if an `evalAssumption` leaf `e ≠ e₀` remains in
`EvalBefore`, full discharge to `EvalAfter = ∅` is impossible. -/
theorem evalRemoveRel_rejects_undischarged {EvalBefore : γ → Prop} {e₀ e : γ}
    (hRem : EvalRemoveRel EvalBefore (fun _ => False) e₀) (he : EvalBefore e) :
    e = e₀ := by
  rcases (hRem.before_iff e).mp he with rfl | hFalse
  · rfl
  · exact False.elim hFalse

/-- Linked-circuit accumulator merge relation verified by `aggr_assert_linked_merge`
in Shape 18 Mode 3a: the output claim's linked-circuit set is the exact union of the
prior linked-circuit set and the newly committed `entry`. -/
def LinkedMergeRel (LinkedBefore : ι → Prop) (entry : ι) (LinkedAfter : ι → Prop) : Prop :=
  ∀ l, LinkedAfter l ↔ LinkedBefore l ∨ l = entry

theorem LinkedMergeRel.prev_sub {LinkedBefore LinkedAfter : ι → Prop} {entry : ι}
    (h : LinkedMergeRel LinkedBefore entry LinkedAfter) {l : ι} (hl : LinkedBefore l) :
    LinkedAfter l :=
  (h l).mpr (.inl hl)

theorem LinkedMergeRel.entry_mem {LinkedBefore LinkedAfter : ι → Prop} {entry : ι}
    (h : LinkedMergeRel LinkedBefore entry LinkedAfter) : LinkedAfter entry :=
  (h entry).mpr (.inr rfl)

/-- Negative control for Shape 18 Mode 3a: recording a `LinkedCircuitEntry` can NEVER
yield an empty `LinkedAfter = ∅` set. -/
theorem linkedMergeRel_rejects_erasure {LinkedBefore : ι → Prop} {entry : ι} :
    ¬ LinkedMergeRel LinkedBefore entry (fun _ => False) :=
  fun h => h.entry_mem

/-! ### Telescoping Range Sums (Shapes `10–12`) -/

/-- Abstract commutative additive monoid over extension-field LogUp residuals. -/
structure ResidualMonoid (ε : Type u) where
  zero : ε
  add : ε → ε → ε
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  zero_add : ∀ a, add zero a = a
  add_zero : ∀ a, add a zero = a

/-- Partial sum `∑_{i ∈ [lo, hi)} f i` in a `ResidualMonoid`. -/
def rangeSumAux {ε : Type u} (M : ResidualMonoid ε) (f : Nat → ε) : Nat → Nat → ε
  | _, 0 => M.zero
  | lo, n + 1 => M.add (f lo) (rangeSumAux M f (lo + 1) n)

def rangeSum {ε : Type u} (M : ResidualMonoid ε) (f : Nat → ε) (lo hi : Nat) : ε :=
  rangeSumAux M f lo (hi - lo)

theorem rangeSumAux_add {ε : Type u} (M : ResidualMonoid ε) (f : Nat → ε) :
    ∀ (lo m n : Nat),
      M.add (rangeSumAux M f lo m) (rangeSumAux M f (lo + m) n) = rangeSumAux M f lo (m + n)
  | lo, 0, n => by
    simp only [rangeSumAux, Nat.add_zero, Nat.zero_add]
    exact M.zero_add _
  | lo, m + 1, n => by
    simp only [rangeSumAux, Nat.succ_add]
    rw [M.add_assoc]
    have hidx : lo + (m + 1) = (lo + 1) + m := by omega
    rw [hidx, rangeSumAux_add M f (lo + 1) m n]

/-- **Telescoping identity for Shapes `10–12`:** combining adjacent shard ranges
`[lo, mid)` and `[mid, hi)` via `M.add` equals the direct range sum over `[lo, hi)`. -/
theorem rangeSum_append {ε : Type u} (M : ResidualMonoid ε) (f : Nat → ε)
    {lo mid hi : Nat} (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    M.add (rangeSum M f lo mid) (rangeSum M f mid hi) = rangeSum M f lo hi := by
  unfold rangeSum
  have hm : lo + (mid - lo) = mid := by omega
  have hlen : (mid - lo) + (hi - mid) = hi - lo := by omega
  have h := rangeSumAux_add M f lo (mid - lo) (hi - mid)
  rw [hm, hlen] at h
  exact h

/-! ### Validator Modes & 19-Shape Derivation System -/

/-- Validator state of a `Check`/`CheckEnv` statement across all 19 shapes:
- `validated b` (`validator = 3`), `assumedBinding b` (`validator = 4`),
- `literalClass k` (`validator = 5`),
- `evalAssumed b` (`validator = 10`), `bindingEvalAssumed b` (`validator = 11`),
- `linked b` (`validator = 12`), `bindingLinked b` (`validator = 13`). -/
inductive ValidatorMode (δ : Type u) where
  | validated (b : δ)
  | assumedBinding (b : δ)
  | literalClass (k : δ)
  | evalAssumed (b : δ)
  | bindingEvalAssumed (b : δ)
  | linked (b : δ)
  | bindingLinked (b : δ)
  deriving BEq, DecidableEq, Repr

def ValidatorMode.bindingOf : ValidatorMode δ → δ
  | .validated b => b
  | .assumedBinding b => b
  | .literalClass k => k
  | .evalAssumed b => b
  | .bindingEvalAssumed b => b
  | .linked b => b
  | .bindingLinked b => b

def ValidatorMode.validatorCode : ValidatorMode δ → UInt8
  | .validated _ => 3
  | .assumedBinding _ => 4
  | .literalClass _ => 5
  | .evalAssumed _ => 10
  | .bindingEvalAssumed _ => 11
  | .linked _ => 12
  | .bindingLinked _ => 13

/-- Binding validity precondition required by a validator mode:
validators `3`, `5`, `10`, `12` already validated their binding (`True`), whereas
validators `4`, `11`, `13` assume `BindingValid b`. -/
def ValidatorMode.bindingCond (BindingValid : δ → Prop) : ValidatorMode δ → Prop
  | .validated _ => True
  | .literalClass _ => True
  | .evalAssumed _ => True
  | .linked _ => True
  | .assumedBinding b => BindingValid b
  | .bindingEvalAssumed b => BindingValid b
  | .bindingLinked b => BindingValid b

/-- Whether a validator mode has already discharged its binding with zero linked
circuits (standard validators `3` or `5`). -/
def ValidatorMode.isBindingDischarged : ValidatorMode δ → Bool
  | .validated _ => true
  | .literalClass _ => true
  | _ => false

/-- Whether a validator mode commits to a non-empty `linkedCircuits` set
(validators `12` or `13`). -/
def ValidatorMode.isLinked : ValidatorMode δ → Bool
  | .linked _ => true
  | .bindingLinked _ => true
  | _ => false

/-- Whether a validator mode may serve as child 0 of Shape 18 (`aggr_discharge_eval`),
carrying remaining `evalAssumptions` (validators `10`, `11`, `12`, `13`). -/
def ValidatorMode.canDischargeEval : ValidatorMode δ → Bool
  | .evalAssumed _ => true
  | .bindingEvalAssumed _ => true
  | .linked _ => true
  | .bindingLinked _ => true
  | _ => false

/-- Validator transition when Shape 18 Mode 2 (`@Eq` `Claim.check`) discharges the
final `evalAssumption` with ZERO linked circuits (`10 → 3` and `11 → 4`).
Validators `12`/`13` return `none` and can NEVER transition to `3`/`4`. -/
def ValidatorMode.dischargeAllEvals : ValidatorMode δ → Option (ValidatorMode δ)
  | .evalAssumed b => some (.validated b)
  | .bindingEvalAssumed b => some (.assumedBinding b)
  | _ => none

/-- Validator transition when Shape 18 Mode 3a (`DynamicLinkStatement`) discharges
an `evalAssumption` and records a `LinkedCircuitEntry` into `linkedCircuits`:
`10 → 12`, `11 → 13`, `12 → 12`, `13 → 13` (NEVER `3` or `4`). -/
def ValidatorMode.toLinkedMode : ValidatorMode δ → Option (ValidatorMode δ)
  | .evalAssumed b => some (.linked b)
  | .bindingEvalAssumed b => some (.bindingLinked b)
  | .linked b => some (.linked b)
  | .bindingLinked b => some (.bindingLinked b)
  | _ => none

theorem validatorMode_toLinkedMode_props {mode outMode : ValidatorMode δ}
    (h : mode.toLinkedMode = some outMode) :
    outMode.isLinked = true ∧
    outMode.validatorCode ≠ 3 ∧
    outMode.validatorCode ≠ 4 ∧
    outMode.bindingOf = mode.bindingOf ∧
    ∀ (BindingValid : δ → Prop), outMode.bindingCond BindingValid → mode.bindingCond BindingValid := by
  cases mode <;> simp [ValidatorMode.toLinkedMode] at h
  · subst h; exact ⟨rfl, by simp [ValidatorMode.validatorCode], by simp [ValidatorMode.validatorCode], rfl, fun _ _ => trivial⟩
  · subst h; exact ⟨rfl, by simp [ValidatorMode.validatorCode], by simp [ValidatorMode.validatorCode], rfl, fun _ hb => hb⟩
  · subst h; exact ⟨rfl, by simp [ValidatorMode.validatorCode], by simp [ValidatorMode.validatorCode], rfl, fun _ _ => trivial⟩
  · subst h; exact ⟨rfl, by simp [ValidatorMode.validatorCode], by simp [ValidatorMode.validatorCode], rfl, fun _ hb => hb⟩

theorem validatorMode_dischargeAllEvals_unlinked {mode outMode : ValidatorMode δ}
    (h : mode.dischargeAllEvals = some outMode) :
    mode.isLinked = false ∧ outMode.isLinked = false := by
  cases mode <;> simp [ValidatorMode.dischargeAllEvals] at h <;> subst h <;> exact ⟨rfl, rfl⟩

/-- Semantic context for the 19-shape aggregation soundness theorem.
`α`: constant subjects, `β`: user axioms, `γ`: eval assumptions, `δ`: bindings/classes,
`ε`: range-sum LogUp residuals, `κ`: Tier-1 `DynamicLinkStatement`s,
`ι`: Mode-3a `LinkedCircuitEntry` records. -/
structure AggrSemantics (α β γ δ ε κ ι : Type) where
  Checked : δ → (β → Prop) → (γ → Prop) → (ι → Prop) → α → Prop
  Dep : α → α → Prop
  BindingValid : δ → Prop
  LiteralClassOf : δ → δ → Prop
  EvalValid : δ → (β → Prop) → γ → Prop
  DynamicLinkValid : κ → Prop
  /-- Circuit-checked binding relation between a Shape 17 `DynamicLinkStatement` `stmt`,
  claim binding `b`, discharged eval leaf `e₀`, and canonical `LinkedCircuitEntry` `entry`. -/
  LinkedRecords : κ → δ → γ → ι → Prop
  residualMonoid : ResidualMonoid ε
  shardCount : Nat → Nat
  shardResidual : Nat → Nat → ε
  messagesAcc : Nat → ε
  /-- Checked subjects are monotone when expanding user axioms. -/
  checked_mono_ax : ∀ {b Ax₁ Ax₂ EvalA Linked x},
    (∀ a, Ax₁ a → Ax₂ a) → Checked b Ax₁ EvalA Linked x → Checked b Ax₂ EvalA Linked x
  /-- Mode 2 (`@Eq` `Claim.check`): discharging a kernel-verified `EvalAssumption` leaf
  preserves `Checked` without modifying `Linked`. -/
  checked_discharge_eval : ∀ {b Ax EvalBefore EvalAfter Linked e₀ x},
    EvalRemoveRel EvalBefore EvalAfter e₀ →
    EvalValid b Ax e₀ →
    Checked b Ax EvalBefore Linked x →
    Checked b Ax EvalAfter Linked x
  /-- Mode 3a (`DynamicLinkStatement`): discharging an `EvalAssumption` leaf via an
  external dynamic circuit preserves `Checked` ONLY by explicitly recording its
  `LinkedCircuitEntry` `entry` in `LinkedAfter` (`LinkedMergeRel`). -/
  checked_discharge_eval_via_link : ∀ {b Ax EvalBefore EvalAfter LinkedBefore LinkedAfter stmt e₀ entry x},
    EvalRemoveRel EvalBefore EvalAfter e₀ →
    DynamicLinkValid stmt →
    LinkedRecords stmt b e₀ entry →
    LinkedMergeRel LinkedBefore entry LinkedAfter →
    Checked b Ax EvalBefore LinkedBefore x →
    Checked b Ax EvalAfter LinkedAfter x
  /-- Valid eval assumptions are monotone when expanding user axioms. -/
  evalValid_mono_ax : ∀ {b Ax₁ Ax₂ e},
    (∀ a, Ax₁ a → Ax₂ a) → EvalValid b Ax₁ e → EvalValid b Ax₂ e
  /-- Transfer of checked subjects across bindings sharing a 13-role literal class (Shape 15). -/
  checked_to_class : ∀ {b k Ax EvalA Linked x},
    LiteralClassOf b k → Checked b Ax EvalA Linked x → Checked k Ax EvalA Linked x
  /-- A full balanced batch (`[0, k)` with `messagesAcc + ∑ r_s = 0`) recovers leaf validity
  for the batch's public claim (Shape 12; IxVM leaves carry `Linked = ∅`). -/
  batch_balance_sound : ∀ (batchId : Nat) (mode : ValidatorMode δ)
    (S A : α → Prop) (Ax : β → Prop) (EvalA : γ → Prop),
    residualMonoid.add (messagesAcc batchId)
      (rangeSum residualMonoid (shardResidual batchId) 0 (shardCount batchId)) =
      residualMonoid.zero →
    (batchClaim : Nat → ValidatorMode δ → (α → Prop) → (α → Prop) → (β → Prop) → (γ → Prop) → Prop) →
    batchClaim batchId mode S A Ax EvalA →
    (mode.bindingCond BindingValid → ∀ x, S x → Checked mode.bindingOf Ax EvalA (fun _ => False) x) ∧
    (∀ x y, S x → Dep x y → S y ∨ A y)

/-- Base leaf obligation for an IxVM shard under `(mode, S, A, Ax, EvalA)` (`Linked = ∅`). -/
structure LeafValid19 (sem : AggrSemantics α β γ δ ε κ ι)
    (mode : ValidatorMode δ) (S A : α → Prop) (Ax : β → Prop) (EvalA : γ → Prop) : Prop where
  unlinked : mode.isLinked = false
  disjoint : ∀ x, S x → ¬ A x
  checked_under_cond : mode.bindingCond sem.BindingValid →
    ∀ x, S x → sem.Checked mode.bindingOf Ax EvalA (fun _ => False) x
  closed : ∀ x y, S x → sem.Dep x y → S y ∨ A y

/-- A structural Merkle pair relation (`Shapes 6–9`, `Shape 15`): subjects are the
union of the two children's subject sets (committed by `nodeHash(left_root, right_root)`
with `left_root ≠ right_root`) and every discharged assumption has a valid Merkle path
into the opposite child's subject tree. -/
structure StructuralJoinRel (SL AL SR AR Sout Aout : α → Prop) extends
    JoinRel SL AL SR AR Sout Aout where
  distinct_roots : ∃ x, (SL x ∧ ¬ SR x) ∨ (SR x ∧ ¬ SL x)

/-- Uniform statement carried by any node in a 19-shape aggregation tree. -/
inductive AggrNodeStmt (α β γ δ ε κ ι : Type) where
  | checkEnv (mode : ValidatorMode δ) (S A : α → Prop) (Ax : β → Prop)
      (EvalA : γ → Prop) (Linked : ι → Prop)
  | rangeStmt (batchId lo hi : Nat) (residual : ε)
  | bindingStmt (b : δ)
  | catalogStmt (members : (δ × (α → Prop) × (β → Prop)) → Prop)
  | dynamicLinkStmt (stmt : κ)
  | evalDischargerStmt (b : δ) (Ax : β → Prop) (e : γ)

/-- Complete inductive derivation tree over ALL 19 aggregation shapes (`0..18`).
Shape 18 Mode 2 (`dischargeEvalStep` / `dischargeEvalAll` / `dischargeEvalLinkedFinal`)
discharges an `EvalAssumption` via a kernel `@Eq` `Claim.check`; Shape 18 Mode 3a
(`dischargeEvalViaDynamicLink`) discharges an `EvalAssumption` via a Shape 17
`DynamicLinkStatement` ONLY by recording its `LinkedCircuitEntry` into `LinkedAfter`
under validators `12`/`13` (NEVER erasing into validators `3`/`4`). -/
inductive AggrDerivation19 (sem : AggrSemantics α β γ δ ε κ ι)
    (batchClaim : Nat → ValidatorMode δ → (α → Prop) → (α → Prop) → (β → Prop) → (γ → Prop) → Prop) :
    AggrNodeStmt α β γ δ ε κ ι → Prop where
  /-- Base IxVM leaf (`Check` / `CheckEnv`, `Linked = ∅`). -/
  | leaf {mode S A Ax EvalA} :
      LeafValid19 sem mode S A Ax EvalA →
      AggrDerivation19 sem batchClaim (.checkEnv mode S A Ax EvalA (fun _ => False))
  /-- Base IxVM `binding` claim establishing `BindingValid b`. -/
  | bindingLeaf {b : δ} :
      sem.BindingValid b →
      AggrDerivation19 sem batchClaim (.bindingStmt b)
  /-- Base IxVM Mode 2 `@Eq` `Claim.check` discharging an `EvalAssumption` leaf `e`. -/
  | evalDischargerLeaf {b : δ} {Ax : β → Prop} {e : γ} :
      sem.EvalValid b Ax e →
      AggrDerivation19 sem batchClaim (.evalDischargerStmt b Ax e)
  /-- Shapes `0–1`: wrap an IxVM or `ix_aggr` child without changing its statement. -/
  | wrap {stmt} :
      AggrDerivation19 sem batchClaim stmt →
      AggrDerivation19 sem batchClaim stmt
  /-- Shapes `2–5`: flat canonical pair fold with cross-discharge and `A7` axiom merge
  (standard unlinked claims `Linked = ∅`). -/
  | pairFlat {mode SL AL AxL SR AR AxR Sout Aout AxOut} :
      mode.isLinked = false →
      AggrDerivation19 sem batchClaim (.checkEnv mode SL AL AxL (fun _ => False) (fun _ => False)) →
      AggrDerivation19 sem batchClaim (.checkEnv mode SR AR AxR (fun _ => False) (fun _ => False)) →
      JoinRel SL AL SR AR Sout Aout →
      AxiomMergeRel AxL AxR AxOut →
      AggrDerivation19 sem batchClaim (.checkEnv mode Sout Aout AxOut (fun _ => False) (fun _ => False))
  /-- Shapes `6–9`: structural Merkle pair fold with Merkle-path discharge and `A7` axiom merge
  (standard unlinked claims `Linked = ∅`). -/
  | pairStructural {mode SL AL AxL SR AR AxR Sout Aout AxOut} :
      mode.isLinked = false →
      AggrDerivation19 sem batchClaim (.checkEnv mode SL AL AxL (fun _ => False) (fun _ => False)) →
      AggrDerivation19 sem batchClaim (.checkEnv mode SR AR AxR (fun _ => False) (fun _ => False)) →
      StructuralJoinRel SL AL SR AR Sout Aout →
      AxiomMergeRel AxL AxR AxOut →
      AggrDerivation19 sem batchClaim (.checkEnv mode Sout Aout AxOut (fun _ => False) (fun _ => False))
  /-- Shape `10`: range leaf verifying shards `[lo, hi)` of `batchId`. -/
  | rangeLeaf {batchId lo hi : Nat} :
      lo ≤ hi →
      AggrDerivation19 sem batchClaim
        (.rangeStmt batchId lo hi (rangeSum sem.residualMonoid (sem.shardResidual batchId) lo hi))
  /-- Shape `11`: range join adding residuals of adjacent shard ranges `[lo, mid)` and `[mid, hi)`. -/
  | rangeJoin {batchId lo mid hi : Nat} {rL rR : ε} :
      AggrDerivation19 sem batchClaim (.rangeStmt batchId lo mid rL) →
      AggrDerivation19 sem batchClaim (.rangeStmt batchId mid hi rR) →
      AggrDerivation19 sem batchClaim
        (.rangeStmt batchId lo hi (sem.residualMonoid.add rL rR))
  /-- Shape `12`: range root closing `[0, shardCount batchId)` with global LogUp vanishing. -/
  | rangeRoot {batchId : Nat} {r : ε} {mode S A Ax EvalA} :
      mode.isLinked = false →
      AggrDerivation19 sem batchClaim (.rangeStmt batchId 0 (sem.shardCount batchId) r) →
      sem.residualMonoid.add (sem.messagesAcc batchId) r = sem.residualMonoid.zero →
      batchClaim batchId mode S A Ax EvalA →
      AggrDerivation19 sem batchClaim (.checkEnv mode S A Ax EvalA (fun _ => False))
  /-- Shapes `13–14`: discharge an assumed role binding (`validator 4 → 3`). -/
  | dischargeBinding {b S A Ax} :
      AggrDerivation19 sem batchClaim (.checkEnv (.assumedBinding b) S A Ax (fun _ => False) (fun _ => False)) →
      AggrDerivation19 sem batchClaim (.bindingStmt b) →
      AggrDerivation19 sem batchClaim (.checkEnv (.validated b) S A Ax (fun _ => False) (fun _ => False))
  /-- Shape `15`: cross-binding structural join under a shared 13-role literal class `k`
  (`validator ∈ {3, 5} → 5`) with `A7` axiom merge. -/
  | crossBinding {modeL modeR : ValidatorMode δ} {k : δ}
      {SL AL AxL SR AR AxR Sout Aout AxOut} :
      AggrDerivation19 sem batchClaim (.checkEnv modeL SL AL AxL (fun _ => False) (fun _ => False)) →
      AggrDerivation19 sem batchClaim (.checkEnv modeR SR AR AxR (fun _ => False) (fun _ => False)) →
      modeL.isBindingDischarged = true →
      modeR.isBindingDischarged = true →
      (modeL = .literalClass k ∨ sem.LiteralClassOf modeL.bindingOf k) →
      (modeR = .literalClass k ∨ sem.LiteralClassOf modeR.bindingOf k) →
      StructuralJoinRel SL AL SR AR Sout Aout →
      AxiomMergeRel AxL AxR AxOut →
      AggrDerivation19 sem batchClaim (.checkEnv (.literalClass k) Sout Aout AxOut (fun _ => False) (fun _ => False))
  /-- Shape `16`: catalog union of two unconditional, unlinked `CheckEnv` or `Catalog` children. -/
  | catalogJoin {membersL membersR membersOut : (δ × (α → Prop) × (β → Prop)) → Prop}
      {stmtL stmtR : AggrNodeStmt α β γ δ ε κ ι} :
      AggrDerivation19 sem batchClaim stmtL →
      AggrDerivation19 sem batchClaim stmtR →
      ((∃ mode S Ax, stmtL = .checkEnv mode S (fun _ => False) Ax (fun _ => False) (fun _ => False) ∧
          mode.isBindingDischarged = true ∧
          ∀ m, membersL m ↔ m = (mode.bindingOf, S, Ax)) ∨
        stmtL = .catalogStmt membersL) →
      ((∃ mode S Ax, stmtR = .checkEnv mode S (fun _ => False) Ax (fun _ => False) (fun _ => False) ∧
          mode.isBindingDischarged = true ∧
          ∀ m, membersR m ↔ m = (mode.bindingOf, S, Ax)) ∨
        stmtR = .catalogStmt membersR) →
      (∀ m, membersOut m ↔ membersL m ∨ membersR m) →
      AggrDerivation19 sem batchClaim (.catalogStmt membersOut)
  /-- Shape `17`: Tier 1 dynamic circuit linking (`aggr_dynamic_link`, `0xE8 0x0D`). -/
  | dynamicLink {stmt : κ} :
      sem.DynamicLinkValid stmt →
      AggrDerivation19 sem batchClaim (.dynamicLinkStmt stmt)
  /-- Shape `18` Mode 2 (partial step): discharge one `EvalAssumption` leaf `e₀` via an
  `@Eq` `Claim.check`, preserving `mode ∈ {10, 11, 12, 13}` and `Linked`, and merging axioms. -/
  | dischargeEvalStep {mode : ValidatorMode δ} {S A Ax₀ Ax₁ AxOut EvalBefore EvalAfter Linked e₀} :
      mode.canDischargeEval = true →
      AggrDerivation19 sem batchClaim (.checkEnv mode S A Ax₀ EvalBefore Linked) →
      AggrDerivation19 sem batchClaim (.evalDischargerStmt mode.bindingOf Ax₁ e₀) →
      EvalRemoveRel EvalBefore EvalAfter e₀ →
      AxiomMergeRel Ax₀ Ax₁ AxOut →
      AggrDerivation19 sem batchClaim (.checkEnv mode S A AxOut EvalAfter Linked)
  /-- Shape `18` Mode 2 (final unlinked step): discharge the last `EvalAssumption` leaf `e₀`
  via an `@Eq` `Claim.check` when `Linked = ∅`, transitioning validator `10 → 3` or `11 → 4`. -/
  | dischargeEvalAll {mode outMode : ValidatorMode δ} {S A Ax₀ Ax₁ AxOut EvalBefore e₀} :
      mode.dischargeAllEvals = some outMode →
      AggrDerivation19 sem batchClaim (.checkEnv mode S A Ax₀ EvalBefore (fun _ => False)) →
      AggrDerivation19 sem batchClaim (.evalDischargerStmt mode.bindingOf Ax₁ e₀) →
      EvalRemoveRel EvalBefore (fun _ => False) e₀ →
      AxiomMergeRel Ax₀ Ax₁ AxOut →
      AggrDerivation19 sem batchClaim (.checkEnv outMode S A AxOut (fun _ => False) (fun _ => False))
  /-- Shape `18` Mode 2 (final linked step): discharge the last `EvalAssumption` leaf `e₀`
  via an `@Eq` `Claim.check` when ALREADY in linked mode (`validator ∈ {12, 13}`); stays in
  `mode ∈ {12, 13}` with `Linked` preserved (NEVER transitions to `3`/`4`). -/
  | dischargeEvalLinkedFinal {mode : ValidatorMode δ} {S A Ax₀ Ax₁ AxOut EvalBefore Linked e₀} :
      mode.isLinked = true →
      AggrDerivation19 sem batchClaim (.checkEnv mode S A Ax₀ EvalBefore Linked) →
      AggrDerivation19 sem batchClaim (.evalDischargerStmt mode.bindingOf Ax₁ e₀) →
      EvalRemoveRel EvalBefore (fun _ => False) e₀ →
      AxiomMergeRel Ax₀ Ax₁ AxOut →
      AggrDerivation19 sem batchClaim (.checkEnv mode S A AxOut (fun _ => False) Linked)
  /-- Shape `18` Mode 3a (`DynamicLinkStatement`): discharge `e₀` via a Shape 17 child,
  ALWAYS transitioning to linked mode (`10 → 12`, `11 → 13`, `12 → 12`, `13 → 13`) and
  recording `entry` into `LinkedAfter` via `LinkedMergeRel` (NEVER emits validator `3`/`4`). -/
  | dischargeEvalViaDynamicLink {mode outMode : ValidatorMode δ}
      {S A Ax EvalBefore EvalAfter LinkedBefore LinkedAfter stmt e₀ entry} :
      mode.toLinkedMode = some outMode →
      AggrDerivation19 sem batchClaim (.checkEnv mode S A Ax EvalBefore LinkedBefore) →
      AggrDerivation19 sem batchClaim (.dynamicLinkStmt stmt) →
      EvalRemoveRel EvalBefore EvalAfter e₀ →
      sem.LinkedRecords stmt mode.bindingOf e₀ entry →
      LinkedMergeRel LinkedBefore entry LinkedAfter →
      AggrDerivation19 sem batchClaim (.checkEnv outMode S A Ax EvalAfter LinkedAfter)

/-- Semantic invariant established inductively for every node of `AggrDerivation19`:
every non-linked `.checkEnv` node (`mode.isLinked = false`, in particular validators
`3`, `4`, `5`, `10`, `11`) has `Linked = ∅` (zero external circuits). -/
def AggrNodeHolds (sem : AggrSemantics α β γ δ ε κ ι) : AggrNodeStmt α β γ δ ε κ ι → Prop
  | .checkEnv mode S A Ax EvalA Linked =>
      (mode.bindingCond sem.BindingValid →
        ∀ x, S x → sem.Checked mode.bindingOf Ax EvalA Linked x) ∧
      (∀ x y, S x → sem.Dep x y → S y ∨ A y) ∧
      (mode.isLinked = false → ∀ l, ¬ Linked l)
  | .rangeStmt batchId lo hi r =>
      lo ≤ hi ∧ r = rangeSum sem.residualMonoid (sem.shardResidual batchId) lo hi
  | .bindingStmt b => sem.BindingValid b
  | .catalogStmt members =>
      ∀ b S Ax, members (b, S, Ax) →
        (∀ x, S x → sem.Checked b Ax (fun _ => False) (fun _ => False) x) ∧
        (∀ x y, S x → sem.Dep x y → S y)
  | .dynamicLinkStmt stmt => sem.DynamicLinkValid stmt
  | .evalDischargerStmt b Ax e => sem.EvalValid b Ax e

private theorem validatorMode_bindingCond_of_discharged {BindingValid : δ → Prop}
    {mode : ValidatorMode δ} (h : mode.isBindingDischarged = true) :
    mode.bindingCond BindingValid := by
  cases mode <;> simp [ValidatorMode.isBindingDischarged, ValidatorMode.bindingCond] at h ⊢

private theorem validatorMode_bindingOf_dischargeAll {mode outMode : ValidatorMode δ}
    (h : mode.dischargeAllEvals = some outMode) :
    outMode.bindingOf = mode.bindingOf ∧
    ∀ (BindingValid : δ → Prop), outMode.bindingCond BindingValid → mode.bindingCond BindingValid := by
  cases mode <;> simp [ValidatorMode.dischargeAllEvals] at h
  · subst h; exact ⟨rfl, fun _ _ => trivial⟩
  · subst h; exact ⟨rfl, fun _ hb => hb⟩

/-- **Inductive Invariant Across All 19 Aggregation Shapes (`0..18`):**
Every node derived by `AggrDerivation19` satisfies `AggrNodeHolds`. -/
theorem aggrDerivation19_invariant {sem : AggrSemantics α β γ δ ε κ ι}
    {batchClaim : Nat → ValidatorMode δ → (α → Prop) → (α → Prop) → (β → Prop) → (γ → Prop) → Prop}
    {stmt : AggrNodeStmt α β γ δ ε κ ι}
    (h : AggrDerivation19 sem batchClaim stmt) :
    AggrNodeHolds sem stmt := by
  induction h with
  | leaf hLeaf =>
    exact ⟨hLeaf.checked_under_cond, hLeaf.closed, fun _ _ hF => hF⟩
  | bindingLeaf hb =>
    exact hb
  | evalDischargerLeaf he =>
    exact he
  | wrap _ ih =>
    exact ih
  | pairFlat _ _ _ hJoin hAx ihL ihR =>
    obtain ⟨hChkL, hClL, _⟩ := ihL
    obtain ⟨hChkR, hClR, _⟩ := ihR
    refine ⟨?_, ?_, fun _ _ hF => hF⟩
    · intro hCond x hx
      rcases (hJoin.subjects_iff x).mp hx with hxL | hxR
      · exact sem.checked_mono_ax (fun _ ha => hAx.left_sub ha) (hChkL hCond x hxL)
      · exact sem.checked_mono_ax (fun _ ha => hAx.right_sub ha) (hChkR hCond x hxR)
    · intro x y hx hDep
      rcases (hJoin.subjects_iff x).mp hx with hxL | hxR
      · rcases hClL x y hxL hDep with hSL | hAL
        · exact .inl ((hJoin.subjects_iff y).mpr (.inl hSL))
        · rcases Classical.em _ with hAout | hAout
          · exact .inr hAout
          · exact .inl ((hJoin.subjects_iff y).mpr (.inr (hJoin.discharge_left y hAL hAout)))
      · rcases hClR x y hxR hDep with hSR | hAR
        · exact .inl ((hJoin.subjects_iff y).mpr (.inr hSR))
        · rcases Classical.em _ with hAout | hAout
          · exact .inr hAout
          · exact .inl ((hJoin.subjects_iff y).mpr (.inl (hJoin.discharge_right y hAR hAout)))
  | pairStructural _ _ _ hJoin hAx ihL ihR =>
    obtain ⟨hChkL, hClL, _⟩ := ihL
    obtain ⟨hChkR, hClR, _⟩ := ihR
    refine ⟨?_, ?_, fun _ _ hF => hF⟩
    · intro hCond x hx
      rcases (hJoin.subjects_iff x).mp hx with hxL | hxR
      · exact sem.checked_mono_ax (fun _ ha => hAx.left_sub ha) (hChkL hCond x hxL)
      · exact sem.checked_mono_ax (fun _ ha => hAx.right_sub ha) (hChkR hCond x hxR)
    · intro x y hx hDep
      rcases (hJoin.subjects_iff x).mp hx with hxL | hxR
      · rcases hClL x y hxL hDep with hSL | hAL
        · exact .inl ((hJoin.subjects_iff y).mpr (.inl hSL))
        · rcases Classical.em _ with hAout | hAout
          · exact .inr hAout
          · exact .inl ((hJoin.subjects_iff y).mpr (.inr (hJoin.discharge_left y hAL hAout)))
      · rcases hClR x y hxR hDep with hSR | hAR
        · exact .inl ((hJoin.subjects_iff y).mpr (.inr hSR))
        · rcases Classical.em _ with hAout | hAout
          · exact .inr hAout
          · exact .inl ((hJoin.subjects_iff y).mpr (.inl (hJoin.discharge_right y hAR hAout)))
  | rangeLeaf hle =>
    exact ⟨hle, rfl⟩
  | rangeJoin _ _ ihL ihR =>
    obtain ⟨h1, hrL⟩ := ihL
    obtain ⟨h2, hrR⟩ := ihR
    refine ⟨Nat.le_trans h1 h2, ?_⟩
    rw [hrL, hrR, rangeSum_append sem.residualMonoid _ h1 h2]
  | rangeRoot _ _ hZero hClaim ih =>
    obtain ⟨_, hr⟩ := ih
    rw [hr] at hZero
    obtain ⟨hChk, hCl⟩ := sem.batch_balance_sound _ _ _ _ _ _ hZero batchClaim hClaim
    exact ⟨hChk, hCl, fun _ _ hF => hF⟩
  | dischargeBinding _ _ ihC ihB =>
    obtain ⟨hChk, hCl, _⟩ := ihC
    exact ⟨fun _ => hChk ihB, hCl, fun _ _ hF => hF⟩
  | crossBinding _ _ hDisL hDisR hClsL hClsR hJoin hAx ihL ihR =>
    obtain ⟨hChkL, hClL, _⟩ := ihL
    obtain ⟨hChkR, hClR, _⟩ := ihR
    refine ⟨?_, ?_, fun _ _ hF => hF⟩
    · intro _ x hx
      rcases (hJoin.subjects_iff x).mp hx with hxL | hxR
      · have hC := hChkL (validatorMode_bindingCond_of_discharged hDisL) x hxL
        rcases hClsL with hEq | hlc
        · subst hEq
          exact sem.checked_mono_ax (fun _ ha => hAx.left_sub ha) hC
        · exact sem.checked_mono_ax (fun _ ha => hAx.left_sub ha) (sem.checked_to_class hlc hC)
      · have hC := hChkR (validatorMode_bindingCond_of_discharged hDisR) x hxR
        rcases hClsR with hEq | hlc
        · subst hEq
          exact sem.checked_mono_ax (fun _ ha => hAx.right_sub ha) hC
        · exact sem.checked_mono_ax (fun _ ha => hAx.right_sub ha) (sem.checked_to_class hlc hC)
    · intro x y hx hDep
      rcases (hJoin.subjects_iff x).mp hx with hxL | hxR
      · rcases hClL x y hxL hDep with hSL | hAL
        · exact .inl ((hJoin.subjects_iff y).mpr (.inl hSL))
        · rcases Classical.em _ with hAout | hAout
          · exact .inr hAout
          · exact .inl ((hJoin.subjects_iff y).mpr (.inr (hJoin.discharge_left y hAL hAout)))
      · rcases hClR x y hxR hDep with hSR | hAR
        · exact .inl ((hJoin.subjects_iff y).mpr (.inr hSR))
        · rcases Classical.em _ with hAout | hAout
          · exact .inr hAout
          · exact .inl ((hJoin.subjects_iff y).mpr (.inl (hJoin.discharge_right y hAR hAout)))
  | catalogJoin _ _ hSideL hSideR hUnion ihL ihR =>
    intro b S Ax hMem
    rcases (hUnion (b, S, Ax)).mp hMem with hL | hR
    · rcases hSideL with ⟨mode, SL, AxL, rfl, hDis, hIff⟩ | rfl
      · have heq := (hIff (b, S, Ax)).mp hL
        cases heq
        obtain ⟨hChk, hCl, _⟩ := ihL
        exact ⟨hChk (validatorMode_bindingCond_of_discharged hDis), fun x y hx hDep =>
          (hCl x y hx hDep).elim id False.elim⟩
      · exact ihL b S Ax hL
    · rcases hSideR with ⟨mode, SR, AxR, rfl, hDis, hIff⟩ | rfl
      · have heq := (hIff (b, S, Ax)).mp hR
        cases heq
        obtain ⟨hChk, hCl, _⟩ := ihR
        exact ⟨hChk (validatorMode_bindingCond_of_discharged hDis), fun x y hx hDep =>
          (hCl x y hx hDep).elim id False.elim⟩
      · exact ihR b S Ax hR
  | dynamicLink hDL =>
    exact hDL
  | dischargeEvalStep _ _ _ hRem hAx ihC ihE =>
    obtain ⟨hChk, hCl, hUnl⟩ := ihC
    refine ⟨?_, hCl, hUnl⟩
    intro hCond x hx
    have hC1 := sem.checked_mono_ax (fun _ ha => hAx.left_sub ha) (hChk hCond x hx)
    have hE1 := sem.evalValid_mono_ax (fun _ ha => hAx.right_sub ha) ihE
    exact sem.checked_discharge_eval hRem hE1 hC1
  | dischargeEvalAll hTrans _ _ hRem hAx ihC ihE =>
    obtain ⟨hChk, hCl, _⟩ := ihC
    obtain ⟨hBindEq, hCondImp⟩ := validatorMode_bindingOf_dischargeAll hTrans
    refine ⟨?_, hCl, fun _ _ hF => hF⟩
    intro hCond x hx
    rw [hBindEq]
    have hC1 := sem.checked_mono_ax (fun _ ha => hAx.left_sub ha)
      (hChk (hCondImp sem.BindingValid hCond) x hx)
    have hE1 := sem.evalValid_mono_ax (fun _ ha => hAx.right_sub ha) ihE
    exact sem.checked_discharge_eval hRem hE1 hC1
  | dischargeEvalLinkedFinal hLnk _ _ hRem hAx ihC ihE =>
    obtain ⟨hChk, hCl, _⟩ := ihC
    refine ⟨?_, hCl, fun hFalse => by rw [hLnk] at hFalse; exact absurd hFalse (by decide)⟩
    intro hCond x hx
    have hC1 := sem.checked_mono_ax (fun _ ha => hAx.left_sub ha) (hChk hCond x hx)
    have hE1 := sem.evalValid_mono_ax (fun _ ha => hAx.right_sub ha) ihE
    exact sem.checked_discharge_eval hRem hE1 hC1
  | dischargeEvalViaDynamicLink hToLnk _ _ hRem hRec hMerge ihC ihDL =>
    obtain ⟨hChk, hCl, _⟩ := ihC
    obtain ⟨hLnk, _, _, hBindEq, hCondImp⟩ := validatorMode_toLinkedMode_props hToLnk
    refine ⟨?_, hCl, fun hFalse => by rw [hLnk] at hFalse; exact absurd hFalse (by decide)⟩
    intro hCond x hx
    rw [hBindEq]
    exact sem.checked_discharge_eval_via_link hRem ihDL hRec hMerge
      (hChk (hCondImp sem.BindingValid hCond) x hx)

/-- **Unlinked Validator Guarantee (`aggrDerivation19_unlinked_empty`):**
Every derived `.checkEnv` node whose validator is unlinked (`mode.isLinked = false`,
in particular validators `3`, `4`, `5`, `10`, `11`) has `Linked = ∅`. -/
theorem aggrDerivation19_unlinked_empty {sem : AggrSemantics α β γ δ ε κ ι}
    {batchClaim : Nat → ValidatorMode δ → (α → Prop) → (α → Prop) → (β → Prop) → (γ → Prop) → Prop}
    {mode : ValidatorMode δ} {S A : α → Prop} {Ax : β → Prop}
    {EvalA : γ → Prop} {Linked : ι → Prop}
    (hUnl : mode.isLinked = false)
    (hDeriv : AggrDerivation19 sem batchClaim (.checkEnv mode S A Ax EvalA Linked)) :
    ∀ l, ¬ Linked l :=
  (aggrDerivation19_invariant hDeriv).2.2 hUnl

/-- **End-to-End 19-Shape Unlinked `CheckEnv` Soundness (`aggrDerivation19_checkEnv_sound`):**
For any unconditional, unlinked `CheckEnv` root (`validator ∈ {3, 5}`, `A = ∅`, `EvalA = ∅`,
`Linked = ∅`, explicit user axiom set `Ax`) derived across ANY combination of the 19 aggregation
shapes (`0..18`), every subject `x ∈ S` satisfies `Valid mode.bindingOf Ax x` by well-founded
induction along `Dep` — using ZERO external linked circuits. -/
theorem aggrDerivation19_checkEnv_sound {sem : AggrSemantics α β γ δ ε κ ι}
    {batchClaim : Nat → ValidatorMode δ → (α → Prop) → (α → Prop) → (β → Prop) → (γ → Prop) → Prop}
    {Valid : δ → (β → Prop) → α → Prop}
    (hWf : WellFounded (fun y x => sem.Dep x y))
    (hStep : ∀ b Ax x, sem.Checked b Ax (fun _ => False) (fun _ => False) x →
      (∀ y, sem.Dep x y → Valid b Ax y) → Valid b Ax x)
    {mode : ValidatorMode δ} {S : α → Prop} {Ax : β → Prop}
    (hDis : mode.isBindingDischarged = true)
    (hDeriv : AggrDerivation19 sem batchClaim
      (.checkEnv mode S (fun _ => False) Ax (fun _ => False) (fun _ => False))) :
    ∀ x, S x → Valid mode.bindingOf Ax x := by
  obtain ⟨hChk, hCl, _⟩ := aggrDerivation19_invariant hDeriv
  have hChecked := hChk (validatorMode_bindingCond_of_discharged hDis)
  have hClosed : ∀ x y, S x → sem.Dep x y → S y := fun x y hx hDep =>
    (hCl x y hx hDep).elim id False.elim
  intro x
  induction x using hWf.induction with
  | h x ih =>
    intro hx
    exact hStep _ _ x (hChecked x hx) (fun y hDep => ih y hDep (hClosed x y hx hDep))

/-- **End-to-End 19-Shape Linked `CheckEnv` Soundness (`aggrDerivation19_linked_checkEnv_sound`):**
For any validator `12` (`linked b`) root with `A = ∅`, `EvalA = ∅`, explicit user axioms `Ax`,
and explicit `Linked` circuit accumulator, every subject `x ∈ S` satisfies `Valid b Ax Linked x`
under the explicitly committed `Linked` circuits. -/
theorem aggrDerivation19_linked_checkEnv_sound {sem : AggrSemantics α β γ δ ε κ ι}
    {batchClaim : Nat → ValidatorMode δ → (α → Prop) → (α → Prop) → (β → Prop) → (γ → Prop) → Prop}
    {Valid : δ → (β → Prop) → (ι → Prop) → α → Prop}
    (hWf : WellFounded (fun y x => sem.Dep x y))
    (hStep : ∀ b Ax Linked x, sem.Checked b Ax (fun _ => False) Linked x →
      (∀ y, sem.Dep x y → Valid b Ax Linked y) → Valid b Ax Linked x)
    {b : δ} {S : α → Prop} {Ax : β → Prop} {Linked : ι → Prop}
    (hDeriv : AggrDerivation19 sem batchClaim
      (.checkEnv (.linked b) S (fun _ => False) Ax (fun _ => False) Linked)) :
    ∀ x, S x → Valid b Ax Linked x := by
  obtain ⟨hChk, hCl, _⟩ := aggrDerivation19_invariant hDeriv
  have hChecked := hChk trivial
  have hClosed : ∀ x y, S x → sem.Dep x y → S y := fun x y hx hDep =>
    (hCl x y hx hDep).elim id False.elim
  intro x
  induction x using hWf.induction with
  | h x ih =>
    intro hx
    exact hStep _ _ _ x (hChecked x hx) (fun y hDep => ih y hDep (hClosed x y hx hDep))

/-- **End-to-End 19-Shape `Catalog` Soundness (`aggrDerivation19_catalog_sound`):**
Every member `(b, S, Ax)` of a derived `Catalog` root certifies `Valid b Ax x` for
every subject `x ∈ S` (with `Linked = ∅`). -/
theorem aggrDerivation19_catalog_sound {sem : AggrSemantics α β γ δ ε κ ι}
    {batchClaim : Nat → ValidatorMode δ → (α → Prop) → (α → Prop) → (β → Prop) → (γ → Prop) → Prop}
    {Valid : δ → (β → Prop) → α → Prop}
    (hWf : WellFounded (fun y x => sem.Dep x y))
    (hStep : ∀ b Ax x, sem.Checked b Ax (fun _ => False) (fun _ => False) x →
      (∀ y, sem.Dep x y → Valid b Ax y) → Valid b Ax x)
    {members : (δ × (α → Prop) × (β → Prop)) → Prop}
    (hDeriv : AggrDerivation19 sem batchClaim (.catalogStmt members)) :
    ∀ b S Ax, members (b, S, Ax) → ∀ x, S x → Valid b Ax x := by
  have hCat := aggrDerivation19_invariant hDeriv
  intro b S Ax hMem x
  obtain ⟨hChecked, hClosed⟩ := hCat b S Ax hMem
  induction x using hWf.induction with
  | h x ih =>
    intro hx
    exact hStep b Ax x (hChecked x hx) (fun y hDep => ih y hDep (hClosed x y hx hDep))

/-- **End-to-End Shape 17 `DynamicLink` Soundness (`aggrDerivation19_dynamicLink_sound`):**
Every derived `DynamicLink` root certifies `sem.DynamicLinkValid stmt`. -/
theorem aggrDerivation19_dynamicLink_sound {sem : AggrSemantics α β γ δ ε κ ι}
    {batchClaim : Nat → ValidatorMode δ → (α → Prop) → (α → Prop) → (β → Prop) → (γ → Prop) → Prop}
    {stmt : κ}
    (hDeriv : AggrDerivation19 sem batchClaim (.dynamicLinkStmt stmt)) :
    sem.DynamicLinkValid stmt :=
  aggrDerivation19_invariant hDeriv

end Aggr
end
