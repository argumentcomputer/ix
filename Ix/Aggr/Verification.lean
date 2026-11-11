module
public import Ix.Aggr.Host
public import Ix.Ixon

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
single linear audit checks that those leaves are exactly the constants in Lean's
logic of the supplied environment (`Ixon.Env.inLogicConsts`): no omissions,
foreign leaves, or duplicates. The unsafe and partial constants are no claim's
subjects (`KernelClaim::assert_claimable`); a leaf among them counts as foreign. -/
def auditAggregateConstants (env : Ixon.Env) (statement : Aggr.CheckEnvTrees) :
    Except String Nat := do
  if let some assumptions := statement.assumptions then
    throw s!"aggregate root retains undischarged assumptions {assumptions.root}"
  let leaves := statement.subjects.leaves
  let claimable := env.inLogicConsts
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
      (first {sample firstMissing}), {foreign} foreign or outside Lean's logic \
      (first {sample firstForeign}), {duplicates} duplicate occurrence(s) \
      (first {sample firstDuplicate}); environment has {claimable.size} constants \
      in Lean's logic ({env.consts.size} in all), subject tree has {leaves.size} leaves"
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

end Aggr
end
