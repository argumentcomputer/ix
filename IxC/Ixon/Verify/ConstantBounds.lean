import IxC.Ixon.Verify.ReaderBounds

namespace Ixon.Verify.ConstantBounds

open Ixon ReaderBounds

/-- Ixon validates flag bytes before the payload: a rejected flag stops. -/
theorem guard_bound {p : Prop} [Decidable p] {rest : GetM α} {units : α → Nat} (reason : String)
    (h : ReaderBound rest units) :
    ReaderBound (if p then (throw reason : GetM PUnit) >>= (fun _ => rest) else rest) units := by
  split
  · exact (throw_bound reason (fun _ => 0)).bind (fun _ => h) units (fun _ _ => by omega)
  · exact h

/-- The strict Boolean reader consumes one byte. -/
theorem getBool_bound : ReaderBound (Serialize.get (α := Bool)) (fun _ => 2) := by
  intro start finish value valid read
  change (EStateM.bind getU8 _) start = _ at read
  obtain ⟨byte, middle, byteRead, read⟩ := bind_ok.mp read
  have byteSpan := getU8_bound _ _ _ valid byteRead
  split at read <;> first | (cases read; exact byteSpan) | cases read

theorem getDefinition_bound : ReaderBound getDefinition Definition.resourceSize := by
  unfold getDefinition
  apply getU8_bound.skip
  intro mode
  refine guard_bound _ ?_
  apply (getTagN_bound 0).skip
  intro levels
  exact getExpr_bound.bind_map (fun _ => getExpr_bound) _ _
    (fun type value => by simp [Definition.resourceSize]; omega)

theorem getRecursorRule_bound : ReaderBound getRecursorRule RecursorRule.resourceSize := by
  unfold getRecursorRule
  apply (getTagN_bound 0).skip
  intro fields
  exact getExpr_bound.map _ _ (fun rhs => by simp [RecursorRule.resourceSize, Nat.add_comm])

theorem getAxiom_bound : ReaderBound getAxiom Axiom.resourceSize := by
  unfold getAxiom
  apply getBool_bound.skip
  intro unsafeFlag
  apply (getTagN_bound 0).skip
  intro levels
  exact getExpr_bound.map _ _ (fun type => by simp [Axiom.resourceSize, Nat.add_comm])

theorem getConstructor_bound : ReaderBound getConstructor Constructor.resourceSize := by
  unfold getConstructor
  apply getBool_bound.skip
  intro unsafeFlag
  apply (getTagN_bound 0).skip
  intro levels
  apply (getTagN_bound 0).skip
  intro index
  apply (getTagN_bound 0).skip
  intro params
  apply (getTagN_bound 0).skip
  intro fields
  exact getExpr_bound.map _ _ (fun type => by simp [Constructor.resourceSize, Nat.add_comm])

theorem getQuotient_bound : ReaderBound getQuotient Quotient.resourceSize := by
  unfold getQuotient
  apply getU8_bound.skip
  intro tag
  have payload (kind : Ix.QuotKind) : ReaderBound (do
      let levels ← getTagN 0
      let type ← getExpr
      pure (⟨kind, levels.value, type⟩ : Quotient)) Quotient.resourceSize := by
    apply (getTagN_bound 0).skip
    intro levels
    exact getExpr_bound.map _ _ (fun type => by simp [Quotient.resourceSize, Nat.add_comm])
  intro start finish value valid read
  split at read
  · exact payload .type _ _ _ valid read
  · exact payload .ctor _ _ _ valid read
  · exact payload .lift _ _ _ valid read
  · exact payload .ind _ _ _ valid read
  · cases read

theorem getInductiveProj_bound : ReaderBound getInductiveProj (fun _ => 0) := by
  unfold getInductiveProj
  apply (getTagN_bound 0).skip
  intro index
  exact address_bound.map _ _ (fun _ => Nat.zero_le _)

theorem getRecursorProj_bound : ReaderBound getRecursorProj (fun _ => 0) := by
  unfold getRecursorProj
  apply (getTagN_bound 0).skip
  intro index
  exact address_bound.map _ _ (fun _ => Nat.zero_le _)

theorem getDefinitionProj_bound : ReaderBound getDefinitionProj (fun _ => 0) := by
  unfold getDefinitionProj
  apply (getTagN_bound 0).skip
  intro index
  exact address_bound.map _ _ (fun _ => Nat.zero_le _)

theorem getConstructorProj_bound : ReaderBound getConstructorProj (fun _ => 0) := by
  unfold getConstructorProj
  apply (getTagN_bound 0).skip
  intro index
  apply (getTagN_bound 0).skip
  intro ctorIndex
  exact address_bound.map _ _ (fun _ => Nat.zero_le _)

open Codec.RecursorConstant in
theorem getRecursorRules_bound (k unsafeFlag : Bool) (levels params indices motives minors : UInt64)
    (type : Expr) : ReaderBound (getRecursorRules k unsafeFlag levels params indices motives minors type)
      (fun value => value.resourceSize - (type.resourceSize + 1)) := by
  unfold getRecursorRules
  apply (getTagN_bound 0).skip
  intro count
  apply (checkCount_bound _ _).skip
  intro checked
  simpa [getArray] using (getArray_bound _ _ getRecursorRule_bound count.value.toNat).map
    (fun rules => (⟨k, unsafeFlag, levels, params, indices, motives, minors, type, rules⟩ : Recursor))
    (fun value => value.resourceSize - (type.resourceSize + 1))
    (fun _ => by simp [Recursor.resourceSize, Nat.add_comm])

open Codec.RecursorConstant in
theorem getRecursor_bound : ReaderBound getRecursor Recursor.resourceSize := by
  rw [getRecursor_eq]
  apply getU8_bound.skip
  intro flags
  unfold getRecursorFromFlags getRecursorAfterFlags
  refine guard_bound _ ?_
  apply (getTagN_bound 0).skip
  intro levels
  apply (getTagN_bound 0).skip
  intro params
  apply (getTagN_bound 0).skip
  intro indices
  apply (getTagN_bound 0).skip
  intro motives
  apply (getTagN_bound 0).skip
  intro minors
  exact getExpr_bound.bind (fun type => getRecursorRules_bound _ _ _ _ _ _ _ type) _
    (fun type value => by omega)

open Codec.MutualConstant in
theorem getInductiveConstructors_bound (unsafeFlag : Bool) (levels params indices : UInt64)
    (type : Expr) : ReaderBound (getInductiveConstructors unsafeFlag levels params indices type)
      (fun value => value.resourceSize - (type.resourceSize + 1)) := by
  unfold getInductiveConstructors
  apply (getTagN_bound 0).skip
  intro count
  apply (checkCount_bound _ _).skip
  intro checked
  simpa [getArray] using (getArray_bound _ _ getConstructor_bound count.value.toNat).map
    (fun ctors => (⟨unsafeFlag, levels, params, indices, type, ctors⟩ : Inductive))
    (fun value => value.resourceSize - (type.resourceSize + 1))
    (fun _ => by simp [Inductive.resourceSize, Nat.add_comm])

open Codec.MutualConstant in
theorem getInductive_bound : ReaderBound getInductive Inductive.resourceSize := by
  rw [getInductive_eq]
  apply getBool_bound.skip
  intro unsafeFlag
  unfold getInductiveAfterFlags
  apply (getTagN_bound 0).skip
  intro levels
  apply (getTagN_bound 0).skip
  intro params
  apply (getTagN_bound 0).skip
  intro indices
  exact getExpr_bound.bind (fun type => getInductiveConstructors_bound _ _ _ _ type) _
    (fun type value => by omega)

open Codec.MutualConstant in
theorem getMutConst_bound : ReaderBound getMutConst MutConst.resourceSize := by
  rw [getMutConst_eq]
  apply getU8_bound.bind (rightUnits := fun _ value => value.resourceSize - 1)
    (fun tag => ?_) _ (fun _ value => by omega)
  unfold getMutConstFromTag
  split
  · exact getDefinition_bound.map _ _ (fun _ => by simp [MutConst.resourceSize])
  · exact getInductive_bound.map _ _ (fun _ => by simp [MutConst.resourceSize])
  · exact getRecursor_bound.map _ _ (fun _ => by simp [MutConst.resourceSize])
  · exact throw_bound _ _

theorem getConstantInfo_bound : ReaderBound getConstantInfo ConstantInfo.resourceSize := by
  unfold getConstantInfo
  apply (getTagN_bound 4).bind (rightUnits := fun _ value => value.resourceSize - 1)
    (fun tag => ?_) _ (fun _ value => by omega)
  by_cases mutualTag : (tag.flag == Constant.FLAG_MUTS) = true
  · simp only [ite_eq_left mutualTag]
    simpa [getArray] using (getArray_bound _ _ getMutConst_bound tag.value.toNat).map
      ConstantInfo.muts (fun value => value.resourceSize - 1)
      (fun _ => by simp [ConstantInfo.resourceSize])
  · simp only [ite_eq_right mutualTag]
    by_cases singleTag : (tag.flag == Constant.FLAG) = true
    · simp only [ite_eq_left singleTag]
      split
      · exact getDefinition_bound.map _ _ (fun _ => by simp [ConstantInfo.resourceSize])
      · exact getRecursor_bound.map _ _ (fun _ => by simp [ConstantInfo.resourceSize])
      · exact getAxiom_bound.map _ _ (fun _ => by simp [ConstantInfo.resourceSize])
      · exact getQuotient_bound.map _ _ (fun _ => by simp [ConstantInfo.resourceSize])
      · exact getConstructorProj_bound.map _ _ (fun _ => by simp [ConstantInfo.resourceSize])
      · exact getRecursorProj_bound.map _ _ (fun _ => by simp [ConstantInfo.resourceSize])
      · exact getInductiveProj_bound.map _ _ (fun _ => by simp [ConstantInfo.resourceSize])
      · exact getDefinitionProj_bound.map _ _ (fun _ => by simp [ConstantInfo.resourceSize])
      · exact throw_bound _ _
    · simp only [ite_eq_right singleTag]
      exact throw_bound _ _

/-- Universe parsing also preserves the buffer and consumes a tag. This
lemma intentionally measures only byte progress; compressed successor
allocation is controlled by the separate expanded-node budget. -/
theorem getUnivFromTag_progress (recur : GetM Univ)
    (bound : ReaderBound recur (fun _ => 2)) (tag : TagN) :
    ReaderBound (getUnivFromTag recur tag) (fun _ => 0) := by
  unfold getUnivFromTag
  split
  · split
    · exact pure_bound _
    · exact bound.map _ _ (fun _ => Nat.zero_le _)
  · exact bound.bind_map (fun _ => bound) Univ.max _ (fun _ _ => Nat.zero_le _)
  · exact bound.bind_map (fun _ => bound) Univ.imax _ (fun _ _ => Nat.zero_le _)
  · exact pure_bound _
  · exact throw_bound _ _

theorem getUnivFuel_progress (fuel : Nat) : ReaderBound (getUnivFuel fuel) (fun _ => 2) := by
  induction fuel with
  | zero => exact throw_bound _ _
  | succ fuel ih =>
    exact (getTagN_bound 2).bind (fun tag => getUnivFromTag_progress _ ih tag) _
      (fun _ _ => Nat.le_refl _)

theorem getUniv_progress : ReaderBound getUniv (fun _ => 2) := by
  intro start finish value valid read
  change getUnivFuel (start.bytes.size - start.idx + 1) start = .ok value finish at read
  exact getUnivFuel_progress _ _ _ _ valid read

/-- Every non-universe component of a production constant is structurally
bounded by consumed bytes. The result includes declaration and expression
constructors, reference-index vectors, and reference/universe table slots.
No canonicality or wire-well-formedness premise is required. -/
theorem getConstant_bound : ReaderBound getConstant Constant.resourceSize := by
  intro start finish value valid read
  unfold getConstant getConstantWithUnivs at read
  obtain ⟨info, infoState, infoRead, read⟩ := bind_ok.mp read
  have infoSpan := getConstantInfo_bound _ _ _ valid infoRead
  obtain ⟨sharingCount, sharingState, sharingCountRead, read⟩ := bind_ok.mp read
  have sharingCountSpan := (getTagN_bound 0) _ _ _ infoSpan.valid sharingCountRead
  obtain ⟨sharing, refsCountState, sharingRead, read⟩ := bind_ok.mp read
  have sharingBound := getExpr_bound.weaken Expr.resourceSize (fun _ => by omega)
  have sharingSpan := getArray_bound _ _ sharingBound _ _ _ _ sharingCountSpan.valid sharingRead
  obtain ⟨refsCount, refsState, refsCountRead, read⟩ := bind_ok.mp read
  have refsCountSpan := (getTagN_bound 0) _ _ _ sharingSpan.valid refsCountRead
  obtain ⟨refs, univsCountState, refsRead, read⟩ := bind_ok.mp read
  have refsBound := address_bound.weaken (fun _ => 1) (fun _ => by decide)
  have refsSpan : Span refsState univsCountState refs.size := by
    simpa [sum_const] using getArray_bound _ _ refsBound _ _ _ _ refsCountSpan.valid refsRead
  obtain ⟨univsCount, univsState, univsCountRead, read⟩ := bind_ok.mp read
  have univsCountSpan := (getTagN_bound 0) _ _ _ refsSpan.valid univsCountRead
  obtain ⟨univs, final, univsRead, result⟩ := bind_ok.mp read
  have univsBound := getUniv_progress.weaken (fun _ => 1) (fun _ => by decide)
  have univsSpan : Span univsState final univs.size := by
    simpa [sum_const] using getArray_bound _ _ univsBound _ _ _ _ univsCountSpan.valid univsRead
  change EStateM.Result.ok _ _ = .ok value finish at result
  cases result
  exact ((((((infoSpan.trans sharingCountSpan).trans sharingSpan).trans refsCountSpan).trans
    refsSpan).trans univsCountSpan).trans univsSpan).weaken (by dsimp [Constant.resourceSize]; omega)

theorem deConstantExact_resource_bound (bytes : ByteArray) (value : Constant)
    (read : deConstantExact bytes = .ok value) : value.resourceSize ≤ 2 * bytes.size :=
  getConstant_bound.runGetExact bytes value read

/-- The existing bounded record API controls the whole decoded structure:
ordinary components are bounded by bytes; universe expansion has its shared
node limit. This adds a theorem, not another validation pass. -/
theorem boundedConstant_resource_bound (maxBytes maxUnivNodes : Nat) (bytes : ByteArray)
    (value : Constant) (read : Bounded.deConstant maxBytes maxUnivNodes bytes = .ok value) :
    value.resourceSize + Bounded.univNodes value.univs ≤ 2 * maxBytes + maxUnivNodes := by
  obtain ⟨bytesFit, nodesFit, exactRead⟩ := BoundedConstant.deConstant_spec _ _ _ _ read
  have structural := deConstantExact_resource_bound _ _ exactRead
  omega

end Ixon.Verify.ConstantBounds
