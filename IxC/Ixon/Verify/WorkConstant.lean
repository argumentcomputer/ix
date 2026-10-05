import IxC.Ixon.Verify.WorkExpr
import IxC.Ixon.Verify.WorkArray
import IxC.Ixon.Verify.WorkUniverse

namespace Ixon.Verify.Work

open Ixon

/-- Ixon's strict Boolean byte. -/
def bool : M Bool := do
  let byte ← u8
  match byte with
  | 0 => pure false
  | 1 => pure true
  | e => fail s!"expected Bool (0 or 1), got {e}"

def defn : M Definition := do
  let flags ← u8
  reject (flags >>> 2 > 2 || (flags &&& 3) > 2) "invalid definition kind/safety"
  let (kind, safety) := unpackDefKindSafety flags
  let lvls ← tagN 0
  let typ ← expr
  let value ← expr
  charged 1 (pure ⟨kind, safety, lvls.value, typ, value⟩)

def recursorRule : M RecursorRule := do
  let fields ← tagN 0
  let rhs ← expr
  charged 1 (pure ⟨fields.value, rhs⟩)

def recursor : M Recursor := do
  let flags ← u8
  reject (flags > 3) "invalid recursor flags"
  let bools := unpackBools 2 flags
  let lvls ← tagN 0
  let params ← tagN 0
  let indices ← tagN 0
  let motives ← tagN 0
  let minors ← tagN 0
  let typ ← expr
  let count ← tagN 0
  check count.value.toNat.toUInt64 2
  let rules ← array recursorRule count.value.toNat
  charged 1 (pure ⟨bools[0]!, bools[1]!, lvls.value, params.value, indices.value,
    motives.value, minors.value, typ, rules⟩)

def axiomDecl : M Axiom := do
  let isUnsafe ← bool
  let lvls ← tagN 0
  let typ ← expr
  charged 1 (pure ⟨isUnsafe, lvls.value, typ⟩)

def quotient : M Quotient := do
  let flags ← u8
  let kind : Ix.QuotKind ← match flags with
    | 0 => pure .type | 1 => pure .ctor | 2 => pure .lift | 3 => pure .ind
    | _ => fail s!"invalid QuotKind tag {flags}"
  let lvls ← tagN 0
  let typ ← expr
  charged 1 (pure ⟨kind, lvls.value, typ⟩)

def ctor : M Constructor := do
  let isUnsafe ← bool
  let lvls ← tagN 0
  let cidx ← tagN 0
  let params ← tagN 0
  let fields ← tagN 0
  let typ ← expr
  charged 1 (pure ⟨isUnsafe, lvls.value, cidx.value, params.value, fields.value, typ⟩)

def inductiveDecl : M Inductive := do
  let isUnsafe ← bool
  let lvls ← tagN 0
  let params ← tagN 0
  let indices ← tagN 0
  let typ ← expr
  let count ← tagN 0
  check count.value.toNat.toUInt64 6
  let ctors ← array ctor count.value.toNat
  charged 1 (pure ⟨isUnsafe, lvls.value, params.value, indices.value, typ, ctors⟩)

def inductiveProj : M InductiveProj := do
  let idx ← tagN 0
  let block ← address
  charged 1 (pure ⟨idx.value, block⟩)

def constructorProj : M ConstructorProj := do
  let idx ← tagN 0
  let cidx ← tagN 0
  let block ← address
  charged 1 (pure ⟨idx.value, cidx.value, block⟩)

def recursorProj : M RecursorProj := do
  let idx ← tagN 0
  let block ← address
  charged 1 (pure ⟨idx.value, block⟩)

def definitionProj : M DefinitionProj := do
  let idx ← tagN 0
  let block ← address
  charged 1 (pure ⟨idx.value, block⟩)

def wrap (make : α → β) (reader : M α) : M β := do
  let value ← reader
  charged 1 (pure (make value))

def mutConst : M MutConst := do
  let tag ← u8
  match tag with
  | 0 => wrap MutConst.defn defn
  | 1 => wrap MutConst.indc inductiveDecl
  | 2 => wrap MutConst.recr recursor
  | t => fail s!"getMutConst: invalid tag {t}"

def constantInfo : M ConstantInfo := do
  let tag ← tagN 4
  if tag.flag == Constant.FLAG_MUTS then
    wrap ConstantInfo.muts (array mutConst tag.value.toNat)
  else if tag.flag == Constant.FLAG then
    match tag.value with
    | 0 => wrap ConstantInfo.defn defn
    | 1 => wrap ConstantInfo.recr recursor
    | 2 => wrap ConstantInfo.axio axiomDecl
    | 3 => wrap ConstantInfo.quot quotient
    | 4 => wrap ConstantInfo.cPrj constructorProj
    | 5 => wrap ConstantInfo.rPrj recursorProj
    | 6 => wrap ConstantInfo.iPrj inductiveProj
    | 7 => wrap ConstantInfo.dPrj definitionProj
    | v => fail s!"getConstantInfo: invalid variant {v}"
  else fail s!"getConstantInfo: invalid flag {tag.flag}"

/-- The tuple exposes the shared grammar prefix in proofs only. Its work is
charged conservatively even though production does not allocate this tuple. -/
def recordPrefix : M (ConstantInfo × Array Expr × Array Address × Nat) := do
  let info ← constantInfo
  let sharingCount ← tagN 0
  let sharing ← array expr sharingCount.value.toNat
  let refsCount ← tagN 0
  let refs ← array address refsCount.value.toNat
  let univsCount ← tagN 0
  charged 1 (pure (info, sharing, refs, univsCount.value.toNat))

def constant (budget : Nat) : M Constant := do
  let (info, sharing, refs, count) ← recordPrefix
  let (univs, _) ← univArray count budget
  charged 1 (pure ⟨info, sharing, refs, univs⟩)

theorem bool_erases : Erases bool (Serialize.get (α := Bool)) := by
  unfold bool
  apply u8_erases.bind
  intro byte
  split <;> simp_all only
  all_goals first | exact pure_erases _ | exact fail_erases _

theorem defn_erases : Erases defn getDefinition := by
  unfold defn getDefinition
  exact u8_erases.bind fun _ => reject_erases _ _ ((tagN_erases 0).bind fun _ =>
    expr_erases.bind fun _ => expr_erases.bind fun _ => (pure_erases _).charged 1)

theorem recursorRule_erases : Erases recursorRule getRecursorRule := by
  unfold recursorRule getRecursorRule
  exact (tagN_erases 0).bind fun _ => expr_erases.bind fun _ => (pure_erases _).charged 1

theorem recursor_erases : Erases recursor getRecursor := by
  unfold recursor getRecursor
  apply u8_erases.bind
  intro flags
  apply reject_erases
  apply (tagN_erases 0).bind
  intro lvls
  apply (tagN_erases 0).bind
  intro params
  apply (tagN_erases 0).bind
  intro indices
  apply (tagN_erases 0).bind
  intro motives
  apply (tagN_erases 0).bind
  intro minors
  apply expr_erases.bind
  intro typ
  apply (tagN_erases 0).bind
  intro count
  apply (check_erases _ _).bind
  intro checked
  have h := (array_erases recursorRule_erases count.value.toNat).bind
    (fun rules => (pure_erases (⟨(unpackBools 2 flags)[0]!, (unpackBools 2 flags)[1]!,
      lvls.value, params.value, indices.value, motives.value, minors.value, typ, rules⟩ : Recursor)).charged 1)
  refine h.trans ?_
  simp only [getArray, bind_assoc, pure_bind]

theorem axiomDecl_erases : Erases axiomDecl getAxiom := by
  unfold axiomDecl getAxiom
  exact bool_erases.bind fun _ => (tagN_erases 0).bind fun _ => expr_erases.bind fun _ =>
    (pure_erases _).charged 1

theorem quotient_erases : Erases quotient getQuotient := by
  unfold quotient getQuotient
  apply u8_erases.bind
  intro flags
  split <;> simp_all only
  all_goals first
  | exact fail_erases _
  | exact (tagN_erases 0).bind fun _ => expr_erases.bind fun _ => (pure_erases _).charged 1

theorem ctor_erases : Erases ctor getConstructor := by
  unfold ctor getConstructor
  exact bool_erases.bind fun _ => (tagN_erases 0).bind fun _ => (tagN_erases 0).bind fun _ =>
    (tagN_erases 0).bind fun _ => (tagN_erases 0).bind fun _ => expr_erases.bind fun _ =>
    (pure_erases _).charged 1

theorem inductiveDecl_erases : Erases inductiveDecl getInductive := by
  unfold inductiveDecl getInductive
  apply bool_erases.bind
  intro isUnsafe
  apply (tagN_erases 0).bind
  intro lvls
  apply (tagN_erases 0).bind
  intro params
  apply (tagN_erases 0).bind
  intro indices
  apply expr_erases.bind
  intro typ
  apply (tagN_erases 0).bind
  intro count
  apply (check_erases _ _).bind
  intro checked
  have h := (array_erases ctor_erases count.value.toNat).bind
    (fun ctors => (pure_erases (⟨isUnsafe, lvls.value, params.value,
      indices.value, typ, ctors⟩ : Inductive)).charged 1)
  refine h.trans ?_
  simp only [getArray, bind_assoc, pure_bind]

theorem inductiveProj_erases : Erases inductiveProj getInductiveProj := by
  unfold inductiveProj getInductiveProj
  exact (tagN_erases 0).bind fun _ => address_erases.bind fun _ => (pure_erases _).charged 1

theorem constructorProj_erases : Erases constructorProj getConstructorProj := by
  unfold constructorProj getConstructorProj
  exact (tagN_erases 0).bind fun _ => (tagN_erases 0).bind fun _ => address_erases.bind fun _ =>
    (pure_erases _).charged 1

theorem recursorProj_erases : Erases recursorProj getRecursorProj := by
  unfold recursorProj getRecursorProj
  exact (tagN_erases 0).bind fun _ => address_erases.bind fun _ => (pure_erases _).charged 1

theorem definitionProj_erases : Erases definitionProj getDefinitionProj := by
  unfold definitionProj getDefinitionProj
  exact (tagN_erases 0).bind fun _ => address_erases.bind fun _ => (pure_erases _).charged 1

theorem wrap_erases {metered : M α} {reader : GetM α} (same : Erases metered reader) (make : α → β) :
    Erases (wrap make metered) (make <$> reader) :=
  same.bind fun _ => (pure_erases _).charged 1

theorem mutConst_erases : Erases mutConst getMutConst := by
  unfold mutConst getMutConst
  apply u8_erases.bind
  intro tag
  split <;> simp_all only
  · exact wrap_erases defn_erases _
  · exact wrap_erases inductiveDecl_erases _
  · exact wrap_erases recursor_erases _
  · exact fail_erases _

theorem constantInfo_erases : Erases constantInfo getConstantInfo := by
  unfold constantInfo getConstantInfo
  apply (tagN_erases 4).bind
  intro tag
  split
  · simpa only [getArray, map_eq_pure_bind, bind_pure] using
      wrap_erases (array_erases mutConst_erases tag.value.toNat) ConstantInfo.muts
  · split
    · split <;> simp_all only
      · exact wrap_erases defn_erases _
      · exact wrap_erases recursor_erases _
      · exact wrap_erases axiomDecl_erases _
      · exact wrap_erases quotient_erases _
      · exact wrap_erases constructorProj_erases _
      · exact wrap_erases recursorProj_erases _
      · exact wrap_erases inductiveProj_erases _
      · exact wrap_erases definitionProj_erases _
      · exact fail_erases _
    · exact fail_erases _

theorem prefix_erases : Erases recordPrefix BoundedConstant.getPrefix := by
  unfold recordPrefix BoundedConstant.getPrefix
  exact constantInfo_erases.bind fun _ => (tagN_erases 0).bind fun _ =>
    (array_erases expr_erases _).bind fun _ => (tagN_erases 0).bind fun _ =>
    (array_erases address_erases _).bind fun _ => (tagN_erases 0).bind fun _ =>
    (pure_erases _).charged 1

theorem constant_erases (budget : Nat) : Erases (constant budget) (Bounded.getConstant budget) := by
  unfold constant Bounded.getConstant
  rw [BoundedConstant.getConstantWithUnivs_eq]
  apply prefix_erases.bind
  rintro ⟨info, sharing, refs, count⟩
  simp only [map_eq_pure_bind, bind_assoc, pure_bind]
  apply (univArray_erases count budget).bind
  rintro ⟨univs, remaining⟩
  exact (pure_erases _).charged 1

theorem bool_bound : Bound bool 16 0 (fun _ => 15) := by
  unfold bool
  apply (u8_bound 16 (by decide)).bind
  intro byte
  split
  all_goals first
  | exact pure_bound _ _ _ _ (Nat.le_refl _)
  | exact fail_bound _ _ _ _

theorem defn_bound : Bound defn 16 0 (fun _ => 2) := by
  unfold defn
  apply (u8_bound 16 (by decide)).bind_zero
  intro flags
  apply (reject_bound 16 0 _ _).bind
  intro checked
  apply (tagN_bound 0 16 (by decide)).bind_zero
  intro lvls
  apply expr_bound.bind_zero
  intro typ
  exact expr_bound.bind fun _ => charged_pure_bound _ _ _ _ _ (by decide)

theorem recursorRule_bound : Bound recursorRule 16 0 (fun _ => 2) := by
  unfold recursorRule
  apply (tagN_bound 0 16 (by decide)).bind_zero
  intro fields
  exact expr_bound.bind fun _ => charged_pure_bound _ _ _ _ _ (by decide)

theorem recursor_bound : Bound recursor 16 0 (fun _ => 2) := by
  unfold recursor
  apply (u8_bound 16 (by decide)).bind_zero
  intro flags
  apply (reject_bound 16 0 _ _).bind
  intro checked
  apply (tagN_bound 0 16 (by decide)).bind_zero
  intro lvls
  apply (tagN_bound 0 16 (by decide)).bind_zero
  intro params
  apply (tagN_bound 0 16 (by decide)).bind_zero
  intro indices
  apply (tagN_bound 0 16 (by decide)).bind_zero
  intro motives
  apply (tagN_bound 0 16 (by decide)).bind_zero
  intro minors
  apply expr_bound.bind_zero
  intro typ
  apply (tagN_bound 0 16 (by decide)).bind
  intro count
  apply (check_bound _ _ _ _).bind
  intro checked
  exact ((array_bound recursorRule_bound _).carry 14).bind fun _ =>
    charged_pure_bound _ _ _ _ _ (by decide)

theorem axiomDecl_bound : Bound axiomDecl 16 0 (fun _ => 2) := by
  unfold axiomDecl
  apply bool_bound.bind_zero
  intro isUnsafe
  apply (tagN_bound 0 16 (by decide)).bind_zero
  intro lvls
  exact expr_bound.bind fun _ => charged_pure_bound _ _ _ _ _ (by decide)

theorem quotient_bound : Bound quotient 16 0 (fun _ => 2) := by
  unfold quotient
  apply (u8_bound 16 (by decide)).bind_zero
  intro flags
  split <;> simp only [Bind.bind, bind_pure_left, bind_fail_left]
  all_goals first
  | exact fail_bound _ _ _ _
  | apply (tagN_bound 0 16 (by decide)).bind_zero
    intro lvls
    exact expr_bound.bind fun _ => charged_pure_bound _ _ _ _ _ (by decide)

theorem ctor_bound : Bound ctor 16 0 (fun _ => 2) := by
  unfold ctor
  apply bool_bound.bind_zero
  intro isUnsafe
  apply (tagN_bound 0 16 (by decide)).bind_zero
  intro lvls
  apply (tagN_bound 0 16 (by decide)).bind_zero
  intro cidx
  apply (tagN_bound 0 16 (by decide)).bind_zero
  intro params
  apply (tagN_bound 0 16 (by decide)).bind_zero
  intro fields
  exact expr_bound.bind fun _ => charged_pure_bound _ _ _ _ _ (by decide)

theorem inductiveDecl_bound : Bound inductiveDecl 16 0 (fun _ => 2) := by
  unfold inductiveDecl
  apply bool_bound.bind_zero
  intro isUnsafe
  apply (tagN_bound 0 16 (by decide)).bind_zero
  intro lvls
  apply (tagN_bound 0 16 (by decide)).bind_zero
  intro params
  apply (tagN_bound 0 16 (by decide)).bind_zero
  intro indices
  apply expr_bound.bind_zero
  intro typ
  apply (tagN_bound 0 16 (by decide)).bind
  intro count
  apply (check_bound _ _ _ _).bind
  intro checked
  exact ((array_bound ctor_bound _).carry 14).bind fun _ =>
    charged_pure_bound _ _ _ _ _ (by decide)

theorem inductiveProj_bound : Bound inductiveProj 16 0 (fun _ => 2) := by
  unfold inductiveProj
  apply (tagN_bound 0 16 (by decide)).bind
  intro idx
  exact (address_bound.carry 14).bind fun _ => charged_pure_bound _ _ _ _ _ (by decide)

theorem constructorProj_bound : Bound constructorProj 16 0 (fun _ => 2) := by
  unfold constructorProj
  apply (tagN_bound 0 16 (by decide)).bind_zero
  intro idx
  apply (tagN_bound 0 16 (by decide)).bind
  intro cidx
  exact (address_bound.carry 14).bind fun _ => charged_pure_bound _ _ _ _ _ (by decide)

theorem recursorProj_bound : Bound recursorProj 16 0 (fun _ => 2) := by
  unfold recursorProj
  apply (tagN_bound 0 16 (by decide)).bind
  intro idx
  exact (address_bound.carry 14).bind fun _ => charged_pure_bound _ _ _ _ _ (by decide)

theorem definitionProj_bound : Bound definitionProj 16 0 (fun _ => 2) := by
  unfold definitionProj
  apply (tagN_bound 0 16 (by decide)).bind
  intro idx
  exact (address_bound.carry 14).bind fun _ => charged_pure_bound _ _ _ _ _ (by decide)

theorem wrap_bound {reader : M α} (bound : Bound reader 16 0 (fun _ => 2)) (make : α → β) :
    Bound (wrap make reader) 16 1 (fun _ => 2) :=
  (bound.carry 1).bind fun _ => charged_pure_bound _ _ _ _ _ (by decide)

theorem mutConst_bound : Bound mutConst 16 0 (fun _ => 2) := by
  unfold mutConst
  apply (u8_bound 16 (by decide)).bind
  intro tag
  split
  · exact (wrap_bound defn_bound _).weaken (by decide) (fun _ => Nat.le_refl _)
  · exact (wrap_bound inductiveDecl_bound _).weaken (by decide) (fun _ => Nat.le_refl _)
  · exact (wrap_bound recursor_bound _).weaken (by decide) (fun _ => Nat.le_refl _)
  · exact fail_bound _ _ _ _

theorem constantInfo_bound : Bound constantInfo 16 0 (fun _ => 2) := by
  unfold constantInfo
  apply (tagN_bound 4 16 (by decide)).bind
  intro tag
  split
  · exact ((array_bound mutConst_bound _).carry 14).bind fun _ =>
      charged_pure_bound _ _ _ _ _ (by decide)
  · split
    · split
      · exact (wrap_bound defn_bound _).weaken (by decide) (fun _ => Nat.le_refl _)
      · exact (wrap_bound recursor_bound _).weaken (by decide) (fun _ => Nat.le_refl _)
      · exact (wrap_bound axiomDecl_bound _).weaken (by decide) (fun _ => Nat.le_refl _)
      · exact (wrap_bound quotient_bound _).weaken (by decide) (fun _ => Nat.le_refl _)
      · exact (wrap_bound constructorProj_bound _).weaken (by decide) (fun _ => Nat.le_refl _)
      · exact (wrap_bound recursorProj_bound _).weaken (by decide) (fun _ => Nat.le_refl _)
      · exact (wrap_bound inductiveProj_bound _).weaken (by decide) (fun _ => Nat.le_refl _)
      · exact (wrap_bound definitionProj_bound _).weaken (by decide) (fun _ => Nat.le_refl _)
      · exact fail_bound _ _ _ _
    · exact fail_bound _ _ _ _

theorem prefix_bound : Bound recordPrefix 16 0 (fun _ => 4) := by
  unfold recordPrefix
  apply constantInfo_bound.bind_zero
  intro info
  apply (tagN_bound 0 16 (by decide)).bind_zero
  intro sharingCount
  apply (array_bound (expr_bound.weaken (Nat.le_refl _) (fun _ => by decide)) _).bind_zero
  intro sharing
  apply (tagN_bound 0 16 (by decide)).bind_zero
  intro refsCount
  apply (array_bound address_bound _).bind_zero
  intro refs
  exact (tagN_bound 0 16 (by decide)).bind fun _ => charged_pure_bound _ _ _ _ _ (by decide)

/-- Complete record work, including arbitrary failures in descendants and
tables. The additive constructor allowance is shared by the whole universe
table and is never multiplied by its untrusted declared count. -/
theorem constant_bound (budget : Nat) : Bound (constant budget) 16 (2 * budget) (fun _ => 0) := by
  unfold constant
  apply (prefix_bound.carry (2 * budget)).bind
  rintro ⟨info, sharing, refs, count⟩
  apply Bound.bind (intermediate := fun value => 2 * value.2 + 4)
  · exact ((univArray_bound count budget).frame 4).weaken (by omega) (fun _ => Nat.le_refl _)
  · rintro ⟨univs, remaining⟩
    exact charged_pure_bound _ _ _ _ _ (by omega)

end Ixon.Verify.Work
