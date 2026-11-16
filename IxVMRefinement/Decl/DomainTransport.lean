import IxVMRefinement.Decl.NativeConstructorFieldChecks
import IxVMRefinement.Decl.NativeConstructorFieldFrames
import IxVMRefinement.Decl.IdentityRefShape

/-! # Transport of a produced domain property through an exact rebuild

This syntactic adapter is useful for properties stable under arbitrary binder substitution.
It is not required by the general checked-sort law: dependent properties may instead use
an actual typed relation between the original and final frames to produce their transport.
-/

namespace IxVM.Refinement.Decl

open Ix.Kernel Ix.Kernel.Model

private inductive DomainAt {md : Mode} (P : Expr md → Prop) : Nat → Expr md → Prop
  | here {domain body : Expr md} {bm : BinderMeta} : P domain → DomainAt P 0 (.forallE domain body bm)
  | next {slot : Nat} {domain body : Expr md} {bm : BinderMeta} :
      DomainAt P slot body → DomainAt P (slot + 1) (.forallE domain body bm)

private theorem DomainAt.abstract1 {md : Mode} {P : Expr md → Prop}
    (preserves : ∀ e index cut, P e → P (e.abstract1 index cut))
    {slot : Nat} {e : Expr md} (shape : DomainAt P slot e) (index : Nat) :
    ∀ cut, DomainAt P slot (e.abstract1 index cut) := by
  induction shape with
  | here domainShape => intro cut; exact .here (preserves _ _ _ domainShape)
  | next _ ih => intro cut; exact .next (ih (cut + 1))

private theorem DomainAt.instantiate1 {md : Mode} {P : Expr md → Prop}
    (preserves : ∀ e value cut, P e → P (e.instantiate1 value cut))
    {slot : Nat} {e : Expr md} (shape : DomainAt P slot e) (value : Expr md) :
    ∀ cut, DomainAt P slot (e.instantiate1 value cut) := by
  induction shape with
  | here domainShape => intro cut; exact .here (preserves _ _ _ domainShape)
  | next _ ih => intro cut; exact .next (ih (cut + 1))

private theorem DomainAt.annotated {P : Expr .anon → Prop}
    (preserves : ∀ {e out}, P e → IxVM.Consistency.Annotates out e → P out)
    {slot : Nat} {e out : Expr .anon} (shape : DomainAt P slot e)
    (annotation : IxVM.Consistency.Annotates out e) : DomainAt P slot out := by
  induction shape generalizing out with
  | here domainShape =>
    cases annotation with
    | forallE domain _ => exact .here (preserves domainShape domain)
  | next _ ih =>
    cases annotation with
    | forallE _ body => exact .next (ih body)

private theorem DomainAt.closeTelescope {md : Mode} {P : Expr md → Prop}
    (preserves : ∀ e index cut, P e → P (e.abstract1 index cut)) :
    ∀ (binders : List (Expr md × BinderMeta)) {slot : Nat} {binder : Expr md × BinderMeta},
      binders[slot]? = some binder → P binder.1 → ∀ depth body,
      DomainAt P slot (closeTelescope binders depth body) := by
  intro binders
  induction binders with
  | nil => intro slot binder absent; cases slot <;> cases absent
  | cons current binders ih =>
    intro slot binder atSlot domainShape depth body
    cases slot with
    | zero =>
      obtain rfl := Option.some.inj atSlot
      exact .here domainShape
    | succ slot =>
      exact .next ((ih atSlot domainShape (depth + 1) body).abstract1 preserves depth 0)

private theorem DomainAt.opened {md : Mode} {P : Expr md → Prop}
    (preserves : ∀ e value cut, P e → P (e.instantiate1 value cut)) :
    ∀ {count depth slot : Nat} {e residual : Expr md} {openedVars : List (Expr md)} {domainVar : Expr md},
      openPisAtFvars count e depth = some (openedVars, residual) →
      DomainAt P slot e → openedVars[slot]? = some domainVar → P domainVar.fvarTypeD := by
  intro count
  induction count with
  | zero =>
    intro depth slot e residual openedVars domainVar opened _ atSlot
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj opened)
    cases slot <;> cases atSlot
  | succ count ih =>
    intro depth slot e residual openedVars domainVar opened shape atSlot
    cases e with
    | forallE domain body bm =>
      simp only [openPisAtFvars] at opened
      cases tail : openPisAtFvars count (body.instantiate1 (.fvar depth domain)) (depth + 1) with
      | none => rw [tail] at opened; cases opened
      | some pair =>
        obtain ⟨tailVars, tailResidual⟩ := pair
        rw [tail] at opened
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj opened)
        cases shape with
        | here domainShape =>
          obtain rfl := Option.some.inj atSlot
          exact domainShape
        | next bodyShape =>
          exact ih tail (bodyShape.instantiate1 preserves (.fvar depth domain) 0) atSlot
    | _ => cases shape

private theorem normFieldDoms_count {md : Mode} {env : Env md} {fuel : Nat} {T : Key md} :
    ∀ {count depth : Nat} {e residual : Expr md} {fields : List (Expr md × BinderMeta)},
      normFieldDoms (fueledOps .verified fuel) env T depth count e = .ok (fields, residual) →
      fields.length = count := by
  intro count
  induction count with
  | zero =>
    intro depth e residual fields run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
    rfl
  | succ count ih =>
    intro depth e residual fields run
    cases e with
    | forallE domain body bm =>
      simp only [normFieldDoms] at run
      obtain ⟨_, _, run⟩ := exceptBind_ok run
      obtain ⟨⟨tailFields, tailResidual⟩, recursive, result⟩ := exceptBind_ok run
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj result)
      simpa only [List.length_cons] using congrArg Nat.succ (ih recursive)
    | _ => cases run

/-- Syntactic closure supplies domain transport through the actual computed rebuild. -/
theorem normCtorVal_domain_predicate {env : Env .anon} {fuel nP nF slot : Nat} {T : Key .anon}
    {P : Expr .anon → Prop}
    (abstracts : ∀ e index cut, P e → P (e.abstract1 index cut))
    (instantiates : ∀ e value cut, P e → P (e.instantiate1 value cut))
    (annotates : ∀ {e out}, P e → IxVM.Consistency.Annotates out e → P out)
    (normalizes : ∀ {depth steps e out}, P e →
      normPosDom (fueledOps .verified fuel) env T depth steps e = .ok out → P out)
    {raw initial checked : ConstantVal .anon} {originalVars finalVars : List (Expr .anon)}
    {originalResidual finalResidual original final : Expr .anon}
    (normalized : normCtorVal (fueledOps .verified fuel) env T nP nF raw initial = .ok checked)
    (originalOpen : openPisAtFvars (nP + nF) initial.type 0 = some (originalVars, originalResidual))
    (finalOpen : openPisAtFvars (nP + nF) checked.type 0 = some (finalVars, finalResidual))
    (originalAt : originalVars[nP + slot]? = some original)
    (finalAt : finalVars[nP + slot]? = some final)
    (shape : P original.fvarTypeD) : P final.fvarTypeD := by
  obtain ⟨rebuilt, rebuild, lastBranch⟩ := normCtorVal_rebuild_trace normalized
  rcases lastBranch with same | checkedAgain
  · rw [same] at finalOpen
    obtain ⟨sameVars, _⟩ := Prod.mk.inj (Option.some.inj (originalOpen.symm.trans finalOpen))
    rw [← sameVars] at finalAt
    obtain rfl := Option.some.inj (originalAt.symm.trans finalAt)
    exact shape
  · obtain ⟨parameters, closedResidual, parameterVars, openedResidual, fields, residual,
      stripped, parametersOpen, fieldRun, rebuiltEq⟩ := rebuild
    obtain ⟨fieldVars, fieldsOpen, fieldCount, calls⟩ := normFieldDoms_calls fieldRun
    have wholeOpen : openPisAtFvars (nP + nF) initial.type 0 = some (parameterVars ++ fieldVars, residual) :=
      openPisAtFvars_add nP parametersOpen (by rw [Nat.zero_add]; exact fieldsOpen)
    obtain ⟨sameVars, _⟩ := Prod.mk.inj (Option.some.inj (originalOpen.symm.trans wholeOpen))
    have parameterCount := Ix.Kernel.Verify.openPisAtFvars_length _ parametersOpen
    have originalFieldAt : fieldVars[slot]? = some original := by
      rw [sameVars, List.getElem?_append_right (by omega), parameterCount,
        Nat.add_sub_cancel_left] at originalAt
      exact originalAt
    have inside : slot < fields.length := by
      have fieldInside := (List.getElem?_eq_some_iff.mp originalFieldAt).1
      rw [normFieldDoms_count fieldRun]
      omega
    have outputAt : fields[slot]? = some fields[slot] := List.getElem?_eq_getElem inside
    have outputShape := normalizes shape (calls slot original fields[slot] originalFieldAt outputAt)
    let parameterBinders := List.zipWith
      (fun (x : Expr .anon) (b : Expr .anon × BinderMeta) => (x.fvarTypeD, b.2)) parameterVars parameters
    have parameterBinderCount : parameterBinders.length = nP := by
      simp only [parameterBinders, List.length_zipWith, parameterCount, Expr.stripPis_length _ stripped, Nat.min_self]
    have outputWholeAt : (parameterBinders ++ fields)[nP + slot]? = some fields[slot] := by
      rw [List.getElem?_append_right (by omega), parameterBinderCount, Nat.add_sub_cancel_left]
      exact outputAt
    have closedShape : DomainAt P (nP + slot) rebuilt := by
      rw [rebuiltEq]
      exact DomainAt.closeTelescope abstracts
        (parameterBinders ++ fields) outputWholeAt outputShape 0 residual
    have annotation := (NativeFormerRestore.initiallyStored checkedAgain).2.2
    have annotatedShape := closedShape.annotated annotates annotation
    exact annotatedShape.opened instantiates finalOpen finalAt

private theorem DomainAt.abstract1_map {P Q : Expr .anon → Prop} {slot : Nat} {e : Expr .anon}
    (shape : DomainAt P slot e) (index cut : Nat)
    (mapping : ∀ expression, P expression → Q (expression.abstract1 index (cut + slot))) :
    DomainAt Q slot (e.abstract1 index cut) := by
  induction shape generalizing cut with
  | here origin => exact .here (by simpa only [Nat.add_zero] using mapping _ origin)
  | next _ ih =>
    refine .next (ih (cut + 1) ?_)
    intro expression origin
    simpa only [Nat.add_succ, Nat.succ_add] using mapping expression origin

private theorem DomainAt.instantiate1_map {P Q : Expr .anon → Prop} {slot : Nat} {e : Expr .anon}
    (shape : DomainAt P slot e) (value : Expr .anon) (cut : Nat)
    (mapping : ∀ expression, P expression → Q (expression.instantiate1 value (cut + slot))) :
    DomainAt Q slot (e.instantiate1 value cut) := by
  induction shape generalizing cut with
  | here origin => exact .here (by simpa only [Nat.add_zero] using mapping _ origin)
  | next _ ih =>
    refine .next (ih (cut + 1) ?_)
    intro expression origin
    simpa only [Nat.add_succ, Nat.succ_add] using mapping expression origin

private def closedReference (depth slot target : Nat) (type : Expr .anon) : Expr .anon :=
  if depth ≤ target then .bvar (depth + slot - 1 - target) else .fvar target type

private theorem closedReference_step (depth slot target : Nat) (type : Expr .anon) :
    (closedReference (depth + 1) slot target type).abstract1 depth slot =
      closedReference depth (slot + 1) target type := by
  by_cases nextBound : depth + 1 ≤ target
  · have currentBound : depth ≤ target := by omega
    simp only [closedReference, if_pos nextBound, if_pos currentBound, Expr.abstract1]
    congr 1
    omega
  · by_cases currentBound : depth ≤ target
    · have same : target = depth := by omega
      subst target
      have position : depth + (slot + 1) - 1 - depth = slot := by omega
      simp [closedReference, Expr.abstract1, position]
    · have different : target ≠ depth := by omega
      simp only [closedReference, if_neg nextBound, if_neg currentBound, Expr.abstract1, if_neg different]

private theorem DomainAt.close_reference {domainSort : Level} :
    ∀ (binders : List (Expr .anon × BinderMeta)) {slot : Nat} {entry : Expr .anon × BinderMeta},
      binders[slot]? = some entry → ∀ depth target type body,
      target < depth + slot → IdentityRef domainSort (.fvar target type) entry.1 →
      DomainAt (IdentityRef domainSort (closedReference depth slot target type)) slot
        (closeTelescope binders depth body) := by
  intro binders
  induction binders with
  | nil => intro slot entry absent; cases slot <;> cases absent
  | cons current binders ih =>
    intro slot entry atSlot depth target type body earlier origin
    cases slot with
    | zero =>
      have same : current = entry := Option.some.inj atSlot
      subst entry
      have outside : ¬ depth ≤ target := by omega
      simpa only [closedReference, if_neg outside] using DomainAt.here (body :=
        (closeTelescope binders (depth + 1) body).abstract1 depth 0) (bm := current.2) origin
    | succ slot =>
      have tail := ih atSlot (depth + 1) target type body (by omega) origin
      refine .next (tail.abstract1_map depth 0 ?_)
      intro expression expressionOrigin
      have mapped := expressionOrigin.abstract1 depth slot
      rw [closedReference_step] at mapped
      simpa only [Nat.zero_add] using mapped

private theorem DomainAt.open_reference {domainSort : Level} :
    ∀ {count depth slot target : Nat} {e residual use : Expr .anon} {fvars : List (Expr .anon)},
      openPisAtFvars count e depth = some (fvars, residual) → target < slot →
      DomainAt (IdentityRef domainSort (.bvar (slot - 1 - target))) slot e →
      fvars[slot]? = some use → ∃ reference,
        fvars[target]? = some reference ∧ IdentityRef domainSort reference use.fvarTypeD := by
  intro count
  induction count with
  | zero =>
    intro depth slot target e residual use fvars opened _ _ atUse
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj opened)
    cases slot <;> cases atUse
  | succ count ih =>
    intro depth slot target e residual use fvars opened earlier shape atUse
    cases slot with
    | zero => omega
    | succ slot =>
      cases e with
      | forallE domain body metadata =>
        cases shape with
        | next bodyShape =>
          simp only [openPisAtFvars] at opened
          cases tail : openPisAtFvars count (body.instantiate1 (.fvar depth domain)) (depth + 1) with
          | none => rw [tail] at opened; cases opened
          | some pair =>
            obtain ⟨tailVars, tailResidual⟩ := pair
            rw [tail] at opened
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj opened)
            cases target with
            | zero =>
              have position : slot + 1 - 1 - 0 = slot := by omega
              rw [position] at bodyShape
              have openedShape : DomainAt (IdentityRef domainSort (.fvar depth domain)) slot
                  (body.instantiate1 (.fvar depth domain)) := by
                refine bodyShape.instantiate1_map (.fvar depth domain) 0 ?_
                intro expression origin
                simpa only [Nat.zero_add, Expr.instantiate1, ↓reduceIte] using
                  origin.instantiate1 (.fvar depth domain) slot
              refine ⟨.fvar depth domain, rfl, ?_⟩
              exact openedShape.opened (fun _ value cut origin => by
                simpa only [Expr.instantiate1] using origin.instantiate1 value cut) tail atUse
            | succ target =>
              have position : slot + 1 - 1 - (target + 1) = slot - 1 - target := by omega
              rw [position] at bodyShape
              have unequal : slot - 1 - target ≠ slot := by omega
              have notGreater : ¬ slot - 1 - target > slot := by omega
              have openedShape : DomainAt (IdentityRef domainSort (.bvar (slot - 1 - target))) slot
                  (body.instantiate1 (.fvar depth domain)) := by
                refine bodyShape.instantiate1_map (.fvar depth domain) 0 ?_
                intro expression origin
                simpa only [Nat.zero_add, Expr.instantiate1, if_neg unequal, if_neg notGreater] using
                  origin.instantiate1 (.fvar depth domain) slot
              obtain ⟨reference, atReference, origin⟩ := ih tail (by omega) openedShape atUse
              exact ⟨reference, atReference, origin⟩
      | _ => cases shape

/-- Closing an earlier reference, annotating the whole telescope and reopening it selects
the matching final opener. Its type annotation is the final frame's actual one. -/
theorem reclosed_identity_domain {domainSort : Level} {binders : List (Expr .anon × BinderMeta)}
    {slot target count : Nat} {entry : Expr .anon × BinderMeta} {type body finalType residual use : Expr .anon}
    {finalVars : List (Expr .anon)} (atSlot : binders[slot]? = some entry) (earlier : target < slot)
    (origin : IdentityRef domainSort (.fvar target type) entry.1)
    (annotation : IxVM.Consistency.Annotates finalType (closeTelescope binders 0 body))
    (opened : openPisAtFvars count finalType 0 = some (finalVars, residual))
    (atUse : finalVars[slot]? = some use) :
    ∃ reference, finalVars[target]? = some reference ∧ IdentityRef domainSort reference use.fvarTypeD := by
  have closed : DomainAt (IdentityRef domainSort (.bvar (slot - 1 - target))) slot
      (closeTelescope binders 0 body) := by
    simpa [closedReference] using DomainAt.close_reference binders atSlot 0 target type body (by omega) origin
  have annotated := closed.annotated (fun h ann => h.annotated_bvar ann) annotation
  exact annotated.open_reference opened earlier atUse

end IxVM.Refinement.Decl
