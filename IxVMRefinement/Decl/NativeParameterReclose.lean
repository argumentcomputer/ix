import IxVMRefinement.Decl.NativeNormalizationFrame
import IxC.Kernel.Verify.Inductives.StructBody
import IxC.Kernel.Verify.Inductives.StructWF

/-! # Reclosing the original constructor parameters around a normalized field telescope -/

namespace IxVM.Refinement.Decl

open Ix.Kernel

private theorem zip_fvars_metadata {md : Mode} :
    ∀ (fvars : List (Expr md)) (binders : List (Expr md × BinderMeta)),
      List.zipWith (fun (x : Expr md) (b : Expr md × BinderMeta) => (x.fvarTypeD, b.2)) fvars binders =
        List.zipWith (fun (x : Expr md) (binderMeta : BinderMeta) => (x.fvarTypeD, binderMeta)) fvars (binders.map Prod.snd)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | x :: fvars, b :: binders =>
    congrArg (List.cons (x.fvarTypeD, b.2)) (zip_fvars_metadata fvars binders)

private theorem stripPis_metadata_inst {md : Mode} {v : Expr md} :
    ∀ {count : Nat} {e : Expr md} {binders : List (Expr md × BinderMeta)} {residual : Expr md}
      (cut : Nat), e.stripPis count = some (binders, residual) →
      ∃ bs body, (e.instantiate1 v cut).stripPis count = some (bs, body) ∧
        bs.map Prod.snd = binders.map Prod.snd
  | 0, e, binders, residual, cut, stripped => by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj stripped)
    exact ⟨[], e.instantiate1 v cut, rfl, rfl⟩
  | count + 1, e, binders, residual, cut, stripped => by
    cases e with
    | forallE dom body bm =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at stripped
      obtain ⟨⟨tail, rest⟩, tailStrip, same⟩ := stripped
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      obtain ⟨bs, out, nextStrip, metadata⟩ := stripPis_metadata_inst (v := v) (cut + 1) tailStrip
      refine ⟨(dom.instantiate1 v cut, bm) :: bs, out, ?_, ?_⟩
      · simp only [Expr.instantiate1, Expr.stripPis, nextStrip, Option.map_some]
      · simp only [List.map_cons, metadata]
    | _ => cases stripped

theorem closeTelescope_append {md : Mode} (left right : List (Expr md × BinderMeta))
    (depth : Nat) (body : Expr md) :
    closeTelescope (left ++ right) depth body =
      closeTelescope left depth (closeTelescope right (depth + left.length) body) := by
  induction left generalizing depth with
  | nil => simp only [List.nil_append, closeTelescope, List.length_nil, Nat.add_zero]
  | cons binder left ih =>
    obtain ⟨dom, bm⟩ := binder
    simp only [List.cons_append, closeTelescope, List.length_cons, ih,
      show depth + 1 + left.length = depth + (left.length + 1) from by omega]

/-- Conversion of a replaced opened body lifts through the actual original parameter opening. -/
theorem reclose_parameter_prefix {md : Mode} {env : Env md} :
    ∀ {count depth : Nat} {e residual closed : Expr md} {fvars : List (Expr md)}
      {binders : List (Expr md × BinderMeta)} {replacement : Expr md},
      e.stripPis count = some (binders, closed) →
      openPisAtFvars count e depth = some (fvars, residual) →
      Expr.WScoped depth e → e.looseBVarsBounded 0 = true →
      Expr.WScoped (depth + count) replacement → replacement.looseBVarsBounded 0 = true →
      (∀ leaf ∈ replacement.fvarLeaves, leaf ∈ residual.fvarLeaves) →
      Rules.DefEq env (depth + count) replacement residual →
      let rebuilt := closeTelescope
        (List.zipWith (fun (x : Expr md) (b : Expr md × BinderMeta) => (x.fvarTypeD, b.2)) fvars binders)
        depth replacement
      Expr.WScoped depth rebuilt ∧ rebuilt.looseBVarsBounded 0 = true ∧
        (∀ leaf ∈ rebuilt.fvarLeaves, leaf ∈ e.fvarLeaves) ∧ Rules.DefEq env depth rebuilt e
  | 0, depth, e, residual, closed, fvars, binders, replacement,
      stripped, opened, _, _, outScope, outBounded, outLeaves, converted => by
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj stripped)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj opened)
    simpa only [List.zipWith_nil_left, closeTelescope, Nat.add_zero] using
      And.intro outScope (And.intro outBounded (And.intro outLeaves converted))
  | count + 1, depth, e, residual, closed, fvars, binders, replacement,
      stripped, opened, scope, bounded, outScope, outBounded, outLeaves, converted => by
    cases e with
    | forallE dom body bm =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at stripped
      obtain ⟨⟨tailBinders, closedBody⟩, tailStrip, same⟩ := stripped
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      simp only [openPisAtFvars] at opened
      cases tailOpen : openPisAtFvars count (body.instantiate1 (.fvar depth dom)) (depth + 1) with
      | none => rw [tailOpen] at opened; cases opened
      | some pair =>
        obtain ⟨tailVars, tailResidual⟩ := pair
        rw [tailOpen] at opened
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj opened)
        simp only [Expr.WScoped] at scope
        simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at bounded
        obtain ⟨nextBinders, nextBody, nextStrip, metadata⟩ :=
          stripPis_metadata_inst (v := .fvar depth dom) 0 tailStrip
        have zipped :
            List.zipWith (fun (x : Expr md) (b : Expr md × BinderMeta) => (x.fvarTypeD, b.2)) tailVars nextBinders =
              List.zipWith (fun (x : Expr md) (b : Expr md × BinderMeta) => (x.fvarTypeD, b.2)) tailVars tailBinders := by
          rw [zip_fvars_metadata, zip_fvars_metadata, metadata]
        obtain ⟨tailScope, tailBounded, tailLeaves, tailEq⟩ := reclose_parameter_prefix nextStrip tailOpen
          (scope.1.instantiate1 0 scope.2) (looseBVarsBounded_instantiate1 _ 0 bounded.2)
          (by simpa only [Nat.add_succ, Nat.succ_add] using outScope) outBounded outLeaves
          (by simpa only [Nat.add_succ, Nat.succ_add] using converted)
        rw [zipped] at tailScope tailBounded tailLeaves tailEq
        have leafCondition : Expr.LeafCond depth dom (body.instantiate1 (.fvar depth dom)) := by
          intro leaf present sameIndex
          rcases Expr.fvarLeaves_instantiate1 body 0 present with inBody | inVar
          · have lt := Expr.fvarLeaves_lt_of_wscoped scope.2 leaf inBody
            omega
          · simp only [Expr.fvarLeaves, List.mem_cons] at inVar
            rcases inVar with rfl | inDom
            · rfl
            · have lt := Expr.fvarLeaves_lt_of_wscoped scope.1 leaf inDom
              omega
        have consistent := Expr.fvarConsistent_of_leafCond _
          (fun leaf present => leafCondition leaf (tailLeaves leaf present))
        have roundTrip := abstract1_instantiate1 _ 0 consistent tailBounded
        dsimp only
        simp only [List.zipWith_cons_cons, closeTelescope,
          show (Expr.fvar depth dom).fvarTypeD = dom from rfl]
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp only [Expr.WScoped]
          exact ⟨scope.1, WScoped.abstract1 0 tailScope⟩
        · simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
          exact ⟨bounded.1, looseBVarsBounded_abstract1 _ 0 tailBounded⟩
        · intro leaf present
          simp only [Expr.fvarLeaves, List.mem_append] at present ⊢
          rcases present with inDom | inBody
          · exact Or.inl inDom
          · obtain ⟨inOutput, notFresh⟩ := Expr.fvarLeaves_abstract1_ne _ 0 tailScope leaf inBody
            rcases Expr.fvarLeaves_instantiate1 body 0 (tailLeaves leaf inOutput) with inRaw | inVar
            · exact Or.inr inRaw
            · simp only [Expr.fvarLeaves, List.mem_cons] at inVar
              rcases inVar with same | inDom
              · subst leaf
                exact (notFresh rfl).elim
              · exact Or.inl inDom
        · apply Rules.DefEq.forallE .refl _ rfl
          rw [roundTrip]
          exact tailEq
    | _ => cases stripped


open Ix.Kernel.Model Ix.Kernel.Semantics Ix.Kernel.SetModel Ix.Kernel.Term Ix.Kernel.Verify
open Ix.Kernel.Model.Rules (Frame Graded)

universe u

/-- The original parameter prefix lifts the semantics of its actual field normalization.
The statement retains the pre-reannotation telescope and its original binder metadata. -/
theorem normalize_parameter_fields_semantics {V : Type u} [SetTheory V] {md : Mode}
    {env : Env md} (model : EnvModelM V .verified env) {fuel fieldCount : Nat} {T : Key md} :
    ∀ {count depth : Nat} {e openedBody closedBody residual : Expr md}
      {parameterVars : List (Expr md)} {parameters fields : List (Expr md × BinderMeta)},
      e.stripPis count = some (parameters, closedBody) →
      openPisAtFvars count e depth = some (parameterVars, openedBody) →
      normFieldDoms (fueledOps .verified fuel) env T (depth + count) fieldCount openedBody =
        .ok (fields, residual) →
      Frame depth e → ∀ {φ : LevelParam → Nat} {context : List AnnotTerm} {reading : AnnotTerm},
      CtxOk model.base2 φ depth context e →
      denoteMeta model.base2.acval env φ depth e = some reading → Graded V context reading →
      let rebuilt := closeTelescope
        (List.zipWith (fun (x : Expr md) (b : Expr md × BinderMeta) => (x.fvarTypeD, b.2))
          parameterVars parameters ++ fields) depth residual
      Expr.WScoped depth rebuilt ∧ rebuilt.looseBVarsBounded 0 = true ∧
        (∀ leaf ∈ rebuilt.fvarLeaves, leaf ∈ e.fvarLeaves) ∧
        ∃ output, denoteMeta model.base2.acval env φ depth rebuilt = some output ∧
          Graded V context output ∧
          ∀ ρ : Nat → V, Sat V context ρ → interp V ρ reading = interp V ρ output
  | count, depth, e, openedBody, closedBody, residual, parameterVars, parameters, fields,
      stripped, opened, fieldRun, frame, φ, context, reading, aligned, read, graded => by
    have openedScope := (openPisAtFvars_WScoped count e depth opened frame.1).2
    have openedBounded := (openPisAtFvars_bounded count opened frame.2.1).1
    obtain ⟨_, fieldScope, fieldBounded, fieldLeaves, fieldEq⟩ :=
      normFieldDoms_reclose model.base2.wf fieldRun openedScope openedBounded
    have syntax := reclose_parameter_prefix stripped opened frame.1 frame.2.1
      fieldScope fieldBounded fieldLeaves fieldEq
    let pbs := List.zipWith (fun (x : Expr md) (b : Expr md × BinderMeta) => (x.fvarTypeD, b.2))
      parameterVars parameters
    have pbsCount : pbs.length = count := by
      simp only [pbs, List.length_zipWith, openPisAtFvars_length _ opened,
        Expr.stripPis_length _ stripped, Nat.min_self]
    have reclosed : closeTelescope (pbs ++ fields) depth residual =
        closeTelescope pbs depth (closeTelescope fields (depth + count) residual) := by
      rw [closeTelescope_append, pbsCount]
    change Expr.WScoped depth (closeTelescope pbs depth (closeTelescope fields (depth + count) residual)) ∧ _ at syntax
    rw [← reclosed] at syntax
    refine ⟨syntax.1, syntax.2.1, syntax.2.2.1, ?_⟩
    cases count with
    | zero =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj stripped)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj opened)
      exact normFieldDoms_semantics model (by simpa only [Nat.add_zero] using fieldRun)
        frame aligned read graded
    | succ count =>
      cases e with
      | forallE dom body bm =>
        simp only [Expr.stripPis, Option.map_eq_some_iff] at stripped
        obtain ⟨⟨tailBinders, tailClosed⟩, tailStrip, same⟩ := stripped
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
        simp only [openPisAtFvars] at opened
        cases tailOpen : openPisAtFvars count (body.instantiate1 (.fvar depth dom)) (depth + 1) with
        | none => rw [tailOpen] at opened; cases opened
        | some pair =>
          obtain ⟨tailVars, tailBody⟩ := pair
          rw [tailOpen] at opened
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj opened)
          obtain ⟨nextBinders, nextBody, nextStrip, metadata⟩ :=
            stripPis_metadata_inst (v := .fvar depth dom) 0 tailStrip
          have zipped :
              List.zipWith (fun (x : Expr md) (b : Expr md × BinderMeta) => (x.fvarTypeD, b.2)) tailVars nextBinders =
                List.zipWith (fun (x : Expr md) (b : Expr md × BinderMeta) => (x.fvarTypeD, b.2)) tailVars tailBinders := by
            rw [zip_fvars_metadata, zip_fvars_metadata, metadata]
          obtain ⟨domainReading, bodyReading, domainRead, bodyRead, rfl⟩ := denoteMeta_forallE_inv read
          obtain ⟨domainGraded, bodyGraded⟩ := Ix.Kernel.Model.Rules.Graded.pi graded
          have openFrame := frame.forallE_open frame.forallE_ty
          have openContext := CtxOk.open aligned.forallE_body aligned.forallE_ty domainRead domainGraded
          obtain ⟨_, tailBounded, tailLeaves, output, outputRead, outputGraded, outputEqual⟩ :=
            normalize_parameter_fields_semantics model nextStrip tailOpen
              (by simpa only [Nat.add_succ, Nat.succ_add] using fieldRun)
              openFrame openContext bodyRead bodyGraded
          rw [zipped] at tailBounded tailLeaves outputRead
          have scopes : Expr.WScoped depth dom ∧ Expr.WScoped depth body := by
            simpa only [Expr.WScoped] using frame.1
          have leafCondition : Expr.LeafCond depth dom (body.instantiate1 (.fvar depth dom)) := by
            intro leaf present sameIndex
            rcases Expr.fvarLeaves_instantiate1 body 0 present with inBody | inVar
            · have lt := Expr.fvarLeaves_lt_of_wscoped scopes.2 leaf inBody
              omega
            · simp only [Expr.fvarLeaves, List.mem_cons] at inVar
              rcases inVar with rfl | inDom
              · rfl
              · have lt := Expr.fvarLeaves_lt_of_wscoped scopes.1 leaf inDom
                omega
          have consistent := Expr.fvarConsistent_of_leafCond _
            (fun leaf present => leafCondition leaf (tailLeaves leaf present))
          have roundTrip := abstract1_instantiate1 _ 0 consistent tailBounded
          refine ⟨.pi 0 (pwBit φ bm.pw) domainReading output, ?_, ?_, ?_⟩
          · simp only [List.zipWith_cons_cons, List.cons_append, closeTelescope, Expr.fvarTypeD]
            rw [denoteMeta_forallE, domainRead, roundTrip, outputRead]
            rfl
          · intro ρ satisfied
            have old := graded ρ satisfied
            simp only [WellDenotedV, WellDenoted_pi, AnnotValid_pi] at old ⊢
            refine ⟨⟨old.1.1, fun x hx => (outputGraded _ (Sat_cons V satisfied hx)).1⟩,
              old.2.1, (fun x hx => (outputGraded _ (Sat_cons V satisfied hx)).2), ?_⟩
            intro zero x member
            rw [← outputEqual (cons x ρ) (Sat_cons V satisfied member)]
            exact old.2.2.2 zero x member
          · intro ρ satisfied
            exact deqStep_piCong rfl (fun x member => outputEqual (cons x ρ) (Sat_cons V satisfied member))
      | _ => cases stripped
termination_by count

end IxVM.Refinement.Decl
