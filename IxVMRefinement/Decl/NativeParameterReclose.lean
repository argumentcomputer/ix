import IxVMRefinement.Decl.NativeRecloseConversion
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
  | _ :: fvars, _ :: binders => by simp only [List.zipWith_cons_cons, List.map_cons, zip_fvars_metadata]

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
        simp only [List.zipWith_cons_cons, Expr.fvarTypeD, closeTelescope]
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact ⟨scope.1, WScoped.abstract1 0 tailScope⟩
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

end IxVM.Refinement.Decl
