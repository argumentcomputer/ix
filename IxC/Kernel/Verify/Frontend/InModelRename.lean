module

public import IxC.Kernel.Verify.Frontend.InModelMemo
public import IxC.Kernel.Verify.Rename.ExprOps

public section

/-!
# The in-model generator commutes with renaming keys (parametricity, step 3)

`Key.map f` renames a term's keys (`Expr.mapKeys f`). The generator's syntactic
inferer reads the constant table at the keys it meets and compares no key, so
it commutes with a renaming under which the table agrees (`inferTyF_mapKeys`).
-/

namespace Ix.Kernel.Frontend.InModel

open Ix.Kernel

variable {md md' : Mode} (f : md.Id → md'.Id)

/-! ## Head β-reduction -/

theorem betaHeadF_mapKeys (fuel : Nat) : ∀ (e : Expr md),
    betaHeadF fuel (e.mapKeys f) = (betaHeadF fuel e).map (Expr.mapKeys f) := by
  induction fuel with
  | zero => intro e; rfl
  | succ fuel ih =>
    intro e
    cases e with
    | app g a =>
      simp only [Expr.mapKeys, betaHeadF, ih g]
      cases hg : betaHeadF fuel g with
      | none => rfl
      | some g' =>
        cases g' with
        | lam d b m =>
          simp only [Option.map_some, Expr.mapKeys, ← Expr.mapKeys_instantiate1, ih]
        | _ => rfl
    | _ => rfl

theorem betaHeadE_mapKeys (e : Expr md) :
    betaHeadE (e.mapKeys f) = (betaHeadE e).map (Expr.mapKeys f) := by
  simp only [betaHeadE, betaHeadF_mapKeys]
  cases betaHeadF inferFuel e <;> rfl

theorem betaHead_mapKeys (e : Expr md) : betaHead (e.mapKeys f) = (betaHead e).mapKeys f := by
  simp only [betaHead, betaHeadF_mapKeys]
  cases betaHeadF inferFuel e <;> rfl

/-! ## The syntactic inferer -/

/-- **The constant table agrees** under the renaming: at a renamed key, the
renamed declared type. -/
def TblAgree (tbl : ConstTable md) (tbl' : ConstTable md') : Prop :=
  ∀ k, tbl' (k.map f) = (tbl k).map fun p => (p.1, p.2.mapKeys f)

theorem inferTyF_sortOfF_mapKeys {tbl : ConstTable md} {tbl' : ConstTable md'}
    (htbl : TblAgree f tbl tbl') (fuel : Nat) :
    (∀ (ctx : List (Expr md)) (e : Expr md),
      inferTyF tbl' fuel (ctx.map (Expr.mapKeys f)) (e.mapKeys f) =
        (inferTyF tbl fuel ctx e).map (Option.map (Expr.mapKeys f))) ∧
    (∀ (ctx : List (Expr md)) (e : Expr md),
      sortOfF tbl' fuel (ctx.map (Expr.mapKeys f)) (e.mapKeys f) = sortOfF tbl fuel ctx e) := by
  induction fuel with
  | zero => exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | succ fuel ih =>
    obtain ⟨ihI, ihS⟩ := ih
    refine ⟨fun ctx e => ?_, fun ctx e => ?_⟩
    · cases e with
      | bvar i =>
        simp only [Expr.mapKeys, inferTyF, List.getElem?_map]
        cases ctx[i]? <;> simp [Except.map, Expr.mapKeys_liftLooseBVars]
      | sort u => rfl
      | const n us =>
        simp only [Expr.mapKeys, inferTyF, htbl n]
        cases tbl n with
        | none => rfl
        | some p =>
          obtain ⟨lps, ty⟩ := p
          simp only [Option.map_some, Option.bind_some]
          split <;> simp [Except.map, Expr.mapKeys_instantiateLevelParams]
      | app g a =>
        simp only [Expr.mapKeys, inferTyF, ihI ctx g]
        cases hg : inferTyF tbl fuel ctx g with
        | error err => rfl
        | ok r =>
          cases r with
          | none => rfl
          | some ft =>
            simp only [Except.map, Option.map_some, bind, Except.bind, betaHeadF_mapKeys]
            cases betaHeadF fuel ft with
            | none => rfl
            | some t =>
              cases t <;> simp [Expr.mapKeys, pure, Except.pure, Expr.mapKeys_instantiate1]
      | lam d b m =>
        have := ihI (d :: ctx) b
        simp only [List.map_cons] at this
        simp only [Expr.mapKeys, inferTyF, this]
        cases inferTyF tbl fuel (d :: ctx) b with
        | error err => rfl
        | ok r => cases r <;> rfl
      | forallE d b m =>
        have hb := ihS (d :: ctx) b
        simp only [List.map_cons] at hb
        simp only [Expr.mapKeys, inferTyF, ihS ctx d, hb]
        cases sortOfF tbl fuel ctx d with
        | error err => rfl
        | ok r =>
          cases r with
          | none => rfl
          | some u =>
            simp only [bind, Except.bind]
            cases sortOfF tbl fuel (d :: ctx) b with
            | error err => rfl
            | ok r => cases r <;> rfl
      | letE t v b l =>
        simp only [Expr.mapKeys, inferTyF, ← Expr.mapKeys_instantiate1, ihI]
      | lit l => cases l <;> rfl
      | fvar i t => rfl
      | proj s i x => rfl
    · simp only [sortOfF, ihI ctx e]
      cases inferTyF tbl fuel ctx e with
      | error err => rfl
      | ok r =>
        cases r with
        | none => rfl
        | some t =>
          simp only [Except.map, Option.map_some, bind, Except.bind, betaHeadF_mapKeys]
          cases betaHeadF fuel t with
          | none => rfl
          | some t' => cases t' <;> rfl

theorem inferTy_mapKeys {tbl : ConstTable md} {tbl' : ConstTable md'} (htbl : TblAgree f tbl tbl')
    (ctx : List (Expr md)) (e : Expr md) :
    inferTy tbl' (ctx.map (Expr.mapKeys f)) (e.mapKeys f) =
      (inferTy tbl ctx e).map (Option.map (Expr.mapKeys f)) :=
  (inferTyF_sortOfF_mapKeys f htbl inferFuel).1 ctx e

theorem sortOf_mapKeys {tbl : ConstTable md} {tbl' : ConstTable md'} (htbl : TblAgree f tbl tbl')
    (ctx : List (Expr md)) (e : Expr md) :
    sortOf tbl' (ctx.map (Expr.mapKeys f)) (e.mapKeys f) = sortOf tbl ctx e :=
  (inferTyF_sortOfF_mapKeys f htbl inferFuel).2 ctx e

end Ix.Kernel.Frontend.InModel
