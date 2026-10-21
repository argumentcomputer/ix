module

public import IxC.Kernel.Verify.Frontend.InModelMemo
public import IxC.Kernel.Verify.Rename.ExprOps
public import IxC.Kernel.Verify.Rename.Ind3

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

/-- `sortCeil`'s last branch: a ceiling for the type of the head. -/
def ceilByHead (tbl : ConstTable md) (fuel : Nat) (ctx : List (Expr md)) (d : Expr md) :
    Except String (Option Level) := do
  match ← inferTy tbl ctx d.getAppFn with
  | some g => sortCeil tbl fuel ctx g
  | none => pure none

theorem sortCeil_mapKeys {tbl : ConstTable md} {tbl' : ConstTable md'} (htbl : TblAgree f tbl tbl')
    (fuel : Nat) : ∀ (ctx : List (Expr md)) (d : Expr md),
      sortCeil tbl' fuel (ctx.map (Expr.mapKeys f)) (d.mapKeys f) = sortCeil tbl fuel ctx d := by
  induction fuel with
  | zero => intro ctx d; rfl
  | succ fuel ih =>
    intro ctx d
    have byHead : ∀ d' : Expr md, ceilByHead tbl' fuel (ctx.map (Expr.mapKeys f)) (d'.mapKeys f) =
        ceilByHead tbl fuel ctx d' := fun d' => by
      simp only [ceilByHead, ← Expr.mapKeys_getAppFn, inferTy_mapKeys f htbl]
      cases inferTy tbl ctx d'.getAppFn with
      | error err => rfl
      | ok r => cases r <;> simp [Except.map, bind, Except.bind, ih]
    simp only [sortCeil, inferTy_mapKeys f htbl]
    cases inferTy tbl ctx d with
    | error err => rfl
    | ok r =>
      cases r with
      | some t =>
        simp only [Except.map, Option.map_some, bind, Except.bind, betaHeadE_mapKeys]
        cases betaHeadE t with
        | error err => rfl
        | ok t' =>
          have h := ih ctx t'
          cases t' <;> first | rfl | exact h
      | none =>
        simp only [Except.map, Option.map_none, bind, Except.bind, betaHeadE_mapKeys]
        cases betaHeadE d with
        | error err => rfl
        | ok d' =>
          have hd := byHead d'
          cases d' with
          | forallE dom body m =>
            have hb := ih (dom :: ctx) body
            simp only [List.map_cons] at hb
            simp only [Expr.mapKeys, ih ctx dom, hb]
          | letE t v b l =>
            simp only [Expr.mapKeys, ← Expr.mapKeys_instantiate1, ih]
          | _ => exact hd

theorem idxSort_mapKeys {tbl : ConstTable md} {tbl' : ConstTable md'} (htbl : TblAgree f tbl tbl')
    (ctx : List (Expr md)) (e : Expr md) :
    idxSort tbl' (ctx.map (Expr.mapKeys f)) (e.mapKeys f) = idxSort tbl ctx e :=
  sortCeil_mapKeys f htbl 128 ctx e

/-! ## Derived names and small builders -/

section Names
variable {f : md.Id → md'.Id}

@[simp] theorem implKey_map (T : Key md) : (implKey T).map f = implKey (T.map f) := rfl
@[simp] theorem tagName_map (T : Key md) : (tagName T).map f = tagName (T.map f) := rfl
@[simp] theorem tagCtorName_map (T : Key md) (k : Nat) :
    (tagCtorName T k).map f = tagCtorName (T.map f) k := rfl
@[simp] theorem auxName_map (T : Key md) : (auxName T).map f = auxName (T.map f) := rfl
@[simp] theorem auxCtorName_map (T : Key md) (k j : Nat) :
    (auxCtorName T k j).map f = auxCtorName (T.map f) k j := rfl
@[simp] theorem modelName_map (n : Key md) : (modelName n).map f = modelName (n.map f) := rfl
@[simp] theorem projModelName_map (T : Key md) (i : Nat) :
    (projModelName T i).map f = projModelName (T.map f) i := rfl
@[simp] theorem auxKey_map (k : Key md) (d : Derived) : (auxKey k d).map f = auxKey (k.map f) d := rfl

@[simp] theorem constP_mapKeys (n : Key md) (lps : List LevelParam) :
    (constP n lps).mapKeys f = constP (n.map f) lps := rfl

@[simp] theorem varsAt_mapKeys (o n : Nat) :
    (varsAt o n : List (Expr md)).map (Expr.mapKeys f) = varsAt o n := by
  simp [varsAt, structPsAt, Expr.mapKeys]

@[simp] theorem structProjPs_mapKeys (nP : Nat) :
    (structProjPs nP : List (Expr md)).map (Expr.mapKeys f) = structProjPs nP := by
  simp [structProjPs, Expr.mapKeys]

@[simp] theorem mkPis_mapKeys (bs : List (Expr md)) (body : Expr md) :
    (mkPis bs body).mapKeys f = mkPis (bs.map (Expr.mapKeys f)) (body.mapKeys f) := by
  induction bs <;> simp_all [mkPis, Expr.mapKeys]

@[simp] theorem mkLams_mapKeys (bs : List (Expr md)) (body : Expr md) :
    (mkLams bs body).mapKeys f = mkLams (bs.map (Expr.mapKeys f)) (body.mapKeys f) := by
  induction bs <;> simp_all [mkLams, Expr.mapKeys]

@[simp] theorem piBinders_mapBinders (bs : List (Expr md × BinderMeta)) :
    piBinders (bs.map fun p => (p.1.mapKeys f, p.2)) = (piBinders bs).map (Expr.mapKeys f) := by
  simp [piBinders]

end Names

/-! ## The recursor builders (the checker's own, renamed in `Rename/Ind3.lean`) -/

theorem recTy_map {f : md.Id → md'.Id} (T : Key md) (lps : List LevelParam) (elim : LevelParam)
    (large : Bool) (nP nIdx : Nat) (tty : Expr md) (ctors : List (Key md × Nat × Expr md × List Nat)) :
    recTy (T.map f) lps elim large nP nIdx (tty.mapKeys f) (ctors4Map f ctors) =
      (recTy T lps elim large nP nIdx tty ctors).map (Expr.mapKeys f) :=
  structRecTyR_map T lps elim large nP nIdx tty ctors

theorem recRhs_map {f : md.Id → md'.Id} (T : Key md) (lps : List LevelParam) (elim : LevelParam)
    (large : Bool) (nP nIdx : Nat) (tty : Expr md) (ctors : List (Key md × Nat × Expr md × List Nat))
    (recC : Key md) (rlvls : List Level) (j : Nat) :
    recRhs (T.map f) lps elim large nP nIdx (tty.mapKeys f) (ctors4Map f ctors) (recC.map f) rlvls j =
      (recRhs T lps elim large nP nIdx tty ctors recC rlvls j).map (Expr.mapKeys f) := by
  simp only [recRhs, structRecRhsR_map, Option.map_map]
  cases structRecRhsR T lps elim large nP nIdx tty ctors recC rlvls j <;>
    simp [Expr.mapKeys_resetMeta]

end Ix.Kernel.Frontend.InModel
