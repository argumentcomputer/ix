/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.VExpr

open Ix.Theory (VLevel)

namespace Ix.Theory.Named

structure VConstant where
  uvars : Nat
  type : VExpr

structure VDefEq where
  uvars : Nat
  lhs : VExpr
  rhs : VExpr
  type : VExpr

/-- Syntax of one registered nonrecursive-structure eta rule.

The projector family is fixed by the checked structure artifact.  Its three
naturality fields are syntactic equations, not semantic assumptions; they
are exactly what weakening and substitution need in order to reconstruct the
same registered eta redex. -/
structure VStructEta where
  uvars : Nat
  nparams : Nat
  nfields : Nat
  familyName : Name
  familyType : VExpr
  constructorName : Name
  projectors : List VLevel → List VExpr → List VExpr
  projectors_length : ∀ levels params,
    levels.length = uvars → params.length = nparams →
      (projectors levels params).length = nfields
  projectors_liftN : ∀ levels params n k,
    params.length = nparams →
    (projectors levels params).map (fun projector =>
      projector.liftN n k) =
      projectors levels (params.map fun param => param.liftN n k)
  projectors_instN : ∀ levels params a k,
    params.length = nparams →
    (projectors levels params).map (fun projector =>
      projector.inst a k) =
      projectors levels (params.map fun param => param.inst a k)
  projectors_instL : ∀ levels params ls,
    (projectors levels params).map (fun projector =>
      projector.instL ls) =
      projectors (levels.map (VLevel.inst ls))
        (params.map (VExpr.instL ls))

namespace VStructEta

/-- The instantiated family type governed by a structure-eta descriptor. -/
def structureType (rule : VStructEta) (levels : List VLevel)
    (params : List VExpr) : VExpr :=
  VExpr.appN (.const rule.familyName levels) params

/-- Canonical projected fields of one major premise. -/
def projectionArgs (rule : VStructEta) (levels : List VLevel)
    (params : List VExpr) (major : VExpr) : List VExpr :=
  (rule.projectors levels params).map fun projector => .app projector major

/-- Constructor reconstruction contracted by the primitive eta rule. -/
def rebuild (rule : VStructEta) (levels : List VLevel)
    (params : List VExpr) (major : VExpr) : VExpr :=
  VExpr.appN (.const rule.constructorName levels)
    (params ++ rule.projectionArgs levels params major)

@[simp] theorem structureType_liftN (rule : VStructEta)
    (levels : List VLevel) (params : List VExpr) (n k : Nat) :
    (rule.structureType levels params).liftN n k =
      rule.structureType levels
        (params.map fun param => param.liftN n k) := by
  unfold structureType
  rw [VExpr.liftN_appN]
  rfl

@[simp] theorem structureType_instN (rule : VStructEta)
    (levels : List VLevel) (params : List VExpr) (a : VExpr) (k : Nat) :
    (rule.structureType levels params).inst a k =
      rule.structureType levels
        (params.map fun param => param.inst a k) := by
  unfold structureType
  rw [VExpr.instN_appN]
  rfl

@[simp] theorem structureType_instL (rule : VStructEta)
    (levels : List VLevel) (params : List VExpr) (ls : List VLevel) :
    (rule.structureType levels params).instL ls =
      rule.structureType (levels.map (VLevel.inst ls))
        (params.map (VExpr.instL ls)) := by
  unfold structureType
  rw [VExpr.instL_appN]
  rfl

@[simp] theorem projectionArgs_length (rule : VStructEta)
    (levels : List VLevel) (params : List VExpr) (major : VExpr)
    (hlevels : levels.length = rule.uvars)
    (hparams : params.length = rule.nparams) :
    (rule.projectionArgs levels params major).length = rule.nfields := by
  simp [projectionArgs,
    rule.projectors_length levels params hlevels hparams]

@[simp] theorem projectionArgs_liftN (rule : VStructEta)
    (levels : List VLevel) (params : List VExpr) (major : VExpr)
    (hparams : params.length = rule.nparams) (n k : Nat) :
    (rule.projectionArgs levels params major).map
        (fun arg => arg.liftN n k) =
      rule.projectionArgs levels
        (params.map fun param => param.liftN n k) (major.liftN n k) := by
  simpa [projectionArgs, VExpr.liftN, List.map_map, Function.comp_def] using
    congrArg (List.map fun projector =>
      projector.app (major.liftN n k))
      (rule.projectors_liftN levels params n k hparams)

@[simp] theorem projectionArgs_instN (rule : VStructEta)
    (levels : List VLevel) (params : List VExpr) (major a : VExpr)
    (hparams : params.length = rule.nparams) (k : Nat) :
    (rule.projectionArgs levels params major).map
        (fun arg => arg.inst a k) =
      rule.projectionArgs levels
        (params.map fun param => param.inst a k) (major.inst a k) := by
  simpa [projectionArgs, VExpr.inst, List.map_map, Function.comp_def] using
    congrArg (List.map fun projector => projector.app (major.inst a k))
      (rule.projectors_instN levels params a k hparams)

@[simp] theorem projectionArgs_instL (rule : VStructEta)
    (levels : List VLevel) (params : List VExpr) (major : VExpr)
    (ls : List VLevel) :
    (rule.projectionArgs levels params major).map
        (fun arg => arg.instL ls) =
      rule.projectionArgs (levels.map (VLevel.inst ls))
        (params.map (VExpr.instL ls)) (major.instL ls) := by
  simpa [projectionArgs, VExpr.instL, List.map_map, Function.comp_def] using
    congrArg (List.map fun projector => projector.app (major.instL ls))
      (rule.projectors_instL levels params ls)

@[simp] theorem rebuild_liftN (rule : VStructEta)
    (levels : List VLevel) (params : List VExpr) (major : VExpr)
    (hparams : params.length = rule.nparams) (n k : Nat) :
    (rule.rebuild levels params major).liftN n k =
      rule.rebuild levels (params.map fun param => param.liftN n k)
        (major.liftN n k) := by
  unfold rebuild
  rw [VExpr.liftN_appN, List.map_append,
    rule.projectionArgs_liftN levels params major hparams n k]
  rfl

@[simp] theorem rebuild_instN (rule : VStructEta)
    (levels : List VLevel) (params : List VExpr) (major a : VExpr)
    (hparams : params.length = rule.nparams) (k : Nat) :
    (rule.rebuild levels params major).inst a k =
      rule.rebuild levels (params.map fun param => param.inst a k)
        (major.inst a k) := by
  unfold rebuild
  rw [VExpr.instN_appN, List.map_append,
    rule.projectionArgs_instN levels params major a hparams k]
  rfl

@[simp] theorem rebuild_instL (rule : VStructEta)
    (levels : List VLevel) (params : List VExpr) (major : VExpr)
    (ls : List VLevel) :
    (rule.rebuild levels params major).instL ls =
      rule.rebuild (levels.map (VLevel.inst ls))
        (params.map (VExpr.instL ls)) (major.instL ls) := by
  unfold rebuild
  rw [VExpr.instL_appN, List.map_append,
    rule.projectionArgs_instL levels params major ls]
  rfl

end VStructEta

@[ext] structure VEnv where
  constants : Name → Option VConstant
  defeqs : VDefEq → Prop
  structEtas : VStructEta → Prop

def VEnv.empty : VEnv where
  constants _ := none
  defeqs _ := False
  structEtas _ := False

instance : EmptyCollection VEnv := ⟨.empty⟩

def VEnv.contains (env : VEnv) (name : Name) := ∃ ci, env.constants name = some ci

def VEnv.addConst (env : VEnv) (name : Name) (ci : VConstant) : Option VEnv :=
  match env.constants name with
  | some _ => none
  | none => some { env with constants := fun n => if name = n then some ci else env.constants n }

def VEnv.addDefEq (env : VEnv) (df : VDefEq) : VEnv :=
  { env with defeqs := fun x => x = df ∨ env.defeqs x }

/-- Register one checked structure-eta descriptor. -/
def VEnv.addStructEta (env : VEnv) (rule : VStructEta) : VEnv :=
  { env with structEtas := fun x => x = rule ∨ env.structEtas x }

structure VEnv.LE (env1 env2 : VEnv) : Prop where
  constants : env1.constants n = some a → env2.constants n = some a
  defeqs : env1.defeqs df → env2.defeqs df
  structEtas : env1.structEtas rule → env2.structEtas rule

instance : LE VEnv := ⟨VEnv.LE⟩

theorem VEnv.LE.rfl {env : VEnv} : env ≤ env := ⟨id, id, id⟩

theorem VEnv.LE.trans {a b c : VEnv} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  ⟨h2.1 ∘ h1.1, h2.2 ∘ h1.2, h2.3 ∘ h1.3⟩
