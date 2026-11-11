import IxCK.Kernel.Denotes
import IxCCGrounding.Syntax

/-!
# The kernel's model, and the laws the development assumes of it (`IxCCGrounding.Laws`)

**The one module of the development that imports the kernel's model** (`IxCK.Kernel.Denotes`,
the statement half: `Denotes`, `Model` and, through its imports, the set theory interface and
`SetModel.Ops`; not the kernel's proof tree). Every other module reaches the model through this
one, so when the certified IxVM work's laws land on `main` as fields of `Model`, this file is
what changes: the four definitions copied from theirs go, and `Laws` keeps its last three fields.

Declarations of the model used by the development: `Denotes` and its rules, `Denotes_functional`,
`Model.cval`, `Model.mem`, `Model.eq_equality`, `push`, `regime`, `field`, `Level.substFn`,
`Level.eval`, `PropWhen.holds`; from the set theory `∈ˢ`, `app`, `pt`, `univ`, `empty`, `eqv`,
`graph`, `mem_eqv`, `univ_zero`, `app_pt`, `not_mem_empty`; from `SetModel.Ops` `piR`, `lamR`
and their lemmas (`lamR_zero`, `app_lamR_pos`, `app_mem_piR`, `app_mem_piR_pos`, `lamR_mem`,
`piR_dom_unique`, `eq_pt_of_mem_piR_zero`, `not_pt_mem_piR_pos`, `eq_pt_of_mem_univZero`,
`piR_zero_mem_univZero`, `eq_of_mem_piR_app_eq`, `app_off_dom_piR_pos`, `lamR_congr`,
`piR_congr`).

## The laws

The public `Model` on this branch has `mem`, `false_empty` and `eq_equality`. The laws the
development needs beyond them are an explicit structure of hypotheses, `Laws`, named as on the
IxVM side where a law exists there:

| Field | Theirs (`jcb/ixvmc-std-model`, 2026-11-11) | Who is to supply it |
| --- | --- | --- |
| `defn_value` | `Model.defn_value`, a field, proved | the IxVM side, when it lands on `main` |
| `iota_rule` | `Model.iota_rule : IotaLaw cval env`, a field, proved | the same |
| `cval_params` | `Model.cval_params`, a field | the same |
| `proj_ctor` | scheduled ("the projection of a constructor"); the value form is ours | the IxVM side, scheduled |
| `nat_accel` | scheduled, over all literals, the fifteen roles | the IxVM side, scheduled |
| `ctor_canon` | none; asked on 2026-11-11 (parameters and levels) | the IxVM side if accepted; otherwise IxCC, by a typed relation |

`DenotesList`, `Fits`, `IotaRule` and `IotaLaw` are copied verbatim from theirs
(`IxC/Kernel/Denotes.lean` at `659ca9130`; the ι law's right-hand side denotes in its
conclusion).
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel

universe w

section Laws

variable {V : Type w} [Ix.Kernel.SetTheory V] {md : Mode}

/-- (theirs, verbatim) -/
inductive DenotesList (cval : Key md → (LevelParam → Nat) → V) (env : Env md)
    (φ : LevelParam → Nat) (ρ : BVarIdx → V) : List (Expr md) → List V → Prop
  | nil : DenotesList cval env φ ρ [] []
  | cons {e : Expr md} {es : List (Expr md)} {v : V} {vs : List V} :
      Denotes cval env φ ρ e v → DenotesList cval env φ ρ es vs →
      DenotesList cval env φ ρ (e :: es) (v :: vs)

/-- (theirs, verbatim) -/
inductive Fits (cval : Key md → (LevelParam → Nat) → V) (env : Env md) (φ : LevelParam → Nat) :
    (BVarIdx → V) → Expr md → List V → (BVarIdx → V) → Expr md → Prop
  | nil {ρ : BVarIdx → V} {T : Expr md} : Fits cval env φ ρ T [] ρ T
  | cons {ρ ρ' : BVarIdx → V} {A B R : Expr md} {m : BinderMeta} {X x : V} {xs : List V} :
      Denotes cval env φ ρ A X → x ∈ˢ X → Fits cval env φ (push x ρ) B xs ρ' R →
      Fits cval env φ ρ (.forallE A B m) (x :: xs) ρ' R

/-- **ι at one stored rule** (theirs, verbatim, `6a64f2b84`). -/
def IotaRule (cval : Key md → (LevelParam → Nat) → V) (env : Env md) (r : Key md)
    (cv : ConstantVal md) (mI rP : Nat) (rl : RecRule md) : Prop :=
  ∀ (cvC : ConstantVal md) (nP nF : Nat),
    env.find? rl.ctor = some (.ctorInfo cvC nP nF) →
    ∀ (us : List Level) (φ : LevelParam → Nat) (ρ σ σC : BVarIdx → V) (xs ys : List V)
      (dom body RC : Expr md) (m : BinderMeta) (D : Key md) (ls : List Level) (R K X : V),
      us.length = cv.levelParams.length → xs.length = mI → ys.length = nP + nF →
      Denotes cval env φ ρ (.const r us) R →
      Fits cval env φ ρ (cv.type.instantiateLevelParams cv.levelParams us) xs σ
        (.forallE dom body m) →
      dom.getAppFn = .const D ls → Denotes cval env φ σ dom X →
      Denotes cval env φ ρ (.const rl.ctor ls) K →
      Fits cval env φ ρ (cvC.type.instantiateLevelParams cvC.levelParams ls) ys σC RC →
      ys.foldl app K ∈ˢ X →
      DenotesList cval env φ σ (dom.getAppArgs.take nP) (ys.take nP) →
      DenotesList cval env φ σC (RC.getAppArgs.drop nP) (xs.drop rP) →
      ∃ H, Denotes cval env φ ρ (rl.rhs.instantiateLevelParams cv.levelParams us) H ∧
        (xs ++ [ys.foldl app K]).foldl app R = (xs.take rP ++ ys.drop nP).foldl app H

/-- **ι at every stored rule** (theirs, verbatim; the field `Model.iota_rule`). -/
def IotaLaw (cval : Key md → (LevelParam → Nat) → V) (env : Env md) : Prop :=
  ∀ (r : Key md) (cv : ConstantVal md) (mI rP : Nat) (rules : List (RecRule md))
    (rl : RecRule md),
    env.find? r = some (.recInfo cv mI rP rules) → rl ∈ rules → IotaRule cval env r cv mI rP rl

/-- **δ** (theirs: the field `Model.defn_value`, stated as here). -/
def DefnValue {env : Env md} (M : Model V env) : Prop :=
  ∀ (cv : ConstantVal md) (value : Expr md) (hint : ReducibilityHint),
    ConstantInfo.defnInfo cv value hint ∈ env.consts →
    ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V), Denotes M.cval env φ ρ value (M.cval cv.name φ)

/-- **Level-parameter irrelevance** (theirs: the field `Model.cval_params`, stated as here). -/
def CvalParams {env : Env md} (M : Model V env) : Prop :=
  ∀ (n : Key md) (ci : ConstantInfo md), env.find? n = some ci →
    ∀ φ₁ φ₂ : LevelParam → Nat, (∀ p ∈ ci.toConstantVal.levelParams, φ₁ p = φ₂ p) →
      M.cval n φ₁ = M.cval n φ₂

/-- **The `Nat` operations on literals** (ours for now; the IxVM side has scheduled a public law
over all literals, with no `pow` cap, covering the fifteen roles): a stored operation applied to
literals denotes the literal of its value, by SrcEval's own table `PrimOp.eval2`. `Bool`
results are the role constructors. -/
def NatAccel {env : Env md} (M : Model V env) : Prop :=
  ∀ (op : IxCC.Src.PrimOp) (a b : Nat) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V),
    (op.arity = 1 → b = 0) →
    Denotes M.cval env φ ρ (primApp op a b) X →
    Denotes M.cval env φ ρ (primResultE (op.eval2 a b)) X

/-- **The projection of a constructor, value form** (ours for now; the IxVM side has scheduled
the projection of a constructor as a public law, their third note item 6, and has this form
from us): at a structure `T` whose projection table has an entry for field `i`, the entry's
constructor applied to sets that fit its type holds the `i`-th field at the entry's position. -/
def ProjCtor {env : Env md} (M : Model V env) : Prop :=
  ∀ (T : Key md) (i : Nat) (entry : ProjEntry md) (cvC : ConstantVal md) (nP nF : Nat)
    (φ : LevelParam → Nat) (ρ σ : BVarIdx → V) (R : Expr md) (Ps Fs : List V) (Y : V),
    env.findProj? T i = some entry → env.find? entry.ctor = some (.ctorInfo cvC nP nF) →
    Ps.length = nP → Fs.length = nF →
    Fits M.cval env φ ρ cvC.type (Ps ++ Fs) σ R → Fs[i]? = some Y →
    field (i + entry.off) ((Ps ++ Fs).foldl app (M.cval entry.ctor φ)) = Y

/-- **Constructor canonicity across parameters and levels** (ours; asked of the IxVM side on
2026-11-11 for parameters, the levels part to be sent with this statement). A constructor
image built at levels `ls'` and parameters `Ps'` that lies in the family `D` at levels `ls` and
parameters `Ps` is the image at `ls` and `Ps`, and its fields fit there. It holds in every
model in which a family's denotation is exactly its constructors' images at its own levels and
parameters, whether or not an image records them. It is what F5 needs at a parameterised
family (`Decidable`), where the major's parameters come from a different term than the
`case`'s. -/
def CtorCanon {env : Env md} (M : Model V env) : Prop :=
  ∀ (c : Key md) (cvC : ConstantVal md) (nP nF : Nat),
    env.find? c = some (.ctorInfo cvC nP nF) →
    ∀ (D : Key md) (ls ls' : List Level) (φ : LevelParam → Nat) (ρ τ σ' : BVarIdx → V)
      (dom R' : Expr md) (Ps Ps' Fs : List V) (K K' X : V),
      Ps.length = nP → Ps'.length = nP → Fs.length = nF →
      Denotes M.cval env φ ρ (.const c ls) K → Denotes M.cval env φ ρ (.const c ls') K' →
      Fits M.cval env φ ρ (cvC.type.instantiateLevelParams cvC.levelParams ls') (Ps' ++ Fs) σ' R' →
      R'.getAppFn = .const D ls' →
      dom.getAppFn = .const D ls → Denotes M.cval env φ τ dom X →
      DenotesList M.cval env φ τ (dom.getAppArgs.take nP) Ps →
      (Ps' ++ Fs).foldl app K' ∈ˢ X →
      (Ps' ++ Fs).foldl app K' = (Ps ++ Fs).foldl app K ∧
        ∃ (σ : BVarIdx → V) (R : Expr md),
          Fits M.cval env φ ρ (cvC.type.instantiateLevelParams cvC.levelParams ls) (Ps ++ Fs) σ R

/-- **The laws the development assumes of a model.** Each field says who is to supply it. -/
structure Laws {env : Env md} (M : Model V env) : Prop where
  /-- δ. IxVM side: `Model.defn_value`, a field, proved (`jcb/ixvmc-std-model`). -/
  defn_value : DefnValue M
  /-- ι. IxVM side: `Model.iota_rule`, a field, proved. -/
  iota_rule : IotaLaw M.cval env
  /-- level-parameter irrelevance. IxVM side: `Model.cval_params`, a field. -/
  cval_params : CvalParams M
  /-- the projection of a constructor, value form. IxVM side: scheduled. -/
  proj_ctor : ProjCtor M
  /-- the fifteen `Nat` operations on all literals. IxVM side: scheduled. -/
  nat_accel : NatAccel M
  /-- constructor canonicity. IxVM side: asked, unanswered; else IxCC's typed relation. -/
  ctor_canon : CtorCanon M

end Laws

end IxCC.Grounding
