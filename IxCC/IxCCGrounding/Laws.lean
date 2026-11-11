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
| `proj_ctor` | scheduled ("the projection of a constructor"); the value form is ours, **restricted** to structures that are not propositions | the IxVM side, scheduled |
| `nat_accel` | scheduled, over all literals, the fifteen roles | the IxVM side, scheduled |
| `ctor_canon` | none, and not scheduled by anyone; **restricted** to families that are not propositions | to be decided: the IxVM side, or IxCC from their recursor membership law |

`DenotesList`, `Fits`, `IotaRule` and `IotaLaw` are copied verbatim from theirs
(`IxC/Kernel/Denotes.lean` at `659ca9130`; the ι law's right-hand side denotes in its
conclusion).

## What was wrong, and what is assumed now

As first landed, `ctor_canon` was stated for every constructor and `proj_ctor` for every
structure. Both are false in a proof-irrelevant set model, where a proposition's constructor
image is the proof point `pt`:

* `ctor_canon`: `Exists.intro (fun _ => True) 1 pt` is `pt`, fits at its own parameters and lies
  in the inhabited `Exists (fun w => w = 0)`, so the law concluded that `pt` proves `1 = 0`. In
  the kernel's own set model (`IxCK/Kernel/SetTheory/Derive/Quot.lean`: `quotClass 0 _ _ _ = pt`,
  `quotSet 1 A R` the classes) `Quot.mk` built at level `0` is `pt`, which is the class of
  `ptTag` in `quotSet 1 {ptTag} R`, so the law concluded `pt ∈ {ptTag}`, which is false.
* `proj_ctor`: at a `Prop` structure with a data field (`Nonempty`, whose projection table the
  kernel installs) the image is `pt`, every component of `pt` is `pt` (`sfst_pt`, `ssnd_pt`),
  so the law concluded that every value of the field's type is `pt`.

Both grounding subjects' environments hold `Quot.mk`, so in the kernel's set model `Laws` had no
instance for them, and `fibRoot` and `decideRoot` as first landed said nothing there. The laws
are now assumed only at families that are not propositions (`finalSort`, the stored sort, with a
nonzero value at the assignments involved); the check supplies that at each use from a decided
fact (`NeverProp`: the family's stored sort is never zero).

**Not yet shown**: that `Laws`, in this restricted form, has a model for any environment. Three
fields are proved on the side that owes them (`defn_value`, `iota_rule`, `cval_params`), two are
scheduled there (`proj_ctor`, `nat_accel`), and the restricted `ctor_canon` is not scheduled by
anyone. Until that side's theorem lands, every theorem of this library is conditional on a
hypothesis whose consistency rests on the arguments written beside each law below.
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

/-- **δ** (theirs: the field `Model.defn_value`, stated as here).

*In a proof-irrelevant set model*: a definition's set is its value's (the model interprets each
stored definition by its value); at a proof the value and the constant are both `pt`. -/
def DefnValue {env : Env md} (M : Model V env) : Prop :=
  ∀ (cv : ConstantVal md) (value : Expr md) (hint : ReducibilityHint),
    ConstantInfo.defnInfo cv value hint ∈ env.consts →
    ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V), Denotes M.cval env φ ρ value (M.cval cv.name φ)

/-- **Level-parameter irrelevance** (theirs: the field `Model.cval_params`, stated as here).

*In a proof-irrelevant set model*: a constant's set is computed from the values of its own level
parameters only. -/
def CvalParams {env : Env md} (M : Model V env) : Prop :=
  ∀ (n : Key md) (ci : ConstantInfo md), env.find? n = some ci →
    ∀ φ₁ φ₂ : LevelParam → Nat, (∀ p ∈ ci.toConstantVal.levelParams, φ₁ p = φ₂ p) →
      M.cval n φ₁ = M.cval n φ₂

/-- **The `Nat` operations on literals** (ours for now; the IxVM side has scheduled a public law
over all literals, with no `pow` cap, covering the fifteen roles): a stored operation applied to
literals denotes the literal of its value, by SrcEval's own table `PrimOp.eval2`. `Bool`
results are the role constructors.

*In a proof-irrelevant set model*: `Nat` and `Bool` are not propositions, the stored operations
are the role-pinned definitions, which compute these values on numerals, and `eval2` agrees with
Lean's `Nat` operations (division and remainder by zero, the shifts). -/
def NatAccel {env : Env md} (M : Model V env) : Prop :=
  ∀ (op : IxCC.Src.PrimOp) (a b : Nat) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V),
    (op.arity = 1 → b = 0) →
    Denotes M.cval env φ ρ (primApp op a b) X →
    Denotes M.cval env φ ρ (primResultE (op.eval2 a b)) X

/-- **The projection of a constructor, value form, at a structure that is not a proposition**
(ours for now; the IxVM side has scheduled the projection of a constructor as a public law, and
has this form from us): at a structure `T` stored as an inductive whose sort `s` is not zero at
the constructor's assignment `φ`, and whose projection table has an entry for field `i`, the
entry's constructor applied to sets that fit its type holds the `i`-th field at the entry's
position.

*In a proof-irrelevant set model*: where the structure's sort is not zero its constructor is read
in the graph regime and its image is the tuple of its arguments after `off` tag positions, so
component `i + off` is field `i`. At a proposition the image is `pt`, every component of `pt` is
`pt` (`sfst_pt`, `ssnd_pt`), and a data field (`Nonempty`'s) cannot be read back: the law as first
landed, without the sort premise, was false there. -/
def ProjCtor {env : Env md} (M : Model V env) : Prop :=
  ∀ (T : Key md) (i : Nat) (entry : ProjEntry md) (cvC : ConstantVal md) (nP nF : Nat)
    (cvT : ConstantVal md) (caps : IndCaps md) (s : Level)
    (φ : LevelParam → Nat) (ρ σ : BVarIdx → V) (R : Expr md) (Ps Fs : List V) (Y : V),
    env.findProj? T i = some entry → env.find? entry.ctor = some (.ctorInfo cvC nP nF) →
    env.find? T = some (.indInfo cvT caps) → finalSort cvT.type = some s → Level.eval φ s ≠ 0 →
    Ps.length = nP → Fs.length = nF →
    Fits M.cval env φ ρ cvC.type (Ps ++ Fs) σ R → Fs[i]? = some Y →
    field (i + entry.off) ((Ps ++ Fs).foldl app (M.cval entry.ctor φ)) = Y

/-- **Constructor canonicity across parameters and levels, at families that are not
propositions** (ours; not scheduled by anyone). A constructor image built at levels `ls'` and
parameters `Ps'` that lies in the family `D` at levels `ls` and parameters `Ps` is the image at
`ls` and `Ps`, and its fields fit there, when `D` is stored as an inductive whose sort `s` is not
zero at either level instantiation. It is what F5 needs at a parameterised family (`Decidable`),
where the major's parameters come from a different term than the `case`'s.

*In a proof-irrelevant set model*: where the family's sort is not zero its constructors are read
in the graph regime and a constructor image is the tagged tuple of its fields; such a tuple lies
in the family at other parameters only if each field lies in its type there, and at parameters
off the family's domain its graph gives the empty set. At a proposition every image is `pt`,
which lies in every inhabited instance: as first landed, without the sort premises, the law was
false there (`Exists.intro`; `Quot.mk` built at level `0` and read at level `1` in the kernel's set
model). -/
def CtorCanon {env : Env md} (M : Model V env) : Prop :=
  ∀ (c : Key md) (cvC : ConstantVal md) (nP nF : Nat),
    env.find? c = some (.ctorInfo cvC nP nF) →
    ∀ (D : Key md) (cvD : ConstantVal md) (caps : IndCaps md) (s : Level)
      (ls ls' : List Level) (φ : LevelParam → Nat) (ρ τ σ' : BVarIdx → V)
      (dom R' : Expr md) (Ps Ps' Fs : List V) (K K' X : V),
      env.find? D = some (.indInfo cvD caps) → finalSort cvD.type = some s →
      Level.eval (Level.substFn φ cvD.levelParams ls) s ≠ 0 →
      Level.eval (Level.substFn φ cvD.levelParams ls') s ≠ 0 →
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
  /-- the projection of a constructor, value form, at structures that are not propositions.
  IxVM side: scheduled. -/
  proj_ctor : ProjCtor M
  /-- the fifteen `Nat` operations on all literals. IxVM side: scheduled. -/
  nat_accel : NatAccel M
  /-- constructor canonicity at families that are not propositions. Not scheduled by anyone. -/
  ctor_canon : CtorCanon M

end Laws

end IxCC.Grounding
