import IxC.Kernel.Denotes
import IxCCGrounding.Syntax

/-!
# The kernel's model, and the derived / legacy laws (`IxCCGrounding.Laws`)

**The one module of the development that imports the kernel's model** (`IxC.Kernel.Denotes`,
the statement half: `Denotes`, `DenotesList`, `Fits`, `GradedBy`, `SpineOk`, `IotaRule`, `IotaLaw`,
`ProjLaw`, `natArithOps`, `natCmpOps`, `NatLitLaw`, `GradedLaw`, `Model` and, through its imports,
the set theory interface and `SetModel.Ops`; not the kernel's proof tree). Every other module
reaches the model through this one.

## Direct use of `Ix.Kernel.Model`

`Ix.Kernel.Model V env` (`IxC/Kernel/Denotes.lean`) directly supplies every law the canonicity-free
root theorems use:

* `Model.defn_value` (δ),
* `Model.iota_rule : Ix.Kernel.IotaLaw M.cval env` (ι, guarded with `GradedBy` and `SpineOk`;
  unconditional form via `Ix.Kernel.IotaRule.of_premises`),
* `Model.proj_law : Ix.Kernel.ProjLaw M.cval env` (projections via `projVal` and structure η when
  `entry.off ≤ 1`),
* `Model.lit_ops : Ix.Kernel.NatLitLaw M.cval env` (`Nat` operations on literals),
* `Model.graded : Ix.Kernel.GradedLaw M.cval env` (graded readings of stored types and values),
* `Model.cval_params` (level-parameter irrelevance).

`IxCCGrounding.Adapt678` derives `ProjCtor M` from `M.proj_law` (`projCtor_of_projLaw`), `NatAccel M`
from `M.lit_ops` under the decided premise `LitDefs env` (`natAccel_of_litOps`), and `LawsNoCanon M`
from `M` and `LitDefs env` (`lawsNoCanon_of_model`). The canonicity-free root theorems quantify
directly over `M : Ix.Kernel.Model V env` with no copied law structure.

The legacy `Laws M` structure keeps `CtorCanon M` (constructor canonicity at non-`Prop` families)
for the older non-`noCanon` theorems (`rootSound`, `fibRoot`, `decideRoot`, `allP_of_check`).
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel

universe w

section Laws

variable {V : Type w} [Ix.Kernel.SetTheory V] {md : Mode}

/-- **δ** (the type of `Ix.Kernel.Model.defn_value`). -/
def DefnValue {env : Env md} (M : Model V env) : Prop :=
  ∀ (cv : ConstantVal md) (value : Expr md) (hint : ReducibilityHint),
    ConstantInfo.defnInfo cv value hint ∈ env.consts →
    ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V), Denotes M.cval env φ ρ value (M.cval cv.name φ)

/-- **Level-parameter irrelevance** (the type of `Ix.Kernel.Model.cval_params`). -/
def CvalParams {env : Env md} (M : Model V env) : Prop :=
  ∀ (n : Key md) (ci : ConstantInfo md), env.find? n = some ci →
    ∀ φ₁ φ₂ : LevelParam → Nat, (∀ p ∈ ci.toConstantVal.levelParams, φ₁ p = φ₂ p) →
      M.cval n φ₁ = M.cval n φ₂

/-- **The `Nat` operations on literals** (derived from `Model.lit_ops` under `LitDefs` in
`IxCCGrounding.Adapt678`): a stored operation applied to literals denotes the literal of its value,
by SrcEval's own table `PrimOp.eval2`. `Bool` results are the role constructors. -/
def NatAccel {env : Env md} (M : Model V env) : Prop :=
  ∀ (op : IxCC.Src.PrimOp) (a b : Nat) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V),
    (op.arity = 1 → b = 0) →
    Denotes M.cval env φ ρ (primApp op a b) X →
    Denotes M.cval env φ ρ (primResultE (op.eval2 a b)) X

/-- **The projection of a constructor, value form, at a structure that is not a proposition**
(derived from `Model.proj_law` in `IxCCGrounding.Adapt678`): at a stored inductive `T` whose
projection table has an entry for field `i` with `entry.structSort` nonzero at the constructor's
assignment `φ`, `projVal` of the entry's constructor applied to sets fitting its type is field `i`.
Covers both native structures (`entry.off ≤ 1`, reading `field (i + entry.off)`) and modeled
structures (`entry.off ≥ 2`, reading `projChainKey`). -/
def ProjCtor {env : Env md} (M : Model V env) : Prop :=
  ∀ (T : Key md) (i : Nat) (entry : ProjEntry md) (cvC : ConstantVal md) (nP nF : Nat)
    (cvT : ConstantVal md) (caps : IndCaps md)
    (φ : LevelParam → Nat) (ρ σ : BVarIdx → V) (R : Expr md) (Ps Fs : List V) (Y : V),
    env.findProj? T i = some entry → env.find? entry.ctor = some (.ctorInfo cvC nP nF) →
    env.find? T = some (.indInfo cvT caps) → Level.eval φ entry.structSort ≠ 0 →
    Ps.length = nP → Fs.length = nF →
    Fits M.cval env φ ρ cvC.type (Ps ++ Fs) σ R → Fs[i]? = some Y →
    projVal M.cval T i entry ((Ps ++ Fs).foldl app (M.cval entry.ctor φ)) = Y

/-- **Constructor canonicity across parameters and levels, at families that are not
propositions** (legacy, for the older non-`noCanon` theorems; not assumed by the canonicity-free
root theorems). -/
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

/-- **The legacy laws structure (including `CtorCanon`)** for the older non-`noCanon` theorems. -/
structure Laws {env : Env md} (M : Model V env) : Prop where
  defn_value : DefnValue M
  iota_rule : IotaLaw M.cval env
  cval_params : CvalParams M
  proj_ctor : ProjCtor M
  nat_accel : NatAccel M
  ctor_canon : CtorCanon M

/-- **The five core laws other than canonicity** (using `Ix.Kernel.IotaLaw` directly): what every
internal lemma of the library that does not read `ctor_canon` takes. Inhabited for every
`M : Ix.Kernel.Model V env` and `LitDefs env` via `lawsNoCanon_of_model`. -/
structure LawsCore {env : Env md} (M : Model V env) : Prop where
  defn_value : DefnValue M
  iota_rule : IotaLaw M.cval env
  cval_params : CvalParams M
  proj_ctor : ProjCtor M
  nat_accel : NatAccel M

/-- `Laws` without its canonicity. -/
theorem lawsCore_of_laws {env : Env md} {M : Model V env} (hL : Laws M) : LawsCore M :=
  ⟨hL.defn_value, hL.iota_rule, hL.cval_params, hL.proj_ctor, hL.nat_accel⟩

/-- **The laws of the canonicity-free family** (`rootSound_noCanon` and its corollaries):
directly inhabited from `M : Ix.Kernel.Model V env` and `LitDefs env` by `lawsNoCanon_of_model`. -/
structure LawsNoCanon {env : Env md} (M : Model V env) : Prop where
  defn_value : DefnValue M
  iota_rule : IotaLaw M.cval env
  cval_params : CvalParams M
  proj_ctor : ProjCtor M
  nat_accel : NatAccel M

/-- The canonicity-free laws give the core. -/
theorem LawsNoCanon.core {env : Env md} {M : Model V env} (hL : LawsNoCanon M) : LawsCore M :=
  ⟨hL.defn_value, hL.iota_rule, hL.cval_params, hL.proj_ctor, hL.nat_accel⟩

end Laws

end IxCC.Grounding
