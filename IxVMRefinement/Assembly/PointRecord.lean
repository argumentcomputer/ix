import IxVMRefinement.Decl.PointModel
import IxVMRefinement.Assembly.NativeBlockLoads
import IxVMRefinement.Assembly.TypingBasisProj
import IxVMRefinement.Assembly.LateRegistry

/-! # The constructors-only route of a block: its record and its install

A block of two or more inductive types, or of one with a syntactic nested occurrence in a
constructor, takes the circuit's modeled branch (`KernelModeled::block_is_modeled` answers
non-zero). Its recursors are refused, so its unit installs the block's types and constructors
only, with the one-point model (`Decl.Point.pointBlock_install`).

This file states, over the store the step runs against:

* `ModeledBlockRecord`: the unit's record, a block of inductive members in Lean's logic whose
  member and constructor projection records the store holds;
* `ModeledAt`: the circuit's dispatch on the block is the modeled branch in every good run;
* `pointFormer`, `pointCtor`: the type former of member `i` and its constructor `j`, at their
  projection addresses' keys, with the readings of their types and their annotations;
* `PointReads`: the formers and constructors of the install are exactly those of the block's
  members, with the canonical annotation of each reading;
* `PointInstall`: the constants the install puts in front of a prefix, as the store reads them
  (the analogue of `BlockInstall` for a block of any number of members, every former at the
  empty capability record).
-/

namespace IxVM.Refinement.Typing

open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal IndCaps)
open IxVM.Refinement.Decl.Point (FormerRec CtorRec)

/-! ## The unit's record -/

/-- **The unit's record on the constructors-only route**: the block at `B` has the members `ms`,
all inductive types, is in Lean's logic, and the store holds each member's and each
constructor's projection record. -/
structure ModeledBlockRecord (E₀ : Ixon.Env) (B : _root_.Address) (cb : Ixon.Constant)
    (ms : Array Ixon.MutConst) : Prop where
  record : recordOf E₀ B = some cb
  muts : cb.info = .muts ms
  logic : InLogic cb
  inds : ∀ (i : Nat) (m : Ixon.MutConst), ms[i]? = some m → ∃ ind : Ixon.Inductive, m = .indc ind
  former : ∀ (i : Nat) (ind : Ixon.Inductive), ms[i]? = some (.indc ind) →
    recordOf E₀ (Core.iprjAddr B i) = some (memberProjection B i (.indc ind))
  ctors : ∀ (i : Nat) (ind : Ixon.Inductive), ms[i]? = some (.indc ind) → ∀ j < ind.ctors.size,
    recordOf E₀ (Core.cprjAddr B i j) = some (constructorProjection B i j)

/-- **The circuit's dispatch on the block is the modeled branch in every good run**: no bounded
run that hashes no collision with `E` observes `KernelModeled::block_is_modeled` answering `0`
at `B` (`NativeAt`). -/
def ModeledAt (E : Ixon.Env) (B : _root_.Address) : Prop := ¬ NativeAt E B

/-! ## The formers and constructors -/

/-- The reading of an expression of the block at `B` over the store `E`. -/
abbrev blockRead (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (B : _root_.Address)
    (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (e : Ixon.Expr) :
    Ix.Kernel.Reader.ReadM (Ix.Kernel.Reader.CExpr .anon) :=
  (exprReader t (fun x => E.blobs.get? x) cb id (blockSelf t B ms)).read e

/-- **The type former of member `i`** at the key of its projection address, with the reading
`ty₀` of its type, the capability record `caps` its reading declares, and the annotation
`ty'`. -/
def pointFormer (t : Ix.Kernel.RoleTable) (B : _root_.Address) (i : Nat) (ind : Ixon.Inductive)
    (ty₀ : Ix.Kernel.Expr .anon) (caps : IndCaps .anon) (ty' : Ix.Kernel.Expr .anon) :
    FormerRec :=
  ⟨⟨Core.keyOf t (Core.iprjAddr B i), List.range ind.lvls.toNat, ty₀⟩, caps, ty'⟩

/-- **Constructor `j` of member `i`** at the key of its projection address, with the reading
`cty₀` of its type, the record's counts and the annotation `cty'`. -/
def pointCtor (t : Ix.Kernel.RoleTable) (B : _root_.Address) (i j : Nat) (ct : Ixon.Constructor)
    (cty₀ cty' : Ix.Kernel.Expr .anon) : CtorRec :=
  ⟨⟨Core.keyOf t (Core.cprjAddr B i j), List.range ct.lvls.toNat, cty₀⟩, ct.params.toNat,
    ct.fields.toNat, cty'⟩

/-- **The reading of member `i`'s type over `E`, and its canonical annotation.** -/
def FormerRead (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (B : _root_.Address)
    (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (i : Nat) (ind : Ixon.Inductive)
    (ty₀ ty' : Ix.Kernel.Expr .anon) : Prop :=
  blockRead t E B cb ms ind.typ = .ok ty₀ ∧ ty₀.looseBVarsBounded 0 = true ∧
    ty₀.allLevelParamsDefined (List.range ind.lvls.toNat) = true ∧
    LoadedReads.canonAnn cb (List.range ind.lvls.toNat)
      ((Ingress.mutsRootOffset ms.toList i : Nat) : F) ind.typ ty₀ = some ty'

/-- **The reading of constructor `j` of member `i` over `E`, and its canonical annotation**; the
constructor's stored index is its position. -/
def CtorRead (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (B : _root_.Address)
    (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (i j : Nat) (ct : Ixon.Constructor)
    (cty₀ cty' : Ix.Kernel.Expr .anon) : Prop :=
  ct.cidx.toNat = j ∧ blockRead t E B cb ms ct.typ = .ok cty₀ ∧
    cty₀.looseBVarsBounded 0 = true ∧
    cty₀.allLevelParamsDefined (List.range ct.lvls.toNat) = true ∧
    LoadedReads.canonAnn cb (List.range ct.lvls.toNat)
      (((Ingress.mutsRootOffset ms.toList i : Nat) : F) + 1 + ((j : Nat) : F)) ct.typ cty₀ =
      some cty'

/-- **The formers and constructors are the block's**, each the reading of its record over `E`
with the canonical annotation of that reading: every former is member `i`'s and every member
has its own among them; every constructor is constructor `j` of member `i` and every constructor
slot has its own among them. -/
structure PointReads (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (B : _root_.Address)
    (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (formers : List FormerRec)
    (ctors : List CtorRec) : Prop where
  formerOf : ∀ f ∈ formers, ∃ (i : Nat) (ind : Ixon.Inductive) (ty₀ ty' : Ix.Kernel.Expr .anon)
      (caps : IndCaps .anon),
    ms[i]? = some (.indc ind) ∧ f = pointFormer t B i ind ty₀ caps ty' ∧
    FormerRead t E B cb ms i ind ty₀ ty'
  formerAt : ∀ (i : Nat) (ind : Ixon.Inductive), ms[i]? = some (.indc ind) →
    ∃ (ty₀ ty' : Ix.Kernel.Expr .anon) (caps : IndCaps .anon),
      pointFormer t B i ind ty₀ caps ty' ∈ formers ∧ FormerRead t E B cb ms i ind ty₀ ty'
  ctorOf : ∀ c ∈ ctors, ∃ (i : Nat) (ind : Ixon.Inductive) (j : Nat) (ct : Ixon.Constructor)
      (cty₀ cty' : Ix.Kernel.Expr .anon),
    ms[i]? = some (.indc ind) ∧ ind.ctors[j]? = some ct ∧
    c = pointCtor t B i j ct cty₀ cty' ∧ CtorRead t E B cb ms i j ct cty₀ cty'
  ctorAt : ∀ (i : Nat) (ind : Ixon.Inductive) (j : Nat), ms[i]? = some (.indc ind) → j < ind.ctors.size →
    ∃ (ct : Ixon.Constructor) (cty₀ cty' : Ix.Kernel.Expr .anon), ind.ctors[j]? = some ct ∧
      pointCtor t B i j ct cty₀ cty' ∈ ctors ∧ CtorRead t E B cb ms i j ct cty₀ cty'

/-! ## The install, as the store reads it -/

/-- **The new constants of a constructors-only install, as the store reads them.** `c` is the
prefix context and `new` the constants the install puts in front. The store `c.E` (decoded,
holding at a hashed block's projection addresses that block's projections) holds the block `cb`
at `B` with the members `ms`, all inductive, and their member and constructor projection
records; every former is stored at its key with the canonical annotation of its reading and the
empty capability record; every constructor at its key with the canonical annotation of its
reading and the record's counts; every new constant is at one of those keys and is the constant
the longer environment finds at its name. -/
structure PointInstall (c : Core.Ctx) (new : List (ConstantInfo .anon)) (B : _root_.Address)
    (cb : Ixon.Constant) (ms : Array Ixon.MutConst) : Prop where
  check : c.t.check = .ok ()
  decoded : Ingress.EnvDecoded c.E
  held : HashedBlockProjectionsHeld c.E
  block : recordOf c.E B = some cb
  muts : cb.info = .muts ms
  inds : ∀ (i : Nat) (m : Ixon.MutConst), ms[i]? = some m → ∃ ind : Ixon.Inductive, m = .indc ind
  formerRec : ∀ (i : Nat) (ind : Ixon.Inductive), ms[i]? = some (.indc ind) →
    recordOf c.E (Core.iprjAddr B i) = some (memberProjection B i (.indc ind))
  ctorRec : ∀ (i : Nat) (ind : Ixon.Inductive), ms[i]? = some (.indc ind) → ∀ j < ind.ctors.size,
    recordOf c.E (Core.cprjAddr B i j) = some (constructorProjection B i j)
  bounds : ∀ (i : Nat) (ind : Ixon.Inductive), ms[i]? = some (.indc ind) →
    ind.params.toNat < 2 ^ 56 ∧ ind.indices.toNat < 2 ^ 56 ∧ ind.ctors.size < 2 ^ 56
  used : Decl.UsedRefsStored c.t (appCtx c new).env cb
  former : ∀ (i : Nat) (ind : Ixon.Inductive), ms[i]? = some (.indc ind) → ∃ ty₀ ty' : Ix.Kernel.Expr .anon,
    blockRead c.t c.E B cb ms ind.typ = .ok ty₀ ∧
    ty₀.looseBVarsBounded 0 = true ∧
    ty₀.allLevelParamsDefined (List.range ind.lvls.toNat) = true ∧
    LoadedReads.canonAnn cb (List.range ind.lvls.toNat)
      ((Ingress.mutsRootOffset ms.toList i : Nat) : F) ind.typ ty₀ = some ty' ∧
    (appCtx c new).env.find? (Core.keyOf c.t (Core.iprjAddr B i)) =
      some (.indInfo ⟨Core.keyOf c.t (Core.iprjAddr B i), List.range ind.lvls.toNat, ty'⟩ {})
  ctor : ∀ (i : Nat) (ind : Ixon.Inductive), ms[i]? = some (.indc ind) → ∀ j < ind.ctors.size,
    ∃ (ct : Ixon.Constructor) (cty cty' : Ix.Kernel.Expr .anon),
    ind.ctors[j]? = some ct ∧ ct.cidx.toNat = j ∧
    blockRead c.t c.E B cb ms ct.typ = .ok cty ∧
    cty.looseBVarsBounded 0 = true ∧
    cty.allLevelParamsDefined (List.range ct.lvls.toNat) = true ∧
    LoadedReads.canonAnn cb (List.range ct.lvls.toNat)
      (((Ingress.mutsRootOffset ms.toList i : Nat) : F) + 1 + ((j : Nat) : F)) ct.typ cty = some cty' ∧
    (appCtx c new).env.find? (Core.keyOf c.t (Core.cprjAddr B i j)) =
      some (.ctorInfo ⟨Core.keyOf c.t (Core.cprjAddr B i j), List.range ct.lvls.toNat, cty'⟩
        ct.params.toNat ct.fields.toNat)
  newName : ∀ ci ∈ new,
    (∃ (i : Nat) (ind : Ixon.Inductive), ms[i]? = some (.indc ind) ∧ ci.name = Core.keyOf c.t (Core.iprjAddr B i)) ∨
    ∃ (i : Nat) (ind : Ixon.Inductive) (j : Nat), ms[i]? = some (.indc ind) ∧ j < ind.ctors.size ∧
      ci.name = Core.keyOf c.t (Core.cprjAddr B i j)
  newFind : ∀ ci ∈ new, (appCtx c new).env.find? ci.name = some ci

theorem PointInstall.wf {c : Core.Ctx} {new : List (ConstantInfo .anon)} {B : _root_.Address}
    {cb : Ixon.Constant} {ms : Array Ixon.MutConst} (hI : PointInstall c new B cb ms) :
    c.t.wf = true := by
  unfold Ix.Kernel.RoleTable.wf
  rw [hI.check]
  rfl

end IxVM.Refinement.Typing
