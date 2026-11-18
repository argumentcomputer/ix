import IxVMRefinement.FamilyAlias.Assembly
import IxVMRefinement.StatementRel.LoadedReadsCanonRec

/-! # The family check's selected forms

The family check selects, with the family as read (`blk`), one annotated type for each member
(`tys`, in the order of `blk`'s types, constructors and recursors) and one list of annotated
right-hand sides for each recursor (`rhsss`). The record installs exactly those
(`famStepConclusion_installed`; `SelectedInstalled` names its two exports).

What the circuit's family check gives of the selected forms, stated beside them, store-free
except for the store a major premise's record is read from:

* `FamilyTysCanon`: the selected forms are the circuit's loads, by position: the canonical
  annotation (`LoadedReads.canonAnn`) of each type's and constructor's reading at its root is its
  `tys` entry; each recursor of the family record, read as a recursor, has the reading's level
  count and scope, declares no K, and has as canonical annotation of its read type its `tys`
  entry and as canonical rules' right-hand sides its `rhsss` entry (`FamRecCanon`);
* `FamRecsCompanion`: the four facts a stored recursor owes the companions, at each recursor of
  the family at its selected annotated type, its rules as read and the constructors a rule names
  as the record stores them (`FamRecCompanion`);
* `SelectedForms`: the two, at the block's and the family record's members.

The lemmas that give the load facts and the companion facts of the installed constants from these
are in `FamilyAlias/TysCanon.lean`. -/

namespace IxVM.Refinement.Typing.FamilyAlias

open IxVM.Consistency
open IxVM (F)
open IxVM.Refinement.Core (KExpr)
open Ix.Kernel (ConstantInfo ConstantVal RecRule LevelParam)
open IxVM.Refinement.Decl.FamilyAlias (nonrecsOf recsOf storedMember)

set_option linter.unusedVariables false

/-! ## The installed forms -/

/-- **The family record's installation of the selected forms** at `env₂` (the two exports of
`famStepConclusion_installed`): each type and constructor of the family at position `i` is stored
as `storedMember` of its `tys` entry; each recursor at position `i` of the recursors is stored at
its `tys` entry with rules stored as the rules as read whose right-hand sides are its `rhsss`
entry. -/
structure SelectedInstalled (blk : List (ConstantInfo .anon)) (tys : List KExpr)
    (rhsss : List (List KExpr)) (env₂ : Ix.Kernel.Env .anon) : Prop where
  nonrecs : ∀ (i : Nat) (ci : ConstantInfo .anon) (tyA : KExpr),
    (nonrecsOf blk)[i]? = some ci → tys[i]? = some tyA →
    env₂.find? ci.name = some (storedMember ci tyA)
  recs : ∀ (i : Nat) (cv : ConstantVal .anon) (mI rP : Nat) (rules : List (RecRule .anon))
      (tyA : KExpr) (rhss : List KExpr),
    (recsOf blk)[i]? = some (.recInfo cv mI rP rules) →
    tys[(nonrecsOf blk).length + i]? = some tyA → rhsss[i]? = some rhss →
    ∃ rules' : List (RecRule .anon),
      env₂.find? cv.name = some (.recInfo ⟨cv.name, cv.levelParams, tyA⟩ mI rP rules') ∧
      List.Forall₂ RuleStored rules' rules ∧
      List.Forall₂ (fun (r' : RecRule .anon) rhsA => r'.rhs = rhsA) rules' rhss

/-! ## The selected forms, as the circuit loads them -/

/-- **The circuit's loaded form of one recursor of the family record, at its selected annotated
type `tyA` and right-hand sides `rhss`**: the recursor `rc` (projection `p` of the block `cb` with
members `ms`), read with level parameters `ps`, type `ty₀` and rules `rules₀`, has the reading's
level count; the read type and rules are closed and over `ps`; it declares no K; the canonical
annotation of the read type at the member's root is `tyA`; the canonical rules from the next root
have right-hand sides `rhss`. -/
structure FamRecCanon (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (p : Ixon.RecursorProj)
    (rc : Ixon.Recursor) (ps : List LevelParam) (ty₀ : KExpr) (rules₀ : List (RecRule .anon))
    (tyA : KExpr) (rhss : List KExpr) : Prop where
  lvls : ps.length = rc.lvls.toNat
  tyBounded : ty₀.looseBVarsBounded 0 = true
  tyLevels : ty₀.allLevelParamsDefined ps = true
  rulesScoped : ∀ rl ∈ rules₀,
    rl.rhs.looseBVarsBounded 0 = true ∧ rl.rhs.allLevelParamsDefined ps = true
  /-- No recursor of a family record declares K: `KernelModeled::check_recs` reads each recursor
  of the record with `get_ci` and asserts its K flag is `0` ("modeled recursor declares K"). -/
  notK : rc.k = false
  ty : LoadedReads.canonAnn cb ps ((L1.mutsRootOffset ms.toList p.idx.toNat : Nat) : F) rc.typ
    ty₀ = some tyA
  rules : ∃ rls : List (RecRule .anon),
    LoadedReads.canonRules cb ps rc.k rc.params.toNat
      (((L1.mutsRootOffset ms.toList p.idx.toNat : Nat) : F) + 1) rc.rules.toList rules₀ =
        some rls ∧
    List.Forall₂ (fun (rl : RecRule .anon) (rhsA : KExpr) => rl.rhs = rhsA) rls rhss

/-- **The family check's selected annotated types and right-hand sides are the circuit's loads**
(store-free, by position), for the block `cb` (members `ms`, at `A`), the family record `crb`
(members `rs`, at `rb`), the family as read `blk` and the selected `tys` and `rhsss`. Each field
is the circuit side's: the family check compares each member as loaded, renamed by the payload's
arrays, with its named model (`KernelModeled::member_val`, through `members_val`; the loaded form
is the canonical annotation of the reading, `LoadedReads.get_ci_iprj_canon`, `get_ci_cprj_canon`,
`get_ci_rprj_canon`), and the selected form is the model's annotated type
(`MemberFacts.model`); two annotations of one reading with one image under the renaming are one
(the review's `samePayloadGivesActualType`). -/
structure FamilyTysCanon (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (A : _root_.Address)
    (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (rb : _root_.Address) (crb : Ixon.Constant)
    (rs : Array Ixon.MutConst) (blk : List (ConstantInfo .anon)) (tys : List KExpr)
    (rhsss : List (List KExpr)) : Prop where
  /-- Each type of the family, at position `k` of the types and constructors, read over the
  store's blobs as `ty₀` at its inductive member `i`: the reading is closed with its level
  parameters defined, and its canonical annotation at the member's root is `tys[k]`. Producer:
  `KernelModeled::member_val` at the type (`members_val`), with the load `Ingress::get_ci_iprj`. -/
  ind : ∀ (k : Nat) (ci : ConstantInfo .anon) (tyA : KExpr),
    (nonrecsOf blk)[k]? = some ci → tys[k]? = some tyA →
    ∀ (i : Nat) (ind : Ixon.Inductive) (ty₀ : Ix.Kernel.Expr .anon),
      i < UInt64.size → ms[i]? = some (.indc ind) → ci.name = keyOf t (Core.iprjAddr A i) →
      (exprReader t (fun x => E₀.blobs.get? x) cb id (blockSelf t A ms)).read ind.typ =
        .ok ty₀ →
      ty₀.looseBVarsBounded 0 = true ∧
        ty₀.allLevelParamsDefined (List.range ind.lvls.toNat) = true ∧
        LoadedReads.canonAnn cb (List.range ind.lvls.toNat)
          ((L1.mutsRootOffset ms.toList i : Nat) : F) ind.typ ty₀ = some tyA
  /-- Each constructor of the family, at position `k`, read as `ty₀` at constructor `j` of member
  `i`: the reading is closed with its level parameters defined, and its canonical annotation at
  the constructor's root is `tys[k]`. Producer: `KernelModeled::member_val` at the constructor,
  with the load `Ingress::get_ci_cprj`. -/
  ctor : ∀ (k : Nat) (ci : ConstantInfo .anon) (tyA : KExpr),
    (nonrecsOf blk)[k]? = some ci → tys[k]? = some tyA →
    ∀ (i : Nat) (ind : Ixon.Inductive) (j : Nat) (ct : Ixon.Constructor)
      (ty₀ : Ix.Kernel.Expr .anon),
      i < UInt64.size → j < UInt64.size → ms[i]? = some (.indc ind) →
      ind.ctors[j]? = some ct → ci.name = keyOf t (Core.cprjAddr A i j) →
      (exprReader t (fun x => E₀.blobs.get? x) cb id (blockSelf t A ms)).read ct.typ =
        .ok ty₀ →
      ty₀.looseBVarsBounded 0 = true ∧
        ty₀.allLevelParamsDefined (List.range ct.lvls.toNat) = true ∧
        LoadedReads.canonAnn cb (List.range ct.lvls.toNat)
          (((L1.mutsRootOffset ms.toList i : Nat) : F) + 1 + ((j : Nat) : F)) ct.typ ty₀ =
          some tyA
  /-- Each recursor of the family, at position `k` of the recursors, read as the recursor
  `cv` (rules `rules₀`) at member `p` of the family record: its loaded form at its selected type
  `tys[n + k]` and right-hand sides `rhsss[k]` (`FamRecCanon`). Producer: `KernelModeled::check_recs`
  (the load `get_ci`, the K assertion) and `check_rules` (the rules' right-hand sides), with
  `member_val` at the recursor. -/
  recr : ∀ (k : Nat) (cv : ConstantVal .anon) (mI rP : Nat) (rules₀ : List (RecRule .anon))
      (tyA : KExpr) (rhss : List KExpr),
    (recsOf blk)[k]? = some (.recInfo cv mI rP rules₀) →
    tys[(nonrecsOf blk).length + k]? = some tyA → rhsss[k]? = some rhss →
    ∀ (p : Ixon.RecursorProj) (rc : Ixon.Recursor), p.block = rb →
      rs[p.idx.toNat]? = some (.recr rc) →
      cv.name = keyOf t (memberAddr rb p.idx.toNat (.recr rc)) →
      RecReads t (recordOf E₀) (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs) cv.name rc
        (.recInfo cv mI rP rules₀) →
      FamRecCanon crb rs p rc cv.levelParams cv.type rules₀ tyA rhss

/-! ## The companion facts at the selected forms -/

/-- **The four facts a recursor of the family owes the companions, at its selected annotated type
`tyA`** and its rules as read `rules₀`, over the store `E` (the record of a major premise's
family), the prefix `env`, the family as read `blk` and the selected `tys` (the constructor a rule
names, as the record stores it: `RuleCtor`): its major premise's record, its rules' constructors,
its plain rules' major premise, and its rules' constructor heads. -/
structure FamRecCompanion (E : Ixon.Env) (t : Ix.Kernel.RoleTable) (env : Ix.Kernel.Env .anon)
    (blk : List (ConstantInfo .anon)) (tys : List KExpr) (tyA : KExpr) (mI rP : Nat)
    (rules₀ : List (RecRule .anon)) : Prop where
  major : ∀ (p : _root_.Address) (us : List Core.KLevel), rules₀ ≠ [] →
    (Core.piDomAt mI tyA).map (·.getAppFn) = some (.const (Core.keyOf t p) us) →
    ∃ cm, Ix.Cert.recordAt E p = some cm
  rules : (rules₀.map (·.ctor)).Nodup ∧
    ∀ (p : _root_.Address) (cm : Ixon.Constant) (ip : Ixon.InductiveProj)
      (us : List Core.KLevel),
      (Core.piDomAt mI tyA).map (·.getAppFn) = some (.const (Core.keyOf t p) us) →
      Ix.Cert.recordAt E p = some cm → cm.info = .iPrj ip →
      ∀ j rl, rules₀[j]? = some rl → rl.ctor = Core.keyOf t (Core.cprjAddr ip.block ip.idx.toNat j)
  plain : ∀ (rl : RecRule .anon) (cvj : ConstantVal .anon) (nP nF : Nat), rl ∈ rules₀ →
    Decl.FamilyAlias.RuleCtor env blk tys rl.ctor cvj nP nF →
    Ix.Kernel.Expr.recRulePlain tyA mI rP nP cvj.levelParams = true →
    ∃ D T, Core.piDomAt mI tyA = some D ∧
      D.getAppFn = .const T (cvj.levelParams.map .param) ∧
      D.getAppArgs.take nP = (List.range nP).map (fun i => .bvar (mI - 1 - i)) ∧
      D.getAppArgs.drop nP = (List.range (mI - rP)).map fun i => .bvar (mI - rP - 1 - i)
  head : ∀ (rl : RecRule .anon) (cvj : ConstantVal .anon) (nP nF : Nat)
    (T : Ix.Kernel.Key .anon) (us : List Core.KLevel), rl ∈ rules₀ →
    Decl.FamilyAlias.RuleCtor env blk tys rl.ctor cvj nP nF →
    (Core.piDomAt mI tyA).map (·.getAppFn) = some (.const T us) →
    ∃ tus, (Ix.Kernel.Expr.piResult cvj.type).getAppFn = .const T tus

/-- **The companion facts of every recursor of the family, at its position**: the recursor at
position `k` of the recursors, with its selected type `tys[n + k]` (`FamRecCompanion`). -/
def FamRecsCompanion (E : Ixon.Env) (t : Ix.Kernel.RoleTable) (env : Ix.Kernel.Env .anon)
    (blk : List (ConstantInfo .anon)) (tys : List KExpr) : Prop :=
  ∀ (k : Nat) (cv : ConstantVal .anon) (mI rP : Nat) (rules₀ : List (RecRule .anon))
    (tyA : KExpr), (recsOf blk)[k]? = some (.recInfo cv mI rP rules₀) →
    tys[(nonrecsOf blk).length + k]? = some tyA →
    FamRecCompanion E t env blk tys tyA mI rP rules₀

/-! ## The selected forms of a block with its family record -/

/-- **What the family check gives of its selected forms**, for the block `c` at `A` and the
family record `crb` at `rb`, the family as read `blk`, the selected `tys` and `rhsss`, at the
prefix `env` and the store `E`: the selected forms are the circuit's loads (`FamilyTysCanon`, at
the two records' members), and each recursor of the family owes the companions their four facts
at its selected type (`FamRecsCompanion`). -/
def SelectedForms (t : Ix.Kernel.RoleTable) (E₀ E : Ixon.Env) (A : _root_.Address)
    (c : Ixon.Constant) (rb : _root_.Address) (crb : Ixon.Constant) (env : Ix.Kernel.Env .anon)
    (blk : List (ConstantInfo .anon)) (tys : List KExpr) (rhsss : List (List KExpr)) : Prop :=
  (∀ ms rs, c.info = .muts ms → crb.info = .muts rs →
    FamilyTysCanon t E₀ A c ms rb crb rs blk tys rhsss) ∧
  FamRecsCompanion E t env blk tys

end IxVM.Refinement.Typing.FamilyAlias
