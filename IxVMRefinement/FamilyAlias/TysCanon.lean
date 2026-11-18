import IxVMRefinement.FamilyAlias.BlockRowCheck
import IxVMRefinement.FamilyAlias.Assembly
import IxVMRefinement.Assembly.TypingRecLateOut

/-! # The family check's selected annotated types are the canonical loads

The family check selects, with the family as read (`blk`), one annotated type for each member
(`tys`, in the order of `blk`'s types, constructors and recursors) and one list of annotated
right-hand sides for each recursor (`rhsss`), and the record installs exactly those
(`famStepConclusion_installed`: each type and constructor as `storedMember` of its `tys` entry,
each recursor at its `tys` entry with rules whose right-hand sides are its `rhsss` entry).

`FamilyTysCanon` is what the circuit's loads give of those selected forms, store-free and by
position: the canonical annotation (`LoadedReads.canonAnn`) of each type's and constructor's
reading at its root is its `tys` entry; each recursor of the family record, read as a recursor,
has the reading's level count and scope, declares no K, and has as canonical annotation of its
read type its `tys` entry and as canonical rules' right-hand sides its `rhsss` entry.

`familyMembersCanon_of_tys`: the seam of the loads (`FamilyMembersCanon`) at the environment the
record installs, from `FamilyTysCanon`, the installed forms and the family record's references
stored. No quantifier over other installations: the stored constants are the selected ones. -/

namespace IxVM.Refinement.Typing.FamilyAlias

open IxVM.Consistency
open IxVM (F)
open IxVM.Refinement.Core (KExpr)
open Ix.Kernel (ConstantInfo ConstantVal RecRule LevelParam)
open IxVM.Refinement.Decl.FamilyAlias (FamilyCheckFacts FamilyAdvice nonrecsOf recsOf
  storedMember)

set_option linter.unusedVariables false

/-! ## Lists -/

/-- Four `List.Forall₂` around one square give the fourth side. -/
theorem forall₂_meet {α β γ δ : Type} {P : γ → α → Prop} {Q : β → γ → Prop}
    {R : α → δ → Prop} {S : β → δ → Prop} {T : α → β → Prop} :
    ∀ {lc : List γ} {la : List α} {lb : List β} {ld : List δ},
      List.Forall₂ P lc la → List.Forall₂ Q lb lc → List.Forall₂ R la ld →
      List.Forall₂ S lb ld → (∀ c a b d, P c a → Q b c → R a d → S b d → T a b) →
      List.Forall₂ T la lb
  | _, _, _, _, .nil, hq, _, _, _ => by
    cases hq
    exact .nil
  | _, _, _, _, .cons hp hps, hq, hr, hs, H => by
    cases hq with
    | cons hq hqs =>
      cases hr with
      | cons hr hrs =>
        cases hs with
        | cons hs hss => exact .cons (H _ _ _ _ hp hq hr hs) (forall₂_meet hps hqs hrs hss H)

/-- The recursors' facts list one right-hand-side list for each recursor. -/
theorem recsFacts_rhsss_length {env : Ix.Kernel.Env .anon}
    {g : Ix.Kernel.Key .anon → Ix.Kernel.Key .anon} {blk : List (ConstantInfo .anon)}
    {tys : List KExpr} :
    ∀ {recs : List (ConstantInfo .anon)} {tysR : List KExpr} {rhsss : List (List KExpr)}
      {thss : List (List (Ix.Kernel.Key .anon))},
      Decl.FamilyAlias.RecsFacts env g blk tys recs tysR rhsss thss →
      rhsss.length = recs.length
  | [], _, _, _, h => by
    obtain ⟨-, h2, -⟩ := Decl.FamilyAlias.RecsFacts.nil_inv h
    rw [h2]
  | _ :: rest, _, _, _, h => by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, -, -, h3, -, -, hr⟩ :=
      Decl.FamilyAlias.RecsFacts.cons_inv h
    rw [h3, List.length_cons, List.length_cons, recsFacts_rhsss_length hr]

/-- A type or constructor of the family has its selected annotated type. -/
theorem tys_of_nonrec {env : Ix.Kernel.Env .anon} {blk : List (ConstantInfo .anon)}
    {adv : FamilyAdvice} {tys : List KExpr} {rhsss : List (List KExpr)}
    (hF : FamilyCheckFacts env blk adv tys rhsss) {k : Nat} {ci : ConstantInfo .anon}
    (h : (nonrecsOf blk)[k]? = some ci) : ∃ tyA, tys[k]? = some tyA := by
  have hlen := Decl.FamilyAlias.MembersFacts.length_eq blk tys hF.members
  have hl2 := congrArg List.length hF.split
  rw [List.length_append] at hl2
  have hlt := (List.getElem?_eq_some_iff.mp h).1
  exact ⟨tys[k]'(by omega), List.getElem?_eq_getElem (by omega)⟩

/-- A recursor of the family has its selected annotated type and right-hand sides. -/
theorem tys_of_rec {env : Ix.Kernel.Env .anon} {blk : List (ConstantInfo .anon)}
    {adv : FamilyAdvice} {tys : List KExpr} {rhsss : List (List KExpr)}
    (hF : FamilyCheckFacts env blk adv tys rhsss) {k : Nat} {ci : ConstantInfo .anon}
    (h : (recsOf blk)[k]? = some ci) :
    (∃ tyA, tys[(nonrecsOf blk).length + k]? = some tyA) ∧ ∃ rhss, rhsss[k]? = some rhss := by
  have hlen := Decl.FamilyAlias.MembersFacts.length_eq blk tys hF.members
  have hl2 := congrArg List.length hF.split
  rw [List.length_append] at hl2
  have hlt := (List.getElem?_eq_some_iff.mp h).1
  have hr := recsFacts_rhsss_length hF.recs
  exact ⟨⟨tys[(nonrecsOf blk).length + k]'(by omega), List.getElem?_eq_getElem (by omega)⟩,
    ⟨rhsss[k]'(by omega), List.getElem?_eq_getElem (by omega)⟩⟩

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

/-! ## The seam of the loads at the installed environment -/

/-- **The seam of the loads at the environment the family record installs** (module docstring):
`FamilyMembersCanon` at `env₂`, from the selected forms as loaded (`FamilyTysCanon`), the members
as `env₂` stores them (`famStepConclusion_installed`'s two exports), and the family record's
references stored at `env₂`. -/
theorem familyMembersCanon_of_tys {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ())
    {E₀ : Ixon.Env} {A rb : _root_.Address} {cb crb : Ixon.Constant}
    {ms rs : Array Ixon.MutConst} (hB : FamBlockRecord E₀ A cb ms)
    (hrb : FamRecRecord E₀ rb crb rs) {env env₂ : Ix.Kernel.Env .anon}
    {blk : List (ConstantInfo .anon)} {adv : FamilyAdvice} {tys : List KExpr}
    {rhsss : List (List KExpr)} (hF : FamilyCheckFacts env blk adv tys rhsss)
    (hreads : FamDeclReads t E₀ A cb rb crb blk)
    (hT : FamilyTysCanon t E₀ A cb ms rb crb rs blk tys rhsss)
    (hN : ∀ (i : Nat) (ci : ConstantInfo .anon) (tyA : KExpr),
      (nonrecsOf blk)[i]? = some ci → tys[i]? = some tyA →
      env₂.find? ci.name = some (storedMember ci tyA))
    (hR : ∀ (i : Nat) (cv : ConstantVal .anon) (mI rP : Nat) (rules : List (RecRule .anon))
      (tyA : KExpr) (rhss : List KExpr),
      (recsOf blk)[i]? = some (.recInfo cv mI rP rules) →
      tys[(nonrecsOf blk).length + i]? = some tyA → rhsss[i]? = some rhss →
      ∃ rules' : List (RecRule .anon),
        env₂.find? cv.name = some (.recInfo ⟨cv.name, cv.levelParams, tyA⟩ mI rP rules') ∧
        List.Forall₂ RuleStored rules' rules ∧
        List.Forall₂ (fun (r' : RecRule .anon) rhsA => r'.rhs = rhsA) rules' rhss)
    (husedRecs : Decl.UsedRefsStored t env₂ crb) :
    FamilyMembersCanon t E₀ A cb ms rb crb rs env₂ := by
  have htwf : t.wf = true := by
    unfold Ix.Kernel.RoleTable.wf
    rw [ht]
    rfl
  have hroles : (t.bound.toList.map (·.1)).Nodup := (Ix.Kernel.RoleTable.check_nodup ht).1
  refine ⟨?_, ?_, husedRecs, ?_⟩
  · -- the types
    intro i ind ty₀ cv caps hi hm hty hf
    have hx : FamAddr A cb rb crb (Core.iprjAddr A i) :=
      Or.inl (Or.inr ⟨ms, i, .indc ind, hB.muts, hm, Or.inl rfl⟩)
    obtain ⟨ci₀, hci₀, hk⟩ := hreads.2.2.1 _ hx
    obtain ⟨y, -, hy, hry⟩ := hreads.2.1 ci₀ hci₀
    have hyx : y = Core.iprjAddr A i := Core.keyOf_inj htwf (hy.symm.trans hk)
    rw [hyx] at hry
    obtain ⟨c', hc', hRd⟩ := hry
    have e : c' = memberProjection A i (.indc ind) :=
      Option.some.inj (hc'.symm.trans (hB.members i (.indc ind) hm))
    subst e
    have hinfo : (memberProjection A i (.indc ind)).info = .iPrj ⟨i.toUInt64, A⟩ := rfl
    rw [hinfo] at hRd
    obtain ⟨cb', ms', ind', -, ty₁, caps₁, -, hci₀eq⟩ := hRd
    subst hci₀eq
    have hnr : _ ∈ nonrecsOf blk := List.mem_filter.mpr ⟨hci₀, rfl⟩
    obtain ⟨k, hkget⟩ := List.getElem?_of_mem hnr
    obtain ⟨tyA, htyA⟩ := tys_of_nonrec hF hkget
    have hst := hN k _ tyA hkget htyA
    rw [hk] at hst
    have e2 := Option.some.inj (hf.symm.trans hst)
    injection e2 with h1 h2
    subst h1
    exact hT.ind k _ tyA hkget htyA i ind ty₀ hi hm hk hty
  · -- the constructors
    intro i ind j ct ty₀ cv nP nF hi hj hm hct hty hf
    have hjlt : j < ind.ctors.size := (Array.getElem?_eq_some_iff.mp hct).1
    have hx : FamAddr A cb rb crb (Core.cprjAddr A i j) :=
      Or.inl (Or.inr ⟨ms, i, .indc ind, hB.muts, hm, Or.inr ⟨ind, j, rfl, hjlt, rfl⟩⟩)
    obtain ⟨ci₀, hci₀, hk⟩ := hreads.2.2.1 _ hx
    obtain ⟨y, -, hy, hry⟩ := hreads.2.1 ci₀ hci₀
    have hyx : y = Core.cprjAddr A i j := Core.keyOf_inj htwf (hy.symm.trans hk)
    rw [hyx] at hry
    obtain ⟨c', hc', hRd⟩ := hry
    have e : c' = constructorProjection A i j :=
      Option.some.inj (hc'.symm.trans (hB.ctors i ind j hm hjlt))
    subst e
    have hinfo : (constructorProjection A i j).info = .cPrj ⟨i.toUInt64, j.toUInt64, A⟩ := rfl
    rw [hinfo] at hRd
    obtain ⟨cb', ms', ind', ct', -, -, -, -, -, -, -, -, ty₁, -, hci₀eq⟩ := hRd
    subst hci₀eq
    have hnr : _ ∈ nonrecsOf blk := List.mem_filter.mpr ⟨hci₀, rfl⟩
    obtain ⟨k, hkget⟩ := List.getElem?_of_mem hnr
    obtain ⟨tyA, htyA⟩ := tys_of_nonrec hF hkget
    have hst := hN k _ tyA hkget htyA
    rw [hk] at hst
    have e2 := Option.some.inj (hf.symm.trans hst)
    injection e2 with h1 h2 h3
    subst h1
    exact hT.ctor k _ tyA hkget htyA i ind j ct ty₀ hi hj hm hct hk hty
  · -- the recursors
    intro p rc cv mI rP rules₀ cv' mI' rP' rules' hpb hm hRR hf
    obtain ⟨pidx, pblk⟩ := p
    have hpb' : pblk = rb := hpb
    subst pblk
    have hx : FamAddr A cb rb crb (memberAddr rb pidx.toNat (.recr rc)) :=
      Or.inr (Or.inr ⟨rs, pidx.toNat, .recr rc, hrb.muts, hm, Or.inl rfl⟩)
    obtain ⟨ci₀, hci₀, hk⟩ := hreads.2.2.1 _ hx
    obtain ⟨y, -, hy, hry⟩ := hreads.2.1 ci₀ hci₀
    have hyx : y = memberAddr rb pidx.toNat (.recr rc) :=
      Core.keyOf_inj htwf (hy.symm.trans hk)
    rw [hyx] at hry
    have hP : recordOf E₀ (memberAddr rb pidx.toNat (.recr rc)) =
        some (memberProjection rb pidx.toNat (.recr rc)) := hrb.members pidx.toNat _ hm
    have hpi : (pidx.toNat).toUInt64 = pidx := UInt64.ofNat_toNat
    have hinfo : (memberProjection rb pidx.toNat (.recr rc)).info = .rPrj ⟨pidx, rb⟩ := by
      show Ixon.ConstantInfo.rPrj ⟨(pidx.toNat).toUInt64, rb⟩ = .rPrj ⟨pidx, rb⟩
      rw [hpi]
    obtain ⟨cb', rs', rc', hMA, hRR'⟩ := TwinFamily.reads_rprj hP hinfo hry
    obtain ⟨hcb', hrs', hmem', -, -, -⟩ := hMA
    have e1 : cb' = crb := Option.some.inj (hcb'.symm.trans hrb.record)
    rw [e1] at hrs' hRR'
    have e2 : rs' = rs := Ixon.ConstantInfo.muts.inj (hrs'.symm.trans hrb.muts)
    rw [e2] at hmem' hRR'
    have e3 : rc' = rc := Ixon.MutConst.recr.inj (Option.some.inj (hmem'.symm.trans hm))
    rw [e3] at hRR'
    -- the family's recursor is the reading the load is handed
    have eci : ci₀ = .recInfo cv mI rP rules₀ := RecReads.same hroles hRR' hRR
    subst eci
    have hcn : cv.name = keyOf t (memberAddr rb pidx.toNat (.recr rc)) := hk
    have hrr : _ ∈ recsOf blk := List.mem_filter.mpr ⟨hci₀, rfl⟩
    obtain ⟨k, hkget⟩ := List.getElem?_of_mem hrr
    obtain ⟨⟨tyA, htyA⟩, ⟨rhss, hrhss⟩⟩ := tys_of_rec hF hkget
    obtain ⟨rules'', hfind, hRS, hrhs⟩ := hR k cv mI rP rules₀ tyA rhss hkget htyA hrhss
    rw [hcn] at hfind
    have e4 := Option.some.inj (hf.symm.trans hfind)
    injection e4 with h1 h2 h3 h4
    subst h1 h4
    have hRRc : RecReads t (recordOf E₀) (fun x => E₀.blobs.get? x) crb (blockSelf t rb rs)
        cv.name rc (.recInfo cv mI rP rules₀) := by
      rw [hcn]
      exact hRR
    have hC := hT.recr k cv mI rP rules₀ tyA rhss hkget htyA hrhss ⟨pidx, rb⟩ rc rfl hm hcn hRRc
    obtain ⟨rls, hcR, hrr'⟩ := hC.rules
    exact
      { lvls := hC.lvls
        tyBounded := hC.tyBounded
        tyLevels := hC.tyLevels
        rulesScoped := hC.rulesScoped
        kOne := fun hk1 => absurd (hC.notK.symm.trans hk1) Bool.false_ne_true
        ty := hC.ty
        rules := ⟨rls, hcR,
          forall₂_meet (canonRules_fields hcR) hRS hrr' hrhs
            (fun c a b d hP' hQ' hR' hS' => ⟨hQ'.2.1.trans hP'.2.2.symm, hS'.trans hR'.symm⟩),
          fun rl rl'' hrl _ hk1 => by
            subst hrl
            have h1 := (canonRules_single hcR).1
            rw [h1, hC.notK] at hk1
            exact absurd hk1 Bool.false_ne_true⟩ }

end IxVM.Refinement.Typing.FamilyAlias
