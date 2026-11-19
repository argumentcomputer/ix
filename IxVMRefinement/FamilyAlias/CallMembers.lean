import IxVMRefinement.FamilyAlias.CallAdvice
import IxVMRefinement.FamilyAlias.CallTables
import IxVMRefinement.FamilyAlias.CallCells
import IxVMRefinement.FamilyAlias.Selected
import IxVMRefinement.Decl.FamilyMentions
import IxVMRefinement.StatementRel.LoadedReadsCanonRec
import IxVMRefinement.Assembly.BareState

/-! # Member validation against advice models (`members_val`, `member_val`)

`KernelModeled::check_family` validates every member of the block and of its family record
against its named advice model via three calls to `KernelModeled::members_val`:
* the block's inductive types against `src`;
* the block's constructors against `ctors ++ recs`;
* the family record's recursors against `recs`.

Each `KernelModeled::member_val` checks that the model is in `aset`, loads both constants with
`Ingress::get_ci`, extracts `(nl, ty)` via `ci_lvls_type`, asserts `expr_mentions_addrs(ty, later) = 0`,
renames `ty` along `(src, dst)`, and asserts `kexpr_struct_eq(rename(ty), mty) = 1`.

This module reads all three walks:
* `annotation_canon_gen_exact` / `annotation_canon_range_exact`: exact `TmCExact` forms of
  canonical annotation;
* `srcAddrs_nodup`: the block's types, constructors, and the family record's recursors have
  pairwise distinct addresses (from `FamBlockRecord` and `FamRecRecord`);
* `membersVal_walk`: walks any `members_val` observation into one `MemberValItem` per entry,
  yielding `AdvChecked`, `AdviceTypeWitness`, and `HeapExprScoped` on `ty`;
* `models_stored_defn`: at any `FamilyStepEnv`, every model address in `dst` resolves to a stored
  `.defnInfo`, enabling `noProjIn_of_renameAll_infer` on every renamed family term;
* `indMembers_of_walk` and `ctorMembers_of_walk`: produce the declared types and constructors,
  their canonical annotations (`FamilyTysCanon.{ind, ctor}`), their non-mention facts, `NoProjIn`,
  and `MemberFacts`;
* `recMemberVal_of_walk`: bridges `evRecsVal` to any recursor's canonical type, producing
  `NoProjIn`, non-mention of `recs`, and `MemberFacts`;
* `typesScopedB_of_blocks`: combines the three blockwise non-mention facts into `typesScopedB`. -/

universe u

namespace IxVM.Refinement.Typing.FamilyAlias

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Consistency
open IxVM (F)
open Ix.Kernel (ConstantInfo ConstantVal LevelParam ReducibilityHint)
open Ix.Kernel.Semantics (NativeFam)
open IxVM.Refinement.Decl.FamilyAlias (aliasMap MemberFacts MembersFacts typesScopedB)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Exact canonical annotations and level/mention helpers -/

/-- Exact `TmCExact` version of `LoadedReads.annotation_canon_gen`. -/
theorem annotation_canon_gen_exact {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ())
    {blob : _root_.Address → Option ByteArray} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    {recurAddrs : List _root_.Address} {ps : List LevelParam}
    {blobs : List (_root_.Address × ByteArray)} {h : Heap F} {e : Ixon.Expr}
    {kp : SourceValue F} {E_rd : KExpr} {root : F} {tree : L1.BinderTreeData}
    {plan : List Core.KLevel}
    (hperm : ps.Perm (List.range ps.length)) (hps : ps.length < 4294967296)
    (hselfk : ∀ i x m k, recurAddrs[i]? = some x → self i = some m → m = .ok k →
      k = Core.keyOf t x)
    (hagree : L1.BlobReadAgreement (readCtx t blob).blob blobs)
    (raw : L1.RawConvExpr src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h 4294967295 e kp)
    (built : L1.BinderTreeBuilt (L1.binderLeavesData src.binders.toList) tree)
    (planned : L1.binderRootPlan tree src.sharing.toList root e = some plan)
    (levels : L1.HeapBinderLevels h kp plan)
    (hread : (exprReader t blob src (Ix.Kernel.Reader.recParam ps) self).read e = .ok E_rd)
    (hlbb : E_rd.looseBVarsBounded 0 = true)
    (hdef : E_rd.allLevelParamsDefined ps = true) :
    ∃ E' : KExpr,
      LoadedReads.canonAnn src ps root e E_rd = some E' ∧ Annotates E' E_rd ∧
      Decl.TmCExact (Core.keyOf t) h (Core.posOf ps E') kp := by
  have hread' : (Ix.Kernel.Reader.MemberReader.mk' (readCtx t blob) src
      (Ix.Kernel.Reader.recParam ps) self).read e = .ok E_rd := hread
  obtain ⟨E', hann, htm, htrace⟩ :=
    raw.toTmCExactTrace_of_blobAgreement (κ := Core.keyOf t) (ps := ps) hperm hps
      (LoadedReads.readCtx_keyAt_inv ht blob) hselfk hagree hread' hlbb hdef
  have hap := htrace plan levels []
  rw [List.append_nil] at hap
  refine ⟨E', ?_, hann, htm⟩
  unfold LoadedReads.canonAnn
  rw [LoadedReads.canonTree_eq built, planned]
  show (L1.applyBinderTrace (fun level => Core.bmeta (L1.invPosLevel ps level))
    E_rd plan).map Prod.fst = some E'
  rw [hap]
  rfl

/-- `annotation_canon_gen_exact` at `List.range n` with identity level parameter map. -/
theorem annotation_canon_range_exact {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ())
    {blob : _root_.Address → Option ByteArray} {src : Ixon.Constant}
    {self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Key .anon))}
    {recurAddrs : List _root_.Address} {n : Nat}
    {blobs : List (_root_.Address × ByteArray)} {h : Heap F} {e : Ixon.Expr}
    {kp : SourceValue F} {E_rd : KExpr} {root : F} {tree : L1.BinderTreeData}
    {plan : List Core.KLevel}
    (hn : n < 4294967296)
    (hselfk : ∀ i x m k, recurAddrs[i]? = some x → self i = some m → m = .ok k →
      k = Core.keyOf t x)
    (hagree : L1.BlobReadAgreement (readCtx t blob).blob blobs)
    (raw : L1.RawConvExpr src.refs.toList recurAddrs src.univs.toList src.sharing.toList blobs
      h 4294967295 e kp)
    (built : L1.BinderTreeBuilt (L1.binderLeavesData src.binders.toList) tree)
    (planned : L1.binderRootPlan tree src.sharing.toList root e = some plan)
    (levels : L1.HeapBinderLevels h kp plan)
    (hread : (exprReader t blob src id self).read e = .ok E_rd)
    (hlbb : E_rd.looseBVarsBounded 0 = true)
    (hdef : E_rd.allLevelParamsDefined (List.range n) = true) :
    ∃ E' : KExpr,
      LoadedReads.canonAnn src (List.range n) root e E_rd = some E' ∧ Annotates E' E_rd ∧
      Decl.TmCExact (Core.keyOf t) h E' kp := by
  have hread' : (exprReader t blob src (Ix.Kernel.Reader.recParam (List.range n)) self).read e =
      .ok E_rd := by
    rw [Assembly.recParam_range]
    exact hread
  obtain ⟨E', hc, hann, htm⟩ :=
    annotation_canon_gen_exact ht (ps := List.range n) (by simp) (by simpa using hn)
      hselfk hagree raw built planned levels hread' hlbb hdef
  rw [Decl.posOf_range] at htm
  exact ⟨E', hc, hann, htm⟩

theorem allLevelParamsDefined_renameAll (g : KKey → KKey) (ps : List LevelParam) :
    ∀ e : KExpr, (Decl.renameAll g e).allLevelParamsDefined ps = e.allLevelParamsDefined ps
  | .bvar _ | .lit _ => rfl
  | .fvar _ ty => allLevelParamsDefined_renameAll g ps ty
  | .sort _ | .const _ _ => rfl
  | .app f a => by
    simp only [Decl.renameAll, Ix.Kernel.Expr.allLevelParamsDefined,
      allLevelParamsDefined_renameAll g ps f, allLevelParamsDefined_renameAll g ps a]
  | .lam t b _ | .forallE t b _ => by
    simp only [Decl.renameAll, Ix.Kernel.Expr.allLevelParamsDefined,
      allLevelParamsDefined_renameAll g ps t, allLevelParamsDefined_renameAll g ps b]
  | .letE t v b _ => by
    simp only [Decl.renameAll, Ix.Kernel.Expr.allLevelParamsDefined,
      allLevelParamsDefined_renameAll g ps t, allLevelParamsDefined_renameAll g ps v,
      allLevelParamsDefined_renameAll g ps b]
  | .proj _ _ e => allLevelParamsDefined_renameAll g ps e

theorem mentionsConst_instantiateLevelParams (ks : List LevelParam) (us : List Core.KLevel)
    (k : KKey) :
    ∀ e : KExpr, (e.instantiateLevelParams ks us).mentionsConst k = e.mentionsConst k
  | .bvar _ | .sort _ | .lit _ => rfl
  | .fvar _ ty => mentionsConst_instantiateLevelParams ks us k ty
  | .const _ _ => rfl
  | .app f a => by
    simp only [Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Expr.mentionsConst,
      mentionsConst_instantiateLevelParams ks us k f,
      mentionsConst_instantiateLevelParams ks us k a]
  | .lam t b _ | .forallE t b _ => by
    simp only [Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Expr.mentionsConst,
      mentionsConst_instantiateLevelParams ks us k t,
      mentionsConst_instantiateLevelParams ks us k b]
  | .letE t v b _ => by
    simp only [Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Expr.mentionsConst,
      mentionsConst_instantiateLevelParams ks us k t,
      mentionsConst_instantiateLevelParams ks us k v,
      mentionsConst_instantiateLevelParams ks us k b]
  | .proj _ _ e => by
    simp only [Ix.Kernel.Expr.instantiateLevelParams, Ix.Kernel.Expr.mentionsConst,
      mentionsConst_instantiateLevelParams ks us k e]

theorem tmExact_hasFvar_false {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {h : Heap F}
    {k : Nat} {E : KExpr} {p : SourceValue F}
    (rep : Decl.TmExact κ 0 Γ h k E p) : E.hasFvar = false := by
  induction rep with
  | bvarLocal _ _ _ => rfl
  | bvarFree _ _ _ hd => exact absurd hd (Nat.not_lt_zero _)
  | sort _ _ => rfl
  | const _ _ _ => rfl
  | app _ _ _ ihf iha => simp [Ix.Kernel.Expr.hasFvar, ihf, iha]
  | lam _ _ _ _ iht ihb => simp [Ix.Kernel.Expr.hasFvar, iht, ihb]
  | forallE _ _ _ _ iht ihb => simp [Ix.Kernel.Expr.hasFvar, iht, ihb]
  | letE _ _ _ _ iht ihv ihb => simp [Ix.Kernel.Expr.hasFvar, iht, ihv, ihb]
  | litNat _ _ _ => rfl
  | litStr _ _ _ => rfl
  | proj _ _ _ ihe => simp [Ix.Kernel.Expr.hasFvar, ihe]

theorem aliasMap_zip_getElem :
    ∀ {ks ds : List KKey}, ks.Nodup → (hlen : ks.length = ds.length) →
      ∀ (i : Nat) (hi : i < ks.length),
        aliasMap (ks.zip ds) ks[i] = ds[i]'(hlen ▸ hi)
  | [], [], _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | k :: ks, d :: ds, hnd, hlen, 0, _ => by
    simp [aliasMap]
  | k :: ks, d :: ds, hnd, hlen, i + 1, hi => by
    obtain ⟨hk_not, hnd'⟩ := List.nodup_cons.mp hnd
    have hi' : i < ks.length := Nat.lt_of_succ_lt_succ hi
    have hne : ks[i]'hi' ≠ k := fun heq => hk_not (heq ▸ List.getElem_mem hi')
    simp only [List.zip_cons_cons, aliasMap, List.getElem_cons_succ, hne, ↓reduceIte]
    exact aliasMap_zip_getElem hnd' (Nat.succ.inj hlen) i hi'

theorem aliasMap_out_of_zip {ks ds : List KKey} {k : KKey} (hnot : ks.contains k = false) :
    aliasMap (ks.zip ds) k = k := by
  rw [← renameKeyList_eq_aliasMap]
  exact Decl.renameKeyList_out k ks ds hnot

/-- `typesScopedB` assembled from the three blockwise non-mention invariants:
types mention nothing in `tKs ++ cKs ++ rKs`, constructors mention nothing in `cKs ++ rKs`,
and recursors mention nothing in `rKs`. -/
theorem typesScopedB_of_blocks {tKs cKs rKs : List KKey} {tTys cTys rTys : List KExpr}
    (htLen : tKs.length = tTys.length) (hcLen : cKs.length = cTys.length)
    (hrLen : rKs.length = rTys.length)
    (htMent : ∀ ty ∈ tTys, ∀ k ∈ tKs ++ (cKs ++ rKs), ty.mentionsConst k = false)
    (hcMent : ∀ ty ∈ cTys, ∀ k ∈ cKs ++ rKs, ty.mentionsConst k = false)
    (hrMent : ∀ ty ∈ rTys, ∀ k ∈ rKs, ty.mentionsConst k = false) :
    typesScopedB (tKs ++ (cKs ++ rKs)) (tTys ++ (cTys ++ rTys)) = true := by
  have go : ∀ (ns : List KKey) (ts : List KExpr) (suf : List KKey),
      ns.length = ts.length →
      (∀ ty ∈ ts, ∀ k ∈ ns ++ suf, ty.mentionsConst k = false) →
      ∀ (tail : List KExpr), typesScopedB suf tail = true →
      typesScopedB (ns ++ suf) (ts ++ tail) = true := by
    intro ns
    induction ns with
    | nil =>
      intro ts suf hlen _ tail htail
      cases ts with
      | nil => exact htail
      | cons _ _ => cases hlen
    | cons n ns ih =>
      intro ts suf hlen hment tail htail
      cases ts with
      | nil => cases hlen
      | cons ty ts =>
        simp only [List.cons_append, typesScopedB, Bool.and_eq_true, List.all_eq_true,
          Bool.not_eq_true']
        refine ⟨fun k hk => hment ty List.mem_cons_self k hk, ?_⟩
        exact ih ts suf (Nat.succ.inj hlen)
          (fun ty' hty' k hk => hment ty' (List.mem_cons_of_mem _ hty') k (List.mem_cons_of_mem _ hk))
          tail htail
  have hR : typesScopedB rKs rTys = true := by
    simpa only [List.append_nil] using go rKs rTys [] hrLen
      (by simpa only [List.append_nil] using hrMent) [] rfl
  have hCR : typesScopedB (cKs ++ rKs) (cTys ++ rTys) = true :=
    go cKs cTys rKs hcLen hcMent rTys hR
  exact go tKs tTys (cKs ++ rKs) htLen htMent (cTys ++ rTys) hCR

/-! ## Address distinctness of `src` -/

/-- Constructor slot descriptor matching `ctorAddrsFrom B ms p` element by element. -/
def ctorSlotsFrom : List Ixon.MutConst → Nat → List (Nat × Ixon.Inductive × Nat × Ixon.Constructor)
  | [], _ => []
  | .indc ind :: rest, p =>
    (ind.ctors.toList.mapIdx fun j ct => (p, ind, j, ct)) ++ ctorSlotsFrom rest (p + 1)
  | _ :: rest, p => ctorSlotsFrom rest (p + 1)

theorem ctorSlotsFrom_addrs (B : _root_.Address) :
    ∀ (ms : List Ixon.MutConst) (p : Nat),
      (ctorSlotsFrom ms p).map (fun s => cprjAddr B s.1 s.2.2.1) = ctorAddrsFrom B ms p
  | [], _ => rfl
  | .indc ind :: rest, p => by
    simp only [ctorSlotsFrom, ctorAddrsFrom, List.map_append, ctorSlotsFrom_addrs B rest (p + 1)]
    congr 1
    apply List.ext_getElem (by simp)
    intro j hj1 hj2
    simp
  | .defn _ :: rest, p => ctorSlotsFrom_addrs B rest (p + 1)
  | .recr _ :: rest, p => ctorSlotsFrom_addrs B rest (p + 1)

theorem ctorSlotsFrom_get {ms : List Ixon.MutConst} :
    ∀ (p : Nat) {s : Nat × Ixon.Inductive × Nat × Ixon.Constructor},
      s ∈ ctorSlotsFrom ms p →
      ∃ k, s.1 = p + k ∧ ms[k]? = some (.indc s.2.1) ∧ s.2.1.ctors[s.2.2.1]? = some s.2.2.2 := by
  induction ms with
  | nil => intro p s hs; cases hs
  | cons m rest ih =>
    intro p s hs
    cases m with
    | indc ind =>
      simp only [ctorSlotsFrom, List.mem_append] at hs
      rcases hs with h1 | h2
      · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp h1
        rw [List.getElem?_mapIdx] at hj
        cases hct : ind.ctors.toList[j]? with
        | none => rw [hct] at hj; cases hj
        | some ct =>
          rw [hct] at hj
          simp only [Option.map_some, Option.some.injEq] at hj
          subst hj
          exact ⟨0, by omega, rfl, by rwa [← Array.getElem?_toList]⟩
      · obtain ⟨k, hk1, hmk, hct⟩ := ih (p + 1) h2
        exact ⟨k + 1, by omega, by simpa using hmk, hct⟩
    | defn _ | recr _ =>
      simp only [ctorSlotsFrom] at hs
      obtain ⟨k, hk1, hmk, hct⟩ := ih (p + 1) hs
      exact ⟨k + 1, by omega, by simpa using hmk, hct⟩

theorem ctorSlotsFrom_nodup :
    ∀ (ms : List Ixon.MutConst) (p : Nat),
      ((ctorSlotsFrom ms p).map fun s => (s.1, s.2.2.1)).Nodup
  | [], _ => List.nodup_nil
  | .indc ind :: rest, p => by
    simp only [ctorSlotsFrom, List.map_append]
    rw [List.nodup_append]
    refine ⟨?_, ctorSlotsFrom_nodup rest (p + 1), ?_⟩
    · have hmap : ((ind.ctors.toList.mapIdx fun j ct => (p, ind, j, ct)).map
          fun s => (s.1, s.2.2.1)) = (List.range ind.ctors.size).map (fun j => (p, j)) := by
        apply List.ext_getElem (by simp)
        intro j hj1 hj2
        simp
      rw [hmap]
      exact List.nodup_range.map (fun _ _ h => (Prod.mk.inj h).2)
    · intro a ha b hb heq
      obtain ⟨s1, hs1, rfl⟩ := List.mem_map.mp ha
      obtain ⟨s2, hs2, rfl⟩ := List.mem_map.mp hb
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hs1
      rw [List.getElem?_mapIdx] at hj
      cases hct : ind.ctors.toList[j]? with
      | none => rw [hct] at hj; cases hj
      | some ct =>
        rw [hct] at hj
        simp only [Option.map_some, Option.some.injEq] at hj
        subst hj
        obtain ⟨k, hk, -, -⟩ := ctorSlotsFrom_get (p + 1) hs2
        have h1 := (Prod.mk.inj heq).1
        omega
  | .defn _ :: rest, p => ctorSlotsFrom_nodup rest (p + 1)
  | .recr _ :: rest, p => ctorSlotsFrom_nodup rest (p + 1)

private theorem toNat_toUInt64_lt {n : Nat} (hn : n < UInt64.size) : n.toUInt64.toNat = n := by
  change (UInt64.ofNat n).toNat = n
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt hn

/-- **Every address in `src = typeAs ++ (ctorAs ++ recAs)` is distinct** (using only `recordOf E₀`,
which maps types to `.iPrj`, constructors to `.cPrj`, and recursors to `.rPrj` with distinct
indices). -/
theorem srcAddrs_nodup {E₀ : Ixon.Env} {B rb : _root_.Address} {cb crb : Ixon.Constant}
    {ms rs : Array Ixon.MutConst}
    (hB : FamBlockRecord E₀ B cb ms) (hR : FamRecRecord E₀ rb crb rs)
    (hms_lt : ms.size < UInt64.size)
    (hct_lt : ∀ ind, Ixon.MutConst.indc ind ∈ ms.toList → ind.ctors.size < UInt64.size)
    (hrs_lt : rs.size < UInt64.size)
    {h : Heap F} {typeAs ctorAs recAs typeMs ctorMs recMs : List Bytes.Address}
    {xtA xcA xrA xtM xcM xrM xsrc xdst : SourceValue F}
    (T : FamilyTables B rb ms rs h typeAs ctorAs recAs typeMs ctorMs recMs xtA xcA xrA xtM xcM
      xrM xsrc xdst) :
    ((typeAs ++ (ctorAs ++ recAs)).map ixAddr).Nodup := by
  have hT_rec : ∀ x ∈ typeAs.map ixAddr, ∃ (i : Nat) (hi : i < ms.size),
      recordOf E₀ x = some (memberProjection B i ms[i]) ∧
      ∃ ind, ms[i]? = some (.indc ind) := by
    intro x hx
    rw [T.types] at hx
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
    rw [List.getElem?_mapIdx] at hi
    cases hm : ms.toList[i]? with
    | none => rw [hm] at hi; cases hi
    | some m =>
      rw [hm] at hi
      simp only [Option.map_some, Option.some.injEq] at hi
      subst hi
      have hiLt : i < ms.size := by
        have := (List.getElem?_eq_some_iff.mp hm).1
        simpa using this
      have hmA : ms[i]? = some m := by rwa [← Array.getElem?_toList]
      obtain ⟨ind, rfl⟩ := hB.indcs m (List.mem_of_getElem? hm)
      refine ⟨i, hiLt, ?_, ind, hmA⟩
      have hget : ms[i] = .indc ind := by
        rw [Array.getElem?_eq_getElem hiLt] at hmA
        exact Option.some.inj hmA
      rw [hget, ← LoadedReads.memberAddr_eq_projAddr]
      exact hB.members i (.indc ind) hmA
  have hC_rec : ∀ x ∈ ctorAs.map ixAddr, ∃ i ind j,
      i < ms.size ∧ ms[i]? = some (.indc ind) ∧ j < ind.ctors.size ∧
      recordOf E₀ x = some (constructorProjection B i j) := by
    intro x hx
    rw [T.ctors, ← ctorSlotsFrom_addrs B ms.toList 0] at hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
    obtain ⟨k, hk, hmk, hct⟩ := ctorSlotsFrom_get 0 hs
    rw [Nat.zero_add] at hk
    have hmkA : ms[k]? = some (.indc s.2.1) := by rwa [← Array.getElem?_toList]
    have hiLt : k < ms.size := (Array.getElem?_eq_some_iff.mp hmkA).1
    have hjLt : s.2.2.1 < s.2.1.ctors.size := (Array.getElem?_eq_some_iff.mp hct).1
    exact ⟨k, s.2.1, s.2.2.1, hiLt, hmkA, hjLt, by
      rw [hk, ← LoadedReads.ctorAddr_eq_cprjAddr]; exact hB.ctors k s.2.1 s.2.2.1 hmkA hjLt⟩
  have hR_rec : ∀ x ∈ recAs.map ixAddr, ∃ (k : Nat) (hk : k < rs.size),
      recordOf E₀ x = some (memberProjection rb k rs[k]) ∧
      ∃ r, rs[k]? = some (.recr r) := by
    intro x hx
    rw [T.recs] at hx
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hx
    rw [List.getElem?_mapIdx] at hk
    cases hm : rs.toList[k]? with
    | none => rw [hm] at hk; cases hk
    | some m =>
      rw [hm] at hk
      simp only [Option.map_some, Option.some.injEq] at hk
      subst hk
      have hkLt : k < rs.size := by
        have := (List.getElem?_eq_some_iff.mp hm).1
        simpa using this
      have hmA : rs[k]? = some m := by rwa [← Array.getElem?_toList]
      obtain ⟨r, rfl⟩ := hR.recrs m (List.mem_of_getElem? hm)
      refine ⟨k, hkLt, ?_, r, hmA⟩
      have hget : rs[k] = .recr r := by
        rw [Array.getElem?_eq_getElem hkLt] at hmA
        exact Option.some.inj hmA
      rw [hget, ← LoadedReads.memberAddr_eq_projAddr]
      exact hR.members k (.recr r) hmA
  have hndT : (typeAs.map ixAddr).Nodup := by
    rw [T.types]
    rw [List.nodup_iff_injective_getElem]
    intro ⟨i, hi⟩ ⟨j, hj⟩ heq
    apply Fin.ext
    simp only [List.length_mapIdx, Array.length_toList] at hi hj
    simp only [List.getElem_mapIdx, Array.getElem_toList] at heq
    have hm_i : ms[i]? = some ms[i] := Array.getElem?_eq_getElem hi
    have hm_j : ms[j]? = some ms[j] := Array.getElem?_eq_getElem hj
    obtain ⟨ind1, h1⟩ := hB.indcs ms[i] (Array.mem_toList_iff.mpr (Array.getElem_mem hi))
    obtain ⟨ind2, h2⟩ := hB.indcs ms[j] (Array.mem_toList_iff.mpr (Array.getElem_mem hj))
    have hr1 := hB.members i ms[i] hm_i
    have hr2 := hB.members j ms[j] hm_j
    rw [LoadedReads.memberAddr_eq_projAddr] at hr1 hr2
    rw [heq] at hr1
    have hpeq := Option.some.inj (hr1.symm.trans hr2)
    rw [h1, h2] at hpeq
    simp only [memberProjection, Ixon.Constant.mk.injEq, Ixon.ConstantInfo.iPrj.injEq,
      Ixon.InductiveProj.mk.injEq] at hpeq
    have hnat := congrArg UInt64.toNat hpeq.1.1
    rwa [toNat_toUInt64_lt (by omega), toNat_toUInt64_lt (by omega)] at hnat
  have hndC : (ctorAs.map ixAddr).Nodup := by
    rw [T.ctors, ← ctorSlotsFrom_addrs B ms.toList 0]
    have hndS := ctorSlotsFrom_nodup ms.toList 0
    rw [List.nodup_iff_injective_getElem] at hndS ⊢
    intro ⟨a, ha⟩ ⟨b, hb⟩ heq
    apply Fin.ext
    simp only [List.length_map] at ha hb
    simp only [List.getElem_map] at heq
    let s1 := (ctorSlotsFrom ms.toList 0)[a]
    let s2 := (ctorSlotsFrom ms.toList 0)[b]
    obtain ⟨k1, hk1, hm1, hct1⟩ := ctorSlotsFrom_get 0 (List.getElem_mem ha)
    obtain ⟨k2, hk2, hm2, hct2⟩ := ctorSlotsFrom_get 0 (List.getElem_mem hb)
    rw [Nat.zero_add] at hk1 hk2
    have hm1A : ms[s1.1]? = some (.indc s1.2.1) := by rw [hk1, ← Array.getElem?_toList]; exact hm1
    have hm2A : ms[s2.1]? = some (.indc s2.2.1) := by rw [hk2, ← Array.getElem?_toList]; exact hm2
    have hi1 : s1.1 < ms.size := (Array.getElem?_eq_some_iff.mp hm1A).1
    have hi2 : s2.1 < ms.size := (Array.getElem?_eq_some_iff.mp hm2A).1
    have hj1 : s1.2.2.1 < s1.2.1.ctors.size := (Array.getElem?_eq_some_iff.mp hct1).1
    have hj2 : s2.2.2.1 < s2.2.1.ctors.size := (Array.getElem?_eq_some_iff.mp hct2).1
    have hcj1 : s1.2.1.ctors.size < UInt64.size := hct_lt s1.2.1 (List.mem_of_getElem? hm1)
    have hcj2 : s2.2.1.ctors.size < UInt64.size := hct_lt s2.2.1 (List.mem_of_getElem? hm2)
    have hr1 := hB.ctors s1.1 s1.2.1 s1.2.2.1 hm1A hj1
    have hr2 := hB.ctors s2.1 s2.2.1 s2.2.2.1 hm2A hj2
    rw [LoadedReads.ctorAddr_eq_cprjAddr] at hr1 hr2
    have heq' : cprjAddr B s1.1 s1.2.2.1 = cprjAddr B s2.1 s2.2.2.1 := heq
    rw [heq'] at hr1
    have hpeq := Option.some.inj (hr1.symm.trans hr2)
    simp only [constructorProjection, Ixon.Constant.mk.injEq, Ixon.ConstantInfo.cPrj.injEq,
      Ixon.ConstructorProj.mk.injEq] at hpeq
    have hni := congrArg UInt64.toNat hpeq.1.1
    have hnj := congrArg UInt64.toNat hpeq.1.2.1
    rw [toNat_toUInt64_lt (by omega), toNat_toUInt64_lt (by omega)] at hni
    rw [toNat_toUInt64_lt (by omega), toNat_toUInt64_lt (by omega)] at hnj
    have hfeq := hndS (a₁ := ⟨a, by simp [ha]⟩) (a₂ := ⟨b, by simp [hb]⟩) (by
      simp only [List.getElem_map]
      exact Prod.ext hni hnj)
    exact Fin.mk.inj hfeq
  have hndR : (recAs.map ixAddr).Nodup := by
    rw [T.recs]
    rw [List.nodup_iff_injective_getElem]
    intro ⟨i, hi⟩ ⟨j, hj⟩ heq
    apply Fin.ext
    simp only [List.length_mapIdx, Array.length_toList] at hi hj
    simp only [List.getElem_mapIdx, Array.getElem_toList] at heq
    have hm_i : rs[i]? = some rs[i] := Array.getElem?_eq_getElem hi
    have hm_j : rs[j]? = some rs[j] := Array.getElem?_eq_getElem hj
    obtain ⟨r1, h1⟩ := hR.recrs rs[i] (Array.mem_toList_iff.mpr (Array.getElem_mem hi))
    obtain ⟨r2, h2⟩ := hR.recrs rs[j] (Array.mem_toList_iff.mpr (Array.getElem_mem hj))
    have hr1 := hR.members i rs[i] hm_i
    have hr2 := hR.members j rs[j] hm_j
    rw [LoadedReads.memberAddr_eq_projAddr] at hr1 hr2
    rw [heq] at hr1
    have hpeq := Option.some.inj (hr1.symm.trans hr2)
    rw [h1, h2] at hpeq
    simp only [memberProjection, Ixon.Constant.mk.injEq, Ixon.ConstantInfo.rPrj.injEq,
      Ixon.RecursorProj.mk.injEq] at hpeq
    have hnat := congrArg UInt64.toNat hpeq.1.1
    rwa [toNat_toUInt64_lt (by omega), toNat_toUInt64_lt (by omega)] at hnat
  simp only [List.map_append]
  rw [List.nodup_append, List.nodup_append]
  refine ⟨hndT, ⟨hndC, hndR, ?_⟩, ?_⟩
  · intro x hx y hy heq
    subst heq
    obtain ⟨i, ind, j, -, -, -, hrc⟩ := hC_rec x hx
    obtain ⟨k, hk, hrr, r, hmr⟩ := hR_rec x hy
    have hget : rs[k] = .recr r := by
      rw [Array.getElem?_eq_getElem hk] at hmr; exact Option.some.inj hmr
    rw [hget] at hrr
    have hpeq := Option.some.inj (hrc.symm.trans hrr)
    simp [constructorProjection, memberProjection] at hpeq
  · intro x hx y hy heq
    subst heq
    obtain ⟨i, hi, hrt, ind, hmi⟩ := hT_rec x hx
    have hget : ms[i] = .indc ind := by
      rw [Array.getElem?_eq_getElem hi] at hmi; exact Option.some.inj hmi
    rw [hget] at hrt
    rcases List.mem_append.mp hy with hyC | hyR
    · obtain ⟨i', ind', j', -, -, -, hrc⟩ := hC_rec x hyC
      have hpeq := Option.some.inj (hrt.symm.trans hrc)
      simp [memberProjection, constructorProjection] at hpeq
    · obtain ⟨k, hk, hrr, r, hmr⟩ := hR_rec x hyR
      have hgetR : rs[k] = .recr r := by
        rw [Array.getElem?_eq_getElem hk] at hmr; exact Option.some.inj hmr
      rw [hgetR] at hrr
      have hpeq := Option.some.inj (hrt.symm.trans hrr)
      simp [memberProjection] at hpeq

/-! ## Walking `members_val` into per-entry `MemberValItem` witnesses -/

/-- **Raw `ci_lvls_type` extraction**: for `Induct`, `Ctor`, or `Rec`, `ci_lvls_type` returns the
first two fields `(nl, ty)` without modifying the heap. -/
theorem ci_lvls_type_raw {v_ci nl ty : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W "KernelModeled::ci_lvls_type" [v_ci] h (.tuple [nl, ty]) h' cs) :
    h' = h ∧
    ∀ tag f0 f1 rest,
      v_ci = .construct kciEnum tag (f0 :: f1 :: rest) →
      nl = f0 ∧ ty = f1 := by
  cases Obs.«KernelModeled::ci_lvls_type».obs ev with
  | Induct x_nl x_ty _ _ _ _ _ _ hv he hh _ =>
    injection he with hl; injection hl with h1 hl; injection hl with h2 _; subst h1 h2 hh
    refine ⟨rfl, fun tag f0 f1 rest hvc => ?_⟩
    rw [hv] at hvc; injection hvc with _ _ ha; injection ha with hf0 ha; injection ha with hf1 _
    exact ⟨hf0, hf1⟩
  | Ctor x_nl x_ty _ _ _ _ _ _ _ hv he hh _ =>
    injection he with hl; injection hl with h1 hl; injection hl with h2 _; subst h1 h2 hh
    refine ⟨rfl, fun tag f0 f1 rest hvc => ?_⟩
    rw [hv] at hvc; injection hvc with _ _ ha; injection ha with hf0 ha; injection ha with hf1 _
    exact ⟨hf0, hf1⟩
  | Rec x_nl x_ty _ _ _ _ _ _ _ _ _ _ _ hv he hh _ =>
    injection he with hl; injection hl with h1 hl; injection hl with h2 _; subst h1 h2 hh
    refine ⟨rfl, fun tag f0 f1 rest hvc => ?_⟩
    rw [hv] at hvc; injection hvc with _ _ ha; injection ha with hf0 ha; injection ha with hf1 _
    exact ⟨hf0, hf1⟩

/-- **Everything one `KernelModeled::member_val` iteration establishes for a pair `(aM, aMd)`**:
the model `aMd` is a checked safe definition with `AdviceTypeWitness` `W`, `mty` is well-scoped
and pulls back to `HeapExprScoped` on `ty`, and every sub-call is heap-chained in `calls`. -/
structure MemberValItem (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (lim : Option Nat) (csFam : List (Call F))
    (advAs srcAs dstAs laterAs : List Bytes.Address) (aM aMd : Bytes.Address) where
  hStart : Heap F
  hEnd : Heap F
  xM : SourceValue F
  xMd : SourceValue F
  xSrc : SourceValue F
  xDst : SourceValue F
  xAset : SourceValue F
  xLater : SourceValue F
  haM : Bytes.RepAddressRef addrTy hStart aM xM
  haMd : Bytes.RepAddressRef addrTy hStart aMd xMd
  hsrcRep : RepList addrListEnum (Bytes.RepAddressRef addrTy) hStart srcAs xSrc
  hdstRep : RepList addrListEnum (Bytes.RepAddressRef addrTy) hStart dstAs xDst
  hlaterRep : RepList addrListEnum (Bytes.RepAddressRef addrTy) hStart laterAs xLater
  chain : MemberValChain xM xMd xSrc xDst xAset xLater hStart hEnd calls
  hAdv : AdvChecked calls bAddr t lim csFam advAs aMd
  cm : Ixon.Constant
  dm : Ixon.Definition
  hrecM : recordOf E₀ (ixAddr aMd) = some cm
  hinfoM : cm.info = .defn dm
  hkindM : dm.kind = .defn
  hlogM : InLogic cm
  hcaM : ConstAddrOf (ixAddr aMd) cm (ixAddr aMd)
  hchkM : Claim.CheckedLimAt calls bAddr t (ixAddr aMd) lim
  ty' : KExpr
  W : AdviceTypeWitness calls t lim aMd dm.lvls.toNat chain.m101 chain.nl chain.mty ty'
  htyScoped : HeapExprScoped hEnd dm.lvls.toNat 0 chain.ty

theorem MemberValItem.ext_m15_m101 {calls bAddr t E₀ lim csFam advAs srcAs dstAs laterAs aM aMd}
    (I : MemberValItem calls bAddr t E₀ lim csFam advAs srcAs dstAs laterAs aM aMd) :
    Heap.Extends I.chain.m15 I.chain.m101 :=
  I.chain.evGetM.extends.trans (I.chain.evLvlsTy.extends.trans
    (I.chain.evNoMent.extends.trans I.chain.evGetMd.extends))

theorem MemberValItem.ext_m65_m101 {calls bAddr t E₀ lim csFam advAs srcAs dstAs laterAs aM aMd}
    (I : MemberValItem calls bAddr t E₀ lim csFam advAs srcAs dstAs laterAs aM aMd) :
    Heap.Extends I.chain.m65 I.chain.m101 :=
  I.chain.evLvlsTy.extends.trans (I.chain.evNoMent.extends.trans I.chain.evGetMd.extends)

theorem MemberValItem.ext_start_m101 {calls bAddr t E₀ lim csFam advAs srcAs dstAs laterAs aM aMd}
    (I : MemberValItem calls bAddr t E₀ lim csFam advAs srcAs dstAs laterAs aM aMd) :
    Heap.Extends I.hStart I.chain.m101 :=
  I.chain.evInAset.extends.trans I.ext_m15_m101

/-- **Build one `MemberValItem` from an observed `member_val` call.** -/
theorem memberVal_item {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {lim : Option Nat} {csFam : List (Call F)}
    (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {advAs srcAs dstAs laterAs : List Bytes.Address} {aM aMd : Bytes.Address}
    {xM xMd xSrc xDst xAset xLater r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hsub : CallSub cs calls)
    (haM : Bytes.RepAddressRef addrTy h aM xM)
    (haMd : Bytes.RepAddressRef addrTy h aMd xMd)
    (hsrcRep : RepList addrListEnum (Bytes.RepAddressRef addrTy) h srcAs xSrc)
    (hdstRep : RepList addrListEnum (Bytes.RepAddressRef addrTy) h dstAs xDst)
    (haset : AddrMapAll addrMapEnum (fun _ k _ => AdvChecked calls bAddr t lim csFam advAs k) h xAset)
    (hlaterRep : RepList addrListEnum (Bytes.RepAddressRef addrTy) h laterAs xLater)
    (ev : ObsFn Obs.W "KernelModeled::member_val" [xM, xMd, xSrc, xDst, xAset, xLater] h r h' cs) :
    Nonempty (MemberValItem calls bAddr t E₀ lim csFam advAs srcAs dstAs laterAs aM aMd) := by
  have htwf : t.wf = true := by unfold Ix.Kernel.RoleTable.wf; rw [ht]; rfl
  obtain ⟨C⟩ := memberVal_chain ev
  let sc0 : ScopedCtx := ScopedCtx.unrestricted ⟨E₀, .empty, t, lim⟩
  have hAdv : AdvChecked calls bAddr t lim csFam advAs aMd :=
    Decl.addr_set_member_one_scoped (c := sc0) htwf haMd haset C.evInAset.obs
  have extStart_mMent : Heap.Extends h C.mMent :=
    C.evInAset.extends.trans (C.evGetM.extends.trans (C.evLvlsTy.extends.trans C.evNoMent.extends))
  have haMd_mMent : Bytes.RepAddressRef addrTy C.mMent aMd xMd :=
    Bytes.repAddressRef_heapMono₂ addrTy extStart_mMent haMd
  have hsubMd : CallSub C.evGetMd.cs calls := fun cl hcl => hsub cl (C.evGetMd.sub cl hcl)
  obtain ⟨cm, dm, hrecM, hinfoM, hkindM, -, hlogM, hcaM, hchkM⟩ :=
    advice_defn_record hbd hS hH hAdv haMd_mMent C.evGetMd.obs hsubMd (Or.inl rfl) C.ldMd
  obtain ⟨ty', ⟨W⟩⟩ :=
    advice_checked_type ht hbd hS hrecM hinfoM (Or.inl (hkindM rfl)) hlogM hchkM
      haMd_mMent C.evGetMd.obs hsubMd (Or.inl ⟨C.w1, C.w2, C.w3, C.ldMd⟩)
  have hrenScoped : HeapExprScoped h' dm.lvls.toNat 0 C.ren :=
    heapExprScoped_of_kexpr_struct_eq (W.mty_scoped.mono C.evRen.extends) C.evEq.obs
  have htyScoped : HeapExprScoped h' dm.lvls.toNat 0 C.ty :=
    heapExprScoped_of_rename C.evRen.obs C.evEq.extends hrenScoped
  have hsubAll : CallSub cs calls := hsub
  exact ⟨{
    hStart := h
    hEnd := h'
    xM, xMd, xSrc, xDst, xAset, xLater
    haM, haMd, hsrcRep, hdstRep, hlaterRep
    chain := {
      m15 := C.m15, evInAset := C.evInAset.mono hsubAll
      p := C.p, ci := C.ci, m65 := C.m65, evGetM := C.evGetM.mono hsubAll
      ldM := C.ldM
      nl := C.nl, ty := C.ty, m50 := C.m50, evLvlsTy := C.evLvlsTy.mono hsubAll
      mMent := C.mMent, evNoMent := C.evNoMent.mono hsubAll
      pm := C.pm, mty := C.mty, w1 := C.w1, w2 := C.w2, w3 := C.w3, m101 := C.m101
      evGetMd := C.evGetMd.mono hsubAll
      ldMd := C.ldMd
      ren := C.ren, m216 := C.m216, evRen := C.evRen.mono hsubAll
      evEq := C.evEq.mono hsubAll }
    hAdv, cm, dm, hrecM, hinfoM, hkindM := hkindM rfl, hlogM, hcaM, hchkM, ty', W, htyScoped }⟩

/-- **Walk an observed `KernelModeled::members_val` call** over parallel `(msAs, mdAs)` into a
pointwise `MemberValItem` for every index `idx < msAs.length`. -/
theorem membersVal_walk {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {lim : Option Nat} {csFam : List (Call F)}
    (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀) (hH : LoadedReads.HashedRecordsStored calls E₀)
    {advAs srcAs dstAs laterAs : List Bytes.Address} :
    ∀ (msAs mdAs : List Bytes.Address)
      {xMs xMds xSrc xDst xAset xLater r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      (hlen : msAs.length = mdAs.length) →
      CallSub cs calls →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h msAs xMs →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h mdAs xMds →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h srcAs xSrc →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h dstAs xDst →
      AddrMapAll addrMapEnum (fun _ k _ => AdvChecked calls bAddr t lim csFam advAs k) h xAset →
      RepList addrListEnum (Bytes.RepAddressRef addrTy) h laterAs xLater →
      ObsFn Obs.W "KernelModeled::members_val" [xMs, xMds, xSrc, xDst, xAset, xLater] h r h' cs →
      ∀ (idx : Nat) (hidx : idx < msAs.length),
        Nonempty (MemberValItem calls bAddr t E₀ lim csFam advAs srcAs dstAs laterAs
          msAs[idx] (mdAs[idx]'(hlen ▸ hidx)))
  | [], [], _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hidx =>
    absurd hidx (Nat.not_lt_zero _)
  | [], _ :: _, _, _, _, _, _, _, _, _, _, _, hlen, _, _, _, _, _, _, _, _, _, _ => by cases hlen
  | _ :: _, [], _, _, _, _, _, _, _, _, _, _, hlen, _, _, _, _, _, _, _, _, _, _ => by cases hlen
  | aM :: msRest, aMd :: mdRest, xMs, xMds, xSrc, xDst, xAset, xLater, r, h, h', cs,
      hlen, hsub, hms, hmds, hsrc, hdst, haset, hlater, ev, idx, hidx => by
    rcases membersVal_step ev with ⟨ldNil, -⟩ | ⟨⟨C⟩⟩
    · exact absurd (Lib.rep_nil_of_load hms ldNil) (List.cons_ne_nil _ _)
    · obtain ⟨aM', msRest', he1, haM, hmsRest⟩ := Lib.rep_cons_of_load hms C.ldMembers
      obtain ⟨aMd', mdRest', he2, haMd, hmdsRest⟩ := Lib.rep_cons_of_load hmds C.ldModels
      injection he1 with h1 h2; subst h1 h2
      injection he2 with h3 h4; subst h3 h4
      cases idx with
      | zero =>
        exact memberVal_item ht hbd hS hH (fun cl hcl => hsub cl (C.evMember.sub cl hcl))
          haM haMd hsrc hdst haset hlater C.evMember.obs
      | succ idx' =>
        have ext := C.evMember.extends
        exact membersVal_walk ht hbd hS hH msRest mdRest (Nat.succ.inj hlen)
          (fun cl hcl => hsub cl (C.evRest.sub cl hcl))
          (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext hmsRest)
          (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext hmdsRest)
          (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext hsrc)
          (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext hdst)
          (AddrMapAll.mono (fun _ _ _ _ _ hx => hx) ext haset)
          (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) ext hlater)
          C.evRest.obs idx' (by simp at hidx; omega)

/-- **From any `MemberValItem` and advice coverage, extract the model's stored `.defnInfo` and
sort typing judgement at any `FamilyStepEnv`.** -/
theorem MemberValItem.stored_defn {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {calls : List (Call F)} {bAddr : _root_.Address} {t : Ix.Kernel.RoleTable}
    {E₀ : Ixon.Env} {lim : Option Nat} {B rb : _root_.Address} {cb crb : Ixon.Constant}
    {adv : _root_.Address → Prop} {E : Ixon.Env} {env : Ix.Kernel.Env .anon}
    (hSE : FamilyStepEnv.{u} L calls t E₀ lim B cb rb crb adv E env)
    {csFam : List (Call F)} {advAs srcAs dstAs laterAs : List Bytes.Address}
    {aM aMd : Bytes.Address}
    (I : MemberValItem calls bAddr t E₀ lim csFam advAs srcAs dstAs laterAs aM aMd)
    (hadv : adv (ixAddr aMd)) :
    ∃ (cvm : ConstantVal .anon) (mval : KExpr) (hint : ReducibilityHint),
      env.find? (Core.keyOf t (ixAddr aMd)) = some (.defnInfo cvm mval hint) ∧
      cvm.levelParams.Perm (List.range I.dm.lvls.toNat) ∧
      ExprLvEq I.ty' (Core.posOf cvm.levelParams cvm.type) ∧
      Decl.TmCExact (Core.Ctx.stored ⟨E, env, t, lim⟩).κ I.chain.m101 I.ty' I.chain.mty ∧
      ∃ stype u, Ix.Kernel.Rules.Infer env .full 0 I.ty' stype ∧
        Ix.Kernel.Rules.Red env 0 stype (.sort u) :=
  advice_stored_defn_facts hSE hadv I.hrecM I.hcaM
    (Bytes.repAddressRef_heapMono₂ addrTy
      (I.chain.evInAset.extends.trans (I.chain.evGetM.extends.trans
        (I.chain.evLvlsTy.extends.trans I.chain.evNoMent.extends))) I.haMd)
    I.chain.evGetMd.obs I.chain.evGetMd.sub I.chain.ldMd I.W

/-- **Discharge `adv (ixAddr aMd)` from the two-case advice hypothesis of `FamilyCallRow`.** -/
theorem adv_of_advChecked {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {lim : Option Nat} {csFam : List (Call F)}
    {adv : _root_.Address → Prop} {advAs : List Bytes.Address}
    {aMd : Bytes.Address} {cm : Ixon.Constant}
    (hAdv : AdvChecked calls bAddr t lim csFam advAs aMd)
    (hrec : recordOf E₀ (ixAddr aMd) = some cm)
    (hca : ConstAddrOf (ixAddr aMd) cm (ixAddr aMd))
    (hadvHyp : (∀ a, AdviceIn csFam a → adv a) ∨
      ∀ a, AdviceListedIn advAs a →
        adv a ∨ ∀ ca x, recordOf E₀ a = some ca → ¬ ConstAddrOf a ca x) :
    adv (ixAddr aMd) := by
  rcases hadvHyp with hIn | hList
  · exact hIn (ixAddr aMd) hAdv.2.1
  · rcases hList (ixAddr aMd) ⟨aMd, hAdv.1, rfl⟩ with h | hno
    · exact h
    · exact absurd hca (hno cm (ixAddr aMd) hrec)

/-! ## Helper: exact renaming, non-mention, and `MemberFacts` from `MemberValItem` -/

private theorem nat_eq_of_field_eq_u32 {a b : Nat} (ha : a < 4294967296) (hb : b < 4294967296)
    (h : (a : F) = (b : F)) : a = b := by
  have h1 := congrArg ZMod.val h
  have hmod : Aiur.Library.U32.Goldilocks.modulus = 18446744069414584321 := rfl
  rwa [SubstAux.val_natCast (by omega), SubstAux.val_natCast (by omega)] at h1

/-- Given a `MemberValItem` where `tyPtr = chain.ty` represents `posOf ps tyA` (with
`ps.length = dm.lvls.toNat` and `ps.Perm (List.range ps.length)`), extracts:
1. `Decl.renameAll g (posOf ps tyA) = I.ty'`;
2. `tyA.allLevelParamsDefined ps = true`;
3. `∀ b ∈ laterAs, tyA.mentionsConst (Core.keyOf t (ixAddr b)) = false`;
4. at any `FamilyStepEnv` where every `b ∈ srcAs` maps to a stored `.defnInfo`:
   `Decl.NoProjIn srcKeys tyA = true` and `MemberFacts env g ci tyA`. -/
theorem memberVal_facts_of_tm {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {lim : Option Nat} {csFam : List (Call F)}
    (ht : t.check = .ok ())
    {advAs srcAs dstAs laterAs : List Bytes.Address}
    (hlenSD : srcAs.length = dstAs.length)
    {aM aMd : Bytes.Address}
    (I : MemberValItem calls bAddr t E₀ lim csFam advAs srcAs dstAs laterAs aM aMd)
    {ps : List LevelParam} {ty₀ tyA : KExpr}
    (hperm : ps.Perm (List.range ps.length))
    (hpsLen : ps.length = I.dm.lvls.toNat)
    (hlbb : ty₀.looseBVarsBounded 0 = true)
    (hty0_fv : ty₀.hasFvar = false)
    (hann : Annotates tyA ty₀)
    (htm : Decl.TmCExact (Core.keyOf t) I.chain.m65 (Core.posOf ps tyA) I.chain.ty) :
    let srcKeys := srcAs.map fun b => Core.keyOf t (ixAddr b)
    let dstKeys := dstAs.map fun b => Core.keyOf t (ixAddr b)
    let g := aliasMap (srcKeys.zip dstKeys)
    Decl.renameAll g (Core.posOf ps tyA) = I.ty' ∧
    tyA.allLevelParamsDefined ps = true ∧
    ty₀.hasFvar = false ∧
    tyA.hasFvar = false ∧
    (∀ b ∈ laterAs, tyA.mentionsConst (Core.keyOf t (ixAddr b)) = false) ∧
    ∀ {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
      {B rb : _root_.Address} {cb crb : Ixon.Constant}
      {adv : _root_.Address → Prop} {E : Ixon.Env} {env : Ix.Kernel.Env .anon}
      (hSE : FamilyStepEnv.{u} L calls t E₀ lim B cb rb crb adv E env),
      adv (ixAddr aMd) →
      (∀ k ∈ srcKeys, ∃ cvm mval hint, env.find? (g k) = some (.defnInfo cvm mval hint)) →
      Decl.NoProjIn srcKeys tyA = true ∧
      ∀ (ci : ConstantInfo .anon),
        ci.toConstantVal = ⟨Core.keyOf t (ixAddr aM), ps, ty₀⟩ →
        g ci.name = Core.keyOf t (ixAddr aMd) →
        MemberFacts env g ci tyA := by
  have htwf : t.wf = true := by unfold Ix.Kernel.RoleTable.wf; rw [ht]; rfl
  let srcKeys := srcAs.map fun b => Core.keyOf t (ixAddr b)
  let dstKeys := dstAs.map fun b => Core.keyOf t (ixAddr b)
  let g := aliasMap (srcKeys.zip dstKeys)
  have hren_eq : Decl.renameAll g (Core.posOf ps tyA) = I.ty' := by
    have htm101 : Decl.TmExact (Core.keyOf t) 0 (fun _ => .sort .zero) I.chain.m101 0
        (Core.posOf ps tyA) I.chain.ty :=
      (htm 0 (fun _ => .sort .zero)).mono I.ext_m65_m101
    have hrenTm := rename_aliasMap (Γ₂ := fun _ => .sort .zero) htwf I.chain.evRen.obs hlenSD
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) I.ext_start_m101 I.hsrcRep)
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy) I.ext_start_m101 I.hdstRep)
      htm101
    have hmtyTm := (I.W.tm_ci 0 (fun _ => .sort .zero)).mono I.chain.evRen.extends
    exact Decl.kexpr_struct_eq_one hrenTm hmtyTm I.chain.evEq.obs
  have htyA_def : tyA.allLevelParamsDefined ps = true := by
    have hpos_def : (Core.posOf ps tyA).allLevelParamsDefined (List.range ps.length) = true := by
      rw [← allLevelParamsDefined_renameAll g (List.range ps.length), hren_eq, hpsLen]
      exact I.W.ty_levels
    exact Decl.allLevelParamsDefined_of_posOf_perm hperm hpos_def
  have htyA_fv : tyA.hasFvar = false := by
    have hf := tmExact_hasFvar_false (htm 0 (fun _ => .sort .zero))
    unfold Core.posOf at hf
    rwa [Decl.hasFvar_instantiateLevelParams] at hf
  have hment : ∀ b ∈ laterAs, tyA.mentionsConst (Core.keyOf t (ixAddr b)) = false := by
    intro b hb
    have hT : ∀ a : Bytes.Address, Core.keyOf t (ixAddr a) = Core.keyOf t (ixAddr b) →
        ∃ b' ∈ laterAs, ixAddr b' = ixAddr a := by
      intro a ha
      exact ⟨b, hb, (Core.keyOf_inj htwf ha).symm⟩
    have hm_pos := Decl.expr_mentions_addrs_zero_spec hT
      ((htm 0 (fun _ => .sort .zero)).mono I.chain.evLvlsTy.extends)
      (RepLinkedList.mono (Bytes.repAddressRef_heapMono₂ addrTy)
        (I.chain.evInAset.extends.trans (I.chain.evGetM.extends.trans I.chain.evLvlsTy.extends))
        I.hlaterRep)
      I.chain.evNoMent.obs
    unfold Core.posOf at hm_pos
    rwa [mentionsConst_instantiateLevelParams] at hm_pos
  refine ⟨hren_eq, htyA_def, hty0_fv, htyA_fv, hment, ?_⟩
  intro L B rb cb crb adv E env hSE hadv hdefSrc
  obtain ⟨cvm, mval, hint, hfind, hpermM, hlvEq, -, stype, u, hinf, hred⟩ :=
    I.stored_defn hSE hadv
  have hpos_fv : (Core.posOf ps tyA).hasFvar = false := by
    unfold Core.posOf
    rw [Decl.hasFvar_instantiateLevelParams]
    exact htyA_fv
  have hnp_pos : Decl.NoProjIn srcKeys (Core.posOf ps tyA) = true := by
    have hinf' : Ix.Kernel.Rules.Infer env .full 0 (Decl.renameAll g (Core.posOf ps tyA)) stype := by
      rw [hren_eq]; exact hinf
    exact noProjIn_of_renameAll_infer hSE.prefixInv.store.store hdefSrc hpos_fv hinf'
  have hnp : Decl.NoProjIn srcKeys tyA = true := by
    unfold Core.posOf at hnp_pos
    rwa [Decl.noProjIn_instantiateLevelParams] at hnp_pos
  have hout : ∀ k, srcKeys.contains k = false → g k = k := fun k hk => aliasMap_out_of_zip hk
  have hren_consts : Core.posOf ps (tyA.renameConsts g) = I.ty' := by
    rw [← hren_eq, Decl.renameAll_eq_renameConsts_of_noProjIn hout hnp_pos]
    unfold Core.posOf
    exact Decl.instantiateLevelParams_renameConsts ps (Core.posLevels ps) g tyA
  refine ⟨hnp, fun ci hcv hgci => ?_⟩
  have hname : ci.name = ci.toConstantVal.name := by cases ci <;> rfl
  refine
    { perm := by rw [hcv]; exact hperm
      closed := by rw [hcv]; exact hty0_fv
      bounded := by rw [hcv]; exact hlbb
      annotated := by rw [hcv]; exact hann
      levels := by rw [hcv]; exact htyA_def
      model := ?_
      modelTyped := ?_ }
  · refine ⟨cvm, mval, hint, ?_, ?_, ?_⟩
    · rw [hgci]; exact hfind
    · rw [hcv, hpsLen]; exact hpermM
    · rw [hcv, hren_consts]; exact hlvEq
  · have hinfP : Ix.Kernel.Rules.Infer env .full 0 (Core.posOf ps (tyA.renameConsts g)) stype := by
      rw [hren_consts]; exact hinf
    exact ⟨Decl.invPosOf ps stype, Decl.invPosLevel ps u,
      Decl.posRulesJ_infer_of_pos hperm hinfP,
      Decl.posRulesJ_sort_of_pos hperm hred⟩

/-! ## Types (`evTysVal`), Constructors (`evCtorsVal`), and Recursors (`evRecsVal`) -/

/-- Store-free canonical + model-bridge data for one inductive member of the block. -/
structure IndMemberData (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (lim : Option Nat) (csFam : List (Call F))
    (B : _root_.Address) (cb : Ixon.Constant) (ms : Array Ixon.MutConst)
    (advAs srcAs dstAs : List Bytes.Address) (i : Nat) (ind : Ixon.Inductive)
    (aMd : Bytes.Address) where
  ty₀ : KExpr
  tyA : KExpr
  hread : (exprReader t (fun x => E₀.blobs.get? x) cb id (blockSelf t B ms)).read ind.typ =
    .ok ty₀
  hlbb : ty₀.looseBVarsBounded 0 = true
  hdef : ty₀.allLevelParamsDefined (List.range ind.lvls.toNat) = true
  hcanon : LoadedReads.canonAnn cb (List.range ind.lvls.toNat)
    ((L1.mutsRootOffset ms.toList i : Nat) : F) ind.typ ty₀ = some tyA
  hann : Annotates tyA ty₀
  hA_def : tyA.allLevelParamsDefined (List.range ind.lvls.toNat) = true
  hA_fv : tyA.hasFvar = false
  h0_fv : ty₀.hasFvar = false
  hment : ∀ b ∈ srcAs, tyA.mentionsConst (Core.keyOf t (ixAddr b)) = false
  aM : Bytes.Address
  haM_eq : ixAddr aM = iprjAddr B i
  hitem : MemberValItem calls bAddr t E₀ lim csFam advAs srcAs dstAs srcAs aM aMd
  hlvls_eq : ind.lvls.toNat = hitem.dm.lvls.toNat
  hren : Decl.renameAll (aliasMap ((srcAs.map fun b => Core.keyOf t (ixAddr b)).zip
    (dstAs.map fun b => Core.keyOf t (ixAddr b)))) tyA = hitem.ty'
  hfacts : ∀ {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
      {rb : _root_.Address} {crb : Ixon.Constant}
      {adv : _root_.Address → Prop} {E : Ixon.Env} {env : Ix.Kernel.Env .anon}
      (hSE : FamilyStepEnv.{u} L calls t E₀ lim B cb rb crb adv E env),
      adv (ixAddr aMd) →
      (∀ k ∈ srcAs.map fun b => Core.keyOf t (ixAddr b),
        ∃ cvm mval hint,
          env.find? (aliasMap ((srcAs.map fun b => Core.keyOf t (ixAddr b)).zip
            (dstAs.map fun b => Core.keyOf t (ixAddr b))) k) = some (.defnInfo cvm mval hint)) →
      Decl.NoProjIn (srcAs.map fun b => Core.keyOf t (ixAddr b)) tyA = true ∧
      MemberFacts env (aliasMap ((srcAs.map fun b => Core.keyOf t (ixAddr b)).zip
        (dstAs.map fun b => Core.keyOf t (ixAddr b))))
        (.indInfo ⟨Core.keyOf t (iprjAddr B i), List.range ind.lvls.toNat, ty₀⟩ {}) tyA

/-- **Inductive member data from one `MemberValItem`** at `iprjAddr B i`. -/
theorem indMember_of_item {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {lim : Option Nat} {csFam : List (Call F)}
    (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀)
    {B : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hB : FamBlockRecord E₀ B cb ms)
    {advAs srcAs dstAs : List Bytes.Address}
    (hlenSD : srcAs.length = dstAs.length)
    {i : Nat} {ind : Ixon.Inductive} {aM aMd : Bytes.Address}
    (hi_u64 : i < UInt64.size) (hmi : ms[i]? = some (.indc ind))
    (haM_eq : ixAddr aM = iprjAddr B i)
    (hg_eq : aliasMap ((srcAs.map fun b => Core.keyOf t (ixAddr b)).zip
      (dstAs.map fun b => Core.keyOf t (ixAddr b))) (Core.keyOf t (iprjAddr B i)) =
      Core.keyOf t (ixAddr aMd))
    (I : MemberValItem calls bAddr t E₀ lim csFam advAs srcAs dstAs srcAs aM aMd) :
    Nonempty (IndMemberData calls bAddr t E₀ lim csFam B cb ms advAs srcAs dstAs i ind aMd) := by
  have haM_m15 : Bytes.RepAddressRef addrTy I.chain.m15 aM I.xM :=
    Bytes.repAddressRef_heapMono₂ addrTy I.chain.evInAset.extends I.haM
  have hbdM : Bounded I.chain.evGetM.cs := bounded_sub I.chain.evGetM.sub hbd
  obtain ⟨rawBytes, cM, hhM, hbaM, hexM, -, htrM⟩ :=
    L1.get_ci_block_trace_spec hbdM haM_m15 I.chain.evGetM.obs
  have hrecM : recordOf E₀ (ixAddr aM) = some (memberProjection B i (.indc ind)) := by
    rw [haM_eq, ← LoadedReads.memberAddr_indc]
    exact hB.members i (.indc ind) hmi
  have hrecAtM : Ix.Cert.recordAt E₀ (ixAddr aM) = some (memberProjection B i (.indc ind)) :=
    (hS.recordOf_eq_recordAt _).symm.trans hrecM
  have hcM_eq : cM = memberProjection B i (.indc ind) :=
    hS.record_eq hrecAtM (Core.hashed_mono I.chain.evGetM.sub hhM) hbaM hexM
  subst hcM_eq
  unfold L1.GetCIBlockTraceResult at htrM
  simp only [memberProjection] at htrM
  obtain ⟨-, blkBytes, cb', ms', ind', blobs, tree, plan, v, hhBlk, hbaBlk, hexBlk, hmuts',
    hmi', hhp, built, planned, hldv, hraw, hlevs⟩ := htrM
  have hrecAtB : Ix.Cert.recordAt E₀ B = some cb :=
    (hS.recordOf_eq_recordAt B).symm.trans hB.record
  have hcb_eq : cb' = cb :=
    hS.record_eq hrecAtB (Core.hashed_mono I.chain.evGetM.sub hhBlk) hbaBlk hexBlk
  subst cb'
  have hms_eq : ms' = ms := Ixon.ConstantInfo.muts.inj (hmuts'.symm.trans hB.muts)
  subst ms'
  have hi_toNat : i.toUInt64.toNat = i := toNat_toUInt64_lt hi_u64
  rw [hi_toNat, Array.getElem?_toList, hmi] at hmi'
  have hind_eq : ind' = ind := Ixon.MutConst.indc.inj (Option.some.inj hmi').symm
  subst ind'
  obtain ⟨hlvls_lt, -, -, -, -, tyPtr, blkPtr, bBlk, -, -, hv_eq, rty⟩ := hraw
  rw [hi_toNat] at planned
  have hci_eq : I.chain.ci = v := Except.ok.inj (I.chain.ldM.symm.trans hldv)
  subst hci_eq
  obtain ⟨-, hlt_raw⟩ := ci_lvls_type_raw I.chain.evLvlsTy.obs
  obtain ⟨hnl_eq, hty_eq⟩ := hlt_raw "Induct" (.field (ind.lvls.toNat : F)) tyPtr _ hv_eq
  subst hty_eq
  have hlvls_eq : ind.lvls.toNat = I.dm.lvls.toNat :=
    nat_eq_of_field_eq_u32 hlvls_lt I.W.nlvls_lt (Value.field.inj (hnl_eq.symm.trans I.W.nl_eq))
  have hblob : ∀ x bs, (x, bs) ∈ blobs → E₀.blobs.get? x = some bs := by
    intro x bs hm
    obtain ⟨hhx, hxa⟩ := hhp (x, bs) hm
    have hrun := hS.blobs bs (Core.hashed_mono I.chain.evGetM.sub hhx)
    rwa [hxa] at hrun
  have hagree : L1.BlobReadAgreement (readCtx t (fun x => E₀.blobs.get? x)).blob blobs :=
    L1.BlobReadAgreement.of_mem hblob
  obtain ⟨ty₀, hread⟩ :=
    LoadedReads.exprReader_read_ok ht rty (LoadedReads.blockSelf_ok t B ms) hblob
  have htySc : HeapExprScoped I.hEnd ind.lvls.toNat 0 I.chain.ty := by
    rw [hlvls_eq]; exact I.htyScoped
  obtain ⟨hlbb, hdef⟩ :=
    rawConvExpr_scoped_of_heapExprScoped rty
      (I.ext_m65_m101.trans (I.chain.evRen.extends.trans I.chain.evEq.extends)) hread htySc
  obtain ⟨cnt, tyPtr', flds, hvc, hbl⟩ := hlevs
  rw [hv_eq] at hvc
  injection hvc with _ _ hca; injection hca with _ hca; injection hca with htp _; subst htp
  obtain ⟨tyA, hcanon, hann, htm⟩ :=
    annotation_canon_range_exact ht hlvls_lt (LoadedReads.blockSelf_key t B ms) hagree rty built
      planned hbl hread hlbb hdef
  have htm_pos : Decl.TmCExact (Core.keyOf t) I.chain.m65
      (Core.posOf (List.range ind.lvls.toNat) tyA) I.chain.ty := by
    rw [Decl.posOf_range]; exact htm
  obtain ⟨hren_pos, hA_def, h0_fv, hA_fv, hment, hstep⟩ :=
    memberVal_facts_of_tm ht hlenSD I (ps := List.range ind.lvls.toNat)
      (by simp) (by simp [hlvls_eq]) hlbb (Assembly.memberReader_read_noFvar hread) hann htm_pos
  rw [Decl.posOf_range] at hren_pos
  exact ⟨{
    ty₀, tyA, hread, hlbb, hdef, hcanon, hann, hA_def, hA_fv, h0_fv, hment
    aM, haM_eq
    hitem := I
    hlvls_eq
    hren := hren_pos
    hfacts := fun hSE hadv hdefSrc => by
      obtain ⟨hnp, hmf⟩ := hstep hSE hadv hdefSrc
      refine ⟨hnp, hmf (.indInfo ⟨Core.keyOf t (iprjAddr B i), List.range ind.lvls.toNat, ty₀⟩ {})
        ?_ ?_⟩
      · simp [ConstantInfo.toConstantVal, haM_eq]
      · exact hg_eq }⟩

/-- Store-free canonical + model-bridge data for one constructor of the block. -/
structure CtorMemberData (calls : List (Call F)) (bAddr : _root_.Address)
    (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (lim : Option Nat) (csFam : List (Call F))
    (B : _root_.Address) (cb : Ixon.Constant) (ms : Array Ixon.MutConst)
    (advAs srcAs dstAs laterAs : List Bytes.Address)
    (i : Nat) (ind : Ixon.Inductive) (j : Nat) (ct : Ixon.Constructor)
    (aMd : Bytes.Address) where
  ty₀ : KExpr
  tyA : KExpr
  hread : (exprReader t (fun x => E₀.blobs.get? x) cb id (blockSelf t B ms)).read ct.typ =
    .ok ty₀
  hlbb : ty₀.looseBVarsBounded 0 = true
  hdef : ty₀.allLevelParamsDefined (List.range ct.lvls.toNat) = true
  hcanon : LoadedReads.canonAnn cb (List.range ct.lvls.toNat)
    (((L1.mutsRootOffset ms.toList i : Nat) : F) + 1 + ((j : Nat) : F)) ct.typ ty₀ = some tyA
  hann : Annotates tyA ty₀
  hA_def : tyA.allLevelParamsDefined (List.range ct.lvls.toNat) = true
  hA_fv : tyA.hasFvar = false
  h0_fv : ty₀.hasFvar = false
  hment : ∀ b ∈ laterAs, tyA.mentionsConst (Core.keyOf t (ixAddr b)) = false
  aM : Bytes.Address
  haM_eq : ixAddr aM = cprjAddr B i j
  hitem : MemberValItem calls bAddr t E₀ lim csFam advAs srcAs dstAs laterAs aM aMd
  hlvls_eq : ct.lvls.toNat = hitem.dm.lvls.toNat
  hren : Decl.renameAll (aliasMap ((srcAs.map fun b => Core.keyOf t (ixAddr b)).zip
    (dstAs.map fun b => Core.keyOf t (ixAddr b)))) tyA = hitem.ty'
  hfacts : ∀ {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
      {rb : _root_.Address} {crb : Ixon.Constant}
      {adv : _root_.Address → Prop} {E : Ixon.Env} {env : Ix.Kernel.Env .anon}
      (hSE : FamilyStepEnv.{u} L calls t E₀ lim B cb rb crb adv E env),
      adv (ixAddr aMd) →
      (∀ k ∈ srcAs.map fun b => Core.keyOf t (ixAddr b),
        ∃ cvm mval hint,
          env.find? (aliasMap ((srcAs.map fun b => Core.keyOf t (ixAddr b)).zip
            (dstAs.map fun b => Core.keyOf t (ixAddr b))) k) = some (.defnInfo cvm mval hint)) →
      Decl.NoProjIn (srcAs.map fun b => Core.keyOf t (ixAddr b)) tyA = true ∧
      MemberFacts env (aliasMap ((srcAs.map fun b => Core.keyOf t (ixAddr b)).zip
        (dstAs.map fun b => Core.keyOf t (ixAddr b))))
        (.ctorInfo ⟨Core.keyOf t (cprjAddr B i j), List.range ct.lvls.toNat, ty₀⟩
          ct.params.toNat ct.fields.toNat) tyA

/-- **Constructor member data from one `MemberValItem`** at `cprjAddr B i j`. -/
theorem ctorMember_of_item {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {lim : Option Nat} {csFam : List (Call F)}
    (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀)
    {B : _root_.Address} {cb : Ixon.Constant} {ms : Array Ixon.MutConst}
    (hB : FamBlockRecord E₀ B cb ms)
    {advAs srcAs dstAs laterAs : List Bytes.Address}
    (hlenSD : srcAs.length = dstAs.length)
    {i : Nat} {ind : Ixon.Inductive} {j : Nat} {ct : Ixon.Constructor} {aM aMd : Bytes.Address}
    (hi_u64 : i < UInt64.size) (hj_u64 : j < UInt64.size)
    (hmi : ms[i]? = some (.indc ind)) (hct : ind.ctors[j]? = some ct)
    (haM_eq : ixAddr aM = cprjAddr B i j)
    (hg_eq : aliasMap ((srcAs.map fun b => Core.keyOf t (ixAddr b)).zip
      (dstAs.map fun b => Core.keyOf t (ixAddr b))) (Core.keyOf t (cprjAddr B i j)) =
      Core.keyOf t (ixAddr aMd))
    (I : MemberValItem calls bAddr t E₀ lim csFam advAs srcAs dstAs laterAs aM aMd) :
    Nonempty (CtorMemberData calls bAddr t E₀ lim csFam B cb ms advAs srcAs dstAs laterAs
      i ind j ct aMd) := by
  have haM_m15 : Bytes.RepAddressRef addrTy I.chain.m15 aM I.xM :=
    Bytes.repAddressRef_heapMono₂ addrTy I.chain.evInAset.extends I.haM
  have hbdM : Bounded I.chain.evGetM.cs := bounded_sub I.chain.evGetM.sub hbd
  obtain ⟨rawBytes, cM, hhM, hbaM, hexM, -, htrM⟩ :=
    L1.get_ci_block_trace_spec hbdM haM_m15 I.chain.evGetM.obs
  have hjLt : j < ind.ctors.size := (Array.getElem?_eq_some_iff.mp hct).1
  have hrecM : recordOf E₀ (ixAddr aM) = some (constructorProjection B i j) := by
    rw [haM_eq, ← LoadedReads.ctorAddr_eq_cprjAddr]
    exact hB.ctors i ind j hmi hjLt
  have hrecAtM : Ix.Cert.recordAt E₀ (ixAddr aM) = some (constructorProjection B i j) :=
    (hS.recordOf_eq_recordAt _).symm.trans hrecM
  have hcM_eq : cM = constructorProjection B i j :=
    hS.record_eq hrecAtM (Core.hashed_mono I.chain.evGetM.sub hhM) hbaM hexM
  subst hcM_eq
  unfold L1.GetCIBlockTraceResult at htrM
  simp only [constructorProjection] at htrM
  obtain ⟨-, -, blkBytes, cb', ms', ind', ct', blobs, tree, plan, v, hhBlk, hbaBlk, hexBlk,
    hmuts', hmi', hct', hhp, built, planned, hldv, hraw, hlevs⟩ := htrM
  have hrecAtB : Ix.Cert.recordAt E₀ B = some cb :=
    (hS.recordOf_eq_recordAt B).symm.trans hB.record
  have hcb_eq : cb' = cb :=
    hS.record_eq hrecAtB (Core.hashed_mono I.chain.evGetM.sub hhBlk) hbaBlk hexBlk
  subst cb'
  have hms_eq : ms' = ms := Ixon.ConstantInfo.muts.inj (hmuts'.symm.trans hB.muts)
  subst ms'
  have hi_toNat : i.toUInt64.toNat = i := toNat_toUInt64_lt hi_u64
  have hj_toNat : j.toUInt64.toNat = j := toNat_toUInt64_lt hj_u64
  rw [hi_toNat, Array.getElem?_toList, hmi] at hmi'
  have hind_eq : ind' = ind := Ixon.MutConst.indc.inj (Option.some.inj hmi').symm
  subst ind'
  rw [hj_toNat, Array.getElem?_toList, hct] at hct'
  have hct_eq : ct' = ct := (Option.some.inj hct').symm
  subst ct'
  obtain ⟨hlvls_lt, -, -, -, -, tyPtr, blkPtr, bBlk, -, -, hv_eq, rty⟩ := hraw
  rw [hi_toNat, hj_toNat] at planned
  have hci_eq : I.chain.ci = v := Except.ok.inj (I.chain.ldM.symm.trans hldv)
  subst hci_eq
  obtain ⟨-, hlt_raw⟩ := ci_lvls_type_raw I.chain.evLvlsTy.obs
  obtain ⟨hnl_eq, hty_eq⟩ := hlt_raw "Ctor" (.field (ct.lvls.toNat : F)) tyPtr _ hv_eq
  subst hty_eq
  have hlvls_eq : ct.lvls.toNat = I.dm.lvls.toNat :=
    nat_eq_of_field_eq_u32 hlvls_lt I.W.nlvls_lt (Value.field.inj (hnl_eq.symm.trans I.W.nl_eq))
  have hblob : ∀ x bs, (x, bs) ∈ blobs → E₀.blobs.get? x = some bs := by
    intro x bs hm
    obtain ⟨hhx, hxa⟩ := hhp (x, bs) hm
    have hrun := hS.blobs bs (Core.hashed_mono I.chain.evGetM.sub hhx)
    rwa [hxa] at hrun
  have hagree : L1.BlobReadAgreement (readCtx t (fun x => E₀.blobs.get? x)).blob blobs :=
    L1.BlobReadAgreement.of_mem hblob
  obtain ⟨ty₀, hread⟩ :=
    LoadedReads.exprReader_read_ok ht rty (LoadedReads.blockSelf_ok t B ms) hblob
  have htySc : HeapExprScoped I.hEnd ct.lvls.toNat 0 I.chain.ty := by
    rw [hlvls_eq]; exact I.htyScoped
  obtain ⟨hlbb, hdef⟩ :=
    rawConvExpr_scoped_of_heapExprScoped rty
      (I.ext_m65_m101.trans (I.chain.evRen.extends.trans I.chain.evEq.extends)) hread htySc
  obtain ⟨cnt, tyPtr', flds, hvc, hbl⟩ := hlevs
  rw [hv_eq] at hvc
  injection hvc with _ _ hca; injection hca with _ hca; injection hca with htp _; subst htp
  obtain ⟨tyA, hcanon, hann, htm⟩ :=
    annotation_canon_range_exact ht hlvls_lt (LoadedReads.blockSelf_key t B ms) hagree rty built
      planned hbl hread hlbb hdef
  have htm_pos : Decl.TmCExact (Core.keyOf t) I.chain.m65
      (Core.posOf (List.range ct.lvls.toNat) tyA) I.chain.ty := by
    rw [Decl.posOf_range]; exact htm
  obtain ⟨hren_pos, hA_def, h0_fv, hA_fv, hment, hstep⟩ :=
    memberVal_facts_of_tm ht hlenSD I (ps := List.range ct.lvls.toNat)
      (by simp) (by simp [hlvls_eq]) hlbb (Assembly.memberReader_read_noFvar hread) hann htm_pos
  rw [Decl.posOf_range] at hren_pos
  exact ⟨{
    ty₀, tyA, hread, hlbb, hdef, hcanon, hann, hA_def, hA_fv, h0_fv, hment
    aM, haM_eq
    hitem := I
    hlvls_eq
    hren := hren_pos
    hfacts := fun hSE hadv hdefSrc => by
      obtain ⟨hnp, hmf⟩ := hstep hSE hadv hdefSrc
      refine ⟨hnp, hmf (.ctorInfo ⟨Core.keyOf t (cprjAddr B i j), List.range ct.lvls.toNat, ty₀⟩
        ct.params.toNat ct.fields.toNat) ?_ ?_⟩
      · simp [ConstantInfo.toConstantVal, haM_eq]
      · exact hg_eq }⟩

/-- **Bridge from `evRecsVal`'s `MemberValItem` at recursor `k`** to `NoProjIn`, non-mention of
`recAs`, and `MemberFacts` for any canonical recursor reading `(ps, ty₀, tyA)`. -/
theorem recMemberVal_of_item {calls : List (Call F)} {bAddr : _root_.Address}
    {t : Ix.Kernel.RoleTable} {E₀ : Ixon.Env} {lim : Option Nat} {csFam : List (Call F)}
    (ht : t.check = .ok ()) (hbd : Bounded calls)
    (hS : LoadedReads.RunStore calls E₀)
    {rb : _root_.Address} {crb : Ixon.Constant} {rs : Array Ixon.MutConst}
    (hR : FamRecRecord E₀ rb crb rs)
    {advAs srcAs dstAs recAs : List Bytes.Address}
    (hlenSD : srcAs.length = dstAs.length)
    {k : Nat} {rc : Ixon.Recursor} {aM aMd : Bytes.Address}
    (hk_u64 : k < UInt64.size) (hrk : rs[k]? = some (.recr rc))
    (haM_eq : ixAddr aM = rprjAddr rb k)
    (hg_eq : aliasMap ((srcAs.map fun b => Core.keyOf t (ixAddr b)).zip
      (dstAs.map fun b => Core.keyOf t (ixAddr b))) (Core.keyOf t (rprjAddr rb k)) =
      Core.keyOf t (ixAddr aMd))
    (I : MemberValItem calls bAddr t E₀ lim csFam advAs srcAs dstAs recAs aM aMd)
    {ps : List LevelParam} {ty₀ tyA : KExpr}
    (hperm : ps.Perm (List.range ps.length))
    (hpsLen : ps.length = rc.lvls.toNat)
    (hread : (exprReader t (fun x => E₀.blobs.get? x) crb (Ix.Kernel.Reader.recParam ps)
      (blockSelf t rb rs)).read rc.typ = .ok ty₀)
    (hlbb : ty₀.looseBVarsBounded 0 = true)
    (hdef : ty₀.allLevelParamsDefined ps = true)
    (hcanon : LoadedReads.canonAnn crb ps ((L1.mutsRootOffset rs.toList k : Nat) : F) rc.typ ty₀ =
      some tyA) :
    let srcKeys := srcAs.map fun b => Core.keyOf t (ixAddr b)
    let dstKeys := dstAs.map fun b => Core.keyOf t (ixAddr b)
    let g := aliasMap (srcKeys.zip dstKeys)
    Decl.renameAll g (Core.posOf ps tyA) = I.ty' ∧
    tyA.allLevelParamsDefined ps = true ∧
    ty₀.hasFvar = false ∧
    tyA.hasFvar = false ∧
    (∀ b ∈ recAs, tyA.mentionsConst (Core.keyOf t (ixAddr b)) = false) ∧
    ∀ {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
      {B : _root_.Address} {cb : Ixon.Constant}
      {adv : _root_.Address → Prop} {E : Ixon.Env} {env : Ix.Kernel.Env .anon}
      (hSE : FamilyStepEnv.{u} L calls t E₀ lim B cb rb crb adv E env),
      adv (ixAddr aMd) →
      (∀ k' ∈ srcKeys, ∃ cvm mval hint, env.find? (g k') = some (.defnInfo cvm mval hint)) →
      Decl.NoProjIn srcKeys tyA = true ∧
      ∀ (mI rP : Nat) (rules₀ : List (Ix.Kernel.RecRule .anon)),
        MemberFacts env g (.recInfo ⟨Core.keyOf t (rprjAddr rb k), ps, ty₀⟩ mI rP rules₀) tyA := by
  have haM_m15 : Bytes.RepAddressRef addrTy I.chain.m15 aM I.xM :=
    Bytes.repAddressRef_heapMono₂ addrTy I.chain.evInAset.extends I.haM
  have hbdM : Bounded I.chain.evGetM.cs := bounded_sub I.chain.evGetM.sub hbd
  obtain ⟨rawBytes, cM, hhM, hbaM, hexM, -, htrM⟩ :=
    L1.get_ci_block_trace_spec hbdM haM_m15 I.chain.evGetM.obs
  have hrecM : recordOf E₀ (ixAddr aM) = some (memberProjection rb k (.recr rc)) := by
    rw [haM_eq, ← LoadedReads.memberAddr_recr]
    exact hR.members k (.recr rc) hrk
  have hrecAtM : Ix.Cert.recordAt E₀ (ixAddr aM) = some (memberProjection rb k (.recr rc)) :=
    (hS.recordOf_eq_recordAt _).symm.trans hrecM
  have hcM_eq : cM = memberProjection rb k (.recr rc) :=
    hS.record_eq hrecAtM (Core.hashed_mono I.chain.evGetM.sub hhM) hbaM hexM
  subst hcM_eq
  unfold L1.GetCIBlockTraceResult at htrM
  simp only [memberProjection] at htrM
  obtain ⟨-, blkBytes, crb', rs', rc', blobs, tree, v, hhBlk, hbaBlk, hexBlk, hmuts',
    hrk', hhp, built, hldv, hrep⟩ := htrM
  have hrecAtR : Ix.Cert.recordAt E₀ rb = some crb :=
    (hS.recordOf_eq_recordAt rb).symm.trans hR.record
  have hcrb_eq : crb' = crb :=
    hS.record_eq hrecAtR (Core.hashed_mono I.chain.evGetM.sub hhBlk) hbaBlk hexBlk
  subst crb'
  have hrs_eq : rs' = rs := Ixon.ConstantInfo.muts.inj (hmuts'.symm.trans hR.muts)
  subst rs'
  have hk_toNat : k.toUInt64.toNat = k := toNat_toUInt64_lt hk_u64
  rw [hk_toNat, Array.getElem?_toList, hrk] at hrk'
  have hrc_eq : rc' = rc := Ixon.MutConst.recr.inj (Option.some.inj hrk').symm
  subst rc'
  rw [hk_toNat] at hrep
  obtain ⟨hlvls_lt, -, -, -, -, -, tyPtr, rulesPtr, blkPtr, bBlk, planT, -, -, hv_eq,
    rty, hpT, hlT, -⟩ := hrep
  have hci_eq : I.chain.ci = v := Except.ok.inj (I.chain.ldM.symm.trans hldv)
  subst hci_eq
  obtain ⟨-, hlt_raw⟩ := ci_lvls_type_raw I.chain.evLvlsTy.obs
  obtain ⟨hnl_eq, hty_eq⟩ := hlt_raw "Rec" (.field (rc.lvls.toNat : F)) tyPtr _ hv_eq
  subst hty_eq
  have hlvls_eq : rc.lvls.toNat = I.dm.lvls.toNat :=
    nat_eq_of_field_eq_u32 hlvls_lt I.W.nlvls_lt (Value.field.inj (hnl_eq.symm.trans I.W.nl_eq))
  have hblob : ∀ x bs, (x, bs) ∈ blobs → E₀.blobs.get? x = some bs := by
    intro x bs hm
    obtain ⟨hhx, hxa⟩ := hhp (x, bs) hm
    have hrun := hS.blobs bs (Core.hashed_mono I.chain.evGetM.sub hhx)
    rwa [hxa] at hrun
  have hagree : L1.BlobReadAgreement (readCtx t (fun x => E₀.blobs.get? x)).blob blobs :=
    L1.BlobReadAgreement.of_mem hblob
  have hself_nil : ∀ i x m k', ([] : List _root_.Address)[i]? = some x →
      blockSelf t rb rs i = some m → m = .ok k' → k' = Core.keyOf t x := fun _ _ _ _ hx => by
    simp at hx
  obtain ⟨tyA', hcanon', hann', htm'⟩ :=
    annotation_canon_gen_exact ht hperm (by rw [hpsLen]; exact hlvls_lt)
      hself_nil hagree rty built hpT hlT hread hlbb hdef
  have htyA_eq : tyA' = tyA := Option.some.inj (hcanon'.symm.trans hcanon)
  subst tyA'
  obtain ⟨hren, hA_def, h0_fv, hA_fv, hment, hstep⟩ :=
    memberVal_facts_of_tm ht hlenSD I hperm (hpsLen.trans hlvls_eq) hlbb
      (Assembly.memberReader_read_noFvar hread) hann' htm'
  refine ⟨hren, hA_def, h0_fv, hA_fv, hment, fun hSE hadv hdefSrc => ?_⟩
  obtain ⟨hnp, hmf⟩ := hstep hSE hadv hdefSrc
  exact ⟨hnp, fun mI rP rules₀ =>
    hmf (.recInfo ⟨Core.keyOf t (rprjAddr rb k), ps, ty₀⟩ mI rP rules₀)
      (by simp [ConstantInfo.toConstantVal, haM_eq]) hg_eq⟩

end IxVM.Refinement.Typing.FamilyAlias
