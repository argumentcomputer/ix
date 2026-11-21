import IxVMRefinement.Assembly.NativeBlockRecScanRaw
import IxVMRefinement.Assembly.NativeBlockNewFacts

/-! # The circuit's `is_rec` verdict at a native block, read as IxC's recursion flag

`KernelWhnf::struct_is_rec` answers Lean's block-level `is_rec`: it loads the parent, computes the
block's member addresses, and for each member scans the field domains of each constructor (after
the parameters) for a constant at a member address. The registered specification
(`Specs.Whnf.struct_is_rec`) states the scan's cleanness for SOME represented constructor value;
it does not expose the constructor load, so it cannot be tied to the stored constructor. This file
reads the run directly:

* `rs_addr_in`, `rs_mentions`, `rs_scan_fields`: the mention scans' facts by their own induction,
  at any keying (no registry, no core facts);
* `rs_scan_ctors`, `rs_scan_members`, `rs_is_rec`: the scans' runs, exposing each constructor slot's
  `Ingress::get_ci_cprj` observation and the cleanness of the loaded type's fields;
* `tm_mentions_false`, `tm_fieldsClean_doms`: a clean heap term's image mentions no constant at a
  key whose addresses are members and at which no projection is permitted;
* `Typing.struct_is_rec_doms`: **an answer other than `1` at the former of a one-member block means
  the canonical constructors' field domains (after the parameters) do not mention the former**;
* `Typing.nativeIsRec_false_of_doms`: then IxC's recursion flag on the classified kinds is false.
-/


namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal IndCaps)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## IxC's recursion flag from clean field domains -/

theorem mapM_option_mem {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → ∀ b ∈ r, ∃ a ∈ l, f a = some b
  | [], r, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    intro b hb
    simp at hb
  | a :: l, r, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    intro b' hb'
    rcases List.mem_cons.mp hb' with rfl | hb'
    · exact ⟨a, by simp, hb⟩
    · obtain ⟨a', ha', hfa'⟩ := mapM_option_mem hbs b' hb'
      exact ⟨a', by simp [ha'], hfa'⟩

/-- A constructor whose field domains do not mention `T` is classified with no recursive and no
reflexive field. -/
theorem recCtorKinds_noRec {T : Core.KKey} {lps : List Ix.Kernel.LevelParam} {nP nIdx : Nat}
    {cA : ConstantVal .anon × Nat} {ks : List Ix.Kernel.RecFieldKind}
    (h : Ix.Kernel.recCtorKinds T lps nP nIdx cA = some ks)
    (hdoms : ∀ cbs body, cA.1.type.stripPis (nP + cA.2) = some (cbs, body) →
      ∀ i < cA.2, ((cbs.getD (nP + i) default).1).mentionsConst T = false) :
    ks.any (fun k => k == .recursive || k == .reflexive) = false := by
  unfold Ix.Kernel.recCtorKinds at h
  cases hs : cA.1.type.stripPis (nP + cA.2) with
  | none => rw [hs] at h; exact nomatch h
  | some r =>
    obtain ⟨cbs, cbody⟩ := r
    rw [hs] at h
    simp only at h
    have hord : ∀ i ∈ List.range cA.2,
        Ix.Kernel.recFieldKind T lps nP nIdx i (cbs.getD (nP + i) default).1 = .ordinary := by
      intro i hi
      have hm := hdoms cbs cbody hs i (List.mem_range.mp hi)
      unfold Ix.Kernel.recFieldKind
      rw [hm]
      simp
    split at h
    · injection h with h
      subst h
      rw [List.any_eq_false]
      intro k hk
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hk
      have ho := hord i hi
      simp only [ho]
      decide
    · injection h with h
      subst h
      rw [List.any_eq_false]
      intro k hk
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hk
      decide

/-- **IxC's recursion flag is false where no constructor's field domain mentions the family.** -/
theorem nativeIsRec_false_of_doms {T : Core.KKey} {lps : List Ix.Kernel.LevelParam}
    {nP nIdx : Nat} {ctorsA : List (ConstantVal .anon × Nat)}
    {kinds : List (List Ix.Kernel.RecFieldKind)}
    (hk : Ix.Kernel.classifyFixKinds (m := Ix.Kernel.CheckM .anon) T lps nP nIdx ctorsA =
      .ok kinds)
    (hdoms : ∀ cA ∈ ctorsA, ∀ cbs body, cA.1.type.stripPis (nP + cA.2) = some (cbs, body) →
      ∀ i < cA.2, ((cbs.getD (nP + i) default).1).mentionsConst T = false) :
    Ix.Kernel.nativeIsRec kinds = false := by
  obtain ⟨hmap, -, -, -⟩ := Ix.Kernel.classifyFixKinds_inv hk
  unfold Ix.Kernel.nativeIsRec
  rw [List.any_eq_false]
  intro ks hks
  obtain ⟨cA, hcA, hrk⟩ := mapM_option_mem hmap ks hks
  have := recCtorKinds_noRec hrk (hdoms cA hcA)
  simp [this]

/-! ## The verdict at the former of a one-member block -/

/-- **An `is_rec` verdict other than `1` at the former reads the canonical constructors' fields.**
The store holds the block `cb` at `B` with one member `ind` and its inductive projection at the
former's address; the prefix stores the references the block uses, not the former's key, and no
key of a projection marker (`HashKeyed`). A run of `KernelWhnf::struct_is_rec` at the former's
address, answering other than `1`, with no hashed collision with the store: then for every
constructor `j`, the canonical annotation `cty'` of its reading has, after the parameters, binder
domains that do not mention the former's key. The scan is read at the keying of the constructor
stage, under which the loaded type represents `cty'` exactly (`LoadedReads.ctor_load_canon`), a
constant at the former's key is at the member's address (which the member list holds), and no
projection at the former is permitted. -/
theorem struct_is_rec_doms {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ())
    {E : Ixon.Env} (hdec : Ingress.EnvDecoded E) {env : Ix.Kernel.Env .anon} {lim : Option Nat}
    (hinv : Decl.PrefixInv E t lim env) (hkeys : HashKeyed t env)
    {B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive}
    (hblock : recordOf E B = some cb) (hmuts : cb.info = .muts #[.indc ind])
    (hproj : recordOf E (Core.iprjAddr B 0) = some (memberProjection B 0 (.indc ind)))
    (hstored : Decl.UsedRefsStored t env cb)
    (hfresh : env.find? (Core.keyOf t (Core.iprjAddr B 0)) = none)
    {sp v : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {sa : Bytes.Address}
    (ev : ObsFn Core.W "KernelWhnf::struct_is_rec" [sp] h v h' cs) (hv : v ≠ .field 1)
    (good : Core.Good ⟨E, env, t, lim⟩ cs)
    (hsa : Bytes.RepAddressRef Core.addrTy h sa sp) (hsaB : Core.ixAddr sa = Core.iprjAddr B 0)
    {j : Nat} {ct : Ixon.Constructor} {cty cty' : Ix.Kernel.Expr .anon}
    (hct : ind.ctors[j]? = some ct) (hcidx : ct.cidx.toNat = j)
    (hty : (exprReader t (fun x => E.blobs.get? x) cb id
      (blockSelf t B #[.indc ind])).read ct.typ = .ok cty)
    (hlbb : cty.looseBVarsBounded 0 = true)
    (hdef : cty.allLevelParamsDefined (List.range ct.lvls.toNat) = true)
    (hcanon : LoadedReads.canonAnn cb (List.range ct.lvls.toNat)
      (((Ingress.mutsRootOffset (#[.indc ind] : Array Ixon.MutConst).toList 0 : Nat) : F) + 1 +
        ((j : Nat) : F)) ct.typ cty = some cty') :
    ∀ (n : Nat) (bs : List (Core.KExpr × Ix.Kernel.BinderMeta)) (body : Core.KExpr),
      cty'.stripPis n = some (bs, body) → ∀ i, ind.params.toNat ≤ i → i < n →
        ((bs.getD i default).1).mentionsConst (Core.keyOf t (Core.iprjAddr B 0)) = false := by
  intro n bs body hs i hi hin
  have htwf : t.wf = true := hinv.tableWf
  -- the outer run: the parent's load, the member list, the member scan
  obtain ⟨m2, p9, cs15, w42, w43, w44, w45, w46, w47, x_block, w48, m90, v116, m117, cs127, cs149,
    ev17, hs15, ld11, e2_90, ev129, hs127, ev151, hs149⟩ := Core.rs_is_rec ev hv
  have e17 := ObsFn.heap_extends ev17
  have g15 := good.sub hs15
  obtain ⟨b, i0, -, hb2, -, hinfo⟩ := get_ci_induct_record hdec g15.1 g15.2 ev17 hsa ld11
    (by rw [hsaB]; exact hproj)
  have hbB : Core.ixAddr b = B := by
    have h0 : (memberProjection B 0 (.indc ind)).info = .iPrj ⟨(0 : Nat).toUInt64, B⟩ := rfl
    rw [h0] at hinfo
    injection hinfo with hpp
    injection hpp with _ hb
    exact hb.symm
  have g127 := good.sub hs127
  obtain ⟨xs, hxs, hmem, -⟩ := Core.Registry.induction (Core.Ctx.stored ⟨E, env, t, lim⟩)
    (Core.scoped_steps _ hinv.scopedCoreFacts) (.whnf .struct_block_member_addrs) [sp, x_block]
    m90 v116 m117 cs127 ev129 sp x_block rfl (Core.CoreGood.ofRaw g127 (fun _ _ => trivial)) sa b
    (Core.se_addrRep_mono (e17.trans e2_90) hsa) (Core.se_addrRep_mono e2_90 hb2) cb
    (by rw [hbB]; exact recordAt_of_recordOf hdec hblock)
  obtain ⟨a₀, ha₀, hxa₀⟩ := hmem #[.indc ind] hmuts 0 ind (by simp)
  rw [hbB] at hxa₀
  -- the member's load and its constructor scan
  obtain ⟨xm, ptr1, h1, h2, cs1, v1, -, hrep1, ev1, hs1, ld1, hscan⟩ :=
    Core.rs_scan_members (cs149.length + 1) (Nat.lt_succ_self _) ev151 hxs hxs hv a₀ ha₀
  have g1 := good.sub (fun x hx => hs149 x (hs1 x hx))
  obtain ⟨tyPtr0, blkPtr, hld1, hp56, hi56, hc56⟩ :=
    former_get_ci_value g1.1 g1.2 hrep1 ev1 (by rw [hxa₀]; exact hproj) hblock hmuts
  have hv1 := Except.ok.inj (ld1.symm.trans hld1)
  obtain ⟨rr, h3, cs3, ev3, hs3, hrr, -, hxs2⟩ := hscan _ _ _ _ _ _ _ _ hv1
  obtain ⟨b', i1, -, hb'2, -, hinfo'⟩ := get_ci_induct_record hdec g1.1 g1.2 ev1 hrep1 hld1
    (by rw [hxa₀]; exact hproj)
  have hb'B : Core.ixAddr b' = B := by
    have h0 : (memberProjection B 0 (.indc ind)).info = .iPrj ⟨(0 : Nat).toUInt64, B⟩ := rfl
    rw [h0] at hinfo'
    injection hinfo' with hpp
    injection hpp with _ hb
    exact hb.symm
  -- constructor `j`'s load
  have hjlt : j < ind.ctors.size := (Array.getElem?_eq_some_iff.mp hct).1
  have hK : ZMod.val ((ind.ctors.size : F) - 0) = ind.ctors.size := by
    rw [sub_zero]
    exact ZMod.val_natCast_of_lt (Nat.lt_trans hc56 (by decide))
  obtain ⟨cvF, hcvF⟩ : ∃ cvF : ConstantVal .anon, cvF.name = Core.keyOf t (Core.iprjAddr B 0) :=
    ⟨⟨Core.keyOf t (Core.iprjAddr B 0), [], .sort .zero⟩, rfl⟩
  obtain ⟨h1', h2', ptr, cs1', nl, ty, rest, eh1, eh2, evc, hsc, ldc, hfc⟩ :=
    Core.rs_scan_ctors (Decl.ctorStage ⟨E, env, t, lim⟩ cvF ({} : IndCaps .anon))
      (ind.ctors.size) hK ev3 hxs2 hrr j hjlt
  have evc' : ObsFn Core.W "Ingress::get_ci_cprj" [blkPtr, .field 0, .field ((j : Nat) : F)]
      h1' ptr h2' cs1' := by
    rw [Nat.cast_zero, zero_add] at evc
    exact evc
  have gc := good.sub (fun x hx => hs149 x (hs3 x (hsc x hx)))
  have hb'1 : Bytes.RepAddressRef Core.addrTy h1' b' blkPtr := Core.se_addrRep_mono eh1 hb'2
  have hblock' : recordOf E (Core.ixAddr b') = some cb := by
    rw [hb'B]
    exact hblock
  have hty' : (exprReader t (fun x => E.blobs.get? x) cb id
      (blockSelf t (Core.ixAddr b') #[.indc ind])).read ct.typ = .ok cty := by
    rw [hb'B]
    exact hty
  have hjF : ZMod.val ((j : Nat) : F) = j :=
    ZMod.val_natCast_of_lt (Nat.lt_trans (Nat.lt_trans hjlt hc56) (by decide))
  obtain ⟨tyPtr, blkPtr', b'', ty'', R', hldc, -, -, -, -, -, hcanon', -, -, -, htm⟩ :=
    LoadedReads.ctor_load_canon (ind := ind) ht gc.1 gc.2 hb'1 evc' hblock' hmuts (by simp)
      (by rw [hjF]; exact hct) (by rw [hjF]; exact hcidx) hty' hlbb hdef
  rw [ZMod.val_zero] at hcanon'
  have hty'' : ty'' = cty' := Option.some.inj (hcanon'.symm.trans hcanon)
  subst hty''
  rw [hldc] at ldc
  have hv2 := Except.ok.inj ldc
  simp only [Value.construct.injEq, List.cons.injEq, true_and] at hv2
  obtain ⟨-, rfl, -⟩ := hv2
  -- the stage's keying on the block's cells
  have hnt : ∀ T : Core.KKey, cvF.name ≠ Ix.Kernel.projTableName T := by
    rw [hcvF]
    exact fun _ => Decl.ne_projTableName_of_isBaseKey (Decl.isBaseKey_keyOf t _)
  have hfreshF : env.find? cvF.name = none := by
    rw [hcvF]
    exact hfresh
  have hused : ∀ i ∈ usedRefIdxs cb, ∀ x, cb.refs.toList[i]? = some x →
      (Decl.ctorStage ⟨E, env, t, lim⟩ cvF ({} : IndCaps .anon)).κ x = Core.keyOf t x ∧
        Core.ProjPermitted (Decl.ctorStage ⟨E, env, t, lim⟩ cvF ({} : IndCaps .anon)).κ x := by
    intro i hi x hx
    obtain ⟨ci, hci⟩ := hstored i hi x hx
    exact ctorStage_of_find hfreshF hnt hci
  have hrecur : ∀ x ∈ Ingress.blockRecurAddrs (Core.ixAddr b')
      (#[.indc ind] : Array Ixon.MutConst).toList,
      (Decl.ctorStage ⟨E, env, t, lim⟩ cvF ({} : IndCaps .anon)).κ x = Core.keyOf t x := by
    rw [hb'B]
    intro x hx
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hx
    obtain ⟨m, hm, rfl⟩ := LoadedReads.blockRecurAddrs_get hk
    have hk0 : k = 0 := by
      have hlt : k < 1 := (Array.getElem?_eq_some_iff.mp hm).1
      omega
    subst hk0
    have hmm : m = .indc ind := by simpa using hm.symm
    subst hmm
    rw [LoadedReads.memberAddr_indc]
    exact ctorStage_former hcvF
  have htmS := htm _ hused hrecur
  -- the loaded type's fields are clean
  have hfc' := hfc ⟨0, fun _ => .sort .zero, 0, _, (htmS 0 _).toTm⟩
  rw [ZMod.val_natCast_of_lt (Nat.lt_trans hp56 (by decide))] at hfc'
  obtain ⟨ds, q, hch, hq, hcl⟩ := hfc'
  have hE3 : Core.Tm (Decl.ctorStage ⟨E, env, t, lim⟩ cvF ({} : IndCaps .anon)).κ 0
      (fun _ => .sort .zero) h3 0 (Core.posOf (List.range ct.lvls.toNat) ty'') tyPtr :=
    Core.Tm.mono eh2 (htmS 0 _).toTm
  -- a constant at the former's key is the member; no projection is permitted there
  have hxk : ∀ a : Bytes.Address,
      (Decl.ctorStage ⟨E, env, t, lim⟩ cvF ({} : IndCaps .anon)).κ (Core.ixAddr a) =
        Core.keyOf t (Core.iprjAddr B 0) → Core.ixAddr a = Core.iprjAddr B 0 := by
    intro a ha
    have hne : (Decl.ctorStage ⟨E, env, t, lim⟩ cvF ({} : IndCaps .anon)).κ (Core.ixAddr a) ≠
        Core.unresolvedKey := by
      rw [ha]
      exact Core.Resolved.ne
    have hk := (Decl.ctorStage ⟨E, env, t, lim⟩ cvF ({} : IndCaps .anon)).key_eq hne
    exact Core.keyOf_inj htwf (hk.symm.trans ha)
  have hc : ∀ a : Bytes.Address,
      (Decl.ctorStage ⟨E, env, t, lim⟩ cvF ({} : IndCaps .anon)).κ (Core.ixAddr a) =
        Core.keyOf t (Core.iprjAddr B 0) → a ∈ xs := by
    intro a ha
    rw [Decl.ixAddr_inj ((hxk a ha).trans hxa₀.symm)]
    exact ha₀
  have hp : ∀ a : Bytes.Address,
      (Decl.ctorStage ⟨E, env, t, lim⟩ cvF ({} : IndCaps .anon)).κ (Core.ixAddr a) =
        Core.keyOf t (Core.iprjAddr B 0) →
      ¬ Core.ProjPermitted (Decl.ctorStage ⟨E, env, t, lim⟩ cvF ({} : IndCaps .anon)).κ
        (Core.ixAddr a) := by
    intro a ha
    rw [hxk a ha]
    have hne' : (ConstantInfo.indInfo cvF ({} : IndCaps .anon)).name ≠
        Core.keyOf t (Core.projMarker (Core.iprjAddr B 0)) := by
      intro e
      exact Core.iprjAddr_not_marker B 0
        ⟨Core.iprjAddr B 0, Core.keyOf_inj htwf (hcvF.symm.trans e)⟩
    exact Core.Ctx.stagedOver_not_projPermitted
      (c := Decl.consCtx ⟨E, env, t, lim⟩ (.indInfo cvF ({} : IndCaps .anon))) (pre := env)
      hfresh ((Ix.Kernel.EnvExt.find?_cons_ne (env := env) hne').trans (hkeys.marker_none _))
  -- the image's binder domains
  obtain ⟨⟨bsE, bodyE⟩, hsE⟩ := Option.isSome_iff_exists.mp
    (Ix.Kernel.Expr.stripPis_instantiateLevelParams_isSome (List.range ct.lvls.toNat)
      (Core.posLevels (List.range ct.lvls.toNat)) n (by rw [hs]; rfl))
  obtain ⟨-, hbsE⟩ := Ix.Kernel.Expr.stripPis_instantiateLevelParams_eq (List.range ct.lvls.toNat)
    (Core.posLevels (List.range ct.lvls.toNat)) n hs hsE
  have hdoms := Core.tm_fieldsClean_doms (d := 0) (Γ := fun _ => .sort .zero) (fun _ => rfl)
    hc hp hch hq ind.params.toNat hcl hE3
    n bsE bodyE hsE i hi hin
  have hlen : bs.length = n := Ix.Kernel.Expr.stripPis_length n hs
  have hlenE : bsE.length = n := Ix.Kernel.Expr.stripPis_length n hsE
  have hb0 : bs[i]? = some (bs[i]'(by omega)) := List.getElem?_eq_getElem (by omega)
  have hbE : bsE[i]? = some (bsE[i]'(by omega)) := List.getElem?_eq_getElem (by omega)
  have heq := hbsE i _ _ hb0 hbE
  rw [List.getD_eq_getElem?_getD, hbE, Option.getD_some, heq,
    Decl.mentionsConst_instantiateLevelParams] at hdoms
  rw [List.getD_eq_getElem?_getD, hb0, Option.getD_some]
  exact hdoms

/-- **The circuit's `is_rec` verdict other than `1` gives IxC's recursion flag `false`**: for
the classified kinds of stored constructors each of which is the canonical annotation of a
constructor slot's reading (as the named install stores them), at the family's key and the
record's parameter count. -/
theorem nativeIsRec_false_of_struct_is_rec {t : Ix.Kernel.RoleTable} (ht : t.check = .ok ())
    {E : Ixon.Env} (hdec : Ingress.EnvDecoded E) {env : Ix.Kernel.Env .anon} {lim : Option Nat}
    (hinv : Decl.PrefixInv E t lim env) (hkeys : HashKeyed t env)
    {B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive}
    (hblock : recordOf E B = some cb) (hmuts : cb.info = .muts #[.indc ind])
    (hproj : recordOf E (Core.iprjAddr B 0) = some (memberProjection B 0 (.indc ind)))
    (hstored : Decl.UsedRefsStored t env cb)
    (hfresh : env.find? (Core.keyOf t (Core.iprjAddr B 0)) = none)
    {sp v : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {sa : Bytes.Address}
    (ev : ObsFn Core.W "KernelWhnf::struct_is_rec" [sp] h v h' cs) (hv : v ≠ .field 1)
    (good : Core.Good ⟨E, env, t, lim⟩ cs)
    (hsa : Bytes.RepAddressRef Core.addrTy h sa sp) (hsaB : Core.ixAddr sa = Core.iprjAddr B 0)
    {T : Core.KKey} (hT : T = Core.keyOf t (Core.iprjAddr B 0)) {lps : List Ix.Kernel.LevelParam}
    {nP nIdx : Nat} (hnP : nP = ind.params.toNat) {ctorsA : List (ConstantVal .anon × Nat)}
    {kinds : List (List Ix.Kernel.RecFieldKind)}
    (hk : Ix.Kernel.classifyFixKinds (m := Ix.Kernel.CheckM .anon) T lps nP nIdx ctorsA =
      .ok kinds)
    (hctorsA : ∀ cA ∈ ctorsA, ∃ (j : Nat) (ct : Ixon.Constructor) (cty : Ix.Kernel.Expr .anon),
      ind.ctors[j]? = some ct ∧ ct.cidx.toNat = j ∧
      (exprReader t (fun x => E.blobs.get? x) cb id
        (blockSelf t B #[.indc ind])).read ct.typ = .ok cty ∧
      cty.looseBVarsBounded 0 = true ∧
      cty.allLevelParamsDefined (List.range ct.lvls.toNat) = true ∧
      LoadedReads.canonAnn cb (List.range ct.lvls.toNat)
        (((Ingress.mutsRootOffset (#[.indc ind] : Array Ixon.MutConst).toList 0 : Nat) : F) + 1 +
          ((j : Nat) : F)) ct.typ cty = some cA.1.type) :
    Ix.Kernel.nativeIsRec kinds = false := by
  subst hT hnP
  refine nativeIsRec_false_of_doms hk (fun cA hcA cbs body hs i hi => ?_)
  obtain ⟨j, ct, cty, h1, h2, h3, h4, h5, h6⟩ := hctorsA cA hcA
  exact struct_is_rec_doms ht hdec hinv hkeys hblock hmuts hproj hstored hfresh ev hv good hsa
    hsaB h1 h2 h3 h4 h5 h6 _ cbs body hs (ind.params.toNat + i) (Nat.le_add_right _ _)
    (by omega)

end IxVM.Refinement.Typing
