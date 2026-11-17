import IxVMRefinement.Assembly.NativeAliasFormer
import IxVMRefinement.Assembly.NativeAliasTeleWalk
import IxVMRefinement.Decl.ModeledAux

/-! # The telescope constant of a former declared at a definition, read at the prefix

At a native family, `check_inductive_shape` runs `former_tele_typed(rc, ty, nP + nI, nl, s)`
after the result-sort walk: at a former that is not syntactically its telescope it builds the
head-normalized telescope (`former_tele_at`), checks its scoping and types it as a sort. This
module reads that call at the prefix and produces the former stage's input
(`FormerAliasTeleC`, `FormerAliasTele` with its parameter clause asked at a family with a
constructor), over one named input:

* `FormerTeleConv` (named input): the paths `former_tele_typed` has once its second arm also
  asserts `k_is_def_eq(rc, ty, tele, []) = 1` (the circuit change proposed for a later batch). It
  holds of the regenerated circuit by inverting the regenerated path; it is not produced here.
* `formerAliasTeleC_of_member`: from the walked check of the block's member, at every native
  former: the telescope constant is the exact reading of the built term, checked from scratch at
  the prefix (`ConstantValCheckJ`: scoping by `validate_expr_well_scoped`, typing by
  `k_ensure_sort`), a telescope of the record's counts into a sort (`TeleShape`), definitionally
  equal to the declared former's annotated type (the conversion, by `Decl.scoped_core_defeq`), and,
  at a family with a constructor (whose parameter agreement walks the declared type's parameters
  as syntactic `Forall` cells), opening its parameters to the declared type's variables. At a
  former declared at its telescope, the declared former is its own telescope constant.
* `formerStageAlias_of_conv`: the former stage at an alias former (T6, second branch) over
  `FormerTeleConv` alone.

Why the parameter clause is asked only at a family with a constructor: at a family with none,
a `let` cell among the declared type's first `nP` cells is head-normalized by `former_tele_at`, and
the exact reading of the domain it builds is related to the declared type's only up to level
equivalence (`KernelWhnf::whnf`'s output is represented up to `LvEq`). The constructor stage, the
only reader of the clause, has a constructor.
-/

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal)
open Ix.Kernel.Semantics (ConstantValCheckJ)
open Ix.Kernel.Model (rulesJ nativePartsAt?)

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

universe u

/-! ## The named input -/

/-- **The paths of `former_tele_typed` with the conversion assertion** (named input). Every
observed derivation of `KernelCheck::former_tele_typed(rc, ty, k, nl, s)` either finds the former
syntactically a telescope (`former_is_tele = 1`), or builds the telescope `tele`
(`former_tele_at` on the empty context), checks its scoping (`validate_expr_well_scoped`), types it
as a sort (`k_ensure_sort`) and then finds `ty` and `tele` convertible
(`k_is_def_eq(rc, ty, tele, []) = 1`), with its calls in that order.

This is the content of the path lemma `Obs.«KernelCheck::former_tele_typed».obs` once the
circuit's `former_tele_typed` asserts the conversion after `k_ensure_sort` (proposed hunk: lane
notes, `stage3-alias-defeq.diff`); after that regeneration it is discharged by one `match` on the
two paths. The circuit at this commit does not assert the conversion, so this input is not
satisfied by it at a former declared at a definition. -/
def FormerTeleConv : Prop :=
  ∀ (rc ty k nl s : SourceValue F) (h : Heap F) (r : SourceValue F) (h' : Heap F)
    (cs : List (Call F)),
    ObsFn Core.W "KernelCheck::former_tele_typed" [rc, ty, k, nl, s] h r h' cs →
    (∃ (m2 : Heap F) (cs13 : List (Call F)),
      ObsFn Core.W "KernelCheck::former_is_tele" [ty, k] h (.field 1) m2 cs13 ∧
      r = .tuple [] ∧ h' = m2 ∧ cs = (⟨"KernelCheck::former_is_tele", [ty, k], h⟩ : Call F) :: cs13) ∨
    (∃ (v1 : SourceValue F) (m2 : Heap F) (cs13 : List (Call F)) (tele : SourceValue F)
        (m46 : Heap F) (cs56 : List (Call F)) (v105 : SourceValue F) (m106 : Heap F)
        (cs116 : List (Call F)) (v142 : SourceValue F) (m143 : Heap F) (cs153 : List (Call F))
        (mD : Heap F) (csD : List (Call F)),
      ObsFn Core.W "KernelCheck::former_is_tele" [ty, k] h v1 m2 cs13 ∧ v1 ≠ .field 1 ∧
      ObsFn Core.W "KernelCheck::former_tele_at"
        [rc, ty, k, .ptr (.enum Core.kexprListEnum) m2.length, s]
        (m2 ++ [.construct Core.kexprListEnum "Nil" []]) tele m46 cs56 ∧
      ObsFn Core.W "KernelCheck::validate_expr_well_scoped" [tele, .field 0, nl]
        m46 v105 m106 cs116 ∧
      ObsFn Core.W "KernelInfer::k_ensure_sort"
        [rc, tele, .ptr (.enum Core.kexprListEnum) m106.length]
        (m106 ++ [.construct Core.kexprListEnum "Nil" []]) v142 m143 cs153 ∧
      ObsFn Core.W "KernelDefEq::k_is_def_eq"
        [rc, ty, tele, .ptr (.enum Core.kexprListEnum) m143.length]
        (m143 ++ [.construct Core.kexprListEnum "Nil" []]) (.field 1) mD csD ∧
      r = .tuple [] ∧ h' = mD ∧
      cs = (⟨"KernelCheck::former_is_tele", [ty, k], h⟩ : Call F) :: (cs13 ++
        ((⟨"KernelCheck::former_tele_at", [rc, ty, k, .ptr (.enum Core.kexprListEnum) m2.length, s],
            m2 ++ [.construct Core.kexprListEnum "Nil" []]⟩ : Call F) :: (cs56 ++
        ((⟨"KernelCheck::validate_expr_well_scoped", [tele, .field 0, nl], m46⟩ : Call F) ::
          (cs116 ++
        ((⟨"KernelInfer::k_ensure_sort", [rc, tele, .ptr (.enum Core.kexprListEnum) m106.length],
            m106 ++ [.construct Core.kexprListEnum "Nil" []]⟩ : Call F) :: (cs153 ++
        ((⟨"KernelDefEq::k_is_def_eq",
            [rc, ty, tele, .ptr (.enum Core.kexprListEnum) m143.length],
            m143 ++ [.construct Core.kexprListEnum "Nil" []]⟩ : Call F) :: csD))))))))

/-! ## The former stage's input, with its parameter clause at a family with a constructor -/

/-- **`FormerAliasTele` with its parameter clause asked at a family with a constructor.** For the
reading `ty₀` of the former's type and its canonical annotation `ty'`: a telescope constant
(`AliasTele`) of the record's counts, which, at a family with a constructor, opens its parameters
as `ty'` does. -/
def FormerAliasTeleC (t : Ix.Kernel.RoleTable) (E : Ixon.Env) (B : _root_.Address)
    (cb : Ixon.Constant) (ind : Ixon.Inductive) (env : Ix.Kernel.Env .anon) : Prop :=
  ∀ ty₀ ty' : Ix.Kernel.Expr .anon,
    (exprReader t (fun x => E.blobs.get? x) cb id (blockSelf t B #[.indc ind])).read ind.typ
      = .ok ty₀ →
    LoadedReads.canonAnn cb (List.range ind.lvls.toNat)
      ((L1.mutsRootOffset (#[.indc ind] : Array Ixon.MutConst).toList 0 : Nat) : F) ind.typ ty₀
      = some ty' →
    ∃ (cvTa : ConstantVal .anon) (s : Ix.Kernel.Level),
      AliasTele env ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty₀⟩
        ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ cvTa
        (ind.params.toNat + ind.indices.toNat) s ∧
      (ind.ctors.size ≠ 0 →
        ∀ tfvs r₁, Ix.Kernel.openPisAtFvars ind.params.toNat ty' 0 = some (tfvs, r₁) →
          ∃ r₂, Ix.Kernel.openPisAtFvars ind.params.toNat cvTa.type 0 = some (tfvs, r₂))

/-- `FormerAliasTele` gives its variant with the parameter clause at a family with a
constructor. -/
theorem FormerAliasTele.toC {t : Ix.Kernel.RoleTable} {E : Ixon.Env} {B : _root_.Address}
    {cb : Ixon.Constant} {ind : Ixon.Inductive} {env : Ix.Kernel.Env .anon}
    (h : FormerAliasTele t E B cb ind env) : FormerAliasTeleC t E B cb ind env := by
  intro ty₀ ty' hty hcT
  obtain ⟨cvTa, s, hAT, hopen⟩ := h ty₀ ty' hty hcT
  exact ⟨cvTa, s, hAT, fun _ => hopen⟩

/-! ## The producer -/

section Producer

variable {t : Ix.Kernel.RoleTable} {calls : List (Call F)} {E₀ E : Ixon.Env}
  {bAddr B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive} {n : Nat}

/-- **The telescope constant of a native former, from its walked check** (`FormerAliasTeleC`),
over the named input `FormerTeleConv`. The other inputs are those of `formerChecked_of_member`
and the native route of the block. -/
theorem formerAliasTeleC_of_member {env : Ix.Kernel.Env .anon} (hconv : FormerTeleConv)
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : MutsMemberCheckedAtFullAt calls bAddr t B #[.indc ind] 0 n)
    (hnat : NativeRouteAt calls B)
    (hinv : Decl.PrefixInv.{u} E t (some n) env) (hstored : Decl.UsedRefsStored t env cb)
    (hfresh : env.find? (Core.keyOf t (Core.iprjAddr B 0)) = none)
    (hfree : Decl.KeyFree (Core.keyOf t (Core.iprjAddr B 0))) :
    FormerAliasTeleC t E B cb ind env := by
  intro ty₀ ty'₀ htyE hcT₀
  have hbound : Bounded calls := (hst.good env none).2
  obtain ⟨hty_lbb, hty_def, hfv⟩ := former_scope hbound hS hrec hchk htyE
  have hblock : recordOf E B = some cb :=
    (recordOf_eq_recordAt_of_decoded hst.decoded B).trans (hst.runRecord B cb hrec.record)
  have hproj : recordOf E (Core.iprjAddr B 0) = some (memberProjection B 0 (.indc ind)) :=
    (recordOf_eq_recordAt_of_decoded hst.decoded _).trans (hst.runRecord _ _ hrec.former)
  have hmuts : cb.info = .muts #[.indc ind] := hrec.muts
  have hunsafe : ind.isUnsafe = false := by
    have h := hrec.logic
    unfold InLogic at h
    rw [hrec.muts] at h
    exact (h (.indc ind) (by simp)).1
  -- the declared former, checked at the prefix
  obtain ⟨ty', hcT', -, hcheck, -⟩ := formerChecked_of_member ht hst hinv hblock hmuts
    hproj hchk htyE hty_lbb hty_def hfv hstored hfresh hfree
  have hty'eq : ty'₀ = ty' := Option.some.inj (hcT₀.symm.trans hcT')
  subst hty'eq
  -- the member's check, navigated as `formerChecked_of_member` does
  have hchkA := mutsMemberAt_checkedAt (mc := .indc ind) hbound hchk (by rfl)
  obtain ⟨h_pre, m_chk, h'_chk, rc, ap, ptr, v, r_chk, cs_load, cs_chk, hrc_pre, hrc_m, ha_pre,
    ha_m, ev_ld, hcl_ld, hsub_ld, hld, ev_chk, hcl_chk, hsub_chk⟩ := hchkA
  obtain ⟨a, ha, hax⟩ := ha_pre
  have hgood : Core.Good ⟨E, env, t, some n⟩ calls := hst.good env (some n)
  have hg_ld : Core.Good ⟨E, env, t, some n⟩ cs_load := hgood.sub hsub_ld
  have hg_chk : Core.Good ⟨E, env, t, some n⟩ cs_chk := hgood.sub hsub_chk
  have h0' : (⟨(0 : Nat).toUInt64, B⟩ : Ixon.InductiveProj).idx.toNat = 0 := by
    show ((0 : Nat).toUInt64).toNat = 0
    decide
  obtain ⟨rawBytes, c', hh, haddr, hex, htv, hres⟩ := L1.get_ci_block_trace_spec hg_ld.2 ha ev_ld
  have hrecA : recordOf E (Core.ixAddr a) = some (memberProjection B 0 (.indc ind)) := by
    rw [hax, LoadedReads.memberAddr_indc]
    exact hproj
  obtain ⟨lc, hget, hdecA⟩ := LoadedReads.recordOf_inv hrecA
  have hb : rawBytes = lc.rawBytes := Core.load_escape hget hg_ld.1 rawBytes hh haddr
  have hc : c' = memberProjection B 0 (.indc ind) := by
    rw [hb, hdecA] at hex
    exact (Except.ok.inj hex).symm
  subst hc
  unfold L1.GetCIBlockTraceResult at hres
  have hinfo : (memberProjection B 0 (.indc ind)).info = .iPrj ⟨(0 : Nat).toUInt64, B⟩ := rfl
  rw [hinfo] at hres
  obtain ⟨hidx, blkBytes, cb', ms', ind', blobs, tree, plan, v₀, hhB, haB, hexB, hcb, hms,
    hhp, built, planned, hld₀, hraw, hlev⟩ := hres
  obtain ⟨lcB, hgetB, hdecB⟩ := LoadedReads.recordOf_inv hblock
  have hbB : blkBytes = lcB.rawBytes := Core.load_escape hgetB hg_ld.1 blkBytes hhB haB
  have hcB : cb' = cb := by
    rw [hbB, hdecB] at hexB
    exact (Except.ok.inj hexB).symm
  subst cb'
  have hmsEq : ms' = #[.indc ind] := (Ixon.ConstantInfo.muts.inj (hcb.symm.trans hmuts))
  subst hmsEq
  rw [h0'] at hms planned hraw
  have hiEq : ind' = ind := by
    have e : (Ixon.MutConst.indc ind : Ixon.MutConst) = .indc ind' := Option.some.inj hms
    exact (Ixon.MutConst.indc.inj e).symm
  subst ind'
  have hvv : v₀ = v := Except.ok.inj (hld₀.symm.trans hld)
  subst v₀
  obtain ⟨hlvls, hp56, hi56, hc56, hidx56, tyPtr, blkPtr, b, hb_eq, hb_rep, hv, rty⟩ := hraw
  subst hv
  obtain ⟨count, typePtr, fields, shape, trace⟩ := hlev
  injection shape with _ _ hargs
  injection hargs with _ hrest
  injection hrest with htp _
  subst typePtr
  have hagree := LoadedReads.blobReadAgreement_of_noCollision hg_ld.1 hhp t
  obtain ⟨ty'', hcT'', hannT, htmT⟩ :=
    LoadedReads.annotation_canon_exact ht hlvls (LoadedReads.blockSelf_key t B #[.indc ind])
      hagree rty built planned trace htyE hty_lbb hty_def
  have hty'' : ty'' = ty'₀ := Option.some.inj (hcT''.symm.trans hcT')
  subst hty''
  obtain ⟨prelude⟩ := Decl.native_prelude_calls ev_chk
  have used : ∀ x, L1.RefUsed cb.refs.toList cb.sharing.toList ind.typ x →
      ∃ ci, env.find? (Core.keyOf t x) = some ci := by
    have hmem' : Ixon.MutConst.indc ind ∈ (#[.indc ind] : Array Ixon.MutConst).toList :=
      List.mem_singleton.mpr rfl
    intro x hu
    obtain ⟨i, hi | ⟨s, hs, his⟩, hr⟩ := hu
    · refine hstored i ?_ x hr
      unfold usedRefIdxs
      rw [hmuts]
      exact List.mem_append_right _
        (List.mem_flatMap.mpr ⟨.indc ind, hmem', by unfold mutRefIdxs; exact List.mem_append_left _ hi⟩)
    · refine hstored i ?_ x hr
      unfold usedRefIdxs
      exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨s, hs, his⟩)
  let cP : Core.ScopedCtx := Core.Ctx.stored ⟨E, env, t, some n⟩
  let κP := cP.κ
  have hextM : Heap.Extends m_chk prelude.mentionsBefore :=
    prelude.initialExtended.trans prelude.scope_to_mentions
  have hagreeP : ∀ a', Core.AddrIn m_chk tyPtr a' →
      κP (Core.ixAddr a') = Core.keyOf t (Core.ixAddr a') := by
    intro a' hin
    rcases rty.addrIn_used a' hin with hu | hr
    · obtain ⟨ci, hci⟩ := used _ hu
      exact Core.Ctx.stored_key_of_find (c := ⟨E, env, t, some n⟩) hci
    · exfalso
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
      obtain ⟨m, hm, hxm⟩ := LoadedReads.blockRecurAddrs_get hk
      have hk0 : k = 0 := by
        have hlt : k < 1 := (Array.getElem?_eq_some_iff.mp hm).1
        omega
      subst hk0
      have hmm : m = .indc ind := by simpa using hm.symm
      subst hmm
      rw [LoadedReads.memberAddr_indc] at hxm
      have hxm' : Core.ixAddr a' = Core.iprjAddr B 0 := hxm
      have hscan := mentions_block_cells (c := ⟨E, env, t, some n⟩) hst.decoded hblock hmuts hproj
        hb_eq hin hextM (prelude.blocksRep hb_rep) prelude.mentionsRun
        (hg_chk.sub prelude.mentionsSubset)
      rcases hscan with hp | hne
      · obtain ⟨ci, hci⟩ := used _ (rty.projIn_used a' hp)
        rw [hxm', hfresh] at hci
        cases hci
      · exact hne hxm'
  have hpermP : ∀ a', Core.ProjIn m_chk tyPtr a' →
      Core.ProjPermitted (Core.keyOf t) (Core.ixAddr a') → Core.ProjPermitted κP (Core.ixAddr a') := by
    intro a' hp _
    obtain ⟨ci, hci⟩ := used _ (rty.projIn_used a' hp)
    exact Core.Ctx.stored_projPermitted_of_find (c := ⟨E, env, t, some n⟩) hci
  have htmP : Decl.TmCExact κP m_chk (Core.posOf (List.range ind.lvls.toNat) ty'₀) tyPtr :=
    TmCExact.rekey htmT hagreeP hpermP
  rw [Decl.posOf_range] at htmP
  -- the native dispatch and the shape stage
  have hsafeF : L1.repBoolField ind.isUnsafe = .field 0 := by
    rw [hunsafe]
    rfl
  rw [hsafeF, Nat.cast_zero] at ev_chk
  rcases Decl.native_induct_dispatch ev_chk with hnative | modeled
  rotate_left
  · exfalso
    obtain ⟨before, result, after, children, obs, hne, hext, -, hsubc⟩ := modeled
    exact hne (hnat blkPtr result before after children b obs
      (fun cl hcl => hsub_chk cl (hsubc cl hcl))
      (Bytes.repAddressRef_heapMono₂ Core.addrTy hext hb_rep) hb_eq)
  obtain ⟨native⟩ := hnative
  have hgS : ∀ cs', (∀ x ∈ cs', x ∈ native.calls) → Core.CoreGood cP cs' := fun cs' hs =>
    Core.CoreGood.ofRaw (hg_chk.sub (fun x hx => native.subset x (hs x hx))) (fun _ _ => trivial)
  have hrcP : Core.RCRep t (some n) m_chk rc := hrc_m.toRCRep
  have hef := hinv.scopedCoreFacts.1
  have hlf := hinv.loads
  have hPI : ind.params.toNat + ind.indices.toNat < 18446744069414584321 := by omega
  match Obs.«KernelCheck::check_inductive_shape».obs native.observed with
  | .run (v1 := lvl) (m2 := sortAfter) (cs12 := sortCalls) (v17 := vS) (m50 := sortBefore)
      (m63 := guardAfter) (cs73 := guardCalls) (m133 := ctorBefore) (cs143 := teleCalls)
      (v148 := vT) (op46 := opS) (hm58 := hmS) (ev14 := sortRun) (ev75 := guardRun)
      (op178 := opT) (ev145 := teleRun) (ev200 := ctorRun) (hc288 := hcS) .. =>
    rw [Decl.evalBinOp_add_nat _ _ opS] at sortRun
    rw [Decl.evalBinOp_add_nat _ _ opT] at teleRun
    have e_sb : Heap.Extends m_chk sortBefore :=
      native.initialToShape.trans (by rw [hmS]; exact Heap.Extends.snoc _ _)
    have e_sa : Heap.Extends m_chk sortAfter := e_sb.trans sortRun.heap_extends
    have e_ga : Heap.Extends m_chk guardAfter := e_sa.trans guardRun.heap_extends
    have e_cb : Heap.Extends m_chk ctorBefore := e_ga.trans teleRun.heap_extends
    -- the result sort's level
    obtain ⟨ℓ, hℓ, -⟩ := Decl.get_result_sort_level_any_spec (c := cP)
      (ind.params.toNat + ind.indices.toNat) hPI (hrcP.mono e_sb)
      (by rw [hmS]; exact Decl.typesRep_alloc_nil κP (fun _ => default) native.before)
      (Decl.ghostScoped_zero _) hef hlf (hgS sortCalls (fun x hx => by rw [hcS]; simp [hx]))
      ((htmP 0 (fun _ => default)).toTm.mono e_sb) sortRun
    have hteleSub : ∀ x ∈ teleCalls, x ∈ native.calls := fun x hx => by rw [hcS]; simp [hx]
    rcases hconv _ _ _ _ _ _ _ _ _ teleRun with
      ⟨m2, cs13, evIs, -, -, -⟩ |
      ⟨v1, m2, cs13, tele, m46, cs56, v105, m106, cs116, v142, m143, cs153, mD, csD,
        evIs, hne1, evAt, evWs, evSort, evDq, -, hhD, hcT⟩
    · -- a former declared at its telescope: its own telescope constant
      obtain ⟨-, bs, s, hstT, -⟩ := Decl.former_is_tele_one_bounded_spec
        (ind.params.toNat + ind.indices.toNat) hPI ((htmP 0 (fun _ => default)).mono e_ga) evIs
      exact ⟨_, s, aliasTele_of_tele hcheck hstT, fun _ tfvs r₁ hop => ⟨r₁, hop⟩⟩
    · -- a former declared at a definition: the built telescope
      have e_m2 : Heap.Extends m_chk (m2 ++ [.construct Core.kexprListEnum "Nil" []]) :=
        e_ga.trans (evIs.heap_extends.trans (Heap.Extends.snoc _ _))
      obtain ⟨⟨R, hR⟩, hshape, hcells⟩ := Decl.former_tele_at_spec (c := cP)
        (ind.params.toNat + ind.indices.toNat) hPI (hrcP.mono e_m2)
        (Decl.typesRep_alloc_nil κP (fun _ => default) m2) (Decl.ghostScoped_zero _) hef hlf
        (hgS cs56 (fun x hx => hteleSub x (by rw [hcT]; simp [hx])))
        ((htmP 0 (fun _ => default)).toTm.mono e_m2)
        (hℓ.mono (sortRun.heap_extends.trans (guardRun.heap_extends.trans
          (evIs.heap_extends.trans (Heap.Extends.snoc _ _))))) evAt
      obtain ⟨E', hE'⟩ := Decl.Tm.exactify hR
      have e_ws : Heap.Extends m46 (m106 ++ [.construct Core.kexprListEnum "Nil" []]) :=
        evWs.heap_extends.trans (Heap.Extends.snoc _ _)
      have e_dq : Heap.Extends m46 (m143 ++ [.construct Core.kexprListEnum "Nil" []]) :=
        e_ws.trans (evSort.heap_extends.trans (Heap.Extends.snoc _ _))
      have e_end : Heap.Extends m46 ctorBefore := by
        rw [hhD]
        exact e_dq.trans evDq.heap_extends
      have e_m46 : Heap.Extends m_chk m46 := e_m2.trans evAt.heap_extends
      -- its shape
      obtain ⟨bs, l, hstE, -⟩ := Decl.TeleShape.stripPis_exact
        (ind.params.toNat + ind.indices.toNat) hshape hE'
      -- checked from scratch at the prefix
      have hlbbE : E'.looseBVarsBounded 0 = true := hE'.toTm.looseBVarsBounded
      have hfvE : E'.hasFvar = false := Decl.Tm.hasFvar_false hE'.toTm
      have hannE : Annotates E' E' := Decl.annotates_refl_of_noLetExpr
        (hE'.noLet (fun _ hlt => absurd hlt (Nat.not_lt_zero _)))
      have hvE : Decl.ValRepExact κP m46 (.field (ind.lvls.toNat : F)) tele
          ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, E'⟩ := by
        refine ⟨by simp, by simpa using hlvls, by simp, ?_⟩
        show Decl.TmCExact κP m46 (Core.posOf (List.range ind.lvls.toNat) E') tele
        rw [Decl.posOf_range]
        exact fun d Γ => hE'.of_depth_zero d
      obtain ⟨checkedT, -⟩ := Decl.constantValCheckJ_of_scoped (c := cP)
        (cv := ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, E'⟩)
        (cv' := ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, E'⟩)
        ⟨rfl, rfl, hannE⟩ hvE hlbbE hfvE hfresh hfree.1
        (Decl.isProjFnShape_of_isBaseKey (Decl.isBaseKey_keyOf t _)) hinv.store.store
        (Decl.PosSortLift.of_range rfl) evWs e_ws (hrcP.mono (e_m46.trans e_ws))
        (Decl.typesRep_alloc_nil κP (fun _ => default) m106) hef hlf
        (hgS cs153 (fun x hx => hteleSub x (by rw [hcT]; simp [hx]))) evSort
      -- convertible with the declared former's annotated type
      have hdq : Ix.Kernel.Rules.DefEq env 0 ty'₀ E' :=
        Decl.scoped_core_defeq (c := cP) (hrcP.mono (e_m46.trans e_dq))
          (Decl.typesRep_alloc_nil κP (fun _ => default) m143) (Decl.ghostScoped_zero _) hef hlf
          (hgS csD (fun x hx => hteleSub x (by rw [hcT]; simp [hx]))) evDq
          ((htmP 0 (fun _ => default)).toTm.mono (e_m46.trans e_dq))
          (hE'.toTm.mono e_dq)
      refine ⟨⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, E'⟩, l,
        ⟨⟨E', checkedT⟩, ⟨bs, hstE⟩, hdq⟩, ?_⟩
      -- the parameters, at a family with a constructor
      intro hnc tfvs r₁ hop
      obtain ⟨H, hH, hfc⟩ := Decl.check_inductive_shape_ctors_param_cells hnc (by omega)
        (by omega) ctorRun
      have hTC := hcells ind.params.toNat H (by omega) (e_end.trans hH) hfc
      have hpre := Decl.TeleCells.prefixEq ind.params.toNat hTC
        ((htmP 0 (fun _ => default)).mono (e_cb.trans hH)) (hE'.mono (e_end.trans hH))
      exact Decl.PrefixEq.openPisAtFvars ind.params.toNat hpre hop

end Producer

/-! ## The former stage over the conversion alone -/

section Stage

variable {t : Ix.Kernel.RoleTable} {calls : List (Call F)} {E₀ : Ixon.Env}
  {bAddr B : _root_.Address} {cb : Ixon.Constant} {ind : Ixon.Inductive} {n : Nat}

/-- **The former's stage at the prefix, at a former declared at a definition** (T6, second
branch), over `FormerAliasTeleC`: `formerStageAlias_of_member`'s statement, whose proof reads
only the telescope constant of the input. -/
theorem formerStageAlias_of_member_C {E : Ixon.Env} (ht : t.check = .ok ())
    (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : MutsMemberCheckedAtFullAt calls bAddr t B #[.indc ind] 0 n)
    {blk : List (ConstantInfo .anon)} (hblk : BlockReadings t E₀ B ind blk)
    {p₀ : Ix.Kernel.NativeParts .anon}
    (hp₀ : nativePartsAt? ind.params.toNat ind.indices.toNat blk = some p₀)
    (hnIdx : p₀.nIdx = ind.indices.toNat) (hn : ind.indices.toNat ≠ 0)
    {env : Ix.Kernel.Env .anon} (hinv : Decl.PrefixInv.{u} E t (some n) env)
    (hstored : Decl.UsedRefsStored t env cb)
    (hfresh : env.find? (Core.keyOf t (Core.iprjAddr B 0)) = none)
    (hfree : Decl.KeyFree (Core.keyOf t (Core.iprjAddr B 0)))
    (htele : FormerAliasTeleC t E B cb ind env) :
    ∀ isRec : Bool, ∃ (cvS cvTa : ConstantVal .anon) (s : Ix.Kernel.Level),
      Ix.Kernel.Semantics.SumIndRunJ rulesJ env p₀.toInductiveShape
        (fun p₁ => Ix.Kernel.nativeCapsAt p₁ isRec)
        ⟨.indInfo cvS (Ix.Kernel.nativeCapsAt (p₀.toInductiveShape.withSort s) isRec)
          :: env.consts⟩ cvTa (p₀.toInductiveShape.withSort s) ∧
      cvS.name = Core.keyOf t (Core.iprjAddr B 0) ∧ cvTa.name = cvS.name ∧
      cvTa.levelParams = cvS.levelParams := by
  intro isRec
  have hbound : Bounded calls := (hst.good env none).2
  obtain ⟨ty₀, caps, cs, rfl, hty, -, -⟩ := blockReads_shape ht hbound hS hrec hchk hblk
  obtain ⟨hlbb, hdef, hfv⟩ := former_scope hbound hS hrec hchk hty
  have hblockE : recordOf E B = some cb :=
    (recordOf_eq_recordAt_of_decoded hst.decoded B).trans (hst.runRecord B cb hrec.record)
  have hprojE : recordOf E (Core.iprjAddr B 0) = some (memberProjection B 0 (.indc ind)) :=
    (recordOf_eq_recordAt_of_decoded hst.decoded _).trans (hst.runRecord _ _ hrec.former)
  have htyE : (exprReader t (fun x => E.blobs.get? x) cb id
      (blockSelf t B #[.indc ind])).read ind.typ = .ok ty₀ :=
    ReaderReads.exprReader_mono (fun x b hb => hst.runBlob x b hb) hty
  obtain ⟨ty', hcT, -, hcheck, -⟩ := formerChecked_of_member ht hst hinv hblockE hrec.muts
    hprojE hchk htyE hlbb hdef hfv hstored hfresh hfree
  obtain ⟨caps₀, hshape, -, -, -, -, -⟩ := nativePartsAt?_inv hp₀
  injection hshape with hhead _
  injection hhead with hcv _
  have hcvT : p₀.toInductiveShape.cvT =
      ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty₀⟩ := hcv.symm
  obtain ⟨cvTa, s, hAT, -⟩ := htele ty₀ ty' htyE hcT
  have hn₀ : p₀.toInductiveShape.nIdx ≠ 0 := by
    show p₀.nIdx ≠ 0
    rw [hnIdx]
    exact hn
  have hnP : p₀.toInductiveShape.nP + p₀.toInductiveShape.nIdx =
      ind.params.toNat + ind.indices.toNat := by
    obtain ⟨-, -, hnP, -⟩ := nativePartsAt?_inv hp₀
    show p₀.nP + p₀.nIdx = _
    rw [hnP, hnIdx]
  have hchk' : ConstantValCheckJ rulesJ env p₀.toInductiveShape.cvT
      ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ := by
    rw [hcvT]
    exact hcheck
  have hAT' : AliasTele env p₀.toInductiveShape.cvT
      ⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩ cvTa
      (p₀.toInductiveShape.nP + p₀.toInductiveShape.nIdx) s := by
    rw [hcvT, hnP]
    exact hAT
  obtain ⟨⟨tyT, htyT⟩, -, -⟩ := hAT
  exact ⟨⟨Core.keyOf t (Core.iprjAddr B 0), List.range ind.lvls.toNat, ty'⟩, cvTa, s,
    sumIndRunJ_of_alias hchk' hAT' hn₀, rfl, htyT.name_eq, htyT.levelParams_eq⟩

/-- **The former stage at an alias former over the conversion alone**: with the named input
`FormerTeleConv` (the regenerated path of `former_tele_typed`), the stage holds from the walked
check of the member at the native route; every other input is one of the block step's. -/
theorem formerStageAlias_of_conv {E : Ixon.Env} (hconv : FormerTeleConv)
    (ht : t.check = .ok ())
    (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hrec : BlockUnitRecord E₀ B cb ind)
    (hchk : MutsMemberCheckedAtFullAt calls bAddr t B #[.indc ind] 0 n)
    (hnat : NativeRouteAt calls B)
    {blk : List (ConstantInfo .anon)} (hblk : BlockReadings t E₀ B ind blk)
    {p₀ : Ix.Kernel.NativeParts .anon}
    (hp₀ : nativePartsAt? ind.params.toNat ind.indices.toNat blk = some p₀)
    (hnIdx : p₀.nIdx = ind.indices.toNat) (hn : ind.indices.toNat ≠ 0)
    {env : Ix.Kernel.Env .anon} (hinv : Decl.PrefixInv.{u} E t (some n) env)
    (hstored : Decl.UsedRefsStored t env cb)
    (hfresh : env.find? (Core.keyOf t (Core.iprjAddr B 0)) = none)
    (hfree : Decl.KeyFree (Core.keyOf t (Core.iprjAddr B 0))) :
    ∀ isRec : Bool, ∃ (cvS cvTa : ConstantVal .anon) (s : Ix.Kernel.Level),
      Ix.Kernel.Semantics.SumIndRunJ rulesJ env p₀.toInductiveShape
        (fun p₁ => Ix.Kernel.nativeCapsAt p₁ isRec)
        ⟨.indInfo cvS (Ix.Kernel.nativeCapsAt (p₀.toInductiveShape.withSort s) isRec)
          :: env.consts⟩ cvTa (p₀.toInductiveShape.withSort s) ∧
      cvS.name = Core.keyOf t (Core.iprjAddr B 0) ∧ cvTa.name = cvS.name ∧
      cvTa.levelParams = cvS.levelParams :=
  formerStageAlias_of_member_C ht hS hst hrec hchk hblk hp₀ hnIdx hn hinv hstored hfresh hfree
    (formerAliasTeleC_of_member hconv ht hS hst hrec hchk hnat hinv hstored hfresh hfree)

end Stage

end IxVM.Refinement.Typing
