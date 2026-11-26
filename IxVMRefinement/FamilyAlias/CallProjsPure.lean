import IxVMRefinement.FamilyAlias.CallProjsAux
import IxVMRefinement.FamilyAlias.CallAdvice
import IxVMRefinement.FamilyAlias.CallLists
import IxVMRefinement.FamilyAlias.CallMembers
import IxVMRefinement.Decl.NativeFront
import IxVM.Obs.KernelModeled
import IxVM.Obs.KernelRoleSpec
import IxVMRefinement.Ingress.TraceRecords
import IxVMRefinement.Assembly.PointUseSites
import IxVMRefinement.FamilyGraph.ProducersRefs

/-! # Inversion of `KernelModeled::check_proj_pure` and its callees

Produces `ProjPureWitness` from an accepted observation of `KernelModeled::check_proj_pure`
inside `KernelModeled::check_family`, covering:

* `ProjsCtx`: ambient step/run context with loader wrappers (`getCI_of_stored`,
  `getCI_defn_of_aset`, `getCI_thm_of_aset`, `getIprj_of_famAt`, `getCprj_of_famAt`),
  record extraction (`recordAt_of_get_ci`, `recRecordAt_of_get_ci`), and `constsResolve`
  preservation;
* `rec_family_block_spec`, `rec_rule_ih_args_spec`, `find_aux_ctor_for_tag_spec`,
  `check_unpack_rebuild_args_spec`, `check_unpack_minors_spec`, `check_proj_nested_minor_spec`,
  `check_proj_pure_sort_poly_spec`;
* `check_proj_pure_rec_spec`, `check_proj_pure_defn_spec`, `check_proj_pure_body_spec`, and
  `check_proj_pure_spec`. -/

universe u

namespace IxVM.Refinement.Typing.FamilyAlias

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.Core
open IxVM.Refinement.Decl (ExprSemEq)
open IxVM.Refinement.KernelLevels (substLevel RepKLevel RepKLevelList)
open IxVM.Consistency
open IxVM (F)
open Ix.Kernel (Expr Level ConstantInfo ConstantVal RecRule LevelParam)
open Ix.Kernel.Semantics (NativeFam)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Section 1: Ambient context, rekeying, `constsResolve`, and loader wrappers -/

/-- Ambient run and step context shared across `check_projs` and `check_proj_pure`. -/
structure ProjsCtx where
  calls : List (Call F)
  bAddr : _root_.Address
  t : Ix.Kernel.RoleTable
  E₀ : Ixon.Env
  lim : Option Nat
  csFam : List (Call F)
  B : _root_.Address
  cb : Ixon.Constant
  rb : _root_.Address
  crb : Ixon.Constant
  adv : _root_.Address → Prop
  E : Ixon.Env
  env : Ix.Kernel.Env .anon
  Reg : NativeFam .anon → Prop
  advAs : List Bytes.Address
  ht : t.check = .ok ()
  hbd : Bounded calls
  hS : LoadedReads.RunStore calls E₀
  hH : LoadedReads.HashedRecordsStored calls E₀
  hSE : FamilyStepEnv.{u} FormerOpenTraceAt calls t E₀ lim B cb rb crb adv E env
  hreg : FamRegistryWith.{u} FormerOpenTraceAt t E env Reg
  hPre : ∀ e ∈ RoleVal.committedPreludeList, Ix.Cert.recordAt E e.1 = some e.2
  hadvCase :
    (∀ a, AdviceIn csFam a → adv a) ∨
    (∀ a, AdviceListedIn advAs a →
      adv a ∨ ∀ ca x, recordOf E₀ a = some ca → ¬ ConstAddrOf a ca x)

namespace ProjsCtx

def ctx (P : ProjsCtx.{u}) : Ctx := ⟨P.E, P.env, P.t, P.lim⟩

noncomputable def sc (P : ProjsCtx.{u}) : ScopedCtx := Ctx.stored P.ctx

theorem htwf (P : ProjsCtx.{u}) : P.t.wf = true := P.hSE.prefixInv.tableWf

theorem hwf (P : ProjsCtx.{u}) : Ix.Kernel.EnvWF P.env := P.hSE.prefixInv.store.store.wf

theorem hgood (P : ProjsCtx.{u}) : Good P.ctx P.calls := P.hSE.store.good P.env P.lim

theorem hgoodSub (P : ProjsCtx.{u}) {cs : List (Call F)} (hsub : ∀ cl ∈ cs, cl ∈ P.calls) :
    Good P.ctx cs :=
  P.hgood.sub hsub

theorem hcoreGoodSub (P : ProjsCtx.{u}) {cs : List (Call F)} (hsub : ∀ cl ∈ cs, cl ∈ P.calls) :
    CoreGood P.sc cs :=
  ⟨(P.hgoodSub hsub).1, (P.hgoodSub hsub).2, fun _ _ => trivial⟩

theorem hbdSub (P : ProjsCtx.{u}) {cs : List (Call F)} (hsub : ∀ cl ∈ cs, cl ∈ P.calls) :
    Bounded cs :=
  (P.hgoodSub hsub).2

theorem keyOf_ne_unresolved (P : ProjsCtx.{u}) (a : _root_.Address) :
    Core.keyOf P.t a ≠ Core.unresolvedKey := by
  intro h
  have hb := Decl.isBaseKey_keyOf P.t a
  rw [h] at hb
  exact absurd hb (by decide)

theorem sc_kappa_eq_of_isSome (P : ProjsCtx.{u}) {a : _root_.Address}
    (h : (P.env.find? (Core.keyOf P.t a)).isSome = true) :
    P.sc.κ a = Core.keyOf P.t a ∧ P.sc.κ a ≠ Core.unresolvedKey := by
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp h
  have hne : P.sc.κ a ≠ Core.unresolvedKey := P.hSE.prefixInv.loads.storedRes a ci hci
  rcases resKey_spec P.t (P.ctx.resolvesOver P.env) a with heq | hun
  · exact ⟨heq, hne⟩
  · exact absurd hun hne

theorem sc_kappa_eq_of_ne (P : ProjsCtx.{u}) {a : _root_.Address}
    (hne : P.sc.κ a ≠ Core.unresolvedKey) : P.sc.κ a = Core.keyOf P.t a := by
  rcases resKey_spec P.t (P.ctx.resolvesOver P.env) a with heq | hun
  · exact heq
  · exact absurd hun hne

theorem nonAux_keyOf (P : ProjsCtx.{u}) (a : _root_.Address) : Decl.NonAuxKey (Core.keyOf P.t a) :=
  Decl.isBaseKey_iff_nonAuxKey.mp (Decl.isBaseKey_keyOf P.t a)

theorem rekey_tm (P : ProjsCtx.{u}) {d : Nat} {Γ : Nat → KExpr} {h : Heap F} {k : Nat}
    {E : KExpr} {p : SourceValue F} (r : Tm P.sc.κ d Γ h k E p) :
    Tm (Core.keyOf P.t) d Γ h k E p := by
  have hres : ∀ x, Resolved (Core.keyOf P.t x) := fun x => ⟨P.keyOf_ne_unresolved x⟩
  have hperm : ∀ x, ProjPermitted (Core.keyOf P.t) x := fun x => ⟨P.keyOf_ne_unresolved (projMarker x)⟩
  induction r with
  | bvarLocal cell hs hi => exact .bvarLocal cell hs hi
  | bvarFree cell hs hk hd => exact .bvarFree cell hs hk hd
  | sort cell rl hu => exact .sort cell rl hu
  | @const k addr ap lsp a ls us res cell ra rls hus =>
    have heq := P.sc_kappa_eq_of_ne res.ne
    rw [heq]
    have : Resolved (Core.keyOf P.t (ixAddr a)) := hres (ixAddr a)
    exact .const cell ra rls hus
  | app cell _ _ ihf iha => exact .app cell ihf iha
  | lam cell _ _ rl iht ihb => exact .lam cell iht ihb rl
  | forallE cell _ _ rl iht ihb => exact .forallE cell iht ihb rl
  | letE cell _ _ _ iht ihv ihb => exact .letE cell iht ihv ihb
  | litNat cell rl hc => exact .litNat cell rl hc
  | litStr cell rb hs => exact .litStr cell rb hs
  | @proj k addr ap ep a i E res perm cell ra _ ihe =>
    have heq := P.sc_kappa_eq_of_ne res.ne
    rw [heq]
    have : Resolved (Core.keyOf P.t (ixAddr a)) := hres (ixAddr a)
    have : ProjPermitted (Core.keyOf P.t) (ixAddr a) := hperm (ixAddr a)
    exact .proj cell ra ihe

theorem rekey_tmC (P : ProjsCtx.{u}) {h : Heap F} {E : KExpr} {p : SourceValue F}
    (r : TmC P.sc.κ h E p) : TmC (Core.keyOf P.t) h E p :=
  fun d Γ => P.rekey_tm (r d Γ)

theorem rekey_rulesRep (P : ProjsCtx.{u}) {h : Heap F} {ps : List LevelParam}
    {j : Nat} {p : SourceValue F} {rls : List (RecRule .anon)}
    (r : RulesRep P.sc.κ h ps j p rls) : RulesRep (Core.keyOf P.t) h ps j p rls := by
  induction r with
  | nil cell => exact .nil cell
  | cons cell hr _ ih =>
    obtain ⟨rhs, rfl, hnf, htm⟩ := hr
    exact .cons cell ⟨rhs, rfl, hnf, P.rekey_tmC htm⟩ ih

theorem getCI_of_stored (P : ProjsCtx.{u}) {a : Bytes.Address} {ap ptr : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hstored : (P.env.find? (Core.keyOf P.t (ixAddr a))).isSome = true)
    (ha : Bytes.RepAddressRef addrTy h a ap)
    (ev : ObsFn Obs.W "Ingress::get_ci" [ap] h ptr h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ P.calls) :
    ∃ ci, P.env.find? (Core.keyOf P.t (ixAddr a)) = some ci ∧
      CIPtrRep P.sc.κ h' ptr ci := by
  obtain ⟨hκ, hne⟩ := P.sc_kappa_eq_of_isSome hstored
  obtain ⟨ci, hfind, hrep⟩ := P.hSE.prefixInv.loads.getCI ap ptr h h' cs a ev trivial hne
    (P.hcoreGoodSub hsub) ha
  change P.env.find? (P.sc.κ (ixAddr a)) = some ci at hfind
  rw [hκ] at hfind
  exact ⟨ci, hfind, hrep⟩

theorem recordAt_of_get_ci (P : ProjsCtx.{u}) {a : Bytes.Address} {ap ptr : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (ha : Bytes.RepAddressRef addrTy h a ap)
    (ev : ObsFn Obs.W "Ingress::get_ci" [ap] h ptr h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ P.calls) :
    ∃ (raw : ByteArray) (cm : Ixon.Constant),
      Ix.Cert.recordAt P.E (ixAddr a) = some cm ∧
      Hashed cs raw ∧ Address.blake3Pure raw = ixAddr a ∧
      Ixon.deConstantExact raw = .ok cm ∧ Ixon.deConstant raw = .ok cm := by
  obtain ⟨_, _, csLd, evLd, hsubLd⟩ := Ingress.get_ci_verified_subcall ev
  obtain ⟨_, raw, cm, hsz, hh, hb, hde, hex, -, -⟩ :=
    Claim.load_verified_constant_de ⟨a, ha, rfl⟩ evLd
  have hrec0 := Claim.recordOf_hashed P.hS P.hH
    (Core.hashed_mono (fun cl hcl => hsub cl (hsubLd cl hcl)) hh) hsz hde hex
  rw [hb] at hrec0
  exact ⟨raw, cm, P.hSE.store.runRecord _ _ hrec0, Core.hashed_mono hsubLd hh, hb, hex, hde⟩

theorem recordAt_of_get_ci_iprj (P : ProjsCtx.{u}) {b : Bytes.Address} {i : F}
    {bp ptr : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hb : Bytes.RepAddressRef addrTy h b bp)
    (ev : ObsFn Obs.W "Ingress::get_ci_iprj" [bp, .field i] h ptr h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ P.calls) :
    ∃ (cb : Ixon.Constant) (ms : Array Ixon.MutConst) (ind : Ixon.Inductive),
      Ix.Cert.recordAt P.E (ixAddr b) = some cb ∧ cb.info = .muts ms ∧
      ms[ZMod.val i]? = some (.indc ind) ∧
      ind.lvls.toNat < 4294967296 ∧ ind.params.toNat < 72057594037927936 ∧
      ind.indices.toNat < 72057594037927936 ∧ ind.ctors.size < 72057594037927936 ∧
      ZMod.val i < 72057594037927936 ∧
      ∃ v, loadValue h' ptr = .ok v ∧
        ∃ tyPtr blkPtr b', ixAddr b' = ixAddr b ∧ Bytes.RepAddressRef addrTy h' b' blkPtr ∧
          v = .construct kciEnum "Induct"
            [.field (ind.lvls.toNat : F), tyPtr,
             .field (ind.params.toNat : F), .field (ind.indices.toNat : F),
             .field (ind.ctors.size : F), Ingress.repBoolField ind.isUnsafe,
             blkPtr, .field (ZMod.val i : F)] := by
  obtain ⟨_, _, csLd, evLd, hsubLd⟩ := Ingress.get_ci_iprj_verified_subcall ev
  obtain ⟨_, raw, cb0, hsz, hh, hbl, hde, hex, -, -⟩ :=
    Claim.load_verified_constant_de ⟨b, hb, rfl⟩ evLd
  have hrec0 := Claim.recordOf_hashed P.hS P.hH
    (Core.hashed_mono (fun cl hcl => hsub cl (hsubLd cl hcl)) hh) hsz hde hex
  rw [hbl] at hrec0
  have hrecE := P.hSE.store.runRecord _ _ hrec0
  obtain ⟨_, hi56, blkBytes, cb, ms, ind, _, v, hh2, hbl2, hex2, _, hmuts, hms, _, hld, hraw⟩ :=
    Ingress.get_ci_iprj_spec (P.hbdSub hsub) hb ev
  have hcb_eq : cb = cb0 := by
    have hrecAt0 := (P.hS.recordOf_eq_recordAt (ixAddr b)).symm.trans hrec0
    exact P.hS.record_eq hrecAt0 (Core.hashed_mono hsub hh2) hbl2 hex2
  subst hcb_eq
  obtain ⟨hlv, hnp, hni, hnc, _, tyPtr, blkPtr, b', hb', hbrep, hv, -⟩ := hraw
  refine ⟨cb, ms, ind, hrecE, hmuts, by simpa using hms, hlv, hnp, hni, hnc, hi56,
    v, hld, tyPtr, blkPtr, b', hb', hbrep, hv⟩

theorem ctorRecordAt_of_get_ci (P : ProjsCtx.{u}) {a : Bytes.Address} {ap ptr : SourceValue F}
    {nl ty blk idx cidx np nf u : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ha : Bytes.RepAddressRef addrTy h a ap)
    (ev : ObsFn Obs.W "Ingress::get_ci" [ap] h ptr h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ P.calls)
    (hld : loadValue h' ptr = .ok (.construct kciEnum "Ctor" [nl, ty, blk, idx, cidx, np, nf, u])) :
    ∃ (cm cb : Ixon.Constant) (xs : Array Ixon.MutConst) (ind : Ixon.Inductive)
      (ct : Ixon.Constructor) (b : Bytes.Address) (i j : F),
      Ix.Cert.recordAt P.E (ixAddr a) = some cm ∧
      Ix.Cert.recordAt P.E (ixAddr b) = some cb ∧
      Bytes.RepAddressRef addrTy h' b blk ∧
      idx = .field i ∧ cidx = .field (ct.cidx.toNat : F) ∧
      ZMod.val i < 2 ^ 56 ∧ ZMod.val j < 2 ^ 56 ∧
      cm.info = .cPrj ⟨(ZMod.val i).toUInt64, (ZMod.val j).toUInt64, ixAddr b⟩ ∧
      cb.info = .muts xs ∧ xs[ZMod.val i]? = some (.indc ind) ∧
      ind.ctors[ZMod.val j]? = some ct := by
  obtain ⟨_, cm0, hrecCm, -, -, -, -⟩ := P.recordAt_of_get_ci ha ev hsub
  obtain ⟨_, _, cm, cb, xs, ind, ct, b, i, j, hh1, hb1, hex1, _,
    hh2, hb2, hex2, _, hbrep, hidx, hcidx, hi56, hj56, hinfo, hmuts, hxs, hct⟩ :=
    ctorRecord_raw_of_get_ci ev (P.hbdSub hsub) ha hld
  have hrecAt0 : Ix.Cert.recordAt P.E₀ (ixAddr a) = some cm0 := by
    obtain ⟨_, _, csLd, evLd, hsubLd⟩ := Ingress.get_ci_verified_subcall ev
    obtain ⟨_, raw', cm', hsz', hh', hb', hde', hex', -, -⟩ :=
      Claim.load_verified_constant_de ⟨a, ha, rfl⟩ evLd
    have hr := Claim.recordOf_hashed P.hS P.hH
      (Core.hashed_mono (fun cl hcl => hsub cl (hsubLd cl hcl)) hh') hsz' hde' hex'
    rw [hb'] at hr
    have e : cm' = cm0 := Option.some.inj ((P.hSE.store.runRecord _ _ hr).symm.trans hrecCm)
    subst e
    exact (P.hS.recordOf_eq_recordAt (ixAddr a)).symm.trans hr
  have hcm_eq : cm = cm0 := P.hS.record_eq hrecAt0 (Core.hashed_mono hsub hh1) hb1 hex1
  subst hcm_eq
  have header : ∀ {middle : Heap F} {cs1 : List (Call F)}
      {info sh rf un bd : SourceValue F},
      ObsFn Obs.W "Ingress::load_verified_constant" [ap] h
        (.construct "Ixon::Constant" "Mk" [info, sh, rf, un, bd]) middle cs1 →
      (∀ cl ∈ cs1, cl ∈ cs) →
      Claim.RepConstantInfo middle (.cPrj ⟨(ZMod.val i).toUInt64, (ZMod.val j).toUInt64, ixAddr b⟩) info := by
    intro middle cs1 info sh rf un bd ev14 hsub1
    obtain ⟨_, raw1, c1, hsz1, hh1', hb1', hde1', hex1', hcp1, -⟩ :=
      Claim.load_verified_constant_de ⟨a, ha, rfl⟩ ev14
    have hr1 := Claim.recordOf_hashed P.hS P.hH
      (Core.hashed_mono (fun cl hcl => hsub cl (hsub1 cl hcl)) hh1') hsz1 hde1' hex1'
    rw [hb1'] at hr1
    have hc1 : c1 = cm := Option.some.inj ((P.hSE.store.runRecord _ _ hr1).symm.trans hrecCm)
    subst hc1
    obtain ⟨iv1, _, _, _, _, hvc1, hir1, -⟩ := hcp1
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hvc1
    obtain ⟨_, _, rfl, -, -, -, -⟩ := hvc1
    rwa [hinfo] at hir1
  have wrong : ∀ {middle : Heap F} {tag : String} {fields : List (SourceValue F)},
      tag ≠ "CPrj" →
      Claim.RepConstantInfo middle (.cPrj ⟨(ZMod.val i).toUInt64, (ZMod.val j).toUInt64, ixAddr b⟩)
        (.construct "Ixon::ConstantInfo" tag fields) → False := by
    intro middle tag fields hne hrep
    obtain ⟨_, htag, _⟩ := hrep
    exact hne (Value.construct.inj htag).2.1
  have hrecCb : Ix.Cert.recordAt P.E (ixAddr b) = some cb := by
    match Obs.«Ingress::get_ci».obs ev with
    | .Defn_n0 (ev14 := ev14) (hc302 := hc) .. =>
      exact (wrong (by decide) (header ev14 (fun _ hcl => by rw [hc]; simp [hcl]))).elim
    | .Defn_other (ev14 := ev14) (hc423 := hc) .. =>
      exact (wrong (by decide) (header ev14 (fun _ hcl => by rw [hc]; simp [hcl]))).elim
    | .Axio (ev14 := ev14) (hc515 := hc) .. =>
      exact (wrong (by decide) (header ev14 (fun _ hcl => by rw [hc]; simp [hcl]))).elim
    | .Quot (ev14 := ev14) (hc606 := hc) .. =>
      exact (wrong (by decide) (header ev14 (fun _ hcl => by rw [hc]; simp [hcl]))).elim
    | .DPrj (ev14 := ev14) (hc675 := hc) .. =>
      exact (wrong (by decide) (header ev14 (fun _ hcl => by rw [hc]; simp [hcl]))).elim
    | .IPrj (ev14 := ev14) (hc750 := hc) .. =>
      exact (wrong (by decide) (header ev14 (fun _ hcl => by rw [hc]; simp [hcl]))).elim
    | .RPrj (ev14 := ev14) (hc926 := hc) .. =>
      exact (wrong (by decide) (header ev14 (fun _ hcl => by rw [hc]; simp [hcl]))).elim
    | .Recr (ev14 := ev14) (hc1071 := hc) .. =>
      exact (wrong (by decide) (header ev14 (fun _ hcl => by rw [hc]; simp [hcl]))).elim
    | .CPrj (ev14 := ev14) (ev822 := evIdx) (ev842 := evCidx) (ev800 := evCprj) (hc851 := hc851) .. =>
      have hir := header ev14 (fun _ hcl => by rw [hc851]; simp [hcl])
      obtain ⟨cpv, hcpv, hcpRep⟩ := hir
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hcpv
      obtain ⟨_, _, rfl⟩ := hcpv
      obtain ⟨blkPtr, hcpv2, b_blk, hb_blk_rep, hb_blk_eq⟩ := hcpRep
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hcpv2
      obtain ⟨_, _, -, -, rfl⟩ := hcpv2
      match Obs.«Ingress::get_ci_cprj».obs evCprj with
      | .run (cs12 := csBlk) (ev14 := evBlk) (hc381 := hcCprj) .. =>
        have extBlk := evIdx.heap_extends.trans evCidx.heap_extends
        obtain ⟨_, rawB, cB, hszB, hhB, hbB, hdeB, hexB, -, -⟩ :=
          Claim.load_verified_constant_de
            ⟨b_blk, Bytes.repAddressRef_heapMono₂ addrTy extBlk hb_blk_rep, rfl⟩ evBlk
        have hsubBlk : ∀ cl ∈ csBlk, cl ∈ P.calls := fun cl hcl =>
          hsub cl (by rw [hc851]; simp [hcCprj, hcl])
        have hrB := Claim.recordOf_hashed P.hS P.hH (Core.hashed_mono hsubBlk hhB) hszB hdeB hexB
        rw [hbB, hb_blk_eq] at hrB
        have hcB_eq : cb = cB := P.hS.record_eq ((P.hS.recordOf_eq_recordAt (ixAddr b)).symm.trans hrB)
          (Core.hashed_mono hsub hh2) hb2 hex2
        rw [hcB_eq]
        exact P.hSE.store.runRecord _ _ hrB
  exact ⟨cm, cb, xs, ind, ct, b, i, j, hrecCm, hrecCb, hbrep, hidx, hcidx, hi56, hj56,
    hinfo, hmuts, hxs, hct⟩

/-- Any advice address (`AdvChecked`) loaded by `Ingress::get_ci` as `Defn` or `Thm` is stored in
`P.env`, with `CIRep` at `P.sc.κ` (and `TmC` rekeyed to `Core.keyOf P.t`). -/
theorem getCI_defn_of_advChecked (P : ProjsCtx.{u}) {a : Bytes.Address}
    {ap ptr nl ty val sf hint : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hAdv : AdvChecked P.calls P.bAddr P.t P.lim P.csFam P.advAs a)
    (ha : Bytes.RepAddressRef addrTy h a ap)
    (ev : ObsFn Obs.W "Ingress::get_ci" [ap] h ptr h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ P.calls)
    (hld : loadValue h' ptr = .ok (.construct kciEnum "Defn" [nl, ty, val, sf, hint])) :
    ∃ (cv : ConstantVal .anon) (V : KExpr) (hn : Ix.Kernel.ReducibilityHint),
      Decl.NonAuxKey (Core.keyOf P.t (ixAddr a)) ∧
      P.env.find? (Core.keyOf P.t (ixAddr a)) = some (.defnInfo cv V hn) ∧
      nl = .field (cv.levelParams.length : F) ∧
      cv.levelParams.length < 4294967296 ∧
      cv.levelParams.Perm (List.range cv.levelParams.length) ∧
      TmC (Core.keyOf P.t) h' (Core.posOf cv.levelParams cv.type) ty ∧
      TmC (Core.keyOf P.t) h' (Core.posOf cv.levelParams V) val ∧
      cv.type.constsResolve P.env = true ∧ V.constsResolve P.env = true := by
  obtain ⟨cm, dm, hrecM, -, -, -, -, hcaM, -⟩ :=
    advice_defn_record P.hbd P.hS P.hH hAdv ha ev hsub (Or.inl rfl) hld
  have hadv := adv_of_advChecked hAdv hrecM hcaM P.hadvCase
  have hst := P.hSE.advStored (ixAddr a) hadv cm hrecM (ixAddr a) hcaM
  obtain ⟨ci, hfind, v, hld', hrep⟩ := P.getCI_of_stored hst ha ev hsub
  rw [hld] at hld'; injection hld' with hveq
  cases hrep with
  | defn hv hV =>
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hveq
    obtain ⟨_, _, rfl, rfl, rfl, rfl, rfl⟩ := hveq
    have hcwf := P.hwf _ (Ix.Kernel.Semantics.Env.find?_mem hfind)
    have hVwf := hcwf.2.2.2.2.1 _ _ _ rfl
    exact ⟨_, _, _, P.nonAux_keyOf (ixAddr a), hfind, hv.1, hv.2.1, hv.2.2.1,
      P.rekey_tmC hv.2.2.2, P.rekey_tmC hV, hcwf.2.2.1, hVwf.2.2.1⟩
  | _ => simp [kciEnum] at hveq

theorem getCI_thm_of_advChecked (P : ProjsCtx.{u}) {a : Bytes.Address}
    {ap ptr nl ty val : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hAdv : AdvChecked P.calls P.bAddr P.t P.lim P.csFam P.advAs a)
    (ha : Bytes.RepAddressRef addrTy h a ap)
    (ev : ObsFn Obs.W "Ingress::get_ci" [ap] h ptr h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ P.calls)
    (hld : loadValue h' ptr = .ok (.construct kciEnum "Thm" [nl, ty, val])) :
    ∃ (cv : ConstantVal .anon) (V : KExpr),
      Decl.NonAuxKey (Core.keyOf P.t (ixAddr a)) ∧
      P.env.find? (Core.keyOf P.t (ixAddr a)) = some (.thmInfo cv V) ∧
      nl = .field (cv.levelParams.length : F) ∧
      cv.levelParams.length < 4294967296 ∧
      cv.levelParams.Perm (List.range cv.levelParams.length) ∧
      TmC (Core.keyOf P.t) h' (Core.posOf cv.levelParams cv.type) ty ∧
      TmC (Core.keyOf P.t) h' (Core.posOf cv.levelParams V) val ∧
      cv.type.constsResolve P.env = true := by
  obtain ⟨cm, dm, hrecM, -, -, -, -, hcaM, -⟩ :=
    advice_defn_record P.hbd P.hS P.hH hAdv ha ev hsub (Or.inr rfl) hld
  have hadv := adv_of_advChecked hAdv hrecM hcaM P.hadvCase
  have hst := P.hSE.advStored (ixAddr a) hadv cm hrecM (ixAddr a) hcaM
  obtain ⟨ci, hfind, v, hld', hrep⟩ := P.getCI_of_stored hst ha ev hsub
  rw [hld] at hld'; injection hld' with hveq
  cases hrep with
  | thm hv hV =>
    simp only [Value.construct.injEq, List.cons.injEq, and_true] at hveq
    obtain ⟨_, _, rfl, rfl, rfl⟩ := hveq
    have hcwf := P.hwf _ (Ix.Kernel.Semantics.Env.find?_mem hfind)
    exact ⟨_, _, P.nonAux_keyOf (ixAddr a), hfind, hv.1, hv.2.1, hv.2.2.1,
      P.rekey_tmC hv.2.2.2, P.rekey_tmC hV, hcwf.2.2.1⟩
  | _ => simp [kciEnum] at hveq

theorem advChecked_of_aset_member (P : ProjsCtx.{u}) {aset ap : SourceValue F} {a : Bytes.Address}
    {h h' : Heap F} {cs : List (Call F)}
    (haset : AddrMapAll addrMapEnum (fun _ k _ =>
      AdvChecked P.calls P.bAddr P.t P.lim P.csFam P.advAs k) h aset)
    (ha : Bytes.RepAddressRef addrTy h a ap)
    (ev : ObsFn Obs.W "KernelClaim::addr_set_member" [ap, aset] h (.field 1) h' cs) :
    AdvChecked P.calls P.bAddr P.t P.lim P.csFam P.advAs a :=
  Decl.addr_set_member_one_scoped (c := ScopedCtx.unrestricted ⟨P.E₀, .empty, P.t, P.lim⟩)
    P.htwf ha haset ev

theorem nativeAt_of_block_is_modeled_zero (P : ProjsCtx.{u}) {b : Bytes.Address}
    {bp : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hb : Bytes.RepAddressRef addrTy h b bp)
    (ev : ObsFn Obs.W "KernelModeled::block_is_modeled" [bp] h (.field 0) h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ P.calls) :
    NativeAt P.E (ixAddr b) :=
  nativeAt_of_obs (c := P.ctx) ev (P.hgoodSub hsub) hb

end ProjsCtx

/-! ### `constsResolve` preservation and pure helpers -/

theorem constsResolve_stripLams {env : Ix.Kernel.Env .anon} :
    ∀ {n : Nat} {e rem : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)},
      e.constsResolve env = true → e.stripLams n = some (bs, rem) →
      rem.constsResolve env = true
  | 0, _, _, _, hcr, hs => by
    injection hs with hp; injection hp with _ hr; subst hr; exact hcr
  | n + 1, .lam _ b _, rem, bs, hcr, hs => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    simp only [Expr.stripLams] at hs
    cases hsb : b.stripLams n with
    | none => simp [hsb] at hs
    | some p =>
      rcases p with ⟨bs₀, rem₀⟩
      rw [hsb] at hs; injection hs with hp; injection hp with _ hr; dsimp only at hr; subst hr
      exact constsResolve_stripLams hcr.2 hsb
  | _ + 1, .bvar _, _, _, _, hs | _ + 1, .fvar _ _, _, _, _, hs | _ + 1, .sort _, _, _, _, hs
  | _ + 1, .const _ _, _, _, _, hs | _ + 1, .app _ _, _, _, _, hs | _ + 1, .forallE _ _ _, _, _, _, hs
  | _ + 1, .letE _ _ _ _, _, _, _, hs | _ + 1, .lit _, _, _, _, hs | _ + 1, .proj _ _ _, _, _, _, hs =>
    nomatch hs

theorem constsResolve_stripPis {env : Ix.Kernel.Env .anon} :
    ∀ {n : Nat} {e rem : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)},
      e.constsResolve env = true → e.stripPis n = some (bs, rem) →
      rem.constsResolve env = true ∧ ∀ bm ∈ bs, bm.1.constsResolve env = true
  | 0, _, _, _, hcr, hs => by
    injection hs with hp; injection hp with h1 h2; subst h1 h2
    exact ⟨hcr, fun _ hm => nomatch hm⟩
  | n + 1, .forallE ty b _, rem, bs, hcr, hs => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    simp only [Expr.stripPis] at hs
    cases hsb : b.stripPis n with
    | none => simp [hsb] at hs
    | some p =>
      rcases p with ⟨bs₀, rem₀⟩
      rw [hsb] at hs; injection hs with hp; injection hp with h1 h2; dsimp only at h1 h2; subst h1 h2
      obtain ⟨hrem, hbs⟩ := constsResolve_stripPis hcr.2 hsb
      refine ⟨hrem, fun bm hbm => ?_⟩
      rcases List.mem_cons.mp hbm with rfl | hmem
      · exact hcr.1
      · exact hbs bm hmem
  | _ + 1, .bvar _, _, _, _, hs | _ + 1, .fvar _ _, _, _, _, hs | _ + 1, .sort _, _, _, _, hs
  | _ + 1, .const _ _, _, _, _, hs | _ + 1, .app _ _, _, _, _, hs | _ + 1, .lam _ _ _, _, _, _, hs
  | _ + 1, .letE _ _ _ _, _, _, _, hs | _ + 1, .lit _, _, _, _, hs | _ + 1, .proj _ _ _, _, _, _, hs =>
    nomatch hs

theorem constsResolve_instantiate1 {env : Ix.Kernel.Env .anon} {v : KExpr}
    (hv : v.constsResolve env = true) :
    ∀ (e : KExpr) (idx : Nat), e.constsResolve env = true →
      (e.instantiate1 v idx).constsResolve env = true :=
  fun _ idx h => Ix.Kernel.Expr.constsResolve_instantiate1_gen hv idx h

theorem constsResolve_stripPisZeta {env : Ix.Kernel.Env .anon} {n d : Nat} {e rem : KExpr}
    (hsz : StripPisZeta n d e rem) (hcr : e.constsResolve env = true) :
    rem.constsResolve env = true := by
  induction hsz with
  | zero _ _ => exact hcr
  | forallE _ _ _ _ _ _ _ ih =>
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    exact ih (constsResolve_instantiate1 (v := .fvar _ (.sort .zero)) rfl _ 0 hcr.2)
  | letE _ _ _ _ _ _ _ _ ih =>
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    exact ih (constsResolve_instantiate1 hcr.1.2 _ 0 hcr.2)

theorem constsResolve_mkAppN {env : Ix.Kernel.Env .anon} :
    ∀ {H : KExpr} {args : List KExpr},
      (Expr.mkAppN H args).constsResolve env = true →
      H.constsResolve env = true ∧ ∀ a ∈ args, a.constsResolve env = true
  | H, [], h => ⟨h, fun _ hm => nomatch hm⟩
  | H, a :: rest, h => by
    obtain ⟨ha, hrest⟩ := constsResolve_mkAppN (H := .app H a) (args := rest) h
    simp only [Expr.constsResolve, Bool.and_eq_true] at ha
    refine ⟨ha.1, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hm
    · exact ha.2
    · exact hrest x hm

theorem constsResolve_lastBinderDom {env : Ix.Kernel.Env .anon} :
    ∀ {e d : KExpr}, e.constsResolve env = true → lastBinderDom e = some d →
      d.constsResolve env = true
  | .forallE ty b _, d, hcr, hl => by
    simp only [Expr.constsResolve, Bool.and_eq_true] at hcr
    unfold lastBinderDom at hl
    cases hb : b with
    | forallE _ _ _ =>
      rw [hb] at hl hcr
      exact constsResolve_lastBinderDom hcr.2 hl
    | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ | letE _ _ _ _
    | lit _ | proj _ _ _ =>
      rw [hb] at hl; injection hl with h; subst h; exact hcr.1
  | .bvar _, _, _, hl | .fvar _ _, _, _, hl | .sort _, _, _, hl | .const _ _, _, _, hl
  | .app _ _, _, _, hl | .lam _ _ _, _, _, hl | .letE _ _ _ _, _, _, hl | .lit _, _, _, hl
  | .proj _ _ _, _, _, hl => nomatch hl

theorem find_isSome_of_constsResolve_const {env : Ix.Kernel.Env .anon} {k : KKey}
    {us : List KLevel} (h : (Expr.const k us).constsResolve env = true) :
    (env.find? k).isSome = true := h

/-- Build parameter level list `[Param start, ..., Param (start + n - 1)]`. -/
private theorem build_param_lvls_range_go_le :
    ∀ (rem start i : Nat) {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      start + i + rem ≤ 4294967296 →
      ObsFn Obs.W "KernelCheck::build_param_lvls_range"
        [.field (start : F), .field ((i + rem : Nat) : F), .field (i : F)] h r h' cs →
      RepKLevelList h' ((List.range rem).map fun k => Level.param (start + (i + k))) r
  | 0, start, i, r, h, h', cs, _, ev => by
    match Obs.«KernelCheck::build_param_lvls_range».obs ev with
    | .n0 (he28 := hr) (hm27 := hh) .. =>
      subst hr hh
      have hnil : RepKLevelList
          (h ++ [.construct KernelLevels.klevelListEnum "Nil" []]) []
          (.ptr (.enum KernelLevels.klevelListEnum) h.length) := .nil (by simp)
      rwa [← klevelListEnum_eq] at hnil
    | .other (op17 := op17) (hne33 := hne33) .. =>
      simp only [Nat.add_zero, evalBinOp, sub_self, Except.ok.injEq] at op17
      exact absurd op17.symm hne33
  | rem + 1, start, i, r, h, h', cs, hlt, ev => by
    have hdiff_ne : ((i + (rem + 1) : Nat) : F) - (i : F) ≠ 0 := by
      rw [Nat.cast_add, add_sub_cancel_left]
      intro heq
      have hv := congrArg ZMod.val heq
      rw [ZMod.val_zero, val_natCast_wide_p (by omega)] at hv
      omega
    match Obs.«KernelCheck::build_param_lvls_range».obs ev with
    | .n0 (op17 := op17) .. =>
      simp only [evalBinOp, Except.ok.injEq, Value.field.injEq] at op17
      exact absurd op17 hdiff_ne
    | .other (v46 := v46) (m48 := m48) (v60 := v60) (m78 := m78) (v91 := v91)
        (he41 := hr) (hm40 := hh) (hm56 := hm56) (op74 := op74) (op119 := op119)
        (ev88 := ev88) .. =>
      subst hr hh
      have hv60 : v60 = .field ((start + i : Nat) : F) := by
        simp only [evalBinOp, Except.ok.injEq] at op74
        rw [← op74, Nat.cast_add]
      have hv91 : v91 = .field ((i + 1 : Nat) : F) := by
        simp only [evalBinOp, Except.ok.injEq] at op119
        rw [← op119, Nat.cast_add, Nat.cast_one]
      rw [hv91, show i + (rem + 1) = (i + 1) + rem by omega] at ev88
      have htl := build_param_lvls_range_go_le rem start (i + 1) (by omega) ev88
      have hhd_m48 : RepKLevel m48 (.param (start + i))
          (.ptr (.enum "KernelTypes::KLevelNode") h.length) := by
        rw [hm56, hv60]
        exact .param (by omega) (by simp)
      have hhd_m78 := hhd_m48.mono ev88.heap_extends
      have ext_end : Heap.Extends m78
          (m78 ++ [.construct Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>» "Cons"
            [.ptr (.enum "KernelTypes::KLevelNode") h.length, v46]]) := Heap.Extends.snoc _ _
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      have hmap_eq :
          List.map ((fun k => Level.param (start + (i + k))) ∘ Nat.succ) (List.range rem) =
          List.map (fun k => Level.param (start + (i + 1 + k))) (List.range rem) := by
        apply List.map_congr_left; intro k _
        simp only [Function.comp_apply]
        apply congrArg Level.param
        show (start + (i + k.succ) : Nat) = start + (i + 1 + k)
        omega
      rw [Nat.add_zero, hmap_eq]
      have hcons : RepKLevelList
          (m78 ++ [.construct Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>» "Cons"
            [.ptr (.enum "KernelTypes::KLevelNode") h.length, v46]])
          (.param (start + i) :: (List.range rem).map fun k => Level.param (start + (i + 1 + k)))
          (.ptr (.enum KernelLevels.klevelListEnum) m78.length) :=
        .cons (by rw [← klevelListEnum_eq]; simp)
          (hhd_m78.mono ext_end)
          (htl.mono ext_end)
      rwa [← klevelListEnum_eq] at hcons

theorem build_param_lvls_range_start {start n : Nat} {r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hlt : start + n ≤ 4294967296)
    (ev : ObsFn Obs.W "KernelCheck::build_param_lvls_range"
      [.field (start : F), .field (n : F), .field 0] h r h' cs) :
    RepKLevelList h' ((List.range n).map fun k => Level.param (start + k)) r := by
  have h1 := build_param_lvls_range_go_le n start 0 (by omega) (by simpa using ev)
  simpa using h1

/-- `KernelLevels::level_is_not_zero = 1` on `RepKLevel h ℓ p` certifies `∀ φ, pwBit φ ℓ.zeronessOf > 0`. -/
theorem pwBit_pos_of_level_is_not_zero {ℓ : KLevel} {p : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hrep : RepKLevel h ℓ p)
    (ev : ObsFn Obs.W "KernelLevels::level_is_not_zero" [p] h (.field 1) h' cs) :
    ∀ φ, Ix.Kernel.Model.pwBit φ ℓ.zeronessOf > 0 := by
  have hnz := IxVM.Refinement.Levels.levelIsNotZero_step ev _ rfl ℓ hrep
  have hnz_b : Ix.Kernel.Level.isNeverZero ℓ = true := by
    cases h0 : Ix.Kernel.Level.isNeverZero ℓ
    · rw [h0] at hnz; exact absurd (Value.field.inj hnz.1) one_ne_zero
    · rfl
  intro φ
  have hne := IxVM.Refinement.KernelLevels.isNeverZero_eval_ne_zero hnz_b φ
  unfold Ix.Kernel.Model.pwBit
  have hh : ℓ.zeronessOf.holds φ = false := by
    rw [Ix.Kernel.PropWhen.zeronessOf_sound]
    simp [hne]
  rw [hh]; simp

/-- `KernelLevels::pw_eq = 1` gives exact equivalence of level zeroness and `pwBit = 0`. -/
theorem eval_zero_iff_pwBit_zero_of_pw_eq {l ℓ : KLevel} {pl pℓ : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hl : RepKLevel h l pl) (hℓ : RepKLevel h ℓ pℓ)
    (ev : ObsFn Obs.W "KernelLevels::pw_eq" [pl, pℓ] h (.field 1) h' cs) :
    ∀ φ, l.eval φ = 0 ↔ Ix.Kernel.Model.pwBit φ ℓ.zeronessOf = 0 := by
  have hpw := Decl.pw_eq_one hl hℓ ev
  intro φ
  have hhold := congrArg (fun p => p.holds φ) hpw
  rw [Ix.Kernel.PropWhen.zeronessOf_sound] at hhold
  unfold Ix.Kernel.Model.pwBit
  rw [← hhold]
  cases h0 : (l.eval φ == 0) with
  | true => simp [beq_iff_eq.mp h0]
  | false =>
    have hne : l.eval φ ≠ 0 := by
      intro heq; rw [heq] at h0; simp at h0
    simp [hne]

/-- `KernelLevels::level_is_not_zero = 1` on `RepKLevel h l p` gives `∀ φ, l.eval φ > 0`. -/
theorem eval_pos_of_level_is_not_zero {l : KLevel} {p : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hl : RepKLevel h l p)
    (ev : ObsFn Obs.W "KernelLevels::level_is_not_zero" [p] h (.field 1) h' cs) :
    ∀ φ, l.eval φ > 0 := by
  have hnz := IxVM.Refinement.Levels.levelIsNotZero_step ev _ rfl l hl
  have hnz_b : Ix.Kernel.Level.isNeverZero l = true := by
    cases h0 : Ix.Kernel.Level.isNeverZero l
    · rw [h0] at hnz; exact absurd (Value.field.inj hnz.1) one_ne_zero
    · rfl
  intro φ
  have hne := IxVM.Refinement.KernelLevels.isNeverZero_eval_ne_zero hnz_b φ
  omega

/-! ### Convenience list, spine, and `bvars_desc` wrappers -/

private theorem kexprList_length_bd {R : Heap F → KExpr → SourceValue F → Prop}
    {xs : List KExpr} {l r : SourceValue F} {h h' : Heap F} {cs csAll : List (Call F)}
    (hl : RepList kexprListEnum R h xs l) (hbd : Bounded csAll)
    (hmem : (⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [l], h⟩ : Call F) ∈ csAll)
    (ev : ObsFn Obs.W Obs.Names.«Lists::length<&KernelTypes::KExprNode>» [l] h r h' cs) :
    r = .field (xs.length : F) ∧ xs.length < 2 ^ 39 ∧ h' = h := by
  obtain ⟨hr, hh⟩ := kexprList_length_spec ev hl
  exact ⟨hr, RomBound.bounded_length_lt hbd hmem (by simp) hl, hh⟩

private theorem klevelList_length_bd {ls : List KLevel} {l r : SourceValue F}
    {h h' : Heap F} {cs csAll : List (Call F)}
    (hl : RepKLevelList h ls l) (hbd : Bounded csAll)
    (hmem : (⟨Obs.Names.«Lists::length<&KernelTypes::KLevelNode>», [l], h⟩ : Call F) ∈ csAll)
    (ev : ObsFn Obs.W Obs.Names.«Lists::length<&KernelTypes::KLevelNode>» [l] h r h' cs) :
    r = .field (ls.length : F) ∧ ls.length < 2 ^ 39 ∧ h' = h := by
  obtain ⟨hr, hh⟩ := klevelList_length_spec ev hl
  exact ⟨hr, RomBound.bounded_length_lt hbd hmem (by simp) hl, hh⟩

private theorem klevelList_lookup_spec {ls : List KLevel} {l r : SourceValue F} {i : F}
    {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn Obs.W Obs.Names.«Lists::lookup<&KernelTypes::KLevelNode>» [l, .field i] h r h' cs)
    (hl : RepKLevelList h ls l) :
    (∃ lv, ls[i.val]? = some lv ∧ RepKLevel h lv r) ∧ h' = h := by
  rw [← Obs.Names.«Lists::lookup<&KernelTypes::KLevelNode>».symbol] at ev
  change RepList KernelLevels.klevelListEnum RepKLevel h ls l at hl
  rw [Levels.klevelList_names, ← Obs.Names.«Lists::Node<&KernelTypes::KLevelNode>».symbol] at hl
  exact Lib.Lists.lookup_spec ev hl

private theorem collect_spine_tuple_tm {κ : _root_.Address → KKey} {d : Nat} {Γ : Nat → KExpr}
    {e hd sp : SourceValue F} {h h' : Heap F} {cs : List (Call F)} {k : Nat} {E : KExpr}
    (ev : ObsFn Obs.W "KernelTypes::collect_spine" [e] h (.tuple [hd, sp]) h' cs)
    (hE : Tm κ d Γ h k E e) :
    ∃ H As, E = Expr.mkAppN H As ∧ Tm κ d Γ h' k H hd ∧
      RepList kexprListEnum (fun h A p => Tm κ d Γ h k A p) h' As sp := by
  obtain ⟨hd', sp', H, As, htup, hH, hAs, hEq⟩ := collect_spine_tm ev hE
  simp only [Value.tuple.injEq, List.cons.injEq, and_true] at htup
  obtain ⟨rfl, rfl⟩ := htup
  exact ⟨H, As, hEq, hH, hAs⟩

private theorem bvar_of_load_d0 {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {h : Heap F}
    {k : Nat} {E : KExpr} {p x : SourceValue F} (rep : Tm κ 0 Γ h k E p)
    (hl : loadValue h p = .ok (.construct kexprEnum "BVar" [x])) :
    ∃ i : F, x = .field i ∧ ZMod.val i < 9223372036854775808 ∧ ZMod.val i < k ∧
      E = .bvar (ZMod.val i) := by
  obtain ⟨i, hx, hsm, ⟨hlt, heq⟩ | ⟨_, hd, _⟩⟩ := rep.bvar_of_load hl
  · exact ⟨i, hx, hsm, hlt, heq⟩
  · omega

private theorem bvars_desc_tm_nat {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {k : Nat}
    {start cnt : Nat} {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (hcnt : cnt ≤ start) (hstart : start ≤ k) (hk : k < 4611686018427387904)
    (ev : ObsFn Obs.W "KernelModeled::bvars_desc" [.field (start : F), .field (cnt : F)] h r h' cs) :
    RepList kexprListEnum (fun h E p => Tm κ 0 Γ h k E p) h'
      ((List.range cnt).map fun m => .bvar (start - 1 - m)) r := by
  have hc : ZMod.val (cnt : F) = cnt := val_natCast_wide_p (by omega)
  have hs : ZMod.val (start : F) = start := val_natCast_wide_p (by omega)
  have h1 := bvars_desc_tm (κ := κ) (Γ := Γ) (k := k) (top := (start : F)) (cnt := (cnt : F))
    (by omega) (by omega) hk ev
  rwa [hc, hs] at h1

private theorem peel_n_lams_collect_tm_nat {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {k : Nat}
    {e acc r_e r_acc : SourceValue F} {n : Nat} {h h' : Heap F} {cs : List (Call F)} {E : KExpr}
    (hn : n < 4611686018427387904) (hE : Tm κ 0 Γ h k E e)
    (ev : ObsFn Obs.W "KernelCheck::peel_n_lams_collect" [e, .field (n : F), .field 0, acc]
      h (.tuple [r_e, .field (n : F), r_acc]) h' cs) :
    ∃ bs body, E.stripLams n = some (bs, body) ∧ Tm κ 0 Γ h' (k + n) body r_e := by
  have hv : ZMod.val (n : F) = n := val_natCast_wide_p hn
  have h1 := peel_n_lams_collect_tm (d := (n : F)) (by omega) ev hE
  rwa [hv] at h1

private theorem lvEqList_drop {as_ bs : List KLevel} (h : LvEqList as_ bs) (n : Nat) :
    LvEqList (as_.drop n) (bs.drop n) := by
  intro φ
  have hφ := h φ
  clear h
  induction n generalizing as_ bs with
  | zero => exact hφ
  | succ n ih =>
    cases as_ with
    | nil =>
      cases bs with
      | nil => trivial
      | cons _ _ => exact hφ.elim
    | cons _ _ =>
      cases bs with
      | nil => exact hφ.elim
      | cons _ _ => exact ih hφ.2

private theorem lvEqList_getD_zero {as_ bs : List KLevel} (h : LvEqList as_ bs) (φ : LevelParam → Nat) :
    (as_.getD 0 .zero).eval φ = (bs.getD 0 .zero).eval φ := by
  have hφ := h φ
  cases as_ with
  | nil =>
    cases bs with
    | nil => rfl
    | cons _ _ => exact hφ.elim
  | cons _ _ =>
    cases bs with
    | nil => exact hφ.elim
    | cons _ _ => exact hφ.1

/-- Compute-iprj hashing helper: `compute_iprj_addr` hashes `serConstant ⟨.iPrj ⟨idx, b⟩, ...⟩`
and returns `iprjAddr b idx`, so any record stored in `E` at that address has `.iPrj ⟨idx, b⟩`. -/
theorem compute_iprj_addr_hashed {c : Ctx} {bp r : SourceValue F} {b : Bytes.Address}
    {idx : Nat} {h h' : Heap F} {cs : List (Call F)}
    (hidx : idx < 4294967296)
    (hb : Bytes.RepAddressRef addrTy h b bp)
    (hgood : Good c cs)
    (ev : ObsFn Obs.W "KernelDefEq::compute_iprj_addr" [bp, .field (idx : F)] h r h' cs) :
    ∃ a : Bytes.Address, Bytes.RepAddressRef addrTy h' a r ∧
      ixAddr a = Core.iprjAddr (ixAddr b) idx ∧
      Hashed cs (Ixon.serConstant ⟨.iPrj ⟨idx.toUInt64, ixAddr b⟩, #[], #[], #[], #[]⟩) := by
  obtain ⟨a, ha, haddr⟩ := Decl.compute_iprj_addr_spec hidx hb hgood ev
  obtain ⟨v1, m2, cs12, m84, m97, m110, m123, v135, m136, cs146, m159, cs174,
    ev14, hm92, hm105, hm118, hm131, hm167, ev148, ev176, hc185⟩ :=
    Obs.«KernelDefEq::compute_iprj_addr».obs ev
  obtain ⟨n, hn, hx, rfl, hm2⟩ := Lib.u64_from_field_spec ev14
  injection hx with hx
  have hval_idx : ZMod.val (idx : F) = idx :=
    ZMod.val_natCast_of_lt (Nat.lt_trans hidx (by decide))
  have hval_n : ZMod.val (idx : F) = n := by
    rw [hx]; exact ZMod.val_natCast_of_lt (Nat.lt_trans hn (by decide))
  have hn_eq : idx = n := hval_idx.symm.trans hval_n
  have e1 : Heap.Extends m2 m84 := by rw [hm92]; exact Heap.Extends.snoc _ _
  have e2 : Heap.Extends m84 m97 := by rw [hm105]; exact Heap.Extends.snoc _ _
  have e3 : Heap.Extends m97 m110 := by rw [hm118]; exact Heap.Extends.snoc _ _
  have e4 : Heap.Extends m110 m123 := by rw [hm131]; exact Heap.Extends.snoc _ _
  have e5 : Heap.Extends m123 m159 := by rw [hm167]; exact Heap.Extends.snoc _ _
  have E : Heap.Extends h m159 := by
    rw [← hm2]; exact e1.trans (e2.trans (e3.trans (e4.trans e5)))
  have c1 : m159[m2.length]? = some (.construct Specs.Callees.ixExprListEnum "Nil" []) :=
    (e2.trans (e3.trans (e4.trans e5))).getElem?_eq (by rw [hm92]; simp)
  have c2 : m159[m84.length]? = some (.construct addrListEnum "Nil" []) :=
    (e3.trans (e4.trans e5)).getElem?_eq (by rw [hm105]; simp)
  have c3 : m159[m97.length]? = some (.construct Specs.Callees.ixUnivListEnum "Nil" []) :=
    (e4.trans e5).getElem?_eq (by rw [hm118]; simp)
  have c4 : m159[m110.length]? = some (.construct Specs.Callees.ixBinderListEnum "Nil" []) :=
    e5.getElem?_eq (by rw [hm131]; simp)
  have c5 : m159[m123.length]? = some (.construct byteListEnum "Nil" []) := by rw [hm167]; simp
  have hrep : RepU64 m159 idx.toUInt64 (TagN.u64Value n) := by
    rw [hn_eq]
    have e := Lib.repU64_ofNatLT m159 (m := n) (Nat.lt_trans hn (by decide))
    rwa [UInt64.ofNatLT_eq_ofNat] at e
  have hinfo : Specs.Callees.ProjInfoRep m159 (.iPrj ⟨idx.toUInt64, ixAddr b⟩)
      (.construct "Ixon::ConstantInfo" "IPrj"
        [.construct "Ixon::InductiveProj" "Mk" [TagN.u64Value n, bp]]) := by
    simp only [Specs.Callees.ProjInfoRep]
    exact ⟨TagN.u64Value n, bp, b, rfl, hrep, Bytes.repAddressRef_heapMono₂ addrTy E hb, rfl⟩
  have hbytes := (Ingress.put_constant_proj_spec
    ⟨_, _, _, _, _, rfl, hinfo, RepLinkedList.nil c1, RepLinkedList.nil c2,
      RepLinkedList.nil c3, RepLinkedList.nil c4⟩
    (RepLinkedList.nil c5) ev148).2
  obtain ⟨_, _, _, _, _, _, evHash, _, _, _, hcBta⟩ := Obs.«Blake3::bytes_to_addr».obs ev176
  have hhashed : Hashed cs (Ixon.serConstant ⟨.iPrj ⟨idx.toUInt64, ixAddr b⟩, #[], #[], #[], #[]⟩) := by
    refine ⟨⟨"Blake3::hash", [v135], m136⟩, ?_, rfl, v135, rfl, ?_⟩
    · rw [hc185, hcBta]; simp
    · have hbse : byteStreamEnum = byteListEnum := rfl
      rw [hbse]
      simpa only [List.append_nil, ProjAddrAux.bytes_mk_toList] using hbytes
  exact ⟨a, ha, haddr, hhashed⟩

/-- Helper: `posOf` preserves `.getAppFn = .const k _`. -/
theorem getAppFn_posOf_const_inv {ps : List LevelParam} {k : KKey} {us : List KLevel} :
    ∀ {e : KExpr}, (Core.posOf ps e).getAppFn = .const k us →
      ∃ us0, e.getAppFn = .const k us0
  | .app f _, h => by
    simp only [Core.posOf, Expr.instantiateLevelParams, Expr.getAppFn] at h
    exact getAppFn_posOf_const_inv (e := f) h
  | .const k' us0, h => by
    simp only [Core.posOf, Expr.instantiateLevelParams, Expr.getAppFn] at h
    injection h with hk _; subst hk
    exact ⟨us0, rfl⟩
  | .bvar _, h | .fvar _ _, h | .sort _, h | .lam _ _ _, h | .forallE _ _ _, h
  | .letE _ _ _ _, h | .lit _, h | .proj _ _ _, h => by
    simp [Core.posOf, Expr.instantiateLevelParams, Expr.getAppFn] at h

/-- Helper: `stripPis` on `posOf ps e` pulls back to `piDomAt n e` when ending in `.forallE`. -/
theorem piDomAt_of_stripPis_posOf {ps : List LevelParam} {n : Nat} {e domPos bodyPos : KExpr}
    {bmPos : Ix.Kernel.BinderMeta} {bs : List (KExpr × Ix.Kernel.BinderMeta)}
    (hs : (Core.posOf ps e).stripPis n = some (bs, .forallE domPos bodyPos bmPos)) :
    ∃ dom, Core.piDomAt n e = some dom ∧ Core.posOf ps dom = domPos := by
  obtain ⟨bs0, rem0, hs0, hrem0⟩ := stripPis_posOf_inv hs
  cases rem0 with
  | forallE dom body bm =>
    simp only [Core.posOf, Expr.instantiateLevelParams] at hrem0
    injection hrem0 with hdom _ _
    refine ⟨dom, (Decl.piDomAt_eq_some_iff n e dom).mpr ⟨bs0, body, bm, hs0⟩, hdom.symm⟩
  | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _ | lam _ _ _ | letE _ _ _ _
  | lit _ | proj _ _ _ => simp [Core.posOf, Expr.instantiateLevelParams] at hrem0

/-- `recMotiveCarrierAt` agrees with `Binding.FamilyOf.motiveCarrierAt`. -/
theorem recMotiveCarrierAt_eq_familyOf (c : Ixon.Constant) (r : Ixon.Recursor) (i n : Nat) :
    recMotiveCarrierAt c r i n = Binding.FamilyOf.motiveCarrierAt c r i n := by
  have hunshare : ∀ k e, recUnshare c k e = Binding.FamilyOf.unshare c k e := by
    intro k; induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro e; cases e with
      | share idx =>
        simp only [recUnshare, Binding.FamilyOf.unshare]
        cases c.sharing[idx.toNat]? with
        | none => rfl
        | some e' => exact ih e'
      | _ => rfl
  have hnode : ∀ e, recNode c e = Binding.FamilyOf.node c e := fun e => hunshare _ e
  have hpeel : ∀ k e, recPeel c k e = Binding.FamilyOf.peel c k e := by
    intro k; induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro e; simp only [recPeel, Binding.FamilyOf.peel, hnode]
      cases Binding.FamilyOf.node c e <;> simp [ih]
  have hdom : ∀ e, recDomOf c e = Binding.FamilyOf.domOf c e := by
    intro e; simp only [recDomOf, Binding.FamilyOf.domOf, hnode]
    cases Binding.FamilyOf.node c e <;> rfl
  have hlast : ∀ k e, recLastDom c k e = Binding.FamilyOf.lastDom c k e := by
    intro k; induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro e; simp only [recLastDom, Binding.FamilyOf.lastDom, hnode]
      cases h1 : Binding.FamilyOf.node c e with
      | all d b =>
        dsimp only
        cases h2 : Binding.FamilyOf.node c b <;> simp [ih]
      | _ => rfl
  have hsp : ∀ k e, recSpineHead c k e = Binding.FamilyOf.spineHead c k e := by
    intro k; induction k with
    | zero => intro e; exact hnode e
    | succ k ih =>
      intro e; simp only [recSpineHead, Binding.FamilyOf.spineHead, hnode]
      cases Binding.FamilyOf.node c e <;> simp [ih]
  have href : ∀ k e, recRefHeadAt c k e = Binding.FamilyOf.refHeadAt c k e := by
    intro k e; simp only [recRefHeadAt, Binding.FamilyOf.refHeadAt, hsp]
    cases Binding.FamilyOf.spineHead c k e <;> rfl
  simp only [recMotiveCarrierAt, Binding.FamilyOf.motiveCarrierAt, hpeel, hdom, hlast, href]

/-- `KernelModeled::rec_family_block` specification: extracts `RecHostAt`, `recMotiveCarrierAt`,
and the target inductive block projection directly from `IxVM.Refinement.Typing.rec_family_block_spec`. -/
theorem rec_family_block_spec (P : ProjsCtx.{u}) {aR : Bytes.Address}
    {x_rec_addr r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (haR : Bytes.RepAddressRef addrTy h aR x_rec_addr)
    (ev : ObsFn Obs.W "KernelModeled::rec_family_block" [x_rec_addr] h r h' cs)
    (hsub : ∀ cl ∈ cs, cl ∈ P.calls) :
    ∃ (b_out : Bytes.Address) (cHost : Ixon.Constant) (rcR : Ixon.Recursor)
      (nf : Nat) (p0 : _root_.Address) (cm0 : Ixon.Constant) (ip0 : Ixon.InductiveProj),
      Bytes.RepAddressRef addrTy h' b_out r ∧
      RecHostAt P.E (ixAddr aR) cHost rcR ∧
      recMotiveCarrierAt cHost rcR 0 nf = some p0 ∧
      Ix.Cert.recordAt P.E p0 = some cm0 ∧
      cm0.info = .iPrj ip0 ∧
      ip0.block = ixAddr b_out := by
  obtain ⟨-, cx, b_out, -, -, j, -, p0, cm0, hcx, hb_out, -, -, -, hcm0, hcm0_info, hcase⟩ :=
    IxVM.Refinement.Typing.rec_family_block_spec P.hS P.hH ⟨aR, haR, rfl⟩ ev hsub
  have hcxE := P.hSE.store.runRecord _ _ hcx
  have hcm0E := P.hSE.store.runRecord _ _ hcm0
  rcases hcase with ⟨rcR, nf, hinfo, hmot⟩ | ⟨idx, aBlk, ca, rs, rcR, nf, hrprj, hca, hmuts, hrs, hmot, -⟩
  · exact ⟨b_out, cx, rcR, nf, p0, cm0, ⟨j, ixAddr b_out⟩, hb_out,
      Or.inl ⟨hcxE, hinfo⟩, by rw [recMotiveCarrierAt_eq_familyOf]; exact hmot, hcm0E, hcm0_info, rfl⟩
  · exact ⟨b_out, ca, rcR, nf, p0, cm0, ⟨j, ixAddr b_out⟩, hb_out,
      Or.inr ⟨cx, ⟨idx, aBlk⟩, rs, hcxE, hrprj, P.hSE.store.runRecord _ _ hca, hmuts, hrs⟩,
      by rw [recMotiveCarrierAt_eq_familyOf]; exact hmot, hcm0E, hcm0_info, rfl⟩

/-- Lifting by `c` at cutoff `k` preserves `hasLooseBVar = false` at shifted index `i + c + k`. -/
private theorem hasLooseBVar_lift_false {i c : Nat} :
    ∀ (x : KExpr) (k : Nat), x.hasLooseBVar (i + k) = false →
      (x.liftLooseBVars c k).hasLooseBVar (i + c + k) = false
  | .bvar u, k, hx => by
    simp only [Ix.Kernel.Expr.hasLooseBVar, beq_eq_false_iff_ne] at hx
    simp only [Ix.Kernel.Expr.liftLooseBVars]
    split <;> (simp only [Ix.Kernel.Expr.hasLooseBVar, beq_eq_false_iff_ne]; omega)
  | .fvar _ _, _, _ | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, k, hx => by
    simp only [Ix.Kernel.Expr.hasLooseBVar, Bool.or_eq_false_iff] at hx
    simp only [Ix.Kernel.Expr.liftLooseBVars, Ix.Kernel.Expr.hasLooseBVar, Bool.or_eq_false_iff]
    exact ⟨hasLooseBVar_lift_false f k hx.1, hasLooseBVar_lift_false a k hx.2⟩
  | .lam t b _, k, hx | .forallE t b _, k, hx => by
    simp only [Ix.Kernel.Expr.hasLooseBVar, Bool.or_eq_false_iff] at hx
    simp only [Ix.Kernel.Expr.liftLooseBVars, Ix.Kernel.Expr.hasLooseBVar, Bool.or_eq_false_iff]
    exact ⟨hasLooseBVar_lift_false t k hx.1,
      by simpa [Nat.add_assoc] using hasLooseBVar_lift_false b (k + 1) (by simpa [Nat.add_assoc] using hx.2)⟩
  | .letE t v b _, k, hx => by
    simp only [Ix.Kernel.Expr.hasLooseBVar, Bool.or_eq_false_iff] at hx
    simp only [Ix.Kernel.Expr.liftLooseBVars, Ix.Kernel.Expr.hasLooseBVar, Bool.or_eq_false_iff]
    exact ⟨⟨hasLooseBVar_lift_false t k hx.1.1, hasLooseBVar_lift_false v k hx.1.2⟩,
      by simpa [Nat.add_assoc] using hasLooseBVar_lift_false b (k + 1) (by simpa [Nat.add_assoc] using hx.2)⟩
  | .proj _ _ a, k, hx => by
    simp only [Ix.Kernel.Expr.liftLooseBVars, Ix.Kernel.Expr.hasLooseBVar] at hx ⊢
    exact hasLooseBVar_lift_false a k hx

private theorem hasLooseBVar_instShift_false {V : KExpr} {i : Nat}
    (hV : V.hasLooseBVar i = false) :
    ∀ (e : KExpr) (c : Nat), e.hasLooseBVar (i + c + 1) = false →
      (instShift V c e).hasLooseBVar (i + c) = false
  | .bvar j, c, he => by
    simp only [instShift, Ix.Kernel.Expr.instantiate1Lift]
    split
    · simpa using hasLooseBVar_lift_false (i := i) (c := c) V 0 (by simpa using hV)
    · split
      · simp only [Ix.Kernel.Expr.hasLooseBVar, beq_eq_false_iff_ne] at he ⊢; omega
      · simp only [Ix.Kernel.Expr.hasLooseBVar, beq_eq_false_iff_ne] at he ⊢; omega
  | .fvar _ _, _, _ | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, c, he => by
    simp only [Ix.Kernel.Expr.hasLooseBVar, Bool.or_eq_false_iff] at he
    simp only [instShift, Ix.Kernel.Expr.instantiate1Lift, Ix.Kernel.Expr.hasLooseBVar,
      Bool.or_eq_false_iff]
    exact ⟨hasLooseBVar_instShift_false hV f c he.1, hasLooseBVar_instShift_false hV a c he.2⟩
  | .lam t b _, c, he | .forallE t b _, c, he => by
    simp only [Ix.Kernel.Expr.hasLooseBVar, Bool.or_eq_false_iff] at he
    simp only [instShift, Ix.Kernel.Expr.instantiate1Lift, Ix.Kernel.Expr.hasLooseBVar,
      Bool.or_eq_false_iff]
    have hb : (instShift V (c + 1) b).hasLooseBVar (i + (c + 1)) = false :=
      hasLooseBVar_instShift_false hV b (c + 1) (by simpa [Nat.add_assoc] using he.2)
    exact ⟨hasLooseBVar_instShift_false hV t c he.1, by simpa [Nat.add_assoc] using hb⟩
  | .letE t v b _, c, he => by
    simp only [Ix.Kernel.Expr.hasLooseBVar, Bool.or_eq_false_iff] at he
    simp only [instShift, Ix.Kernel.Expr.instantiate1Lift, Ix.Kernel.Expr.hasLooseBVar,
      Bool.or_eq_false_iff]
    have hb : (instShift V (c + 1) b).hasLooseBVar (i + (c + 1)) = false :=
      hasLooseBVar_instShift_false hV b (c + 1) (by simpa [Nat.add_assoc] using he.2)
    exact ⟨⟨hasLooseBVar_instShift_false hV t c he.1.1, hasLooseBVar_instShift_false hV v c he.1.2⟩,
      by simpa [Nat.add_assoc] using hb⟩
  | .proj _ _ a, c, he => by
    simp only [instShift, Ix.Kernel.Expr.instantiate1Lift, Ix.Kernel.Expr.hasLooseBVar] at he ⊢
    exact hasLooseBVar_instShift_false hV a c he

/-- `NoIdx h lo hi p` on a `Tm` at `(d = 0, k)` implies `E.hasLooseBVar i = false` for all
`lo ≤ i < hi`. -/
theorem hasLooseBVar_false_of_noIdx_tm {κ : _root_.Address → KKey} {Γ : Nat → KExpr} {h : Heap F}
    {k : Nat} {E : KExpr} {p : SourceValue F} (rep : Tm κ 0 Γ h k E p) :
    ∀ {lo hi : Nat}, Specs.Subst.NoIdx h lo hi p → ∀ i, lo ≤ i → i < hi → E.hasLooseBVar i = false := by
  induction rep with
  | bvarLocal cell _ _ =>
    intro lo hi hno i hlo hhi
    obtain ⟨i', hx, hP⟩ := SubstAux.idxAll_bvar_inv hno (loadValue_enum_cell cell)
    injection hx with hx; subst hx
    simp only [Nat.add_zero] at hP
    simp only [Ix.Kernel.Expr.hasLooseBVar, beq_eq_false_iff_ne]
    omega
  | bvarFree _ _ _ hd => omega
  | sort _ _ _ => intro _ _ _ _ _ _; rfl
  | const _ _ _ _ => intro _ _ _ _ _ _; rfl
  | litNat _ _ _ => intro _ _ _ _ _ _; rfl
  | litStr _ _ _ => intro _ _ _ _ _ _; rfl
  | app cell _ _ ihf iha =>
    intro lo hi hno i hlo hhi
    obtain ⟨hf, ha⟩ := SubstAux.idxAll_app_inv hno (loadValue_enum_cell cell)
    simp only [Ix.Kernel.Expr.hasLooseBVar, Bool.or_eq_false_iff]
    exact ⟨ihf hf i hlo hhi, iha ha i hlo hhi⟩
  | lam cell _ _ _ iht ihb =>
    intro lo hi hno i hlo hhi
    obtain ⟨ht, hb⟩ := SubstAux.idxAll_lam_inv hno (loadValue_enum_cell cell)
    simp only [Ix.Kernel.Expr.hasLooseBVar, Bool.or_eq_false_iff]
    refine ⟨iht ht i hlo hhi, ihb (lo := lo + 1) (hi := hi + 1) ?_ (i + 1) (by omega) (by omega)⟩
    exact SubstAux.idxAll_imp hb (fun n j hj => by omega)
  | forallE cell _ _ _ iht ihb =>
    intro lo hi hno i hlo hhi
    obtain ⟨ht, hb⟩ := SubstAux.idxAll_forallE_inv hno (loadValue_enum_cell cell)
    simp only [Ix.Kernel.Expr.hasLooseBVar, Bool.or_eq_false_iff]
    refine ⟨iht ht i hlo hhi, ihb (lo := lo + 1) (hi := hi + 1) ?_ (i + 1) (by omega) (by omega)⟩
    exact SubstAux.idxAll_imp hb (fun n j hj => by omega)
  | letE cell _ _ _ _ ihv ihb =>
    intro lo hi hno i hlo hhi
    obtain ⟨-, hv, hb⟩ := SubstAux.idxAll_letE_inv hno (loadValue_enum_cell cell)
    have hV0 := ihv hv i hlo hhi
    have hB1 := ihb (lo := lo + 1) (hi := hi + 1)
      (SubstAux.idxAll_imp hb (fun n j hj => by omega)) (i + 1) (by omega) (by omega)
    simpa using hasLooseBVar_instShift_false hV0 _ 0 (by simpa using hB1)
  | proj cell _ _ ihe =>
    intro lo hi hno i hlo hhi
    exact ihe (SubstAux.idxAll_proj_inv hno (loadValue_enum_cell cell)) i hlo hhi

/-- `KernelSubst::has_bvar_in_range [pe, 0, fidx] = 0` certifies `∀ i < fidx, E.hasLooseBVar i = false`. -/
theorem noLooseBVar_of_hasBVarInRange_zero {κ : _root_.Address → KKey} {Γ : Nat → KExpr}
    {h h' : Heap F} {cs : List (Call F)} {k fidx : Nat} {E : KExpr} {pe : SourceValue F}
    (hfidx : fidx < 72057594037927936) (hbd : Bounded cs) (hE : Tm κ 0 Γ h k E pe)
    (ev : ObsFn Obs.W "KernelSubst::has_bvar_in_range" [pe, .field 0, .field (fidx : F)] h
      (.field 0) h' cs) :
    ∀ i < fidx, E.hasLooseBVar i = false := by
  have hspec := SubstAux.gall κ .has_bvar_in_range _ _ _ _ _ ev pe 0 (fidx : F) rfl hbd
  have hnoF : Specs.Subst.NoIdxF h (ZMod.val (0 : F)) (ZMod.val (fidx : F)) pe :=
    hspec.2.2 rfl 0 Γ k E hE
  rw [ZMod.val_zero, val_natCast_wide_p (by omega)] at hnoF
  have hno : Specs.Subst.NoIdx h 0 fidx pe :=
    SubstAux.noIdx_of_noIdxF_tm hE (by
      change fidx + 9223372036854775808 ≤ 18446744069414584321; omega) hnoF
  intro i hi
  exact hasLooseBVar_false_of_noIdx_tm hE hno i (Nat.zero_le i) hi

/-- `posOf (List.range n)` is identity. -/
theorem posOf_range_id (n : Nat) (e : KExpr)
    (_ : e.allLevelParamsDefined (List.range n) = true) :
    Core.posOf (List.range n) e = e :=
  Decl.posOf_range n e

/-- Evaluation of `substLevel u ((List.range bnl).map .param)` equals `u.eval`. -/
theorem substLevel_range_eval {bnl : Nat} {u : KLevel}
    (hdef : u.allParamsDefined (List.range bnl) = true) (φ : LevelParam → Nat) :
    (substLevel u ((List.range bnl).map .param)).eval φ = u.eval φ := by
  clear hdef
  induction u with
  | zero => rfl
  | succ x ih => simp [substLevel, Level.eval, ih]
  | max a b iha ihb =>
    simp [substLevel, IxVM.Refinement.KernelLevels.eval_levelMax, Level.eval, iha, ihb]
  | imax a b iha ihb =>
    simp [substLevel, IxVM.Refinement.KernelLevels.eval_levelIMax, Level.eval, iha, ihb]
  | param p =>
    simp only [substLevel]
    by_cases hp : p < bnl
    · simp [hp]
    · have hnone : ((List.range bnl).map Level.param)[p]? = none := by
        simp [hp]
      rw [hnone]; rfl

/-- `posOf` produces level parameters all in `List.range ps.length`. -/
theorem allLevelParamsDefined_posOf {ps : List LevelParam} (e : KExpr)
    (he : e.allLevelParamsDefined ps = true) :
    (Core.posOf ps e).allLevelParamsDefined (List.range ps.length) = true := by
  apply Decl.allLevelParamsDefined_instantiateLevelParams _ (by simp [Core.posLevels]) he
  intro u hu
  simp only [Core.posLevels, List.mem_map, List.mem_range] at hu
  obtain ⟨i, hi, rfl⟩ := hu
  simp [Ix.Kernel.Level.allParamsDefined, hi]

theorem allLevelParamsDefined_stripPis_sort {ps : List LevelParam} :
    ∀ {n : Nat} {e : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)} {u : KLevel},
      e.allLevelParamsDefined ps = true → e.stripPis n = some (bs, .sort u) →
      u.allParamsDefined ps = true
  | 0, _, _, _, hd, hs => by
    injection hs with hp; injection hp with _ hr; subst hr; exact hd
  | n + 1, .forallE _ b _, bs, u, hd, hs => by
    simp only [Ix.Kernel.Expr.allLevelParamsDefined, Bool.and_eq_true] at hd
    simp only [Expr.stripPis] at hs
    cases hsb : b.stripPis n with
    | none => simp [hsb] at hs
    | some p =>
      rcases p with ⟨bs₀, rem₀⟩
      rw [hsb] at hs; injection hs with hp; injection hp with _ hr; dsimp only at hr; rw [hr] at hsb
      exact allLevelParamsDefined_stripPis_sort hd.1.2 hsb
  | _ + 1, .bvar _, _, _, _, hs | _ + 1, .fvar _ _, _, _, _, hs | _ + 1, .sort _, _, _, _, hs
  | _ + 1, .const _ _, _, _, _, hs | _ + 1, .app _ _, _, _, _, hs | _ + 1, .lam _ _ _, _, _, _, hs
  | _ + 1, .letE _ _ _ _, _, _, _, hs | _ + 1, .lit _, _, _, _, hs | _ + 1, .proj _ _ _, _, _, _, hs =>
    nomatch hs

/-! ## Section 2: `KernelModeled::rec_rule_ih_args` -/

theorem rec_rule_ih_args_spec {κ : _root_.Address → KKey} {ps : List LevelParam}
    {rl : RecRule .anon} {nP anc k : Nat} {x_rule x_rnf x_ih_args : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)}
    (hnP : nP < 72057594037927936) (hanc : anc < 72057594037927936) (hk : k < anc)
    (hbd : Bounded cs) (hrl : RuleRep κ h ps k x_rule rl)
    (ev : ObsFn Obs.W "KernelModeled::rec_rule_ih_args"
      [x_rule, .field (nP : F), .field (anc : F), .field (k : F)] h
      (.tuple [x_rnf, x_ih_args]) h' cs) :
    x_rnf = .field (rl.nfields : F) ∧
    ∃ rbs rargs,
      (Core.posOf ps rl.rhs).stripLams (nP + 1 + anc + rl.nfields) =
        some (rbs, Expr.mkAppN (.bvar (rl.nfields + anc - 1 - k)) rargs) ∧
      rl.nfields ≤ rargs.length ∧
      rargs.length < 2 ^ 39 ∧
      List.Forall₂ ExprSemEq (rargs.take rl.nfields)
        ((List.range rl.nfields).map fun m => .bvar (rl.nfields - 1 - m)) ∧
      RepList kexprListEnum (fun h A p => Tm κ 0 zeroGhost h (nP + 1 + anc + rl.nfields) A p)
        h' (rargs.drop rl.nfields) x_ih_args := by
  obtain ⟨rhsPtr, hruleEq, hrnf56, hrhsTm⟩ := hrl
  match Obs.«KernelModeled::rec_rule_ih_args».obs ev with
  | .run (x_rcidx := x_rcidx) (x_rnf := x_rnf0) (x_rrhs := x_rrhs)
      (v_nmripuiu := v_tot) (x_djuissaf := v_dju) (x_nanbnbpl := v_nan)
      (m_clhugmph := m_peel) (cs_xwnciguy := cs_peel) (m_syuvhsrv := m_nil)
      (x_rbody := x_rbody) (x_rpeeled := x_rpeeled)
      (m_hcspykae := m_sp) (cs_kyjqcwll := cs_sp) (x_rh := x_rh) (x_rargs := x_rargs)
      (x_hbv := x_hbv) (v_hagqyygb := v_hbv) (x_cdnuqdxo := v_cd) (x_etznhnzl := v_et)
      (v_dluivija := v_lt) (m_mgeadsnm := m_lt) (cs_fauinifx := cs_lt)
      (v_twdvdrzc := v_len1) (x_zjdhgjqs := v_len) (m_fnffujnf := m_len) (cs_ldrzuwxe := cs_len)
      (v_accabcut := v_eq) (m_hsbecaoz := m_eq) (cs_avltqkms := cs_eq)
      (v_kpxdiojs := v_take) (v_vwuuohub := v_bv) (m_yrttvmxo := m_take) (cs_hqgmeaum := cs_take)
      (m_bzdllppo := m_bv) (cs_oddvstfz := cs_bv)
      (v_rbdizhpq := v_drop) (m_mzdnrcrq := m_drop) (cs_hvduiklz := cs_drop)
      (hv_znvnbgdc := hru) (op_wpcwnnnk := op1) (op_nhpzlmoh := op2) (op_rqlpojet := op3)
      (hm_dqydtsal := hmNil) (ev_uivgtpyq := evPeel) (heq_xpooygvc := hpeeled)
      (ev_zxskbtka := evSp) (ld_wnisetpz := ldRh)
      (op_gxvqupty := op4) (op_pugxxsji := op5) (op_tzooqonj := op6) (heq_xvvylyjc := hhbv)
      (ev_teadbhvv := evLen) (op_qphykznn := opLen1) (ev_dowjzuoi := evLt) (heq_rkkyjofg := hlt1)
      (ev_mrzbrjda := evTake) (ev_pkovtnzu := evBv) (ev_ektjfhyt := evEq) (heq_zysjmxya := heq1)
      (he_xnwfxhtv := hret) (ev_clbohndu := evDrop) (he_aosuzxec := hh') (hc_sgljalbe := hc) .. =>
    rw [hruleEq] at hru
    injection hru with _ _ hruArgs
    simp only [List.cons.injEq, and_true] at hruArgs
    obtain ⟨rfl, rfl, rfl⟩ := hruArgs
    simp only [Value.tuple.injEq, List.cons.injEq, and_true] at hret
    obtain ⟨rfl, rfl⟩ := hret
    subst hh' hlt1 heq1
    have htot_eq : v_tot = .field ((nP + 1 + anc + rl.nfields : Nat) : F) := by
      rw [evalBinOp_add_field_p op1] at op2
      rw [evalBinOp_add_field_p op2] at op3
      rw [evalBinOp_add_field_p op3]; push_cast; rfl
    rw [htot_eq] at evPeel hpeeled
    have extNil : Heap.Extends h m_nil := by rw [hmNil]; exact Heap.Extends.snoc _ _
    have hrhs' : Tm κ 0 zeroGhost m_nil 0 (Core.posOf ps rl.rhs) rhsPtr :=
      (hrhsTm 0 zeroGhost).mono extNil
    rw [hpeeled] at evPeel
    obtain ⟨rbs, rbody, hstrip, hbodyTm⟩ := peel_n_lams_collect_tm_nat (n := nP + 1 + anc + rl.nfields)
      (by omega) hrhs' evPeel
    simp only [Nat.zero_add] at hbodyTm
    obtain ⟨H, rargs, hrbodyEq, hHTm, hargsRep⟩ := collect_spine_tuple_tm evSp hbodyTm
    obtain ⟨hbv_f, rfl, hbv_small, hbv_lt, rfl⟩ := bvar_of_load_d0 hHTm ldRh
    have hbv_eq : v_hbv = .field ((rl.nfields + anc - 1 - k : Nat) : F) := by
      rw [evalBinOp_add_field_p op4] at op5
      rw [evalBinOp_sub_field_p op5] at op6
      rw [evalBinOp_sub_field_p op6]
      congr 1
      have h2 : ((rl.nfields + anc - 1 - k : Nat) : F) + 1 + (k : F) = (rl.nfields : F) + (anc : F) := by
        have hnat : rl.nfields + anc - 1 - k + 1 + k = rl.nfields + anc := by omega
        have := congrArg (Nat.cast (R := F)) hnat
        simpa [Nat.cast_add] using this
      linear_combination -h2
    rw [hbv_eq] at hhbv
    have hhbv_nat : ZMod.val hbv_f = rl.nfields + anc - 1 - k := by
      have h1 := congrArg ZMod.val (Value.field.inj hhbv)
      rwa [val_natCast_wide_p (by omega)] at h1
    rw [hhbv_nat] at hrbodyEq
    obtain ⟨hvlen, hrargs_lt, hm_len⟩ := kexprList_length_bd hargsRep hbd (by rw [hc]; simp) evLen
    subst hvlen hm_len
    have hlen1 : v_len1 = .field ((rargs.length + 1 : Nat) : F) := by
      rw [evalBinOp_add_field_p opLen1]; push_cast; rfl
    rw [hlen1] at evLt
    obtain ⟨_, _, hlt_iff, _, hm_lt⟩ := Lib.less_than_fields_field evLt
    have hrnf_lt := hlt_iff.mp rfl
    subst hm_lt
    have hrnf_le : rl.nfields ≤ rargs.length := by
      have h1 : ZMod.val (rl.nfields : F) = rl.nfields := val_natCast_wide_p (by omega)
      have h2 : ZMod.val ((rargs.length + 1 : Nat) : F) = rargs.length + 1 := val_natCast_wide_p (by omega)
      rw [h1, h2] at hrnf_lt; omega
    obtain ⟨-, htakeRep⟩ := kexprList_take_spec (fun _ _ _ _ ext r => r.mono ext) evTake hargsRep
    rw [val_natCast_wide_p (by omega)] at htakeRep
    have hbvRep := bvars_desc_tm_nat (κ := κ) (Γ := zeroGhost)
      (k := nP + 1 + anc + rl.nfields) (start := rl.nfields) (cnt := rl.nfields)
      (by omega) (by omega) (by omega) evBv
    have htakeEq := spec_params_ptr_eq_tm_one
      (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) evBv.heap_extends htakeRep) hbvRep evEq
    have extEq :=
      (evTake.heap_extends.trans evBv.heap_extends).trans evEq.heap_extends
    obtain ⟨-, hdropRep, hm_drop⟩ := kexprList_drop_spec evDrop
      (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) extEq hargsRep)
    rw [val_natCast_wide_p (by omega)] at hdropRep
    subst hm_drop
    refine ⟨rfl, rbs, rargs, hrbodyEq ▸ hstrip, hrnf_le, hrargs_lt, htakeEq, hdropRep⟩

/-! ## Section 3: `KernelModeled::find_aux_ctor_for_tag` -/

private theorem find_aux_ctor_for_tag_go (P : ProjsCtx.{u})
    {auxKey tagCKey : KKey} {auxBlk tagBlk : _root_.Address}
    {bAux bTag aAux : Bytes.Address}
    {x_aux_blk x_aux_addr x_tag_blk : SourceValue F}
    {anc nP bnl tagCidx nF : Nat} {tagCidxF : F}
    (hanc : anc < 72057594037927936) (hnP : nP < 72057594037927936)
    (hbnl : bnl < 4294967296) (hnF : nF < 72057594037927936)
    (hbAux_eq : ixAddr bAux = auxBlk) (hbTag_eq : ixAddr bTag = tagBlk)
    (haAux_eq : Core.keyOf P.t (ixAddr aAux) = auxKey)
    (hfamAux : P.sc.FamAt auxBlk 0)
    (hauxCtorStored : ∀ k < anc, ∃ cv knf,
      P.env.find? (Core.keyOf P.t (Core.cprjAddr auxBlk 0 k)) = some (.ctorInfo cv nP knf))
    (tagCWit : NativeCtorWitness P.t P.E P.env tagCKey (Core.keyOf P.t (Core.iprjAddr tagBlk 0)) tagCidx)
    (htagC_blk : tagCWit.cp.block = tagBlk)
    (htagC_idx : tagCWit.cp.idx.toNat = 0)
    (htagC_key_f : tagCKey = P.sc.κ (Core.cprjAddr tagBlk 0 (ZMod.val tagCidxF)))
    (htag_rec : ∃ cb ms ind ctTag, Ix.Cert.recordAt P.E tagBlk = some cb ∧ cb.info = .muts ms ∧
      ms[0]? = some (.indc ind) ∧ 1 < ind.ctors.size ∧
      ind.ctors[tagCidx]? = some ctTag ∧ tagCidxF = (ctTag.cidx.toNat : F))
    (htag_nat : NativeAt P.E tagBlk)
    (htag_neNat : Core.keyOf P.t (Core.iprjAddr tagBlk 0) ≠ Ix.Kernel.natName) :
    ∀ (rem k : Nat) (hk : k + rem = anc)
      (found_flag : F) (found_j : SourceValue F)
      (hfound : found_flag = 0 ∨ ∃ j₀ : Nat, found_flag = 1 ∧ found_j = .field (j₀ : F) ∧ j₀ < k)
      {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      Bytes.RepAddressRef addrTy h bAux x_aux_blk →
      Bytes.RepAddressRef addrTy h aAux x_aux_addr →
      Bytes.RepAddressRef addrTy h bTag x_tag_blk →
      (∀ cl ∈ cs, cl ∈ P.calls) →
      ObsFn Obs.W "KernelModeled::find_aux_ctor_for_tag"
        [x_aux_blk, .field (anc : F), .field (k : F), .field (nP : F), .field (bnl : F),
         x_aux_addr, x_tag_blk, .field tagCidxF, .field (nF : F),
         .field found_flag, found_j] h r h' cs →
      ∃ jIdx : Nat, r = .field (jIdx : F) ∧ jIdx < anc ∧
        ((found_flag = 1 → found_j = .field (jIdx : F)) ∧
         (found_flag = 0 → k ≤ jIdx)) ∧
        ∀ m, k ≤ m → m < anc →
          ∃ w : AuxCtorTagWitness P.t P.E P.env auxKey
              (Core.keyOf P.t (Core.iprjAddr tagBlk 0)) nP bnl m,
            w.ctorKey = Core.keyOf P.t (Core.cprjAddr auxBlk 0 m) ∧
            (m = jIdx → w.ktcCidx = tagCidx ∧ w.knf = nF) ∧
            (m ≠ jIdx → w.ktcCidx ≠ tagCidx) := by
  intro rem
  induction rem with
  | zero =>
    intro k hk found_flag found_j hfound r h h' cs hbAux haAux hbTag hsub ev
    match Obs.«KernelModeled::find_aux_ctor_for_tag».obs ev with
    | .n0 (heq_cwqwghph := hff) (he_whiproaa := hr) .. =>
      have hff1 : found_flag = 1 := Value.field.inj hff
      rcases hfound with h0 | ⟨j₀, -, hfj, hj₀⟩
      · rw [h0] at hff1; exact absurd hff1 zero_ne_one
      · refine ⟨j₀, hr.trans hfj, by omega,
          ⟨fun _ => hfj, fun h0 => absurd (h0.symm.trans hff1) zero_ne_one⟩,
          fun m hm1 hm2 => by omega⟩
    | .other_n0 (op_mmyajoju := op) (hne_xjnibfzs := hne) ..
    | .other_other (op_mmyajoju := op) (hne_xjnibfzs := hne) .. =>
      have hk_eq : k = anc := by omega
      subst hk_eq
      have hsub0 : evalBinOp .sub (.field (k : F)) (.field (k : F)) =
          (.ok (.field 0) : Except EvalError (SourceValue F)) := by
        simp [evalBinOp]
      rw [hsub0] at op; injection op with op; exact absurd op.symm hne
  | succ rem ih =>
    intro k hk found_flag found_j hfound r h h' cs hbAux haAux hbTag hsub ev
    have hk_lt : k < anc := by omega
    have hstep : ∀ {p_c : SourceValue F} {m_c : Heap F} {cs_c : List (Call F)}
        {x_knl x_kty x_knp x_knf : SourceValue F} {w1 w2 w3 w4 : SourceValue F}
        {v_res : SourceValue F} {m_peel : Heap F} {cs_peel : List (Call F)}
        {v_tot : SourceValue F} {m_sp1 : Heap F} {cs_sp1 : List (Call F)}
        {x_kh x_kargs x_aux2 w_ul : SourceValue F}
        {v_aeq : SourceValue F} {m_aeq : Heap F} {cs_aeq : List (Call F)}
        {v_klen v_np1 : SourceValue F} {m_klen : Heap F} {cs_klen : List (Call F)}
        {v_kidx : SourceValue F} {m_kidx : Heap F} {cs_kidx : List (Call F)}
        {m_sp2 : Heap F} {cs_sp2 : List (Call F)}
        {x_kth x_kt_args x_ktc_addr x_kt_lvls : SourceValue F}
        {m_ktc : Heap F} {p_ktc : SourceValue F} {cs_ktc : List (Call F)}
        {x_ktc_nl w_ktc_ty x_ktc_blk x_ktc_ind x_ktc_cidx x_ktc_np x_ktc_cnf w_ktc_u : SourceValue F}
        {v_lvlen : SourceValue F} {m_lvlen : Heap F} {cs_lvlen : List (Call F)}
        {v_arglen v_argsum : SourceValue F} {m_arglen : Heap F} {cs_arglen : List (Call F)}
        {v_beq : SourceValue F} {m_beq : Heap F} {cs_beq : List (Call F)},
        (∀ cl ∈ cs_c, cl ∈ P.calls) → (∀ cl ∈ cs_peel, cl ∈ P.calls) →
        (⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [x_kargs], m_aeq⟩ : Call F) ∈ P.calls →
        (∀ cl ∈ cs_ktc, cl ∈ P.calls) →
        (⟨Obs.Names.«Lists::length<&KernelTypes::KLevelNode>», [x_kt_lvls], m_ktc⟩ : Call F) ∈ P.calls →
        (⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [x_kt_args], m_lvlen⟩ : Call F) ∈ P.calls →
        ObsFn Obs.W "Ingress::get_ci_cprj" [x_aux_blk, .field 0, .field (k : F)] h p_c m_c cs_c →
        loadValue m_c p_c = .ok (.construct kciEnum "Ctor" [x_knl, x_kty, w1, w2, w3, x_knp, x_knf, w4]) →
        x_knl = .field (bnl : F) → x_knp = .field (nP : F) →
        evalBinOp .add (.field (nP : F)) x_knf = .ok v_tot →
        ObsFn Obs.W "KernelCheck::peel_n_foralls_zeta" [x_kty, v_tot] m_c v_res m_peel cs_peel →
        ObsFn Obs.W "KernelTypes::collect_spine" [v_res] m_peel (.tuple [x_kh, x_kargs]) m_sp1 cs_sp1 →
        loadValue m_sp1 x_kh = .ok (.construct kexprEnum "Const" [x_aux2, w_ul]) →
        ObsFn Obs.W "Bytes::address_eq" [x_aux2, x_aux_addr] m_sp1 v_aeq m_aeq cs_aeq →
        v_aeq = .field 1 →
        ObsFn Obs.W Obs.Names.«Lists::length<&KernelTypes::KExprNode>» [x_kargs] m_aeq v_klen m_klen cs_klen →
        evalBinOp .add (.field (nP : F)) (.field 1) = .ok v_np1 →
        v_klen = v_np1 →
        ObsFn Obs.W Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>» [x_kargs, .field (nP : F)] m_klen v_kidx m_kidx cs_kidx →
        ObsFn Obs.W "KernelTypes::collect_spine" [v_kidx] m_kidx (.tuple [x_kth, x_kt_args]) m_sp2 cs_sp2 →
        loadValue m_sp2 x_kth = .ok (.construct kexprEnum "Const" [x_ktc_addr, x_kt_lvls]) →
        ObsFn Obs.W "Ingress::get_ci" [x_ktc_addr] m_sp2 p_ktc m_ktc cs_ktc →
        loadValue m_ktc p_ktc = .ok (.construct kciEnum "Ctor"
          [x_ktc_nl, w_ktc_ty, x_ktc_blk, x_ktc_ind, x_ktc_cidx, x_ktc_np, x_ktc_cnf, w_ktc_u]) →
        ObsFn Obs.W Obs.Names.«Lists::length<&KernelTypes::KLevelNode>» [x_kt_lvls] m_ktc v_lvlen m_lvlen cs_lvlen →
        v_lvlen = x_ktc_nl →
        ObsFn Obs.W Obs.Names.«Lists::length<&KernelTypes::KExprNode>» [x_kt_args] m_lvlen v_arglen m_arglen cs_arglen →
        evalBinOp .add x_ktc_np x_ktc_cnf = .ok v_argsum →
        v_arglen = v_argsum →
        ObsFn Obs.W "Bytes::address_eq" [x_ktc_blk, x_tag_blk] m_arglen v_beq m_beq cs_beq →
        v_beq = .field 1 → x_ktc_ind = .field 0 →
        ∃ w : AuxCtorTagWitness P.t P.E P.env auxKey (Core.keyOf P.t (Core.iprjAddr tagBlk 0)) nP bnl k,
          w.ctorKey = Core.keyOf P.t (Core.cprjAddr auxBlk 0 k) ∧
          x_knf = .field (w.knf : F) ∧ w.knf < 72057594037927936 ∧
          (x_ktc_cidx = .field tagCidxF ↔ w.ktcCidx = tagCidx) ∧
          Heap.Extends h m_beq := by
      intro p_c m_c cs_c x_knl x_kty x_knp x_knf w1 w2 w3 w4 v_res m_peel cs_peel v_tot
        m_sp1 cs_sp1 x_kh x_kargs x_aux2 w_ul v_aeq m_aeq cs_aeq v_klen v_np1 m_klen cs_klen
        v_kidx m_kidx cs_kidx m_sp2 cs_sp2 x_kth x_kt_args x_ktc_addr x_kt_lvls m_ktc p_ktc cs_ktc
        x_ktc_nl w_ktc_ty x_ktc_blk x_ktc_ind x_ktc_cidx x_ktc_np x_ktc_cnf w_ktc_u
        v_lvlen m_lvlen cs_lvlen v_arglen v_argsum m_arglen cs_arglen v_beq m_beq cs_beq
        hsub_c hsub_peel hsub_klen hsub_ktc hsub_lvlen hsub_arglen
        evC ldC hknl hknp opTot evPeel evSp1 ldKh evAeq haeq1 evKlen opNp1 hklen evKidx
        evSp2 ldKth evKtc ldKtc evLvlen hlvlen evArglen opArgsum harglen evBeq hbeq1 hktcind
      subst haeq1 hbeq1 hktcind
      obtain ⟨cvC, knf, hfindC⟩ := hauxCtorStored k hk_lt
      have hk_val : ZMod.val (k : F) = k := val_natCast_wide_p (by omega)
      have hfam' : P.sc.FamAt (ixAddr bAux) (ZMod.val (0 : F)) := by
        rw [hbAux_eq, ZMod.val_zero]; exact hfamAux
      obtain ⟨hκC, -⟩ := P.sc_kappa_eq_of_isSome (a := Core.cprjAddr auxBlk 0 k) (by rw [hfindC]; rfl)
      have hfindC' : P.sc.env.find? (P.sc.κ (Core.cprjAddr (ixAddr bAux) (ZMod.val (0 : F)) (ZMod.val (k : F)))) =
          some (.ctorInfo cvC nP knf) := by
        rw [hbAux_eq, ZMod.val_zero, hk_val, hκC]; exact hfindC
      have hrepC := (P.hSE.prefixInv.loads.getCprj x_aux_blk p_c 0 (k : F) h m_c cs_c bAux
        evC trivial hfam' (P.hcoreGoodSub hsub_c) hbAux).2 cvC nP knf hfindC'
      obtain ⟨vC, hldC', hciC⟩ := hrepC
      rw [ldC] at hldC'; injection hldC' with hveq
      cases hciC with
      | ctor hvC hnpC hnfC hcntC _ =>
        simp only [Value.construct.injEq, List.cons.injEq, and_true] at hveq
        obtain ⟨_, _, rfl, rfl, -, -, -, rfl, rfl, -⟩ := hveq
        have hbnl_eq : cvC.levelParams.length = bnl :=
          nat_eq_of_field_eq_u56_p (by have := hvC.2.1; omega) (by omega)
            (Value.field.inj (hvC.1.symm.trans hknl))
        have hpermC : cvC.levelParams.Perm (List.range bnl) := by rw [← hbnl_eq]; exact hvC.2.2.1
        rw [hnfC] at opTot
        have htot_eq : v_tot = .field ((nP + knf : Nat) : F) := by
          rw [evalBinOp_add_field_p opTot]; push_cast; rfl
        rw [htot_eq] at evPeel
        have hktyTm : Tm (Core.keyOf P.t) 0 zeroGhost m_c 0 (Core.posOf cvC.levelParams cvC.type) x_kty :=
          P.rekey_tm (hvC.2.2.2 0 zeroGhost)
        obtain ⟨kres, hstrip, hkresTm⟩ := peel_n_foralls_zeta_open evPeel
          (P.hbdSub hsub_peel) x_kty (nP + knf) 0 _ rfl (by omega) hktyTm
        obtain ⟨H1, kargs, hkresEq, hH1Tm, hkargsRep⟩ := collect_spine_tuple_tm evSp1 hkresTm
        obtain ⟨aAux2, auxLvls, rfl, haAux2, -, -, -⟩ := hH1Tm.const_of_load ldKh
        have ext1 : Heap.Extends h m_sp1 :=
          evC.heap_extends.trans (evPeel.heap_extends.trans evSp1.heap_extends)
        obtain ⟨hAeq_f, hm_aeq⟩ := Lib.address_eq_spec evAeq haAux2
          (Bytes.repAddressRef_heapMono₂ addrTy ext1 haAux)
        subst hm_aeq
        have haAux2_eq : aAux2 = aAux := by by_contra hne; simp [hne] at hAeq_f
        subst haAux2_eq
        rw [haAux_eq] at hkresEq
        obtain ⟨hklen_eq, hkargs_lt, hm_klen⟩ := kexprList_length_bd hkargsRep P.hbd hsub_klen evKlen
        subst hm_klen
        rw [evalBinOp_add_field_p opNp1] at hklen
        have hkargs_len : kargs.length = nP + 1 := by
          have h1 : (.field (kargs.length : F) : SourceValue F) = .field ((nP + 1 : Nat) : F) := by
            rw [← hklen_eq, hklen]; push_cast; rfl
          exact nat_eq_of_field_eq_wide_p (by omega) (by omega) (Value.field.inj h1)
        obtain ⟨⟨kidxE, hkidx_get, hkidxTm⟩, hm_kidx⟩ := kexprList_lookup_spec evKidx hkargsRep
        rw [val_natCast_wide_p (by omega)] at hkidx_get
        subst hm_kidx
        obtain ⟨H2, ktArgs, hkidxEq, hH2Tm, hktArgsRep⟩ := collect_spine_tuple_tm evSp2 hkidxTm
        obtain ⟨aKtc, ktLvls, rfl, haKtc, ktLvls', hktLvlsRep, hktLvlsEq⟩ := hH2Tm.const_of_load ldKth
        have hcrC : (Core.posOf cvC.levelParams cvC.type).constsResolve P.env = true := by
          rw [Decl.constsResolve_posOf]
          exact (P.hwf _ (Ix.Kernel.Semantics.Env.find?_mem hfindC)).2.2.1
        have hcr_res : kres.constsResolve P.env = true := constsResolve_stripPisZeta hstrip hcrC
        have hcr_idx : kidxE.constsResolve P.env = true :=
          (constsResolve_mkAppN (hkresEq ▸ hcr_res)).2 kidxE (List.mem_of_getElem? hkidx_get)
        have hcr_ktc : (Expr.const (Core.keyOf P.t (ixAddr aKtc)) ktLvls).constsResolve P.env = true :=
          (constsResolve_mkAppN (hkidxEq ▸ hcr_idx)).1
        have hstKtc := find_isSome_of_constsResolve_const hcr_ktc
        obtain ⟨ciKtc, hfindKtc, vKtc, hldKtc', hrepKtc⟩ := P.getCI_of_stored hstKtc haKtc evKtc hsub_ktc
        rw [ldKtc] at hldKtc'; injection hldKtc' with hveq2
        cases hrepKtc with
        | @ctor _ _ _ _ _ _ _ _ cvKtc nPKtc nFKtc hvKtc hnpKtc hnfKtc hcntKtc hkeyKtc =>
          simp only [Value.construct.injEq, List.cons.injEq, and_true] at hveq2
          obtain ⟨_, _, rfl, -, rfl, rfl, rfl, rfl, rfl, -⟩ := hveq2
          obtain ⟨cmKtc, cbKtc, xsKtc, indKtc, ctKtc, bKtc, iKtc, jKtc,
            hrecCmKtc, hrecCbKtc, hbKtc_rep, hiKtc, hcidxKtc, hi56, hj56, hinfoKtc,
            hmutsKtc, hxsKtc, hctKtc⟩ := P.ctorRecordAt_of_get_ci haKtc evKtc hsub_ktc ldKtc
          have hi0 : iKtc = 0 := Value.field.inj hiKtc.symm
          subst hi0
          obtain ⟨hlvlen_eq, hktLvls_lt, hm_lvlen⟩ :=
            klevelList_length_bd (hktLvlsRep.mono evKtc.heap_extends) P.hbd hsub_lvlen evLvlen
          subst hm_lvlen
          have hktLvls_len : ktLvls.length = cvKtc.levelParams.length := by
            have h1 : (.field (ktLvls'.length : F) : SourceValue F) =
                .field (cvKtc.levelParams.length : F) := by
              rw [← hlvlen_eq, hlvlen, hvKtc.1]
            exact hktLvlsEq.length_eq.trans
              (nat_eq_of_field_eq_wide_p (by omega) (by have := hvKtc.2.1; omega) (Value.field.inj h1))
          obtain ⟨harglen_eq, hktArgs_lt, hm_arglen⟩ := kexprList_length_bd
            (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) evKtc.heap_extends hktArgsRep)
            P.hbd hsub_arglen evArglen
          subst hm_arglen
          rw [hnpKtc, hnfKtc] at opArgsum
          have hktArgs_len : ktArgs.length = nPKtc + nFKtc := by
            have h1 : (.field (ktArgs.length : F) : SourceValue F) =
                .field ((nPKtc + nFKtc : Nat) : F) := by
              rw [← harglen_eq, harglen, evalBinOp_add_field_p opArgsum]; push_cast; rfl
            exact nat_eq_of_field_eq_wide_p (by omega) (by omega) (Value.field.inj h1)
          have ext2 :=
            ext1.trans (evSp2.heap_extends.trans evKtc.heap_extends)
          obtain ⟨hBeq_f, hm_beq⟩ := Lib.address_eq_spec evBeq hbKtc_rep
            (Bytes.repAddressRef_heapMono₂ addrTy ext2 hbTag)
          subst hm_beq
          have hbKtc_eq : bKtc = bTag := by by_contra hne; simp [hne] at hBeq_f
          rw [hbKtc_eq, hbTag_eq] at hinfoKtc hrecCbKtc
          have hnotResKtc : Ix.Kernel.reservedBasisNames.contains (Core.keyOf P.t (ixAddr aKtc)) = false := by
            obtain ⟨cbT, msT, indT, _, hrecBT, hmutsT, hms0T, hgt1T, _, _⟩ := htag_rec
            obtain ⟨G, R, envT, hshape, _⟩ := P.hSE.shape
            exact not_reserved_tag_ctor P.htwf hshape P.hPre hrecBT hmutsT hms0T hgt1T
              htag_neNat hrecCmKtc (by simpa [ZMod.val_zero] using hinfoKtc)
          have hj_u64 : (ZMod.val jKtc).toUInt64.toNat = ZMod.val jKtc := by
            change (UInt64.ofNat _).toNat = _; rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
          have hi_u64 : (0 : UInt64).toNat = 0 := rfl
          let cpKtc : Ixon.ConstructorProj := ⟨(0 : Nat).toUInt64, (ZMod.val jKtc).toUInt64, tagBlk⟩
          have hinfoKtc' : cmKtc.info = .cPrj cpKtc := by simpa [cpKtc, ZMod.val_zero] using hinfoKtc
          let hktcWit : NativeCtorWitness P.t P.E P.env (Core.keyOf P.t (ixAddr aKtc))
              (Core.keyOf P.t (Core.iprjAddr tagBlk 0)) (ZMod.val jKtc) :=
            { addr := ixAddr aKtc
              cm := cmKtc
              cp := cpKtc
              cv := cvKtc
              nP := nPKtc
              nF := nFKtc
              hkey := rfl
              hfind := hfindKtc
              hnotRes := hnotResKtc
              hrec := hrecCmKtc
              hinfo := hinfoKtc'
              hnat := htag_nat
              hindKey := by simp [cpKtc]
              hcidx := hj_u64 }
          have hiff : x_ktc_cidx = .field tagCidxF ↔ ZMod.val jKtc = tagCidx := by
            constructor
            · intro hfeq
              obtain ⟨b', i', j', hb'rep, hi'eq, hj'eq, hname'⟩ := hkeyKtc
              have hb'_eq : b' = bTag := (addr_det hb'rep hbKtc_rep).trans hbKtc_eq
              have hi'_eq : i' = 0 := Value.field.inj hi'eq.symm
              have hj'_eq : j' = tagCidxF := Value.field.inj (hj'eq.symm.trans hfeq)
              subst hb'_eq hi'_eq hj'_eq
              rw [hbTag_eq, ZMod.val_zero] at hname'
              have hcvKtc_name : cvKtc.name = Core.keyOf P.t (ixAddr aKtc) :=
                Ix.Kernel.Semantics.Env.find?_name hfindKtc
              have hkeyEq : Core.keyOf P.t (ixAddr aKtc) = tagCKey := by
                rw [← hcvKtc_name, hname', ← htagC_key_f]
              have haddrEq : ixAddr aKtc = tagCWit.addr :=
                Core.keyOf_inj P.htwf (hkeyEq.trans tagCWit.hkey.symm)
              have hcmEq : cmKtc = tagCWit.cm :=
                Option.some.inj (hrecCmKtc.symm.trans (by rw [haddrEq]; exact tagCWit.hrec))
              have hcpEq : cpKtc = tagCWit.cp :=
                Ixon.ConstantInfo.cPrj.inj (hinfoKtc'.symm.trans (by rw [hcmEq]; exact tagCWit.hinfo))
              rw [← hj_u64]
              change cpKtc.cidx.toNat = tagCidx
              rw [hcpEq]
              exact tagCWit.hcidx
            · intro hceq
              obtain ⟨cbT, msT, indT, ctTag, hrecBT, hmutsT, hms0T, _, hctTag, htagF⟩ := htag_rec
              have hcbEq : cbKtc = cbT := Option.some.inj (hrecCbKtc.symm.trans hrecBT)
              rw [hcbEq, hmutsT] at hmutsKtc
              obtain rfl := Ixon.ConstantInfo.muts.inj hmutsKtc
              rw [ZMod.val_zero, hms0T] at hxsKtc
              obtain rfl := Ixon.MutConst.indc.inj (Option.some.inj hxsKtc)
              rw [hceq, hctTag] at hctKtc
              obtain rfl := Option.some.inj hctKtc
              rw [hcidxKtc, htagF]
          refine ⟨{ ctorKey := Core.keyOf P.t (Core.cprjAddr auxBlk 0 k)
                    cv := cvC
                    knf := knf
                    hfind := hfindC
                    hlvls := hbnl_eq
                    hperm := hpermC
                    kres := kres
                    kargs := kargs
                    auxLvls := auxLvls
                    hstrip := hstrip
                    hkres := hkresEq
                    hkargs_len := hkargs_len
                    ktcKey := Core.keyOf P.t (ixAddr aKtc)
                    ktLvls := ktLvls
                    ktArgs := ktArgs
                    ktcCidx := ZMod.val jKtc
                    hkidx := by rw [hkidx_get, hkidxEq]
                    hktc := hktcWit
                    hktLvls_len := hktLvls_len
                    hktArgs_len := hktArgs_len },
            rfl, hnfC, hcntC.2, hiff, ext2⟩
        | _ => simp [kciEnum] at hveq2
      | _ => simp [kciEnum] at hveq
    match Obs.«KernelModeled::find_aux_ctor_for_tag».obs ev with
    | .n0 (op_mmyajoju := op) .. =>
      have h1 : (anc : F) - (k : F) = 0 := (Value.field.inj (evalBinOp_sub_field_p op)).symm
      have h2 : anc = k := nat_eq_of_field_eq_u56_p hanc (by omega) (sub_eq_zero.mp h1)
      omega
    | .other_n0 (cs_sltnamaq := csC) (cs_lrjqlddc := csPeel) (cs_eclxpkgv := csKlen)
        (cs_hsucgfxz := csKtc) (cs_vvfgeivu := csLvlen) (cs_cztvhame := csArglen)
        (cs_miqzkpej := csRec) (x_ktc_cidx := x_ktc_cidx) (ev_issyabcp := evC) (ld_eknhyjpp := ldC)
        (heq_ygtxaoaq := hknl) (heq_bflcvadk := hknp) (op_jbkebxtb := opTot)
        (ev_zngwgjsi := evPeel) (ev_bnioqzjp := evSp1) (ld_dymazmqy := ldKh)
        (ev_oewgplzh := evAeq) (heq_jicfjvvg := haeq1) (ev_wbkqhkil := evKlen)
        (op_rofnjoic := opNp1) (heq_erlqgkyv := hklen) (ev_wpadjwpw := evKidx)
        (ev_phsqbslk := evSp2) (ld_kjfyernl := ldKth) (ev_hsiyaein := evKtc)
        (ld_dguqqigh := ldKtc) (ev_wnvimqur := evLvlen) (heq_rhtrcenh := hlvlen)
        (ev_dbpiymho := evArglen) (op_yovvzfdl := opArgsum) (heq_bsfpaqfz := harglen)
        (ev_uyjheftf := evBeq) (heq_fdtcdxaq := hbeq1) (heq_wwvvuxpk := hktcind)
        (op_bssudskp := opCidx) (heq_aogltome := hff0) (heq_yvcdobpg := hknfEq)
        (op_ogxhqswp := opK1) (ev_pimyxtkn := evRec) (hc_sdcrobqe := hc) .. =>
      obtain ⟨w, hwKey, hknfVal, hknf56, hiff, extB⟩ := hstep
        (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
        (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
        (hsub _ (by rw [hc]; simp))
        (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
        (hsub _ (by rw [hc]; simp))
        (hsub _ (by rw [hc]; simp))
        evC ldC hknl hknp opTot evPeel evSp1 ldKh evAeq haeq1 evKlen opNp1 hklen evKidx
        evSp2 ldKth evKtc ldKtc evLvlen hlvlen evArglen opArgsum harglen evBeq hbeq1 hktcind
      have hff0' : found_flag = 0 := Value.field.inj hff0
      have hcidxEq : w.ktcCidx = tagCidx := by
        apply hiff.mp
        cases x_ktc_cidx with
        | field f =>
          simp only [evalBinOp, Except.ok.injEq, Value.field.injEq] at opCidx
          exact congrArg Value.field (sub_eq_zero.mp opCidx)
        | ptr _ _ | tuple _ | construct _ _ _ => simp [evalBinOp] at opCidx
      have hknf_eq : w.knf = nF :=
        nat_eq_of_field_eq_u56_p hknf56 hnF (Value.field.inj (hknfVal.symm.trans hknfEq))
      rw [evalBinOp_add_field_p opK1, show (k : F) + 1 = ((k + 1 : Nat) : F) by push_cast; ring] at evRec
      obtain ⟨jIdx, hr, hj_lt, ⟨hj_eq, _⟩, hrest⟩ :=
        ih (k + 1) (by omega) 1 (.field (k : F)) (Or.inr ⟨k, rfl, rfl, by omega⟩)
          (Bytes.repAddressRef_heapMono₂ addrTy extB hbAux)
          (Bytes.repAddressRef_heapMono₂ addrTy extB haAux)
          (Bytes.repAddressRef_heapMono₂ addrTy extB hbTag)
          (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) evRec
      have hk_eq_j : k = jIdx :=
        nat_eq_of_field_eq_u56_p (by omega) (by omega) (Value.field.inj (hj_eq rfl))
      subst hk_eq_j
      refine ⟨k, hr, hk_lt, ⟨fun h1 => absurd (hff0'.symm.trans h1) zero_ne_one, fun _ => Nat.le_refl k⟩,
        fun m hm1 hm2 => ?_⟩
      rcases Nat.eq_or_lt_of_le hm1 with rfl | hgt
      · exact ⟨w, hwKey, fun _ => ⟨hcidxEq, hknf_eq⟩, fun hne => absurd rfl hne⟩
      · exact hrest m hgt hm2
    | .other_other (cs_sltnamaq := csC) (cs_lrjqlddc := csPeel) (cs_eclxpkgv := csKlen)
        (cs_hsucgfxz := csKtc) (cs_vvfgeivu := csLvlen) (cs_cztvhame := csArglen)
        (cs_xbiklrbt := csRec) (ev_issyabcp := evC) (ld_eknhyjpp := ldC)
        (heq_ygtxaoaq := hknl) (heq_bflcvadk := hknp) (op_jbkebxtb := opTot)
        (ev_zngwgjsi := evPeel) (ev_bnioqzjp := evSp1) (ld_dymazmqy := ldKh)
        (ev_oewgplzh := evAeq) (heq_jicfjvvg := haeq1) (ev_wbkqhkil := evKlen)
        (op_rofnjoic := opNp1) (heq_erlqgkyv := hklen) (ev_wpadjwpw := evKidx)
        (ev_phsqbslk := evSp2) (ld_kjfyernl := ldKth) (ev_hsiyaein := evKtc)
        (ld_dguqqigh := ldKtc) (ev_wnvimqur := evLvlen) (heq_rhtrcenh := hlvlen)
        (ev_dbpiymho := evArglen) (op_yovvzfdl := opArgsum) (heq_bsfpaqfz := harglen)
        (ev_uyjheftf := evBeq) (heq_fdtcdxaq := hbeq1) (heq_wwvvuxpk := hktcind)
        (op_bssudskp := opCidx) (hne_trdykyhf := hne0)
        (op_kwhdnbvn := opK1) (ev_xlfhdvvw := evRec) (hc_bmwtsztg := hc) .. =>
      obtain ⟨w, hwKey, _, _, hiff, extB⟩ := hstep
        (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
        (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
        (hsub _ (by rw [hc]; simp))
        (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
        (hsub _ (by rw [hc]; simp))
        (hsub _ (by rw [hc]; simp))
        evC ldC hknl hknp opTot evPeel evSp1 ldKh evAeq haeq1 evKlen opNp1 hklen evKidx
        evSp2 ldKth evKtc ldKtc evLvlen hlvlen evArglen opArgsum harglen evBeq hbeq1 hktcind
      have hcidxNe : w.ktcCidx ≠ tagCidx := by
        intro heq
        have hfeq := hiff.mpr heq
        rw [hfeq] at opCidx
        simp only [evalBinOp, sub_self, Except.ok.injEq] at opCidx
        exact hne0 opCidx.symm
      rw [evalBinOp_add_field_p opK1, show (k : F) + 1 = ((k + 1 : Nat) : F) by push_cast; ring] at evRec
      have hfound' : found_flag = 0 ∨ ∃ j₀ : Nat, found_flag = 1 ∧ found_j = .field (j₀ : F) ∧ j₀ < k + 1 :=
        hfound.imp id fun ⟨j₀, h1, h2, h3⟩ => ⟨j₀, h1, h2, by omega⟩
      obtain ⟨jIdx, hr, hj_lt, ⟨hj1, hj0⟩, hrest⟩ :=
        ih (k + 1) (by omega) found_flag found_j hfound'
          (Bytes.repAddressRef_heapMono₂ addrTy extB hbAux)
          (Bytes.repAddressRef_heapMono₂ addrTy extB haAux)
          (Bytes.repAddressRef_heapMono₂ addrTy extB hbTag)
          (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) evRec
      have hk_ne_j : k ≠ jIdx := by
        rcases hfound with h0 | ⟨j₀, h1, hfj, hj₀_lt⟩
        · have := hj0 h0; omega
        · have hfj' := hj1 h1
          have hjeq := nat_eq_of_field_eq_u56_p (by omega) (by omega) (Value.field.inj (hfj.symm.trans hfj'))
          omega
      refine ⟨jIdx, hr, hj_lt, ⟨hj1, fun h0 => by have := hj0 h0; omega⟩, fun m hm1 hm2 => ?_⟩
      rcases Nat.eq_or_lt_of_le hm1 with rfl | hgt
      · exact ⟨w, hwKey, fun heq => absurd heq hk_ne_j, fun _ => hcidxNe⟩
      · exact hrest m hgt hm2

theorem find_aux_ctor_for_tag_spec (P : ProjsCtx.{u})
    {auxKey tagCKey : KKey} {auxBlk tagBlk : _root_.Address}
    {bAux bTag aAux : Bytes.Address}
    {x_aux_blk x_aux_addr x_tag_blk r : SourceValue F}
    {anc nP bnl tagCidx nF : Nat} {tagCidxF : F} {h h' : Heap F} {cs : List (Call F)}
    (hanc : anc < 72057594037927936) (hnP : nP < 72057594037927936)
    (hbnl : bnl < 4294967296) (hnF : nF < 72057594037927936)
    (hbAux_eq : ixAddr bAux = auxBlk) (hbTag_eq : ixAddr bTag = tagBlk)
    (haAux_eq : Core.keyOf P.t (ixAddr aAux) = auxKey)
    (hfamAux : P.sc.FamAt auxBlk 0)
    (hauxCtorStored : ∀ k < anc, ∃ cv knf,
      P.env.find? (Core.keyOf P.t (Core.cprjAddr auxBlk 0 k)) = some (.ctorInfo cv nP knf))
    (tagCWit : NativeCtorWitness P.t P.E P.env tagCKey (Core.keyOf P.t (Core.iprjAddr tagBlk 0)) tagCidx)
    (htagC_blk : tagCWit.cp.block = tagBlk)
    (htagC_idx : tagCWit.cp.idx.toNat = 0)
    (htagC_key_f : tagCKey = P.sc.κ (Core.cprjAddr tagBlk 0 (ZMod.val tagCidxF)))
    (htag_rec : ∃ cb ms ind ctTag, Ix.Cert.recordAt P.E tagBlk = some cb ∧ cb.info = .muts ms ∧
      ms[0]? = some (.indc ind) ∧ 1 < ind.ctors.size ∧
      ind.ctors[tagCidx]? = some ctTag ∧ tagCidxF = (ctTag.cidx.toNat : F))
    (htag_nat : NativeAt P.E tagBlk)
    (htag_neNat : Core.keyOf P.t (Core.iprjAddr tagBlk 0) ≠ Ix.Kernel.natName)
    (hbAux : Bytes.RepAddressRef addrTy h bAux x_aux_blk)
    (haAux : Bytes.RepAddressRef addrTy h aAux x_aux_addr)
    (hbTag : Bytes.RepAddressRef addrTy h bTag x_tag_blk)
    (hsub : ∀ cl ∈ cs, cl ∈ P.calls)
    (ev : ObsFn Obs.W "KernelModeled::find_aux_ctor_for_tag"
      [x_aux_blk, .field (anc : F), .field 0, .field (nP : F), .field (bnl : F),
       x_aux_addr, x_tag_blk, .field tagCidxF, .field (nF : F),
       .field 0, .field 0] h r h' cs) :
    ∃ jIdx : Nat, r = .field (jIdx : F) ∧ jIdx < anc ∧
      ∀ k < anc,
        ∃ w : AuxCtorTagWitness P.t P.E P.env auxKey
            (Core.keyOf P.t (Core.iprjAddr tagBlk 0)) nP bnl k,
          w.ctorKey = Core.keyOf P.t (Core.cprjAddr auxBlk 0 k) ∧
          (k = jIdx → w.ktcCidx = tagCidx ∧ w.knf = nF) ∧
          (k ≠ jIdx → w.ktcCidx ≠ tagCidx) := by
  obtain ⟨jIdx, hr, hj, -, hall⟩ :=
    find_aux_ctor_for_tag_go P hanc hnP hbnl hnF hbAux_eq hbTag_eq haAux_eq hfamAux
      hauxCtorStored tagCWit htagC_blk htagC_idx htagC_key_f htag_rec htag_nat htag_neNat
      anc 0 (Nat.zero_add anc) 0 (.field 0) (Or.inl rfl) hbAux haAux hbTag hsub (by simpa using ev)
  exact ⟨jIdx, hr, hj, fun k hk => hall k (Nat.zero_le k) hk⟩

/-! ## Section 4: `KernelModeled::check_unpack_rebuild_args` -/

theorem check_unpack_rebuild_args_spec {κ : _root_.Address → KKey}
    {auxKey auxRecKey : KKey} {aAux aAuxRec : Bytes.Address}
    {x_aux_addr x_aux_rec_addr x_ih_args : SourceValue F}
    {nP bnl anc rnf nIh : Nat} {ihArgs : List KExpr}
    (hnP : nP < 72057594037927936) (hbnl : bnl < 4294967296)
    (hanc : anc < 72057594037927936) (hrnf : rnf < 72057594037927936)
    (hnIh : nIh < 2 ^ 39)
    (haAux_eq : κ (ixAddr aAux) = auxKey) (haAuxRec_eq : κ (ixAddr aAuxRec) = auxRecKey) :
    ∀ (fargs : List KExpr) (l : Nat) (hl : l + fargs.length = rnf)
      {remL : KExpr} {x_fargs x_kftele r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      Bounded cs →
      RepList kexprListEnum (fun h A p => Tm κ 0 zeroGhost h (nP + rnf + nIh) A p) h fargs x_fargs →
      Tm κ 0 zeroGhost h (nP + l) remL x_kftele →
      RepList kexprListEnum (fun h A p => Tm κ 0 zeroGhost h (nP + 1 + anc + rnf) A p) h ihArgs x_ih_args →
      Bytes.RepAddressRef addrTy h aAux x_aux_addr →
      Bytes.RepAddressRef addrTy h aAuxRec x_aux_rec_addr →
      ObsFn Obs.W "KernelModeled::check_unpack_rebuild_args"
        [x_fargs, x_kftele, .field (l : F), .field (rnf : F), .field (nIh : F),
         x_ih_args, x_aux_addr, x_aux_rec_addr, .field (nP : F), .field (bnl : F), .field (anc : F)]
        h r h' cs →
      ∃ bsF remF, remL.stripPis fargs.length = some (bsF, remF) ∧
        ∀ i (hi : i < fargs.length),
          UnpackRebuildArgWitness auxKey auxRecKey nP bnl anc rnf nIh ihArgs (l + i)
            (fargs.getD i default) ((bsF.map Prod.fst).getD i default) := by
  intro fargs
  induction fargs with
  | nil =>
    intro l hl remL x_fargs x_kftele r h h' cs hbd hfargs htele hih haAux haAuxRec ev
    match Obs.«KernelModeled::check_unpack_rebuild_args».obs ev with
    | .Nil .. => exact ⟨[], remL, rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    | .Cons (ld_bolbylmd := ld) .. =>
      cases hfargs with
      | nil cell => rw [loadValue_enum_cell cell] at ld; simp at ld
  | cons arg rest ih =>
    intro l hl remL x_fargs x_kftele r h h' cs hbd hfargs htele hih haAux haAuxRec ev
    match Obs.«KernelModeled::check_unpack_rebuild_args».obs ev with
    | .Nil (ld_bolbylmd := ld) .. =>
      cases hfargs with
      | cons cell _ _ => rw [loadValue_enum_cell cell] at ld; simp at ld
    | .Cons (x_arg := x_arg) (x_rest := x_rest) (x_kfdom := x_kfdom) (x_kfrest := x_kfrest)
        (x_bv := x_bv) (m_axniurgo := m_seg) (cs_yyqkawty := cs_seg) (cs_barmioxp := cs_rec)
        (v_vdbsfmsw := v_l1) (ld_bolbylmd := ld_fa) (ld_cmesyczu := ld_kf)
        (ld_imefuuur := ld_bv) (sg_yjhpldho := sg) (op_xupimmsf := op_l1)
        (ev_makrojwj := ev_rec) (hc_ykguwyaf := hc) .. =>
      cases hfargs with
      | cons cell hargTm hrestRep =>
        rw [loadValue_enum_cell cell] at ld_fa
        injection ld_fa with hfa_eq; injection hfa_eq with _ _ hfa_args
        simp only [List.cons.injEq, and_true] at hfa_args
        obtain ⟨rfl, rfl⟩ := hfa_args
        obtain ⟨kfdom, kfrest, ℓkf, rfl, hkfdomTm, hkfrestTm, -⟩ := htele.forallE_of_load ld_kf
        obtain ⟨bv_f, rfl, hbv_small, hbv_lt, rfl⟩ := bvar_of_load_d0 hargTm ld_bv
        have hseg_wit : UnpackRebuildArgWitness auxKey auxRecKey nP bnl anc rnf nIh ihArgs l
            (.bvar (ZMod.val bv_f)) kfdom ∧ Heap.Extends h m_seg := by
          match sg with
          | .n0 (op_fggqedsq := op1) (op_pbldybfb := op2) (op_diezotng := op3)
              (op_akymjsie := op4) (he_oekmaroo := hh_seg) .. =>
            subst hh_seg
            rw [evalBinOp_add_field_p op1] at op2
            rw [evalBinOp_sub_field_p op2] at op3
            rw [evalBinOp_sub_field_p op3] at op4
            have h1 := Value.field.inj (evalBinOp_sub_field_p op4)
            have h2 : bv_f = ((nIh + rnf - 1 - l : Nat) : F) := by
              have hsub := sub_eq_zero.mp h1.symm
              have hcast : ((nIh + rnf - 1 - l : Nat) : F) + 1 + (l : F) = (nIh : F) + (rnf : F) := by
                have hnat : nIh + rnf - 1 - l + 1 + l = nIh + rnf := by simp at hl; omega
                have := congrArg (Nat.cast (R := F)) hnat
                simpa [Nat.cast_add] using this
              linear_combination hsub - hcast
            have hbv_nat : ZMod.val bv_f = nIh + rnf - 1 - l := by
              rw [h2, val_natCast_wide_p (by omega)]
            rw [hbv_nat]
            exact ⟨.nonRec rfl, Heap.Extends.refl _⟩
          | .other (m_mkowpnnv := m_lt) (cs_dpkmnzxy := cs_lt) (v_zxolgasb := v_idx)
              (x_lglrrkly := v_nih1) (v_uowknteu := v_ih) (m_zfkjqrfp := m_ih)
              (cs_wymehdot := cs_ih) (m_bwanvbyi := m_sp) (cs_ibhmfgdg := cs_sp)
              (x_ih_h := x_ih_h) (x_ih_sargs := x_ih_sargs) (x_ih_rec := x_ih_rec)
              (x_ih_lvls := x_ih_lvls) (m_fcbaziza := m_aeq) (cs_wriqefnl := cs_aeq)
              (m_nidmcbzx := m_leq) (cs_pkhdtuke := cs_leq) (v_udigwbmw := v_lvls)
              (m_mxgnnfqs := m_lvls) (cs_nforzuqp := cs_lvls) (v_vkbkeqar := v_bnl1)
              (v_rkslpqvw := v_slen) (v_bbqnzfkp := v_slen_e) (m_ejdrfphe := m_slen)
              (cs_wywitdqv := cs_slen) (x_cfkowjky := x_cf) (x_upcwbnon := x_up)
              (m_hfgkpoqo := m_peq) (cs_fsuosijv := cs_peq) (v_uosvznxu := v_take)
              (v_pboxdmpp := v_bvs) (m_vmxkkmyc := m_take) (cs_qjuhkazu := cs_take)
              (v_klgdyjgc := v_preflen) (x_jmrjipch := x_jm) (m_xjmmsvwc := m_bvs)
              (cs_clxqpvkl := cs_bvs) (v_pxeuxlla := v_bvstart) (v_cbfzzjke := v_bvcnt)
              (x_dxirlmal := x_dx) (x_ffcvtsbk := x_ff) (x_ucvxzopf := x_uc)
              (v_rouwgxpl := v_maj) (m_yatakenr := m_maj) (cs_iswwuoxv := cs_maj)
              (v_lfuuedsm := v_majidx) (x_olknstel := x_ol) (x_dzhtpbwk := x_dz)
              (x_mbv := x_mbv) (v_aqsevwta := v_rnf1l) (x_pvhhjznh := x_rnf1)
              (m_kkavwlbv := m_kfsp) (cs_irwttmkv := cs_kfsp) (x_kfh := x_kfh)
              (x_kfh_addr := x_kfh_addr) (m_ojieqfxy := m_kfaeq) (cs_ehyyqaxc := cs_kfaeq)
              (ev_rfayeznu := evLt) (heq_kxtwynur := hlt1)
              (op_xamhqerg := opNih1) (op_khvknfha := opIdx) (ev_mhqmryog := evLkp)
              (ev_rphrsbqt := evSp) (ld_uoohrygz := ldIh) (ev_ifvmpplf := evAeq)
              (heq_dopqidyu := haeq1) (op_nopdnwmj := opBnl1) (ev_fkklindy := evLvls)
              (ev_hwkdmnlq := evLeq) (heq_vbaupdzi := hleq1)
              (ev_wunrbvie := evSlen) (op_kdjwbrby := opS1) (op_valqwjmt := opS2)
              (op_qgesgrqk := opS3) (heq_wtkgjmvu := hslenEq)
              (op_pgkarsyb := opP1) (op_gofgxhpp := opP2) (ev_eshfxwok := evTake)
              (op_hkibwmth := opB1) (op_efgerhfv := opB2) (op_cchfcuss := opB3)
              (op_gkoimhqd := opC1) (op_fjekcwqj := opC2) (ev_hmvegway := evBvs)
              (ev_liiembai := evPeq) (heq_uzhoubwc := hpeq1)
              (op_wtyudiqk := opM1) (op_cjmnpgaf := opM2) (op_gywxqdbh := opM3)
              (ev_gninmtwd := evMaj) (ld_yhnnolth := ldMaj) (op_tgjctzjb := opR1)
              (op_ulssgkfw := opR2) (heq_hprwgsxw := hmajEq)
              (ev_hlyqyllu := evKfSp) (ld_qqmkwmtr := ldKfh) (ev_mohfynfw := evKfAeq)
              (heq_fxmpsuct := hkfaeq1) (he_xojuvbxz := hh_seg) (hc_defginaw := hc_seg) .. =>
            subst hh_seg hlt1 haeq1 hleq1 hpeq1 hkfaeq1
            obtain ⟨_, _, hlt_iff, _, hm_lt⟩ := Lib.less_than_fields_field evLt
            have hbv_lt_f := hlt_iff.mp rfl
            subst hm_lt
            have hbv_lt_nih : ZMod.val bv_f < nIh := by
              rwa [val_natCast_wide_p (by omega)] at hbv_lt_f
            have hidx_eq : v_idx = .field ((nIh - 1 - ZMod.val bv_f : Nat) : F) := by
              rw [evalBinOp_sub_field_p opNih1] at opIdx
              rw [evalBinOp_sub_field_p opIdx]
              congr 1
              have h1 : ((nIh - 1 - ZMod.val bv_f : Nat) : F) + 1 + bv_f = (nIh : F) := by
                have := ZMod.natCast_zmod_val bv_f
                rw [← this]
                have hnat : nIh - 1 - ZMod.val bv_f + 1 + ZMod.val bv_f = nIh := by omega
                have h2 := congrArg (Nat.cast (R := F)) hnat
                simpa [Nat.cast_add] using h2
              linear_combination -h1
            rw [hidx_eq] at evLkp
            obtain ⟨⟨ihE, hih_get, hihTm⟩, hm_ih⟩ := kexprList_lookup_spec evLkp hih
            rw [val_natCast_wide_p (by omega)] at hih_get
            subst hm_ih
            obtain ⟨H_ih, ihSargs, hihEq, hHihTm, hihSargsRep⟩ := collect_spine_tuple_tm evSp hihTm
            obtain ⟨aRec2, ihLvls, rfl, haRec2, ihLvls', hihLvlsRep, hihLvlsEq⟩ := hHihTm.const_of_load ldIh
            obtain ⟨hAeq_f, hm_aeq⟩ := Lib.address_eq_spec evAeq haRec2
              (Bytes.repAddressRef_heapMono₂ addrTy evSp.heap_extends haAuxRec)
            subst hm_aeq
            have haRec2_eq : aRec2 = aAuxRec := by by_contra hne; simp [hne] at hAeq_f
            subst haRec2_eq
            rw [haAuxRec_eq] at hihEq
            rw [evalBinOp_add_field_p opBnl1, show (bnl : F) + 1 = ((bnl + 1 : Nat) : F) by push_cast; ring] at evLvls
            have hlvlsRep := build_param_lvls_range_start (start := 0) (n := bnl + 1) (by omega) evLvls
            obtain ⟨hlvls_eq, hm_leq⟩ := Decl.level_list_struct_eq_one
              (hihLvlsRep.mono evLvls.heap_extends) hlvlsRep evLeq
            subst hm_leq
            have hihLvls_rel : LvEqList ihLvls ((List.range (bnl + 1)).map Level.param) := by
              rw [hlvls_eq] at hihLvlsEq; simpa using hihLvlsEq
            have ext_sp_lvls := evLvls.heap_extends
            obtain ⟨hslen_f, hihSargs_lt, hm_slen⟩ := kexprList_length_bd
              (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) ext_sp_lvls hihSargsRep)
              hbd (by rw [hc, hc_seg]; simp) evSlen
            subst hm_slen
            rw [evalBinOp_add_field_p opS1] at opS2
            rw [evalBinOp_add_field_p opS2] at opS3
            rw [evalBinOp_add_field_p opS3] at hslenEq
            have hihSargs_len : ihSargs.length = nP + 1 + anc + 2 := by
              have h1 : (.field (ihSargs.length : F) : SourceValue F) =
                  .field ((nP + 1 + anc + 2 : Nat) : F) := by
                rw [← hslen_f, hslenEq]; push_cast; rfl
              exact nat_eq_of_field_eq_wide_p (by omega) (by omega) (Value.field.inj h1)
            have hpreflen_eq : v_preflen = .field ((nP + 1 + anc : Nat) : F) := by
              rw [evalBinOp_add_field_p opP1] at opP2
              rw [evalBinOp_add_field_p opP2]; push_cast; rfl
            rw [hpreflen_eq] at evTake
            obtain ⟨-, htakeRep⟩ := kexprList_take_spec (fun _ _ _ _ ext r => r.mono ext) evTake
              (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) ext_sp_lvls hihSargsRep)
            rw [val_natCast_wide_p (by omega)] at htakeRep
            have hbvstart_eq : v_bvstart = .field ((nP + 1 + anc + rnf : Nat) : F) := by
              rw [evalBinOp_add_field_p opB1] at opB2
              rw [evalBinOp_add_field_p opB2] at opB3
              rw [evalBinOp_add_field_p opB3]; push_cast; rfl
            have hbvcnt_eq : v_bvcnt = .field ((nP + 1 + anc : Nat) : F) := by
              rw [evalBinOp_add_field_p opC1] at opC2
              rw [evalBinOp_add_field_p opC2]; push_cast; rfl
            rw [hbvstart_eq, hbvcnt_eq] at evBvs
            have hbvsRep := bvars_desc_tm_nat (κ := κ) (Γ := zeroGhost)
              (k := nP + 1 + anc + rnf) (start := nP + 1 + anc + rnf) (cnt := nP + 1 + anc)
              (by omega) (by omega) (by omega) evBvs
            have hihPref := spec_params_ptr_eq_tm_one
              (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) evBvs.heap_extends htakeRep) hbvsRep evPeq
            have hmajidx_eq : v_majidx = .field ((nP + 1 + anc + 1 : Nat) : F) := by
              rw [evalBinOp_add_field_p opM1] at opM2
              rw [evalBinOp_add_field_p opM2] at opM3
              rw [evalBinOp_add_field_p opM3]; push_cast; rfl
            rw [hmajidx_eq] at evMaj
            have ext_sp_peq :=
              ext_sp_lvls.trans ((evTake.heap_extends.trans evBvs.heap_extends).trans evPeq.heap_extends)
            obtain ⟨⟨majE, hmaj_get, hmajTm⟩, hm_maj⟩ := kexprList_lookup_spec evMaj
              (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) ext_sp_peq hihSargsRep)
            rw [val_natCast_wide_p (by omega)] at hmaj_get
            subst hm_maj
            obtain ⟨mbv_f, rfl, hmbv_small, hmbv_lt, rfl⟩ := bvar_of_load_d0 hmajTm ldMaj
            have hrnf1l_eq : v_rnf1l = .field ((rnf - 1 - l : Nat) : F) := by
              rw [evalBinOp_sub_field_p opR1] at opR2
              rw [evalBinOp_sub_field_p opR2]
              congr 1
              have h1 : ((rnf - 1 - l : Nat) : F) + 1 + (l : F) = (rnf : F) := by
                have hnat : rnf - 1 - l + 1 + l = rnf := by simp at hl; omega
                have h2 := congrArg (Nat.cast (R := F)) hnat
                simpa [Nat.cast_add] using h2
              linear_combination -h1
            rw [hrnf1l_eq] at hmajEq
            have hmbv_nat : ZMod.val mbv_f = rnf - 1 - l := by
              have h1 := congrArg ZMod.val (Value.field.inj hmajEq)
              rwa [val_natCast_wide_p (by omega)] at h1
            rw [hmbv_nat] at hmaj_get
            have ext_h_peq := evSp.heap_extends.trans ext_sp_peq
            obtain ⟨H_kf, kfArgs, hkfEq, hHkfTm, -⟩ := collect_spine_tuple_tm evKfSp (hkfdomTm.mono ext_h_peq)
            obtain ⟨aAux2, kfLvls, rfl, haAux2, -, -, -⟩ := hHkfTm.const_of_load ldKfh
            have ext_h_kfsp := ext_h_peq.trans evKfSp.heap_extends
            obtain ⟨hKfAeq_f, hm_kfaeq⟩ := Lib.address_eq_spec evKfAeq haAux2
              (Bytes.repAddressRef_heapMono₂ addrTy ext_h_kfsp haAux)
            subst hm_kfaeq
            have haAux2_eq : aAux2 = aAux := by by_contra hne; simp [hne] at hKfAeq_f
            subst haAux2_eq
            rw [haAux_eq] at hkfEq
            exact ⟨.recField (ZMod.val bv_f) ihLvls ihSargs kfLvls kfArgs rfl hbv_lt_nih
              (hihEq ▸ hih_get) hihLvls_rel hihSargs_len hihPref hmaj_get hkfEq, ext_h_kfsp⟩
        obtain ⟨hw0, extSeg⟩ := hseg_wit
        rw [evalBinOp_add_field_p op_l1, show (l : F) + 1 = ((l + 1 : Nat) : F) by push_cast; ring] at ev_rec
        have hbdRec : Bounded cs_rec := bounded_sub (fun _ hcl => by rw [hc]; simp [hcl]) hbd
        obtain ⟨bsF_rest, remF, hstrip_rest, hrest_wit⟩ := ih (l + 1) (by simp at hl; omega) hbdRec
          (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) extSeg hrestRep)
          (by simpa [Nat.add_assoc] using hkfrestTm.mono extSeg)
          (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) extSeg hih)
          (Bytes.repAddressRef_heapMono₂ addrTy extSeg haAux)
          (Bytes.repAddressRef_heapMono₂ addrTy extSeg haAuxRec)
          ev_rec
        refine ⟨(kfdom, Core.bmeta ℓkf) :: bsF_rest, remF, by simp [Expr.stripPis, hstrip_rest], ?_⟩
        intro i hi
        cases i with
        | zero => simpa using hw0
        | succ i' =>
          have h1 := hrest_wit i' (by simpa using hi)
          simpa [Nat.add_assoc, Nat.add_comm 1 i'] using h1

/-! ## Section 5: `KernelModeled::check_unpack_minors` -/

theorem check_unpack_minors_spec (P : ProjsCtx.{u})
    {auxKey auxRecKey : KKey} {auxBlk : _root_.Address}
    {bAux aAux aAuxRec : Bytes.Address}
    {x_aux_blk x_aux_addr x_aux_rec_addr : SourceValue F}
    {auxRecLps : List LevelParam} {nP bnl anc : Nat}
    (hnP : nP < 72057594037927936) (hbnl : bnl < 4294967296) (hanc : anc < 72057594037927936)
    (hbAux_eq : ixAddr bAux = auxBlk)
    (haAux_eq : Core.keyOf P.t (ixAddr aAux) = auxKey)
    (haAuxRec_eq : Core.keyOf P.t (ixAddr aAuxRec) = auxRecKey)
    (hfamAux : P.sc.FamAt auxBlk 0)
    (hauxCtorStored : ∀ k < anc, ∃ cv knf,
      P.env.find? (Core.keyOf P.t (Core.cprjAddr auxBlk 0 k)) = some (.ctorInfo cv nP knf))
    {cvAuxRec : ConstantVal .anon} {allRules : List (RecRule .anon)}
    (hfindAuxRec : P.env.find? auxRecKey =
      some (.recInfo cvAuxRec (nP + 1 + anc + 1) (nP + 1 + anc) allRules))
    (hrecCtor : ∀ j rl, allRules[j]? = some rl → rl.ctor = Core.keyOf P.t (Core.cprjAddr auxBlk 0 j)) :
    ∀ (minors : List KExpr) (rls : List (RecRule .anon)) (k : Nat)
      (hk : k + minors.length = anc)
      (hrls_sub : ∀ i rl, rls[i]? = some rl → allRules[k + i]? = some rl)
      {x_minors x_arules r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
      RepList kexprListEnum (fun h A p => Tm (Core.keyOf P.t) 0 zeroGhost h nP A p) h minors x_minors →
      (∀ m ∈ minors, m.constsResolve P.env = true) →
      RulesRep (Core.keyOf P.t) h auxRecLps k x_arules rls →
      Bytes.RepAddressRef addrTy h bAux x_aux_blk →
      Bytes.RepAddressRef addrTy h aAux x_aux_addr →
      Bytes.RepAddressRef addrTy h aAuxRec x_aux_rec_addr →
      (∀ cl ∈ cs, cl ∈ P.calls) →
      ObsFn Obs.W "KernelModeled::check_unpack_minors"
        [x_minors, x_arules, x_aux_blk, x_aux_addr, x_aux_rec_addr,
         .field (nP : F), .field (bnl : F), .field (anc : F), .field (k : F)]
        h r h' cs →
      rls.length = minors.length ∧
      ∀ i (hi : i < minors.length),
        ∃ rl, rls[i]? = some rl ∧
          Nonempty (UnpackMinorWitness P.t P.E P.env auxKey auxRecKey auxRecLps
            (Core.keyOf P.t (Core.cprjAddr auxBlk 0 (k + i))) nP bnl anc (k + i)
            (minors.getD i default) rl) := by
  intro minors
  induction minors with
  | nil =>
    intro rls k hk hrls_sub x_minors x_arules r h h' cs hmin hcr hrules hbAux haAux haAuxRec hsub ev
    match Obs.«KernelModeled::check_unpack_minors».obs ev with
    | .Nil (ld_ylavbzof := ldR) .. =>
      cases hrules with
      | nil _ => exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
      | cons cell _ _ => rw [loadValue_enum_cell cell] at ldR; simp at ldR
    | .Cons_n1 (ld_bolbylmd := ldM) .. | .Cons_other (ld_bolbylmd := ldM) .. =>
      cases hmin with
      | nil cell => rw [loadValue_enum_cell cell] at ldM; simp at ldM
  | cons minor mrest ih =>
    intro rls k hk hrls_sub x_minors x_arules r h h' cs hmin hcr hrules hbAux haAux haAuxRec hsub ev
    have hk_lt : k < anc := by simp at hk; omega
    match Obs.«KernelModeled::check_unpack_minors».obs ev with
    | .Nil (ld_bolbylmd := ldM) .. =>
      cases hmin with
      | cons cell _ _ => rw [loadValue_enum_cell cell] at ldM; simp at ldM
    | .Cons_n1 (x_minor_k := x_mk) (x_mrest := x_mrest) (x_rule_k := x_rk) (x_rrest := x_rrest)
        (m_cjhqbeug := m_ih) (cs_vjuksxxi := cs_ih) (x_rnf_k := x_rnf) (x_ih_args := x_ih_args)
        (v_woodzyxz := v_nih) (m_kufuitih := m_nih) (cs_cualfcwu := cs_nih)
        (m_nnrlphqw := m_peel) (cs_vhkpaeir := cs_peel) (v_hyenppsh := v_tot1)
        (m_gxahsgkq := m_nil) (x_mbody_k := x_mbody) (x_mpeeled_k := x_mpeeled)
        (v_geqprxpl := v_tot2) (m_aueknfej := m_sp) (cs_jwrngahy := cs_sp)
        (x_mh_k := x_mh) (x_margs_k := x_margs) (v_osrclnbq := v_plvls)
        (m_yhjlydbh := m_plvls) (cs_cduorzad := cs_plvls) (v_dtaujabo := v_auxc)
        (m_wpobiuyt := m_auxc) (cs_gkvgafed := cs_auxc) (x_mc_addr := x_mc_addr)
        (x_mc_lvls := x_mc_lvls) (m_mnshbkvs := m_aeq) (cs_mbwldfnn := cs_aeq)
        (m_salxodax := m_succ) (m_rwzwzmzu := m_zero) (v_sefozmhw := v_pw)
        (m_urzizksh := m_pw) (cs_xswvhkbb := cs_pw) (v_fbytnpjn := v_tot3)
        (v_zfftvstl := v_leq) (m_ickcwtpj := m_leq) (cs_mbatylgg := cs_leq)
        (v_egwdfqoo := v_mlen) (v_xhcictzj := v_nprnf) (m_mlwucwyy := m_mlen)
        (cs_vxxvuhmz := cs_mlen) (v_nyxbzskt := v_peq1) (m_trxzalgx := m_peq1)
        (cs_uzssntwg := cs_peq1) (v_wpqgazxa := v_take) (v_xzthbqfn := v_bv1)
        (m_uiambqec := m_take) (cs_fyzscyee := cs_take) (m_jwrznxvy := m_bv1)
        (cs_podwhswu := cs_bv1) (v_fgmjfonp := v_start1) (x_xvrcuezp := x_xv)
        (v_pwnxmjrq := v_peq2) (m_lkxwpvkr := m_peq2) (cs_fsvwnohh := cs_peq2)
        (v_vorptpbu := v_drop) (v_ggtwmwqh := v_bv2) (m_jfqgrnqb := m_drop)
        (cs_rhhznrmv := cs_drop) (m_xvbbxfxq := m_bv2) (cs_rnzbkgvd := cs_bv2)
        (v_iykouvue := v_start2) (cs_zfnnovea := cs_rec) (v_vmicjiof := v_k1)
        (ld_bolbylmd := ldM) (ld_ihqqubap := ldR) (ev_lxubeqgr := evIh)
        (ev_abvtsmte := evNih) (op_qootdwat := opTot1) (hm_blpsekwn := hmNil)
        (ev_bbafyfnm := evPeel) (op_dreixede := opTot2) (heq_vpdiqlzz := hmpeeled)
        (ev_gsxgfpma := evSp) (ev_majjfziw := evPlvls) (ev_atrrcaah := evAuxC)
        (ld_jmlgtrux := ldMh) (ev_kttiftek := evAeq) (hm_tufwxakm := hmSucc)
        (hm_svfypdew := hmZero) (op_jklsftdi := opTot3) (ev_eqiwhekx := evPw)
        (ev_vuvtyenm := evLeq) (heq_grzbhuma := hleq1) (ev_vfxyzzrg := evMlen)
        (op_qddyacrr := opNprnf) (heq_jgmseagw := hmlen) (ev_zfvfyjcb := evTake)
        (op_lqvmzrqd := opS1a) (op_aklhiclr := opS1b) (ev_bhalevnw := evBv1)
        (ev_fioaraud := evPeq1) (heq_whxdunih := hpeq1) (ev_jtxtvfvt := evDrop)
        (op_srohvrnt := opS2) (ev_gaxbtwin := evBv2) (ev_dpqaevrb := evPeq2)
        (heq_bfycqatt := hpeq2) (op_zyevxmzu := opK1) (ev_vbkrxazh := evRec)
        (hc_gsysyyvr := hc) .. =>
      subst hleq1 hpeq1 hpeq2
      cases hmin with
      | cons cellM hminorTm hmrestRep =>
        rw [loadValue_enum_cell cellM] at ldM; injection ldM with hmeq; injection hmeq with _ _ hmargs
        simp only [List.cons.injEq, and_true] at hmargs; obtain ⟨rfl, rfl⟩ := hmargs
        cases hrules with
        | nil cellR => rw [loadValue_enum_cell cellR] at ldR; simp at ldR
        | @cons _ _ _ _ rl rrest cellR hrlRep hrrRep =>
          rw [loadValue_enum_cell cellR] at ldR; injection ldR with hreq; injection hreq with _ _ hrargs
          simp only [List.cons.injEq, and_true] at hrargs; obtain ⟨rfl, rfl⟩ := hrargs
          have hrnf56 : rl.nfields < 72057594037927936 := by
            obtain ⟨_, _, h56, _⟩ := hrlRep; exact h56
          obtain ⟨hrnf_eq, rbs, rargs, hr_strip, hrargs_ge, hrargs_lt, hrargs_fields, hihRep⟩ :=
            rec_rule_ih_args_spec hnP hanc hk_lt
              (P.hbdSub (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))) hrlRep evIh
          subst hrnf_eq
          obtain ⟨hnih_f, hnih_lt, hm_nih⟩ := kexprList_length_bd hihRep P.hbd
            (hsub _ (by rw [hc]; simp)) evNih
          subst hm_nih
          have hnih_eq : (rargs.drop rl.nfields).length = rargs.length - rl.nfields :=
            List.length_drop ..
          rw [hnih_eq] at hnih_f hnih_lt
          rw [hnih_f] at opTot1 opTot2 opTot3 opS1b opS2
          have htot_eq : v_tot1 = .field ((rl.nfields + (rargs.length - rl.nfields) : Nat) : F) := by
            rw [evalBinOp_add_field_p opTot1]; push_cast; rfl
          have htot2_eq : v_tot2 = .field ((rl.nfields + (rargs.length - rl.nfields) : Nat) : F) := by
            rw [evalBinOp_add_field_p opTot2]; push_cast; rfl
          have htot3_eq : v_tot3 = .field ((rl.nfields + (rargs.length - rl.nfields) : Nat) : F) := by
            rw [evalBinOp_add_field_p opTot3]; push_cast; rfl
          rw [htot_eq] at evPeel; rw [htot2_eq] at hmpeeled; rw [htot3_eq] at evPw
          have extNil : Heap.Extends h m_nil :=
            evIh.heap_extends.trans (by rw [hmNil]; exact Heap.Extends.snoc _ _)
          rw [hmpeeled] at evPeel
          obtain ⟨mbs, mbody, hmin_strip, hmbodyTm⟩ :=
            peel_n_lams_collect_tm_nat (n := rl.nfields + (rargs.length - rl.nfields))
              (by omega) (hminorTm.mono extNil) evPeel
          obtain ⟨H_m, margs, hmbodyEq, hHmTm, hmargsRep⟩ := collect_spine_tuple_tm evSp hmbodyTm
          have hplvlsRep := (show ((List.range bnl).map fun k => Level.param (0 + k)) = (List.range bnl).map Level.param by simp) ▸ build_param_lvls_range_start (start := 0) (n := bnl) (by omega) evPlvls
          have extPlvls : Heap.Extends h m_plvls :=
            extNil.trans (evPeel.heap_extends.trans (evSp.heap_extends.trans evPlvls.heap_extends))
          obtain ⟨aAuxC, haAuxC_rep, haAuxC_eq⟩ := projection_addr_ctor_bounded evAuxC
            (P.hbdSub (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])))
            (Bytes.repAddressRef_heapMono₂ addrTy extPlvls hbAux)
          rw [hbAux_eq, ZMod.val_zero, val_natCast_wide_p (by omega)] at haAuxC_eq
          obtain ⟨aMc, mcLvls, rfl, haMc, mcLvls', hmcLvlsRep, hmcLvlsEq⟩ :=
            (hHmTm.mono (evPlvls.heap_extends.trans evAuxC.heap_extends)).const_of_load ldMh
          obtain ⟨hAeq_f, hm_aeq⟩ := Lib.address_eq_spec evAeq haMc haAuxC_rep
          subst hm_aeq
          have haMc_eq : aMc = aAuxC := by by_contra hne; simp [hne] at hAeq_f
          have hmcKey_eq : Core.keyOf P.t (ixAddr aMc) = Core.keyOf P.t (Core.cprjAddr auxBlk 0 k) := by
            rw [haMc_eq, haAuxC_eq]
          rw [hmcKey_eq] at hmbodyEq
          -- `peel_n_lams_pw_eq` with `Succ Zero` gives `bm.2.pw = .never`
          have extSucc : Heap.Extends m_aeq m_succ := by
            rw [hmSucc, hmZero]
            exact (Heap.Extends.snoc _ _).trans (Heap.Extends.snoc _ _)
          have hrepZero : RepKLevel m_zero .zero (.ptr (.enum KernelLevels.klevelEnum) m_aeq.length) := by
            rw [hmZero]; exact .zero (by simp)
          have hrepSucc : RepKLevel m_succ (.succ .zero) (.ptr (.enum KernelLevels.klevelEnum) m_zero.length) := by
            rw [hmSucc]
            exact .succ (by simp) (hrepZero.mono (Heap.Extends.snoc _ _))
          have extH_succ := (extPlvls.trans evAuxC.heap_extends).trans extSucc
          obtain ⟨mbs', _, hmin_strip', _, hmbs'_pw⟩ :=
            peel_n_lams_pw_eq_tm (rl.nfields + (rargs.length - rl.nfields)) (by omega)
              (hminorTm.mono extH_succ) hrepSucc evPw
          have hmbs_eq : mbs = mbs' := by
            have := Option.some.inj (hmin_strip.symm.trans hmin_strip')
            exact congrArg Prod.fst this
          subst hmbs_eq
          have ext_sp_pw :=
            (evPlvls.heap_extends.trans evAuxC.heap_extends).trans (extSucc.trans evPw.heap_extends)
          obtain ⟨hmcLvls_eq, hm_leq⟩ := Decl.level_list_struct_eq_one
            (hmcLvlsRep.mono (extSucc.trans evPw.heap_extends))
            (hplvlsRep.mono (evAuxC.heap_extends.trans (extSucc.trans evPw.heap_extends))) evLeq
          subst hm_leq
          have hmcLvls_rel : LvEqList mcLvls ((List.range bnl).map Level.param) := by
            rw [hmcLvls_eq] at hmcLvlsEq; simpa using hmcLvlsEq
          have hmargsRep_pw := RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) ext_sp_pw hmargsRep
          obtain ⟨hmlen_f, hmargs_lt, hm_mlen⟩ := kexprList_length_bd hmargsRep_pw P.hbd
            (hsub _ (by rw [hc]; simp)) evMlen
          subst hm_mlen
          rw [evalBinOp_add_field_p opNprnf] at hmlen
          have hmargs_len : margs.length = nP + rl.nfields := by
            have h1 : (.field (margs.length : F) : SourceValue F) =
                .field ((nP + rl.nfields : Nat) : F) := by
              rw [← hmlen_f, hmlen]; push_cast; rfl
            exact nat_eq_of_field_eq_wide_p (by omega) (by omega) (Value.field.inj h1)
          obtain ⟨-, htakeRep⟩ := kexprList_take_spec (fun _ _ _ _ ext r => r.mono ext) evTake hmargsRep_pw
          rw [val_natCast_wide_p (by omega)] at htakeRep
          have hs1_eq : v_start1 = .field ((nP + rl.nfields + (rargs.length - rl.nfields) : Nat) : F) := by
            rw [evalBinOp_add_field_p opS1a] at opS1b
            rw [evalBinOp_add_field_p opS1b]; push_cast; rfl
          rw [hs1_eq] at evBv1
          have hbv1Rep := bvars_desc_tm_nat (κ := Core.keyOf P.t) (Γ := zeroGhost)
            (k := nP + (rl.nfields + (rargs.length - rl.nfields)))
            (start := nP + rl.nfields + (rargs.length - rl.nfields)) (cnt := nP)
            (by omega) (by omega) (by omega) evBv1
          have hmargs_take := spec_params_ptr_eq_tm_one
            (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) evBv1.heap_extends htakeRep) hbv1Rep evPeq1
          have ext_pw_peq1 :=
            (evTake.heap_extends.trans evBv1.heap_extends).trans evPeq1.heap_extends
          obtain ⟨-, hdropRep, hm_drop⟩ := kexprList_drop_spec evDrop
            (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) ext_pw_peq1 hmargsRep_pw)
          rw [val_natCast_wide_p (by omega)] at hdropRep
          subst hm_drop
          have hs2_eq : v_start2 = .field ((rl.nfields + (rargs.length - rl.nfields) : Nat) : F) := by
            rw [evalBinOp_add_field_p opS2]; push_cast; rfl
          rw [hs2_eq] at evBv2
          have hbv2Rep := bvars_desc_tm_nat (κ := Core.keyOf P.t) (Γ := zeroGhost)
            (k := nP + (rl.nfields + (rargs.length - rl.nfields)))
            (start := rl.nfields + (rargs.length - rl.nfields)) (cnt := rl.nfields)
            (by omega) (by omega) (by omega) evBv2
          have hmargs_drop := spec_params_ptr_eq_tm_one
            (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) evBv2.heap_extends hdropRep) hbv2Rep evPeq2
          have ext_h_peq2 : Heap.Extends h m_peq2 :=
            (extH_succ.trans evPw.heap_extends).trans
              (ext_pw_peq1.trans (evBv2.heap_extends.trans evPeq2.heap_extends))
          rw [evalBinOp_add_field_p opK1, show (k : F) + 1 = ((k + 1 : Nat) : F) by push_cast; ring] at evRec
          obtain ⟨hlen_rest, hrest_wit⟩ := ih rrest (k + 1) (by simp at hk; omega)
            (fun i rl' hi => by
              have h1 := hrls_sub (i + 1) rl' hi
              rwa [show k + (i + 1) = k + 1 + i by omega] at h1)
            (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) ext_h_peq2 hmrestRep)
            (fun m hm => hcr m (List.mem_cons_of_mem _ hm))
            (hrrRep.mono ext_h_peq2)
            (Bytes.repAddressRef_heapMono₂ addrTy ext_h_peq2 hbAux)
            (Bytes.repAddressRef_heapMono₂ addrTy ext_h_peq2 haAux)
            (Bytes.repAddressRef_heapMono₂ addrTy ext_h_peq2 haAuxRec)
            (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) evRec
          refine ⟨by simp [hlen_rest], fun i hi => ?_⟩
          cases i with
          | zero =>
            refine ⟨rl, rfl, ⟨{
              rnf := rl.nfields
              hrnf := rfl
              rbs := rbs
              rargs := rargs
              hr_strip := hr_strip
              hrargs_ge := hrargs_ge
              hrargs_fields := hrargs_fields
              mbs := mbs
              mcKey := Core.keyOf P.t (Core.cprjAddr auxBlk 0 k)
              mcLvls := mcLvls
              margs := margs
              hmin_strip := hmbodyEq ▸ hmin_strip
              hbranch := Or.inl ⟨rfl, fun bm hbm => by
                  simpa [Ix.Kernel.Level.zeronessOf] using hmbs'_pw bm hbm,
                hmcLvls_rel, hmargs_len, hmargs_take, hmargs_drop⟩ }⟩⟩
          | succ i' =>
            obtain ⟨rl', hrl', hw'⟩ := hrest_wit i' (by simpa using hi)
            refine ⟨rl', hrl', ?_⟩
            simpa [Nat.add_assoc, Nat.add_comm 1 i'] using hw'
    | .Cons_other (x_minor_k := x_mk) (x_mrest := x_mrest) (x_rule_k := x_rk) (x_rrest := x_rrest)
        (m_cjhqbeug := m_ih) (cs_vjuksxxi := cs_ih) (x_rnf_k := x_rnf) (x_ih_args := x_ih_args)
        (v_woodzyxz := v_nih) (m_kufuitih := m_nih) (cs_cualfcwu := cs_nih)
        (m_nnrlphqw := m_peel) (cs_vhkpaeir := cs_peel) (v_hyenppsh := v_tot1)
        (m_gxahsgkq := m_nil) (x_mbody_k := x_mbody) (x_mpeeled_k := x_mpeeled)
        (v_geqprxpl := v_tot2) (m_aueknfej := m_sp) (cs_jwrngahy := cs_sp)
        (x_mh_k := x_mh) (x_margs_k := x_margs) (v_osrclnbq := v_plvls)
        (m_yhjlydbh := m_plvls) (cs_cduorzad := cs_plvls) (v_dtaujabo := v_auxc)
        (m_wpobiuyt := m_auxc) (cs_gkvgafed := cs_auxc) (m_uotxwmxo := m_reb)
        (x_mc_addr := x_mc_addr) (x_mc_lvls := x_mc_lvls) (v_tbkpvhxw := v_aeq)
        (m_mnshbkvs := m_aeq) (cs_mbwldfnn := cs_aeq) (m_yqjaettj := m_mc)
        (p_jcxixttw := p_mc) (cs_yzxpuuhb := cs_mc) (x_cnl_k := x_cnl)
        (x_cblk_k := x_cblk) (x_cind_k := x_cind) (x_cnp_k := x_cnp) (x_cnf_k := x_cnf)
        (m_ocwwcsxl := m_mod) (cs_gpmsikbn := cs_mod) (m_ugdchfiq := m_iz) (cs_ldodaijo := cs_iz)
        (v_opewidnb := v_lvlen) (m_fnoqmwqi := m_lvlen) (cs_ilaspwja := cs_lvlen)
        (v_qdxqsnvh := v_mlen) (v_cbyrqphc := v_cnpf) (m_oxtdieat := m_mlen) (cs_kdvkfcnm := cs_mlen)
        (m_elmvwbxe := m_iprj) (p_tjpeqylo := p_iprj) (cs_ocivzsdb := cs_iprj)
        (x_inl_k := x_inl) (x_ity_k := x_ity) (x_inp_k := x_inp) (x_ini_k := x_ini)
        (m_xdsifdqt := m_seg) (cs_riyxiwxg := cs_seg)
        (m_kzsrakgf := m_auxc_ci) (p_cppezrvz := p_auxc_ci) (cs_ljwlxdrj := cs_auxc_ci)
        (x_kty := x_kty) (v_aiotfphx := v_kftele) (m_ptkbdsnr := m_pfor) (cs_iwbkrukp := cs_pfor)
        (cs_myounysu := cs_reb) (v_ckfogytj := v_fargs) (m_rzbxqvqz := m_drop) (cs_nwupzgfz := cs_drop)
        (cs_rphvqyts := cs_rec) (v_fjvlzcfh := v_k1)
        (ld_bolbylmd := ldM) (ld_ihqqubap := ldR) (ev_lxubeqgr := evIh)
        (ev_abvtsmte := evNih) (op_qootdwat := opTot1) (hm_blpsekwn := hmNil)
        (ev_bbafyfnm := evPeel) (op_dreixede := opTot2) (heq_vpdiqlzz := hmpeeled)
        (ev_gsxgfpma := evSp) (ev_majjfziw := evPlvls) (ev_atrrcaah := evAuxC)
        (ld_jmlgtrux := ldMh) (ev_kttiftek := evAeq) (hne_qoxsgczv := hneAeq)
        (ev_nmsursiw := evMc) (ld_gjxeyajc := ldMc) (heq_spaxxwkm := hcnfEq)
        (ev_gkdcserz := evMod) (heq_nkqjabtc := hmod0) (ev_ebvtomzt := evIz) (heq_qrpylspz := hiz0)
        (ev_bsdtfwdk := evLvlen) (heq_yamojcpo := hlvlen) (ev_mhvebsca := evMlen)
        (op_fwicspbq := opCnpf) (heq_kbtklekg := hmlen) (ev_bvlvhpke := evIprj)
        (ld_jbhcgzuu := ldIprj) (heq_ddwfaloy := hinlEq) (heq_sztkdwuc := hinpEq)
        (sg_hryilmzi := sgSort) (ev_hfhausdh := evAuxC_ci) (ld_ncqkeouc := ldAuxC_ci)
        (ev_owgkqevj := evPfor) (ev_iqgocfst := evDrop) (ev_eiybxtzi := evReb)
        (op_agaksyuo := opK1) (ev_uzymlhvb := evRec) (hc_tmxzbzju := hc) .. =>
      subst hmod0 hiz0
      cases hmin with
      | cons cellM hminorTm hmrestRep =>
        rw [loadValue_enum_cell cellM] at ldM; injection ldM with hmeq; injection hmeq with _ _ hmargs
        simp only [List.cons.injEq, and_true] at hmargs; obtain ⟨rfl, rfl⟩ := hmargs
        cases hrules with
        | nil cellR => rw [loadValue_enum_cell cellR] at ldR; simp at ldR
        | @cons _ _ _ _ rl rrest cellR hrlRep hrrRep =>
          rw [loadValue_enum_cell cellR] at ldR; injection ldR with hreq; injection hreq with _ _ hrargs
          simp only [List.cons.injEq, and_true] at hrargs; obtain ⟨rfl, rfl⟩ := hrargs
          have hrnf56 : rl.nfields < 72057594037927936 := by
            obtain ⟨_, _, h56, _⟩ := hrlRep; exact h56
          obtain ⟨hrnf_eq, rbs, rargs, hr_strip, hrargs_ge, hrargs_lt, hrargs_fields, hihRep⟩ :=
            rec_rule_ih_args_spec hnP hanc hk_lt
              (P.hbdSub (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))) hrlRep evIh
          subst hrnf_eq
          obtain ⟨hnih_f, hnih_lt, hm_nih⟩ := kexprList_length_bd hihRep P.hbd
            (hsub _ (by rw [hc]; simp)) evNih
          subst hm_nih
          have hnih_eq : (rargs.drop rl.nfields).length = rargs.length - rl.nfields := List.length_drop ..
          rw [hnih_eq] at hnih_f hnih_lt
          rw [hnih_f] at opTot1 opTot2
          have htot_eq : v_tot1 = .field ((rl.nfields + (rargs.length - rl.nfields) : Nat) : F) := by
            rw [evalBinOp_add_field_p opTot1]; push_cast; rfl
          have htot2_eq : v_tot2 = .field ((rl.nfields + (rargs.length - rl.nfields) : Nat) : F) := by
            rw [evalBinOp_add_field_p opTot2]; push_cast; rfl
          rw [htot_eq] at evPeel; rw [htot2_eq] at hmpeeled
          have extNil : Heap.Extends h m_nil :=
            evIh.heap_extends.trans (by rw [hmNil]; exact Heap.Extends.snoc _ _)
          rw [hmpeeled] at evPeel
          obtain ⟨mbs, mbody, hmin_strip, hmbodyTm⟩ :=
            peel_n_lams_collect_tm_nat (n := rl.nfields + (rargs.length - rl.nfields))
              (by omega) (hminorTm.mono extNil) evPeel
          obtain ⟨H_m, margs, hmbodyEq, hHmTm, hmargsRep⟩ := collect_spine_tuple_tm evSp hmbodyTm
          have extPlvls : Heap.Extends h m_plvls :=
            extNil.trans (evPeel.heap_extends.trans (evSp.heap_extends.trans evPlvls.heap_extends))
          obtain ⟨aAuxC, haAuxC_rep, haAuxC_eq⟩ := projection_addr_ctor_bounded evAuxC
            (P.hbdSub (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])))
            (Bytes.repAddressRef_heapMono₂ addrTy extPlvls hbAux)
          rw [hbAux_eq, ZMod.val_zero, val_natCast_wide_p (by omega)] at haAuxC_eq
          obtain ⟨aMc, mcLvls, rfl, haMc, mcLvls', hmcLvlsRep, hmcLvlsEq⟩ :=
            (hHmTm.mono (evPlvls.heap_extends.trans evAuxC.heap_extends)).const_of_load ldMh
          obtain ⟨hAeq_f, hm_aeq⟩ := Lib.address_eq_spec evAeq haMc haAuxC_rep
          subst hm_aeq
          have haMc_ne : aMc ≠ aAuxC := by
            intro heq; subst heq; simp at hAeq_f; exact hneAeq hAeq_f
          have hmcKey_ne : Core.keyOf P.t (ixAddr aMc) ≠ Core.keyOf P.t (Core.cprjAddr auxBlk 0 k) := by
            intro hkeq
            have haeq := Core.keyOf_inj P.htwf hkeq
            rw [← haAuxC_eq] at haeq
            exact haMc_ne (Decl.ixAddr_inj haeq)
          -- `aMc` resolves because `minor` resolves in `P.env`
          have hcrM : minor.constsResolve P.env = true := hcr minor List.mem_cons_self
          have hcr_body : mbody.constsResolve P.env = true := constsResolve_stripLams hcrM hmin_strip
          have hcr_mc : (Expr.const (Core.keyOf P.t (ixAddr aMc)) mcLvls).constsResolve P.env = true :=
            (constsResolve_mkAppN (hmbodyEq ▸ hcr_body)).1
          have hstMc := find_isSome_of_constsResolve_const hcr_mc
          have hsubMc : ∀ cl ∈ cs_mc, cl ∈ P.calls := fun cl hcl => hsub cl (by rw [hc]; simp [hcl])
          obtain ⟨ciMc, hfindMc, vMc, hldMc', hrepMc⟩ := P.getCI_of_stored hstMc haMc evMc hsubMc
          rw [ldMc] at hldMc'; injection hldMc' with hveq
          cases hrepMc with
          | @ctor _ _ _ _ _ _ _ _ cvMC cnp cnf hvMC hnpMC hnfMC hcntMC hkeyMC =>
            simp only [Value.construct.injEq, List.cons.injEq, and_true] at hveq
            obtain ⟨_, _, rfl, -, rfl, rfl, -, rfl, rfl, -⟩ := hveq
            have hcnf_eq : cnf = rl.nfields :=
              nat_eq_of_field_eq_u56_p hcntMC.2 hrnf56 (Value.field.inj (hnfMC.symm.trans hcnfEq))
            subst hcnf_eq
            obtain ⟨cmMC, cbMC, xsMC, indMC, ctMC, bMC, iMC, jMC,
              hrecCmMC, _, hbMC_rep, hiMC, _, hiMC56, hjMC56, hinfoMC, _, _, _⟩ :=
              P.ctorRecordAt_of_get_ci haMc evMc hsubMc ldMc
            have hnatMC : NativeAt P.E (ixAddr bMC) :=
              P.nativeAt_of_block_is_modeled_zero hbMC_rep evMod
                (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
            rw [hnpMC] at evIz
            obtain ⟨hiz_eq, hm_iz⟩ := Lib.is_zero_field evIz
            subst hm_iz
            have hcnp_pos : 0 < cnp := by
              by_contra h0
              have hc0 : cnp = 0 := by omega
              subst hc0; simp at hiz_eq
            have ext_auxc_mod :=
              evMc.heap_extends.trans evMod.heap_extends
            obtain ⟨hlvlen_f, hmcLvls_lt, hm_lvlen⟩ := klevelList_length_bd
              (hmcLvlsRep.mono ext_auxc_mod) P.hbd (hsub _ (by rw [hc]; simp)) evLvlen
            subst hm_lvlen
            have hmcLvls_len : mcLvls.length = cvMC.levelParams.length := by
              have h1 : (.field (mcLvls'.length : F) : SourceValue F) =
                  .field (cvMC.levelParams.length : F) := by
                rw [← hlvlen_f, hlvlen, hvMC.1]
              exact hmcLvlsEq.length_eq.trans
                (nat_eq_of_field_eq_wide_p (by omega) (by have := hvMC.2.1; omega) (Value.field.inj h1))
            have ext_sp_mod :=
              (evPlvls.heap_extends.trans evAuxC.heap_extends).trans ext_auxc_mod
            obtain ⟨hmlen_f, hmargs_lt, hm_mlen⟩ := kexprList_length_bd
              (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) ext_sp_mod hmargsRep)
              P.hbd (hsub _ (by rw [hc]; simp)) evMlen
            subst hm_mlen
            rw [hnpMC, hnfMC] at opCnpf
            have hmargs_len : margs.length = cnp + rl.nfields := by
              have h1 : (.field (margs.length : F) : SourceValue F) =
                  .field ((cnp + rl.nfields : Nat) : F) := by
                rw [← hmlen_f, hmlen, evalBinOp_add_field_p opCnpf]; push_cast; rfl
              exact nat_eq_of_field_eq_wide_p (by omega) (by omega) (Value.field.inj h1)
            -- `get_ci_iprj [x_cblk, x_cind]` via `ScopedCtx.famAt_of_ctor`!
            obtain ⟨bMC', iMC', jMC', hbMC'rep, hiMC'eq, _, hnameMC'⟩ := hkeyMC
            have hbMC'_eq : bMC' = bMC := addr_det hbMC'rep hbMC_rep
            have hiMC'_eq : iMC' = iMC := Value.field.inj (hiMC'eq.symm.trans hiMC)
            rw [hbMC'_eq, hiMC'_eq] at hnameMC'
            have hfamMC : P.sc.FamAt (ixAddr bMC) (ZMod.val iMC) := by
              obtain ⟨hκMC, -⟩ := P.sc_kappa_eq_of_isSome hstMc
              exact ScopedCtx.famAt_of_ctor (a := ixAddr aMc) (b := ixAddr bMC)
                (i := ZMod.val iMC) (j := ZMod.val jMC') (by rw [hκMC]; exact hfindMc) hnameMC'
            rw [hiMC] at evIprj
            have hsubIprj : ∀ cl ∈ cs_iprj, cl ∈ P.calls := fun cl hcl => hsub cl (by rw [hc]; simp [hcl])
            obtain ⟨ciMCI, hfindMCI_sc, vMCI, hldMCI', hrepMCI⟩ :=
              P.hSE.prefixInv.loads.getIprj x_cblk p_iprj iMC _ m_iprj cs_iprj bMC
                evIprj trivial hfamMC (P.hcoreGoodSub hsubIprj)
                (Bytes.repAddressRef_heapMono₂ addrTy evMod.heap_extends hbMC_rep)
            rw [ldIprj] at hldMCI'; injection hldMCI' with hveqMCI
            have hneMCI : P.sc.κ (Core.iprjAddr (ixAddr bMC) (ZMod.val iMC)) ≠ Core.unresolvedKey :=
              P.hSE.prefixInv.loads.findRes _ _ hfindMCI_sc
            have hκMCI := P.sc_kappa_eq_of_ne hneMCI
            change P.env.find? (P.sc.κ (Core.iprjAddr (ixAddr bMC) (ZMod.val iMC))) = some ciMCI at hfindMCI_sc
            rw [hκMCI] at hfindMCI_sc
            cases hrepMCI with
            | @induct _ _ _ _ _ _ _ _ cvMCI capsMCI hvMCI hcntMCI _ =>
              simp only [Value.construct.injEq, List.cons.injEq, and_true] at hveqMCI
              obtain ⟨_, _, rfl, rfl, rfl, rfl, -, -, -, -⟩ := hveqMCI
              obtain ⟨inpN, iniN, _, hinpF, hiniF, _, hinp56, hini56, _⟩ := hcntMCI
              have hinl_eq : cvMCI.levelParams.length = cvMC.levelParams.length :=
                nat_eq_of_field_eq_u56_p (by have := hvMCI.2.1; omega) (by have := hvMC.2.1; omega)
                  (Value.field.inj (hvMCI.1.symm.trans (hinlEq.trans hvMC.1)))
              have hinp_eq : inpN = cnp :=
                nat_eq_of_field_eq_u56_p hinp56 hcntMC.1
                  (Value.field.inj (hinpF.symm.trans (hinpEq.trans hnpMC)))
              subst inpN
              -- Eq.refl or `NativeCtorWitness` via `not_reserved_ctor_of_nP_pos_or_eqRefl`
              have hmc_or_nat :
                  (Core.keyOf P.t (ixAddr aMc) = Ix.Kernel.eqReflName ∧ rl.nfields = 0 ∧
                    P.env.find? Ix.Kernel.eqName = some Ix.Kernel.eqA ∧
                    P.env.find? Ix.Kernel.eqReflName = some Ix.Kernel.eqReflA) ∨
                  ∃ cidx, Nonempty (NativeCtorWitness P.t P.E P.env (Core.keyOf P.t (ixAddr aMc))
                    (Core.keyOf P.t (Core.iprjAddr (ixAddr bMC) (ZMod.val iMC))) cidx) := by
                obtain ⟨G, R, envT, hshape, hextT⟩ := P.hSE.shape
                rcases not_reserved_ctor_of_nP_pos_or_eqRefl P.htwf hshape P.hPre hextT P.hSE.nodup
                    hrecCmMC hinfoMC hfindMc hcnp_pos with ⟨heqRefl, hnf0⟩ | hnotResMC
                · have hfeq : P.env.find? Ix.Kernel.eqName = some Ix.Kernel.eqA :=
                    find_of_mem_nodup P.hSE.nodup (hextT _ (hshape.pins .eqK Ix.Kernel.eqA List.mem_cons_self))
                  have hfrefl : P.env.find? Ix.Kernel.eqReflName = some Ix.Kernel.eqReflA :=
                    find_of_mem_nodup P.hSE.nodup (hextT _ (hshape.pins .eqK Ix.Kernel.eqReflA
                      (List.mem_cons_of_mem _ List.mem_cons_self)))
                  exact Or.inl ⟨heqRefl, hnf0, hfeq, hfrefl⟩
                · have hi_u64 : (ZMod.val iMC).toUInt64.toNat = ZMod.val iMC := by
                    change (UInt64.ofNat _).toNat = _; rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
                  have hj_u64 : (ZMod.val jMC).toUInt64.toNat = ZMod.val jMC := by
                    change (UInt64.ofNat _).toNat = _; rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
                  exact Or.inr ⟨ZMod.val jMC, ⟨{
                    addr := ixAddr aMc
                    cm := cmMC
                    cp := ⟨(ZMod.val iMC).toUInt64, (ZMod.val jMC).toUInt64, ixAddr bMC⟩
                    cv := cvMC
                    nP := cnp
                    nF := rl.nfields
                    hkey := rfl
                    hfind := hfindMc
                    hnotRes := hnotResMC
                    hrec := hrecCmMC
                    hinfo := hinfoMC
                    hnat := hnatMC
                    hindKey := by simp [hi_u64]
                    hcidx := hj_u64 }⟩⟩
              -- `Seg_bpxmpmmr`: `type_sort_fixed_zeta` + `peel_n_lams_pw_eq`
              have hsort_and_pw :
                  ∃ sortL, StripPisZetaSort (cnp + iniN) 0 (Core.posOf cvMCI.levelParams cvMCI.type) sortL ∧
                    (((∀ φ, (substLevel sortL mcLvls).eval φ > 0) ∧ ∀ bm ∈ mbs, bm.2.pw = .never) ∨
                     ((∀ φ, (substLevel sortL mcLvls).eval φ = 0) ∧ ∀ bm ∈ mbs, bm.2.pw = .ifAllZero [])) ∧
                    Heap.Extends m_iprj m_seg := by
                have hityTm : Tm (Core.keyOf P.t) 0 zeroGhost m_iprj 0
                    (Core.posOf cvMCI.levelParams cvMCI.type) x_ity :=
                  P.rekey_tm (hvMCI.2.2.2 0 zeroGhost)
                have hmcLvlsRep_iprj := hmcLvlsRep.mono (ext_auxc_mod.trans evIprj.heap_extends)
                have ext_h_iprj : Heap.Extends h m_iprj :=
                  (extPlvls.trans evAuxC.heap_extends).trans (ext_auxc_mod.trans evIprj.heap_extends)
                match sgSort with
                | .n1 (m_mnkcwtqr := m_ts) (cs_szebtaqe := cs_ts) (v_blrmrkxq := v_sum)
                    (m_rryjvmuu := m_su) (m_cfaxhnga := m_ze) (m_fzdulokp := m_pw1)
                    (v_plhvtggw := v_tot3)
                    (op_mbkeyhor := opSum) (ev_jzgszguu := evTs)
                    (hm_emyibuyv := hmSu) (hm_buxferkf := hmZe)
                    (op_egzevqni := opTot3) (ev_xtxanqwd := evPw1)
                    (he_glntkitw := hhSeg) (hc_phkkzdyl := hcSeg) .. =>
                  subst hhSeg
                  rw [hinpF, hiniF] at opSum
                  rw [evalBinOp_add_field_p opSum,
                    show (cnp : F) + (iniN : F) = ((cnp + iniN : Nat) : F) by push_cast; ring] at evTs
                  obtain ⟨sortL, hsz, hres⟩ := type_sort_fixed_zeta_tm evTs (Or.inl rfl)
                    (P.hbdSub (fun cl hcl => hsub cl (by rw [hc, hcSeg]; simp [hcl])))
                    _ _ (cnp + iniN) 0 _ mcLvls' rfl (by omega) hityTm hmcLvlsRep_iprj
                  have hpos' : ∀ φ, (substLevel sortL mcLvls).eval φ > 0 := by
                    rcases hres with ⟨_, hpos⟩ | ⟨h12, _⟩
                    · intro φ
                      have hev : (substLevel sortL mcLvls).eval φ = (substLevel sortL mcLvls').eval φ := by
                        rw [KernelLevels.eval_substLevel_eq_subst]
                        exact SubstAux.lvEq_subst (LvEq.refl sortL) hmcLvlsEq φ
                      rw [hev]; exact hpos φ
                    · exact absurd (Value.field.inj h12) (by decide)
                  rw [hnih_f] at opTot3
                  rw [evalBinOp_add_field_p opTot3,
                    show (rl.nfields : F) + ((rargs.length - rl.nfields : Nat) : F) =
                      ((rl.nfields + (rargs.length - rl.nfields) : Nat) : F) by push_cast; ring] at evPw1
                  have extSu : Heap.Extends m_ts m_su := by
                    rw [hmSu, hmZe]; exact (Heap.Extends.snoc _ _).trans (Heap.Extends.snoc _ _)
                  have hrepZe : RepKLevel m_ze .zero (.ptr (.enum KernelLevels.klevelEnum) m_ts.length) := by
                    rw [hmZe]; exact .zero (by simp)
                  have hrepSu : RepKLevel m_su (.succ .zero) (.ptr (.enum KernelLevels.klevelEnum) m_ze.length) := by
                    rw [hmSu]; exact .succ (by simp) (hrepZe.mono (Heap.Extends.snoc _ _))
                  obtain ⟨mbs', _, hmin_strip', _, hmbs'_pw⟩ :=
                    peel_n_lams_pw_eq_tm (rl.nfields + (rargs.length - rl.nfields)) (by omega)
                      (hminorTm.mono (ext_h_iprj.trans (evTs.heap_extends.trans extSu))) hrepSu evPw1
                  have hmbs_eq : mbs = mbs' := congrArg Prod.fst (Option.some.inj (hmin_strip.symm.trans hmin_strip'))
                  subst hmbs_eq
                  exact ⟨sortL, hsz, Or.inl ⟨hpos', fun bm hbm => by
                    simpa [Ix.Kernel.Level.zeronessOf] using hmbs'_pw bm hbm⟩,
                    (evTs.heap_extends.trans extSu).trans evPw1.heap_extends⟩
                | .n2 (m_mnkcwtqr := m_ts) (cs_szebtaqe := cs_ts) (v_blrmrkxq := v_sum)
                    (m_zkyipdyo := m_pw2) (v_pmvwqtye := v_tot3) (m_mkntivxs := m_ze)
                    (op_mbkeyhor := opSum) (ev_jzgszguu := evTs)
                    (op_fyiroxhu := opTot3) (hm_prcfexln := hmZe) (ev_gzibppin := evPw2)
                    (he_wlrbxqvi := hhSeg) (hc_txuxwksa := hcSeg) .. =>
                  subst hhSeg
                  rw [hinpF, hiniF] at opSum
                  rw [evalBinOp_add_field_p opSum,
                    show (cnp : F) + (iniN : F) = ((cnp + iniN : Nat) : F) by push_cast; ring] at evTs
                  obtain ⟨sortL, hsz, hres⟩ := type_sort_fixed_zeta_tm evTs (Or.inr rfl)
                    (P.hbdSub (fun cl hcl => hsub cl (by rw [hc, hcSeg]; simp [hcl])))
                    _ _ (cnp + iniN) 0 _ mcLvls' rfl (by omega) hityTm hmcLvlsRep_iprj
                  have hzero' : ∀ φ, (substLevel sortL mcLvls).eval φ = 0 := by
                    rcases hres with ⟨h21, _⟩ | ⟨_, hzero⟩
                    · exact absurd (Value.field.inj h21) (by decide)
                    · intro φ
                      have hev : (substLevel sortL mcLvls).eval φ = (substLevel sortL mcLvls').eval φ := by
                        rw [KernelLevels.eval_substLevel_eq_subst]
                        exact SubstAux.lvEq_subst (LvEq.refl sortL) hmcLvlsEq φ
                      rw [hev]; exact hzero φ
                  rw [hnih_f] at opTot3
                  rw [evalBinOp_add_field_p opTot3,
                    show (rl.nfields : F) + ((rargs.length - rl.nfields : Nat) : F) =
                      ((rl.nfields + (rargs.length - rl.nfields) : Nat) : F) by push_cast; ring] at evPw2
                  have extZe : Heap.Extends m_ts m_ze := by rw [hmZe]; exact Heap.Extends.snoc _ _
                  have hrepZe : RepKLevel m_ze .zero (.ptr (.enum KernelLevels.klevelEnum) m_ts.length) := by
                    rw [hmZe]; exact .zero (by simp)
                  obtain ⟨mbs', _, hmin_strip', _, hmbs'_pw⟩ :=
                    peel_n_lams_pw_eq_tm (rl.nfields + (rargs.length - rl.nfields)) (by omega)
                      (hminorTm.mono (ext_h_iprj.trans (evTs.heap_extends.trans extZe))) hrepZe evPw2
                  have hmbs_eq : mbs = mbs' := congrArg Prod.fst (Option.some.inj (hmin_strip.symm.trans hmin_strip'))
                  subst hmbs_eq
                  exact ⟨sortL, hsz, Or.inr ⟨hzero', fun bm hbm => by
                    simpa [Ix.Kernel.Level.zeronessOf] using hmbs'_pw bm hbm⟩,
                    (evTs.heap_extends.trans extZe).trans evPw2.heap_extends⟩
              obtain ⟨sortL, hszSort, hsortPw, extSeg⟩ := hsort_and_pw
              -- Load `aux.c_k` via `getCprj` and match `knf = rl.nfields` via `ruleCtor_arity`
              obtain ⟨cvAuxC, knf_c, hfindAuxC⟩ := hauxCtorStored k hk_lt
              have hrl_all : allRules[k]? = some rl := by simpa using hrls_sub 0 rl rfl
              have hrl_ctor : rl.ctor = Core.keyOf P.t (Core.cprjAddr auxBlk 0 k) := hrecCtor k rl hrl_all
              have hrl_ar := P.hSE.prefixInv.store.store.ruleCtor_arity hfindAuxRec
                (List.mem_of_getElem? hrl_all) (by rw [hrl_ctor]; exact hfindAuxC)
              have hknf_eq_rnf : knf_c = rl.nfields := hrl_ar.2.1
              subst hknf_eq_rnf
              have ext_h_seg : Heap.Extends h m_seg :=
                (extPlvls.trans evAuxC.heap_extends).trans ((ext_auxc_mod.trans evIprj.heap_extends).trans extSeg)
              have hfamAux' : P.sc.FamAt (ixAddr bAux) (ZMod.val (0 : F)) := by
                rw [hbAux_eq, ZMod.val_zero]; exact hfamAux
              obtain ⟨hκAuxC, -⟩ := P.sc_kappa_eq_of_isSome (a := Core.cprjAddr auxBlk 0 k)
                (by rw [hfindAuxC]; rfl)
              have hfindAuxC' : P.sc.env.find? (P.sc.κ (Core.cprjAddr (ixAddr bAux) (ZMod.val (0 : F)) (ZMod.val (k : F)))) =
                  some (.ctorInfo cvAuxC nP rl.nfields) := by
                rw [hbAux_eq, ZMod.val_zero, val_natCast_wide_p (by omega), hκAuxC]; exact hfindAuxC
              have hrepAuxC := (P.hSE.prefixInv.loads.getCprj x_aux_blk p_auxc_ci 0 (k : F)
                m_seg m_auxc_ci cs_auxc_ci bAux evAuxC_ci trivial hfamAux'
                (P.hcoreGoodSub (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])))
                (Bytes.repAddressRef_heapMono₂ addrTy ext_h_seg hbAux)).2 cvAuxC nP rl.nfields hfindAuxC'
              obtain ⟨vAuxC, hldAuxC', hciAuxC⟩ := hrepAuxC
              rw [ldAuxC_ci] at hldAuxC'; injection hldAuxC' with hveqAuxC
              cases hciAuxC with
              | ctor hvAuxC _ _ _ _ =>
                simp only [Value.construct.injEq, List.cons.injEq, and_true] at hveqAuxC
                obtain ⟨_, _, -, rfl, -, -, -, -, -, -⟩ := hveqAuxC
                have hktyTm : Tm (Core.keyOf P.t) 0 zeroGhost m_auxc_ci 0
                    (Core.posOf cvAuxC.levelParams cvAuxC.type) x_kty :=
                  P.rekey_tm (hvAuxC.2.2.2 0 zeroGhost)
                obtain ⟨bsP, remP, hstripP, hremPTm, hm_pfor⟩ :=
                  Decl.peel_n_foralls_tm nP (val_natCast_wide_p (by omega)) evPfor hktyTm
                subst hm_pfor
                simp only [Nat.zero_add] at hremPTm
                have ext_sp_auxc :=
                  ext_sp_mod.trans ((evIprj.heap_extends.trans extSeg).trans evAuxC_ci.heap_extends)
                rw [hnpMC] at evDrop
                obtain ⟨-, hfargsRep, hm_drop⟩ := kexprList_drop_spec evDrop
                  (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) ext_sp_auxc hmargsRep)
                rw [val_natCast_wide_p (by omega)] at hfargsRep
                subst hm_drop
                have ext_ih_auxc :=
                  ((show Heap.Extends m_nih m_nil by rw [hmNil]; exact Heap.Extends.snoc _ _).trans
                    (evPeel.heap_extends.trans evSp.heap_extends)).trans ext_sp_auxc
                have ext_h_auxc := ext_h_seg.trans evAuxC_ci.heap_extends
                rw [hnih_f] at evReb
                obtain ⟨bsF, remF, hstripF, hrebWit⟩ := check_unpack_rebuild_args_spec
                  hnP hbnl hanc hrnf56 hnih_lt haAux_eq haAuxRec_eq
                  (margs.drop cnp) 0 (by simp [hmargs_len])
                  (P.hbdSub (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])))
                  (by simpa [Nat.add_assoc] using hfargsRep)
                  (by simpa using hremPTm)
                  (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) ext_ih_auxc hihRep)
                  (Bytes.repAddressRef_heapMono₂ addrTy ext_h_auxc haAux)
                  (Bytes.repAddressRef_heapMono₂ addrTy ext_h_auxc haAuxRec)
                  evReb
                have hdrop_len : (margs.drop cnp).length = rl.nfields := by simp [hmargs_len]
                rw [hdrop_len] at hstripF
                have ext_h_reb : Heap.Extends h m_reb := ext_h_auxc.trans evReb.heap_extends
                rw [evalBinOp_add_field_p opK1,
                  show (k : F) + 1 = ((k + 1 : Nat) : F) by push_cast; ring] at evRec
                obtain ⟨hlen_rest, hrest_wit⟩ := ih rrest (k + 1) (by simp at hk; omega)
                  (fun i rl' hi => by
                    have h1 := hrls_sub (i + 1) rl' hi
                    rwa [show k + (i + 1) = k + 1 + i by omega] at h1)
                  (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) ext_h_reb hmrestRep)
                  (fun m hm => hcr m (List.mem_cons_of_mem _ hm))
                  (hrrRep.mono ext_h_reb)
                  (Bytes.repAddressRef_heapMono₂ addrTy ext_h_reb hbAux)
                  (Bytes.repAddressRef_heapMono₂ addrTy ext_h_reb haAux)
                  (Bytes.repAddressRef_heapMono₂ addrTy ext_h_reb haAuxRec)
                  (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) evRec
                refine ⟨by simp [hlen_rest], fun i hi => ?_⟩
                cases i with
                | zero =>
                  refine ⟨rl, rfl, ⟨{
                    rnf := rl.nfields
                    hrnf := rfl
                    rbs := rbs
                    rargs := rargs
                    hr_strip := hr_strip
                    hrargs_ge := hrargs_ge
                    hrargs_fields := hrargs_fields
                    mbs := mbs
                    mcKey := Core.keyOf P.t (ixAddr aMc)
                    mcLvls := mcLvls
                    margs := margs
                    hmin_strip := hmbodyEq ▸ hmin_strip
                    hbranch := Or.inr ⟨cvMC, cnp,
                      Core.keyOf P.t (Core.iprjAddr (ixAddr bMC) (ZMod.val iMC)),
                      cvMCI, capsMCI, iniN, sortL, cvAuxC, bsP, bsF, remP, remF,
                      hmcKey_ne, hfindMc, hcnp_pos, hmcLvls_len, hmargs_len, hfindMCI_sc,
                      hinl_eq, hmc_or_nat, hszSort, hsortPw, hfindAuxC, hstripP, hstripF,
                      fun l hl => by simpa using hrebWit l (by omega)⟩ }⟩⟩
                | succ i' =>
                  obtain ⟨rl', hrl', hw'⟩ := hrest_wit i' (by simpa using hi)
                  refine ⟨rl', hrl', ?_⟩
                  simpa [Nat.add_assoc, Nat.add_comm 1 i'] using hw'
              | _ => simp [kciEnum] at hveqAuxC
            | _ => simp [kciEnum] at hveqMCI
          | _ => simp [kciEnum] at hveq

/-! ## Section 6: `KernelModeled::check_proj_nested_minor` -/

theorem check_proj_nested_minor_spec (P : ProjsCtx.{u})
    {auxKey auxRecKey : KKey} {auxBlk : _root_.Address}
    {bAux aAux aAuxRec : Bytes.Address}
    {x_mbody x_aux_blk x_aux_addr x_aux_rec_addr x_arules x_sbl_nz x_aset r : SourceValue F}
    {auxRecLps : List LevelParam} {sbl : KLevel} {arules : List (RecRule .anon)}
    {cvAuxRec : ConstantVal .anon}
    {nP bnl anc nF nIhJ fidx : Nat} {mbody : KExpr} {h h' : Heap F} {cs : List (Call F)}
    (hnP : nP < 72057594037927936) (hbnl : bnl < 4294967296)
    (hanc : anc < 72057594037927936) (hnF : nF < 72057594037927936)
    (hnIhJ : nIhJ < 2 ^ 39) (hfidx : fidx < nF)
    (hbAux_eq : ixAddr bAux = auxBlk)
    (haAux_eq : Core.keyOf P.t (ixAddr aAux) = auxKey)
    (haAuxRec_eq : Core.keyOf P.t (ixAddr aAuxRec) = auxRecKey)
    (hfamAux : P.sc.FamAt auxBlk 0)
    (hauxCtorStored : ∀ k < anc, ∃ cv knf,
      P.env.find? (Core.keyOf P.t (Core.cprjAddr auxBlk 0 k)) = some (.ctorInfo cv nP knf))
    (hfindAuxRec : P.env.find? auxRecKey =
      some (.recInfo cvAuxRec (nP + 1 + anc + 1) (nP + 1 + anc) arules))
    (hrecCtor : ∀ j rl, arules[j]? = some rl → rl.ctor = Core.keyOf P.t (Core.cprjAddr auxBlk 0 j))
    (hsbl_nz_spec : x_sbl_nz = .field 1 → ∀ φ, Ix.Kernel.Model.pwBit φ sbl.zeronessOf > 0)
    (hmbodyTm : Tm (Core.keyOf P.t) 0 zeroGhost h (nP + 1 + nF + nIhJ) mbody x_mbody)
    (hrules : RulesRep (Core.keyOf P.t) h auxRecLps 0 x_arules arules)
    (hbAux : Bytes.RepAddressRef addrTy h bAux x_aux_blk)
    (haAux : Bytes.RepAddressRef addrTy h aAux x_aux_addr)
    (haAuxRec : Bytes.RepAddressRef addrTy h aAuxRec x_aux_rec_addr)
    (haset : AddrMapAll addrMapEnum (fun _ k _ =>
      AdvChecked P.calls P.bAddr P.t P.lim P.csFam P.advAs k) h x_aset)
    (hsub : ∀ cl ∈ cs, cl ∈ P.calls)
    (ev : ObsFn Obs.W "KernelModeled::check_proj_nested_minor"
      [x_mbody, x_aux_blk, x_aux_addr, x_aux_rec_addr, x_arules, x_sbl_nz,
       .field (nP : F), .field (bnl : F), .field (anc : F), .field (nF : F),
       .field (nIhJ : F), .field (fidx : F), x_aset] h r h' cs) :
    ProjMinorWitness P.t P.E P.env auxKey auxRecKey auxRecLps arules
      (fun k => Core.keyOf P.t (Core.cprjAddr auxBlk 0 k)) sbl.zeronessOf
      nP bnl anc nF nIhJ fidx mbody := by
  have htgt_eq : ∀ {v1 v2 v3 : SourceValue F},
      evalBinOp .add (.field (nIhJ : F)) (.field (nF : F)) = .ok v1 →
      evalBinOp .sub v1 (.field 1) = .ok v2 →
      evalBinOp .sub v2 (.field (fidx : F)) = .ok v3 →
      v3 = .field ((nIhJ + nF - 1 - fidx : Nat) : F) := by
    intro v1 v2 v3 op1 op2 op3
    rw [evalBinOp_add_field_p op1] at op2
    rw [evalBinOp_sub_field_p op2] at op3
    rw [evalBinOp_sub_field_p op3]
    congr 1
    have h1 : ((nIhJ + nF - 1 - fidx : Nat) : F) + 1 + (fidx : F) = (nIhJ : F) + (nF : F) := by
      have hnat : nIhJ + nF - 1 - fidx + 1 + fidx = nIhJ + nF := by omega
      have h2 := congrArg (Nat.cast (R := F)) hnat
      simpa [Nat.cast_add] using h2
    linear_combination -h1
  match Obs.«KernelModeled::check_proj_nested_minor».obs ev with
  | .BVar (op_emsauwnp := op1) (op_sbvbulnj := op2) (op_xyoszxhe := op3)
      (ld_bolbylmd := ldBv) (heq_lkkiojmp := hbvEq) .. =>
    obtain ⟨bv_f, rfl, -, -, rfl⟩ := bvar_of_load_d0 hmbodyTm ldBv
    rw [htgt_eq op1 op2 op3] at hbvEq
    have hbv_nat : ZMod.val bv_f = nIhJ + nF - 1 - fidx := by
      have h1 := congrArg ZMod.val (Value.field.inj hbvEq)
      rwa [val_natCast_wide_p (by omega)] at h1
    rw [hbv_nat]
    exact .bvar rfl
  | .other (v_lipfahcz := v_tgt) (m_aqdywcwd := m_sp1) (x_uh := x_uh) (x_uargs := x_uargs)
      (v_braoivot := v_plvls) (m_wzmrgkdh := m_plvls) (x_u_addr := x_u_addr) (x_u_lvls := x_u_lvls)
      (m_mtnkzfhp := m_memU) (m_diawdzto := m_uleq) (v_dwrmhako := v_ulen) (m_poanccks := m_ulen)
      (m_izcyqpqx := m_ult) (v_lfqbucha := v_utake) (v_kjshwkqb := v_ubv) (m_rnylylds := m_utake)
      (m_tlkauhph := m_ubv) (m_xwsmdvmb := m_upeq) (v_csktsfda := v_ustart) (v_eedlsvrd := v_ulast)
      (m_bogisjgj := m_ulast) (v_hczlgagy := v_ulen1) (x_ubv := x_ubv)
      (m_atbimbtr := m_ciU) (p_hjtozfeg := p_ciU) (cs_bkxacyxh := cs_ciU)
      (x_unl := x_unl) (x_uval := x_uval) (m_stjemycb := m_succ) (m_hdmdtpnd := m_zero)
      (v_bqjlmbjm := v_ubody) (m_cngotxbn := m_upeel) (m_sweucrww := m_sp2)
      (x_uah := x_uah) (x_ua_args := x_ua_args) (x_ua_addr := x_ua_addr) (x_ua_lvls := x_ua_lvls)
      (m_aujpfwum := m_memUA) (m_sfdbqngc := m_ualeq) (v_ymzeuxny := v_ualen)
      (v_wjdiijvc := v_np2) (m_napildtc := m_ualen) (m_rmnrrdhm := m_uapeq)
      (v_bsmigpxm := v_uatake) (v_uggnusti := v_uabv) (m_tylehxks := m_uatake) (m_qevjsqnu := m_uabv)
      (m_lajuufdx := m_ualast) (p_oyimlwwu := p_ualast) (v_ninfjcqh := v_np1a) (x_abv := x_abv)
      (m_csfcfegj := m_ciUA) (p_dchvcwzg := p_ciUA) (cs_zvrxhybw := cs_ciUA)
      (x_uanl := x_uanl) (x_uaval := x_uaval) (v_ilqttfgo := v_uabody) (m_oeqfbefa := m_uapeel)
      (m_jvfjvwec := m_sp3) (x_uarh := x_uarh) (x_uar_args := x_uar_args)
      (x_uar_addr := x_uar_addr) (x_uar_lvls := x_uar_lvls) (m_wtdkiufa := m_araeq)
      (v_lelygemj := v_arlvlen) (v_qazgyfef := v_bnl1) (m_wbxrjzlw := m_arlvlen)
      (m_wxlllmos := m_arnz) (v_ikgbzoay := v_arlv0) (m_fnvmbpef := m_arlv0)
      (m_ptjsklfe := m_arleq) (v_pzmopiic := v_arlvdrop) (m_yynvdody := m_arlvdrop)
      (v_raqpbdpd := v_ararglen) (v_kwehjysj := v_np1anc) (m_tigphkum := m_ararglen)
      (m_fuwjrfry := m_arpeq) (v_wmvnjwxf := v_artake) (v_zvpavblf := v_arbv)
      (m_kaynadjl := m_artake) (m_gmypednm := m_arbv) (v_pqaluwud := v_minors)
      (m_tdmluvhy := m_ardrop) (v_radyybwm := v_np1b) (cs_efedkgym := cs_min)
      (op_emsauwnp := op1) (op_sbvbulnj := op2) (op_xyoszxhe := op3)
      (heq_gsqpsvst := hsbl1) (ev_pfylwyun := evSp1) (ev_ohmoyxsf := evPlvls)
      (ld_ohkeraqx := ldUh) (ev_onkqlpak := evMemU) (heq_yukqpsnp := hmemU1)
      (ev_skloqfty := evUleq) (heq_rguuiwwi := huleq1) (ev_kxxhwkzk := evUlen)
      (ev_uijuldse := evUlt) (heq_htfqrepy := hult1) (ev_eqeuwyve := evUtake)
      (op_asuhlnms := opU1) (op_mmrlwiox := opU2) (op_ahfqxdrk := opU3)
      (ev_isbblmud := evUbv) (ev_ydqeteoj := evUpeq) (heq_mjnzxrpw := hupeq1)
      (op_gvkrewih := opUlen1) (ev_rgxynxjb := evUlast) (ld_uurjntyd := ldUlast)
      (heq_vxhyqthw := hubvEq) (ev_kkcqwiyf := evCiU) (ld_atqqapac := ldCiU)
      (heq_tnkwtlwk := hunlEq) (hm_qagjyfji := hmSucc) (hm_djgcdhxv := hmZero)
      (ev_kzkuumpk := evUpeel) (ev_hwfpxpok := evSp2) (ld_ayfkwwbf := ldUah)
      (ev_famhcrpg := evMemUA) (heq_zfnwreen := hmemUA1) (ev_oxaikude := evUAleq)
      (heq_cridoaeo := hualeq1) (ev_qbomjolu := evUAlen) (op_kczyvpvv := opNp2)
      (heq_zrhhutjf := hualenEq) (ev_lmfsaaub := evUAtake) (ev_zudcqeio := evUAbv)
      (ev_umevdaug := evUApeq) (heq_tmznaffo := huapeq1) (op_pdewwggl := opNp1a)
      (ev_xaslgjul := evUAlast) (ld_nnxeuymp := ldUAlast) (heq_ecxjxyek := habv0)
      (ev_kgprnbqv := evCiUA) (ld_olflaeyf := ldCiUA) (heq_cnnaxsgr := huanlEq)
      (ev_qukpudxe := evUApeel) (ev_jkghhvin := evSp3) (ld_fwuexrpg := ldUarh)
      (ev_fvpdtzkr := evArAeq) (heq_cyrzmcrr := haraeq1) (ev_whplplyz := evArLvlen)
      (op_pzgnpjce := opBnl1) (heq_uoegfufx := harlvlenEq) (ev_zutybnxz := evArLv0)
      (ev_munhihux := evArNz) (heq_yfecrhzs := harnz1) (ev_pxoarcsz := evArLvdrop)
      (ev_eywbtcut := evArLeq) (heq_amaznabj := harleq1) (ev_dnowhdrj := evArArglen)
      (op_uitjfoef := opNp1c) (op_mggzymnr := opAnc) (heq_ezaemidz := hararglenEq)
      (ev_rrslinan := evArTake) (ev_uwfqotgt := evArBv) (ev_biprwcam := evArPeq)
      (heq_udnjedwi := harpeq1) (op_btwdrtpa := opNp1b) (ev_ojvkcljr := evArDrop)
      (ev_obuzlacq := evMin) (hc_kjrxaxhl := hc) .. =>
    subst hmemU1 huleq1 hult1 hupeq1 hmemUA1 hualeq1 huapeq1 haraeq1 harnz1 harleq1 harpeq1
    have hsbl_nz := hsbl_nz_spec hsbl1
    have htgt := htgt_eq op1 op2 op3
    obtain ⟨H_u, uargs, hmbodyEq, hHuTm, huargsRep⟩ := collect_spine_tuple_tm evSp1 hmbodyTm
    have hplvlsRep := (show ((List.range bnl).map fun k => Level.param (0 + k)) = (List.range bnl).map Level.param by simp) ▸ build_param_lvls_range_start (start := 0) (n := bnl) (by omega) evPlvls
    obtain ⟨aU, uLvls, rfl, haU, uLvls', huLvlsRep, huLvlsEq⟩ :=
      (hHuTm.mono evPlvls.heap_extends).const_of_load ldUh
    have ext_h_plvls : Heap.Extends h m_plvls := evSp1.heap_extends.trans evPlvls.heap_extends
    have hAdvU := P.advChecked_of_aset_member
      (AddrMapAll.mono (fun _ _ _ _ _ x => x) ext_h_plvls haset) haU evMemU
    obtain ⟨huLvls_eq, hm_uleq⟩ := Decl.level_list_struct_eq_one
      (huLvlsRep.mono evMemU.heap_extends) (hplvlsRep.mono evMemU.heap_extends) evUleq
    subst hm_uleq
    have huLvls_rel : LvEqList uLvls ((List.range bnl).map Level.param) := by
      rw [huLvls_eq] at huLvlsEq; simpa using huLvlsEq
    have ext_sp1_memU : Heap.Extends m_sp1 m_uleq := evPlvls.heap_extends.trans evMemU.heap_extends
    have huargsRep_m := RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) ext_sp1_memU huargsRep
    obtain ⟨hulen_f, huargs_lt, hm_ulen⟩ := kexprList_length_bd huargsRep_m P.hbd
      (hsub _ (by rw [hc]; simp)) evUlen
    subst hm_ulen
    rw [hulen_f] at evUlt opUlen1 evUpeel evUAbv
    obtain ⟨_, _, hult_iff, _, hm_ult⟩ := Lib.less_than_fields_field evUlt
    have huargs_gt_f := hult_iff.mp rfl
    subst hm_ult
    have huargs_gt : nP < uargs.length := by
      rw [val_natCast_wide_p (by omega), val_natCast_wide_p (by omega)] at huargs_gt_f
      exact huargs_gt_f
    obtain ⟨-, hutakeRep⟩ := kexprList_take_spec (fun _ _ _ _ ext r => r.mono ext) evUtake huargsRep_m
    rw [val_natCast_wide_p (by omega)] at hutakeRep
    have hustart_eq : v_ustart = .field ((nP + 1 + nF + nIhJ : Nat) : F) := by
      rw [evalBinOp_add_field_p opU1] at opU2
      rw [evalBinOp_add_field_p opU2] at opU3
      rw [evalBinOp_add_field_p opU3]; push_cast; rfl
    rw [hustart_eq] at evUbv
    have hubvRep := bvars_desc_tm_nat (κ := Core.keyOf P.t) (Γ := zeroGhost)
      (k := nP + 1 + nF + nIhJ) (start := nP + 1 + nF + nIhJ) (cnt := nP)
      (by omega) (by omega) (by omega) evUbv
    have huargs_pref := spec_params_ptr_eq_tm_one
      (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) evUbv.heap_extends hutakeRep) hubvRep evUpeq
    have ext_memU_upeq :=
      (evUtake.heap_extends.trans evUbv.heap_extends).trans evUpeq.heap_extends
    have hulen1_eq : v_ulen1 = .field ((uargs.length - 1 : Nat) : F) := by
      rw [evalBinOp_sub_field_p opUlen1]
      congr 1
      have h1 : ((uargs.length - 1 : Nat) : F) + 1 = (uargs.length : F) := by
        have hnat : uargs.length - 1 + 1 = uargs.length := by omega
        have h2 := congrArg (Nat.cast (R := F)) hnat
        simpa [Nat.cast_add] using h2
      linear_combination -h1
    rw [hulen1_eq] at evUlast
    obtain ⟨⟨ulastE, hulast_get, hulastTm⟩, hm_ulast⟩ := kexprList_lookup_spec evUlast
      (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) ext_memU_upeq huargsRep_m)
    rw [val_natCast_wide_p (by omega)] at hulast_get
    subst hm_ulast
    obtain ⟨ubv_f, rfl, -, -, rfl⟩ := bvar_of_load_d0 hulastTm ldUlast
    rw [htgt] at hubvEq
    have hubv_nat : ZMod.val ubv_f = nIhJ + nF - 1 - fidx := by
      have h1 := congrArg ZMod.val (Value.field.inj hubvEq)
      rwa [val_natCast_wide_p (by omega)] at h1
    rw [hubv_nat] at hulast_get
    -- `get_ci [x_u_addr]` → `Defn`
    have ext_plvls_upeq := evMemU.heap_extends.trans ext_memU_upeq
    obtain ⟨cvU, uval, uHint, hU_nonAux, hfindU, hunl_f, hU_lvls_lt, hU_perm0, _, huvalTmC, _, _⟩ :=
      P.getCI_defn_of_advChecked hAdvU
        (Bytes.repAddressRef_heapMono₂ addrTy ext_plvls_upeq haU) evCiU
        (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) ldCiU
    have hU_lvls : cvU.levelParams.length = bnl :=
      nat_eq_of_field_eq_u56_p (by omega) (by omega) (Value.field.inj (hunl_f.symm.trans hunlEq))
    have hU_perm : cvU.levelParams.Perm (List.range bnl) := by rw [← hU_lvls]; exact hU_perm0
    have extSucc : Heap.Extends m_ciU m_succ := by
      rw [hmSucc, hmZero]; exact (Heap.Extends.snoc _ _).trans (Heap.Extends.snoc _ _)
    have hrepZero : RepKLevel m_zero .zero (.ptr (.enum KernelLevels.klevelEnum) m_ciU.length) := by
      rw [hmZero]; exact .zero (by simp)
    have hrepSucc : RepKLevel m_succ (.succ .zero) (.ptr (.enum KernelLevels.klevelEnum) m_zero.length) := by
      rw [hmSucc]; exact .succ (by simp) (hrepZero.mono (Heap.Extends.snoc _ _))
    obtain ⟨ubs, ubody, hu_strip, hubodyTm, hu_pw0⟩ :=
      peel_n_lams_pw_eq_tm uargs.length (by omega) ((huvalTmC 0 zeroGhost).mono extSucc) hrepSucc evUpeel
    simp only [Nat.zero_add] at hubodyTm
    obtain ⟨H_ua, uaArgs, hubodyEq, hHuaTm, huaArgsRep⟩ := collect_spine_tuple_tm evSp2 hubodyTm
    obtain ⟨aUA, uaLvls, rfl, haUA, uaLvls', huaLvlsRep, huaLvlsEq⟩ := hHuaTm.const_of_load ldUah
    have ext_h_sp2 : Heap.Extends h m_sp2 :=
      (ext_h_plvls.trans (ext_plvls_upeq.trans (evCiU.heap_extends.trans extSucc))).trans
        (evUpeel.heap_extends.trans evSp2.heap_extends)
    have hAdvUA := P.advChecked_of_aset_member
      (AddrMapAll.mono (fun _ _ _ _ _ x => x) ext_h_sp2 haset) haUA evMemUA
    have ext_plvls_memUA : Heap.Extends m_plvls m_memUA :=
      (ext_plvls_upeq.trans (evCiU.heap_extends.trans extSucc)).trans
        ((evUpeel.heap_extends.trans evSp2.heap_extends).trans evMemUA.heap_extends)
    obtain ⟨huaLvls_eq, hm_ualeq⟩ := Decl.level_list_struct_eq_one
      (huaLvlsRep.mono evMemUA.heap_extends) (hplvlsRep.mono ext_plvls_memUA) evUAleq
    subst hm_ualeq
    have huaLvls_rel : LvEqList uaLvls ((List.range bnl).map Level.param) := by
      rw [huaLvls_eq] at huaLvlsEq; simpa using huaLvlsEq
    have huaArgsRep_m := RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) evMemUA.heap_extends huaArgsRep
    obtain ⟨hualen_f, huaArgs_lt, hm_ualen⟩ := kexprList_length_bd huaArgsRep_m P.hbd
      (hsub _ (by rw [hc]; simp)) evUAlen
    subst hm_ualen
    rw [evalBinOp_add_field_p opNp2] at hualenEq
    have hua_len : uaArgs.length = nP + 2 := by
      have h1 : (.field (uaArgs.length : F) : SourceValue F) = .field ((nP + 2 : Nat) : F) := by
        rw [← hualen_f, hualenEq]; push_cast; rfl
      exact nat_eq_of_field_eq_wide_p (by omega) (by omega) (Value.field.inj h1)
    obtain ⟨-, huatakeRep⟩ := kexprList_take_spec (fun _ _ _ _ ext r => r.mono ext) evUAtake huaArgsRep_m
    rw [val_natCast_wide_p (by omega)] at huatakeRep
    have huabvRep := bvars_desc_tm_nat (κ := Core.keyOf P.t) (Γ := zeroGhost)
      (k := uargs.length) (start := uargs.length) (cnt := nP)
      (by omega) (le_refl _) (by omega) evUAbv
    have hua_pref := spec_params_ptr_eq_tm_one
      (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) evUAbv.heap_extends huatakeRep) huabvRep evUApeq
    have ext_memUA_uapeq :=
      (evUAtake.heap_extends.trans evUAbv.heap_extends).trans evUApeq.heap_extends
    have hnp1a_eq : v_np1a = .field ((nP + 1 : Nat) : F) := by
      rw [evalBinOp_add_field_p opNp1a]; push_cast; rfl
    rw [hnp1a_eq] at evUAlast
    obtain ⟨⟨ualastE, hualast_get, hualastTm⟩, hm_ualast⟩ := kexprList_lookup_spec evUAlast
      (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) ext_memUA_uapeq huaArgsRep_m)
    rw [val_natCast_wide_p (by omega)] at hualast_get
    subst hm_ualast
    obtain ⟨abv_f, rfl, -, -, rfl⟩ := bvar_of_load_d0 hualastTm ldUAlast
    have habv_nat : ZMod.val abv_f = 0 := by rw [Value.field.inj habv0]; exact ZMod.val_zero
    rw [habv_nat] at hualast_get
    -- `get_ci [x_ua_addr]` → `Defn`
    obtain ⟨cvUA, uaval, uaHint, hUA_nonAux, hfindUA, huanl_f, hUA_lvls_lt, hUA_perm0, _, huavalTmC, _, huavalCr⟩ :=
      P.getCI_defn_of_advChecked hAdvUA
        (Bytes.repAddressRef_heapMono₂ addrTy (evMemUA.heap_extends.trans ext_memUA_uapeq) haUA) evCiUA
        (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) ldCiUA
    have hUA_lvls : cvUA.levelParams.length = bnl :=
      nat_eq_of_field_eq_u56_p (by omega) (by omega) (Value.field.inj (huanl_f.symm.trans huanlEq))
    have hUA_perm : cvUA.levelParams.Perm (List.range bnl) := by rw [← hUA_lvls]; exact hUA_perm0
    have ext_succ_ciUA : Heap.Extends m_succ m_ciUA :=
      ((evUpeel.heap_extends.trans evSp2.heap_extends).trans
        (evMemUA.heap_extends.trans ext_memUA_uapeq)).trans evCiUA.heap_extends
    obtain ⟨uabs, uabody, hua_strip, huabodyTm, hua_pw0⟩ :=
      peel_n_lams_pw_eq_tm nP (by omega) (huavalTmC 0 zeroGhost) (hrepSucc.mono ext_succ_ciUA) evUApeel
    simp only [Nat.zero_add] at huabodyTm
    obtain ⟨H_uar, uarArgs, huabodyEq, hHuarTm, huarArgsRep⟩ := collect_spine_tuple_tm evSp3 huabodyTm
    obtain ⟨aUar, uarLvls, rfl, haUar, uarLvls', huarLvlsRep, huarLvlsEq⟩ := hHuarTm.const_of_load ldUarh
    have ext_h_sp3 : Heap.Extends h m_sp3 :=
      (ext_h_sp2.trans (evMemUA.heap_extends.trans (ext_memUA_uapeq.trans evCiUA.heap_extends))).trans
        (evUApeel.heap_extends.trans evSp3.heap_extends)
    obtain ⟨hArAeq_f, hm_araeq⟩ := Lib.address_eq_spec evArAeq haUar
      (Bytes.repAddressRef_heapMono₂ addrTy ext_h_sp3 haAuxRec)
    subst hm_araeq
    have haUar_eq : aUar = aAuxRec := by by_contra hne; simp [hne] at hArAeq_f
    subst haUar_eq
    rw [haAuxRec_eq] at huabodyEq
    obtain ⟨harlvlen_f, huarLvls_lt, hm_arlvlen⟩ := klevelList_length_bd huarLvlsRep P.hbd
      (hsub _ (by rw [hc]; simp)) evArLvlen
    subst hm_arlvlen
    rw [evalBinOp_add_field_p opBnl1] at harlvlenEq
    have huar_lvls_len : uarLvls.length = bnl + 1 := by
      have h1 : (.field (uarLvls'.length : F) : SourceValue F) = .field ((bnl + 1 : Nat) : F) := by
        rw [← harlvlen_f, harlvlenEq]; push_cast; rfl
      exact huarLvlsEq.length_eq.trans
        (nat_eq_of_field_eq_wide_p (by omega) (by omega) (Value.field.inj h1))
    obtain ⟨⟨lv0', hlv0'_get, hlv0'_rep⟩, hm_arlv0⟩ := klevelList_lookup_spec evArLv0 huarLvlsRep
    rw [ZMod.val_zero] at hlv0'_get
    subst hm_arlv0
    have hlv0'_pos := eval_pos_of_level_is_not_zero hlv0'_rep evArNz
    have huar_elim_nz : ∀ φ, (uarLvls.getD 0 .zero).eval φ > 0 := by
      intro φ
      rw [lvEqList_getD_zero huarLvlsEq φ]
      have hget0 : uarLvls'.getD 0 .zero = lv0' := by simp [List.getD, hlv0'_get]
      rw [hget0]; exact hlv0'_pos φ
    obtain ⟨-, hlvdropRep, hm_arlvdrop⟩ :=
      klevelList_drop_spec evArLvdrop (huarLvlsRep.mono evArNz.heap_extends)
    rw [ZMod.val_one] at hlvdropRep
    subst hm_arlvdrop
    have ext_plvls_arnz :=
      (ext_plvls_memUA.trans (ext_memUA_uapeq.trans evCiUA.heap_extends)).trans
        ((evUApeel.heap_extends.trans evSp3.heap_extends).trans evArNz.heap_extends)
    obtain ⟨hlvdrop_eq, hm_arleq⟩ := Decl.level_list_struct_eq_one hlvdropRep
      (hplvlsRep.mono ext_plvls_arnz) evArLeq
    subst hm_arleq
    have huar_lvls_drop : LvEqList (uarLvls.drop 1) ((List.range bnl).map Level.param) := by
      have h1 := lvEqList_drop huarLvlsEq 1
      rw [hlvdrop_eq] at h1; simpa using h1
    have huarArgsRep_n := RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) evArNz.heap_extends huarArgsRep
    obtain ⟨hararglen_f, huarArgs_lt, hm_ararglen⟩ := kexprList_length_bd huarArgsRep_n P.hbd
      (hsub _ (by rw [hc]; simp)) evArArglen
    subst hm_ararglen
    rw [evalBinOp_add_field_p opNp1c] at opAnc
    rw [evalBinOp_add_field_p opAnc] at hararglenEq
    have huar_len : uarArgs.length = nP + 1 + anc := by
      have h1 : (.field (uarArgs.length : F) : SourceValue F) = .field ((nP + 1 + anc : Nat) : F) := by
        rw [← hararglen_f, hararglenEq]; push_cast; rfl
      exact nat_eq_of_field_eq_wide_p (by omega) (by omega) (Value.field.inj h1)
    obtain ⟨-, hartakeRep⟩ := kexprList_take_spec (fun _ _ _ _ ext r => r.mono ext) evArTake huarArgsRep_n
    rw [val_natCast_wide_p (by omega)] at hartakeRep
    have harbvRep := bvars_desc_tm_nat (κ := Core.keyOf P.t) (Γ := zeroGhost)
      (k := nP) (start := nP) (cnt := nP) (le_refl _) (le_refl _) (by omega) evArBv
    have huar_pref := spec_params_ptr_eq_tm_one
      (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) evArBv.heap_extends hartakeRep) harbvRep evArPeq
    have ext_arnz_arpeq :=
      (evArTake.heap_extends.trans evArBv.heap_extends).trans evArPeq.heap_extends
    have hnp1b_eq : v_np1b = .field ((nP + 1 : Nat) : F) := by
      rw [evalBinOp_add_field_p opNp1b]; push_cast; rfl
    rw [hnp1b_eq] at evArDrop
    obtain ⟨-, hminorsRep, hm_ardrop⟩ := kexprList_drop_spec evArDrop
      (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) ext_arnz_arpeq huarArgsRep_n)
    rw [val_natCast_wide_p (by omega)] at hminorsRep
    subst hm_ardrop
    have hcr_minors : ∀ m ∈ uarArgs.drop (nP + 1), m.constsResolve P.env = true := by
      have hcr1 : (Core.posOf cvUA.levelParams uaval).constsResolve P.env = true := by
        rw [Decl.constsResolve_posOf]; exact huavalCr
      have hcr2 := constsResolve_stripLams hcr1 hua_strip
      have hcr3 := (constsResolve_mkAppN (huabodyEq ▸ hcr2)).2
      exact fun m hm => hcr3 m (List.mem_of_mem_drop hm)
    have ext_h_arpeq :=
      ext_h_sp3.trans (evArNz.heap_extends.trans ext_arnz_arpeq)
    obtain ⟨_, hminors_wit⟩ := check_unpack_minors_spec P hnP hbnl hanc hbAux_eq haAux_eq haAuxRec_eq
      hfamAux hauxCtorStored hfindAuxRec hrecCtor
      (uarArgs.drop (nP + 1)) arules 0 (by simp [huar_len]) (fun i rl hi => by simpa using hi)
      hminorsRep hcr_minors (hrules.mono ext_h_arpeq)
      (Bytes.repAddressRef_heapMono₂ addrTy ext_h_arpeq hbAux)
      (Bytes.repAddressRef_heapMono₂ addrTy ext_h_arpeq haAux)
      (Bytes.repAddressRef_heapMono₂ addrTy ext_h_arpeq haAuxRec)
      (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) evMin
    exact .unpack hsbl_nz (Core.keyOf P.t (ixAddr aU)) cvU uval uHint uLvls uargs
      (Core.keyOf P.t (ixAddr aUA)) cvUA uaval uaHint ubs uaLvls uaArgs uabs uarLvls uarArgs
      hmbodyEq hU_nonAux hfindU hU_lvls hU_perm huLvls_rel huargs_gt huargs_pref hulast_get
      (hubodyEq ▸ hu_strip) (fun bm hbm => by simpa [Ix.Kernel.Level.zeronessOf] using hu_pw0 bm hbm)
      hUA_nonAux hfindUA hUA_lvls hUA_perm huaLvls_rel hua_len hua_pref hualast_get
      (huabodyEq ▸ hua_strip) (fun bm hbm => by simpa [Ix.Kernel.Level.zeronessOf] using hua_pw0 bm hbm)
      huar_lvls_len huar_elim_nz huar_lvls_drop huar_len huar_pref
      (fun k hk => by
        obtain ⟨rl, hrl, hw⟩ := hminors_wit k (by simp [huar_len, hk])
        exact ⟨rl, hrl, by simpa using hw⟩)

/-! ## Section 7: `KernelModeled::check_proj_pure_sort_poly` -/

theorem check_proj_pure_sort_poly_spec (P : ProjsCtx.{u})
    {auxBlk : _root_.Address} {bAux : Bytes.Address}
    {x_aux_blk x_cty_m x_raw_dom x_sbl_nz r : SourceValue F}
    {sbl : KLevel} {ctyMPos rawDom : KExpr} {nP nF fidx jIdx : Nat}
    {h h' : Heap F} {cs : List (Call F)}
    (hnP : nP < 72057594037927936) (hfidx : fidx < 72057594037927936)
    (hjIdx : jIdx < 72057594037927936)
    (hbAux_eq : ixAddr bAux = auxBlk)
    (hfamAux : P.sc.FamAt auxBlk 0)
    (hauxCtorJ : ∃ cv, P.env.find? (Core.keyOf P.t (Core.cprjAddr auxBlk 0 jIdx)) = some (.ctorInfo cv nP nF))
    (hsbl_nz_spec : x_sbl_nz = .field 1 → ∀ φ, Ix.Kernel.Model.pwBit φ sbl.zeronessOf > 0)
    (hbAux : Bytes.RepAddressRef addrTy h bAux x_aux_blk)
    (hcty : Tm (Core.keyOf P.t) 0 zeroGhost h 0 ctyMPos x_cty_m)
    (hraw : Tm (Core.keyOf P.t) 0 zeroGhost h (nP + fidx) rawDom x_raw_dom)
    (hsub : ∀ cl ∈ cs, cl ∈ P.calls)
    (ev : ObsFn Obs.W "KernelModeled::check_proj_pure_sort_poly"
      [x_aux_blk, .field (jIdx : F), x_cty_m, x_raw_dom, x_sbl_nz, .field (nP : F), .field (fidx : F)]
      h r h' cs) :
    (∀ φ, Ix.Kernel.Model.pwBit φ sbl.zeronessOf > 0) ∨
    ((∀ i < fidx, rawDom.hasLooseBVar i = false) ∧
      ∃ (cvAuxC : ConstantVal .anon) (kbs : List (KExpr × Ix.Kernel.BinderMeta)) (krest : KExpr)
        (cbs : List (KExpr × Ix.Kernel.BinderMeta)) (crest : KExpr)
        (kfbs : List (KExpr × Ix.Kernel.BinderMeta)) (kfdom kfrest : KExpr)
        (kfbm : Ix.Kernel.BinderMeta),
      P.env.find? (Core.keyOf P.t (Core.cprjAddr auxBlk 0 jIdx)) = some (.ctorInfo cvAuxC nP nF) ∧
      (Core.posOf cvAuxC.levelParams cvAuxC.type).stripPis nP = some (kbs, krest) ∧
      ctyMPos.stripPis nP = some (cbs, crest) ∧
      List.Forall₂ ExprSemEq (kbs.map Prod.fst) (cbs.map Prod.fst) ∧
      krest.stripPis fidx = some (kfbs, .forallE kfdom kfrest kfbm) ∧
      ExprSemEq kfdom rawDom) := by
  match Obs.«KernelModeled::check_proj_pure_sort_poly».obs ev with
  | .n1 (hv_dhvipoqr := hv) .. => exact Or.inl (hsbl_nz_spec hv)
  | .other (m_fvxirhgm := m_bvr) (cs_vmeeoynk := cs_bvr) (m_iepmyiby := m_cprj)
      (p_kdldqddj := p_cprj) (cs_xeulgpzn := cs_cprj) (x_kty_j := x_kty_j)
      (m_wazbnxcy := m_tele) (m_nubksjxp := m_pfor) (p_rhpslgjq := p_pfor)
      (x_kfdom_j := x_kfdom_j)
      (ev_uxhrptga := evBvr) (heq_huqrnewm := hbvr0)
      (ev_plaaaxzd := evCprj) (ld_ghzzxirj := ldCprj)
      (ev_fbeuxmrt := evTele) (ev_pyaharxd := evPfor) (ld_wmhveqyc := ldForall)
      (ev_lubnqwpv := evEq) (heq_vcugsbsx := heq1) (hc_kjrxaxhl := hc) .. =>
    subst hbvr0 heq1
    have hnoBvr := noLooseBVar_of_hasBVarInRange_zero hfidx
      (P.hbdSub (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))) hraw evBvr
    obtain ⟨cvAuxC, hfindAuxC⟩ := hauxCtorJ
    have hfam' : P.sc.FamAt (ixAddr bAux) (ZMod.val (0 : F)) := by
      rw [hbAux_eq, ZMod.val_zero]; exact hfamAux
    obtain ⟨hκC, -⟩ := P.sc_kappa_eq_of_isSome (a := Core.cprjAddr auxBlk 0 jIdx)
      (by rw [hfindAuxC]; rfl)
    have hfindC' : P.sc.env.find? (P.sc.κ (Core.cprjAddr (ixAddr bAux) (ZMod.val (0 : F)) (ZMod.val (jIdx : F)))) =
        some (.ctorInfo cvAuxC nP nF) := by
      rw [hbAux_eq, ZMod.val_zero, val_natCast_wide_p (by omega), hκC]; exact hfindAuxC
    have hrepC := (P.hSE.prefixInv.loads.getCprj x_aux_blk p_cprj 0 (jIdx : F)
      m_bvr m_cprj cs_cprj bAux evCprj trivial hfam'
      (P.hcoreGoodSub (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])))
      (Bytes.repAddressRef_heapMono₂ addrTy evBvr.heap_extends hbAux)).2 cvAuxC nP nF hfindC'
    obtain ⟨vC, hldC', hciC⟩ := hrepC
    rw [ldCprj] at hldC'; injection hldC' with hveq
    cases hciC with
    | ctor hvC _ _ _ _ =>
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hveq
      obtain ⟨_, _, -, rfl, -, -, -, -, -, -⟩ := hveq
      have hktyTm : Tm (Core.keyOf P.t) 0 zeroGhost m_cprj 0
          (Core.posOf cvAuxC.levelParams cvAuxC.type) x_kty_j :=
        P.rekey_tm (hvC.2.2.2 0 zeroGhost)
      have ext_h_cprj : Heap.Extends h m_cprj := evBvr.heap_extends.trans evCprj.heap_extends
      obtain ⟨kbs, cbs, krest, crest, hkstrip, hcstrip, hdoms, hkrestTm⟩ :=
        struct_eq_tele_tm nP (by omega) hktyTm (hcty.mono ext_h_cprj) evTele
      simp only [Nat.zero_add] at hkrestTm
      obtain ⟨kfbs, krem, hkfstrip, hkremTm, hm_pfor⟩ :=
        Decl.peel_n_foralls_tm fidx (val_natCast_wide_p (by omega)) evPfor hkrestTm
      subst hm_pfor
      obtain ⟨kfdom, kfrest, ℓkf, rfl, hkfdomTm, -, -⟩ := hkremTm.forallE_of_load ldForall
      have hkfdom_eq := Decl.kexpr_struct_eq_tm_one hkfdomTm
        (hraw.mono (ext_h_cprj.trans evTele.heap_extends)) evEq
      exact Or.inr ⟨hnoBvr, cvAuxC, kbs, krest, cbs, crest, kfbs, kfdom, kfrest, Core.bmeta ℓkf,
        hfindAuxC, hkstrip, hcstrip, hdoms, hkfstrip, hkfdom_eq⟩
    | _ => simp [kciEnum] at hveq

/-! ## Section 8: `check_proj_pure_rec`, `check_proj_pure_defn`, `check_proj_pure_body`, `check_proj_pure` -/

/-- Shared major-premise extraction for `aux.rec` inside both `check_proj_pure_rec` and
`check_proj_pure_defn`. -/
private theorem auxRec_major_spec (P : ProjsCtx.{u})
    {auxKey auxRecKey : KKey} {auxBlk : _root_.Address} {aAux : Bytes.Address}
    {cvAuxRec : ConstantVal .anon} {arules : List (RecRule .anon)}
    {x_arty x_aux_addr : SourceValue F} {nP bnl anc : Nat}
    {h h_peel h_sp h_aeq h_lvls h_leq h_len h_take h_bv h_peq h_lkp : Heap F}
    {v_peel x_maj_dom w1 w2 x_maj_h x_maj_args x_maj_addr x_maj_lvls
      v_aeq v_lvls v_leq v_len v_np1 v_take v_bv v_peq p_lkp x_mbv v_tot v_bvstart : SourceValue F}
    {cs_peel cs_sp cs_aeq cs_lvls cs_leq cs_len cs_take cs_bv cs_peq cs_lkp : List (Call F)}
    (hnP : nP < 72057594037927936) (hbnl : bnl < 4294967296) (hanc : anc < 72057594037927936)
    (haAux_eq : Core.keyOf P.t (ixAddr aAux) = auxKey)
    (auxIndWit : NativeIndWitness P.t P.E P.env auxKey)
    (hauxInd_blk : auxIndWit.ip.block = auxBlk)
    (hauxInd_idx : auxIndWit.ip.idx.toNat = 0)
    (hfindAuxRec : P.env.find? auxRecKey =
      some (.recInfo cvAuxRec (nP + 1 + anc + 1) (nP + 1 + anc) arules))
    (hartyTm : Tm (Core.keyOf P.t) 0 zeroGhost h 0 (Core.posOf cvAuxRec.levelParams cvAuxRec.type) x_arty)
    (haAux : Bytes.RepAddressRef addrTy h aAux x_aux_addr)
    (hmemLen : (⟨Obs.Names.«Lists::length<&KernelTypes::KExprNode>», [x_maj_args], h_leq⟩ : Call F) ∈ P.calls)
    (hv_tot : v_tot = .field ((nP + 1 + anc + 1 : Nat) : F))
    (evPeel : ObsFn Obs.W "KernelCheck::peel_n_foralls" [x_arty, v_tot] h v_peel h_peel cs_peel)
    (ldMaj : loadValue h_peel v_peel = .ok (.construct kexprEnum "Forall" [x_maj_dom, w1, w2]))
    (evSp : ObsFn Obs.W "KernelTypes::collect_spine" [x_maj_dom] h_peel (.tuple [x_maj_h, x_maj_args]) h_sp cs_sp)
    (ldH : loadValue h_sp x_maj_h = .ok (.construct kexprEnum "Const" [x_maj_addr, x_maj_lvls]))
    (evAeq : ObsFn Obs.W "Bytes::address_eq" [x_maj_addr, x_aux_addr] h_sp v_aeq h_aeq cs_aeq)
    (haeq1 : v_aeq = .field 1)
    (evLvls : ObsFn Obs.W "KernelCheck::build_param_lvls_range" [.field 1, .field (bnl : F), .field 0] h_aeq v_lvls h_lvls cs_lvls)
    (evLeq : ObsFn Obs.W "KernelCheck::level_list_struct_eq" [x_maj_lvls, v_lvls] h_lvls v_leq h_leq cs_leq)
    (hleq1 : v_leq = .field 1)
    (evLen : ObsFn Obs.W Obs.Names.«Lists::length<&KernelTypes::KExprNode>» [x_maj_args] h_leq v_len h_len cs_len)
    (opNp1 : evalBinOp .add (.field (nP : F)) (.field 1) = .ok v_np1)
    (hlenEq : v_len = v_np1)
    (evTake : ObsFn Obs.W Obs.Names.«Lists::take<&KernelTypes::KExprNode>» [x_maj_args, .field (nP : F)] h_len v_take h_take cs_take)
    (hv_bvstart : v_bvstart = .field ((nP + 1 + anc + 1 : Nat) : F))
    (evBv : ObsFn Obs.W "KernelModeled::bvars_desc" [v_bvstart, .field (nP : F)] h_take v_bv h_bv cs_bv)
    (evPeq : ObsFn Obs.W "KernelCheck::spec_params_ptr_eq" [v_take, v_bv] h_bv v_peq h_peq cs_peq)
    (hpeq1 : v_peq = .field 1)
    (evLkp : ObsFn Obs.W Obs.Names.«Lists::lookup<&KernelTypes::KExprNode>» [x_maj_args, .field (nP : F)] h_peq p_lkp h_lkp cs_lkp)
    (ldMbv : loadValue h_lkp p_lkp = .ok (.construct kexprEnum "BVar" [x_mbv]))
    (hmbv0 : x_mbv = .field 0) :
    Heap.Extends h h_lkp ∧
    (∀ j rl, arules[j]? = some rl → rl.ctor = Core.keyOf P.t (Core.cprjAddr auxBlk 0 j)) ∧
    ∃ (majBs : List (KExpr × Ix.Kernel.BinderMeta)) (majDom majBody : KExpr)
      (majBm : Ix.Kernel.BinderMeta) (majLvls : List KLevel) (majArgs : List KExpr),
      (Core.posOf cvAuxRec.levelParams cvAuxRec.type).stripPis (nP + 1 + anc + 1) =
        some (majBs, .forallE majDom majBody majBm) ∧
      majDom = Expr.mkAppN (.const auxKey majLvls) majArgs ∧
      LvEqList majLvls ((List.range bnl).map fun m => .param (1 + m)) ∧
      majArgs.length = nP + 1 ∧
      List.Forall₂ ExprSemEq (majArgs.take nP)
        ((List.range nP).map fun m => .bvar (nP + 1 + anc + 1 - 1 - m)) ∧
      majArgs[nP]? = some (.bvar 0) := by
  subst haeq1 hleq1 hpeq1 hv_tot hv_bvstart
  obtain ⟨majBs, majRem, hstrip, hremTm, hm_peel⟩ :=
    Decl.peel_n_foralls_tm (nP + 1 + anc + 1) (val_natCast_wide_p (by omega)) evPeel hartyTm
  subst hm_peel
  simp only [Nat.zero_add] at hremTm
  obtain ⟨majDom, majBody, ℓm, rfl, hmajDomTm, -, -⟩ := hremTm.forallE_of_load ldMaj
  obtain ⟨H_m, majArgs, hmajDomEq, hHmTm, hmajArgsRep⟩ := collect_spine_tuple_tm evSp hmajDomTm
  obtain ⟨aMaj, majLvls, rfl, haMaj, majLvls', hmajLvlsRep, hmajLvlsEq⟩ := hHmTm.const_of_load ldH
  obtain ⟨hAeq_f, hm_aeq⟩ := Lib.address_eq_spec evAeq haMaj
    (Bytes.repAddressRef_heapMono₂ addrTy evSp.heap_extends haAux)
  subst hm_aeq
  have haMaj_eq : aMaj = aAux := by by_contra hne; simp [hne] at hAeq_f
  subst haMaj_eq
  rw [haAux_eq] at hmajDomEq
  have hlvlsRep := build_param_lvls_range_start (start := 1) (n := bnl) (by omega) evLvls
  obtain ⟨hmajLvls_eq, hm_leq⟩ := Decl.level_list_struct_eq_one
    (hmajLvlsRep.mono evLvls.heap_extends) hlvlsRep evLeq
  have hmajLvls_rel : LvEqList majLvls ((List.range bnl).map fun m => Level.param (1 + m)) := by
    rw [hmajLvls_eq] at hmajLvlsEq; simpa using hmajLvlsEq
  have hmajArgsRep_l := RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) evLvls.heap_extends hmajArgsRep
  obtain ⟨hlen_f, hmajArgs_lt, hm_len⟩ := kexprList_length_bd
    (hm_leq ▸ hmajArgsRep_l) P.hbd hmemLen evLen
  subst hm_len hm_leq
  rw [evalBinOp_add_field_p opNp1] at hlenEq
  have hmajArgs_len : majArgs.length = nP + 1 := by
    have h1 : (.field (majArgs.length : F) : SourceValue F) = .field ((nP + 1 : Nat) : F) := by
      rw [← hlen_f, hlenEq]; push_cast; rfl
    exact nat_eq_of_field_eq_wide_p (by omega) (by omega) (Value.field.inj h1)
  obtain ⟨-, htakeRep⟩ := kexprList_take_spec (fun _ _ _ _ ext r => r.mono ext) evTake hmajArgsRep_l
  rw [val_natCast_wide_p (by omega)] at htakeRep
  have hbvRep := bvars_desc_tm_nat (κ := Core.keyOf P.t) (Γ := zeroGhost)
    (k := nP + 1 + anc + 1) (start := nP + 1 + anc + 1) (cnt := nP)
    (by omega) (le_refl _) (by omega) evBv
  have hmajArgs_pref := spec_params_ptr_eq_tm_one
    (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) evBv.heap_extends htakeRep) hbvRep evPeq
  have ext_lvls_peq :=
    (evTake.heap_extends.trans evBv.heap_extends).trans evPeq.heap_extends
  obtain ⟨⟨mbvE, hmaj_idx, hmbvTm⟩, hm_lkp⟩ := kexprList_lookup_spec evLkp
    (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) ext_lvls_peq hmajArgsRep_l)
  rw [val_natCast_wide_p (by omega)] at hmaj_idx
  subst hm_lkp
  obtain ⟨mbv_f, rfl, -, -, rfl⟩ := bvar_of_load_d0 hmbvTm ldMbv
  have hmbv_nat : ZMod.val mbv_f = 0 := by rw [Value.field.inj hmbv0]; exact ZMod.val_zero
  rw [hmbv_nat] at hmaj_idx
  -- Derive `hrecCtor` from `companions.recRulesNodupAndProj`
  have hrecCtor : ∀ j rl, arules[j]? = some rl → rl.ctor = Core.keyOf P.t (Core.cprjAddr auxBlk 0 j) := by
    obtain ⟨dom0, hpiDom0, hdom0Pos⟩ := piDomAt_of_stripPis_posOf hstrip
    have hfnPos : (Core.posOf cvAuxRec.levelParams dom0).getAppFn =
        .const (Core.keyOf P.t auxIndWit.addr) majLvls := by
      rw [hdom0Pos, hmajDomEq, auxIndWit.hkey, Expr.getAppFn_mkAppN]; rfl
    obtain ⟨us0, hfn0⟩ := getAppFn_posOf_const_inv hfnPos
    have hpiFn : (Core.piDomAt (nP + 1 + anc + 1) cvAuxRec.type).map (·.getAppFn) =
        some (.const (P.ctx.κ auxIndWit.addr) us0) := by
      rw [hpiDom0, Option.map_some, hfn0]; rfl
    have hprj := (P.hSE.prefixInv.companions.recRulesNodupAndProj auxRecKey cvAuxRec
      (nP + 1 + anc + 1) (nP + 1 + anc) arules hfindAuxRec).2
      auxIndWit.addr auxIndWit.cm auxIndWit.ip us0 hpiFn auxIndWit.hrec auxIndWit.hinfo
    intro j rl hj
    have h1 := hprj j rl hj
    rw [hauxInd_blk, hauxInd_idx] at h1
    exact h1
  exact ⟨(evSp.heap_extends.trans evLvls.heap_extends).trans ext_lvls_peq, hrecCtor,
    majBs, majDom, majBody, Core.bmeta ℓm, majLvls, majArgs,
    hstrip, hmajDomEq, hmajLvls_rel, hmajArgs_len, hmajArgs_pref, hmaj_idx⟩

theorem check_proj_pure_rec_spec (P : ProjsCtx.{u})
    {auxKey tagCKey auxRecKey : KKey} {auxBlk : _root_.Address}
    {bAux aAux aTagC aAuxRec : Bytes.Address}
    {x_phead_addr x_pargs x_arnl x_arty x_arnp x_arni x_arnmot x_arnmin x_arules
      x_aux_blk x_aux_addr x_tag_c_addr x_sbl x_sbl_nz x_aset r : SourceValue F}
    {sbl : KLevel} {pvalPos : KExpr} {pbs : List (KExpr × Ix.Kernel.BinderMeta)}
    {pheadLvls : List KLevel} {pargs : List KExpr}
    {cvAuxRec : ConstantVal .anon} {mI rP : Nat} {arules : List (RecRule .anon)}
    {pRec iRec mRec miRec : F} {nP bnl anc nF fidx jIdx : Nat}
    {h h' : Heap F} {cs : List (Call F)}
    (hnP : nP < 72057594037927936) (hbnl : bnl < 4294967296)
    (hanc : anc < 72057594037927936) (hnF : nF < 72057594037927936)
    (hfidx : fidx < nF) (hjIdx : jIdx < anc)
    (hbAux_eq : ixAddr bAux = auxBlk)
    (haAux_eq : Core.keyOf P.t (ixAddr aAux) = auxKey)
    (haTagC_eq : Core.keyOf P.t (ixAddr aTagC) = tagCKey)
    (haAuxRec_eq : Core.keyOf P.t (ixAddr aAuxRec) = auxRecKey)
    (hfamAux : P.sc.FamAt auxBlk 0)
    (auxIndWit : NativeIndWitness P.t P.E P.env auxKey)
    (hauxInd_blk : auxIndWit.ip.block = auxBlk)
    (hauxInd_idx : auxIndWit.ip.idx.toNat = 0)
    (hauxCtorStored : ∀ k < anc, ∃ cv knf,
      P.env.find? (Core.keyOf P.t (Core.cprjAddr auxBlk 0 k)) = some (.ctorInfo cv nP knf))
    (hp_strip : pvalPos.stripLams (nP + 1) =
      some (pbs, Expr.mkAppN (.const auxRecKey pheadLvls) pargs))
    (hp_pw : ∀ bm ∈ pbs, bm.2.pw = sbl.zeronessOf)
    (hplvls_len : pheadLvls.length = bnl + 1)
    (hplvls_elim : ∀ φ, (pheadLvls.getD 0 .zero).eval φ = 0 ↔ Ix.Kernel.Model.pwBit φ sbl.zeronessOf = 0)
    (hplvls_drop : LvEqList (pheadLvls.drop 1) ((List.range bnl).map .param))
    (hfindAuxRec : P.env.find? auxRecKey = some (.recInfo cvAuxRec mI rP arules))
    (hvAuxRec : ValRep P.sc.κ h x_arnl x_arty cvAuxRec)
    (hnpR : x_arnp = .field pRec) (hniR : x_arni = .field iRec)
    (hnmR : x_arnmot = .field mRec) (hnmiR : x_arnmin = .field miRec)
    (hrP_eq : (rP : F) = pRec + mRec + miRec) (hmI_eq : (mI : F) = pRec + mRec + miRec + iRec)
    (hcntR : rP ≤ mI ∧ mI < 288230376151711744)
    (hrules : RulesRep (Core.keyOf P.t) h cvAuxRec.levelParams 0 x_arules arules)
    (haAuxRec : Bytes.RepAddressRef addrTy h aAuxRec x_phead_addr)
    (hpargsRep : RepList kexprListEnum (fun h A p => Tm (Core.keyOf P.t) 0 zeroGhost h (nP + 1) A p) h pargs x_pargs)
    (hbAux : Bytes.RepAddressRef addrTy h bAux x_aux_blk)
    (haAux : Bytes.RepAddressRef addrTy h aAux x_aux_addr)
    (haTagC : Bytes.RepAddressRef addrTy h aTagC x_tag_c_addr)
    (hrepSbl : RepKLevel h sbl x_sbl)
    (hsbl_nz_spec : x_sbl_nz = .field 1 → ∀ φ, Ix.Kernel.Model.pwBit φ sbl.zeronessOf > 0)
    (haset : AddrMapAll addrMapEnum (fun _ k _ =>
      AdvChecked P.calls P.bAddr P.t P.lim P.csFam P.advAs k) h x_aset)
    (hsub : ∀ cl ∈ cs, cl ∈ P.calls)
    (ev : ObsFn Obs.W "KernelModeled::check_proj_pure_rec"
      [x_phead_addr, x_pargs, x_arnl, x_arty, x_arnp, x_arni, x_arnmot, x_arnmin, x_arules,
       x_aux_blk, x_aux_addr, .field (anc : F), x_tag_c_addr, x_sbl, x_sbl_nz,
       .field (nP : F), .field (bnl : F), .field (nF : F), .field (fidx : F),
       .field (jIdx : F), x_aset] h r h' cs) :
    mI = nP + 1 + anc + 1 ∧ rP = nP + 1 + anc ∧
    cvAuxRec.levelParams.length = bnl + 1 ∧
    cvAuxRec.levelParams.Perm (List.range (bnl + 1)) ∧
    (∀ j rl, arules[j]? = some rl → rl.ctor = Core.keyOf P.t (Core.cprjAddr auxBlk 0 j)) ∧
    (∃ (aR : _root_.Address) (cHost : Ixon.Constant) (rcR : Ixon.Recursor)
        (nf : Nat) (p0 : _root_.Address) (cm0 : Ixon.Constant) (ip0 : Ixon.InductiveProj),
      Core.keyOf P.t aR = auxRecKey ∧ RecHostAt P.E aR cHost rcR ∧
      recMotiveCarrierAt cHost rcR 0 nf = some p0 ∧
      Ix.Cert.recordAt P.E p0 = some cm0 ∧ cm0.info = .iPrj ip0 ∧ ip0.block = auxBlk) ∧
    (∃ (majBs : List (KExpr × Ix.Kernel.BinderMeta)) (majDom majBody : KExpr)
        (majBm : Ix.Kernel.BinderMeta) (majLvls : List KLevel) (majArgs : List KExpr),
      (Core.posOf cvAuxRec.levelParams cvAuxRec.type).stripPis (nP + 1 + anc + 1) =
        some (majBs, .forallE majDom majBody majBm) ∧
      majDom = Expr.mkAppN (.const auxKey majLvls) majArgs ∧
      LvEqList majLvls ((List.range bnl).map fun m => .param (1 + m)) ∧
      majArgs.length = nP + 1 ∧
      List.Forall₂ ExprSemEq (majArgs.take nP)
        ((List.range nP).map fun m => .bvar (nP + 1 + anc + 1 - 1 - m)) ∧
      majArgs[nP]? = some (.bvar 0)) ∧
    ProjPureBodyWitness P.t P.E P.env auxKey tagCKey auxRecKey cvAuxRec.levelParams arules
      (fun k => Core.keyOf P.t (Core.cprjAddr auxBlk 0 k)) sbl.zeronessOf
      nP bnl anc nF fidx jIdx pvalPos := by
  match Obs.«KernelModeled::check_proj_pure_rec».obs ev with
  | .run (v_qdacqrgy := v_plvls) (m_aintkoeo := m_plvls) (m_ksicvqzz := m_blkeq)
      (m_yftxmzzr := m_rblk) (cs_wywufpzb := cs_rblk) (v_nutitcbk := v_bnl1)
      (v_jabjkeuj := v_majtot) (m_dqrnkfzt := m_peel) (m_xtuozyaw := m_majsp)
      (m_qhwmmsaz := m_majaeq) (m_ocvtmpnt := m_majlvls) (m_furvjmrg := m_majleq)
      (m_gvubbxwm := m_majlen) (m_jrugkcdu := m_majtake) (m_bkafcawg := m_majbv)
      (m_eeyhhaau := m_majpeq) (m_qakmtasv := m_majlkp) (v_cxlrbkwy := v_majbvstart)
      (v_hootmcek := v_plen) (v_lgzoqlrs := v_plen_e) (m_tcowwzww := m_plen)
      (m_hsbecaoz := m_ppeq) (v_kpxdiojs := v_ptake) (v_vwuuohub := v_pbv)
      (m_yrttvmxo := m_ptake) (m_bzdllppo := m_pbv) (v_fvneoxrz := v_np1a)
      (v_hosacwic := v_tagapp) (m_pyizucvj := m_tagapp) (v_qfogzqtu := v_tagbvs)
      (m_aayhiafh := m_tagconst) (m_rdvxggwt := m_tagbvs) (v_wqdunxyx := v_np1b)
      (m_vxulazih := m_tageq) (v_ctmgkvsi := v_ptag) (m_kfsfksvq := m_ptag)
      (v_gwsaspub := v_tagidx) (m_shxzzgry := m_psubj) (p_allzfacu := p_psubj)
      (v_ujxawuye := v_subjidx) (x_sbv := x_sbv) (m_gennqwkl := m_ih) (cs_hvlucssc := cs_ih)
      (v_ofvytstb := v_rlj) (m_dkykcukr := m_rlj) (x_rnf_j := x_rnf_j) (x_ih_args_j := x_ih_args_j)
      (v_lgnynwzu := v_nihj) (m_jpgjnjac := m_nihj) (v_slfljbex := v_minj) (m_tgnpqjvk := m_minj)
      (v_leexmnsn := v_minidx) (v_brljsbfx := v_mbody) (m_ydpcxppq := m_mpeel)
      (v_otoqcdwg := v_mtot) (cs_scjnrhld := cs_nest)
      (ev_rshtqdit := evPlvls) (ev_jkovfbdj := evRblk) (ev_lsutwlwt := evBlkeq)
      (heq_fqzdfvrt := hblkeq1) (op_doerphwd := opBnl1) (heq_zcfftydb := harnlEq)
      (heq_sdgrumvc := harnpEq) (heq_nwvwrqsj := harniEq) (heq_cngqztzt := harnmotEq)
      (heq_scuryefg := harnminEq) (op_wvgzbfnh := opM1) (op_yoejtfdt := opM2) (op_qopzypls := opM3)
      (ev_hgruihkx := evMajPeel) (ld_mfnewfyr := ldMaj) (ev_ffspccks := evMajSp)
      (ld_kgnvzdpv := ldMajH) (ev_iblqfkjn := evMajAeq) (heq_vluavntd := hmajaeq1)
      (ev_kulqmnhr := evMajLvls) (ev_wfofqsdf := evMajLeq) (heq_njfscthi := hmajleq1)
      (ev_arlnacsw := evMajLen) (op_saiuztol := opMajNp1) (heq_hbijvnut := hmajlenEq)
      (ev_mnygrjnp := evMajTake) (op_ewpopdya := opB1) (op_ukhbiama := opB2) (op_vnziympe := opB3)
      (ev_ykqpzcvk := evMajBv) (ev_puyltavd := evMajPeq) (heq_jugbrwqg := hmajpeq1)
      (ev_preqblma := evMajLkp) (ld_ydmndlpj := ldMajBv) (heq_hkquyrto := hmbv0)
      (ev_dmcqdkxx := evPlen) (op_eokyajpg := opP1) (op_gswrlheb := opP2) (op_xgynhkla := opP3)
      (heq_ombumgmi := hplenEq) (ev_mrzbrjda := evPtake) (op_xjgtwawb := opNp1a)
      (ev_pkovtnzu := evPbv) (ev_ektjfhyt := evPpeq) (heq_zysjmxya := hppeq1)
      (hm_lpccgcof := hmTagConst) (op_exyciezg := opNp1b) (ev_yacewbtl := evTagBvs)
      (ev_xyutqczr := evTagApp) (op_vqjqurgp := opT1) (op_kiozuttt := opT2)
      (ev_lkdwdwtu := evPtag) (ev_klqpjhjg := evTageq) (heq_uqbuhigu := htageq1)
      (op_xpxzihna := opS1) (op_hzoizbuy := opS2) (op_fqxdzork := opS3)
      (ev_xdcitkkt := evPsubj) (ld_oobxpqpq := ldPsubj) (heq_nmzfurfp := hsbv0)
      (ev_tjjcdaoz := evRlj) (ev_ytthevnz := evIh) (heq_qzpjwkxg := hrnfEq)
      (ev_gbkpokwl := evNihj) (op_nhapkqza := opJ1) (op_brtoddyd := opJ2)
      (ev_vdfhbejv := evMinj) (op_uycvvtmi := opMtot) (ev_faxksigz := evMpeel)
      (ev_ciwpvzhv := evNest) (hc_sgljalbe := hc) .. =>
    subst hblkeq1 hppeq1 htageq1
    -- Match `pRec, iRec, mRec, miRec` and derive `mI`, `rP`, `cvAuxRec.levelParams.length`
    have hpRec : pRec = (nP : F) := Value.field.inj (hnpR.symm.trans harnpEq)
    have hiRec : iRec = 1 := Value.field.inj (hniR.symm.trans harniEq)
    have hmRec : mRec = 1 := Value.field.inj (hnmR.symm.trans harnmotEq)
    have hmiRec : miRec = (anc : F) := Value.field.inj (hnmiR.symm.trans harnminEq)
    subst hpRec hiRec hmRec hmiRec
    have hrP_nat : rP = nP + 1 + anc :=
      nat_eq_of_field_eq_wide_p (by omega) (by omega) (by rw [hrP_eq]; push_cast; ring)
    have hmI_nat : mI = nP + 1 + anc + 1 :=
      nat_eq_of_field_eq_wide_p (by omega) (by omega) (by rw [hmI_eq]; push_cast; ring)
    subst hrP_nat hmI_nat
    rw [evalBinOp_add_field_p opBnl1] at harnlEq
    have hAuxRec_lvls : cvAuxRec.levelParams.length = bnl + 1 := by
      have h1 : (.field (cvAuxRec.levelParams.length : F) : SourceValue F) =
          .field ((bnl + 1 : Nat) : F) := by
        rw [← hvAuxRec.1, harnlEq]; push_cast; rfl
      exact nat_eq_of_field_eq_u56_p (by have := hvAuxRec.2.1; omega) (by omega) (Value.field.inj h1)
    have hAuxRec_perm : cvAuxRec.levelParams.Perm (List.range (bnl + 1)) := by
      rw [← hAuxRec_lvls]; exact hvAuxRec.2.2.1
    have hplvlsRep := (show ((List.range bnl).map fun k => Level.param (0 + k)) = (List.range bnl).map Level.param by simp) ▸ build_param_lvls_range_start (start := 0) (n := bnl) (by omega) evPlvls
    -- `rec_family_block`
    obtain ⟨bOut, cHost, rcR, nf, p0, cm0, ip0, hbOut, hhost, hmot, hrec0, hinfo0, hip0_blk⟩ :=
      rec_family_block_spec P
        (Bytes.repAddressRef_heapMono₂ addrTy evPlvls.heap_extends haAuxRec) evRblk
        (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
    obtain ⟨hBeq_f, hm_blkeq⟩ := Lib.address_eq_spec evBlkeq hbOut
      (Bytes.repAddressRef_heapMono₂ addrTy (evPlvls.heap_extends.trans evRblk.heap_extends) hbAux)
    subst hm_blkeq
    have hbOut_eq : bOut = bAux := by by_contra hne; simp [hne] at hBeq_f
    subst hbOut_eq
    rw [hbAux_eq] at hip0_blk
    -- Shared major-premise check
    have ext_h_rblk : Heap.Extends h m_blkeq := evPlvls.heap_extends.trans evRblk.heap_extends
    have hmajtot_eq : v_majtot = .field ((nP + 1 + anc + 1 : Nat) : F) := by
      rw [evalBinOp_add_field_p opM1] at opM2
      rw [evalBinOp_add_field_p opM2] at opM3
      rw [evalBinOp_add_field_p opM3]; push_cast; rfl
    have hmajbv_eq : v_majbvstart = .field ((nP + 1 + anc + 1 : Nat) : F) := by
      rw [evalBinOp_add_field_p opB1] at opB2
      rw [evalBinOp_add_field_p opB2] at opB3
      rw [evalBinOp_add_field_p opB3]; push_cast; rfl
    obtain ⟨ext_rblk_maj, hrecCtor, majBs, majDom, majBody, majBm, majLvls, majArgs,
        hAuxRec_maj, hmajDom, hmajLvls, hmajArgs_len, hmajArgs_pref, hmajArgs_idx⟩ :=
      auxRec_major_spec P hnP hbnl hanc haAux_eq auxIndWit hauxInd_blk hauxInd_idx hfindAuxRec
        ((P.rekey_tm (hvAuxRec.2.2.2 0 zeroGhost)).mono ext_h_rblk)
        (Bytes.repAddressRef_heapMono₂ addrTy ext_h_rblk haAux)
        (hsub _ (by rw [hc]; simp)) hmajtot_eq evMajPeel ldMaj evMajSp ldMajH evMajAeq hmajaeq1
        evMajLvls evMajLeq hmajleq1 evMajLen opMajNp1 hmajlenEq evMajTake hmajbv_eq evMajBv
        evMajPeq hmajpeq1 evMajLkp ldMajBv hmbv0
    have ext_h_maj : Heap.Extends h m_majlkp := ext_h_rblk.trans ext_rblk_maj
    -- Checks on `x_pargs`
    have hpargsRep_m := RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) ext_h_maj hpargsRep
    obtain ⟨hplen_f, hpargs_lt, hm_plen⟩ := kexprList_length_bd hpargsRep_m P.hbd
      (hsub _ (by rw [hc]; simp)) evPlen
    subst hm_plen
    rw [evalBinOp_add_field_p opP1] at opP2
    rw [evalBinOp_add_field_p opP2] at opP3
    rw [evalBinOp_add_field_p opP3] at hplenEq
    have hpargs_len : pargs.length = nP + 1 + anc + 2 := by
      have h1 : (.field (pargs.length : F) : SourceValue F) = .field ((nP + 1 + anc + 2 : Nat) : F) := by
        rw [← hplen_f, hplenEq]; push_cast; rfl
      exact nat_eq_of_field_eq_wide_p (by omega) (by omega) (Value.field.inj h1)
    obtain ⟨-, hptakeRep⟩ := kexprList_take_spec (fun _ _ _ _ ext r => r.mono ext) evPtake hpargsRep_m
    rw [val_natCast_wide_p (by omega)] at hptakeRep
    have hnp1a_eq : v_np1a = .field ((nP + 1 : Nat) : F) := by
      rw [evalBinOp_add_field_p opNp1a]; push_cast; rfl
    rw [hnp1a_eq] at evPbv
    have hpbvRep := bvars_desc_tm_nat (κ := Core.keyOf P.t) (Γ := zeroGhost)
      (k := nP + 1) (start := nP + 1) (cnt := nP) (by omega) (le_refl _) (by omega) evPbv
    have hpargs_pref := spec_params_ptr_eq_tm_one
      (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) evPbv.heap_extends hptakeRep) hpbvRep evPpeq
    have ext_maj_ppeq : Heap.Extends m_plen m_ppeq :=
      (evPtake.heap_extends.trans evPbv.heap_extends).trans evPpeq.heap_extends
    -- Tag argument: `Expr.mkAppN (.const tagCKey ((List.range bnl).map .param)) (bvars_desc (nP+1) nP)`
    have ext_ppeq_tc : Heap.Extends m_ppeq m_tagconst := by
      rw [hmTagConst]; exact Heap.Extends.snoc _ _
    have ext_plvls_tc : Heap.Extends m_plvls m_tagconst :=
      ((evRblk.heap_extends.trans ext_rblk_maj).trans ext_maj_ppeq).trans ext_ppeq_tc
    have htagConstTm : Tm (Core.keyOf P.t) 0 zeroGhost m_tagconst (nP + 1)
        (.const tagCKey ((List.range bnl).map .param))
        (.ptr (.enum kexprEnum) m_ppeq.length) := by
      have : Resolved (Core.keyOf P.t (ixAddr aTagC)) := ⟨P.keyOf_ne_unresolved _⟩
      rw [← haTagC_eq]
      exact .const (by rw [hmTagConst]; simp)
        (Bytes.repAddressRef_heapMono₂ addrTy (evPlvls.heap_extends.trans ext_plvls_tc) haTagC)
        (hplvlsRep.mono ext_plvls_tc)
        (by simpa using LvEqList.refl ((List.range bnl).map Level.param))
    have hnp1b_eq : v_np1b = .field ((nP + 1 : Nat) : F) := by
      rw [evalBinOp_add_field_p opNp1b]; push_cast; rfl
    rw [hnp1b_eq] at evTagBvs
    have htagBvsRep := bvars_desc_tm_nat (κ := Core.keyOf P.t) (Γ := zeroGhost)
      (k := nP + 1) (start := nP + 1) (cnt := nP) (by omega) (le_refl _) (by omega) evTagBvs
    have htagAppTm := Decl.apply_spine_tm evTagApp (htagConstTm.mono evTagBvs.heap_extends) htagBvsRep
    have htagidx_eq : v_tagidx = .field ((nP + 1 + anc : Nat) : F) := by
      rw [evalBinOp_add_field_p opT1] at opT2
      rw [evalBinOp_add_field_p opT2]; push_cast; rfl
    rw [htagidx_eq] at evPtag
    have ext_maj_tagapp : Heap.Extends m_plen m_tagapp :=
      ext_maj_ppeq.trans (ext_ppeq_tc.trans (evTagBvs.heap_extends.trans evTagApp.heap_extends))
    obtain ⟨⟨tArg, hptag_get, hptagTm⟩, hm_ptag⟩ := kexprList_lookup_spec evPtag
      (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) ext_maj_tagapp hpargsRep_m)
    rw [val_natCast_wide_p (by omega)] at hptag_get
    subst hm_ptag
    have hptag_eq := Decl.kexpr_struct_eq_tm_one hptagTm htagAppTm evTageq
    -- Subject argument `BVar 0` at `nP + 1 + anc + 1`
    have hsubjidx_eq : v_subjidx = .field ((nP + 1 + anc + 1 : Nat) : F) := by
      rw [evalBinOp_add_field_p opS1] at opS2
      rw [evalBinOp_add_field_p opS2] at opS3
      rw [evalBinOp_add_field_p opS3]; push_cast; rfl
    rw [hsubjidx_eq] at evPsubj
    have ext_maj_tageq : Heap.Extends m_plen m_tageq := ext_maj_tagapp.trans evTageq.heap_extends
    obtain ⟨⟨subjE, hpsubj_get, hpsubjTm⟩, hm_psubj⟩ := kexprList_lookup_spec evPsubj
      (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) ext_maj_tageq hpargsRep_m)
    rw [val_natCast_wide_p (by omega)] at hpsubj_get
    subst hm_psubj
    obtain ⟨sbv_f, hsbv_eq, -, -, rfl⟩ := bvar_of_load_d0 hpsubjTm ldPsubj
    have hsbv_nat : ZMod.val sbv_f = 0 := by rw [Value.field.inj (hsbv_eq.symm.trans hsbv0)]; exact ZMod.val_zero
    rw [hsbv_nat] at hpsubj_get
    -- Rule `jIdx`, `rec_rule_ih_args`, `peel_n_lams_pw_eq`, `check_proj_nested_minor`
    have ext_h_tageq := ext_h_maj.trans ext_maj_tageq
    obtain ⟨⟨rlJ, hrlJ_get, hrlJRep⟩, hm_rlj⟩ :=
      krecRuleList_lookup_spec evRlj (hrules.mono ext_h_tageq)
    rw [val_natCast_wide_p (by omega)] at hrlJ_get hrlJRep
    rw [Nat.zero_add] at hrlJRep
    subst hm_rlj
    obtain ⟨hrnf_j_f, rbsJ, rargsJ, hrlJ_strip, hrargsJ_ge, hrargsJ_lt, hrargsJ_fields, hihJRep⟩ :=
      rec_rule_ih_args_spec hnP hanc hjIdx
        (P.hbdSub (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))) hrlJRep evIh
    have hrnfJ_56 : rlJ.nfields < 72057594037927936 := by
      obtain ⟨_, _, h56, _⟩ := hrlJRep; exact h56
    have hrlJ_nf : rlJ.nfields = nF :=
      nat_eq_of_field_eq_u56_p hrnfJ_56 hnF (Value.field.inj (hrnf_j_f.symm.trans hrnfEq))
    subst hrlJ_nf
    obtain ⟨hnihj_f, hnihj_lt, hm_nihj⟩ := kexprList_length_bd hihJRep P.hbd
      (hsub _ (by rw [hc]; simp)) evNihj
    subst hm_nihj
    have hnihj_len : (rargsJ.drop rlJ.nfields).length = rargsJ.length - rlJ.nfields := List.length_drop ..
    rw [hnihj_len] at hnihj_f hnihj_lt
    have hminidx_eq : v_minidx = .field ((nP + 1 + jIdx : Nat) : F) := by
      rw [evalBinOp_add_field_p opJ1] at opJ2
      rw [evalBinOp_add_field_p opJ2]; push_cast; rfl
    rw [hminidx_eq] at evMinj
    have ext_maj_ih := ext_maj_tageq.trans evIh.heap_extends
    obtain ⟨⟨minJE, hminj_get, hminjTm⟩, hm_minj⟩ := kexprList_lookup_spec evMinj
      (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) ext_maj_ih hpargsRep_m)
    rw [val_natCast_wide_p (by omega)] at hminj_get
    subst hm_minj
    rw [hnihj_f] at opMtot evNest
    have hmtot_eq : v_mtot = .field ((rlJ.nfields + (rargsJ.length - rlJ.nfields) : Nat) : F) := by
      rw [evalBinOp_add_field_p opMtot]; push_cast; rfl
    rw [hmtot_eq] at evMpeel
    have ext_h_ih := ext_h_maj.trans ext_maj_ih
    obtain ⟨mbsJ, mbody, hminJ_strip, hmbodyTm, hminJ_pw⟩ :=
      peel_n_lams_pw_eq_tm (rlJ.nfields + (rargsJ.length - rlJ.nfields)) (by omega)
        hminjTm (hrepSbl.mono ext_h_ih) evMpeel
    have ext_h_mpeel : Heap.Extends h m_mpeel := ext_h_ih.trans evMpeel.heap_extends
    have hminor := check_proj_nested_minor_spec P hnP hbnl hanc hnF hnihj_lt hfidx
      hbAux_eq haAux_eq haAuxRec_eq hfamAux hauxCtorStored hfindAuxRec hrecCtor hsbl_nz_spec
      (by simpa [Nat.add_assoc] using hmbodyTm)
      (hrules.mono ext_h_mpeel)
      (Bytes.repAddressRef_heapMono₂ addrTy ext_h_mpeel hbAux)
      (Bytes.repAddressRef_heapMono₂ addrTy ext_h_mpeel haAux)
      (Bytes.repAddressRef_heapMono₂ addrTy ext_h_mpeel haAuxRec)
      (AddrMapAll.mono (fun _ _ _ _ _ x => x) ext_h_mpeel haset)
      (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) evNest
    have hminJ_getD : pargs.getD (nP + 1 + jIdx) default = minJE := by simp [List.getD, hminj_get]
    refine ⟨rfl, rfl, hAuxRec_lvls, hAuxRec_perm, hrecCtor,
      ⟨ixAddr aAuxRec, cHost, rcR, nf, p0, cm0, ip0,
        haAuxRec_eq, hhost, hmot, hrec0, hinfo0, hip0_blk⟩,
      ⟨majBs, majDom, majBody, majBm, majLvls, majArgs,
        hAuxRec_maj, hmajDom, hmajLvls, hmajArgs_len, hmajArgs_pref, hmajArgs_idx⟩,
      .direct pbs pheadLvls pargs rbsJ rargsJ mbsJ mbody rlJ
        hp_strip hp_pw hplvls_len hplvls_elim hplvls_drop hpargs_len hpargs_pref
        ⟨tArg, hptag_get, hptag_eq⟩ hpsubj_get hrlJ_get rfl hrlJ_strip hrargsJ_ge hrargsJ_fields
        (hminJ_getD ▸ hminJ_strip) hminJ_pw hminor⟩

theorem check_proj_pure_defn_spec (P : ProjsCtx.{u})
    {auxKey tagCKey pheadKey : KKey} {auxBlk : _root_.Address}
    {bAux aAux aTagC aPhead : Bytes.Address}
    {x_phead_addr x_pargs x_rnl x_rval x_aux_blk x_aux_addr x_tag_c_addr
      x_sbl x_sbl_nz x_aset r : SourceValue F}
    {sbl : KLevel} {pvalPos : KExpr} {pbs : List (KExpr × Ix.Kernel.BinderMeta)}
    {pheadLvls : List KLevel} {pargs : List KExpr}
    {cvR : ConstantVal .anon} {rval : KExpr} {rHint : Ix.Kernel.ReducibilityHint}
    {nP bnl anc nF fidx jIdx : Nat} {h h' : Heap F} {cs : List (Call F)}
    (hnP : nP < 72057594037927936) (hbnl : bnl < 4294967296)
    (hanc : anc < 72057594037927936) (hnF : nF < 72057594037927936)
    (hfidx : fidx < nF) (hjIdx : jIdx < anc)
    (hbAux_eq : ixAddr bAux = auxBlk)
    (haAux_eq : Core.keyOf P.t (ixAddr aAux) = auxKey)
    (haTagC_eq : Core.keyOf P.t (ixAddr aTagC) = tagCKey)
    (haPhead_eq : Core.keyOf P.t (ixAddr aPhead) = pheadKey)
    (hfamAux : P.sc.FamAt auxBlk 0)
    (auxIndWit : NativeIndWitness P.t P.E P.env auxKey)
    (hauxInd_blk : auxIndWit.ip.block = auxBlk)
    (hauxInd_idx : auxIndWit.ip.idx.toNat = 0)
    (hauxCtorStored : ∀ k < anc, ∃ cv knf,
      P.env.find? (Core.keyOf P.t (Core.cprjAddr auxBlk 0 k)) = some (.ctorInfo cv nP knf))
    (hp_strip : pvalPos.stripLams (nP + 1) =
      some (pbs, Expr.mkAppN (.const pheadKey pheadLvls) pargs))
    (hp_pw : ∀ bm ∈ pbs, bm.2.pw = sbl.zeronessOf)
    (hplvls_len : pheadLvls.length = bnl + 1)
    (hplvls_elim : ∀ φ, (pheadLvls.getD 0 .zero).eval φ = 0 ↔ Ix.Kernel.Model.pwBit φ sbl.zeronessOf = 0)
    (hplvls_drop : LvEqList (pheadLvls.drop 1) ((List.range bnl).map .param))
    (hfindR : P.env.find? pheadKey = some (.defnInfo cvR rval rHint))
    (hR_nl : x_rnl = .field (cvR.levelParams.length : F))
    (hR_lvls_lt : cvR.levelParams.length < 4294967296)
    (hR_perm0 : cvR.levelParams.Perm (List.range cvR.levelParams.length))
    (hrvalTm : Tm (Core.keyOf P.t) 0 zeroGhost h 0 (Core.posOf cvR.levelParams rval) x_rval)
    (hrvalCr : rval.constsResolve P.env = true)
    (haPhead : Bytes.RepAddressRef addrTy h aPhead x_phead_addr)
    (hpargsRep : RepList kexprListEnum (fun h A p => Tm (Core.keyOf P.t) 0 zeroGhost h (nP + 1) A p) h pargs x_pargs)
    (hbAux : Bytes.RepAddressRef addrTy h bAux x_aux_blk)
    (haAux : Bytes.RepAddressRef addrTy h aAux x_aux_addr)
    (haTagC : Bytes.RepAddressRef addrTy h aTagC x_tag_c_addr)
    (hrepSbl : RepKLevel h sbl x_sbl)
    (hsbl_nz_spec : x_sbl_nz = .field 1 → ∀ φ, Ix.Kernel.Model.pwBit φ sbl.zeronessOf > 0)
    (haset : AddrMapAll addrMapEnum (fun _ k _ =>
      AdvChecked P.calls P.bAddr P.t P.lim P.csFam P.advAs k) h x_aset)
    (hsub : ∀ cl ∈ cs, cl ∈ P.calls)
    (ev : ObsFn Obs.W "KernelModeled::check_proj_pure_defn"
      [x_phead_addr, x_pargs, x_rnl, x_rval, x_aux_blk, x_aux_addr, .field (anc : F),
       x_tag_c_addr, x_sbl, x_sbl_nz, .field (nP : F), .field (bnl : F), .field (nF : F),
       .field (fidx : F), .field (jIdx : F), x_aset] h r h' cs) :
    ∃ (auxRecKey : KKey) (cvAuxRec : ConstantVal .anon) (arules : List (RecRule .anon)),
      P.env.find? auxRecKey = some (.recInfo cvAuxRec (nP + 1 + anc + 1) (nP + 1 + anc) arules) ∧
      cvAuxRec.levelParams.length = bnl + 1 ∧
      cvAuxRec.levelParams.Perm (List.range (bnl + 1)) ∧
      (∀ j rl, arules[j]? = some rl → rl.ctor = Core.keyOf P.t (Core.cprjAddr auxBlk 0 j)) ∧
      (∃ (aR : _root_.Address) (cHost : Ixon.Constant) (rcR : Ixon.Recursor)
          (nf : Nat) (p0 : _root_.Address) (cm0 : Ixon.Constant) (ip0 : Ixon.InductiveProj),
        Core.keyOf P.t aR = auxRecKey ∧ RecHostAt P.E aR cHost rcR ∧
        recMotiveCarrierAt cHost rcR 0 nf = some p0 ∧
        Ix.Cert.recordAt P.E p0 = some cm0 ∧ cm0.info = .iPrj ip0 ∧ ip0.block = auxBlk) ∧
      (∃ (majBs : List (KExpr × Ix.Kernel.BinderMeta)) (majDom majBody : KExpr)
          (majBm : Ix.Kernel.BinderMeta) (majLvls : List KLevel) (majArgs : List KExpr),
        (Core.posOf cvAuxRec.levelParams cvAuxRec.type).stripPis (nP + 1 + anc + 1) =
          some (majBs, .forallE majDom majBody majBm) ∧
        majDom = Expr.mkAppN (.const auxKey majLvls) majArgs ∧
        LvEqList majLvls ((List.range bnl).map fun m => .param (1 + m)) ∧
        majArgs.length = nP + 1 ∧
        List.Forall₂ ExprSemEq (majArgs.take nP)
          ((List.range nP).map fun m => .bvar (nP + 1 + anc + 1 - 1 - m)) ∧
        majArgs[nP]? = some (.bvar 0)) ∧
      ProjPureBodyWitness P.t P.E P.env auxKey tagCKey auxRecKey cvAuxRec.levelParams arules
        (fun k => Core.keyOf P.t (Core.cprjAddr auxBlk 0 k)) sbl.zeronessOf
        nP bnl anc nF fidx jIdx pvalPos := by
  match Obs.«KernelModeled::check_proj_pure_defn».obs ev with
  | .run (m_owbjouiz := m_mem) (v_mqldvidc := v_plen) (m_evvwhypc := m_plen)
      (m_mgeadsnm := m_plt) (v_nczhmone := v_npanc1) (v_iwumrdzg := v_nmot)
      (m_ddwoyinf := m_ppeq) (m_jwshchsn := m_ptake) (m_hhodqiwg := m_pbv)
      (v_pttydkun := v_np1a) (m_qtliyytb := m_psubj) (p_djwpsxlq := p_psubj)
      (v_gissseua := v_plen1) (x_sbv := x_sbv) (m_gniewqwq := m_rpeel)
      (m_zvcgeycn := m_param0) (m_hcspykae := m_rsp) (x_rh := x_rh) (x_rargs := x_rargs)
      (x_aux_rec_addr := x_aux_rec_addr) (x_ar_lvls := x_ar_lvls)
      (m_ksicvqzz := m_blkeq) (m_yftxmzzr := m_rblk) (m_snknmlna := m_arleq)
      (m_vnczfmsb := m_arlvls) (v_xuqqfsyn := v_bnl1b) (m_qoxnokbx := m_ciAR)
      (p_ovkrfmsj := p_ciAR) (cs_ktevtaxi := cs_ciAR)
      (x_arnl := x_arnl) (x_arty := x_arty) (x_arnp := x_arnp) (x_arni := x_arni)
      (x_arnmot := x_arnmot) (x_arnmin := x_arnmin) (x_arules := x_arules)
      (v_jabjkeuj := v_majtot) (m_dqrnkfzt := m_majpeel) (m_xtuozyaw := m_majsp)
      (m_qhwmmsaz := m_majaeq) (m_ocvtmpnt := m_majlvls) (m_furvjmrg := m_majleq)
      (m_gvubbxwm := m_majlen) (m_jrugkcdu := m_majtake) (m_bkafcawg := m_majbv)
      (m_eeyhhaau := m_majpeq) (m_qakmtasv := m_majlkp) (v_cxlrbkwy := v_majbvstart)
      (v_hootmcek := v_rlen) (m_tcowwzww := m_rlen) (m_wrnvzdtn := m_rpeq1)
      (m_dtqdawct := m_rtake) (m_zdusgbxt := m_rbv1) (m_gtbidkni := m_rpeq2)
      (m_dhcvvkyp := m_mtake) (m_xzmlmqxj := m_mdrop) (v_zbirbomv := v_np1c)
      (m_efvxdtrf := m_mbv) (v_xzoibmts := v_anc1) (m_mqmscgln := m_tagapp)
      (m_ghvojzgi := m_tagconst) (m_utayqybr := m_taglvls) (m_utovmogr := m_tagbvs)
      (m_vxulazih := m_tageq) (m_kfsfksvq := m_rtag) (v_gwsaspub := v_tagidx)
      (m_yzdanltl := m_rsubj) (p_fmeclipa := p_rsubj) (v_txordylv := v_subjidx)
      (x_rbv := x_rbv) (m_gennqwkl := m_ih) (m_dkykcukr := m_rlj)
      (x_rnf_j := x_rnf_j) (x_ih_args_j := x_ih_args_j) (v_lgnynwzu := v_nihj)
      (m_jpgjnjac := m_nihj) (m_tgnpqjvk := m_minj) (v_leexmnsn := v_minidx)
      (m_ydpcxppq := m_mpeel) (v_otoqcdwg := v_mtot)
      (ev_pxifpjdw := evMem) (heq_pouftxfw := hmem1)
      (op_szovihcy := opBnl1a) (heq_nmhllwyp := hrnlEq)
      (ev_xxeqotiv := evPlen) (op_hlfyibnw := opNpAnc) (op_tqtsbbum := opNpAnc1)
      (ev_dowjzuoi := evPlt) (heq_rkkyjofg := hplt1)
      (op_hupskzzd := opSubNp) (op_ydcsxzxy := opAnc1a) (op_lplcdyhp := opNmot)
      (ev_xwdbrsqn := evPtake) (op_yttnxaoc := opNp1a) (ev_uuxfkktp := evPbv)
      (ev_wpewcopb := evPpeq) (heq_qtpfrdvi := hppeq1)
      (op_ibauwrxh := opPlen1) (ev_asqmodyj := evPsubj) (ld_wnoigzcw := ldPsubj)
      (heq_tsxlmgtm := hsbv0) (hm_dawfypvh := hmParam0) (ev_ypqargsj := evRpeel)
      (ev_zxskbtka := evRsp) (ld_pkolyrlc := ldRh)
      (ev_jkovfbdj := evRblk) (ev_lsutwlwt := evBlkeq) (heq_fqzdfvrt := hblkeq1)
      (op_tuayfwkz := opBnl1b) (ev_lwrncsnh := evArLvls) (ev_bbmushaf := evArLeq)
      (heq_dtpjcgsn := harleq1) (ev_jbjkbmub := evCiAR) (ld_ouqtevwv := ldCiAR)
      (op_doerphwd := opBnl1c) (heq_zcfftydb := harnlEq)
      (heq_sdgrumvc := harnpEq) (heq_nwvwrqsj := harniEq) (heq_cngqztzt := harnmotEq)
      (heq_scuryefg := harnminEq) (op_wvgzbfnh := opM1) (op_yoejtfdt := opM2) (op_qopzypls := opM3)
      (ev_hgruihkx := evMajPeel) (ld_mfnewfyr := ldMaj) (ev_ffspccks := evMajSp)
      (ld_kgnvzdpv := ldMajH) (ev_iblqfkjn := evMajAeq) (heq_vluavntd := hmajaeq1)
      (ev_kulqmnhr := evMajLvls) (ev_wfofqsdf := evMajLeq) (heq_njfscthi := hmajleq1)
      (ev_arlnacsw := evMajLen) (op_saiuztol := opMajNp1) (heq_hbijvnut := hmajlenEq)
      (ev_mnygrjnp := evMajTake) (op_ewpopdya := opB1) (op_ukhbiama := opB2) (op_vnziympe := opB3)
      (ev_ykqpzcvk := evMajBv) (ev_puyltavd := evMajPeq) (heq_jugbrwqg := hmajpeq1)
      (ev_preqblma := evMajLkp) (ld_ydmndlpj := ldMajBv) (heq_hkquyrto := hmbv0)
      (ev_dmcqdkxx := evRlen) (op_eokyajpg := opR1) (op_gswrlheb := opR2) (op_xgynhkla := opR3)
      (heq_ombumgmi := hrlenEq) (ev_oijtfaok := evRtake) (ev_uokqvwsg := evRbv1)
      (ev_inchyxpt := evRpeq1) (heq_nkutguvj := hrpeq1) (op_bvdvqxyd := opNp1c)
      (ev_aszmdeia := evMdrop) (ev_ocehwugs := evMtake) (op_fumuaokf := opAnc1b)
      (ev_lnskyvsh := evMbv) (ev_ssqvvaba := evRpeq2) (heq_mmykiruj := hrpeq2)
      (hm_ojyvwkjn := hmTagConst) (ev_ratyjjru := evTagLvls) (ev_qigolyxy := evTagBvs)
      (ev_fjrkyvte := evTagApp) (op_vqjqurgp := opT1) (op_kiozuttt := opT2)
      (ev_lkdwdwtu := evRtag) (ev_klqpjhjg := evTageq) (heq_uqbuhigu := htageq1)
      (op_szngryhb := opS1) (op_itsqfuec := opS2) (op_bfxxcnlg := opS3)
      (ev_accmcsfn := evRsubj) (ld_mlspjsau := ldRsubj) (heq_qldlglnd := hrbv0)
      (ev_tjjcdaoz := evRlj) (ev_ytthevnz := evIh) (heq_qzpjwkxg := hrnfEq)
      (ev_gbkpokwl := evNihj) (op_nhapkqza := opJ1) (op_brtoddyd := opJ2)
      (ev_vdfhbejv := evMinj) (op_uycvvtmi := opMtot) (ev_faxksigz := evMpeel)
      (ev_ciwpvzhv := evNest) (hc_sgljalbe := hc) .. =>
    subst hmem1 hplt1 hppeq1 hblkeq1 harleq1 hrpeq1 hrpeq2 htageq1
    have hR_nonAux : Decl.NonAuxKey pheadKey := haPhead_eq ▸ P.nonAux_keyOf (ixAddr aPhead)
    rw [evalBinOp_add_field_p opBnl1a] at hrnlEq
    have hR_lvls : cvR.levelParams.length = bnl + 1 := by
      have h1 : (.field (cvR.levelParams.length : F) : SourceValue F) = .field ((bnl + 1 : Nat) : F) := by
        rw [← hR_nl, hrnlEq]; push_cast; rfl
      exact nat_eq_of_field_eq_u56_p (by omega) (by omega) (Value.field.inj h1)
    have hR_perm : cvR.levelParams.Perm (List.range (bnl + 1)) := by rw [← hR_lvls]; exact hR_perm0
    have hpargsRep_m := RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) evMem.heap_extends hpargsRep
    obtain ⟨hplen_f, hpargs_lt, hm_plen⟩ := kexprList_length_bd hpargsRep_m P.hbd
      (hsub _ (by rw [hc]; simp)) evPlen
    subst hm_plen
    rw [hplen_f] at evPlt opSubNp opPlen1 evRpeel evRbv1 evTagBvs
    have hnpanc1_eq : v_npanc1 = .field ((nP + anc + 1 : Nat) : F) := by
      rw [evalBinOp_add_field_p opNpAnc] at opNpAnc1
      rw [evalBinOp_add_field_p opNpAnc1]; push_cast; rfl
    rw [hnpanc1_eq] at evPlt
    obtain ⟨_, _, hplen_iff, _, hm_plt⟩ := Lib.less_than_fields_field evPlt
    subst hm_plt
    have hplen_gt : nP + anc + 1 < pargs.length := by
      have hlt := hplen_iff.mp rfl
      rw [val_natCast_wide_p (by omega), val_natCast_wide_p (by omega)] at hlt
      exact hlt
    have hnmot_eq : v_nmot = .field ((pargs.length - nP - (anc + 1) : Nat) : F) := by
      rw [evalBinOp_sub_field_p opSubNp] at opNmot
      rw [evalBinOp_add_field_p opAnc1a] at opNmot
      rw [evalBinOp_sub_field_p opNmot]
      congr 1
      have hnat : pargs.length - nP - (anc + 1) + (anc + 1) + nP = pargs.length := by omega
      have h1 : ((pargs.length - nP - (anc + 1) : Nat) : F) + ((anc : F) + 1) + (nP : F) =
          (pargs.length : F) := by
        have := congrArg (Nat.cast (R := F)) hnat
        simpa [Nat.cast_add] using this
      linear_combination -h1
    obtain ⟨-, hptakeRep⟩ := kexprList_take_spec (fun _ _ _ _ ext r => r.mono ext) evPtake hpargsRep_m
    rw [val_natCast_wide_p (by omega)] at hptakeRep
    have hnp1a_eq : v_np1a = .field ((nP + 1 : Nat) : F) := by
      rw [evalBinOp_add_field_p opNp1a]; push_cast; rfl
    rw [hnp1a_eq] at evPbv
    have hpbvRep := bvars_desc_tm_nat (κ := Core.keyOf P.t) (Γ := zeroGhost)
      (k := nP + 1) (start := nP + 1) (cnt := nP) (by omega) (le_refl _) (by omega) evPbv
    have hpargs_pref := spec_params_ptr_eq_tm_one
      (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) evPbv.heap_extends hptakeRep) hpbvRep evPpeq
    have ext_mem_ppeq :=
      (evPtake.heap_extends.trans evPbv.heap_extends).trans evPpeq.heap_extends
    have hplen1_eq : v_plen1 = .field ((pargs.length - 1 : Nat) : F) := by
      rw [evalBinOp_sub_field_p opPlen1]
      congr 1
      have hnat : pargs.length - 1 + 1 = pargs.length := by omega
      have h1 : ((pargs.length - 1 : Nat) : F) + 1 = (pargs.length : F) := by
        have := congrArg (Nat.cast (R := F)) hnat
        simpa [Nat.cast_add] using this
      linear_combination -h1
    rw [hplen1_eq] at evPsubj
    obtain ⟨⟨psubjE, hpsubj_get, hpsubjTm⟩, hm_psubj⟩ := kexprList_lookup_spec evPsubj
      (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) ext_mem_ppeq hpargsRep_m)
    rw [val_natCast_wide_p (by omega)] at hpsubj_get
    subst hm_psubj
    obtain ⟨sbv_f, hsbv_eq, -, -, rfl⟩ := bvar_of_load_d0 hpsubjTm ldPsubj
    have hsbv_nat : ZMod.val sbv_f = 0 := by rw [Value.field.inj (hsbv_eq.symm.trans hsbv0)]; exact ZMod.val_zero
    rw [hsbv_nat] at hpsubj_get
    -- Peel `pargs.length` lams of `rval` with `Param 0` (`.ifAllZero [0]`)
    have ext_h_param0 : Heap.Extends h m_param0 :=
      (evMem.heap_extends.trans ext_mem_ppeq).trans (by rw [hmParam0]; exact Heap.Extends.snoc _ _)
    have hrepParam0 : RepKLevel m_param0 (.param 0) (.ptr (.enum KernelLevels.klevelEnum) m_psubj.length) := by
      rw [hmParam0]; exact .param (by decide) (by simp)
    obtain ⟨rbs, rbody, hr_strip, hrbodyTm, hr_pw0⟩ :=
      peel_n_lams_pw_eq_tm pargs.length (by omega) (hrvalTm.mono ext_h_param0) hrepParam0 evRpeel
    simp only [Nat.zero_add] at hrbodyTm
    obtain ⟨H_r, rargs, hrbodyEq, hHrTm, hrargsRep⟩ := collect_spine_tuple_tm evRsp hrbodyTm
    obtain ⟨aAuxRec, arLvls, rfl, haAuxRec, arLvls', harLvlsRep, harLvlsEq⟩ := hHrTm.const_of_load ldRh
    -- `aAuxRec` is stored in `P.env` via `hrvalCr`
    have hcr_rval : (Core.posOf cvR.levelParams rval).constsResolve P.env = true := by
      rw [Decl.constsResolve_posOf]; exact hrvalCr
    have hcr_ar : (Expr.const (Core.keyOf P.t (ixAddr aAuxRec)) arLvls).constsResolve P.env = true :=
      (constsResolve_mkAppN (hrbodyEq ▸ constsResolve_stripLams hcr_rval hr_strip)).1
    have hstAuxRec := find_isSome_of_constsResolve_const hcr_ar
    -- `get_ci [x_aux_rec_addr]` → `Rec`
    have ext_h_rsp : Heap.Extends h m_rsp :=
      ext_h_param0.trans (evRpeel.heap_extends.trans evRsp.heap_extends)
    have hbnl1b_eq : v_bnl1b = .field ((bnl + 1 : Nat) : F) := by
      rw [evalBinOp_add_field_p opBnl1b]; push_cast; rfl
    rw [hbnl1b_eq] at evArLvls
    have harLvlsRange := build_param_lvls_range_start (start := 0) (n := bnl + 1) (by omega) evArLvls
    have ext_rsp_arlvls : Heap.Extends m_rsp m_arlvls :=
      (evRblk.heap_extends.trans evBlkeq.heap_extends).trans evArLvls.heap_extends
    obtain ⟨harLvls_eq, hm_arleq⟩ := Decl.level_list_struct_eq_one
      (harLvlsRep.mono ext_rsp_arlvls) harLvlsRange evArLeq
    subst hm_arleq
    have harLvls_rel : LvEqList arLvls ((List.range (bnl + 1)).map Level.param) := by
      rw [harLvls_eq] at harLvlsEq; simpa using harLvlsEq
    have hsubCiAR : ∀ cl ∈ cs_ciAR, cl ∈ P.calls := fun cl hcl => hsub cl (by rw [hc]; simp [hcl])
    obtain ⟨ciAR, hfindAR, vAR, hldAR', hrepAR⟩ := P.getCI_of_stored hstAuxRec
      (Bytes.repAddressRef_heapMono₂ addrTy ext_rsp_arlvls haAuxRec) evCiAR hsubCiAR
    rw [ldCiAR] at hldAR'; injection hldAR' with hveq
    cases hrepAR with
    | @recr _ _ _ _ _ _ _ _ _ _ _ cvAuxRec mI rP arules pRec iRec mRec miRec
        hvAuxRec hnpR hniR hnmR hnmiR hrP_eq hmI_eq hcntR hrules_sc _ _ =>
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hveq
      obtain ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, -, -, -, -⟩ := hveq
      have hpRec : pRec = (nP : F) := Value.field.inj (hnpR.symm.trans harnpEq)
      have hiRec : iRec = 1 := Value.field.inj (hniR.symm.trans harniEq)
      have hmRec : mRec = 1 := Value.field.inj (hnmR.symm.trans harnmotEq)
      have hmiRec : miRec = (anc : F) := Value.field.inj (hnmiR.symm.trans harnminEq)
      subst hpRec hiRec hmRec hmiRec
      have hrP_nat : rP = nP + 1 + anc :=
        nat_eq_of_field_eq_wide_p (by omega) (by omega) (by rw [hrP_eq]; push_cast; ring)
      have hmI_nat : mI = nP + 1 + anc + 1 :=
        nat_eq_of_field_eq_wide_p (by omega) (by omega) (by rw [hmI_eq]; push_cast; ring)
      subst hrP_nat hmI_nat
      rw [evalBinOp_add_field_p opBnl1c] at harnlEq
      have hAuxRec_lvls : cvAuxRec.levelParams.length = bnl + 1 := by
        have h1 : (.field (cvAuxRec.levelParams.length : F) : SourceValue F) =
            .field ((bnl + 1 : Nat) : F) := by
          rw [← hvAuxRec.1, harnlEq]; push_cast; rfl
        exact nat_eq_of_field_eq_u56_p (by have := hvAuxRec.2.1; omega) (by omega) (Value.field.inj h1)
      have hAuxRec_perm : cvAuxRec.levelParams.Perm (List.range (bnl + 1)) := by
        rw [← hAuxRec_lvls]; exact hvAuxRec.2.2.1
      -- `rec_family_block` on `aAuxRec`
      obtain ⟨bOut, cHost, rcR, nf, p0, cm0, ip0, hbOut, hhost, hmot, hrec0, hinfo0, hip0_blk⟩ :=
        rec_family_block_spec P haAuxRec evRblk
          (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
      obtain ⟨hBeq_f, hm_blkeq⟩ := Lib.address_eq_spec evBlkeq hbOut
        (Bytes.repAddressRef_heapMono₂ addrTy (ext_h_rsp.trans evRblk.heap_extends) hbAux)
      have hbOut_eq : bOut = bAux := by by_contra hne; simp [hne] at hBeq_f
      subst hbOut_eq
      rw [hbAux_eq] at hip0_blk
      -- Major premise check
      have ext_h_ciAR : Heap.Extends h m_ciAR :=
        ext_h_rsp.trans (ext_rsp_arlvls.trans evCiAR.heap_extends)
      have hmajtot_eq : v_majtot = .field ((nP + 1 + anc + 1 : Nat) : F) := by
        rw [evalBinOp_add_field_p opM1] at opM2
        rw [evalBinOp_add_field_p opM2] at opM3
        rw [evalBinOp_add_field_p opM3]; push_cast; rfl
      have hmajbv_eq : v_majbvstart = .field ((nP + 1 + anc + 1 : Nat) : F) := by
        rw [evalBinOp_add_field_p opB1] at opB2
        rw [evalBinOp_add_field_p opB2] at opB3
        rw [evalBinOp_add_field_p opB3]; push_cast; rfl
      obtain ⟨ext_ciAR_maj, hrecCtor, majBs, majDom, majBody, majBm, majLvls, majArgs,
          hAuxRec_maj, hmajDom, hmajLvls, hmajArgs_len, hmajArgs_pref, hmajArgs_idx⟩ :=
        auxRec_major_spec P hnP hbnl hanc haAux_eq auxIndWit hauxInd_blk hauxInd_idx hfindAR
          (P.rekey_tm (hvAuxRec.2.2.2 0 zeroGhost))
          (Bytes.repAddressRef_heapMono₂ addrTy ext_h_ciAR haAux)
          (hsub _ (by rw [hc]; simp)) hmajtot_eq evMajPeel ldMaj evMajSp ldMajH evMajAeq hmajaeq1
          evMajLvls evMajLeq hmajleq1 evMajLen opMajNp1 hmajlenEq evMajTake hmajbv_eq evMajBv
          evMajPeq hmajpeq1 evMajLkp ldMajBv hmbv0
      -- Checks on `x_rargs`
      have ext_rsp_maj : Heap.Extends m_rsp m_majlkp :=
        (ext_rsp_arlvls.trans evCiAR.heap_extends).trans ext_ciAR_maj
      have hrargsRep_m := RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) ext_rsp_maj hrargsRep
      obtain ⟨hrlen_f, hrargs_lt, hm_rlen⟩ := kexprList_length_bd hrargsRep_m P.hbd
        (hsub _ (by rw [hc]; simp)) evRlen
      subst hm_rlen
      rw [evalBinOp_add_field_p opR1] at opR2
      rw [evalBinOp_add_field_p opR2] at opR3
      rw [evalBinOp_add_field_p opR3] at hrlenEq
      have hrargs_len : rargs.length = nP + 1 + anc + 2 := by
        have h1 : (.field (rargs.length : F) : SourceValue F) = .field ((nP + 1 + anc + 2 : Nat) : F) := by
          rw [← hrlen_f, hrlenEq]; push_cast; rfl
        exact nat_eq_of_field_eq_wide_p (by omega) (by omega) (Value.field.inj h1)
      obtain ⟨-, hrtakeRep⟩ := kexprList_take_spec (fun _ _ _ _ ext r => r.mono ext) evRtake hrargsRep_m
      rw [val_natCast_wide_p (by omega)] at hrtakeRep
      have hrbv1Rep := bvars_desc_tm_nat (κ := Core.keyOf P.t) (Γ := zeroGhost)
        (k := pargs.length) (start := pargs.length) (cnt := nP)
        (by omega) (le_refl _) (by omega) evRbv1
      have hrargs_pref := spec_params_ptr_eq_tm_one
        (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) evRbv1.heap_extends hrtakeRep) hrbv1Rep evRpeq1
      have ext_maj_rpeq1 : Heap.Extends m_rlen m_rpeq1 :=
        (evRtake.heap_extends.trans evRbv1.heap_extends).trans evRpeq1.heap_extends
      have hnp1c_eq : v_np1c = .field ((nP + 1 : Nat) : F) := by
        rw [evalBinOp_add_field_p opNp1c]; push_cast; rfl
      rw [hnp1c_eq] at evMdrop
      obtain ⟨-, hmdropRep, hm_mdrop⟩ := kexprList_drop_spec evMdrop
        (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) ext_maj_rpeq1 hrargsRep_m)
      rw [val_natCast_wide_p (by omega)] at hmdropRep
      subst hm_mdrop
      obtain ⟨-, hmtakeRep⟩ := kexprList_take_spec (fun _ _ _ _ ext r => r.mono ext) evMtake hmdropRep
      rw [val_natCast_wide_p (by omega)] at hmtakeRep
      have hanc1b_eq : v_anc1 = .field ((anc + 1 : Nat) : F) := by
        rw [evalBinOp_add_field_p opAnc1b]; push_cast; rfl
      rw [hanc1b_eq] at evMbv
      have hmbvRep := bvars_desc_tm_nat (κ := Core.keyOf P.t) (Γ := zeroGhost)
        (k := pargs.length) (start := anc + 1) (cnt := anc) (by omega) (by omega) (by omega) evMbv
      have hrargs_minors := spec_params_ptr_eq_tm_one
        (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) evMbv.heap_extends hmtakeRep) hmbvRep evRpeq2
      have ext_maj_rpeq2 : Heap.Extends m_rlen m_rpeq2 :=
        ext_maj_rpeq1.trans ((evMtake.heap_extends.trans evMbv.heap_extends).trans evRpeq2.heap_extends)
      -- Tag argument in `rargs` at `nP + 1 + anc`
      have htagLvlsRep := build_param_lvls_range_start (start := 1) (n := bnl) (by omega) evTagLvls
      have ext_tl_tc : Heap.Extends m_taglvls m_tagconst := by
        rw [hmTagConst]; exact Heap.Extends.snoc _ _
      have ext_h_tc : Heap.Extends h m_tagconst :=
        (ext_h_ciAR.trans (ext_ciAR_maj.trans ext_maj_rpeq2)).trans (evTagLvls.heap_extends.trans ext_tl_tc)
      have htagConstTm : Tm (Core.keyOf P.t) 0 zeroGhost m_tagconst pargs.length
          (.const tagCKey ((List.range bnl).map fun m => .param (1 + m)))
          (.ptr (.enum kexprEnum) m_taglvls.length) := by
        have : Resolved (Core.keyOf P.t (ixAddr aTagC)) := ⟨P.keyOf_ne_unresolved _⟩
        rw [← haTagC_eq]
        exact .const (by rw [hmTagConst]; simp)
          (Bytes.repAddressRef_heapMono₂ addrTy ext_h_tc haTagC)
          (htagLvlsRep.mono ext_tl_tc)
          (LvEqList.refl _)
      have htagBvsRep := bvars_desc_tm_nat (κ := Core.keyOf P.t) (Γ := zeroGhost)
        (k := pargs.length) (start := pargs.length) (cnt := nP)
        (by omega) (le_refl _) (by omega) evTagBvs
      have htagAppTm := Decl.apply_spine_tm evTagApp (htagConstTm.mono evTagBvs.heap_extends) htagBvsRep
      have htagidx_eq : v_tagidx = .field ((nP + 1 + anc : Nat) : F) := by
        rw [evalBinOp_add_field_p opT1] at opT2
        rw [evalBinOp_add_field_p opT2]; push_cast; rfl
      rw [htagidx_eq] at evRtag
      have ext_maj_tagapp : Heap.Extends m_rlen m_tagapp :=
        ext_maj_rpeq2.trans
          ((evTagLvls.heap_extends.trans ext_tl_tc).trans (evTagBvs.heap_extends.trans evTagApp.heap_extends))
      obtain ⟨⟨rtArg, hrtag_get, hrtagTm⟩, hm_rtag⟩ := kexprList_lookup_spec evRtag
        (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) ext_maj_tagapp hrargsRep_m)
      rw [val_natCast_wide_p (by omega)] at hrtag_get
      subst hm_rtag
      have hrtag_eq := Decl.kexpr_struct_eq_tm_one hrtagTm htagAppTm evTageq
      -- Subject argument `BVar 0` at `nP + 1 + anc + 1`
      have hsubjidx_eq : v_subjidx = .field ((nP + 1 + anc + 1 : Nat) : F) := by
        rw [evalBinOp_add_field_p opS1] at opS2
        rw [evalBinOp_add_field_p opS2] at opS3
        rw [evalBinOp_add_field_p opS3]; push_cast; rfl
      rw [hsubjidx_eq] at evRsubj
      have ext_maj_tageq : Heap.Extends m_rlen m_tageq := ext_maj_tagapp.trans evTageq.heap_extends
      obtain ⟨⟨rsubjE, hrsubj_get, hrsubjTm⟩, hm_rsubj⟩ := kexprList_lookup_spec evRsubj
        (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) ext_maj_tageq hrargsRep_m)
      rw [val_natCast_wide_p (by omega)] at hrsubj_get
      subst hm_rsubj
      obtain ⟨rbv_f, hrbv_eq, -, -, rfl⟩ := bvar_of_load_d0 hrsubjTm ldRsubj
      have hrbv_nat : ZMod.val rbv_f = 0 := by rw [Value.field.inj (hrbv_eq.symm.trans hrbv0)]; exact ZMod.val_zero
      rw [hrbv_nat] at hrsubj_get
      -- Rule `jIdx`, `rec_rule_ih_args`, `peel_n_lams_pw_eq`, `check_proj_nested_minor`
      have hrules : RulesRep (Core.keyOf P.t) m_ciAR cvAuxRec.levelParams 0 x_arules arules :=
        P.rekey_rulesRep hrules_sc
      have ext_ciAR_tageq := ext_ciAR_maj.trans ext_maj_tageq
      obtain ⟨⟨rlJ, hrlJ_get, hrlJRep⟩, hm_rlj⟩ :=
        krecRuleList_lookup_spec evRlj (hrules.mono ext_ciAR_tageq)
      rw [val_natCast_wide_p (by omega)] at hrlJ_get hrlJRep
      rw [Nat.zero_add] at hrlJRep
      subst hm_rlj
      obtain ⟨hrnf_j_f, rbsJ, rargsJ, hrlJ_strip, hrargsJ_ge, hrargsJ_lt, hrargsJ_fields, hihJRep⟩ :=
        rec_rule_ih_args_spec hnP hanc hjIdx
          (P.hbdSub (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))) hrlJRep evIh
      have hrnfJ_56 : rlJ.nfields < 72057594037927936 := by
        obtain ⟨_, _, h56, _⟩ := hrlJRep; exact h56
      have hrlJ_nf : rlJ.nfields = nF :=
        nat_eq_of_field_eq_u56_p hrnfJ_56 hnF (Value.field.inj (hrnf_j_f.symm.trans hrnfEq))
      subst hrlJ_nf
      obtain ⟨hnihj_f, hnihj_lt, hm_nihj⟩ := kexprList_length_bd hihJRep P.hbd
        (hsub _ (by rw [hc]; simp)) evNihj
      subst hm_nihj
      have hnihj_len : (rargsJ.drop rlJ.nfields).length = rargsJ.length - rlJ.nfields := List.length_drop ..
      rw [hnihj_len] at hnihj_f hnihj_lt
      rw [hnmot_eq] at opJ1
      have hminidx_eq : v_minidx = .field ((nP + (pargs.length - nP - (anc + 1)) + jIdx : Nat) : F) := by
        rw [evalBinOp_add_field_p opJ1] at opJ2
        rw [evalBinOp_add_field_p opJ2]; push_cast; rfl
      rw [hminidx_eq] at evMinj
      have ext_h_ih :=
        (ext_h_ciAR.trans ext_ciAR_tageq).trans evIh.heap_extends
      obtain ⟨⟨minJE, hminj_get, hminjTm⟩, hm_minj⟩ := kexprList_lookup_spec evMinj
        (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) ext_h_ih hpargsRep)
      rw [val_natCast_wide_p (by omega)] at hminj_get
      subst hm_minj
      rw [hnihj_f] at opMtot evNest
      have hmtot_eq : v_mtot = .field ((rlJ.nfields + (rargsJ.length - rlJ.nfields) : Nat) : F) := by
        rw [evalBinOp_add_field_p opMtot]; push_cast; rfl
      rw [hmtot_eq] at evMpeel
      obtain ⟨mbsJ, mbody, hminJ_strip, hmbodyTm, hminJ_pw⟩ :=
        peel_n_lams_pw_eq_tm (rlJ.nfields + (rargsJ.length - rlJ.nfields)) (by omega)
          hminjTm (hrepSbl.mono ext_h_ih) evMpeel
      have ext_ciAR_mpeel : Heap.Extends m_ciAR m_mpeel :=
        (ext_ciAR_tageq.trans evIh.heap_extends).trans evMpeel.heap_extends
      have ext_h_mpeel : Heap.Extends h m_mpeel := ext_h_ih.trans evMpeel.heap_extends
      have ext_rsp_mpeel : Heap.Extends m_rsp m_mpeel :=
        (ext_rsp_arlvls.trans evCiAR.heap_extends).trans ext_ciAR_mpeel
      have hminor := check_proj_nested_minor_spec P hnP hbnl hanc hnF hnihj_lt hfidx
        hbAux_eq haAux_eq rfl hfamAux hauxCtorStored hfindAR hrecCtor hsbl_nz_spec
        (by simpa [Nat.add_assoc] using hmbodyTm)
        (hrules.mono ext_ciAR_mpeel)
        (Bytes.repAddressRef_heapMono₂ addrTy ext_h_mpeel hbAux)
        (Bytes.repAddressRef_heapMono₂ addrTy ext_h_mpeel haAux)
        (Bytes.repAddressRef_heapMono₂ addrTy ext_rsp_mpeel haAuxRec)
        (AddrMapAll.mono (fun _ _ _ _ _ x => x) ext_h_mpeel haset)
        (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) evNest
      have hminJ_getD : pargs.getD (nP + (pargs.length - nP - (anc + 1)) + jIdx) default = minJE := by
        simp [List.getD, hminj_get]
      exact ⟨Core.keyOf P.t (ixAddr aAuxRec), cvAuxRec, arules,
        hfindAR, hAuxRec_lvls, hAuxRec_perm, hrecCtor,
        ⟨ixAddr aAuxRec, cHost, rcR, nf, p0, cm0, ip0,
          rfl, hhost, hmot, hrec0, hinfo0, hip0_blk⟩,
        ⟨majBs, majDom, majBody, majBm, majLvls, majArgs,
          hAuxRec_maj, hmajDom, hmajLvls, hmajArgs_len, hmajArgs_pref, hmajArgs_idx⟩,
        .viaDefn pheadKey cvR rval rHint pbs pheadLvls pargs rbs arLvls rargs
          rbsJ rargsJ mbsJ mbody rlJ
          hp_strip hp_pw hplvls_len hplvls_elim hplvls_drop
          hR_nonAux hfindR hR_lvls hR_perm hplen_gt hpargs_pref hpsubj_get
          (hrbodyEq ▸ hr_strip) (fun bm hbm => by simpa [Ix.Kernel.Level.zeronessOf] using hr_pw0 bm hbm)
          harLvls_rel hrargs_len hrargs_pref hrargs_minors ⟨rtArg, hrtag_get, hrtag_eq⟩ hrsubj_get
          hrlJ_get rfl hrlJ_strip hrargsJ_ge hrargsJ_fields
          (hminJ_getD ▸ hminJ_strip) hminJ_pw hminor⟩
    | _ => simp [kciEnum] at hveq

theorem check_proj_pure_body_spec (P : ProjsCtx.{u})
    {auxKey tagCKey : KKey} {auxBlk : _root_.Address}
    {bAux aAux aTagC : Bytes.Address}
    {x_pval x_aux_blk x_aux_addr x_tag_c_addr x_sbl x_sbl_nz x_aset r : SourceValue F}
    {sbl : KLevel} {pvalPos : KExpr} {nP bnl anc nF fidx jIdx : Nat}
    {h h' : Heap F} {cs : List (Call F)}
    (hnP : nP < 72057594037927936) (hbnl : bnl < 4294967296)
    (hanc : anc < 72057594037927936) (hnF : nF < 72057594037927936)
    (hfidx : fidx < nF) (hjIdx : jIdx < anc)
    (hbAux_eq : ixAddr bAux = auxBlk)
    (haAux_eq : Core.keyOf P.t (ixAddr aAux) = auxKey)
    (haTagC_eq : Core.keyOf P.t (ixAddr aTagC) = tagCKey)
    (hfamAux : P.sc.FamAt auxBlk 0)
    (auxIndWit : NativeIndWitness P.t P.E P.env auxKey)
    (hauxInd_blk : auxIndWit.ip.block = auxBlk)
    (hauxInd_idx : auxIndWit.ip.idx.toNat = 0)
    (hauxCtorStored : ∀ k < anc, ∃ cv knf,
      P.env.find? (Core.keyOf P.t (Core.cprjAddr auxBlk 0 k)) = some (.ctorInfo cv nP knf))
    (hpvalTm : Tm (Core.keyOf P.t) 0 zeroGhost h 0 pvalPos x_pval)
    (hpvalCr : pvalPos.constsResolve P.env = true)
    (hbAux : Bytes.RepAddressRef addrTy h bAux x_aux_blk)
    (haAux : Bytes.RepAddressRef addrTy h aAux x_aux_addr)
    (haTagC : Bytes.RepAddressRef addrTy h aTagC x_tag_c_addr)
    (hrepSbl : RepKLevel h sbl x_sbl)
    (hsbl_nz_spec : x_sbl_nz = .field 1 → ∀ φ, Ix.Kernel.Model.pwBit φ sbl.zeronessOf > 0)
    (haset : AddrMapAll addrMapEnum (fun _ k _ =>
      AdvChecked P.calls P.bAddr P.t P.lim P.csFam P.advAs k) h x_aset)
    (hsub : ∀ cl ∈ cs, cl ∈ P.calls)
    (ev : ObsFn Obs.W "KernelModeled::check_proj_pure_body"
      [x_pval, x_aux_blk, x_aux_addr, .field (anc : F), x_tag_c_addr, x_sbl, x_sbl_nz,
       .field (nP : F), .field (bnl : F), .field (nF : F), .field (fidx : F),
       .field (jIdx : F), x_aset] h r h' cs) :
    ∃ (auxRecKey : KKey) (cvAuxRec : ConstantVal .anon) (arules : List (RecRule .anon)),
      P.env.find? auxRecKey = some (.recInfo cvAuxRec (nP + 1 + anc + 1) (nP + 1 + anc) arules) ∧
      cvAuxRec.levelParams.length = bnl + 1 ∧
      cvAuxRec.levelParams.Perm (List.range (bnl + 1)) ∧
      (∀ j rl, arules[j]? = some rl → rl.ctor = Core.keyOf P.t (Core.cprjAddr auxBlk 0 j)) ∧
      (∃ (aR : _root_.Address) (cHost : Ixon.Constant) (rcR : Ixon.Recursor)
          (nf : Nat) (p0 : _root_.Address) (cm0 : Ixon.Constant) (ip0 : Ixon.InductiveProj),
        Core.keyOf P.t aR = auxRecKey ∧ RecHostAt P.E aR cHost rcR ∧
        recMotiveCarrierAt cHost rcR 0 nf = some p0 ∧
        Ix.Cert.recordAt P.E p0 = some cm0 ∧ cm0.info = .iPrj ip0 ∧ ip0.block = auxBlk) ∧
      (∃ (majBs : List (KExpr × Ix.Kernel.BinderMeta)) (majDom majBody : KExpr)
          (majBm : Ix.Kernel.BinderMeta) (majLvls : List KLevel) (majArgs : List KExpr),
        (Core.posOf cvAuxRec.levelParams cvAuxRec.type).stripPis (nP + 1 + anc + 1) =
          some (majBs, .forallE majDom majBody majBm) ∧
        majDom = Expr.mkAppN (.const auxKey majLvls) majArgs ∧
        LvEqList majLvls ((List.range bnl).map fun m => .param (1 + m)) ∧
        majArgs.length = nP + 1 ∧
        List.Forall₂ ExprSemEq (majArgs.take nP)
          ((List.range nP).map fun m => .bvar (nP + 1 + anc + 1 - 1 - m)) ∧
        majArgs[nP]? = some (.bvar 0)) ∧
      ProjPureBodyWitness P.t P.E P.env auxKey tagCKey auxRecKey cvAuxRec.levelParams arules
        (fun k => Core.keyOf P.t (Core.cprjAddr auxBlk 0 k)) sbl.zeronessOf
        nP bnl anc nF fidx jIdx pvalPos := by
  have hhead : ∀ {v_plvls v_pbody v_np1 x_ph x_pargs x_phead_addr x_phead_lvls
      v_lvlen v_bnl1 v_pw v_lv0 v_leq v_lvdrop p_ci : SourceValue F}
      {m_plvls m_peel m_sp m_lvlen m_pw m_lv0 m_leq m_lvdrop m_ci : Heap F}
      {cs_plvls cs_peel cs_sp cs_lvlen cs_pw cs_lv0 cs_leq cs_lvdrop cs_ci : List (Call F)},
      (⟨Obs.Names.«Lists::length<&KernelTypes::KLevelNode>», [x_phead_lvls], m_sp⟩ : Call F) ∈ P.calls →
      (∀ cl ∈ cs_ci, cl ∈ P.calls) →
      ObsFn Obs.W "KernelCheck::build_param_lvls_range" [.field 0, .field (bnl : F), .field 0] h v_plvls m_plvls cs_plvls →
      evalBinOp .add (.field (nP : F)) (.field 1) = .ok v_np1 →
      ObsFn Obs.W "KernelModeled::peel_n_lams_pw_eq" [x_pval, v_np1, x_sbl] m_plvls v_pbody m_peel cs_peel →
      ObsFn Obs.W "KernelTypes::collect_spine" [v_pbody] m_peel (.tuple [x_ph, x_pargs]) m_sp cs_sp →
      loadValue m_sp x_ph = .ok (.construct kexprEnum "Const" [x_phead_addr, x_phead_lvls]) →
      ObsFn Obs.W Obs.Names.«Lists::length<&KernelTypes::KLevelNode>» [x_phead_lvls] m_sp v_lvlen m_lvlen cs_lvlen →
      evalBinOp .add (.field (bnl : F)) (.field 1) = .ok v_bnl1 →
      v_lvlen = v_bnl1 →
      ObsFn Obs.W Obs.Names.«Lists::lookup<&KernelTypes::KLevelNode>» [x_phead_lvls, .field 0] m_lvlen v_lv0 m_lv0 cs_lv0 →
      ObsFn Obs.W "KernelLevels::pw_eq" [v_lv0, x_sbl] m_lv0 v_pw m_pw cs_pw →
      v_pw = .field 1 →
      ObsFn Obs.W Obs.Names.«Lists::drop<&KernelTypes::KLevelNode>» [x_phead_lvls, .field 1] m_pw v_lvdrop m_lvdrop cs_lvdrop →
      ObsFn Obs.W "KernelCheck::level_list_struct_eq" [v_lvdrop, v_plvls] m_lvdrop v_leq m_leq cs_leq →
      v_leq = .field 1 →
      ObsFn Obs.W "Ingress::get_ci" [x_phead_addr] m_leq p_ci m_ci cs_ci →
      ∃ (aPhead : Bytes.Address) (pbs : List (KExpr × Ix.Kernel.BinderMeta))
        (pheadLvls : List KLevel) (pargs : List KExpr) (ci : ConstantInfo .anon),
        Heap.Extends h m_ci ∧
        Bytes.RepAddressRef addrTy m_ci aPhead x_phead_addr ∧
        RepList kexprListEnum (fun h A p => Tm (Core.keyOf P.t) 0 zeroGhost h (nP + 1) A p) m_ci pargs x_pargs ∧
        pvalPos.stripLams (nP + 1) = some (pbs, Expr.mkAppN (.const (Core.keyOf P.t (ixAddr aPhead)) pheadLvls) pargs) ∧
        (∀ bm ∈ pbs, bm.2.pw = sbl.zeronessOf) ∧
        pheadLvls.length = bnl + 1 ∧
        (∀ φ, (pheadLvls.getD 0 .zero).eval φ = 0 ↔ Ix.Kernel.Model.pwBit φ sbl.zeronessOf = 0) ∧
        LvEqList (pheadLvls.drop 1) ((List.range bnl).map .param) ∧
        P.env.find? (Core.keyOf P.t (ixAddr aPhead)) = some ci ∧
        CIPtrRep P.sc.κ m_ci p_ci ci ∧
        Bytes.RepAddressRef addrTy m_leq aPhead x_phead_addr := by
    intro v_plvls v_pbody v_np1 x_ph x_pargs x_phead_addr x_phead_lvls
      v_lvlen v_bnl1 v_pw v_lv0 v_leq v_lvdrop p_ci
      m_plvls m_peel m_sp m_lvlen m_pw m_lv0 m_leq m_lvdrop m_ci
      cs_plvls cs_peel cs_sp cs_lvlen cs_pw cs_lv0 cs_leq cs_lvdrop cs_ci
      hmemLen hsubCi evPlvls opNp1 evPeel evSp ldPh evLvlen opBnl1 hlvlenEq
      evLv0 evPw hpw1 evLvdrop evLeq hleq1 evCi
    subst hpw1 hleq1
    have hplvlsRep := (show ((List.range bnl).map fun k => Level.param (0 + k)) = (List.range bnl).map Level.param by simp) ▸ build_param_lvls_range_start (start := 0) (n := bnl) (by omega) evPlvls
    have hnp1_eq : v_np1 = .field ((nP + 1 : Nat) : F) := by
      rw [evalBinOp_add_field_p opNp1]; push_cast; rfl
    rw [hnp1_eq] at evPeel
    obtain ⟨pbs, pbody, hp_strip, hpbodyTm, hp_pw⟩ :=
      peel_n_lams_pw_eq_tm (nP + 1) (by omega)
        (hpvalTm.mono evPlvls.heap_extends) (hrepSbl.mono evPlvls.heap_extends) evPeel
    simp only [Nat.zero_add] at hpbodyTm
    obtain ⟨H_p, pargs, hpbodyEq, hHpTm, hpargsRep⟩ := collect_spine_tuple_tm evSp hpbodyTm
    obtain ⟨aPhead, pheadLvls, rfl, haPhead, pheadLvls', hpheadLvlsRep, hpheadLvlsEq⟩ :=
      hHpTm.const_of_load ldPh
    obtain ⟨hlvlen_f, hpheadLvls_lt, hm_lvlen⟩ :=
      klevelList_length_bd hpheadLvlsRep P.hbd hmemLen evLvlen
    subst hm_lvlen
    rw [evalBinOp_add_field_p opBnl1] at hlvlenEq
    have hplvls_len : pheadLvls.length = bnl + 1 := by
      have h1 : (.field (pheadLvls'.length : F) : SourceValue F) = .field ((bnl + 1 : Nat) : F) := by
        rw [← hlvlen_f, hlvlenEq]; push_cast; rfl
      exact hpheadLvlsEq.length_eq.trans
        (nat_eq_of_field_eq_wide_p (by omega) (by omega) (Value.field.inj h1))
    obtain ⟨⟨lv0', hlv0'_get, hlv0'_rep⟩, hm_lv0⟩ := klevelList_lookup_spec evLv0 hpheadLvlsRep
    rw [ZMod.val_zero] at hlv0'_get
    subst hm_lv0
    have ext_h_sp :=
      (evPlvls.heap_extends.trans evPeel.heap_extends).trans evSp.heap_extends
    have hlv0'_pw := eval_zero_iff_pwBit_zero_of_pw_eq hlv0'_rep (hrepSbl.mono ext_h_sp) evPw
    have hplvls_elim : ∀ φ, (pheadLvls.getD 0 .zero).eval φ = 0 ↔ Ix.Kernel.Model.pwBit φ sbl.zeronessOf = 0 := by
      intro φ
      rw [lvEqList_getD_zero hpheadLvlsEq φ]
      have hget0 : pheadLvls'.getD 0 .zero = lv0' := by simp [List.getD, hlv0'_get]
      rw [hget0]; exact hlv0'_pw φ
    obtain ⟨-, hlvdropRep, hm_lvdrop⟩ :=
      klevelList_drop_spec evLvdrop (hpheadLvlsRep.mono evPw.heap_extends)
    rw [ZMod.val_one] at hlvdropRep
    subst hm_lvdrop
    have ext_plvls_pw :=
      (evPeel.heap_extends.trans evSp.heap_extends).trans evPw.heap_extends
    obtain ⟨hlvdrop_eq, hm_leq⟩ := Decl.level_list_struct_eq_one hlvdropRep
      (hplvlsRep.mono ext_plvls_pw) evLeq
    subst hm_leq
    have hplvls_drop : LvEqList (pheadLvls.drop 1) ((List.range bnl).map Level.param) := by
      have h1 := lvEqList_drop hpheadLvlsEq 1
      rw [hlvdrop_eq] at h1; simpa using h1
    have hcr_head : (Expr.const (Core.keyOf P.t (ixAddr aPhead)) pheadLvls).constsResolve P.env = true :=
      (constsResolve_mkAppN (hpbodyEq ▸ constsResolve_stripLams hpvalCr hp_strip)).1
    have hstHead := find_isSome_of_constsResolve_const hcr_head
    have haPhead_pw := Bytes.repAddressRef_heapMono₂ addrTy evPw.heap_extends haPhead
    obtain ⟨ci, hfindCi, hciPtr⟩ := P.getCI_of_stored hstHead haPhead_pw evCi hsubCi
    have ext_sp_ci := evPw.heap_extends.trans evCi.heap_extends
    exact ⟨aPhead, pbs, pheadLvls, pargs, ci, ext_h_sp.trans ext_sp_ci,
      Bytes.repAddressRef_heapMono₂ addrTy ext_sp_ci haPhead,
      RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) ext_sp_ci hpargsRep,
      hpbodyEq ▸ hp_strip, hp_pw, hplvls_len, hplvls_elim, hplvls_drop, hfindCi, hciPtr, haPhead_pw⟩
  match Obs.«KernelModeled::check_proj_pure_body».obs ev with
  | .Rec (m_rcpqfuna := m_ci) (cs_orkpbzzk := cs_ci) (cs_ctcjxhph := cs_rec)
      (ev_rshtqdit := evPlvls) (op_uuhsyurb := opNp1) (ev_gxtvjnsg := evPeel)
      (ev_ujxohomv := evSp) (ld_shrryqkl := ldPh) (ev_dmcqdkxx := evLvlen)
      (op_xgynhkla := opBnl1) (heq_ombumgmi := hlvlenEq) (ev_jjsknwtc := evLv0)
      (ev_ikqompra := evPw) (heq_wafgipri := hpw1) (ev_kdzifxkd := evLvdrop)
      (ev_bbmushaf := evLeq) (heq_dtpjcgsn := hleq1) (ev_aoulgoya := evCi)
      (ld_bolbylmd := ldRec) (ev_cdyguuig := evRec) (hc_cexanrqv := hc) .. =>
    have hsubCi : ∀ cl ∈ cs_ci, cl ∈ P.calls := fun cl hcl => hsub cl (by rw [hc]; simp [hcl])
    obtain ⟨aPhead, pbs, pheadLvls, pargs, ci, ext_h_ci, haPhead_ci, hpargs_ci,
        hp_strip, hp_pw, hplvls_len, hplvls_elim, hplvls_drop, hfindCi, ⟨vCi, hldCi', hrepCi⟩,
        haPhead_pw⟩ :=
      hhead (hsub _ (by rw [hc]; simp)) hsubCi evPlvls opNp1 evPeel evSp ldPh evLvlen opBnl1
        hlvlenEq evLv0 evPw hpw1 evLvdrop evLeq hleq1 evCi
    rw [ldRec] at hldCi'; injection hldCi' with hveq
    cases hrepCi with
    | @recr _ _ _ _ _ _ _ _ _ _ _ cvAuxRec mI rP arules pRec iRec mRec miRec
        hvAuxRec hnpR hniR hnmR hnmiR hrP_eq hmI_eq hcntR hrules_sc _ _ =>
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hveq
      obtain ⟨_, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, -, -, -, -⟩ := hveq
      obtain ⟨hmI, hrP, hlvls, hperm, hrecCtor, hfamBlk, hmaj, hbody⟩ :=
        check_proj_pure_rec_spec P hnP hbnl hanc hnF hfidx hjIdx hbAux_eq haAux_eq haTagC_eq rfl
          hfamAux auxIndWit hauxInd_blk hauxInd_idx hauxCtorStored
          hp_strip hp_pw hplvls_len hplvls_elim hplvls_drop hfindCi
          hvAuxRec hnpR hniR hnmR hnmiR hrP_eq hmI_eq hcntR (P.rekey_rulesRep hrules_sc)
          haPhead_ci hpargs_ci
          (Bytes.repAddressRef_heapMono₂ addrTy ext_h_ci hbAux)
          (Bytes.repAddressRef_heapMono₂ addrTy ext_h_ci haAux)
          (Bytes.repAddressRef_heapMono₂ addrTy ext_h_ci haTagC)
          (hrepSbl.mono ext_h_ci) hsbl_nz_spec
          (AddrMapAll.mono (fun _ _ _ _ _ x => x) ext_h_ci haset)
          (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) evRec
      subst hmI hrP
      exact ⟨Core.keyOf P.t (ixAddr aPhead), cvAuxRec, arules,
        hfindCi, hlvls, hperm, hrecCtor, hfamBlk, hmaj, hbody⟩
    | _ => simp [kciEnum] at hveq
  | .Defn (m_rcpqfuna := m_ci) (cs_orkpbzzk := cs_ci) (cs_sfjmiqjr := cs_defn)
      (ev_rshtqdit := evPlvls) (op_uuhsyurb := opNp1) (ev_gxtvjnsg := evPeel)
      (ev_ujxohomv := evSp) (ld_shrryqkl := ldPh) (ev_dmcqdkxx := evLvlen)
      (op_xgynhkla := opBnl1) (heq_ombumgmi := hlvlenEq) (ev_jjsknwtc := evLv0)
      (ev_ikqompra := evPw) (heq_wafgipri := hpw1) (ev_kdzifxkd := evLvdrop)
      (ev_bbmushaf := evLeq) (heq_dtpjcgsn := hleq1) (ev_aoulgoya := evCi)
      (ld_bolbylmd := ldDefn) (ev_uxbikqyp := evDefn) (hc_mdosrdaa := hc) .. =>
    have hsubCi : ∀ cl ∈ cs_ci, cl ∈ P.calls := fun cl hcl => hsub cl (by rw [hc]; simp [hcl])
    obtain ⟨aPhead, pbs, pheadLvls, pargs, ci, ext_h_ci, haPhead_ci, hpargs_ci,
        hp_strip, hp_pw, hplvls_len, hplvls_elim, hplvls_drop, hfindCi, ⟨vCi, hldCi', hrepCi⟩, _⟩ :=
      hhead (hsub _ (by rw [hc]; simp)) hsubCi evPlvls opNp1 evPeel evSp ldPh evLvlen opBnl1
        hlvlenEq evLv0 evPw hpw1 evLvdrop evLeq hleq1 evCi
    rw [ldDefn] at hldCi'; injection hldCi' with hveq
    cases hrepCi with
    | @defn _ _ _ _ _ cvR rval rHint hvR hrvalTmC =>
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hveq
      obtain ⟨_, _, rfl, -, rfl, -, -⟩ := hveq
      have hcwf := P.hwf _ (Ix.Kernel.Semantics.Env.find?_mem hfindCi)
      have hrvalCr : rval.constsResolve P.env = true := (hcwf.2.2.2.2.1 _ _ _ rfl).2.2.1
      exact check_proj_pure_defn_spec P hnP hbnl hanc hnF hfidx hjIdx hbAux_eq haAux_eq haTagC_eq rfl
        hfamAux auxIndWit hauxInd_blk hauxInd_idx hauxCtorStored
        hp_strip hp_pw hplvls_len hplvls_elim hplvls_drop
        hfindCi hvR.1 hvR.2.1 hvR.2.2.1 (P.rekey_tm (hrvalTmC 0 zeroGhost)) hrvalCr
        haPhead_ci hpargs_ci
        (Bytes.repAddressRef_heapMono₂ addrTy ext_h_ci hbAux)
        (Bytes.repAddressRef_heapMono₂ addrTy ext_h_ci haAux)
        (Bytes.repAddressRef_heapMono₂ addrTy ext_h_ci haTagC)
        (hrepSbl.mono ext_h_ci) hsbl_nz_spec
        (AddrMapAll.mono (fun _ _ _ _ _ x => x) ext_h_ci haset)
        (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) evDefn
    | _ => simp [kciEnum] at hveq

private theorem stripPis_posOf_some {lps : List LevelParam} :
    ∀ {n : Nat} {e rem : KExpr} {bs : List (KExpr × Ix.Kernel.BinderMeta)},
      e.stripPis n = some (bs, rem) →
      ∃ bs', (Core.posOf lps e).stripPis n = some (bs', Core.posOf lps rem)
  | 0, _, _, _, h => by
    injection h with hp; injection hp with _ hr; subst hr
    exact ⟨[], rfl⟩
  | n + 1, .forallE t b bm, rem, bs, h => by
    simp only [Expr.stripPis] at h
    cases hb : b.stripPis n with
    | none => simp [hb] at h
    | some p =>
      rcases p with ⟨bs₀, rem₀⟩
      rw [hb] at h; injection h with hp; injection hp with _ hr; dsimp only at hr; subst hr
      obtain ⟨bs', hbs'⟩ := stripPis_posOf_some (lps := lps) hb
      refine ⟨(Core.posOf lps t,
        { pw := Ix.Kernel.Level.substPW lps (Core.posLevels lps) bm.pw, display := bm.display }) :: bs', ?_⟩
      simp [Core.posOf, Expr.instantiateLevelParams, Expr.stripPis]
      exact hbs'
  | _ + 1, .bvar _, _, _, h | _ + 1, .fvar _ _, _, _, h | _ + 1, .sort _, _, _, h
  | _ + 1, .const _ _, _, _, h | _ + 1, .app _ _, _, _, h | _ + 1, .lam _ _ _, _, _, h
  | _ + 1, .letE _ _ _ _, _, _, h | _ + 1, .lit _, _, _, h | _ + 1, .proj _ _ _, _, _, h =>
    nomatch h

private theorem stripPis_sort_len_eq :
    ∀ {m n : Nat} {e : KExpr} {bs1 bs2 : List (KExpr × Ix.Kernel.BinderMeta)} {u1 u2 : KLevel},
      e.stripPis m = some (bs1, .sort u1) → e.stripPis n = some (bs2, .sort u2) → m = n
  | 0, 0, _, _, _, _, _, _, _ => rfl
  | 0, _ + 1, e, _, _, _, _, h1, h2 => by
    cases e <;> simp [Expr.stripPis] at h1 h2
  | _ + 1, 0, e, _, _, _, _, h1, h2 => by
    cases e <;> simp [Expr.stripPis] at h1 h2
  | m + 1, n + 1, .forallE _ b _, _, _, _, _, h1, h2 => by
    simp only [Expr.stripPis] at h1 h2
    cases hb1 : b.stripPis m with
    | none => simp [hb1] at h1
    | some p1 =>
      cases hb2 : b.stripPis n with
      | none => simp [hb2] at h2
      | some p2 =>
        rcases p1 with ⟨_, r1⟩; rcases p2 with ⟨_, r2⟩
        rw [hb1] at h1; rw [hb2] at h2
        injection h1 with h1; injection h1 with _ hr1; dsimp only at hr1; subst hr1
        injection h2 with h2; injection h2 with _ hr2; dsimp only at hr2; subst hr2
        exact congrArg (· + 1) (stripPis_sort_len_eq hb1 hb2)
  | _ + 1, _ + 1, .bvar _, _, _, _, _, h1, _ | _ + 1, _ + 1, .fvar _ _, _, _, _, _, h1, _
  | _ + 1, _ + 1, .sort _, _, _, _, _, h1, _ | _ + 1, _ + 1, .const _ _, _, _, _, _, h1, _
  | _ + 1, _ + 1, .app _ _, _, _, _, _, h1, _ | _ + 1, _ + 1, .lam _ _ _, _, _, _, _, h1, _
  | _ + 1, _ + 1, .letE _ _ _ _, _, _, _, _, h1, _ | _ + 1, _ + 1, .lit _, _, _, _, _, h1, _
  | _ + 1, _ + 1, .proj _ _ _, _, _, _, _, h1, _ => nomatch h1

theorem check_proj_pure_spec (P : ProjsCtx.{u})
    {tModelKey : KKey} {aTM : Bytes.Address}
    {x_rc x_t_model x_pval x_cty_m x_raw_dom x_sbl x_sbl_nz x_aset r : SourceValue F}
    {sbl : KLevel} {pvalPos ctyMPos rawDom : KExpr} {nP bnl nF fidx : Nat}
    {h h' : Heap F} {cs : List (Call F)}
    (hnP : nP < 72057594037927936) (hbnl : bnl < 4294967296)
    (hnF : nF < 72057594037927936) (hfidx : fidx < nF)
    (haTM_eq : Core.keyOf P.t (ixAddr aTM) = tModelKey)
    (hAdvTM : AdvChecked P.calls P.bAddr P.t P.lim P.csFam P.advAs aTM)
    (hrc : Claim.RCLimRep P.t P.bAddr P.lim h x_rc)
    (haTM : Bytes.RepAddressRef addrTy h aTM x_t_model)
    (hpvalTm : Tm (Core.keyOf P.t) 0 zeroGhost h 0 pvalPos x_pval)
    (hpvalCr : pvalPos.constsResolve P.env = true)
    (hctyTm : Tm (Core.keyOf P.t) 0 zeroGhost h 0 ctyMPos x_cty_m)
    (hrawTm : Tm (Core.keyOf P.t) 0 zeroGhost h (nP + fidx) rawDom x_raw_dom)
    (hrepSbl : RepKLevel h sbl x_sbl)
    (hsbl_nz_spec : x_sbl_nz = .field 1 → ∀ φ, Ix.Kernel.Model.pwBit φ sbl.zeronessOf > 0)
    (haset : AddrMapAll addrMapEnum (fun _ k _ =>
      AdvChecked P.calls P.bAddr P.t P.lim P.csFam P.advAs k) h x_aset)
    (hsub : ∀ cl ∈ cs, cl ∈ P.calls)
    (ev : ObsFn Obs.W "KernelModeled::check_proj_pure"
      [x_rc, x_t_model, x_pval, x_cty_m, x_raw_dom, x_sbl, x_sbl_nz,
       .field (nP : F), .field (bnl : F), .field (nF : F), .field (fidx : F), x_aset]
      h r h' cs) :
    Nonempty (ProjPureWitness P.t P.E P.env tModelKey pvalPos ctyMPos rawDom sbl.zeronessOf
      nP bnl nF fidx) := by
  match Obs.«KernelModeled::check_proj_pure».obs ev with
  | .run (v_qdacqrgy := v_plvls) (m_aintkoeo := m_plvls) (m_jxiyqvdv := m_ciTM)
      (p_azgyovjs := p_ciTM) (cs_jfcnncbj := cs_ciTM) (x_tmnl := x_tmnl) (x_tmval := x_tmval)
      (m_kjqwvvkk := m_succ) (m_oryxwgln := m_zero) (m_tiuzwzyt := m_tmpeel)
      (m_izypcuix := m_sp1) (x_aux_h := x_aux_h) (x_aux_args := x_aux_args)
      (x_aux_addr := x_aux_addr) (x_aux_lvls := x_aux_lvls) (m_xqbfhtya := m_auxleq)
      (m_tcowwzww := m_auxlen) (m_gapuspoa := m_auxpeq) (m_cswywuge := m_auxtake)
      (m_csmlibsp := m_auxbv) (m_nqzviqid := m_taglkp) (m_uqrgyjzi := m_sp2)
      (x_tc_h := x_tc_h) (x_tc_args := x_tc_args) (x_tag_c_addr := x_tag_c_addr)
      (x_tc_lvls := x_tc_lvls) (m_nqbkpxoo := m_tcleq) (m_amwjepdc := m_tcpeq)
      (m_hhbxwxaw := m_tcbv) (m_ueqabnko := m_ciTC) (p_xhhroaon := p_ciTC)
      (cs_crghxgic := cs_ciTC) (x_tcnl := x_tcnl) (x_tag_blk := x_tag_blk)
      (x_tag_ind := x_tag_ind) (x_tag_cidx := x_tag_cidx) (x_tcnp := x_tcnp) (x_tcnf := x_tcnf)
      (m_bnsjeivr := m_tagmod) (cs_khswuuzz := cs_tagmod) (v_dcomhcoe := v_tagIaddr)
      (m_advesnzd := m_tagIaddr) (cs_mmktoifl := cs_tagIaddr) (v_xbevtdqn := v_ridx)
      (m_oiexxlof := m_ridx) (m_czuaafch := m_riz) (m_yqmdtvax := m_rnat)
      (m_howyuxzt := m_ciTI) (p_eoqpjmtu := p_ciTI) (cs_qfgjpjym := cs_ciTI)
      (x_tlnl := x_tlnl) (x_tlty := x_tlty) (x_tlnp := x_tlnp) (x_tlni := x_tlni)
      (x_tlnc := x_tlnc) (m_zfknvcbu := m_tlnc) (m_vjnblyay := m_tsn1) (cs_zflmqmpe := cs_tsn1)
      (m_ezynajkt := m_ciAux) (p_zgihxoti := p_ciAux) (cs_jnfwyrbe := cs_ciAux)
      (x_anl := x_anl) (x_aty := x_aty) (x_anp := x_anp) (x_ani := x_ani) (x_anc := x_anc)
      (x_aux_blk := x_aux_blk) (x_aind := x_aind) (m_jirhnmed := m_auxmod)
      (cs_qbhfknfy := cs_auxmod) (m_kxfdsief := m_tsn2) (cs_csjxwbmp := cs_tsn2)
      (v_bckfuelx := v_np1b) (v_svqvjlyh := v_jidx) (m_qsiptmsh := m_find)
      (cs_zftsgrqb := cs_find) (m_rytgljmb := m_poly) (cs_rjotcxlg := cs_poly)
      (cs_pmhwjjfa := cs_body)
      (ev_rshtqdit := evPlvls) (ev_ipetuqzi := evCiTM) (ld_mgcwgnuj := ldCiTM)
      (heq_degenrno := htmnlEq) (hm_lpcratak := hmSucc) (hm_kihgjxsn := hmZero)
      (ev_hoxcxxzd := evTmPeel) (ev_szvgtgvm := evSp1) (ld_sucpvvzm := ldAuxH)
      (ev_bqgdosch := evAuxLeq) (heq_gksbovvx := hauxleq1) (ev_dmcqdkxx := evAuxLen)
      (op_xgynhkla := opNp1a) (heq_ombumgmi := hauxlenEq) (ev_rdjkgptb := evAuxTake)
      (ev_ofwnsevo := evAuxBv) (ev_ybyqstej := evAuxPeq) (heq_ntmzhkcf := hauxpeq1)
      (ev_jchdwfin := evTagLkp) (ev_uezczvel := evSp2) (ld_muhtyejp := ldTcH)
      (ev_eeszfwzl := evTcLeq) (heq_clfnyyqw := htcleq1) (ev_puwvxscg := evTcBv)
      (ev_jiurkkhe := evTcPeq) (heq_limsbine := htcpeq1) (ev_ruhpbrts := evCiTC)
      (ld_tfdibcvk := ldCiTC) (heq_ettiritb := htcnlEq) (heq_zxmakudp := htagind0)
      (heq_wldafjzx := htcnpEq) (heq_kqptltgu := htcnf0) (ev_mrifyqqv := evTagMod)
      (heq_rapylson := htagmod0) (ev_pqqqmjtq := evTagIaddr) (ev_dpkyobcd := evRidx)
      (ev_dedfhyry := evRnat) (op_euvupebj := opRnat1) (op_ogxfukba := opRsub)
      (ev_dikajveo := evRiz) (heq_fwkhriwi := hriz0) (ev_yvelfbzo := evCiTI)
      (ld_mkokdiax := ldCiTI) (heq_cdczczrj := htlnlEq) (heq_pbhxfpje := htlnpEq)
      (heq_cwakrunh := htlni0) (ev_nyimmeno := evTlnc) (heq_wsdcltpq := htlnc1)
      (ev_hkpcbiff := evTsn1) (heq_urhkgpjy := htsn1_1) (ev_laaermvn := evCiAux)
      (ld_rrtluyiy := ldCiAux) (heq_ozlhgiik := hanlEq) (heq_ojgckxcx := hanpEq)
      (heq_lbwaychk := hani1) (heq_bpfvptps := haind0) (ev_qkafkkeu := evAuxMod)
      (heq_yeoykybk := hauxmod0) (op_otaotjqb := opNp1b) (ev_hygnnajj := evTsn2)
      (heq_gfmqkzlj := htsn2_1) (ev_ukwkaefs := evFind) (ev_gsjxezap := evPoly)
      (ev_vjraaukp := evBody) (hc_sgljalbe := hc) .. =>
    subst hauxleq1 hauxpeq1 htcleq1 htcpeq1 htagind0 htcnf0 htagmod0 hriz0 htlni0
      htlnc1 htsn1_1 hani1 haind0 hauxmod0 htsn2_1
    have hplvlsRep := (show ((List.range bnl).map fun k => Level.param (0 + k)) = (List.range bnl).map Level.param by simp) ▸ build_param_lvls_range_start (start := 0) (n := bnl) (by omega) evPlvls
    -- 1. `t_model` Defn
    obtain ⟨cvmT, mvalT, hintT, hTM_nonAux, hfindTM, htmnl_f, hTM_lvls_lt, hTM_perm0, _, hmvalT_tmC, _, hmvalT_cr⟩ :=
      P.getCI_defn_of_advChecked hAdvTM
        (Bytes.repAddressRef_heapMono₂ addrTy evPlvls.heap_extends haTM) evCiTM
        (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) ldCiTM
    rw [haTM_eq] at hTM_nonAux hfindTM
    have hTM_lvls : cvmT.levelParams.length = bnl :=
      nat_eq_of_field_eq_u56_p (by omega) (by omega) (Value.field.inj (htmnl_f.symm.trans htmnlEq))
    have hTM_perm : cvmT.levelParams.Perm (List.range bnl) := by rw [← hTM_lvls]; exact hTM_perm0
    have extSucc : Heap.Extends m_ciTM m_succ := by
      rw [hmSucc, hmZero]; exact (Heap.Extends.snoc _ _).trans (Heap.Extends.snoc _ _)
    have hrepZero : RepKLevel m_zero .zero (.ptr (.enum KernelLevels.klevelEnum) m_ciTM.length) := by
      rw [hmZero]; exact .zero (by simp)
    have hrepSucc : RepKLevel m_succ (.succ .zero) (.ptr (.enum KernelLevels.klevelEnum) m_zero.length) := by
      rw [hmSucc]; exact .succ (by simp) (hrepZero.mono (Heap.Extends.snoc _ _))
    obtain ⟨tmbs, tmbody, hTM_strip, htmbodyTm, hTM_pw0⟩ :=
      peel_n_lams_pw_eq_tm nP (by omega) ((hmvalT_tmC 0 zeroGhost).mono extSucc) hrepSucc evTmPeel
    simp only [Nat.zero_add] at htmbodyTm
    obtain ⟨H_aux, auxArgs, htmbodyEq, hHauxTm, hauxArgsRep⟩ := collect_spine_tuple_tm evSp1 htmbodyTm
    obtain ⟨aAux, auxLvls, rfl, haAux, auxLvls', hauxLvlsRep, hauxLvlsEq⟩ := hHauxTm.const_of_load ldAuxH
    have ext_plvls_sp1 : Heap.Extends m_plvls m_sp1 :=
      (evCiTM.heap_extends.trans extSucc).trans (evTmPeel.heap_extends.trans evSp1.heap_extends)
    obtain ⟨hauxLvls_eq, hm_auxleq⟩ := Decl.level_list_struct_eq_one hauxLvlsRep
      (hplvlsRep.mono ext_plvls_sp1) evAuxLeq
    subst hm_auxleq
    have hauxLvls_rel : LvEqList auxLvls ((List.range bnl).map Level.param) := by
      rw [hauxLvls_eq] at hauxLvlsEq; simpa using hauxLvlsEq
    obtain ⟨hauxlen_f, hauxArgs_lt, hm_auxlen⟩ := kexprList_length_bd hauxArgsRep P.hbd
      (hsub _ (by rw [hc]; simp)) evAuxLen
    subst hm_auxlen
    rw [evalBinOp_add_field_p opNp1a] at hauxlenEq
    have hauxArgs_len : auxArgs.length = nP + 1 := by
      have h1 : (.field (auxArgs.length : F) : SourceValue F) = .field ((nP + 1 : Nat) : F) := by
        rw [← hauxlen_f, hauxlenEq]; push_cast; rfl
      exact nat_eq_of_field_eq_wide_p (by omega) (by omega) (Value.field.inj h1)
    obtain ⟨-, hauxtakeRep⟩ := kexprList_take_spec (fun _ _ _ _ ext r => r.mono ext) evAuxTake hauxArgsRep
    rw [val_natCast_wide_p (by omega)] at hauxtakeRep
    have hauxbvRep := bvars_desc_tm_nat (κ := Core.keyOf P.t) (Γ := zeroGhost)
      (k := nP) (start := nP) (cnt := nP) (le_refl _) (le_refl _) (by omega) evAuxBv
    have hauxArgs_pref := spec_params_ptr_eq_tm_one
      (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) evAuxBv.heap_extends hauxtakeRep) hauxbvRep evAuxPeq
    have ext_sp1_auxpeq :=
      (evAuxTake.heap_extends.trans evAuxBv.heap_extends).trans evAuxPeq.heap_extends
    obtain ⟨⟨tagE, hauxArgs_tag_get, htagETm⟩, hm_taglkp⟩ := kexprList_lookup_spec evTagLkp
      (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) ext_sp1_auxpeq hauxArgsRep)
    rw [val_natCast_wide_p (by omega)] at hauxArgs_tag_get
    subst hm_taglkp
    obtain ⟨H_tc, tcArgs, htagEq, hHtcTm, htcArgsRep⟩ := collect_spine_tuple_tm evSp2 htagETm
    obtain ⟨aTagC, tcLvls, rfl, haTagC, tcLvls', htcLvlsRep, htcLvlsEq⟩ := hHtcTm.const_of_load ldTcH
    have ext_plvls_sp2 : Heap.Extends m_plvls m_sp2 :=
      ext_plvls_sp1.trans (ext_sp1_auxpeq.trans evSp2.heap_extends)
    obtain ⟨htcLvls_eq, hm_tcleq⟩ := Decl.level_list_struct_eq_one htcLvlsRep
      (hplvlsRep.mono ext_plvls_sp2) evTcLeq
    subst hm_tcleq
    have htcLvls_rel : LvEqList tcLvls ((List.range bnl).map Level.param) := by
      rw [htcLvls_eq] at htcLvlsEq; simpa using htcLvlsEq
    have htcbvRep := bvars_desc_tm_nat (κ := Core.keyOf P.t) (Γ := zeroGhost)
      (k := nP) (start := nP) (cnt := nP) (le_refl _) (le_refl _) (by omega) evTcBv
    have htcArgs_eq := spec_params_ptr_eq_tm_one
      (RepLinkedList.mono (fun _ _ _ _ ext r => r.mono ext) evTcBv.heap_extends htcArgsRep) htcbvRep evTcPeq
    -- 2. Tag constructor (`aTagC`) & Tag inductive (`tagBlk`, 0)
    have hcr_mval : (Core.posOf cvmT.levelParams mvalT).constsResolve P.env = true := by
      rw [Decl.constsResolve_posOf]; exact hmvalT_cr
    have hcr_auxApp := constsResolve_stripLams hcr_mval hTM_strip
    have hcr_aux : (Expr.const (Core.keyOf P.t (ixAddr aAux)) auxLvls).constsResolve P.env = true :=
      (constsResolve_mkAppN (htmbodyEq ▸ hcr_auxApp)).1
    have hcr_tagE : tagE.constsResolve P.env = true :=
      (constsResolve_mkAppN (htmbodyEq ▸ hcr_auxApp)).2 tagE (List.mem_of_getElem? hauxArgs_tag_get)
    have hcr_tc : (Expr.const (Core.keyOf P.t (ixAddr aTagC)) tcLvls).constsResolve P.env = true :=
      (constsResolve_mkAppN (htagEq ▸ hcr_tagE)).1
    have hstAux := find_isSome_of_constsResolve_const hcr_aux
    have hstTC := find_isSome_of_constsResolve_const hcr_tc
    have ext_sp2_tcpeq := evTcBv.heap_extends.trans evTcPeq.heap_extends
    have hsubCiTC : ∀ cl ∈ cs_ciTC, cl ∈ P.calls := fun cl hcl => hsub cl (by rw [hc]; simp [hcl])
    have haTagC_tcpeq := Bytes.repAddressRef_heapMono₂ addrTy ext_sp2_tcpeq haTagC
    obtain ⟨ciTC, hfindTC, vTC, hldTC', hrepTC⟩ := P.getCI_of_stored hstTC haTagC_tcpeq evCiTC hsubCiTC
    rw [ldCiTC] at hldTC'; injection hldTC' with hveqTC
    cases hrepTC with
    | @ctor _ _ _ _ _ _ _ _ cvTC nPTC nFTC hvTC hnpTC hnfTC hcntTC hkeyTC =>
      simp only [Value.construct.injEq, List.cons.injEq, and_true] at hveqTC
      obtain ⟨_, _, rfl, -, rfl, rfl, rfl, rfl, rfl, -⟩ := hveqTC
      have htc_lvls : cvTC.levelParams.length = bnl :=
        nat_eq_of_field_eq_u56_p (by have := hvTC.2.1; omega) (by omega)
          (Value.field.inj (hvTC.1.symm.trans htcnlEq))
      have htc_nP : nPTC = nP :=
        nat_eq_of_field_eq_u56_p hcntTC.1 hnP (Value.field.inj (hnpTC.symm.trans htcnpEq))
      have htc_nF : nFTC = 0 :=
        nat_eq_of_field_eq_u56_p hcntTC.2 (by omega) (by simpa using Value.field.inj hnfTC.symm)
      subst nPTC nFTC
      obtain ⟨cmTC, cbTag, xsTag, indTag, ctTag, bTag, iTag, jTag,
        hrecCmTC, hrecCbTag, hbTag_rep, hiTag, hcidxTag, hi56, hj56, hinfoTC,
        hmutsTag, hxsTag, hctTag⟩ := P.ctorRecordAt_of_get_ci haTagC_tcpeq evCiTC hsubCiTC ldCiTC
      have hiTag0 : iTag = 0 := Value.field.inj hiTag.symm
      subst hiTag0
      have htag_nat : NativeAt P.E (ixAddr bTag) :=
        P.nativeAt_of_block_is_modeled_zero hbTag_rep evTagMod
          (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
      -- `compute_iprj_addr [x_tag_blk, 0]` + `role_index_of ≠ role_nat + 1`
      have hsubTagI : ∀ cl ∈ cs_tagIaddr, cl ∈ P.calls := fun cl hcl => hsub cl (by rw [hc]; simp [hcl])
      obtain ⟨aTagI, haTagI_rep, haTagI_eq, hhashTagI⟩ :=
        compute_iprj_addr_hashed (c := P.ctx) (idx := 0) (by decide)
          (Bytes.repAddressRef_heapMono₂ addrTy evTagMod.heap_extends hbTag_rep)
          (P.hgoodSub hsubTagI) (by simpa using evTagIaddr)
      have ext_h_tagI : Heap.Extends h m_tagIaddr :=
        ((evPlvls.heap_extends.trans (ext_plvls_sp2.trans ext_sp2_tcpeq)).trans
          (evCiTC.heap_extends.trans evTagMod.heap_extends)).trans evTagIaddr.heap_extends
      obtain ⟨hm_ridx, hridx_res⟩ :=
        Claim.role_index_of_lim_spec (hrc.mono ext_h_tagI) ⟨aTagI, haTagI_rep, rfl⟩ evRidx
      subst hm_ridx
      match Obs.«KernelRoleSpec::role_nat».obs evRnat with
      | .run (he1 := hrnat0) (he2 := hm_rnat) .. =>
        subst hrnat0 hm_rnat
        rw [evalBinOp_add_field_p opRnat1] at opRsub
        have htagInd_neNat : Core.keyOf P.t (Core.iprjAddr (ixAddr bTag) 0) ≠ Ix.Kernel.natName := by
          intro hnatEq
          have haNat : P.t.addressOf? .nat = some (Core.iprjAddr (ixAddr bTag) 0) :=
            Core.addressOf_of_keyOf P.htwf hnatEq
          rw [← haTagI_eq] at haNat
          rcases hridx_res with ⟨_, hno⟩ | ⟨ro, hr_eq, hro⟩
          · exact hno .nat haNat
          · have hro_nat : ro = .nat := by
              have h1 := Core.keyOf_of_addressOf P.htwf hro
              have h2 := Core.keyOf_of_addressOf P.htwf haNat
              exact Ix.Kernel.Key.role.inj (h1.symm.trans h2)
            subst hro_nat
            have hnum0 : Core.roleNum .nat = 0 := rfl
            rw [hr_eq, hnum0] at opRsub
            have hsub0 := evalBinOp_sub_field_p opRsub
            rw [hsub0] at evRiz
            obtain ⟨hiz, _⟩ := Lib.is_zero_field evRiz
            simp at hiz
        -- `get_ci_iprj [x_tag_blk, 0]` + `1 < tlnc` + `type_sort_never`
        have hsubCiTI : ∀ cl ∈ cs_ciTI, cl ∈ P.calls := fun cl hcl => hsub cl (by rw [hc]; simp [hcl])
        have ext_ciTC_riz : Heap.Extends m_ciTC m_riz :=
          (evTagMod.heap_extends.trans evTagIaddr.heap_extends).trans evRiz.heap_extends
        have hbTag_riz := Bytes.repAddressRef_heapMono₂ addrTy ext_ciTC_riz hbTag_rep
        obtain ⟨cbTag2, msTag2, indTag2, hrecCbTag2, hmutsTag2, hms0Tag2, _, _, _, htlnc56, _,
          vTI, hldTI', _, _, _, _, _, hvTI⟩ := P.recordAt_of_get_ci_iprj hbTag_riz evCiTI hsubCiTI
        have hcbEq : cbTag2 = cbTag := Option.some.inj (hrecCbTag2.symm.trans hrecCbTag)
        subst cbTag2
        rw [hmutsTag] at hmutsTag2; obtain rfl := Ixon.ConstantInfo.muts.inj hmutsTag2
        simp only [ZMod.val_zero] at hxsTag hms0Tag2
        rw [hxsTag] at hms0Tag2
        obtain rfl := Ixon.MutConst.indc.inj (Option.some.inj hms0Tag2)
        rw [ldCiTI] at hldTI'; injection hldTI' with hveq; rw [← hveq] at hvTI
        simp only [Value.construct.injEq, List.cons.injEq, and_true] at hvTI
        obtain ⟨-, -, _, _, htl_np_f, htl_ni_f, htl_nc_f, -, -, -⟩ := hvTI
        have htag_nP : indTag.params.toNat = nP :=
          nat_eq_of_field_eq_u56_p (by omega) hnP (Value.field.inj (htl_np_f.symm.trans htlnpEq))
        have htag_nI : indTag.indices.toNat = 0 :=
          nat_eq_of_field_eq_u56_p (by omega) (by omega) (by simpa using Value.field.inj htl_ni_f.symm)
        rw [htl_nc_f] at evTlnc
        obtain ⟨_, _, htlnc_iff, _, hm_tlnc⟩ := Lib.less_than_fields_field evTlnc
        subst hm_tlnc
        have htag_gt1 : 1 < indTag.ctors.size := by
          have hlt := htlnc_iff.mp rfl
          rw [ZMod.val_one, val_natCast_wide_p (by omega)] at hlt; exact hlt
        -- Build `tagCWit`
        have hnotResTC : Ix.Kernel.reservedBasisNames.contains (Core.keyOf P.t (ixAddr aTagC)) = false := by
          obtain ⟨G, R, envT, hshape, _⟩ := P.hSE.shape
          exact not_reserved_tag_ctor P.htwf hshape P.hPre hrecCbTag hmutsTag
            (by simpa [ZMod.val_zero] using hxsTag) htag_gt1 htagInd_neNat hrecCmTC
            (by simpa [ZMod.val_zero] using hinfoTC)
        have hjTag_u64 : (ZMod.val jTag).toUInt64.toNat = ZMod.val jTag := by
          change (UInt64.ofNat _).toNat = _; rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
        let cpTC : Ixon.ConstructorProj := ⟨(0 : Nat).toUInt64, (ZMod.val jTag).toUInt64, ixAddr bTag⟩
        have hinfoTC' : cmTC.info = .cPrj cpTC := by simpa [cpTC, ZMod.val_zero] using hinfoTC
        let tagCWit : NativeCtorWitness P.t P.E P.env (Core.keyOf P.t (ixAddr aTagC))
            (Core.keyOf P.t (Core.iprjAddr (ixAddr bTag) 0)) (ZMod.val jTag) :=
          { addr := ixAddr aTagC
            cm := cmTC
            cp := cpTC
            cv := cvTC
            nP := nP
            nF := 0
            hkey := rfl
            hfind := hfindTC
            hnotRes := hnotResTC
            hrec := hrecCmTC
            hinfo := hinfoTC'
            hnat := htag_nat
            hindKey := by simp [cpTC]
            hcidx := hjTag_u64 }
        -- Build `tagIndWit` via `P.hreg.completeCtor` + `hhashTagI` + `getIprj`
        obtain ⟨famTag, jTag', cATag, hRegTag, hfamTag_name, -, -, -⟩ :=
          P.hreg.completeCtor (ixAddr aTagC) cmTC cpTC cvTC nP 0
            hfindTC hnotResTC hrecCmTC hinfoTC' htag_nat
        have hfindTI_fam := (P.hreg.fams famTag hRegTag).stored.former
        simp only [cpTC] at hfamTag_name
        change famTag.p.cvT.name = Core.keyOf P.t (Core.iprjAddr (ixAddr bTag) 0) at hfamTag_name
        rw [hfamTag_name] at hfindTI_fam
        let cTagI : Ixon.Constant := ⟨.iPrj ⟨(0 : Nat).toUInt64, ixAddr bTag⟩, #[], #[], #[], #[]⟩
        have hrecTagI : Ix.Cert.recordAt P.E (Core.iprjAddr (ixAddr bTag) 0) = some cTagI := by
          have hwfTI := Ingress.projConstant_wireWF_iPrj (0 : Nat).toUInt64 bTag
          have hexTI : Ixon.deConstantExact (Ixon.serConstant cTagI) = .ok cTagI :=
            Ixon.Verify.deConstantExact_serConstant cTagI hwfTI
          have hdeTI : Ixon.deConstant (Ixon.serConstant cTagI) = .ok cTagI :=
            Ingress.deConstant_of_deConstantExact hexTI
          have hszTI : (Ixon.serConstant cTagI).size < 4294967296 :=
            IxVM.Refinement.Typing.serConstant_iprj_size_lt (0 : Nat).toUInt64 bTag
          have hr0 := Claim.recordOf_hashed P.hS P.hH
            (Core.hashed_mono hsubTagI hhashTagI) hszTI hdeTI hexTI
          exact P.hSE.store.runRecord _ _ hr0
        have hnotResTI : Ix.Kernel.reservedBasisNames.contains
            (Core.keyOf P.t (Core.iprjAddr (ixAddr bTag) 0)) = false := by
          obtain ⟨G, R, envT, hshape, _⟩ := P.hSE.shape
          exact not_reserved_tag_ind P.htwf hshape P.hPre hrecCbTag hmutsTag
            (by simpa [ZMod.val_zero] using hxsTag) htag_gt1 htagInd_neNat hrecTagI rfl
        let tagIndWit : NativeIndWitness P.t P.E P.env (Core.keyOf P.t (Core.iprjAddr (ixAddr bTag) 0)) :=
          { addr := Core.iprjAddr (ixAddr bTag) 0
            cm := cTagI
            ip := ⟨(0 : Nat).toUInt64, ixAddr bTag⟩
            cv := famTag.cvS
            caps := Ix.Kernel.nativeCaps famTag.p
            hkey := rfl
            hfind := hfindTI_fam
            hnotRes := hnotResTI
            hrec := hrecTagI
            hinfo := rfl
            hnat := htag_nat }
        -- `getIprj` on `evCiTI` for `CIRep.induct` + `type_sort_never_tm`
        obtain ⟨bTC', iTC', jTC', hbTC'rep, hiTC'eq, hjTC'eq, hnameTC'⟩ := hkeyTC
        have hbTC'_eq : bTC' = bTag := addr_det hbTC'rep hbTag_rep
        have hiTC'_eq : iTC' = 0 := Value.field.inj hiTC'eq.symm
        rw [hbTC'_eq, hiTC'_eq] at hnameTC'
        have hfamTag : P.sc.FamAt (ixAddr bTag) 0 := by
          obtain ⟨hκTC, -⟩ := P.sc_kappa_eq_of_isSome hstTC
          have h1 := ScopedCtx.famAt_of_ctor (a := ixAddr aTagC) (b := ixAddr bTag)
            (i := ZMod.val (0 : F)) (j := ZMod.val jTC') (by rw [hκTC]; exact hfindTC) hnameTC'
          rwa [ZMod.val_zero] at h1
        have hfamTag' : P.sc.FamAt (ixAddr bTag) (ZMod.val (0 : F)) := by rwa [ZMod.val_zero]
        obtain ⟨ciTI, hfindTI_sc, vTI_sc, hldTI_sc, hrepTI_sc⟩ :=
          P.hSE.prefixInv.loads.getIprj x_tag_blk p_ciTI 0 m_riz _ cs_ciTI bTag
            evCiTI trivial hfamTag' (P.hcoreGoodSub hsubCiTI) hbTag_riz
        have hneTI : P.sc.κ (Core.iprjAddr (ixAddr bTag) (ZMod.val (0 : F))) ≠ Core.unresolvedKey :=
          P.hSE.prefixInv.loads.findRes _ _ hfindTI_sc
        change P.env.find? (P.sc.κ (Core.iprjAddr (ixAddr bTag) (ZMod.val (0 : F)))) = some ciTI at hfindTI_sc
        rw [P.sc_kappa_eq_of_ne hneTI, ZMod.val_zero, hfindTI_fam] at hfindTI_sc
        obtain rfl := Option.some.inj hfindTI_sc.symm
        rw [ldCiTI] at hldTI_sc; injection hldTI_sc with hveqTI
        cases hrepTI_sc with
        | induct hvTI_sc _ _ =>
          simp only [Value.construct.injEq, List.cons.injEq, and_true] at hveqTI
          obtain ⟨_, _, rfl, rfl, -, -, -, -, -, -⟩ := hveqTI
          have htagInd_lvls : famTag.cvS.levelParams.length = bnl :=
            nat_eq_of_field_eq_u56_p (by have := hvTI_sc.2.1; omega) (by omega)
              (Value.field.inj (hvTI_sc.1.symm.trans htlnlEq))
          have htltyTm : Tm (Core.keyOf P.t) 0 zeroGhost m_tlnc 0
              (Core.posOf famTag.cvS.levelParams famTag.cvS.type) x_tlty :=
            P.rekey_tm (hvTI_sc.2.2.2 0 zeroGhost)
          have ext_plvls_ciTI :=
            (ext_plvls_sp2.trans ext_sp2_tcpeq).trans
              (evCiTC.heap_extends.trans (ext_ciTC_riz.trans evCiTI.heap_extends))
          rw [htlnpEq] at evTsn1
          obtain ⟨tagSortBs, tagSortU, htagInd_sort, htagInd_nz⟩ :=
            type_sort_never_tm nP (by omega)
              (P.hbdSub (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])))
              htltyTm (hplvlsRep.mono ext_plvls_ciTI) evTsn1
          -- 3. Aux inductive (`aAux`)
          have ext_sp1_tsn1 :=
            ((ext_sp1_auxpeq.trans (evSp2.heap_extends.trans ext_sp2_tcpeq)).trans
              (evCiTC.heap_extends.trans (ext_ciTC_riz.trans evCiTI.heap_extends))).trans evTsn1.heap_extends
          have haAux_tsn1 := Bytes.repAddressRef_heapMono₂ addrTy ext_sp1_tsn1 haAux
          have hsubCiAux : ∀ cl ∈ cs_ciAux, cl ∈ P.calls := fun cl hcl => hsub cl (by rw [hc]; simp [hcl])
          obtain ⟨ciAux, hfindAux, vAux, hldAux', hrepAux⟩ :=
            P.getCI_of_stored hstAux haAux_tsn1 evCiAux hsubCiAux
          rw [ldCiAux] at hldAux'; injection hldAux' with hveqAux
          cases hrepAux with
          | @induct _ _ _ _ _ _ _ _ cvAux capsAux hvAux hcntAux hkeyAux =>
            simp only [Value.construct.injEq, List.cons.injEq, and_true] at hveqAux
            obtain ⟨_, _, rfl, rfl, rfl, rfl, rfl, -, rfl, rfl⟩ := hveqAux
            obtain ⟨anpN, aniN, ancN, hanpF, haniF, hancF, hanp56, hani56, hanc56⟩ := hcntAux
            have hauxInd_lvls : cvAux.levelParams.length = bnl :=
              nat_eq_of_field_eq_u56_p (by have := hvAux.2.1; omega) (by omega)
                (Value.field.inj (hvAux.1.symm.trans hanlEq))
            have hanp_eq : anpN = nP :=
              nat_eq_of_field_eq_u56_p hanp56 hnP (Value.field.inj (hanpF.symm.trans hanpEq))
            have hani_eq : aniN = 1 :=
              nat_eq_of_field_eq_u56_p hani56 (by omega) (by simpa using Value.field.inj haniF.symm)
            subst anpN aniN
            -- Record & block of `aAux` via `loads.inductRecord`, `inductBlock`, `indRecord`
            obtain ⟨-, hneAux⟩ := P.sc_kappa_eq_of_isSome hstAux
            obtain ⟨cmAux, bAux, idxAux, hrecCmAux, hbAux_rep, hidxAux, hinfoAux⟩ :=
              P.hSE.prefixInv.loads.inductRecord x_aux_addr p_ciAux m_tsn1 m_ciAux cs_ciAux aAux
                x_anl x_aty x_anp (.field 1) x_anc _ x_aux_blk (.field 0)
                evCiAux trivial hneAux (P.hgoodSub hsubCiAux) haAux_tsn1 ldCiAux
            have hidxAux0 : idxAux = 0 := Value.field.inj hidxAux.symm
            subst hidxAux0
            obtain ⟨cbAux, msAux, indAux, hrecCbAux, hmutsAux, hms0Aux⟩ :=
              P.hSE.prefixInv.loads.inductBlock x_aux_addr p_ciAux m_tsn1 m_ciAux cs_ciAux aAux bAux
                x_anl x_aty x_anp (.field 1) x_anc _ x_aux_blk (0 : F)
                evCiAux trivial hneAux (P.hgoodSub hsubCiAux) haAux_tsn1 ldCiAux hbAux_rep
            obtain ⟨_, _, _, _, _, hldIndAux, -, -, -, hanc56_ind⟩ :=
              P.hSE.prefixInv.loads.indRecord x_aux_addr p_ciAux m_tsn1 m_ciAux cs_ciAux aAux
                cmAux cbAux ⟨(0 : Nat).toUInt64, ixAddr bAux⟩ msAux indAux
                evCiAux (P.hgoodSub hsubCiAux) haAux_tsn1 hrecCmAux
                (by simpa [ZMod.val_zero] using hinfoAux) hrecCbAux hmutsAux
                (by simpa [ZMod.val_zero] using hms0Aux)
            rw [ldCiAux] at hldIndAux; injection hldIndAux with hldIndAux
            simp only [Value.construct.injEq, List.cons.injEq, and_true] at hldIndAux
            obtain ⟨_, _, -, -, hanpInd, haniInd, hancInd, -, -, -⟩ := hldIndAux
            have haux_nat : NativeAt P.E (ixAddr bAux) :=
              P.nativeAt_of_block_is_modeled_zero hbAux_rep evAuxMod
                (fun cl hcl => hsub cl (by rw [hc]; simp [hcl]))
            -- `type_sort_never` on `x_aty` with `nP + 1`
            rw [hanpEq] at opNp1b
            have hnp1b_eq : v_np1b = .field ((nP + 1 : Nat) : F) := by
              rw [evalBinOp_add_field_p opNp1b]; push_cast; rfl
            rw [hnp1b_eq] at evTsn2
            have hatyTm : Tm (Core.keyOf P.t) 0 zeroGhost m_auxmod 0
                (Core.posOf cvAux.levelParams cvAux.type) x_aty :=
              (P.rekey_tm (hvAux.2.2.2 0 zeroGhost)).mono evAuxMod.heap_extends
            have ext_plvls_auxmod : Heap.Extends m_plvls m_auxmod :=
              ((ext_plvls_ciTI.trans evTsn1.heap_extends).trans evCiAux.heap_extends).trans evAuxMod.heap_extends
            obtain ⟨auxSortBs, auxSortU, hauxInd_sort, hauxInd_nz⟩ :=
              type_sort_never_tm (nP + 1) (by omega)
                (P.hbdSub (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])))
                hatyTm (hplvlsRep.mono ext_plvls_auxmod) evTsn2
            have hauxSortU_pos : ∀ φ, auxSortU.eval φ > 0 := by
              intro φ
              have hdefT := (P.hwf _ (Ix.Kernel.Semantics.Env.find?_mem hfindAux)).2.1
              have hdefPos := allLevelParamsDefined_posOf cvAux.type hdefT
              simp only [ConstantInfo.toConstantVal] at hdefPos
              rw [hauxInd_lvls] at hdefPos
              have hdefU := allLevelParamsDefined_stripPis_sort hdefPos hauxInd_sort
              rw [← substLevel_range_eval hdefU φ]
              exact hauxInd_nz φ
            have hnotResAux : Ix.Kernel.reservedBasisNames.contains (Core.keyOf P.t (ixAddr aAux)) = false := by
              obtain ⟨G, R, envT, hshape, hextT⟩ := P.hSE.shape
              exact not_reserved_ind_of_neverZero_arity hshape hextT P.hSE.nodup
                hfindAux (Nat.succ_pos nP) hauxInd_sort hauxSortU_pos
            let auxIndWit : NativeIndWitness P.t P.E P.env (Core.keyOf P.t (ixAddr aAux)) :=
              { addr := ixAddr aAux
                cm := cmAux
                ip := ⟨(0 : Nat).toUInt64, ixAddr bAux⟩
                cv := cvAux
                caps := capsAux
                hkey := rfl
                hfind := hfindAux
                hnotRes := hnotResAux
                hrec := hrecCmAux
                hinfo := by simpa [ZMod.val_zero] using hinfoAux
                hnat := haux_nat }
            -- `hauxCtorStored` + `indAux` parameter/index/ctor counts from `P.hreg.at_parent`
            obtain ⟨famAux, hRegAux, hreadAux⟩ := P.hreg.at_parent P.ht
              auxIndWit.hfind auxIndWit.hnotRes auxIndWit.hrec auxIndWit.hinfo auxIndWit.hnat
            have hfamAux_rec := (P.hreg.fams famAux hRegAux).record
            obtain ⟨P', cm', ip', cb', ms', ind', hname', hrecP', hinfoP', hrecB', hmuts', hms',
              hnp', hni', hlenA', hckeys', _, _⟩ := hfamAux_rec
            have hPeq : P' = ixAddr aAux := Core.keyOf_inj P.htwf (hname'.symm.trans hreadAux.2.1)
            subst P'
            have hcmEq : cm' = cmAux := Option.some.inj (hrecP'.symm.trans hrecCmAux)
            subst cm'
            have hipEq : ip' = ⟨(0 : Nat).toUInt64, ixAddr bAux⟩ :=
              Ixon.ConstantInfo.iPrj.inj (hinfoP'.symm.trans auxIndWit.hinfo)
            subst ip'
            have hcbEq : cb' = cbAux := Option.some.inj (hrecB'.symm.trans hrecCbAux)
            subst cb'
            rw [hmutsAux] at hmuts'; obtain rfl := Ixon.ConstantInfo.muts.inj hmuts'
            simp only [ZMod.val_zero] at hms0Aux
            change msAux[0]? = some (Ixon.MutConst.indc ind') at hms'
            rw [hms0Aux] at hms'; obtain rfl := Ixon.MutConst.indc.inj (Option.some.inj hms')
            have haux_bounds : indAux.params.toNat < 72057594037927936 ∧
                indAux.indices.toNat < 72057594037927936 := by
              obtain ⟨_, rawA, cmA, _, hhA, haA, hexA, -, -, -, hresA⟩ :=
                Ingress.get_ci_spec (P.hbdSub hsubCiAux) haAux_tsn1 evCiAux
              have hcmA_eq : cmA = cmAux := by
                have hrecA : Ix.Cert.recordAt P.E (ixAddr aAux) = some cmAux := hrecCmAux
                unfold Ix.Cert.recordAt at hrecA
                cases hgetA : P.E.consts.get? (ixAddr aAux) with
                | none => rw [hgetA] at hrecA; cases hrecA
                | some lcA =>
                  rw [hgetA, Option.bind_some] at hrecA
                  obtain ⟨_, hvalA, hexA₀⟩ := P.hSE.store.decoded (ixAddr aAux) lcA hgetA
                  have hesc := Core.load_escape hgetA (P.hgoodSub hsubCiAux).1 rawA hhA haA
                  rw [hesc, hexA₀] at hexA
                  exact (Except.ok.inj hexA).symm.trans (Option.some.inj (hvalA.symm.trans hrecA))
              subst cmA
              unfold Ingress.GetCIRawResult at hresA
              rw [auxIndWit.hinfo] at hresA
              obtain ⟨-, blkBytes, cbA, xsA, indA, _, hhB, haB, hexB, -, hmutsA, hmsA, -, hrawA⟩ := hresA
              have hcbA_eq : cbA = cbAux := by
                have hrecB : Ix.Cert.recordAt P.E (ixAddr bAux) = some cbAux := hrecCbAux
                unfold Ix.Cert.recordAt at hrecB
                cases hgetB : P.E.consts.get? (ixAddr bAux) with
                | none => rw [hgetB] at hrecB; cases hrecB
                | some lcB =>
                  rw [hgetB, Option.bind_some] at hrecB
                  obtain ⟨_, hvalB, hexB₀⟩ := P.hSE.store.decoded (ixAddr bAux) lcB hgetB
                  have hesc := Core.load_escape hgetB (P.hgoodSub hsubCiAux).1 blkBytes hhB haB
                  rw [hesc, hexB₀] at hexB
                  exact (Except.ok.inj hexB).symm.trans (Option.some.inj (hvalB.symm.trans hrecB))
              subst cbA
              rw [hmutsAux] at hmutsA; obtain rfl := Ixon.ConstantInfo.muts.inj hmutsA
              rw [Array.getElem?_toList] at hmsA
              change msAux[0]? = some (Ixon.MutConst.indc indA) at hmsA
              rw [hms0Aux] at hmsA; obtain rfl := Ixon.MutConst.indc.inj (Option.some.inj hmsA)
              exact ⟨hrawA.2.1, hrawA.2.2.1⟩
            have haux_np_ind : indAux.params.toNat = nP :=
              nat_eq_of_field_eq_u56_p haux_bounds.1 hnP (Value.field.inj (hanpInd.symm.trans hanpEq))
            have haux_ni_ind : indAux.indices.toNat = 1 :=
              nat_eq_of_field_eq_u56_p haux_bounds.2 (by omega) (by simpa using Value.field.inj haniInd.symm)
            have haux_nc_ind : indAux.ctors.size = ancN :=
              nat_eq_of_field_eq_u56_p hanc56_ind hanc56 (Value.field.inj (hancInd.symm.trans hancF))
            have hauxCtorStored : ∀ k < ancN, ∃ cv knf,
                P.env.find? (Core.keyOf P.t (Core.cprjAddr (ixAddr bAux) 0 k)) = some (.ctorInfo cv nP knf) := by
              intro k hk
              have hk_lt : k < famAux.ctorsA.length := by omega
              let cA := famAux.ctorsA[k]'hk_lt
              have hcA : famAux.ctorsA[k]? = some cA := List.getElem?_eq_getElem hk_lt
              have hfindCA := ((P.hreg.fams famAux hRegAux).stored.ctor k cA hcA).1
              have hkeyCA := hckeys' k cA hcA
              change cA.1.name = Core.keyOf P.t (Core.cprjAddr (ixAddr bAux) 0 k) at hkeyCA
              rw [hkeyCA, hnp', haux_np_ind] at hfindCA
              exact ⟨cA.1, cA.2, hfindCA⟩
            -- `hfamAux` via `ScopedCtx.famAt_of_ind`
            have hfamAux : P.sc.FamAt (ixAddr bAux) 0 := by
              obtain ⟨bAux', iAux', hbAux'rep, hiAux'eq, hnameAux'⟩ := hkeyAux
              have hbAux'_eq : bAux' = bAux := addr_det hbAux'rep hbAux_rep
              have hiAux'_eq : iAux' = 0 := Value.field.inj hiAux'eq.symm
              rw [hbAux'_eq, hiAux'_eq] at hnameAux'
              obtain ⟨hκAux, -⟩ := P.sc_kappa_eq_of_isSome hstAux
              have h1 := ScopedCtx.famAt_of_ind (a := ixAddr aAux) (b := ixAddr bAux)
                (i := ZMod.val (0 : F)) (by rw [hκAux]; exact hfindAux) hnameAux'
              rwa [ZMod.val_zero] at h1
            -- 4. `find_aux_ctor_for_tag`
            have htagC_key_f : Core.keyOf P.t (ixAddr aTagC) =
                P.sc.κ (Core.cprjAddr (ixAddr bTag) 0 (ZMod.val (ctTag.cidx.toNat : F))) := by
              have h1 : cvTC.name = Core.keyOf P.t (ixAddr aTagC) :=
                Ix.Kernel.Semantics.Env.find?_name hfindTC
              have h2 : jTC' = (ctTag.cidx.toNat : F) := Value.field.inj (hjTC'eq.symm.trans hcidxTag)
              rw [← h1, hnameTC', ZMod.val_zero, h2]
            have ext_ciAux_tsn2 : Heap.Extends m_ciAux m_tsn2 :=
              evAuxMod.heap_extends.trans evTsn2.heap_extends
            have ext_ciTC_tsn2 : Heap.Extends m_ciTC m_tsn2 :=
              ((ext_ciTC_riz.trans evCiTI.heap_extends).trans
                (evTsn1.heap_extends.trans evCiAux.heap_extends)).trans ext_ciAux_tsn2
            rw [hancF, hcidxTag] at evFind
            obtain ⟨jIdx, hv_jidx, hjIdx_lt, hauxCtors⟩ :=
              find_aux_ctor_for_tag_spec P hanc56 hnP hbnl hnF rfl rfl rfl hfamAux hauxCtorStored
                tagCWit rfl rfl htagC_key_f
                ⟨cbTag, xsTag, indTag, ctTag, hrecCbTag, hmutsTag,
                  hxsTag, htag_gt1, hctTag, rfl⟩
                htag_nat htagInd_neNat
                (Bytes.repAddressRef_heapMono₂ addrTy ext_ciAux_tsn2 hbAux_rep)
                (Bytes.repAddressRef_heapMono₂ addrTy (evCiAux.heap_extends.trans ext_ciAux_tsn2) haAux_tsn1)
                (Bytes.repAddressRef_heapMono₂ addrTy ext_ciTC_tsn2 hbTag_rep)
                (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) evFind
            subst hv_jidx
            -- 5. `check_proj_pure_sort_poly`
            have hauxCtorJ : ∃ cv, P.env.find? (Core.keyOf P.t (Core.cprjAddr (ixAddr bAux) 0 jIdx)) =
                some (.ctorInfo cv nP nF) := by
              obtain ⟨w, hwKey, hwEq, _⟩ := hauxCtors jIdx hjIdx_lt
              obtain ⟨_, hknf⟩ := hwEq rfl
              exact ⟨w.cv, by rw [← hwKey, ← hknf]; exact w.hfind⟩
            have ext_h_find : Heap.Extends h m_find :=
              ((evPlvls.heap_extends.trans ext_plvls_auxmod).trans evTsn2.heap_extends).trans evFind.heap_extends
            have ext_ciAux_find : Heap.Extends m_ciAux m_find := ext_ciAux_tsn2.trans evFind.heap_extends
            have hsort_poly := check_proj_pure_sort_poly_spec P hnP (by omega) (by omega) rfl hfamAux
              hauxCtorJ hsbl_nz_spec
              (Bytes.repAddressRef_heapMono₂ addrTy ext_ciAux_find hbAux_rep)
              (hctyTm.mono ext_h_find) (hrawTm.mono ext_h_find)
              (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) evPoly
            -- 6. `check_proj_pure_body`
            have ext_h_poly : Heap.Extends h m_poly := ext_h_find.trans evPoly.heap_extends
            have ext_ciAux_poly : Heap.Extends m_ciAux m_poly := ext_ciAux_find.trans evPoly.heap_extends
            have ext_sp1_poly :=
              ((ext_sp1_tsn1.trans evCiAux.heap_extends).trans ext_ciAux_poly)
            have ext_sp2_poly :=
              ((ext_sp2_tcpeq.trans evCiTC.heap_extends).trans ext_ciTC_tsn2).trans
                (evFind.heap_extends.trans evPoly.heap_extends)
            rw [hancF] at evBody
            obtain ⟨auxRecKey, cvAuxRec, arules, hfindAuxRec, hAuxRec_lvls, hAuxRec_perm,
              hrecCtor, hauxRec_famBlk, ⟨majBs, majDom, majBody, majBm, majLvls, majArgs,
                hAuxRec_maj, hmajDom, hmajLvls, hmajArgs_len, hmajArgs_pref, hmajArgs_idx⟩,
              hbody⟩ :=
              check_proj_pure_body_spec P hnP hbnl hanc56 hnF hfidx hjIdx_lt rfl rfl rfl
                hfamAux auxIndWit rfl rfl hauxCtorStored
                (hpvalTm.mono ext_h_poly) hpvalCr
                (Bytes.repAddressRef_heapMono₂ addrTy ext_ciAux_poly hbAux_rep)
                (Bytes.repAddressRef_heapMono₂ addrTy ext_sp1_poly haAux)
                (Bytes.repAddressRef_heapMono₂ addrTy ext_sp2_poly haTagC)
                (hrepSbl.mono ext_h_poly) hsbl_nz_spec
                (AddrMapAll.mono (fun _ _ _ _ _ x => x) ext_h_poly haset)
                (fun cl hcl => hsub cl (by rw [hc]; simp [hcl])) evBody
            exact ⟨{
              cvmT := cvmT
              mvalT := mvalT
              hintT := hintT
              hTM_nonAux := hTM_nonAux
              hfindTM := hfindTM
              hTM_lvls := hTM_lvls
              hTM_perm := hTM_perm
              auxKey := Core.keyOf P.t (ixAddr aAux)
              tagKey := Core.keyOf P.t (Core.iprjAddr (ixAddr bTag) 0)
              tagCKey := Core.keyOf P.t (ixAddr aTagC)
              tagCidx := ZMod.val jTag
              tmbs := tmbs
              auxLvls := auxLvls
              auxArgs := auxArgs
              tcLvls := tcLvls
              tcArgs := tcArgs
              hTM_strip := htmbodyEq ▸ hTM_strip
              hTM_pw := fun bm hbm => by simpa [Ix.Kernel.Level.zeronessOf] using hTM_pw0 bm hbm
              hauxLvls := hauxLvls_rel
              hauxArgs_len := hauxArgs_len
              hauxArgs_pref := hauxArgs_pref
              hauxArgs_tag := htagEq ▸ hauxArgs_tag_get
              htcLvls := htcLvls_rel
              htcArgs := htcArgs_eq
              tagCWit := tagCWit
              htagC_lvls := htc_lvls
              htagC_nP := rfl
              htagC_nF := rfl
              tagIndWit := tagIndWit
              htagInd_lvls := htagInd_lvls
              htagInd_neNat := htagInd_neNat
              htagInd_idx := rfl
              htagInd_rec := ⟨cbTag, xsTag, indTag, hrecCbTag, hmutsTag,
                by simpa [ZMod.val_zero] using hxsTag, htag_nP, htag_nI, htag_gt1⟩
              tagSortBs := tagSortBs
              tagSortU := tagSortU
              htagInd_sort := htagInd_sort
              htagInd_nz := htagInd_nz
              auxIndWit := auxIndWit
              hauxInd_lvls := hauxInd_lvls
              hauxInd_idx := rfl
              auxSortBs := auxSortBs
              auxSortU := auxSortU
              hauxInd_sort := hauxInd_sort
              hauxInd_nz := hauxInd_nz
              anc := ancN
              hauxInd_rec := ⟨cbAux, msAux, indAux, hrecCbAux, hmutsAux,
                by simpa [ZMod.val_zero] using hms0Aux, haux_np_ind, haux_ni_ind, haux_nc_ind⟩
              jIdx := jIdx
              hjIdx_lt := hjIdx_lt
              auxCtorKeyAt := fun k => Core.keyOf P.t (Core.cprjAddr (ixAddr bAux) 0 k)
              hauxCtorKeyAt := fun _ => rfl
              hauxCtors := hauxCtors
              auxRecKey := auxRecKey
              cvAuxRec := cvAuxRec
              arules := arules
              hfindAuxRec := hfindAuxRec
              hAuxRec_lvls := hAuxRec_lvls
              hAuxRec_perm := hAuxRec_perm
              hrecCtor := hrecCtor
              hauxRec_famBlk := hauxRec_famBlk
              majBs := majBs
              majDom := majDom
              majBody := majBody
              majBm := majBm
              majLvls := majLvls
              majArgs := majArgs
              hAuxRec_maj := hAuxRec_maj
              hmajDom := hmajDom
              hmajLvls := hmajLvls
              hmajArgs_len := hmajArgs_len
              hmajArgs_pref := hmajArgs_pref
              hmajArgs_idx := hmajArgs_idx
              hsort_poly := hsort_poly
              hbody := hbody }⟩
          | _ => simp [kciEnum] at hveqAux
        | _ => simp [kciEnum] at hveqTI
    | _ => simp [kciEnum] at hveqTC

end IxVM.Refinement.Typing.FamilyAlias


