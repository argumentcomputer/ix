import IxVMRefinement.Assembly.TypingRecLateArm

/-! # The parent read at a recursor record is the record's

`recParent_of_arm` reads a parent family off the circuit's route, but its conclusion (`RecParent`)
does not say whose parent it is: `RecParent t E env P ip` holds of every stored, non-basis former
of a native block. The late step's relation is about the recursor's own family, so the second
interface must receive the parent the route read, not any registered family.

* `RecMajorTie`: the key heading the major premise's domain, in an annotation of the reading of
  the record's type, is the parent's key;
* `recParent_of_route_tied`, `recParent_of_arm_tied`: the route gives the parent with that tie
  (the route's scan returns the head of the major premise's domain of the represented type);
* `unitStep_recLate_of_tied`: `unitStep_recLate_of` with a predicate `Q` on the parent, produced
  with it and handed to the second interface.
-/

universe u

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal)

/-- **The parent `P` is the recursor's**: an annotation of the reading of the record's type
(positional level parameters, over the run's blobs) has the parent's key at the head of the
major premise's domain. -/
def RecMajorTie (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env) (A : _root_.Address)
    (c : Ixon.Constant) (rc : Ixon.Recursor) (P : _root_.Address) : Prop :=
  ∃ tyP E' : Ix.Kernel.Expr .anon,
    (exprReader t (fun x => E₀.blobs.get? x) c id (soloSelf t A)).read rc.typ = .ok tyP ∧
    Annotates E' tyP ∧ majorKey rc E' = some (keyOf t P)

/-- **`recParent_of_route`, with the head it read**: the parent's key heads the domain of the
binder the route's scan reached in the represented type. -/
theorem recParent_of_route_tied {E : Ixon.Env} {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    {env : Ix.Kernel.Env .anon} (hinv : Decl.PrefixInv.{u} E t lim env)
    {calls cs₁ cs₂ cs₃ : List (Call F)}
    (hgood : Core.Good ⟨E, env, t, lim⟩ calls)
    {ty parent ptr nl pty np ni nc pu blk idx : SourceValue F} {p m mi i : F}
    {h₁ h₂ h₃ h₄ : Heap F} {T : Core.KExpr}
    (hT : Core.TmC (Core.Ctx.stored ⟨E, env, t, lim⟩).κ h₁ T ty)
    (ev₁ : ObsFn Core.W "KernelCheck::rec_to_parent_addr"
      [ty, .field p, .field m, .field mi, .field i] h₁ parent h₂ cs₁)
    (hs₁ : ∀ x ∈ cs₁, x ∈ calls)
    (ev₂ : ObsFn Core.W "Ingress::get_ci" [parent] h₂ ptr h₃ cs₂)
    (hs₂ : ∀ x ∈ cs₂, x ∈ calls)
    (hld : loadValue h₃ ptr = .ok (.construct Core.kciEnum "Induct"
      [nl, pty, np, ni, nc, pu, blk, idx]))
    (ev₃ : ObsFn Core.W "KernelModeled::block_is_modeled" [blk] h₃ (.field 0) h₄ cs₃)
    (hs₃ : ∀ x ∈ cs₃, x ∈ calls)
    (hres : ∀ (dom : Core.KExpr) (k : Core.KKey) (us : List Core.KLevel),
      Core.piDomAt (ZMod.val (p + m + mi + i)) T = some dom → dom.getAppFn = .const k us →
      Ix.Kernel.reservedBasisNames.contains k = false) :
    ∃ P ip, RecParent t E env P ip ∧ ∃ (dom : Core.KExpr) (us : List Core.KLevel),
      Core.piDomAt (ZMod.val (p + m + mi + i)) T = some dom ∧
      dom.getAppFn = .const (keyOf t P) us := by
  let c : Core.ScopedCtx := Core.Ctx.stored ⟨E, env, t, lim⟩
  have hc : Core.ScopedCoreFacts c := hinv.scopedCoreFacts
  have hspec := Decl.scopedCalleesSpec c hc .rec_to_parent_addr _ _ _ _ _ ev₁
  obtain ⟨a, dom, us, ha, hpi, hhead⟩ := hspec ty p m mi i rfl
    (Core.CoreGood.ofRaw (hgood.sub hs₁) (fun _ _ => trivial)) T hT
  have hkr : Core.KeysResolved T := (hT 0 (fun _ => .sort .zero)).keysResolved
  have hne : c.κ (Core.ixAddr a) ≠ Core.unresolvedKey :=
    keysResolved_getAppFn (keysResolved_piDomAt _ hkr hpi) hhead
  obtain ⟨ci, hfci, hrep⟩ := hinv.loads.getCI parent ptr h₂ h₃ cs₂ a ev₂ trivial hne
    (Core.CoreGood.ofRaw (hgood.sub hs₂) (fun _ _ => trivial)) ha
  obtain ⟨v, hv, hcir⟩ := hrep
  rw [hld] at hv
  obtain rfl := (Except.ok.inj hv).symm
  obtain ⟨cv, caps, _, _, _, rfl, -⟩ := Core.WhnfAux.ind_inv hcir
  have hkey : c.κ (Core.ixAddr a) = Core.keyOf t (Core.ixAddr a) := c.key_eq hne
  have hr := hres dom _ us hpi hhead
  have hhead' := hhead
  rw [hkey] at hfci hr hhead'
  obtain ⟨cm, b, i', hcm, hb, -, hinfo⟩ := hinv.loads.inductRecord parent ptr h₂ h₃ cs₂ a nl pty
    np ni nc pu blk idx ev₂ trivial hne (hgood.sub hs₂) ha hld
  refine ⟨Core.ixAddr a, ⟨(ZMod.val i').toUInt64, Core.ixAddr b⟩,
    ⟨⟨cv, caps, hfci⟩, hr, ⟨cm, hcm, hinfo⟩, ?_⟩, dom, us, hpi, hhead'⟩
  exact nativeAt_of_route (c := ⟨E, env, t, lim⟩) ev₃ hs₃ hgood hb

/-- **`recParent_of_arm`, with the tie**: the parent the circuit read is the recursor's, its key
heading the major premise's domain of the annotation of the record's type the route scanned. -/
theorem recParent_of_arm_tied {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E : Ixon.Env} {envT : Ix.Kernel.Env .anon} {lim : Option Nat}
    {bAddr A : _root_.Address} {c : Ixon.Constant} {rc : Ixon.Recursor} {n : Nat}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .recr rc) (hlim : lim = some n)
    (hnat : NativeRecArm calls bAddr t A n) (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c)
    (hres : RecMajorNotBasis t E₀ A c rc)
    (env : Ix.Kernel.Env .anon) (hstep : StepAt.{u} t envT E₀ E lim A c env) :
    ∃ P ip, RecParent t E env P ip ∧ RecMajorTie t E₀ A c rc P := by
  subst hlim
  have hgood : Core.Good ⟨E, env, t, some n⟩ calls := hst.good env (some n)
  have hbound : Bounded calls := hgood.2
  have hrec₀ : Ix.Cert.recordAt E₀ A = some c := (hS.recordOf_eq_recordAt A).symm.trans hc
  have hstored : Decl.UsedRefsStored t env c :=
    usedRefsStored_of_cover (hcover env ⟨hstep.ext, hstep.refs, hstep.fresh⟩) hinert
  obtain ⟨h_pre, m_chk, h'_chk, rcv, ap, ptr, r_chk, levels, type, parameters, indices, motives,
    minors, rules, kf, uns, block, position, cs_load, cs_chk, -, -, ha_pre, -, ev_ld, hsub_ld,
    hld, ev_chk, hsub_chk⟩ := hnat
  obtain ⟨a', ha'_ref, haA⟩ := ha_pre
  subst haA
  obtain ⟨rawBytes, c', hh, hba, hex, -, hres'⟩ :=
    L1.get_ci_block_trace_spec (hgood.sub hsub_ld).2 ha'_ref ev_ld
  have hcc : c' = c := hS.record_eq hrec₀ (Core.hashed_mono hsub_ld hh) hba hex
  subst c'
  unfold L1.GetCIBlockTraceResult at hres'
  rw [hinfo] at hres'
  obtain ⟨blobs, tree, v, hhp, built, hldv, htr⟩ := hres'
  rw [hld] at hldv
  obtain ⟨hlvls, hp56, hi56, hm56, hmi56, -, tyPtr, rulesPtr, blkPtr, b, planT, -, -, hv, rty,
    -, -, -⟩ := htr
  subst hv
  injection hldv with hv'
  injection hv' with _ _ hfields
  simp only [List.cons.injEq, and_true] at hfields
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, -, -, -, -, -⟩ := hfields
  have hblob : ∀ x bs, (x, bs) ∈ blobs → E₀.blobs.get? x = some bs := by
    intro x bs hm
    obtain ⟨hhx, hxa⟩ := hhp (x, bs) hm
    have hhx' : Hashed cs_load bs := hhx
    have hxa' : Address.blake3Pure bs = x := hxa
    have hrun := hS.blobs bs (Core.hashed_mono hsub_ld hhx')
    rw [hxa'] at hrun
    exact hrun
  obtain ⟨tyP, htyP⟩ := LoadedReads.exprReader_read_ok (t := t)
    (blob := fun x => E₀.blobs.get? x) ht (param := id) (self := soloSelf t (Core.ixAddr a'))
    rty (fun i x hx => by simp at hx) hblob
  obtain ⟨sB, sA, mH, sR, sCs, mCs, hextS, evS, hmemS, hextM, evM, hsubM⟩ :=
    check_const_rec_route ev_chk
  obtain ⟨-, hlbb, hdef⟩ := Assembly.validate_expr_well_scoped_spec
    (cx := readCtx t (fun x => E₀.blobs.get? x)) (self := soloSelf t (Core.ixAddr a'))
    hbound hlvls rty hextS htyP evS (hsub_chk _ hmemS)
  have hrd : (Ix.Kernel.Reader.MemberReader.mk' (readCtx t (fun x => E₀.blobs.get? x)) c
      (Ix.Kernel.Reader.recParam (List.range rc.lvls.toNat))
      (soloSelf t (Core.ixAddr a'))).read rc.typ = .ok tyP := by
    rw [Assembly.recParam_range]
    exact htyP
  obtain ⟨E', hann, htm⟩ := rty.toTmC (κ := Core.keyOf t) (ps := List.range rc.lvls.toNat)
    (by simp) (by simpa using hlvls) (LoadedReads.readCtx_keyAt_inv ht _)
    (fun i x m k hx => by simp at hx) hblob hrd hlbb hdef
  have htmS := Decl.tmC_stored_of_usedRefs (E₀ := E) (env := env) (lim := some n) rty
    (recr_typ_usedRefs hinfo) hstored htm
  rw [Decl.posOf_range] at htmS
  obtain ⟨parent, pointer, scanHeap, loadedHeap, routedHeap, scanCalls, loadCalls, routeCalls,
    nl, pty, np, ni, nc, pu, blk, idx, evScan, hsScan, evLoad, hsLoad, hldP, evRoute, hsRoute⟩ :=
    native_rec_route_calls evM
  have hsum : ZMod.val ((rc.params.toNat : F) + (rc.motives.toNat : F) + (rc.minors.toNat : F) +
      (rc.indices.toNat : F)) =
      rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat := by
    rw [← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add]
    exact ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  obtain ⟨P, ip, hpar, dom, us, hpi, hhead⟩ := recParent_of_route_tied hstep.inv hgood
    (htmS.mono hextM) evScan
    (fun x hx => hsub_chk x (hsubM x (hsScan x hx))) evLoad
    (fun x hx => hsub_chk x (hsubM x (hsLoad x hx))) hldP evRoute
    (fun x hx => hsub_chk x (hsubM x (hsRoute x hx)))
    (fun dom k us hpi hhead => hres tyP E' k htyP hann
      (majorKey_of_piDomAt (by rw [← hsum]; exact hpi) hhead))
  exact ⟨P, ip, hpar, tyP, E', htyP, hann,
    majorKey_of_piDomAt (by rw [← hsum]; exact hpi) hhead⟩

/-- **`unitStep_recLate_of` with a predicate on the parent**: the first interface produces the
parent with `Q`, the second receives it. With `Q := RecMajorTie t E₀ A c rc` the second
interface is about the recursor's own family. -/
theorem unitStep_recLate_of_tied {t : Ix.Kernel.RoleTable} {E₀ E : Ixon.Env}
    {envT : Ix.Kernel.Env .anon} {lim : Option Nat} {A : _root_.Address} {c : Ixon.Constant}
    {rc : Ixon.Recursor} (Q : _root_.Address → Prop)
    (ht : t.check = .ok ()) (hinfo : c.info = .recr rc)
    (hparent : ∀ env, StepAt.{u} t envT E₀ E lim A c env →
      ∃ P ip, RecParent t E env P ip ∧ Q P)
    (hout : ∀ env P ip fam, StepAt.{u} t envT E₀ E lim A c env → RecParent t E env P ip →
      Q P → MatchedAt t E env P ip fam → RecLateOut t E₀ E A env fam) :
    UnitStep.{u} (LateRegistry.{u} t E) t envT E₀ E lim A c := by
  intro env hext hnd hinv hX href hfresh
  have hstep : StepAt.{u} t envT E₀ E lim A c env := ⟨hext, hnd, hinv, href, hfresh⟩
  obtain ⟨Reg, hR⟩ := hX
  obtain ⟨P, ip, hpar, hQ⟩ := hparent env hstep
  obtain ⟨⟨cvP, capsP, hfP⟩, hres, ⟨cm, hcm, hcmi⟩, hnat⟩ := hpar
  obtain ⟨fam, hReg, hat, hnameP, hmatch⟩ := hR.at_parent ht hfP hres hcm hcmi hnat
  obtain ⟨cvR, mI, rP, rules, cn, ci₀, hrun, hname, hreads, hstored, hreload⟩ :=
    hout env P ip fam hstep ⟨⟨cvP, capsP, hfP⟩, hres, ⟨cm, hcm, hcmi⟩, hnat⟩ hQ
      ⟨hat, hnameP, hmatch⟩
  have hcomp := late_companions ht hinv.companions ⟨hat, hnameP, hmatch⟩ hcm hcmi hrun
  obtain ⟨hinv', hR'⟩ := late_prefixInv_step hinv hR hReg hrun
    (hname.trans (LoadedReads.keyOf_eq t A).symm) hcomp hreload
  obtain ⟨hfreshN, -, -, -⟩ := late_head hrun
  have hown : ConstAddrOf A c A := Or.inl ⟨rfl, Or.inr (Or.inl ⟨rc, hinfo⟩)⟩
  refine ⟨[cn], List.nodup_singleton _, ?_, hinv', ⟨Reg, hR'⟩, ?_, ?_⟩
  · intro ci hci
    obtain rfl := List.mem_singleton.mp hci
    exact hfreshN
  · intro x hx
    rcases hx with ⟨hxA, -⟩ | ⟨ms, i, m, hms, -, -⟩
    · rw [hxA]
      exact ⟨cn, List.mem_singleton_self _, ci₀, hname, hreads, hstored⟩
    · have h := hinfo.symm.trans hms
      cases h
  · intro ci hci
    obtain rfl := List.mem_singleton.mp hci
    exact Or.inl ⟨A, hown, hname⟩

end IxVM.Refinement.Typing
