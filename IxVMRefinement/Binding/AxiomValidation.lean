import IxVMRefinement.Binding.ShapeAnchors
import IxVMRefinement.Binding.TermCells
import IxVMRefinement.RoleVal.AxiomRecordLim
import IxVMRefinement.Claim.RefSafety
import IxVMRefinement.Assembly.ProjSafe
import IxVMRefinement.Assembly.BareState
import IxVMRefinement.Assembly.NativeBlockReads
import IxVMRefinement.Assembly.NativeBlockRegister
import IxVMRefinement.StatementRel.ReadsMono

/-! # What a binding run's validation of a standard axiom gives the fold

`KernelRoles::validate_standard_axiom` (`KernelRoles.lean:926`) loads the record bound to
`propext` or `Classical.choice`, asserts it a safe axiom, checks its type well scoped and a sort
under the group's role context (`k_ensure_sort`), and pins it: `assert_type_pinned(ty,
role_type(tbl, r))`. This file proves `AxiomInstall.AxiomValidationFacts` from that, so the
residual's hypothesis `standardAxiomRoleUnit` has no premise left.

The type is checked against the closure's environment, under the keying of the prefix, which
resolves an address only where the environment stores its key. The pin decides which addresses
the loaded type names: `kexpr_struct_eq` compares cell by cell, so the loaded type's cells are
the cells of `role_type`'s term (`kexpr_struct_eq_cells`), and those are the addresses of the
roles the specified type names (`roleType_cells`): `Iff` and `Eq` for `propext`, `Nonempty` for
`choice`. Those roles are of earlier groups and stored (`TableShape.kept`, `preludeKept`). Every
other load of the record converts the same expression, so it has the same cells
(`RawConvExpr.cells_of_twin`); that gives the reload. No fact about the record's other
references (its sharing table may name records the type never reaches) is needed.

* `LoadedReads.get_ci_axio_canon_raw`: `get_ci_axio_canon_exact` with the load's value and its
  raw conversion.
* `stdNeeds`, `stdNamed`: the roles a standard axiom's specified type names.
* `axiomValidationFacts`: **the validation facts at every binding run**.
* `standardAxiomRoleUnit_closed`: **the residual's hypothesis `standardAxiomRoleUnit`, with no
  premise**.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.LoadedReads

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM (F)
open IxVM.Consistency

variable {t : Ix.Kernel.RoleTable}

/-- **`get_ci_axio_canon_exact`, with the load's value and its raw conversion**: a load of a
held axiom record, in calls that hash no collision with the store, returns an `Axiom` value
whose type pointer is a conversion of the record's type expression and represents the canonical
annotation of the read type exactly under the table's keying. -/
theorem get_ci_axio_canon_raw (ht : t.check = .ok ()) {E : Ixon.Env} {cs : List (Call F)}
    (hnc : ¬ View.HashedCollision { env := E } [] cs) {a : Aiur.Library.Bytes.Address}
    {addr ptr : SourceValue F} {h h' : Heap F}
    (ha : Aiur.Library.Bytes.RepAddressRef Core.addrTy h a addr)
    (ev : ObsFn Core.W "Ingress::get_ci" [addr] h ptr h' cs) {c : Ixon.Constant}
    {ax : Ixon.Axiom} (hrec : recordOf E (Core.ixAddr a) = some c)
    (hinfo : c.info = .axio ax) {ty₀ : Ix.Kernel.Expr .anon}
    (hty : (exprReader t (fun x => E.blobs.get? x) c id (fun _ => none)).read ax.typ = .ok ty₀)
    (hty_lbb : ty₀.looseBVarsBounded 0 = true)
    (hty_def : ty₀.allLevelParamsDefined (List.range ax.lvls.toNat) = true) :
    ∃ (ty' : Ix.Kernel.Expr .anon) (tyPtr : SourceValue F)
      (blobs : List (_root_.Address × ByteArray)),
      canonAnn c (List.range ax.lvls.toNat) 0 ax.typ ty₀ = some ty' ∧ Annotates ty' ty₀ ∧
      (∃ u, loadValue h' ptr =
        .ok (.construct Core.kciEnum "Axiom" [.field (ax.lvls.toNat : F), tyPtr, u])) ∧
      ax.lvls.toNat < 4294967296 ∧
      Ingress.RawConvExpr c.refs.toList [] c.univs.toList c.sharing.toList blobs h' 4294967295
        ax.typ tyPtr ∧
      Decl.TmCExact (Core.keyOf t) h' ty' tyPtr := by
  obtain ⟨rawBytes, c', hh, haddr, hex, hres⟩ := Ingress.get_ci_trace_spec ha ev
  obtain ⟨lc, hget, hdec⟩ := recordOf_inv hrec
  have hb : rawBytes = lc.rawBytes := Core.load_escape hget hnc rawBytes hh haddr
  have hc : c = c' := by
    rw [hb, hdec] at hex
    exact Except.ok.inj hex
  subst hc
  unfold Ingress.GetCITraceResult at hres
  rw [hinfo] at hres
  obtain ⟨blobs, tree, v, hhp, built, hld, htr⟩ := hres
  obtain ⟨hnlvls, tyPtr, plan, hv, rty, hp, hl⟩ := htr
  subst hv
  have hagree := blobReadAgreement_of_noCollision hnc hhp t
  obtain ⟨ty', hcT, hannT, htmT⟩ :=
    annotation_canon_exact (recurAddrs := []) ht hnlvls (fun _ _ _ _ hx => by simp at hx) hagree
      rty built hp hl hty hty_lbb hty_def
  rw [Decl.posOf_range] at htmT
  exact ⟨ty', tyPtr, blobs, hcT, hannT, ⟨_, hld⟩, hnlvls, rty, htmT⟩

end IxVM.Refinement.LoadedReads

namespace IxVM.Refinement.Binding

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Refinement.Core
open Ix.Kernel (Role)
open Ix.Kernel.Semantics (NativeFam)

/-! ## The roles a standard axiom's type names -/

/-- **The roles a standard axiom's specified type names**: `Iff` and `Eq` for `propext`,
`Nonempty` for `Classical.choice`. -/
def stdNeeds (r : Role) : List Role := if r = .propext then [.iff, .eq] else [.nonempty]

/-- A key is one of those roles' keys. -/
def stdNamed (r : Role) (k : KKey) : Bool :=
  (stdNeeds r).any fun r' => decide (k = Ix.Kernel.Key.role r')

set_option maxRecDepth 100000 in
private theorem std_named_all : IxVM.Consistency.standardAxioms.all (fun r =>
    (specTypeRaw r).all fun T₀ => T₀.constsResolveBy (stdNamed r)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The roles a standard axiom's type names are of earlier groups, and each is walked, a shape
anchor, or a prelude role. -/
private theorem std_needs_facts : ∀ r ∈ IxVM.Consistency.standardAxioms, ∀ r' ∈ stdNeeds r,
    Ix.SpecDigest.groupOf r' < Ix.SpecDigest.groupOf r ∧
      (IxVM.Consistency.walkedRole r' = true ∨ r' ∈ IxVM.Consistency.shapeAnchors ∨
        r' ∈ IxVM.Consistency.preludeRoles) := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem std_misc : ∀ r ∈ IxVM.Consistency.standardAxioms,
    Ix.Kernel.reservedBasisNames.contains (Ix.Kernel.Key.role r : KKey) = false ∧
      IxVM.Consistency.inertKey (Ix.Kernel.Key.role r) = false ∧
      (specLevels r).isSome = true ∧ (specTypeRaw r).isSome = true := by
  decide +kernel

theorem std_named {r : Role} (hr : r ∈ IxVM.Consistency.standardAxioms) {T₀ : KExpr}
    (hT : specTypeRaw r = some T₀) : T₀.constsResolveBy (stdNamed r) = true := by
  have h := List.all_eq_true.mp std_named_all r hr
  rw [hT] at h
  exact h

/-- **A role a standard axiom's type names is stored by the closure's environment.** -/
theorem stdNeed_stored {L : Ix.Kernel.Env .anon → NativeFam .anon → Prop}
    {t : Ix.Kernel.RoleTable} {g : Nat} {R₁ : Ixon.Env} {env₁ : Ix.Kernel.Env .anon}
    (hb : BndOver.{u} L t (· < g) R₁ env₁) {r r' : Role}
    (hr : r ∈ IxVM.Consistency.standardAxioms) (hg : Ix.SpecDigest.groupOf r = g)
    (hr' : r' ∈ stdNeeds r) {x : _root_.Address} (hx : t.addressOf? r' = some x) :
    ∃ ci, env₁.find? (Ix.Kernel.Key.role r') = some ci := by
  obtain ⟨hlt, hk⟩ := std_needs_facts r hr r' hr'
  have hlt' : Ix.SpecDigest.groupOf r' < g := hg ▸ hlt
  rcases hk with hw | hs | hp
  · obtain ⟨ci, hci, -⟩ := hb.shape.kept _ r' x hlt' (IxVM.Consistency.role_mem_roleGroup r')
      (Or.inl (Or.inl hw)) hx
    exact ⟨ci, hci⟩
  · obtain ⟨ci, hci, -⟩ := hb.shape.kept _ r' x hlt' (IxVM.Consistency.role_mem_roleGroup r')
      (Or.inl (Or.inr hs)) hx
    exact ⟨ci, hci⟩
  · obtain ⟨ci, hci, -⟩ := hb.shape.preludeKept _ r' x hlt'
      (IxVM.Consistency.role_mem_roleGroup r') hp hx
    exact ⟨ci, hci⟩

private theorem recordOf_up' {R R' : Ixon.Env}
    (h : ∀ a lc, R.consts.get? a = some lc → R'.consts.get? a = some lc) :
    ∀ x c, IxVM.Consistency.recordOf R x = some c → IxVM.Consistency.recordOf R' x = some c := by
  intro x c hc
  unfold IxVM.Consistency.recordOf at hc ⊢
  cases hg : R.consts.get? x with
  | none => rw [hg] at hc; cases hc
  | some lc => rw [hg] at hc; rw [h x lc hg]; exact hc

/-! ## The validation facts -/

set_option maxHeartbeats 3200000 in
/-- **What a binding run's validation of a standard axiom gives the fold**, at every binding
run (module docstring). -/
theorem axiomValidationFacts (L : Ix.Kernel.Env .anon → NativeFam .anon → Prop)
    (calls : List (Call F)) : AxiomInstall.AxiomValidationFacts.{u} L calls := by
  intro t ρ Rs hrun hss hall ht g r a R R₁ R' env₁ h6 h77 hgrp hstd ha hadm hrd hb hadds
  have htwf : t.wf = true := wf_of_check ht
  have hrg : r ∈ IxVM.Consistency.roleGroup g := by rw [hgrp]; exact List.mem_singleton.mpr rfl
  have hgr : Ix.SpecDigest.groupOf r = g := OpInstall.groupOf_of_mem_roleGroup hrg
  have hkeya : keyOf t a = Ix.Kernel.Key.role r := keyOf_of_addressOf htwf ha
  obtain ⟨hres, hinert, hnS, hTS⟩ := std_misc r hstd
  obtain ⟨n₀, hn₀⟩ := Option.isSome_iff_exists.mp hnS
  obtain ⟨T₀, hT⟩ := Option.isSome_iff_exists.mp hTS
  -- the run's validation of the axiom
  obtain ⟨bAddr, tb, -, -, hρ⟩ := hrun.observed
  have hval : RoleValidationIn calls bAddr t g r := by
    have e : ρ.validated = (observedRun calls bAddr t ρ.E₀ ρ.rank).validated :=
      congrArg BRun.validated hρ
    have h1 := hadm.validated r hrg
    rw [e] at h1
    exact h1
  -- the record: a safe axiom record of the run's store, held by `R'`
  obtain ⟨a', raw0, c, ax, had', hsz, hh, hblk, hde, hdeE, hinfo, hsafe⟩ :=
    RoleVal.ValidateRoleIn.axiom_record (show RoleVal.ValidateRoleIn calls bAddr t g r from hval)
      ((RoleVal.specKind_three_iff r).mpr hstd)
  have ea : a = a' := Option.some.inj (ha.symm.trans had')
  subst ea
  have hcE : IxVM.Consistency.recordOf ρ.E₀ a = some c := by
    rw [← hblk]
    exact Claim.recordOf_hashed hrun.runStore hrun.hashedStored hh hsz hde hdeE
  have hcR' : IxVM.Consistency.recordOf R' a = some c := by
    obtain ⟨c₁, hc₁⟩ := Option.isSome_iff_exists.mp
      (hadm.kept r hrg (Or.inl (Or.inr hstd)) a ha)
    have h1 := recordOf_up' hadm.loaded a c₁ hc₁
    rw [hcE] at h1
    rw [hc₁, Option.some.inj h1]
  refine ⟨⟨c, ax, hcR', hinfo⟩, fun hfresh => ?_⟩
  have hlogic : IxVM.Consistency.InLogic c := by
    unfold IxVM.Consistency.InLogic
    rw [hinfo]
    exact hsafe
  -- a record store for `R'` the run's calls are good for
  obtain ⟨Ec, hEc, hst⟩ := hss R' hadm.loaded hadm.loadedBlobs hadm.committed hadm.zeroFree
  have hcEc : IxVM.Consistency.recordOf Ec a = some c :=
    (Typing.recordOf_eq_recordAt_of_decoded hEc.1 a).trans (hEc.2.1 a c hcR')
  -- the observed call
  obtain ⟨h, h', x_rc, x_tbl, res, cs, hrc, htbl, ev, hsubV⟩ := hval
  have htblR : TableRep t h x_tbl := htbl.toTableRep
  cases Obs.«KernelRoles::validate_role».obs ev with
  | n3 v1 m2 cs12 v31 m32 p39 cs45 v67 v68 m70 cs78 m90 cs98 m111 cs122 cs288
      ev14 ev47 ld41 ev80 ev100 heq109 ev124 ev290 hc323 =>
    have hsub45 : ∀ cl ∈ cs45, cl ∈ calls := fun cl hm => hsubV cl (by rw [hc323]; simp [hm])
    have hsub288 : ∀ cl ∈ cs288, cl ∈ calls := fun cl hm => hsubV cl (by rw [hc323]; simp [hm])
    obtain ⟨ext_ba, a'', ha_m2, had⟩ := RoleVal.role_bound_addr_uncond htblR ev14
    have ea : a = a'' := Option.some.inj (ha.symm.trans had)
    subst ea
    obtain ⟨b, hbr, hba⟩ := ha_m2
    -- the load, read over `R'`
    have hbound45 : IxVM.Consistency.Bounded cs45 := RomBound.bounded_mono hrun.bounded hsub45
    obtain ⟨-, bytes, E_ld, hhash, hblake, hloaded, hL1⟩ :=
      Ingress.get_ci_loadedRecords_spec hbound45 hbr ev47
    have hrecA : Ix.Cert.recordAt ρ.E₀ (ixAddr b) = some c := by
      rw [← hrun.runStore.recordOf_eq_recordAt, hba]
      exact hcE
    obtain ⟨-, -, v, hld, hraw⟩ :=
      LoadedReads.loadedRecords_record hrun.runStore hsub45 hhash hblake hL1 hrecA
    have hvv31 : v = v31 := Except.ok.inj (hld.symm.trans ld41)
    unfold Ingress.RawCIRep at hraw
    rw [hinfo] at hraw
    obtain ⟨blobs, hbt, hrawV⟩ := hraw
    have hblobR : ∀ x bs, (x, bs) ∈ blobs → R'.blobs.get? x = some bs := fun x bs hm =>
      hrd.blobs x bs (hrun.runStore.blob_of_table hloaded hsub45 hbt x bs hm)
    obtain ⟨ty₀, hty, hreads, -⟩ :=
      LoadedReads.axio_reading ht (store := IxVM.Consistency.recordOf R')
        (blob := fun x => R'.blobs.get? x) hcR' hinfo hlogic (by
          have e : IxVM.Consistency.keyOf t a = Ix.Kernel.Key.role r := hkeya
          rw [e]; exact hinert)
        hblobR hrawV
    obtain ⟨hnl, tyPtr, hvV, rawT⟩ := hrawV
    -- the axiom's checks
    match Obs.«KernelRoles::validate_standard_axiom».obs ev290 with
    | .run (m60 := b60) (m97 := b97) (cs107 := cs_es) (m128 := b128) (m164 := b164)
        (hv15 := hci) (ev72 := e72) (hm136 := hm) (ev109 := e109) (ev174 := e174)
        (ev153 := e153) (hc388 := hca) .. =>
      have hcia := (Value.construct.inj (hvV.symm.trans (hvv31.trans hci))).2.2
      injection hcia with hnlE hcia2
      injection hcia2 with htyE hcia3
      subst hnlE
      rw [← htyE] at e72 e109 e153 hca
      have hsubW : (⟨"KernelCheck::validate_expr_well_scoped",
          [tyPtr, .field 0, .field (ax.lvls.toNat : F)], m111⟩ : Call F) ∈ calls :=
        hsub288 _ (by rw [hca]; simp)
      have hsubES : ∀ cl ∈ cs_es, cl ∈ calls := fun cl hm' =>
        hsub288 cl (by rw [hca]; simp [hm'])
      -- heaps
      have ext32 : Heap.Extends m32 m111 :=
        ev80.heap_extends.trans (ev100.heap_extends.trans ev124.heap_extends)
      have ext60 : Heap.Extends m32 b60 := ext32.trans e72.heap_extends
      have ext128 : Heap.Extends m32 b128 := by
        rw [hm]
        exact ext60.trans (Heap.Extends.snoc b60 _)
      have ext97 : Heap.Extends m32 b97 := ext128.trans e109.heap_extends
      have ext164 : Heap.Extends m32 b164 := ext97.trans e174.heap_extends
      have hhm32 : Heap.Extends h m32 := ext_ba.trans ev47.heap_extends
      -- the type is well scoped
      obtain ⟨-, hlbb, hdef⟩ :=
        Assembly.validate_expr_well_scoped_spec hrun.bounded hnl rawT ext32 hty e72 hsubW
      -- the canonical type, loaded exactly
      have hgE : Good ⟨Ec, env₁, t, none⟩ (cs45) := (hst.good env₁ none).sub hsub45
      have htyEc : (IxVM.Consistency.exprReader t (fun x => Ec.blobs.get? x) c id
          (fun _ => none)).read ax.typ = .ok ty₀ :=
        ReaderReads.exprReader_mono (fun x b' h₁ => hEc.2.2.1 x b' h₁) hty
      obtain ⟨ty', tyPtrV, blobsV, hcanon, hann, ⟨uV, hldV⟩, -, rtyV, htm⟩ :=
        LoadedReads.get_ci_axio_canon_raw ht hgE.1 hbr ev47 (by rw [hba]; exact hcEc) hinfo htyEc
          hlbb hdef
      have hvvl := (Value.construct.inj ((Except.ok.inj (hldV.symm.trans ld41)).trans
        (hvv31.symm.trans hvV))).2.2
      injection hvvl with hvh hvvl2
      injection hvvl2 with hptr hvt
      rw [hptr] at rtyV htm
      -- the pin
      have htbl97 : TableRep t b97 x_tbl := htblR.mono (hhm32.trans ext97)
      have hpinE : ty'.erasePw = T₀.erasePw :=
        typePinned_erasePw htwf hT htbl97 (htm.mono ext97) e174 e153
      have ev80' := ev80
      rw [← hvv31, hvV] at ev80'
      obtain ⟨e67, -⟩ := const_num_lvls_fields ev80'
      obtain ⟨e68, -, hlt8⟩ := role_levels_spec hn₀ ev100
      have hnn : ax.lvls.toNat = n₀ := by
        have hf' : ((ax.lvls.toNat : Nat) : F) = ((n₀ : Nat) : F) :=
          Value.field.inj (e67.symm.trans (heq109.trans e68))
        have hv' := congrArg ZMod.val hf'
        rw [RolesAux.val_natCast (by omega), RolesAux.val_natCast (by omega)] at hv'
        exact hv'
      have hpin : Ix.Kernel.ConstantVal.matchesPin
          ⟨.role r, List.range ax.lvls.toNat, ty'⟩ (AxiomInstall.stdAxiomPin r) = true := by
        rw [hnn]
        exact stdAxiom_matchesPin hstd hT hn₀ hpinE
      -- the cells of the loaded type are stored
      obtain ⟨v12, m15, cs23, ev25, heq48, -, -, -⟩ :=
        Obs.«KernelRoles::assert_type_pinned».obs e153
      subst heq48
      obtain ⟨-, T, hTrep, -⟩ := roleTypeRenders t r T₀ hT htwf htbl97 e174
      have hcells : ∀ x, AddrIn m32 tyPtr x →
          ∃ ci, env₁.find? (keyOf t (ixAddr x)) = some ci := by
        intro x hin
        have h2 := kexpr_struct_eq_cells ((htm.mono ext164) 0 (fun _ => .sort .zero))
          (hTrep 0 (fun _ => .sort .zero)) ev25 x (AddrIn.mono' ext164 hin)
        obtain ⟨r', hr', hP⟩ := roleType_cells hT htwf htbl97 e174 x h2
        have hn := hP (stdNamed r) (std_named hstd hT)
        unfold stdNamed at hn
        obtain ⟨r'', hr'', he⟩ := List.any_eq_true.mp hn
        have he' : r' = r'' := Ix.Kernel.Key.role.inj (of_decide_eq_true he)
        subst he'
        obtain ⟨ci, hci⟩ := stdNeed_stored hb hstd hgr hr'' hr'
        rw [keyOf_of_addressOf htwf hr']
        exact ⟨ci, hci⟩
      -- the declaration checked at the closure's environment
      have hinv : Decl.PrefixInv.{u} Ec t (some (valLimit g)) env₁ :=
        hb.inv (OpInstall.recordsFor_down hadds hEc) (carried_valLimit g) (limWithin_below t g)
      let cx : ScopedCtx := Ctx.stored ⟨Ec, env₁, t, some (valLimit g)⟩
      obtain ⟨hef, hlf⟩ := hinv.scopedCoreFacts
      have htmC : TmC cx.κ b128 ty' tyPtr :=
        (Typing.TmCExact.rekey (htm.mono ext128)
          (fun x hin => by
            obtain ⟨ci, hci⟩ := hcells x (TmExact.addrIn_back (htm 0 (fun _ => .sort .zero))
              ext128 x hin)
            exact Ctx.stored_key_of_find (c := ⟨Ec, env₁, t, some (valLimit g)⟩) hci)
          (fun x hp _ => by
            obtain ⟨ci, hci⟩ := hcells x (TmExact.addrIn_back (htm 0 (fun _ => .sort .zero))
              ext128 x hp.addrIn)
            exact Ctx.stagedOver_projPermitted_of_find
              (c := ⟨Ec, env₁, t, some (valLimit g)⟩) (pre := env₁) hci)).toTmC
      have hrc128 : RCRep t (some (valLimit g)) b128 x_rc :=
        Claim.RCFullRep.toRCRep (hrc.mono ((hhm32.trans ext128)))
      have htys : TypesRep cx.κ (fun _ => .sort .zero) b128 0
          (.ptr (.enum kexprListEnum) b60.length) := by
        rw [hm]
        exact Decl.typesRep_alloc_nil cx.κ (fun _ => .sort .zero) b60
      have hgood_c : Good cx.toCtx calls := hst.good env₁ (some (valLimit g))
      obtain ⟨stype, uu, -, hinf, hred, -, -⟩ :=
        Decl.scoped_core_ensure_sort (c := cx) hrc128 htys (Decl.ghostScoped_zero _) hef hlf
          (CoreGood.ofRaw (hgood_c.sub hsubES) (fun _ _ => trivial)) e109
          (htmC 0 (fun _ => .sort .zero))
      have hnfv₀ : ty₀.hasFvar = false := Assembly.memberReader_read_noFvar hty
      have hnfv' : ty'.hasFvar = false := Decl.annotates_hasFvar_false hann hnfv₀
      have hdef' : ty'.allLevelParamsDefined (List.range ax.lvls.toNat) = true :=
        Decl.validate_expr_well_scoped_spec hnl ((htm.mono ext32) 0 (fun _ => .sort .zero)) e72
      have hnoprj : (Ix.Kernel.Key.role r : KKey).isProjFnShape = false := by
        rw [← hkeya]
        exact Decl.isProjFnShape_of_isBaseKey (Decl.isBaseKey_keyOf t a)
      have hcv : Ix.Kernel.Semantics.ConstantValRunJ Ix.Kernel.Model.rulesJ env₁
          ⟨.role r, List.range ax.lvls.toNat, ty₀⟩ ty' :=
        ⟨by show (env₁.find? (Ix.Kernel.Key.role r)).isNone = true; rw [hfresh]; rfl, hres,
          hnoprj, Decl.levelParam_nodup_of_nodup List.nodup_range, hlbb, hnfv₀, Decl.annot_of_annotates hann hnfv₀ hlbb 0, hdef',
          Decl.infer_constsResolve hinf hef.store hnfv', stype, uu, hinf, hred⟩
      -- the reload
      have hnt : ∀ T : Ix.Kernel.Key .anon,
          (Ix.Kernel.Key.role r : KKey) ≠ Ix.Kernel.projTableName T := by
        intro T
        rw [← hkeya]
        exact Decl.ne_projTableName_of_isBaseKey (Decl.isBaseKey_keyOf t a)
      have hext : Ix.Kernel.EnvExt env₁
          (AxiomInstall.axInstalled env₁ r (List.range ax.lvls.toNat) ty') :=
        Ix.Kernel.EnvExt.cons hfresh (fun _ => hnt _)
      have hreload : ∀ E, Typing.RecordsFor R' E →
          Decl.ReloadsAs E t (AxiomInstall.axInstalled env₁ r (List.range ax.lvls.toNat) ty')
            (.axiomInfo ⟨.role r, List.range ax.lvls.toNat, ty'⟩) := by
        intro E hE addr ptr h₁ h₁' cs₁ a₁ ev₁ hgood₁ ha₁ hkey₁
        have hk : keyOf t (ixAddr a₁) = keyOf t a := hkey₁.trans hkeya.symm
        have hka : ixAddr a₁ = a := Assembly.keyOf_injective ht hk
        have hrecE : IxVM.Consistency.recordOf E (ixAddr a₁) = some c := by
          rw [hka]
          exact (Typing.recordOf_eq_recordAt_of_decoded hE.1 a).trans (hE.2.1 a c hcR')
        have htyE' : (IxVM.Consistency.exprReader t (fun x => E.blobs.get? x) c id
            (fun _ => none)).read ax.typ = .ok ty₀ :=
          ReaderReads.exprReader_mono (fun x b' h₂ => hE.2.2.1 x b' h₂) hty
        obtain ⟨ty'', tyPtr'', blobs'', hcanon'', -, ⟨u'', hld''⟩, hnl'', rty'', htm''⟩ :=
          LoadedReads.get_ci_axio_canon_raw ht hgood₁.1 ha₁ ev₁ hrecE hinfo htyE' hlbb hdef
        have ety : ty'' = ty' := Option.some.inj (hcanon''.symm.trans hcanon)
        rw [ety] at htm''
        have hvr : Decl.ValRepExact (keyOf t) h₁' (.field (ax.lvls.toNat : F)) tyPtr''
            (⟨.role r, List.range ax.lvls.toNat, ty'⟩ : Ix.Kernel.ConstantVal .anon) :=
          LoadedReads.valRepExact_range hnl'' (by rw [Decl.posOf_range]; exact htm'')
        refine ⟨_, hld'', .axio (ValRep.rekey hvr.toValRep (fun x hin => ?_) (fun x hp _ => ?_))⟩
        · obtain ⟨y, hy, hxy⟩ := RawConvExpr.cells_of_twin rty'' rtyV x hin
          obtain ⟨ci, hci⟩ := hcells y hy
          rw [hxy] at hci
          exact Ctx.stored_key_of_find
            (c := ⟨E, AxiomInstall.axInstalled env₁ r (List.range ax.lvls.toNat) ty', t, none⟩)
            (hext.find hci)
        · obtain ⟨y, hy, hxy⟩ := RawConvExpr.cells_of_twin rty'' rtyV x hp.addrIn
          obtain ⟨ci, hci⟩ := hcells y hy
          rw [hxy] at hci
          exact Ctx.stagedOver_projPermitted_of_find
            (c := ⟨E, AxiomInstall.axInstalled env₁ r (List.range ax.lvls.toNat) ty', t, none⟩)
            (pre := AxiomInstall.axInstalled env₁ r (List.range ax.lvls.toNat) ty') (hext.find hci)
      have hrefs : ty₀.RefsIn Decl.NonAuxKey :=
        Assembly.memberReader_read_refsIn_nonAux
          (cx := IxVM.Consistency.readCtx t (fun x => R'.blobs.get? x))
          (fun ref k hk => Ix.Cert.ReaderUnits.bindingsOf_keyed _ t ref k hk)
          (fun i m k hs _ => by cases hs) hty
      refine ⟨List.range ax.lvls.toNat, ty₀, ty', hcv, hpin,
        hrefs, hann, ?_,
        Typing.address_size_of_record hrun.runStore hcE, hreload⟩
      have hr := hreads
      have ek : IxVM.Consistency.keyOf t a = Ix.Kernel.Key.role r := hkeya
      rw [ek] at hr
      exact hr
  | n0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, -⟩ := RoleVal.role_spec_kind_spec ev124
    rw [(RoleVal.specKind_three_iff r).mpr hstd] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, -⟩ := RoleVal.role_spec_kind_spec ev124
    rw [(RoleVal.specKind_three_iff r).mpr hstd] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, -⟩ := RoleVal.role_spec_kind_spec ev124
    rw [(RoleVal.specKind_three_iff r).mpr hstd] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, -⟩ := RoleVal.role_spec_kind_spec ev124
    rw [(RoleVal.specKind_three_iff r).mpr hstd] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)
  | n5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ev124 _ _ =>
    obtain ⟨hsk_f, -⟩ := RoleVal.role_spec_kind_spec ev124
    rw [(RoleVal.specKind_three_iff r).mpr hstd] at hsk_f
    exact absurd (Value.field.inj hsk_f) (by decide)

/-- **The residual's hypothesis `standardAxiomRoleUnit`, with no premise.** -/
theorem standardAxiomRoleUnit_closed :
    ∀ calls : List (Call F), AtGroups (BindingRun calls)
      (RoleUnitStepOver.{u} (· ∈ IxVM.Consistency.standardAxioms) Typing.FormerOpenTraceAt) :=
  AxiomInstall.standardAxiomRoleUnit
    (fun calls => axiomValidationFacts Typing.FormerOpenTraceAt calls)

end IxVM.Refinement.Binding
