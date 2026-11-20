import IxVMRefinement.Assembly.TypingRecParentTie
import IxVMRefinement.RoleVal.BasisPins

/-! # The basis-recursor guard of the member check, inverted

`check_recursor_member` ends with `KernelRoles::basis_rec_at_pin(parent_addr, addr)` on the
address its scan read at the head of the major premise's domain and on the record's own
address. The guard compares the parent with the committed address of each of the five basis
families (`Nat`, `Eq`, `PUnit`, `Empty`, `False`) and, where they agree, asserts that the
record's address is the committed address of that family's recursor. It reads no role context:
its addresses are the constants `KernelRoles::basis_pin` returns, which are the default role
table's bindings (`RoleVal.basis_pin_prelude`).

* `basisRecPairs`: the five family roles, each with its recursor's role, as the guard pairs
  them;
* `basis_rec_pair_spec`: one comparison of the guard. If the default table binds the family at
  the parent, it binds the recursor at the record's address;
* `basis_rec_at_pin_spec`: the guard, at the five pairs;
* `native_rec_basis_guard`: the member check's scan and its guard run, on the scanned parent
  and the record's address, at a heap after the scan's;
* `recScanned_of_route`: the scan returns a represented address whose key heads the major
  premise's domain of the represented type;
* `recGuard_of_arm`: from the walk's check of a recursor record, at an environment a step is
  asked at: the scanned parent heads the record's major premise (`RecMajorTie`), and the guard
  ran on it and on the record's address.
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

/-! ## The guard -/

/-- **The basis families with their recursors**, by role, as `basis_rec_at_pin` pairs them. -/
def basisRecPairs : List (Ix.Kernel.Role × Ix.Kernel.Role) :=
  [(.nat, .natRec), (.eq, .eqRec), (.punit, .punitRec), (.empty, .emptyRec), (.false, .falseRec)]

/-- **One comparison of the guard**, at the role numbers of a family `fam` and of its recursor
`rcr`, both prelude roles: if the default table binds `fam` at the parent's address, it binds
`rcr` at the record's address. Where the parent is the family's pin the run asserted the
second comparison; where it is not, the first comparison answered otherwise. -/
theorem basis_rec_pair_spec {fam rcr : Ix.Kernel.Role} {f g : F}
    (hf : f = Core.roleNum fam) (hg : g = Core.roleNum rcr)
    (hfam : fam ∈ Ix.Kernel.preludeShape.flatMap id)
    (hrcr : rcr ∈ Ix.Kernel.preludeShape.flatMap id)
    {parent addr r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    {P A : _root_.Address}
    (ev : ObsFn Obs.W "KernelRoles::basis_rec_pair" [parent, addr, .field f, .field g]
      h r h' cs)
    (hP : Core.BaseSeams.addr h parent P) (hA : Core.BaseSeams.addr h addr A) :
    RoleVal.committedDefaultRoleTable.addressOf? fam = some P →
      RoleVal.committedDefaultRoleTable.addressOf? rcr = some A := by
  subst hf hg
  intro hbound
  match Obs.«KernelRoles::basis_rec_pair».obs ev with
  | .n1 (ev14 := pinFam) (ev51 := eqFam) (ev85 := pinRec) (ev132 := eqRec)
      (heq155 := asserted) .. =>
    obtain ⟨-, aR, haR, r', hr', hrR⟩ := RoleVal.basis_pin_prelude hrcr pinRec
    obtain ⟨a', ha', haA⟩ := Core.BaseSeams.addr_mono
      (pinFam.heap_extends.trans (eqFam.heap_extends.trans pinRec.heap_extends)) hA
    obtain ⟨hv, -⟩ := Lib.address_eq_spec eqRec ha' hr'
    have hsame : a' = r' := by
      by_cases hs : a' = r'
      · exact hs
      · rw [ite_eq_right hs] at hv
        exact absurd (Value.field.inj (asserted.symm.trans hv)) one_ne_zero
    have e : aR = A := hrR.symm.trans ((congrArg Core.ixAddr hsame.symm).trans haA)
    rw [haR, e]
  | .other (ev14 := pinFam) (ev51 := eqFam) (hne161 := differs) .. =>
    obtain ⟨-, aF, haF, f', hf', hfF⟩ := RoleVal.basis_pin_prelude hfam pinFam
    obtain ⟨p', hp', hpP⟩ := Core.BaseSeams.addr_mono pinFam.heap_extends hP
    obtain ⟨hv, -⟩ := Lib.address_eq_spec eqFam hp' hf'
    have hPF : P = aF := Option.some.inj (hbound.symm.trans haF)
    have hsame : p' = f' := Decl.ixAddr_injective (hpP.trans (hPF.trans hfF.symm))
    rw [ite_eq_left hsame] at hv
    exact absurd hv differs

/-- **The guard, inverted**: on a represented parent address and a represented record address,
for each of the five basis families, if the default table binds the family at the parent it
binds the family's recursor at the record's address. -/
theorem basis_rec_at_pin_spec {parent addr r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} {P A : _root_.Address}
    (ev : ObsFn Obs.W "KernelRoles::basis_rec_at_pin" [parent, addr] h r h' cs)
    (hP : Core.BaseSeams.addr h parent P) (hA : Core.BaseSeams.addr h addr A) :
    ∀ p ∈ basisRecPairs, RoleVal.committedDefaultRoleTable.addressOf? p.1 = some P →
      RoleVal.committedDefaultRoleTable.addressOf? p.2 = some A := by
  match Obs.«KernelRoles::basis_rec_at_pin».obs ev with
  | .run (ev14 := natRun) (ev58 := eqRun) (ev102 := punitRun) (ev146 := emptyRun)
      (ev182 := falseRun) .. =>
    have x₁ := natRun.heap_extends
    have x₂ := x₁.trans eqRun.heap_extends
    have x₃ := x₂.trans punitRun.heap_extends
    have x₄ := x₃.trans emptyRun.heap_extends
    have s₁ := basis_rec_pair_spec (fam := .nat) (rcr := .natRec) (f := 0) (g := 3) rfl rfl
      (by decide) (by decide) natRun hP hA
    have s₂ := basis_rec_pair_spec (fam := .eq) (rcr := .eqRec) (f := 8) (g := 10) rfl rfl
      (by decide) (by decide) eqRun (Core.BaseSeams.addr_mono x₁ hP) (Core.BaseSeams.addr_mono x₁ hA)
    have s₃ := basis_rec_pair_spec (fam := .punit) (rcr := .punitRec) (f := 11) (g := 13)
      rfl rfl (by decide) (by decide) punitRun (Core.BaseSeams.addr_mono x₂ hP)
      (Core.BaseSeams.addr_mono x₂ hA)
    have s₄ := basis_rec_pair_spec (fam := .empty) (rcr := .emptyRec) (f := 14) (g := 15)
      rfl rfl (by decide) (by decide) emptyRun (Core.BaseSeams.addr_mono x₃ hP)
      (Core.BaseSeams.addr_mono x₃ hA)
    have s₅ := basis_rec_pair_spec (fam := .false) (rcr := .falseRec) (f := 16) (g := 17)
      rfl rfl (by decide) (by decide) falseRun (Core.BaseSeams.addr_mono x₄ hP)
      (Core.BaseSeams.addr_mono x₄ hA)
    intro p hp
    unfold basisRecPairs at hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact s₁
    rcases List.mem_cons.mp hp with rfl | hp
    · exact s₂
    rcases List.mem_cons.mp hp with rfl | hp
    · exact s₃
    rcases List.mem_cons.mp hp with rfl | hp
    · exact s₄
    rcases List.mem_cons.mp hp with rfl | hp
    · exact s₅
    · cases hp

/-! ## The guard's run in the member check -/

/-- **The member check's scan and its guard**: `check_recursor_member` scans the type for the
major premise's parent and, last, runs `basis_rec_at_pin` on the scanned parent and the
record's address, at a heap after the scan's. -/
theorem native_rec_basis_guard
    {rc address levels type parameters indices motives minors rules k unsafeFlag block position
      result : SourceValue F}
    {heap final : Heap F} {calls : List (Call F)}
    (observed : ObsFn Obs.W "KernelCheck::check_recursor_member"
      [rc, .construct "KernelTypes::KConstantInfo" "Rec"
        [levels, type, parameters, indices, motives, minors, rules, k, unsafeFlag, block,
          position], address]
      heap result final calls) :
    ∃ (parent : SourceValue F) (scanHeap guardHeap : Heap F)
      (scanCalls guardCalls : List (Call F)),
      ObsFn Obs.W "KernelCheck::rec_to_parent_addr" [type, parameters, motives, minors, indices]
        heap parent scanHeap scanCalls ∧
      (∀ cl ∈ scanCalls, cl ∈ calls) ∧
      Heap.Extends scanHeap guardHeap ∧
      ObsFn Obs.W "KernelRoles::basis_rec_at_pin" [parent, address] guardHeap result final
        guardCalls := by
  match Obs.«KernelCheck::check_recursor_member».obs observed with
  | .run (v72 := parent) (m73 := scanHeap) (cs83 := scanCalls) (m823 := guardHeap)
      (cs879 := guardCalls)
      (hv15 := input) (ev85 := scan) (ev142 := load) (ev233 := route) (ev278 := muts₁)
      (ev292 := muts₂) (ev314 := sameBlock) (heq357 := notAux) (ev382 := lenRun)
      (ev412 := peelRun) (ev477 := scopeRun) (sg671 := seg) (ev685 := kRun)
      (ev751 := shapeRun) (ev781 := letsRun) (ev835 := canonRun) (ev881 := guardRun)
      (hc898 := children) .. =>
    injection input with _ _ fields
    simp only [List.cons.injEq, and_true] at fields
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := fields
    have eSeg := load.heap_extends.trans (route.heap_extends.trans (muts₁.heap_extends.trans
      (muts₂.heap_extends.trans (sameBlock.heap_extends.trans (lenRun.heap_extends.trans
        (peelRun.heap_extends.trans scopeRun.heap_extends))))))
    match seg with
    | .n1 (hv533 := isAux) .. =>
      exact absurd (Value.field.inj (isAux.symm.trans notAux)) one_ne_zero
    | .other (ev604 := spineRun) .. =>
      refine ⟨parent, scanHeap, guardHeap, scanCalls, guardCalls, scan, ?_,
        eSeg.trans (spineRun.heap_extends.trans (kRun.heap_extends.trans
          (shapeRun.heap_extends.trans (letsRun.heap_extends.trans canonRun.heap_extends)))),
        guardRun⟩
      intro call member; rw [children]; simp [member]

/-! ## The scanned parent -/

/-- **The scan returns the head of the major premise's domain**: on the record's type
represented under the prefix keying, `rec_to_parent_addr` returns a represented address whose
key heads the domain of the binder it reached. -/
theorem recScanned_of_route {E : Ixon.Env} {t : Ix.Kernel.RoleTable} {lim : Option Nat}
    {env : Ix.Kernel.Env .anon} (hinv : Decl.PrefixInv.{u} E t lim env)
    {calls cs₁ : List (Call F)}
    (hgood : Core.Good ⟨E, env, t, lim⟩ calls)
    {ty parent : SourceValue F} {p m mi i : F}
    {h₁ h₂ : Heap F} {T : Core.KExpr}
    (hT : Core.TmC (Core.Ctx.stored ⟨E, env, t, lim⟩).κ h₁ T ty)
    (ev₁ : ObsFn Core.W "KernelCheck::rec_to_parent_addr"
      [ty, .field p, .field m, .field mi, .field i] h₁ parent h₂ cs₁)
    (hs₁ : ∀ x ∈ cs₁, x ∈ calls) :
    ∃ (a : Bytes.Address) (dom : Core.KExpr) (us : List Core.KLevel),
      Bytes.RepAddressRef Core.addrTy h₂ a parent ∧
      Core.piDomAt (ZMod.val (p + m + mi + i)) T = some dom ∧
      dom.getAppFn = .const (keyOf t (Core.ixAddr a)) us := by
  let c : Core.ScopedCtx := Core.Ctx.stored ⟨E, env, t, lim⟩
  have hc : Core.ScopedCoreFacts c := hinv.scopedCoreFacts
  have hspec := Decl.scopedCalleesSpec c hc .rec_to_parent_addr _ _ _ _ _ ev₁
  obtain ⟨a, dom, us, ha, hpi, hhead⟩ := hspec ty p m mi i rfl
    (Core.CoreGood.ofRaw (hgood.sub hs₁) (fun _ _ => trivial)) T hT
  have hkr : Core.KeysResolved T := (hT 0 (fun _ => .sort .zero)).keysResolved
  have hne : c.κ (Core.ixAddr a) ≠ Core.unresolvedKey :=
    keysResolved_getAppFn (keysResolved_piDomAt _ hkr hpi) hhead
  have hkey : c.κ (Core.ixAddr a) = Core.keyOf t (Core.ixAddr a) := c.key_eq hne
  have hhead' := hhead
  rw [hkey] at hhead'
  exact ⟨a, dom, us, ha, hpi, hhead'⟩

/-- **The guard at a recursor record, from the walk's check of the record.** At every
environment the skeleton hands the step, the address the member check scanned heads the
record's major premise (`RecMajorTie`), and `basis_rec_at_pin` ran on its value and on the
value of the record's address, both represented at the guard's heap. The route to the scan is
that of `recParent_of_arm_tied`. -/
theorem recGuard_of_arm {calls : List (Call F)} {t : Ix.Kernel.RoleTable}
    {E₀ E : Ixon.Env} {envT : Ix.Kernel.Env .anon} {lim : Option Nat}
    {A : _root_.Address} {c : Ixon.Constant} {rc : Ixon.Recursor}
    (ht : t.check = .ok ()) (hS : LoadedReads.RunStore calls E₀) (hst : StepStore calls t E₀ E)
    (hc : recordOf E₀ A = some c) (hinfo : c.info = .recr rc)
    (hnat : RecArmRun calls t A lim) (hinert : InertClause t c)
    (hcover : ∀ env, HandedRefs t envT E₀ A c env → CoverAt t env c)
    (env : Ix.Kernel.Env .anon) (hstep : StepAt.{u} t envT E₀ E lim A c env) :
    ∃ (a : Bytes.Address) (parent addr result : SourceValue F) (guardHeap final : Heap F)
      (guardCalls : List (Call F)),
      RecMajorTie t E₀ A c rc (Core.ixAddr a) ∧
      Core.BaseSeams.addr guardHeap parent (Core.ixAddr a) ∧ Core.BaseSeams.addr guardHeap addr A ∧
      ObsFn Obs.W "KernelRoles::basis_rec_at_pin" [parent, addr] guardHeap result final
        guardCalls := by
  have hgood : Core.Good ⟨E, env, t, lim⟩ calls := hst.good env lim
  have hbound : Bounded calls := hgood.2
  have hrec₀ : Ix.Cert.recordAt E₀ A = some c := (hS.recordOf_eq_recordAt A).symm.trans hc
  have hstored : Decl.UsedRefsStored t env c :=
    usedRefsStored_of_cover (hcover env ⟨hstep.ext, hstep.refs, hstep.fresh⟩) hinert
  obtain ⟨h_pre, m_chk, h'_chk, rcv, ap, ptr, r_chk, levels, type, parameters, indices, motives,
    minors, rules, kf, uns, block, position, cs_load, cs_chk, -, -, ha_pre, ha_m, ev_ld, hsub_ld,
    hld, ev_chk, hsub_chk, hfr⟩ := hnat
  obtain ⟨a', ha'_ref, haA⟩ := ha_pre
  subst haA
  obtain ⟨rawBytes, c', hh, hba, hex, -, hres'⟩ :=
    Ingress.get_ci_block_trace_spec (hgood.sub hsub_ld).2 ha'_ref ev_ld
  have hcc : c' = c := hS.record_eq hrec₀ (Core.hashed_mono hsub_ld hh) hba hex
  subst c'
  unfold Ingress.GetCIBlockTraceResult at hres'
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
    check_const_rec_route ev_chk hfr
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
  have htmS := Decl.tmC_stored_of_usedRefs (E₀ := E) (env := env) (lim := lim) rty
    (recr_typ_usedRefs hinfo) hstored htm
  rw [Decl.posOf_range] at htmS
  obtain ⟨parent, scanHeap, guardHeap, scanCalls, guardCalls, evScan, hsScan, hextG, evGuard⟩ :=
    native_rec_basis_guard evM
  have hsum : ZMod.val ((rc.params.toNat : F) + (rc.motives.toNat : F) + (rc.minors.toNat : F) +
      (rc.indices.toNat : F)) =
      rc.params.toNat + rc.motives.toNat + rc.minors.toNat + rc.indices.toNat := by
    rw [← Nat.cast_add, ← Nat.cast_add, ← Nat.cast_add]
    exact ZMod.val_natCast_of_lt (by unfold Aiur.Library.U32.Goldilocks.modulus; omega)
  obtain ⟨a, dom, us, ha, hpi, hhead⟩ := recScanned_of_route hstep.inv hgood
    (htmS.mono hextM) evScan (fun x hx => hsub_chk x (hsubM x (hsScan x hx)))
  exact ⟨a, parent, ap, r_chk, guardHeap, h'_chk, guardCalls,
    ⟨tyP, E', htyP, hann, majorKey_of_piDomAt (by rw [← hsum]; exact hpi) hhead⟩,
    ⟨a, Bytes.repAddressRef_heapMono₂ Core.addrTy hextG ha, rfl⟩,
    Core.BaseSeams.addr_mono (hextM.trans (evScan.heap_extends.trans hextG)) ha_m, evGuard⟩

end IxVM.Refinement.Typing
