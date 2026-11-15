import IxVMRefinement.Decl.NativeFront
import IxVMRefinement.L1.Records

/-! # Constructor witnesses from canonical raw loads

A nullary constructor's type is its former, so its exact reading is fixed before the
constructor is installed. Canonical record data and the observed load establish that reading
without an installed-load contract.
-/

namespace IxVM.Refinement.Decl

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open IxVM.Refinement.Core
open IxVM.Refinement.L1
open IxVM.Refinement.KernelLevels (RepKLevelList)

namespace NativeCtorLoad

/-- The serialized constructor of a one-member family with no parameters or fields. -/
def nullary : Ixon.Constructor := ⟨false, 0, 0, 0, 0, .inherited, .recur 0 #[]⟩

def nullaryVal (t : Ix.Kernel.RoleTable) (b : Bytes.Address) : KConstantVal :=
  ⟨keyOf t (cprjAddr (ixAddr b) 0 0), [], .const (keyOf t (iprjAddr (ixAddr b) 0)) []⟩

/-- The canonical block fixes every repeated raw read of its nullary constructor. Only
collision freedom for the actual enclosing trace is used; no constructor lookup is assumed. -/
theorem nullary_of_record {c : Ctx} {b₀ : Bytes.Address} {cb : Ixon.Constant}
    {ind : Ixon.Inductive} {order : List _root_.Address} {cs_root : List (Call F)}
    (hcan : Ix.Cert.Stream.StoredCanonical c.E order)
    (horder : ixAddr b₀ ∈ order)
    (hrec : Ix.Cert.recordAt c.E (ixAddr b₀) = some cb)
    (hblock : cb.info = .muts #[.indc ind])
    (hctors : ind.ctors = #[nullary])
    (hgood : Good c cs_root) :
    CtorLoadAt c.t b₀ 0 cs_root [(nullaryVal c.t b₀, 0)] [(nullaryVal c.t b₀, 0)]
      [.const (c.κ (iprjAddr (ixAddr b₀) 0)) []] := by
  refine ⟨rfl, fun j hj => ?_⟩
  have hj0 : j = 0 := by simpa using hj
  subst j
  refine ⟨(nullaryVal c.t b₀, 0), nullaryVal c.t b₀, rfl, rfl,
    ⟨rfl, rfl, .const⟩, ?_⟩
  intro bp ptr h h' cs hsub hbp ev
  have hg := hgood.sub hsub
  obtain ⟨_, _, _, bytes, cb', ms, ind', ct, blobs, v, hh, ha, hex, _,
    hcb, hms, hct, _, hld, hraw⟩ := L1.get_ci_cprj_spec hg.2 hbp ev
  unfold Ix.Cert.recordAt at hrec
  cases hget : c.E.consts.get? (ixAddr b₀) with
  | none => rw [hget] at hrec; cases hrec
  | some lc =>
    have hlc : lc.get? = some cb := by simpa [hget] using hrec
    have hdec := L1.deConstantExact_of_storedCanonical hcan horder hget hlc
    have hbytes := load_escape hget hg.1 bytes hh ha
    rw [hbytes, hdec] at hex
    injection hex with heq
    subst cb'
    rw [hblock] at hcb
    injection hcb with heq
    subst ms
    simp only [Array.toList_toArray, List.getElem?_cons_zero, ZMod.val_zero] at hms
    injection hms with heq
    injection heq with heq
    subst ind'
    rw [hctors] at hct
    simp only [Array.toList_toArray, List.getElem?_cons_zero, ZMod.val_zero] at hct
    injection hct with heq
    subst ct
    obtain ⟨_, _, _, _, _, ty, blk, b, hb, hblk, hv, hty⟩ := hraw
    change v = .construct kciEnum "Ctor"
      [.field 0, ty, blk, .field 0, .field 0, .field 0, .field 0, .field 0] at hv
    subst v
    have hrawTy : ∀ d Γ, RawTmExact c.κ d Γ h' 0
        (.const (c.κ (iprjAddr (ixAddr b₀) 0)) [])
        (.const (c.κ (iprjAddr (ixAddr b₀) 0)) []) ty := by
      cases hty with
      | recur _ hself hd ra hls rls cell =>
        simp only [blockRecurAddrs, blockRecurAddrsAux, Specs.Callees.memberProjInfo,
          Array.toList_toArray, List.getElem?_cons_zero] at hself
        injection hself with heq
        subst heq
        simp only [Array.toList_empty, List.mapM_nil, Option.some.injEq] at hls
        subst hls
        have levels : RepKLevelList h' [] _ := rls.toRepKLevelList (by simp)
        intro d Γ
        have rep := RawTmExact.const (κ := c.κ) (d := d) (Γ := Γ) (k := 0) cell ra levels
        simpa only [hd, iprjAddr] using rep
    refine ⟨.field 0, ty, blk, .field 0, .field 0, b, hld, hblk, hb,
      hrawTy, ?_⟩
    refine .ctor ⟨rfl, by decide, .refl [], fun d Γ => (hrawTy d Γ).toTmExact⟩
      rfl rfl ⟨by decide, by decide⟩ ⟨b, 0, 0, hblk, rfl, rfl, ?_⟩
    simpa only [nullaryVal, ZMod.val_zero, hb]

/-- The scoped raw constructor-load result is constructible at a fresh constructor of the
canonical nullary family. Installed agreement is vacuous exactly because the key is fresh. -/
theorem nullary_fresh {c : ScopedCtx} {b₀ : Bytes.Address} {cb : Ixon.Constant}
    {ind : Ixon.Inductive} {order : List _root_.Address} {cs_root cs : List (Call F)}
    {bp ptr : SourceValue F} {h h' : Heap F}
    (hcan : Ix.Cert.Stream.StoredCanonical c.E order)
    (horder : ixAddr b₀ ∈ order)
    (hrec : Ix.Cert.recordAt c.E (ixAddr b₀) = some cb)
    (hblock : cb.info = .muts #[.indc ind])
    (hctors : ind.ctors = #[nullary])
    (hgood : Good c.toCtx cs_root) (hsub : ∀ cl ∈ cs, cl ∈ cs_root)
    (hbp : Bytes.RepAddressRef addrTy h b₀ bp)
    (ev : ObsFn W "Ingress::get_ci_cprj" [bp, .field 0, .field 0] h ptr h' cs)
    (hfresh : c.env.find? (c.κ (cprjAddr (ixAddr b₀) 0 0)) = none) :
    (∃ ci, CIPtrRep c.κ h' ptr ci) ∧
    ∀ ci, c.env.find? (c.κ (cprjAddr (ixAddr b₀) 0 0)) = some ci →
      CIPtrRep c.κ h' ptr ci := by
  exact (nullary_of_record hcan horder hrec hblock hctors hgood).fresh_read
    (c := c) (j := 0) (by decide) hsub hbp ev (by simpa using hfresh)

end NativeCtorLoad

end IxVM.Refinement.Decl
