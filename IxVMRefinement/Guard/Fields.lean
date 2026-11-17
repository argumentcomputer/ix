import IxVMRefinement.Guard.InferRep
import IxC.Kernel.Semantics.Inductives.DeclNativeJ

/-! # Installation field sorts with actual classifier provenance

The checked field loop supplies its own sorts. Each sort retains the domain/context pointers,
actual classifier subcall, and zero-set agreement, so later consumers need not attach classifier
facts to an unrelated existential choice of typing derivations.
-/

namespace IxVM.Refinement.Core.GuardData

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open Ix.Kernel (Expr Level)
open Ix.Kernel.Rules (Infer Red)
open IxVM.Refinement.KernelLevels (RepKLevel)

/-- Evidence for one actually checked domain, including the physical classifier input. -/
def CheckedSortAt (c : ScopedCtx) (start : Heap F) (calls : List (Call F))
    (depth : Nat) (domain : KExpr) (sort : KLevel) : Prop :=
  ∃ (type : KExpr) (signature : KLevel) (Γ : Nat → KExpr)
    (input context predicted : SourceValue F) (before after : Heap F) (inner : List (Call F)),
    Infer c.env .full depth domain type ∧ Red c.env depth type (.sort sort) ∧
    Heap.Extends start before ∧ c.types Γ before depth context ∧
    Tm c.κ depth Γ before 0 domain input ∧
    ObsFn W "KernelGuard::sort_signature" [input, context] before predicted after inner ∧
    RepKLevel after signature predicted ∧ (∀ cl ∈ inner, cl ∈ calls) ∧
    ∀ φ, Level.eval φ sort = 0 ↔ Level.eval φ signature = 0

theorem CheckedSortAt.weaken {c : ScopedCtx} {start earlier : Heap F}
    {calls outer : List (Call F)} {depth : Nat} {domain : KExpr} {sort : KLevel}
    (checked : CheckedSortAt c start calls depth domain sort)
    (extension : Heap.Extends earlier start) (included : ∀ cl ∈ calls, cl ∈ outer) :
    CheckedSortAt c earlier outer depth domain sort := by
  obtain ⟨type, signature, Γ, input, context, predicted, before, after, inner,
    infer, reduce, extension, types, represented, observed, level, members, zero⟩ := checked
  exact ⟨type, signature, Γ, input, context, predicted, before, after, inner,
    infer, reduce, extension.trans extension, types, represented, observed, level,
    fun cl member => included cl (members cl member), zero⟩

/-- Actual assertion evidence retains the classifier's represented physical input. -/
theorem checked_sort_at {c : ScopedCtx} (hc : ScopedCoreFacts c)
    {d : Nat} {Γ : Nat → KExpr} {E : KExpr} {rc p ctx r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} (hg : CoreGood c cs)
    (hrc : c.rc h rc) (hctx : c.types Γ h d ctx) (hE : Tm c.κ d Γ h 0 E p)
    (ev : ObsFn W "KernelGuard::checked_sort" [rc, p, ctx] h r h' cs) :
    ∃ u, CheckedSortAt c h cs d E u := by
  obtain ⟨type, u, actual, signature, predicted, before, after, inner,
    infer, reduce, _, _, extension, observed, level, members, zero⟩ :=
      checked_sort_zero_iff hc hg hrc hctx hE ev
  exact ⟨u, type, signature, Γ, p, ctx, predicted, before, after, inner,
    infer, reduce, extension, types_mono extension hctx, hE.mono extension,
    observed, level, members, zero⟩

/-- With parameters already peeled, the actual installation loop chooses one sort per field
and retains each actual classifier call. -/
theorem check_fields_open {c : ScopedCtx} (hc : ScopedCoreFacts c) :
    ∀ (n : Nat) {d : Nat} {Γ : Nat → KExpr} {E body : KExpr} {fvs : List KExpr}
      {rc p ctx r : SourceValue F} {nf : F} {h h' : Heap F} {cs : List (Call F)},
      nf.val = n → Ix.Kernel.openPisAtFvars n E d = some (fvs, body) →
      CoreGood c cs → c.rc h rc → c.types Γ h d ctx → Tm c.κ d Γ h 0 E p →
      ObsFn W "KernelGuard::check_fields" [rc, p, .field 0, .field nf, ctx] h r h' cs →
      ∃ sorts : List KLevel, sorts.length = n ∧
        ∀ i < n, ∃ fv u, fvs[i]? = some fv ∧ sorts[i]? = some u ∧
          CheckedSortAt c h cs (d + i) fv.fvarTypeD u := by
  intro n
  induction n with
  | zero =>
    intro d Γ E body fvs rc p ctx r nf h h' cs _ _ _ _ _ _ _
    exact ⟨[], rfl, fun i hi => (Nat.not_lt_zero i hi).elim⟩
  | succ n ih =>
    intro d Γ E body fvs rc p ctx r nf h h' cs hn hop hg hrc hctx hE ev
    have hn0 : nf ≠ 0 := by intro equal; rw [equal, ZMod.val_zero] at hn; omega
    match Obs.«KernelGuard::check_fields».obs ev with
    | .n0_n0 (hv28 := zero) .. => exact (hn0 (Value.field.inj zero)).elim
    | .other (hne183 := nonzero) .. => exact (nonzero rfl).elim
    | .n0_other (x_dom := dom) (x_body := tail) (m70 := checkedHeap)
        (cs80 := first) (cs110 := rest) (v116 := remaining) (m154 := nextHeap)
        (ld48 := loaded) (ev82 := checked) (op151 := subtracted) (hm162 := allocated)
        (ev112 := walked) (hc182 := events) .. =>
      obtain ⟨D, B, metadata, rfl, hD, hB, _⟩ := hE.forallE_of_load loaded
      simp only [Ix.Kernel.openPisAtFvars] at hop
      rcases opened : Ix.Kernel.openPisAtFvars n (B.instantiate1 (.fvar d D)) (d + 1) with
        _ | ⟨fvs', body'⟩ <;> rw [opened] at hop
      · exact nomatch hop
      · simp only [Option.some.injEq, Prod.mk.injEq] at hop
        obtain ⟨rfl, rfl⟩ := hop
        have firstInside : ∀ cl ∈ first, cl ∈ cs := by intro cl member; rw [events]; simp [member]
        have restInside : ∀ cl ∈ rest, cl ∈ cs := by intro cl member; rw [events]; simp [member]
        obtain ⟨u, hu⟩ := checked_sort_at hc (hg.sub firstInside) hrc hctx hD checked
        have remainingValue : remaining = .field (nf - 1) := NatAux.sub_ok subtracted
        subst remainingValue allocated
        have decremented : (nf - 1).val = n := by have := NatAux.val_sub_one hn0; omega
        have extension := checked.heap_extends
        have cellExtension := Heap.Extends.snoc checkedHeap (.construct kexprListEnum "Cons" [dom, ctx])
        have allExtension := extension.trans cellExtension
        have newTypes := ProjAux.types_extend (types_mono extension hctx) (hD.mono extension)
        have newBody := Tm.open_body (Ghost.extend_at Γ d D) (Ghost.extend_below Γ d D)
          (hB.mono allExtension)
        obtain ⟨sorts, length, fields⟩ := ih decremented opened (hg.sub restInside)
          (hrc.mono allExtension) newTypes newBody walked
        refine ⟨u :: sorts, by simp [length], fun i hi => ?_⟩
        cases i with
        | zero =>
          refine ⟨.fvar d D, u, rfl, rfl, ?_⟩
          simpa only [Nat.add_zero, Expr.fvarTypeD] using
            hu.weaken (Heap.Extends.refl h) firstInside
        | succ i =>
          obtain ⟨fv, v, hfv, hv, checkedField⟩ := fields i (by omega)
          refine ⟨fv, v, hfv, hv, ?_⟩
          have result := checkedField.weaken allExtension restInside
          simpa only [Nat.add_assoc, Nat.add_comm 1 i] using result

end IxVM.Refinement.Core.GuardData
