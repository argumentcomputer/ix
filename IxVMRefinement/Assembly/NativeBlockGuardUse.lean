import IxVMRefinement.Assembly.NativeBlockGuardWalk
import IxVMRefinement.Guard.UseWalk

/-! # The projection guard at a use, with the raw walk it made, from the facts a prefix carries

`peel_open`, `walk_open_checked` and `proj_guard_open` (`NativeBlockGuardWalk.lean`) read a
`KernelInfer::proj_guard` run at the term seam: the guard level as the fold of the field levels
under the flags, typed sorts, and the flags against the stored constructor type. They keep no
fact of the classifier calls the checked walk makes.

The twins that keep the raw data are in `Guard/UseWalk.lean` (`peel_traces`,
`walk_open_traced_ih`, `proj_guard_traced_ih`), stated over the facts before the registry and
the registry's induction hypothesis, so that a use can be read inside the registry's induction.
The forms here take the facts a prefix carries, which give both:

* `walk_open_traced`: the checked walk classifies each of the fields `0..K` of the raw
  telescope in the raw context of the binders before it, and the level it joins for a field
  has the zero-set of that field's signature.
* `proj_guard_traced`: a `proj_guard` run either took the unchecked walk, after its own
  `is_inductive_prop` call answered something other than `1` (the call and the inductive's
  load are returned), or its level is the fold of levels `lus` under `flags`, the flags cover
  `structUsedLater` of the stored constructor type, and the raw telescope `S` behind the type
  pointer of the constructor it loaded has field traces of its fields `0..f` whose signatures
  have the zero-sets of `lus`.
-/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Core.GuardWalk

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library Aiur.Library.List
open IxVM.Refinement.KernelLevels (RepKLevel RepKLevelList)
open IxVM.Refinement.Decl (RawExprRep RawContext RawTypeAt RawDeltaAt RawSignatureTrace
  RawDomainTraces RawFieldTraces)

/-- **The checked walk, with its raw walk**: the fold and the flags of `walk_open_checked`, and
for the same levels `lus` the signature traces of the raw telescope's fields `0..K` over the
run's loads, with the zero-set agreement of each level with its field's signature. -/
theorem walk_open_traced (rawKey : _root_.Address → KKey) [∀ a, Resolved (rawKey a)]
    (c : ScopedCtx) (hc : ScopedCoreFacts c) (Γ0 : Nat → KExpr) (rootCalls : List (Call F)) :
    ∀ (K : Nat) {x_rc x_ty x_ctx x_deps r : SourceValue F} {h h' : Heap F}
      {calls : List (Call F)} (k : F), ZMod.val k = K → CoreGood c calls →
      (∀ cl ∈ calls, cl ∈ rootCalls) →
      ObsFn W "KernelGuard::proj_walk_checked" [x_rc, x_ty, x_ctx, .field k, x_deps] h r h'
        calls →
      ∀ (d : Nat) (Γ : Nat → KExpr) (E : KExpr) (kr : Nat) (R : KExpr) (ls : List KLevel)
        (context : List KExpr) (kraw : Nat) (S : KExpr),
        c.rc h x_rc → c.types Γ h d x_ctx → c.tm d Γ h E x_ty → Tm c.κ 0 Γ0 h kr R x_ty →
        RepKLevelList h ls x_deps →
        RawContext rawKey h context x_ctx → RawExprRep rawKey h kraw S x_ty →
        (∃ x y z, loadValue h x_ty = .ok (.construct "KernelTypes::KExprNode" "Forall" [x, y, z])) ∧
        ∃ (lus : List KLevel) (flags : List Bool) (sigs : List KLevel),
          lus.length = K + 1 ∧ flags.length = K ∧
          RepKLevel h' ((ls ++ selDeps lus flags).foldl (fun a b => Ix.Kernel.Level.max a b)
            (lus.getD K .zero)) r ∧
          (∀ j, j < K → flags.getD j false = false →
            ∀ (bs : List (KExpr × Ix.Kernel.BinderMeta)) (rest : KExpr),
              R.stripPis (j + 1) = some (bs, rest) → rest.hasLooseBVar 0 = false) ∧
          RawDomainTraces (RawTypeAt c rawKey rootCalls) (RawDeltaAt c rawKey rootCalls)
            (K + 1) context S sigs ∧
          ∀ j, j ≤ K → ∀ φ : Ix.Kernel.LevelParam → Nat,
            Ix.Kernel.Level.eval φ (lus.getD j .zero) = 0 ↔
              Ix.Kernel.Level.eval φ (sigs.getD j .zero) = 0 := by
  intro K x_rc x_ty x_ctx x_deps r h h' calls k hk good
  exact walk_open_traced_ih rawKey c hc.base Γ0 rootCalls K k hk good (hc.ih calls)

/-- **The projection guard at a use, with its raw walk** (module docstring). The constructor
load is the run's own `get_ci_cprj`; `S` is the raw telescope its type pointer reads as. -/
theorem proj_guard_traced (rawKey : _root_.Address → KKey) [∀ a, Resolved (rawKey a)]
    (c : ScopedCtx) (hc : ScopedCoreFacts c)
    {x_rc bp r : SourceValue F} {i f : F} {h h' : Heap F} {calls : List (Call F)}
    (good : CoreGood c calls)
    (ev : ObsFn W "KernelInfer::proj_guard" [x_rc, bp, .field i, .field f] h r h' calls)
    (hrc : c.rc h x_rc)
    {nm : KKey} {k : Nat} {T : KExpr} {nP nF : Nat}
    (hload : ∀ (ptr : SourceValue F) (m : Heap F) (cs : List (Call F)),
      ObsFn W "Ingress::get_ci_cprj" [bp, .field i, .field 0] h ptr m cs →
      (∀ cl ∈ cs, cl ∈ calls) →
      CIPtrRep c.κ m ptr (.ctorInfo ⟨nm, List.range k, T⟩ nP nF))
    (hf : ZMod.val f < nF)
    {g : KLevel} (hg : RepKLevel h' g r) :
    (∃ (ptr ity np ni n v w₁ w₅ w₆ w₇ w₈ : SourceValue F) (m₀ m₁ m₂ : Heap F)
        (cs₁ cs₂ : List (Call F)),
      Heap.Extends h m₀ ∧
      ObsFn W "Ingress::get_ci_iprj" [bp, .field i] m₀ ptr m₁ cs₁ ∧ (∀ cl ∈ cs₁, cl ∈ calls) ∧
      loadValue m₁ ptr = .ok (.construct "KernelTypes::KConstantInfo" "Induct"
        [w₁, ity, np, ni, w₅, w₆, w₇, w₈]) ∧
      evalBinOp .add np ni = .ok n ∧
      ObsFn W "KernelInfer::is_inductive_prop" [x_rc, ity, n] m₁ v m₂ cs₂ ∧
      (∀ cl ∈ cs₂, cl ∈ calls) ∧ v ≠ .field 1) ∨
    ∃ (lus : List KLevel) (flags : List Bool) (sigs : List KLevel) (S : KExpr)
      (ptr x_cty w₁ w₃ w₄ w₅ w₆ w₇ w₈ : SourceValue F) (m : Heap F) (cs₀ : List (Call F)),
      g = (List.range (ZMod.val f)).foldl
          (fun acc j => if flags.getD j false then Ix.Kernel.Level.max acc (lus.getD j .zero)
            else acc) (lus.getD (ZMod.val f) .zero) ∧
      (∀ j, j < ZMod.val f → Ix.Kernel.structUsedLater T nP j = true →
        flags.getD j false = true) ∧
      ObsFn W "Ingress::get_ci_cprj" [bp, .field i, .field 0] h ptr m cs₀ ∧
      (∀ cl ∈ cs₀, cl ∈ calls) ∧
      loadValue m ptr = .ok (.construct "KernelTypes::KConstantInfo" "Ctor"
        [w₁, x_cty, w₃, w₄, w₅, w₆, w₇, w₈]) ∧
      RawExprRep rawKey m 0 S x_cty ∧
      RawFieldTraces (RawTypeAt c rawKey calls) (RawDeltaAt c rawKey calls)
        nP (ZMod.val f + 1) [] S sigs ∧
      ∀ j, j ≤ ZMod.val f → ∀ φ : Ix.Kernel.LevelParam → Nat,
        Ix.Kernel.Level.eval φ (lus.getD j .zero) = 0 ↔
          Ix.Kernel.Level.eval φ (sigs.getD j .zero) = 0 := by
  rcases proj_guard_traced_ih rawKey c hc.base good (hc.ih calls) ev hrc
      (cv := ⟨nm, List.range k, T⟩) (fun ptr m cs ev' hs _ => hload ptr m cs ev' hs) hf hg with
    ⟨ptr, ity, np, ni, n, v, w₁, w₅, w₆, w₇, w₈, m₀, m₁, m₂, cs₁, cs₂, e0, l1, s1, ld, op, l2, s2,
      hne, -, -⟩ | used
  · exact Or.inl ⟨ptr, ity, np, ni, n, v, w₁, w₅, w₆, w₇, w₈, m₀, m₁, m₂, cs₁, cs₂, e0, l1, s1,
      ld, op, l2, s2, hne⟩
  · exact Or.inr used

end IxVM.Refinement.Core.GuardWalk
