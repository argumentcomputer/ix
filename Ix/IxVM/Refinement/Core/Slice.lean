import Ix.IxVM.Refinement.Core.DefEq
import IxC.Kernel.Model.Rules.Sound
import IxC.Kernel.Audit.Axioms

/-! # The vertical slice, to a fact in the model

Spike S3. `whnf_model`: an observed derivation of IxVM's `whnf` on a
represented term either hashed a collision, or its result represents a reduct
whose reading is the input's, in every model of the environment
(`Ix.Kernel.Model.Rules.red_sound`). Together with the step lemmas and the
induction (`Ix.IxVM.Refinement.Core.Whnf`), this is the slice of plan 8.7 S3,
under the assumptions collected in `Assumed` and the fragment hypotheses of
`Good`.

Also here: the certified β step of the rules (`red_beta_certified`), which is
what IxVM's β has to produce at a binder whose datum may be a proposition
(lane s2's PM-C, "Fix A"), and `Infer.toIO`, the kernel-side lemma that turns
the certificate IxVM's full-grade inference would compute into the io-grade
certificate the rule asks for. -/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Library
open Ix.Kernel.Rules (Red DefEq Infer Grade)

universe w

/-! ## The induction -/

/-- **The induction skeleton**: every observed derivation of a function of the
slice satisfies its spec, given the specs the slice assumes. One strong
induction on the size of the derivation (the length of its call list), for all
functions at once; each case is that function's step lemma. -/
theorem core_sound (c : Ctx) (hA : Assumed c) :
    ∀ n args h r h' calls, ObsFn W n args h r h' calls → CoreSpecs c n args h r h' calls := by
  apply ObsFn.strong_induction
  intro n args h r h' calls ev ih
  exact {
    whnf := fun hn => by subst hn; exact whnf_step c ev ih
    whnfCore := fun hn => by subst hn; exact whnfCore_step c ev ih
    withSpine := fun hn => by subst hn; exact withSpine_step c hA ev ih
    applyBeta := fun hn => by subst hn; exact applyBeta_step c hA ev ih
    constHead := fun hn => by subst hn; exact constHead_step c hA ev ih
    applySpine := fun hn => by subst hn; exact applySpine_step c ev ih
    peel := fun hn => by subst hn; exact peel_step c ev ih
    collect := fun hn => by subst hn; exact collect_step c hA ev ih
    instLevels := fun hn => by subst hn; exact instLevels_step ev
    defEq := fun hn => by subst hn; exact defEq_step c ev ih
    defEqCore := fun hn => by subst hn; exact defEqCore_step c ev ih
    defEqOrdered := fun hn => by subst hn; exact defEqOrdered_step c ev ih
    tryApp := fun hn => by subst hn; exact tryApp_step c hA ev ih
    deArgs := fun hn => by subst hn; exact deArgs_step c ev ih }

/-- **`whnf` is a reduction, or the run hashed a collision**: for every observed
derivation of `whnf(rc, e, types) = e'` in the fragment, either the run hashed a
second preimage of the view's data, or for every opening depth and ghost
context at which `e` represents `E`, `e'` represents some `E'` with
`Red env d E E'`. -/
theorem whnf_red (c : Ctx) (hA : Assumed c) {rc e types : SourceValue F} {h h' : Heap F}
    {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::whnf" [rc, e, types] h r h' calls)
    (loads : LoadsInFrag c calls) (natives : NoNatives calls)
    (bound : calls.length < 4294967296) :
    c.V.HashedCollision [] calls ∨
      ∀ d Γ E, RepE c.κ d Γ h E e → ∃ E', RepE c.κ d Γ h' E' r ∧ Red c.env d E E' := by
  by_cases hc : c.V.HashedCollision [] calls
  · exact .inl hc
  · exact .inr ((core_sound c hA _ _ _ _ _ _ ev).whnf rfl rc e types rfl
      ⟨hc, loads, natives, bound⟩)

/-- **A nonzero `is_def_eq` is `DefEq`, or the run hashed a collision**, in the
fragment (fast path: same-head spines, pairwise). -/
theorem defEq_of_run (c : Ctx) (hA : Assumed c) {rc a b types : SourceValue F}
    {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::k_is_def_eq" [rc, a, b, types] h r h' calls)
    (loads : LoadsInFrag c calls) (natives : NoNatives calls)
    (bound : calls.length < 4294967296) (hr : r ≠ .field 0) :
    c.V.HashedCollision [] calls ∨
      ∀ d Γ A B, RepE c.κ d Γ h A a → RepE c.κ d Γ h B b → DefEq c.env d A B := by
  by_cases hc : c.V.HashedCollision [] calls
  · exact .inl hc
  · exact .inr ((core_sound c hA _ _ _ _ _ _ ev).defEq rfl rc a b types rfl
      ⟨hc, loads, natives, bound⟩ hr)

/-- **`is_def_eq` to a fact in the model**: a nonzero answer on represented,
framed, readable, graded terms means equal interpretations (`DefEqSem`). -/
theorem defEq_model (c : Ctx) (hA : Assumed c) {V : Type w} [Ix.Kernel.SetTheory V]
    {m : Ix.Kernel.Model.EnvModel V c.env} {φ : Ix.Kernel.LevelParam → Nat}
    (hin : Ix.Kernel.Model.Rules.RulesInputs V m φ)
    {rc a b types : SourceValue F} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelDefEq::k_is_def_eq" [rc, a, b, types] h r h' calls)
    (loads : LoadsInFrag c calls) (natives : NoNatives calls)
    (bound : calls.length < 4294967296) (hr : r ≠ .field 0) :
    c.V.HashedCollision [] calls ∨
      ∀ d Γ A B, RepE c.κ d Γ h A a → RepE c.κ d Γ h B b →
        Ix.Kernel.Model.Rules.DefEqSem m φ d A B := by
  rcases defEq_of_run c hA ev loads natives bound hr with hc | hde
  · exact .inl hc
  · exact .inr fun d Γ A B hA' hB' => Ix.Kernel.Model.Rules.defeq_sound hin (hde d Γ A B hA' hB')

/-- **`whnf` to a fact in the model.** Under the slice's assumptions and fragment
hypotheses, an observed derivation of `whnf(rc, e, types) = e'` either hashed a
second preimage of the view's data, or for every opening depth and ghost
context at which `e` represents `E`, `e'` represents some `E'` such that, in
every set-theoretic model of the environment satisfying the rules' inputs, a
framed, readable, graded `E` has a reduct `E'` that reads, is graded, and has
the same interpretation (`RedSem`). -/
theorem whnf_model (c : Ctx) (hA : Assumed c) {V : Type w} [Ix.Kernel.SetTheory V]
    {m : Ix.Kernel.Model.EnvModel V c.env} {φ : Ix.Kernel.LevelParam → Nat}
    (hin : Ix.Kernel.Model.Rules.RulesInputs V m φ)
    {rc e types : SourceValue F} {h h' : Heap F} {r : SourceValue F} {calls : List (Call F)}
    (ev : ObsFn W "KernelWhnf::whnf" [rc, e, types] h r h' calls)
    (loads : LoadsInFrag c calls) (natives : NoNatives calls)
    (bound : calls.length < 4294967296) :
    c.V.HashedCollision [] calls ∨
      ∀ d Γ E, RepE c.κ d Γ h E e →
        ∃ E', RepE c.κ d Γ h' E' r ∧ Ix.Kernel.Model.Rules.RedSem m φ d E E' := by
  rcases whnf_red c hA ev loads natives bound with hc | hred
  · exact .inl hc
  · refine .inr fun d Γ E hE => ?_
    obtain ⟨E', hE', hr⟩ := hred d Γ E hE
    exact ⟨E', hE', Ix.Kernel.Model.Rules.red_sound hin hr⟩

/-! ## Fix A's certified branch (kernel side) -/

/-- **The certified β step under a spine**: at a binder of any datum, β with
the argument's io-grade type definitionally equal to the domain. -/
theorem red_beta_certified {env : Ix.Kernel.Env .anon} {d : Nat} {T B A TA : KExpr}
    {mb : Ix.Kernel.BinderMeta} (rest : List KExpr)
    (hta : Infer env .io d A TA) (hd : DefEq env d TA T) :
    Red env d (K.mkAppN (.app (.lam T B mb) A) rest) (K.mkAppN (B.instantiate1 A) rest) :=
  K.red_mkAppN rest (.beta hta hd)

/-- **A full-grade inference is an io-grade one**: the io grade drops checks
and adds `appSkip`. IxVM's `k_infer` is the full grade, `Red.beta`'s
certificate is io-grade. -/
theorem Infer.toIO {env : Ix.Kernel.Env .anon} :
    ∀ {g : Grade} {d : Nat} {e t : KExpr}, Infer env g d e t → g = .full → Infer env .io d e t
  | _, _, _, _, .sort, _ => .sort
  | _, _, _, _, .fvar hlt, _ => .fvar hlt
  | _, _, _, _, .const hf ht hus, _ => .const hf ht hus
  | _, _, _, _, .natLit hs, _ => .natLit hs
  | _, _, _, _, .strLit hs, _ => .strLit hs
  | _, _, _, _, .forallE hs hu hbs hv hz, hg =>
    .forallE (Infer.toIO hs hg) hu (Infer.toIO hbs hg) hv hz
  | _, _, _, _, .lam hs hu hbt hchain hbtt hv hz, hg =>
    .lam (fun _ => hs hg) (fun _ => hu hg) (Infer.toIO hbt hg) hchain hbtt hv hz
  | _, _, _, _, .app htf hw hta hd, hg => .app (Infer.toIO htf hg) hw (Infer.toIO hta hg) hd
  | _, _, _, _, .appSkip _ _ _, hg => absurd hg (by decide)
  | _, _, _, _, .proj htpe hte hhead hent hlen hus hprop, hg =>
    .proj (Infer.toIO htpe hg) hte hhead hent hlen hus hprop

end IxVM.Refinement.Core

#guard_module_axioms Ix.IxVM.Refinement.Core.Obs Ix.IxVM.Refinement.Core.Rep
  Ix.IxVM.Refinement.Core.Specs Ix.IxVM.Refinement.Core.Whnf Ix.IxVM.Refinement.Core.DefEq
