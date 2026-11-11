import IxCK.Kernel.Verify.Cached.KnotC
import IxCK.Kernel.Verify.Rules.Bridge
import IxCK.Kernel.Model.Rules.Sound
import IxCC.Src.KernelFront.Proof

/-!
# The kernel front end's relevance classes as kernel judgements (`IxKernelBridge.KernelFront`)

IxCC's front end over the certified kernel (`IxCC.Src.KernelFront`) classifies a
binder, argument or let as a proof under a zero condition when the executed kernel
core's runs give the position's type and the type's sort `Sort u`, and the condition
is `u`'s (`IxCC.Src.KernelFront.Ctx.classifyTerm_proof`, in IxCC). This module
composes that with the kernel's own theorems:

- the cached core simulates the fueled specification functions from any invariant
  memo state (`Ix.Kernel.Cached.ssimC`), so each run is an accepting specification
  run at some fuel (`infer_derives`, `whnf_derives`, `annotate_runs`: the kernel-side
  lemma the front end's design asks for, packaged);
- an accepting run is a derivation of the relational judgements
  (`Ix.Kernel.Rules.inferTypeCore_bridge`, `whnf_bridge`);
- every derivation is sound in every model meeting `RulesInputs`
  (`Ix.Kernel.Model.Rules.infer_sound`, `red_sound`).

So a `proof` class at a position is, for the kernel's annotation of the position's
term, an `Infer` derivation of its type, an `Infer` derivation of that type's type and
a `Red` derivation of the latter to `Sort u` (`classifyTerm_derivations`), and their
semantic readings in every such model (`classifyTerm_sound`): for every valuation
satisfying the opened context, the term's denotation is a member of its type's, which
is a member of `Sort u`'s. What `InferSem` assumes of the position (its frame, its
context's reading, the term's reading) is the typing-transport question the front
end's design leaves to the kernel's owners. -/

universe w

namespace IxKernelBridge.KernelFront

open Ix.Kernel Ix.Kernel.Cached Ix.Kernel.Rules Ix.Kernel.Model Ix.Kernel.Model.Rules
open Ix.Kernel.Semantics

variable {env : Env .anon}

/-- **An executed inference run is a derivation**: from an invariant memo state,
on a term well scoped at the depth, the cached core's inference run gives an
`Infer` derivation of its result, an invariant state and a well-scoped type. -/
theorem infer_derives (henv : EnvWF env) {s s' : CState .anon} (hs : CSOK .verified env s)
    {d : Nat} {e t : Expr .anon} (hw : Expr.WScoped d e)
    (h : (IxCC.Src.KernelFront.coreOf (mkFEnv env)).infer d e s = .ok (t, s')) :
    Infer env .full d e t ∧ CSOK .verified env s' ∧ Expr.WScoped d t := by
  obtain ⟨hs', v, ⟨hrel, hwv⟩, F, hF⟩ := (ssimC rfl env henv checkFuel).infer hs rfl hw t s' h
  obtain rfl : t = v := hrel
  exact ⟨inferTypeCore_bridge hF, hs', hwv⟩

/-- **An executed reduction run is a derivation** (`Red`). -/
theorem whnf_derives (henv : EnvWF env) {s s' : CState .anon} (hs : CSOK .verified env s)
    {d : Nat} {e e' : Expr .anon} (hw : Expr.WScoped d e)
    (h : (IxCC.Src.KernelFront.coreOf (mkFEnv env)).whnf d e s = .ok (e', s')) :
    Red env d e e' ∧ CSOK .verified env s' ∧ Expr.WScoped d e' := by
  obtain ⟨hs', v, ⟨hrel, hwv⟩, F, hF⟩ := (ssimC rfl env henv checkFuel).whnf hs rfl hw e' s' h
  obtain rfl : e' = v := hrel
  exact ⟨whnf_bridge hF, hs', hwv⟩

/-- **An executed annotation run is the specification's** at some fuel. -/
theorem annotate_runs (henv : EnvWF env) {s s' : CState .anon} (hs : CSOK .verified env s)
    {d : Nat} {e e' : Expr .anon} (hw : Expr.WScoped d e)
    (h : (IxCC.Src.KernelFront.coreOf (mkFEnv env)).annotate d e s = .ok (e', s')) :
    (∃ F, annotateCore .verified env F d e = .ok e') ∧ CSOK .verified env s' ∧
      Expr.WScoped d e' := by
  obtain ⟨hs', v, ⟨hrel, hwv⟩, F, hF⟩ := (ssimC rfl env henv checkFuel).annotate hs rfl hw e' s' h
  obtain rfl : e' = v := hrel
  exact ⟨⟨F, hF⟩, hs', hwv⟩

/-- **A `proof` class is a derivation.** For an environment the kernel accepted (so
well formed), from an invariant memo state, at a position whose kernel term `e` is
well scoped at the depth: the kernel's annotation `e'` of `e`, `Infer` derivations of
its type `t` and of `t`'s type `ty`, and a `Red` derivation of `ty` to `Sort u`, whose
zero condition is the class's. -/
theorem classifyTerm_derivations (henv : EnvWF env) {s s' : CState .anon}
    (hs : CSOK .verified env s) {back : Nat → Nat} {d : Nat} {e : Expr .anon}
    {w : IxCC.Src.PropWhen} (hw : Expr.WScoped d e)
    (h : ({ core := IxCC.Src.KernelFront.coreOf (mkFEnv env), back } :
      IxCC.Src.KernelFront.Ctx).classifyTerm d e s = .ok (.proof w, s')) :
    ∃ e' t ty u, (∃ F, annotateCore .verified env F d e = .ok e') ∧
      Infer env .full d e' t ∧ Infer env .full d t ty ∧ Red env d ty (.sort u) ∧
      IxCC.Src.KernelFront.condOfLevel back u = w ∧ (IxCC.Src.KernelFront.zeroCond u).isSome := by
  obtain ⟨e', s₁, t, s₂, ty, s₃, u, ha, hi, hi', hwh, hc, hz⟩ :=
    IxCC.Src.KernelFront.Ctx.classifyTerm_proof h
  obtain ⟨hA, hs₁, hw₁⟩ := annotate_runs henv hs hw ha
  obtain ⟨hI₁, hs₂, hw₂⟩ := infer_derives henv hs₁ hw₁ hi
  obtain ⟨hI₂, hs₃, hw₃⟩ := infer_derives henv hs₂ hw₂ hi'
  obtain ⟨hR, -, -⟩ := whnf_derives henv hs₃ hw₃ hwh
  exact ⟨e', t, ty, u, hA, hI₁, hI₂, hR, hc, hz⟩

/-- **A `proof` class in every model.** In every model meeting `RulesInputs` (every
strong model of the accepted environment supplies one, `RulesInputs.ofSem`): the
semantic readings of the derivations of `classifyTerm_derivations`. For every valuation
satisfying the opened context, the kernel's annotation of the position's term denotes
a member of its type, which denotes a member of `Sort u`; at a level assignment under
which the class's condition holds, `u` is zero. -/
theorem classifyTerm_sound {V : Type w} [SetTheory V] {m : EnvModel V env}
    {φ : LevelParam → Nat} (hin : RulesInputs V m φ) (henv : EnvWF env) {s s' : CState .anon}
    (hs : CSOK .verified env s) {back : Nat → Nat} {d : Nat} {e : Expr .anon}
    {w : IxCC.Src.PropWhen} (hw : Expr.WScoped d e)
    (h : ({ core := IxCC.Src.KernelFront.coreOf (mkFEnv env), back } :
      IxCC.Src.KernelFront.Ctx).classifyTerm d e s = .ok (.proof w, s')) :
    ∃ e' t ty u, (∃ F, annotateCore .verified env F d e = .ok e') ∧
      InferSem m φ .full d e' t ∧ InferSem m φ .full d t ty ∧ RedSem m φ d ty (.sort u) ∧
      IxCC.Src.KernelFront.condOfLevel back u = w := by
  obtain ⟨e', t, ty, u, hA, hI₁, hI₂, hR, hc, -⟩ := classifyTerm_derivations henv hs hw h
  exact ⟨e', t, ty, u, hA, infer_sound hin hI₁, infer_sound hin hI₂, red_sound hin hR, hc⟩

end IxKernelBridge.KernelFront
