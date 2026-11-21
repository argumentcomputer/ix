import IxVMRefinement.Assembly.TypingRecLate
import IxVMRefinement.Decl.DeclSpecs

/-! # The parent family the circuit read at a recursor record

The native recursor route of `check_recursor_member` (`Assembly.native_rec_actual_parent_route`)
finds the parent family by `rec_to_parent_addr` on the record's type, loads it with `get_ci`,
and tests its block with `block_is_modeled`, which answers `0`. `recParent_of_route` reads that
off at a prefix with the standing invariant: the parent's key is stored, as a former (the type
is represented, so its constants' keys resolve, and a resolved key is stored); the store's
record at the parent is an inductive projection (`inductRecord`); its block is native
(`nativeAt_of_route`). The inputs are the three runs of the route, the type's representation
under the prefix keying at the route's heap, and that the parent's key is no basis name.
-/

universe u

set_option linter.unusedVariables false

namespace IxVM.Refinement.Typing

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Aiur.Library
open IxVM (F)
open IxVM.Consistency
open Ix.Kernel (ConstantInfo ConstantVal)

/-- The domain of a binder of a term whose keys resolve has resolved keys. -/
theorem keysResolved_piDomAt :
    ∀ (n : Nat) {e dom : Core.KExpr}, Core.KeysResolved e → Core.piDomAt n e = some dom →
      Core.KeysResolved dom
  | 0, .forallE ty _ _, _, hr, hd => by
    simp only [Core.piDomAt, Option.some.injEq] at hd
    subst hd
    exact hr.1
  | n + 1, .forallE _ b _, _, hr, hd => by
    simp only [Core.piDomAt] at hd
    exact keysResolved_piDomAt n hr.2 hd
  | 0, .bvar _, _, _, hd | 0, .fvar _ _, _, _, hd | 0, .sort _, _, _, hd
  | 0, .const _ _, _, _, hd | 0, .app _ _, _, _, hd | 0, .lam _ _ _, _, _, hd
  | 0, .letE _ _ _ _, _, _, hd | 0, .lit _, _, _, hd | 0, .proj _ _ _, _, _, hd
  | _ + 1, .bvar _, _, _, hd | _ + 1, .fvar _ _, _, _, hd | _ + 1, .sort _, _, _, hd
  | _ + 1, .const _ _, _, _, hd | _ + 1, .app _ _, _, _, hd | _ + 1, .lam _ _ _, _, _, hd
  | _ + 1, .letE _ _ _ _, _, _, hd | _ + 1, .lit _, _, _, hd
  | _ + 1, .proj _ _ _, _, _, hd => by simp [Core.piDomAt] at hd

/-- The head constant of a term whose keys resolve has a resolved key. -/
theorem keysResolved_getAppFn :
    ∀ {e : Core.KExpr} {k : Core.KKey} {us : List Core.KLevel}, Core.KeysResolved e →
      e.getAppFn = .const k us → k ≠ Core.unresolvedKey
  | .const k' us', k, us, hr, hf => by
    simp only [Ix.Kernel.Expr.getAppFn, Ix.Kernel.Expr.const.injEq] at hf
    obtain ⟨rfl, -⟩ := hf
    exact hr
  | .app f _, k, us, hr, hf => by
    simp only [Ix.Kernel.Expr.getAppFn] at hf
    exact keysResolved_getAppFn hr.1 hf
  | .bvar _, _, _, _, hf | .fvar _ _, _, _, _, hf | .sort _, _, _, _, hf
  | .lam _ _ _, _, _, _, hf | .forallE _ _ _, _, _, _, hf | .letE _ _ _ _, _, _, _, hf
  | .lit _, _, _, _, hf | .proj _ _ _, _, _, _, hf => by
    simp [Ix.Kernel.Expr.getAppFn] at hf

/-- **The parent the native recursor route read, at a prefix with the standing invariant.**
The route's three runs (`rec_to_parent_addr` on the record's type with its four counts,
`get_ci` at the result returning an inductive, `block_is_modeled` at its block answering `0`),
within calls good for the store; the type represented under the prefix keying at the first
run's heap; the parent's key no basis name. Then the parent is a stored former whose record
is an inductive projection of a native block. -/
theorem recParent_of_route {E : Ixon.Env} {t : Ix.Kernel.RoleTable} {lim : Option Nat}
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
    ∃ P ip, RecParent t E env P ip := by
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
  rw [hkey] at hfci hr
  obtain ⟨cm, b, i', hcm, hb, -, hinfo⟩ := hinv.loads.inductRecord parent ptr h₂ h₃ cs₂ a nl pty
    np ni nc pu blk idx ev₂ trivial hne (hgood.sub hs₂) ha hld
  refine ⟨Core.ixAddr a, ⟨(ZMod.val i').toUInt64, Core.ixAddr b⟩,
    ⟨cv, caps, hfci⟩, hr, ⟨cm, hcm, hinfo⟩, ?_⟩
  exact nativeAt_of_route (c := ⟨E, env, t, lim⟩) ev₃ hs₃ hgood hb

end IxVM.Refinement.Typing
