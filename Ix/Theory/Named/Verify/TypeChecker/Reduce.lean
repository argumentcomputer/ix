/-
Adapted for Ix: namespace, imports, and shared universe semantics.
SPDX-License-Identifier: Apache-2.0
Source attribution and revision: Ix/Theory/Named/NOTICE.
-/

import Ix.Theory.Named.Verify.TypeChecker.Basic

namespace Ix.Theory.Named.TypeChecker.Inner
open Lean hiding Environment Exception
open Kernel

theorem reduceNative.WF :
    (reduceNative env e).WF fun oe => ∀ e₁, oe = some e₁ → False := by
  unfold reduceNative; split <;> [skip; exact .pure nofun]
  split <;> [exact .throw; skip]; split <;> [exact .throw; exact .pure nofun]

theorem rawNatLitExt?.WF {c : VContext} (H : rawNatLitExt? e = some n) (he : c.TrExprS e e') :
    c.venv.contains ``Nat ∧ e' = .natLit n := by
  have : c.TrExprS (.lit (.natVal n)) e' := by
    unfold rawNatLitExt? at H; split at H <;> rename_i h
    · cases H; have := he.eqv h; exact .lit (this.nat_of_natZero c.Ewf c.hasPrimitives) this
    · unfold Expr.rawNatLit? at H; split at H <;> cases H; exact he
  have hn := this.lit_has_type
  exact ⟨hn, this.unique (by trivial) (TrExprS.natLit c.hasPrimitives hn n).1⟩

/-- `checkNatSize` either throws or leaves the state alone, so it is transparent to any
postcondition that already holds. -/
theorem checkNatSize.WF {c : VContext} {s : VState} {Q : Unit → VState → Prop} (H : Q () s) :
    RecM.WF c s (checkNatSize n) Q := by
  unfold checkNatSize; exact .readThe (by split <;> [exact .throw; exact .pure H])

@[inherit_doc checkNatSize.WF]
theorem checkCountArg.WF {c : VContext} {s : VState} {Q : Unit → VState → Prop} (H : Q () s) :
    RecM.WF c s (checkCountArg n op) Q := by
  unfold checkCountArg; split <;> [exact .throw; exact .pure H]

@[inherit_doc checkNatSize.WF]
theorem checkLitSize.WF {c : VContext} {s : VState} {Q : Unit → VState → Prop} (H : Q () s) :
    RecM.WF c s (checkLitSize l) Q := by
  unfold checkLitSize; split <;> [exact checkNatSize.WF H; exact .pure H]

@[inherit_doc checkNatSize.WF]
theorem checkNatSizeIf.WF {c : VContext} {s : VState} {Q : Unit → VState → Prop} (H : Q () s) :
    RecM.WF c s (checkNatSizeIf checkSize n) Q := by
  unfold checkNatSizeIf; split <;> [exact checkNatSize.WF H; exact .pure H]

@[inherit_doc checkNatSize.WF]
theorem checkPowSize.WF {c : VContext} {s : VState} {Q : Unit → VState → Prop} (H : Q () s) :
    RecM.WF c s (checkPowSize base exp) Q := by
  unfold checkPowSize
  exact (checkCountArg.WF H).bind fun _ _ _ H =>
    .readThe (by split <;> [exact .throw; exact .pure H])

@[inherit_doc checkNatSize.WF]
theorem checkShiftLeftSize.WF {c : VContext} {s : VState} {Q : Unit → VState → Prop} (H : Q () s) :
    RecM.WF c s (checkShiftLeftSize v shift) Q := by
  unfold checkShiftLeftSize
  split <;> [exact (checkCountArg.WF H).bind fun _ _ _ H => checkNatSize.WF H; exact .pure H]

/-- The shared skeleton of the binary `Nat` reductions: reduce both operands to literals, run a
size `check` that can only throw, and return the literal `f v1 v2`. -/
theorem reduceBinNatOpCore.WF {c : VContext} {check : Nat → Nat → RecM Unit}
    (hcheck : ∀ {v1 v2 s'} {Q : Unit → VState → Prop}, Q () s' → RecM.WF c s' (check v1 v2) Q)
    (he : c.TrExprS (.app (.app (.const fc ls) a) b) e')
    (hprim : Environment.primitives.contains fc)
    (heval : c.venv.ReflectsNatNatNat fc f) :
    RecM.WF c s (do
        let some v1 := rawNatLitExt? (← whnf a) | return none
        let some v2 := rawNatLitExt? (← whnf b) | return none
        check v1 v2
        return some <| .lit <| .natVal <| f v1 v2)
      fun oe _ => ∀ e₁, oe = some e₁ →
        c.FVarsBelow (.app (.app (.const fc ls) a) b) e₁ ∧ c.TrExpr e₁ e' := by
  let .app hb1 hb2 hf hb := he
  let .app ha1 ha2 hf ha := hf
  let .const h1 h2 h3 := hf
  refine (whnf.WF ha).bind fun a₁ _ _ ⟨a1, _, a2, a3⟩ => ?_
  split <;> [rename_i v1 h; exact .pure nofun]
  obtain ⟨hn, rfl⟩ := rawNatLitExt?.WF h a2
  refine (whnf.WF hb).bind fun b₁ _ _ ⟨b1, _, b2, b3⟩ => ?_
  split <;> [rename_i v2 h; exact .pure nofun]
  cases (rawNatLitExt?.WF h b2).2
  refine (hcheck (Q := fun _ _ => True) trivial).bind fun _ _ _ _ => ?_
  refine .pure ?_; rintro _ ⟨⟩; refine ⟨fun _ _ _ => trivial, ?_⟩
  have ⟨ci, c1, _⟩ := c.trenv.find?_iff.2 ⟨_, h1⟩
  have ⟨_, c3⟩ := c.safePrimitives c1 hprim
  have ⟨_, d1, d2, d3⟩ := c.trenv.find?_uniq c1 h1
  simp [c3] at d2; simp [← d2] at h3; simp [h3] at h2; subst h2
  refine ⟨_, (TrExprS.natLit c.hasPrimitives hn _).1, ?_⟩
  have := heval ⟨_, h1⟩ v1 v2 |>.instL (U' := c.lparams.length) (ls := []) nofun
  simp [VExpr.instL] at this
  refine this.weak0 c.Ewf (Γ := c.vlctx.toCtx) |>.symm.trans c.Ewf c.Δwf ?_
  have a3 := a3.of_r c.Ewf c.Δwf ha2
  have b3 := b3.of_r c.Ewf c.Δwf hb2
  have := ha1.appDF a3 |>.toU.of_r c.Ewf c.Δwf hb1
  exact ⟨_, .appDF this b3⟩

theorem reduceBinNatOp.WF {c : VContext}
    (he : c.TrExprS (.app (.app (.const fc ls) a) b) e')
    (hprim : Environment.primitives.contains fc)
    (heval : c.venv.ReflectsNatNatNat fc f) :
    RecM.WF c s (reduceBinNatOp f a b checkSize) fun oe _ => ∀ e₁, oe = some e₁ →
      c.FVarsBelow (.app (.app (.const fc ls) a) b) e₁ ∧ c.TrExpr e₁ e' := by
  unfold reduceBinNatOp
  exact reduceBinNatOpCore.WF (fun H => checkNatSizeIf.WF H) he hprim heval

theorem reducePow.WF {c : VContext}
    (he : c.TrExprS (.app (.app (.const fc ls) a) b) e')
    (hprim : Environment.primitives.contains fc)
    (heval : c.venv.ReflectsNatNatNat fc Nat.pow) :
    RecM.WF c s (reducePow a b) fun oe _ => ∀ e₁, oe = some e₁ →
      c.FVarsBelow (.app (.app (.const fc ls) a) b) e₁ ∧ c.TrExpr e₁ e' := by
  unfold reducePow
  exact reduceBinNatOpCore.WF (fun H => checkPowSize.WF H) he hprim heval

theorem reduceShiftLeft.WF {c : VContext}
    (he : c.TrExprS (.app (.app (.const fc ls) a) b) e')
    (hprim : Environment.primitives.contains fc)
    (heval : c.venv.ReflectsNatNatNat fc (· <<< ·)) :
    RecM.WF c s (reduceShiftLeft a b) fun oe _ => ∀ e₁, oe = some e₁ →
      c.FVarsBelow (.app (.app (.const fc ls) a) b) e₁ ∧ c.TrExpr e₁ e' := by
  unfold reduceShiftLeft
  exact reduceBinNatOpCore.WF (fun H => checkShiftLeftSize.WF H) he hprim heval

theorem reduceBinNatPred.WF {c : VContext}
    (he : c.TrExprS (.app (.app (.const fc ls) a) b) e')
    (hprim : Environment.primitives.contains fc)
    (heval : c.venv.ReflectsNatNatBool fc f) :
    RecM.WF c s (reduceBinNatPred f a b) fun oe _ => ∀ e₁, oe = some e₁ →
      c.FVarsBelow (.app (.app (.const fc ls) a) b) e₁ ∧ c.TrExpr e₁ e' := by
  let .app hb1 hb2 hf hb := he
  let .app ha1 ha2 hf ha := hf
  let .const h1 h2 h3 := hf
  unfold reduceBinNatPred
  refine (whnf.WF ha).bind fun a₁ _ _ ⟨a1, _, a2, a3⟩ => ?_
  split <;> [rename_i v1 h; exact .pure nofun]; cases (rawNatLitExt?.WF h a2).2
  refine (whnf.WF hb).bind fun b₁ _ _ ⟨b1, _, b2, b3⟩ => ?_
  split <;> [rename_i v2 h; exact .pure nofun]; cases (rawNatLitExt?.WF h b2).2
  refine .pure ?_; rintro _ ⟨⟩; refine ⟨fun _ _ _ => .boolLit, ?_⟩
  have ⟨ci, c1, _⟩ := c.trenv.find?_iff.2 ⟨_, h1⟩
  have ⟨_, c3⟩ := c.safePrimitives c1 hprim
  have ⟨_, d1, d2, d3⟩ := c.trenv.find?_uniq c1 h1
  simp [c3] at d2; simp [← d2] at h3; simp [h3] at h2; subst h2
  have := heval ⟨_, h1⟩ v1 v2 |>.instL (U' := c.lparams.length) (ls := []) nofun
  simp [VExpr.instL] at this
  refine ⟨_, (TrExprS.boolLit c.hasPrimitives ?_ _).1, ?_⟩
  · let ⟨_, H⟩ := this
    exact VExpr.WF.boolLit_has_type c.Ewf c.hasPrimitives (Γ := []) trivial ⟨_, H.hasType.2⟩
  refine this.weak0 c.Ewf (Γ := c.vlctx.toCtx) |>.symm.trans c.Ewf c.Δwf ?_
  have a3 := a3.of_r c.Ewf c.Δwf ha2
  have b3 := b3.of_r c.Ewf c.Δwf hb2
  have := ha1.appDF a3 |>.toU.of_r c.Ewf c.Δwf hb1
  exact  ⟨_, .appDF this b3⟩

theorem reduceNat.WF {c : VContext} (he : c.TrExprS e e') :
    RecM.WF c s (reduceNat e) fun oe _ => ∀ e₁, oe = some e₁ →
      c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  generalize hP : (fun oe => _) = P
  refine let prims := _; have hprims : Environment.primitives = .ofList prims := rfl; ?_
  replace hprims {a} : Environment.primitives.contains a ↔ a ∈ prims := by
    simp [hprims, NameSet.contains, NameSet.ofList]
  unfold reduceNat; extract_lets nargs F1 fn
  cases h1 : nargs == 1 <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · cases nargs == 2 <;> [exact hP ▸ .pure nofun; simp only [↓reduceIte]]
    split <;> [rename_i f ls a b; exact hP ▸ .pure nofun]
    have hfun checkSize {g fc G} (hprim : fc ∈ prims)
        (heval : c.venv.ReflectsNatNatNat fc g) (hG : RecM.WF c s G P) :
        RecM.WF c s (do if f == fc then {return ← reduceBinNatOp g a b checkSize}; G) P := by
      split <;> [rename_i h; exact hG]
      simp at h ⊢; subst h
      exact hP ▸ reduceBinNatOp.WF he (hprims.2 hprim) heval
    have hpow {fc G} (hprim : fc ∈ prims)
        (heval : c.venv.ReflectsNatNatNat fc Nat.pow) (hG : RecM.WF c s G P) :
        RecM.WF c s (do if f == fc then {return ← reducePow a b}; G) P := by
      split <;> [rename_i h; exact hG]
      simp at h ⊢; subst h
      exact hP ▸ reducePow.WF he (hprims.2 hprim) heval
    have hshl {fc G} (hprim : fc ∈ prims)
        (heval : c.venv.ReflectsNatNatNat fc (· <<< ·)) (hG : RecM.WF c s G P) :
        RecM.WF c s (do if f == fc then {return ← reduceShiftLeft a b}; G) P := by
      split <;> [rename_i h; exact hG]
      simp at h ⊢; subst h
      exact hP ▸ reduceShiftLeft.WF he (hprims.2 hprim) heval
    have hpred {g fc G} (hprim : fc ∈ prims)
        (heval : c.venv.ReflectsNatNatBool fc g) (hG : RecM.WF c s G P) :
        RecM.WF c s (do if f == fc then {return ← reduceBinNatPred g a b}; G) P := by
      split <;> [rename_i h; exact hG]
      simp at h ⊢; subst h
      exact hP ▸ reduceBinNatPred.WF he (hprims.2 hprim) heval
    apply hfun true (by simp [prims]) c.hasPrimitives.natAdd
    apply hfun true (by simp [prims]) c.hasPrimitives.natSub
    apply hfun true (by simp [prims]) c.hasPrimitives.natMul
    apply hpow (by simp [prims]) c.hasPrimitives.natPow
    apply hfun false (by simp [prims]) c.hasPrimitives.natGcd
    apply hfun false (by simp [prims]) c.hasPrimitives.natMod
    apply hfun false (by simp [prims]) c.hasPrimitives.natDiv
    apply hpred (by simp [prims]) c.hasPrimitives.natBEq
    apply hpred (by simp [prims]) c.hasPrimitives.natBLE
    apply hfun false (by simp [prims]) c.hasPrimitives.natLAnd
    apply hfun false (by simp [prims]) c.hasPrimitives.natLOr
    apply hfun false (by simp [prims]) c.hasPrimitives.natXor
    apply hshl (by simp [prims]) c.hasPrimitives.natShiftLeft
    apply hfun false (by simp [prims]) c.hasPrimitives.natShiftRight
    exact hP ▸ .pure nofun
  · split <;> [rename_i h2; exact hP ▸ .pure nofun]
    simp [nargs, Expr.getAppNumArgs_eq] at h1; subst fn
    let .app f a := e; simp [Expr.appFn!, Expr.structuralEq_const] at h2 ⊢; subst h2
    let .app ha1 ha2 hf ha := he
    let .const h1 h2 h3 := hf
    refine (whnf.WF ha).bind fun a₁ _ _ ⟨a1, _, a2, a3⟩ => ?_
    split <;> [rename_i n h; exact hP ▸ .pure nofun]
    obtain ⟨hn, rfl⟩ := rawNatLitExt?.WF h a2
    refine hP ▸ (checkNatSize.WF (Q := fun _ _ => True) trivial).map fun _ _ _ _ => ?_
    rintro _ ⟨⟩; refine ⟨fun _ _ _ => trivial, ?_⟩
    have ⟨ci, c1, _⟩ := c.trenv.find?_iff.2 ⟨_, h1⟩
    have ⟨c2, c3⟩ := c.safePrimitives c1 <| hprims.2 (by simp [prims])
    have ⟨d1, d2, d3⟩ := c.trenv.find?_uniq c1 h1; cases h2
    refine have ⟨p1, p2⟩ := TrExprS.natLit c.hasPrimitives hn _; ⟨_, p1, ?_⟩
    refine p2.toU.symm.trans c.Ewf c.Δwf ?_
    exact ⟨_, ha1.appDF <| a3.of_r c.Ewf c.Δwf ha2⟩
