module

public import IxC.Kernel.Model.Inductives.NativeJudge

@[expose] public section

/-!
# The constructors' binders carry the family's zero-ness

At a block that stores its declared former (`FormerStoredJ`), a derivation infers the type of the
family applied through the declared type and its reductions, so the sort it ends at is not read
off the stored type. The block's record carries instead the syntactic fact the model reads
(`ctorZeroOk`, in `FormerReadJ`): every binder of each constructor's type, and every binder of each
field domain ending in the family, carries the zero-ness datum of the family's result sort. Its
reading at each binder is the result sort's zero-ness (`PiBitsOpen`), and it survives opening the
telescope at free variables.
-/

namespace Ix.Kernel.Model

open Ix.Kernel.Semantics
open Ix.Kernel (Env Key Expr Level ConstantInfo ConstantVal PropWhen)

variable {md : Ix.Kernel.Mode}

theorem pwsAll_instantiate1 (z : PropWhen) (i : Nat) (t : Expr md) :
    ∀ (e : Expr md) (k : Nat), pwsAll z (e.instantiate1 (.fvar i t) k) = pwsAll z e
  | .forallE ty b m, k => by
    simp only [Expr.instantiate1, pwsAll, pwsAll_instantiate1 z i t b (k + 1)]
  | .bvar j, k => by
    simp only [Expr.instantiate1]
    split
    · rfl
    · split <;> rfl
  | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .app _ _, _ | .lam _ _ _, _
  | .letE _ _ _ _, _ | .lit _, _ | .proj _ _ _, _ => rfl

theorem famHead_instantiate1 (T : Key md) (i : Nat) (t : Expr md) :
    ∀ (e : Expr md) (k : Nat), famHead T (e.instantiate1 (.fvar i t) k) = famHead T e
  | .forallE ty b m, k => by
    simp only [Expr.instantiate1, famHead, famHead_instantiate1 T i t b (k + 1)]
  | .app f a, k => by
    simp only [Expr.instantiate1, famHead, famHead_instantiate1 T i t f k]
  | .bvar j, k => by
    simp only [Expr.instantiate1]
    split
    · rfl
    · split <;> rfl
  | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .lam _ _ _, _
  | .letE _ _ _ _, _ | .lit _, _ | .proj _ _ _, _ => rfl

theorem famDomOk_instantiate1 (T : Key md) (z : PropWhen) (i : Nat) (t e : Expr md) (k : Nat) :
    famDomOk T z (e.instantiate1 (.fvar i t) k) = famDomOk T z e := by
  simp only [famDomOk, famHead_instantiate1, pwsAll_instantiate1]

theorem ctorZeroOk_instantiate1 (T : Key md) (z : PropWhen) (i : Nat) (t : Expr md) :
    ∀ (e : Expr md) (k : Nat), ctorZeroOk T z (e.instantiate1 (.fvar i t) k) = ctorZeroOk T z e
  | .forallE ty b m, k => by
    simp only [Expr.instantiate1, ctorZeroOk, famDomOk_instantiate1,
      ctorZeroOk_instantiate1 T z i t b (k + 1)]
  | .bvar j, k => by
    simp only [Expr.instantiate1]
    split
    · rfl
    · split <;> rfl
  | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .app _ _, _ | .lam _ _ _, _
  | .letE _ _ _ _, _ | .lit _, _ | .proj _ _ _, _ => rfl

/-- **A constructor type's binders, opened**: each opened domain carries the zero-ness where it
ends in the family, and each binder's bit is the level's zero-ness. -/
theorem ctorZeroOk_open {T : Key md} {l : Level} :
    ∀ (n : Nat) {e : Expr md} {d : Nat} {fvs : List (Expr md)} {body : Expr md},
      ctorZeroOk T (Level.zeronessOf l) e = true → openPisAtFvars n e d = some (fvs, body) →
      (∀ x ∈ fvs, famDomOk T (Level.zeronessOf l) x.fvarTypeD = true) ∧
      ∀ φ, PiBitsOpen φ (Level.eval φ l = 0) n d e
  | 0, e, d, fvs, body, _, hop => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨rfl, -⟩ := hop
    exact ⟨fun _ h => (nomatch h), fun _ => trivial⟩
  | n + 1, .forallE dom b m, d, fvs, body, hz, hop => by
    simp only [ctorZeroOk, Bool.and_eq_true, beq_iff_eq] at hz
    obtain ⟨⟨hpw, hdom⟩, hb⟩ := hz
    simp only [openPisAtFvars] at hop
    split at hop
    · next fvs' e' hop' =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hop
      obtain ⟨rfl, -⟩ := hop
      have hb' : ctorZeroOk T (Level.zeronessOf l) (b.instantiate1 (.fvar d dom)) = true := by
        rw [ctorZeroOk_instantiate1]; exact hb
      obtain ⟨hfv, hbits⟩ := ctorZeroOk_open n hb' hop'
      refine ⟨fun x hx => ?_, fun φ => ⟨by rw [hpw, pwBit_zeronessOf], hbits φ⟩⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hdom
      · exact hfv x hx
    · exact nomatch hop
  | _ + 1, .bvar _, _, _, _, _, hop | _ + 1, .fvar _ _, _, _, _, _, hop
  | _ + 1, .sort _, _, _, _, _, hop | _ + 1, .const _ _, _, _, _, _, hop
  | _ + 1, .app _ _, _, _, _, _, hop | _ + 1, .lam _ _ _, _, _, _, _, hop
  | _ + 1, .letE _ _ _ _, _, _, _, _, hop | _ + 1, .lit _, _, _, _, _, hop
  | _ + 1, .proj _ _ _, _, _, _, _, hop => by simp [openPisAtFvars] at hop

/-- **A domain's binders all carry the zero-ness, opened**: each binder's bit is the level's
zero-ness. -/
theorem pwsAll_open {l : Level} :
    ∀ (n : Nat) {e : Expr md} {d : Nat} {fvs : List (Expr md)} {body : Expr md},
      pwsAll (Level.zeronessOf l) e = true → openPisAtFvars n e d = some (fvs, body) →
      ∀ φ, PiBitsOpen φ (Level.eval φ l = 0) n d e
  | 0, _, _, _, _, _, _ => fun _ => trivial
  | n + 1, .forallE dom b m, d, fvs, body, hz, hop => by
    simp only [pwsAll, Bool.and_eq_true, beq_iff_eq] at hz
    obtain ⟨hpw, hb⟩ := hz
    simp only [openPisAtFvars] at hop
    split at hop
    · next fvs' e' hop' =>
      have hb' : pwsAll (Level.zeronessOf l) (b.instantiate1 (.fvar d dom)) = true := by
        rw [pwsAll_instantiate1]; exact hb
      exact fun φ => ⟨by rw [hpw, pwBit_zeronessOf], pwsAll_open n hb' hop' φ⟩
    · exact nomatch hop
  | _ + 1, .bvar _, _, _, _, _, hop | _ + 1, .fvar _ _, _, _, _, _, hop
  | _ + 1, .sort _, _, _, _, _, hop | _ + 1, .const _ _, _, _, _, _, hop
  | _ + 1, .app _ _, _, _, _, _, hop | _ + 1, .lam _ _ _, _, _, _, _, hop
  | _ + 1, .letE _ _ _ _, _, _, _, _, hop | _ + 1, .lit _, _, _, _, _, hop
  | _ + 1, .proj _ _ _, _, _, _, _, hop => by simp [openPisAtFvars] at hop

theorem famHead_of_getAppFn {T : Key md} {us : List Level} :
    ∀ {e : Expr md}, e.getAppFn = .const T us → famHead T e = true
  | .const _ _, h => by
    simp only [Expr.getAppFn, Expr.const.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp [famHead]
  | .app f _, h => by
    simp only [Expr.getAppFn] at h
    simp only [famHead]
    exact famHead_of_getAppFn h
  | .bvar _, h | .fvar _ _, h | .sort _, h | .lam _ _ _, h | .forallE _ _ _, h
  | .letE _ _ _ _, h | .lit _, h | .proj _ _ _, h => by simp [Expr.getAppFn] at h

/-- A telescope opened to a body headed by the family ends in the family. -/
theorem famHead_of_open {T : Key md} {us : List Level} :
    ∀ (n : Nat) {e : Expr md} {d : Nat} {fvs : List (Expr md)} {body : Expr md},
      openPisAtFvars n e d = some (fvs, body) → body.getAppFn = .const T us → famHead T e = true
  | 0, e, d, fvs, body, hop, hfn => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨-, rfl⟩ := hop
    exact famHead_of_getAppFn hfn
  | n + 1, .forallE dom b m, d, fvs, body, hop, hfn => by
    simp only [openPisAtFvars] at hop
    split at hop
    · next fvs' e' hop' =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hop
      obtain ⟨-, rfl⟩ := hop
      have := famHead_of_open n hop' hfn
      rw [famHead_instantiate1] at this
      simpa [famHead] using this
    · exact nomatch hop
  | _ + 1, .bvar _, _, _, _, hop, _ | _ + 1, .fvar _ _, _, _, _, hop, _
  | _ + 1, .sort _, _, _, _, hop, _ | _ + 1, .const _ _, _, _, _, hop, _
  | _ + 1, .app _ _, _, _, _, hop, _ | _ + 1, .lam _ _ _, _, _, _, hop, _
  | _ + 1, .letE _ _ _ _, _, _, _, hop, _ | _ + 1, .lit _, _, _, _, hop, _
  | _ + 1, .proj _ _ _, _, _, _, hop, _ => by simp [openPisAtFvars] at hop

/-- **A field domain ending in the family, opened to its end**: each binder's bit is the result
sort's zero-ness. -/
theorem famDomOk_open {T : Key md} {l : Level} {us : List Level} {dom : Expr md}
    (h : famDomOk T (Level.zeronessOf l) dom = true) {n d : Nat} {fvs : List (Expr md)}
    {body : Expr md} (hop : openPisAtFvars n dom d = some (fvs, body))
    (hfn : body.getAppFn = .const T us) :
    ∀ φ, PiBitsOpen φ (Level.eval φ l = 0) n d dom := by
  have hh := famHead_of_open n hop hfn
  simp only [famDomOk, hh, Bool.not_true, Bool.false_or] at h
  exact pwsAll_open n h hop

/-- **What a constructor's stage reads of the stored former** `cvS`: the telescope constant `cvTa`
itself, whose type strips to the result sort, or the constructor's binders carry the result sort's
zero-ness. -/
def FormerZeroSrc (T : Key md) (nP nIdx : Nat) (resSort : Level) (cvTa cvS : ConstantVal md)
    (cty : Expr md) : Prop :=
  (cvS = cvTa ∧ ∃ bs, cvTa.type.stripPis (nP + nIdx) = some (bs, .sort resSort)) ∨
  ctorZeroOk T (Level.zeronessOf resSort) cty = true

/-- `FormerZeroSrc` at every constructor of a block. -/
def FormerZeroSrcAll (T : Key md) (nP nIdx : Nat) (resSort : Level) (cvTa cvS : ConstantVal md)
    (ctorsA : List (ConstantVal md × Nat)) : Prop :=
  (cvS = cvTa ∧ ∃ bs, cvTa.type.stripPis (nP + nIdx) = some (bs, .sort resSort)) ∨
  ctorsA.all (fun cA => ctorZeroOk T (Level.zeronessOf resSort) cA.1.type) = true

theorem FormerZeroSrcAll.get {T : Key md} {nP nIdx : Nat} {resSort : Level}
    {cvTa cvS : ConstantVal md} {ctorsA : List (ConstantVal md × Nat)}
    (h : FormerZeroSrcAll T nP nIdx resSort cvTa cvS ctorsA) {cA : ConstantVal md × Nat}
    (hc : cA ∈ ctorsA) : FormerZeroSrc T nP nIdx resSort cvTa cvS cA.1.type := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (List.all_eq_true.mp h cA hc)

end Ix.Kernel.Model
