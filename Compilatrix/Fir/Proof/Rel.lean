import Compilatrix.Fir.Proof.Mono
import Compilatrix.Fir.Lower
import Compilatrix.Anf.Proof.Mono
import Compilatrix.Sem.Forall2

/-! # Anf and Fir values related

The value relation of `Fir.convert_correct` (design note 03 §2.2, `ValRel`):
literals to literals, □ to `erased`, and an Anf constructor to the Fir
constructor of its table row (`CtorInfo.ofKey`) with related fields. There
is no closure case: the lowering declines closures (`fir.closures`), so the
first-order fragment never builds one. A related constructor has the
table's field count, which is what lets Fir select a `case` alternative by
key alone where Anf also compares the arity.

Below: list facts, `asCtor` (constructor reading, with `Nat` literals
peeling into the pinned keys), primitives, and the pinned keys' field
counts that `Lower.pinsOk` and `Lower.boolPinsOk` check. -/

set_option autoImplicit false

namespace Compilatrix.Fir.Proof

open Compilatrix.Sem (Result Forall2)

/-- `omega` after unfolding Fir's name types (`Var`, `JoinId` and `FunId`
are `Nat`, which `omega` does not see through). -/
macro "fir_omega" : tactic =>
  `(tactic| ((try dsimp only [Compilatrix.Fir.Var, Compilatrix.Fir.JoinId, Compilatrix.Fir.FunId] at *) <;> omega))


/-- Anf and Fir values related (03 §2.2 `ValRel`). -/
inductive VR (A : Anf.Program) : Anf.Val → Val → Prop
  | lit (l : Lam.Lit) : VR A (.lit l) (.lit l)
  | box : VR A .box .erased
  | con {c : Key.CtorKey} {info : CtorInfo} {vs : List Anf.Val} {ws : List Val} :
      CtorInfo.ofKey A.ctors c = some info → Forall2 (VR A) vs ws → ws.length = info.arity →
      VR A (.con c vs) (.ctor info ws)

/-- Lists of related values. -/
abbrev VRs (A : Anf.Program) : List Anf.Val → List Val → Prop := Forall2 (VR A)

variable {A : Anf.Program}

/-! ## Constructor info from the table -/

theorem ofKey_key {t : List Lam.CtorInfo} {c : Key.CtorKey} {info : CtorInfo}
    (h : CtorInfo.ofKey t c = some info) : info.key = c := by
  simp only [CtorInfo.ofKey, Option.map_eq_some_iff] at h
  obtain ⟨_, _, rfl⟩ := h
  rfl

/-! ## Reading a value as a constructor -/

/-- Related values read as the same constructor with related fields, or
neither does. -/
theorem asCtor_rel {K : Lam.Known} {v : Anf.Val} {w : Val} (h : VR A v w) :
    (∀ c vs, v.asCtor K = some (c, vs) → ∃ ws, w.asCtor K = some (c, ws) ∧ VRs A vs ws) ∧
      (v.asCtor K = none → w.asCtor K = none) := by
  cases h with
  | lit l =>
    rcases l with (_ | n) | s
    · refine ⟨fun c vs hc => ?_, fun hc => ?_⟩
      · simp only [Anf.Val.asCtor, Option.map_eq_some_iff, Prod.mk.injEq] at hc
        obtain ⟨c', hc', rfl, rfl⟩ := hc
        exact ⟨[], by simp [Val.asCtor, hc'], .nil⟩
      · simp only [Anf.Val.asCtor, Option.map_eq_none_iff] at hc
        simp [Val.asCtor, hc]
    · refine ⟨fun c vs hc => ?_, fun hc => ?_⟩
      · simp only [Anf.Val.asCtor, Option.map_eq_some_iff, Prod.mk.injEq] at hc
        obtain ⟨c', hc', rfl, rfl⟩ := hc
        exact ⟨[.lit (.nat n)], by simp [Val.asCtor, hc'], .cons (.lit _) .nil⟩
      · simp only [Anf.Val.asCtor, Option.map_eq_none_iff] at hc
        simp [Val.asCtor, hc]
    · exact ⟨fun c vs hc => by simp [Anf.Val.asCtor] at hc, fun _ => rfl⟩
  | box => exact ⟨fun c vs hc => by simp [Anf.Val.asCtor] at hc, fun _ => rfl⟩
  | con hk hvs _ =>
    refine ⟨fun c vs hc => ?_, fun hc => by simp [Anf.Val.asCtor] at hc⟩
    simp only [Anf.Val.asCtor, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    exact ⟨_, by simp [Val.asCtor, ofKey_key hk], hvs⟩

/-- The table arity of a pinned key, where listed. -/
theorem pinOk_some {n : Nat} {must : Bool} {c : Key.CtorKey} {info : CtorInfo}
    (h : Lower.pinOk A n must (some c) = true) (hi : CtorInfo.ofKey A.ctors c = some info) :
    info.arity = n := by
  simp only [Lower.pinOk, hi, beq_iff_eq] at h
  exact h

theorem pinOk_listed {n : Nat} {c : Key.CtorKey} (h : Lower.pinOk A n true (some c) = true) :
    ∃ info, CtorInfo.ofKey A.ctors c = some info ∧ info.arity = n := by
  simp only [Lower.pinOk] at h
  split at h
  · next info hi => exact ⟨info, hi, by simpa using h⟩
  · simp at h

theorem pinsOk_parts (h : Lower.pinsOk A = true) :
    Lower.pinOk A 0 false A.known.natZero = true ∧ Lower.pinOk A 1 false A.known.natSucc = true ∧
      Lower.pinOk A 0 false A.known.boolFalse = true ∧ Lower.pinOk A 0 false A.known.boolTrue = true := by
  simp only [Lower.pinsOk, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

/-- A related value read as a listed constructor has the table's field
count (the `Nat` pins, where listed, have 0 and 1 fields). -/
theorem asCtor_arity (hp : Lower.pinsOk A = true) {v : Anf.Val} {w : Val} (h : VR A v w)
    {c : Key.CtorKey} {vs : List Anf.Val} (hc : v.asCtor A.known = some (c, vs)) {info : CtorInfo}
    (hi : CtorInfo.ofKey A.ctors c = some info) : vs.length = info.arity := by
  obtain ⟨hz, hs, _, _⟩ := pinsOk_parts hp
  cases h with
  | lit l =>
    rcases l with (_ | n) | s
    · simp only [Anf.Val.asCtor, Option.map_eq_some_iff, Prod.mk.injEq] at hc
      obtain ⟨c', hc', rfl, rfl⟩ := hc
      rw [hc'] at hz
      exact (pinOk_some hz hi).symm
    · simp only [Anf.Val.asCtor, Option.map_eq_some_iff, Prod.mk.injEq] at hc
      obtain ⟨c', hc', rfl, rfl⟩ := hc
      rw [hc'] at hs
      exact (pinOk_some hs hi).symm
    · simp [Anf.Val.asCtor] at hc
  | box => simp [Anf.Val.asCtor] at hc
  | con hk hvs hl =>
    simp only [Anf.Val.asCtor, Option.some.injEq, Prod.mk.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    rw [hk] at hi
    cases hi
    rw [hvs.length, hl]

/-! ## Primitives -/

theorem natArgs_rel {vs : List Anf.Val} {ws : List Val} (h : VRs A vs ws) :
    Anf.natArgs vs = Fir.natArgs ws := by
  induction h with
  | nil => rfl
  | cons hvw _ ih =>
    cases hvw with
    | lit l =>
      rcases l with n | s
      · simp [Anf.natArgs, Fir.natArgs, ih]
      · rfl
    | box => rfl
    | con => rfl

/-- Only the comparison primitives return a Boolean. -/
theorem sem_bool {p : Lam.Prim} {ns : List Nat} {b : Bool} (h : p.sem ns = some (.bool b)) :
    Lower.boolPrim p = true := by
  cases p <;> (try rfl) <;> (unfold Lam.Prim.sem at h; split at h <;>
    simp_all [Src.PrimOp.eval2, Lam.Prim.sem.srcOp])

/-- A primitive on related arguments: a related value, or Anf is stuck. -/
theorem primResult_rel {F : Program} (hk : F.known = A.known) (hc : F.ctors = A.ctors)
    {op : Lam.Prim} (hb : Lower.boolPrim op = true → Lower.boolPinsOk A = true)
    {vs : List Anf.Val} {ws : List Val} (h : VRs A vs ws) :
    (∀ v, Anf.primResult A.known op vs = .ok v → ∃ w, Fir.primResult F op ws = .ok w ∧ VR A v w) ∧
      (Anf.primResult A.known op vs = .stuck ∨ ∃ v, Anf.primResult A.known op vs = .ok v) := by
  constructor
  · intro v hv
    unfold Anf.primResult at hv
    unfold Fir.primResult
    rw [← natArgs_rel h]
    split at hv
    · next ns hns =>
      simp only [hns]
      split at hv
      · next n hn => simp only [hn]; cases hv; exact ⟨_, rfl, .lit _⟩
      · next b hb' =>
        simp only [hb']
        have hbp := hb (sem_bool hb')
        simp only [Lower.boolPinsOk, Bool.and_eq_true] at hbp
        split at hv
        · next c hcb =>
          cases hv
          obtain ⟨info, hi, ha⟩ : ∃ info, CtorInfo.ofKey A.ctors c = some info ∧ info.arity = 0 := by
            cases b
            · simp only [Bool.false_eq_true, ↓reduceIte] at hcb; rw [hcb] at hbp; exact pinOk_listed hbp.1
            · simp only [↓reduceIte] at hcb; rw [hcb] at hbp; exact pinOk_listed hbp.2
          refine ⟨.ctor info [], ?_, .con hi .nil (by simp [ha])⟩
          simp [boolVal, hk, hcb, Program.ctorInfo?, hc, hi, Result.ofOption]
        · cases hv
      · cases hv
    · cases hv
  · unfold Anf.primResult
    split
    · split
      · exact .inr ⟨_, rfl⟩
      · split
        · exact .inr ⟨_, rfl⟩
        · exact .inl rfl
      · exact .inl rfl
    · exact .inl rfl

end Compilatrix.Fir.Proof
