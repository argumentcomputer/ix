import Compilatrix.Rt.Proof.Heap
import Compilatrix.Rt.Proof.Chunk

/-!
# Registers and operands

A Cfg activation's environment and its Lir frame's registers relate by
`EnvRel T P D sup ρ ρl`: every Cfg variable is below the function's
register supply `sup` (Lir temporaries are allocated from there up, so they
never clash), and every variable outside `D` holds a word related to its
value. `D` is the set of variables Lir never reads: the comparisons a fused
`switch` consumes (`Rt.lower` branches on them directly and never assigns
them).

`operand_rel`/`operands_rel`: a lowered operand evaluates in the registers
to a word related to the Cfg operand's value, and keeps doing so while
temporaries are assigned.
-/

set_option autoImplicit false

namespace Compilatrix.Rt.Proof

open Compilatrix.Lir (Word)
open Compilatrix.Rt.Lower (Tables)


structure EnvRel (T : Tables) (P : List Word) (D : Nat → Prop) (sup : Nat) (ρ : Own.Env) (ρl : Lir.Env) :
    Prop where
  dom : ∀ {y : Nat} {v : Own.RVal}, ρ.get? y = some v → y < sup
  val : ∀ {y : Nat} {v : Own.RVal}, ρ.get? y = some v → ¬ D y → ∃ w, ρl[y]? = some w ∧ ValRel T P v w

namespace EnvRel

variable {T : Tables} {P : List Word} {D : Nat → Prop} {sup : Nat} {ρ : Own.Env} {ρl : Lir.Env}

theorem mono {P' : List Word} (hP : P <+: P') (h : EnvRel T P D sup ρ ρl) : EnvRel T P' D sup ρ ρl where
  dom := h.dom
  val hy hD := by
    obtain ⟨w, hw, hv⟩ := h.val hy hD
    exact ⟨w, hw, ValRel.mono hP hv⟩

/-- A temporary at or above the supply changes nothing the relation sees. -/
theorem temp {t : Nat} (ht : sup ≤ t) (u : Word) (h : EnvRel T P D sup ρ ρl) :
    EnvRel T P D sup ρ (ρl.insert t u) where
  dom := h.dom
  val := by
    intro y v hy hD
    obtain ⟨w, hw, hv⟩ := h.val hy hD
    have := h.dom hy
    refine ⟨w, ?_, hv⟩
    rw [Lir.env_insert_ne (y := y) _ _ (Nat.ne_of_gt (by omega))]
    exact hw

theorem insert {x : Nat} {v : Own.RVal} {w : Word} (hx : x < sup) (hv : ValRel T P v w)
    (h : EnvRel T P D sup ρ ρl) : EnvRel T P D sup (ρ.insert x v) (ρl.insert x w) where
  dom := by
    intro y v' hy
    rw [Src.NatMap.get?_insert] at hy
    split at hy
    · omega
    · exact h.dom hy
  val := by
    intro y v' hy hD
    rw [Src.NatMap.get?_insert] at hy
    split at hy
    · rename_i hyx
      subst hyx
      cases hy
      exact ⟨w, by simp, hv⟩
    · rename_i hyx
      obtain ⟨w', hw', hv'⟩ := h.val hy hD
      exact ⟨w', by rw [Lir.env_insert_ne _ _ (Ne.symm hyx)]; exact hw', hv'⟩

/-- A variable Lir never reads may take any value. -/
theorem insert_dead {x : Nat} {v : Own.RVal} (hx : x < sup) (hD : D x) (h : EnvRel T P D sup ρ ρl) :
    EnvRel T P D sup (ρ.insert x v) ρl where
  dom := by
    intro y v' hy
    rw [Src.NatMap.get?_insert] at hy
    split at hy
    · omega
    · exact h.dom hy
  val := by
    intro y v' hy hD'
    rw [Src.NatMap.get?_insert] at hy
    split at hy
    · rename_i hyx; subst hyx; exact absurd hD hD'
    · exact h.val hy hD'

end EnvRel

/-- A lowered operand reads only Cfg variables. -/
def ArgReads (sup : Nat) (la : Lir.Arg) : Prop := ∀ y : Nat, la = .v y → y < sup

theorem ArgReads.imm (sup : Nat) (w : Word) : ArgReads sup (.imm w) := fun _ h => by cases h

/-- An operand that reads below the supply keeps its value while
temporaries are assigned. -/
theorem arg_eval_temp {sup : Nat} {la : Lir.Arg} (ha : ArgReads sup la) {ρl : Lir.Env} {t : Nat}
    (ht : sup ≤ t) (u : Word) : la.eval (ρl.insert t u) = la.eval ρl := by
  cases la with
  | v y =>
    have := ha y rfl
    simp only [Lir.Arg.eval_v]
    exact Lir.env_insert_ne (y := y) _ _ (Nat.ne_of_gt (by omega))
  | imm w => rfl

/-- The variables an operand reads are outside `D`. -/
def LiveArg (D : Nat → Prop) (a : Fir.Arg) : Prop := ∀ y, a = .var y → ¬ D y

theorem operand_rel {T : Tables} {P : List Word} {D : Nat → Prop} {sup : Nat} {ρ : Own.Env} {ρl : Lir.Env}
    (hρ : EnvRel T P D sup ρ ρl) {f : Fir.FunId} {a : Fir.Arg} {la : Lir.Arg}
    (ho : Lower.operand f a = .ok (some la)) (hl : LiveArg D a) {v : Own.RVal} (hv : Own.evalArg ρ a = some v) :
    ∃ w, la.eval ρl = some w ∧ ValRel T P v w ∧ ArgReads sup la := by
  cases a with
  | var y =>
    simp only [Lower.operand, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at ho
    subst ho
    simp only [Own.evalArg] at hv
    obtain ⟨w, hw, hvw⟩ := hρ.val hv (hl y rfl)
    refine ⟨w, hw, hvw, fun y' h => ?_⟩
    cases h
    exact hρ.dom hv
  | lit l =>
    cases l with
    | nat n =>
      simp only [Lower.operand, pure, Except.pure, Except.ok.injEq] at ho
      simp only [Own.evalArg, Option.some.injEq] at hv
      subst hv
      cases hn : natWord n with
      | none => simp [hn] at ho
      | some w =>
        simp only [hn, Option.map_some, Option.some.injEq] at ho
        subst ho
        exact ⟨w, rfl, hn, ArgReads.imm _ _⟩
    | str s => simp [Lower.operand, throw, throwThe, MonadExceptOf.throw] at ho
  | erased =>
    simp only [Lower.operand, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at ho
    subst ho
    simp only [Own.evalArg, Option.some.injEq] at hv
    subst hv
    exact ⟨erasedWord, rfl, rfl, ArgReads.imm _ _⟩

theorem operands_rel {T : Tables} {P : List Word} {D : Nat → Prop} {sup : Nat} {ρ : Own.Env} {ρl : Lir.Env}
    (hρ : EnvRel T P D sup ρ ρl) {f : Fir.FunId} :
    ∀ {as : List Fir.Arg} {las : List Lir.Arg}, Lower.operands f as = .ok (some las) → (∀ a ∈ as, LiveArg D a) →
      ∀ {vs : List Own.RVal}, Own.evalArgs ρ as = some vs →
      ∃ ws, Lir.evalArgs ρl las = some ws ∧ ListRel (ValRel T P) vs ws ∧ ∀ la ∈ las, ArgReads sup la
  | [], las, ho, _, vs, hv => by
    simp only [Lower.operands, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at ho
    subst ho
    simp only [Own.evalArgs, Option.some.injEq] at hv
    subst hv
    exact ⟨[], rfl, .nil, by simp⟩
  | a :: as, las, ho, hl, vs, hv => by
    simp only [Lower.operands, bind, Except.bind] at ho
    cases ha : Lower.operand f a with
    | error e => simp [ha] at ho
    | ok x =>
      cases has : Lower.operands f as with
      | error e => simp [ha, has] at ho
      | ok xs =>
        simp only [ha, has, pure, Except.pure, Except.ok.injEq] at ho
        cases x with
        | none => simp at ho
        | some la =>
          cases xs with
          | none => simp at ho
          | some las' =>
            simp only [Option.some.injEq] at ho
            subst ho
            simp only [Own.evalArgs] at hv
            cases hva : Own.evalArg ρ a with
            | none => simp [hva] at hv
            | some v =>
              cases hvas : Own.evalArgs ρ as with
              | none => simp [hva, hvas] at hv
              | some vs' =>
                simp only [hva, hvas, Option.some.injEq] at hv
                subst hv
                obtain ⟨w, hw, hvw, hr⟩ := operand_rel hρ ha (hl a (by simp)) hva
                obtain ⟨ws, hws, hrel, hrs⟩ := operands_rel hρ has (fun a' h => hl a' (by simp [h])) hvas
                refine ⟨w :: ws, ?_, .cons hvw hrel, ?_⟩
                · simp [hw, hws]
                · intro la' h
                  simp only [List.mem_cons] at h
                  rcases h with rfl | h
                  · exact hr
                  · exact hrs la' h

end Compilatrix.Rt.Proof
