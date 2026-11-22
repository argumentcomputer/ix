import IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedCtorEnv
import IxCC.Rt.Proof.Env

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar
open IxCC IxCC.Rt IxCC.Rt.Proof IxCC.Rt.Rc.Procs
open IxCC.Lir (Word)
open IxCC.Rt.Lower (Tables)

/-- Pointwise scalar proof interface with current dynamic locations. No
immortal heap invariant or append-only physical placement is involved. -/
def ValRel (T : Tables) (P : AddressMap) : Own.RVal → Word → Prop
  | .lit (.nat n), w => natWord n = some w
  | .lit (.str _), _ => False
  | .ctor0 c, w => w = ctor0Word c.tag ∧ CtorOk T c ∧ c.fieldless = true
  | .erased, w => w = erasedWord
  | .loc location, w => P location = some w

theorem ValRel.words {T : Tables} {P : AddressMap} {value : Own.RVal} {word : Word}
    (related : ValRel T P value word) :
    valueWord P value = some word ∧ ValueCtorOk T value := by
  cases value with
  | loc l => exact ⟨related, trivial⟩
  | lit literal =>
    cases literal with
    | nat n => exact ⟨related, trivial⟩
    | str s => exact related.elim
  | erased => cases related; exact ⟨rfl, trivial⟩
  | ctor0 ctor =>
    obtain ⟨rfl, compatible, zero⟩ := related
    have arity : ctor.arity = 0 := by simpa [Fir.CtorInfo.fieldless] using zero
    exact ⟨by simp [valueWord, arity, compatible.tag], compatible, zero⟩

theorem ValRel.of_words {T : Tables} {P : AddressMap} {value : Own.RVal} {word : Word}
    (represented : valueWord P value = some word) (compatible : ValueCtorOk T value) :
    ValRel T P value word := by
  cases value with
  | loc l => exact represented
  | lit literal =>
    cases literal with
    | nat n => exact represented
    | str s => cases represented
  | erased => cases represented; rfl
  | ctor0 ctor =>
    obtain ⟨compatible, zero⟩ := compatible
    have arity : ctor.arity = 0 := by simpa [Fir.CtorInfo.fieldless] using zero
    have equal : ctor0Word ctor.tag = word := by
      simpa [valueWord, arity, compatible.tag] using represented
    exact ⟨equal.symm, compatible, zero⟩

structure EnvRel (T : Tables) (P : AddressMap) (D : Nat → Prop) (sup : Nat) (ρ : Own.Env) (ρl : Lir.Env) :
    Prop where
  dom : ∀ {y : Nat} {v : Own.RVal}, ρ.get? y = some v → y < sup
  val : ∀ {y : Nat} {v : Own.RVal}, ρ.get? y = some v → ¬ D y → ∃ w, ρl[y]? = some w ∧ ValRel T P v w

namespace EnvRel

variable {T : Tables} {P : AddressMap} {D : Nat → Prop} {sup : Nat} {ρ : Own.Env} {ρl : Lir.Env}

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

theorem operand_rel {T : Tables} {P : AddressMap} {D : Nat → Prop} {sup : Nat} {ρ : Own.Env} {ρl : Lir.Env}
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

theorem operands_rel {T : Tables} {P : AddressMap} {D : Nat → Prop} {sup : Nat} {ρ : Own.Env} {ρl : Lir.Env}
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


theorem EnvRel.of_fused {T : Tables} {P : AddressMap} {D : Nat → Prop} {sup : Nat}
    {source : Own.Env} {target : Lir.Env}
    (words : FusedWords P D sup source target) (ctors : FusedCtorOk T D source) :
    EnvRel T P D sup source target := by
  refine ⟨words.dom, ?_⟩
  intro x value lookup live
  obtain ⟨word, represented, register⟩ := words.word lookup live
  exact ⟨word, register, ValRel.of_words represented (ctors x value lookup live)⟩

theorem EnvRel.to_fused {T : Tables} {P : AddressMap} {D : Nat → Prop} {sup : Nat}
    {source : Own.Env} {target : Lir.Env} (related : EnvRel T P D sup source target) :
    FusedWords P D sup source target ∧ FusedCtorOk T D source := by
  constructor
  · refine ⟨related.dom, ?_⟩
    intro x value lookup live
    obtain ⟨word, register, represented⟩ := related.val lookup live
    exact ⟨word, represented.words.1, register⟩
  · intro x value lookup live
    obtain ⟨word, _, represented⟩ := related.val lookup live
    exact represented.words.2










end IxCC.Cfg.Rc.Proof.Physical.Bridge.Scalar
