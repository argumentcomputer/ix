import IxCC.Rt.Proof.Instr
import IxCC.Cfg.Rc.Proof.Physical.Bridge.RawWords
import IxCC.Cfg.Rc.Proof.Physical.Bridge.FusedBindings

/-!
# Values at raw and tagged positions

A flow into a parameter, a return or a copy carries a value to a position the lowering's tables
mark raw or tagged (`Rt.Lower.operandsAt`). `SlotVal` is its word there: the raw word of a
literal below `2^64` at a raw position, `valueWord` at a tagged one. The flow check
(`Cfg.Rc.Raw.argsFit`) gives every register argument its position's flag, so a register
argument's word is the one its own relation states.
-/

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC IxCC.Rt IxCC.Rt.Rc.Procs
open IxCC.Rt.Lower (Tables)
open IxCC.Rt.Proof (Fused ListRel LiveArg ArgReads)

/-- A value's word at a raw or a tagged position. -/
def SlotVal (addresses : AddressMap) (raw : Bool) (v : Own.RVal) (w : Lir.Word) : Prop :=
  if raw then RawVal v w else valueWord addresses v = some w

theorem SlotVal.tagged {addresses : AddressMap} {v : Own.RVal} {w : Lir.Word} :
    SlotVal addresses false v w ↔ valueWord addresses v = some w := by
  simp [SlotVal]

theorem SlotVal.raw {addresses : AddressMap} {v : Own.RVal} {w : Lir.Word} :
    SlotVal addresses true v w ↔ RawVal v w := by
  simp [SlotVal]

/-- Values' words at positions with the given flags (a missing flag is `false`). -/
inductive SlotsRel (addresses : AddressMap) : List Bool → List Own.RVal → List Lir.Word → Prop
  | nil (rs : List Bool) : SlotsRel addresses rs [] []
  | cons {rs : List Bool} {v : Own.RVal} {vs : List Own.RVal} {w : Lir.Word} {ws : List Lir.Word} :
      SlotVal addresses (rs.headD false) v w → SlotsRel addresses rs.tail vs ws →
      SlotsRel addresses rs (v :: vs) (w :: ws)

theorem SlotsRel.length_eq {addresses : AddressMap} {rs : List Bool} {vs : List Own.RVal}
    {ws : List Lir.Word} (h : SlotsRel addresses rs vs ws) : vs.length = ws.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- At tagged positions only, the relation is the tagged one. -/
theorem SlotsRel.of_tagged {addresses : AddressMap} :
    ∀ {rs : List Bool} {vs : List Own.RVal} {ws : List Lir.Word}, (∀ r ∈ rs, r = false) →
      ListRel (fun v w => valueWord addresses v = some w) vs ws → SlotsRel addresses rs vs ws
  | _, _, _, _, .nil => .nil _
  | rs, _, _, h, .cons hv tail => by
    have head : rs.headD false = false := by
      cases rs with
      | nil => rfl
      | cons r rs => exact h r (by simp)
    refine .cons (by rw [head]; exact SlotVal.tagged.2 hv) (SlotsRel.of_tagged (fun r hr => ?_) tail)
    cases rs with
    | nil => simp at hr
    | cons r' rs => exact h r (by simp_all)

theorem SlotsRel.to_tagged {addresses : AddressMap} :
    ∀ {rs : List Bool} {vs : List Own.RVal} {ws : List Lir.Word}, (∀ r ∈ rs, r = false) →
      SlotsRel addresses rs vs ws → ListRel (fun v w => valueWord addresses v = some w) vs ws
  | _, _, _, _, .nil _ => .nil
  | rs, _, _, h, .cons hv tail => by
    have head : rs.headD false = false := by
      cases rs with
      | nil => rfl
      | cons r rs => exact h r (by simp)
    rw [head] at hv
    refine .cons (SlotVal.tagged.1 hv) (SlotsRel.to_tagged (fun r hr => ?_) tail)
    cases rs with
    | nil => simp at hr
    | cons r' rs => exact h r (by simp_all)

/-! ## Operands at positions -/

/-- **An operand at a position**: its lowered word is the value's word there. -/
theorem slot_operand_word {addresses : AddressMap} {T : Tables} {fn : Nat} {fd : Cfg.Fun}
    {bound : Nat} {source : Own.Env} {target : Lir.Env}
    (related : FusedWords addresses (Omit T fn fd) bound source target)
    (raws : RawWords (T.rawVar fn) source target)
    {f : Fir.FunId} {r : Bool} {a : Fir.Arg} {operand : Lir.Arg} {value : Own.RVal}
    (lowered : Lower.operandAt f r a = .ok (some operand))
    (fits : Cfg.Rc.Raw.argFits (T.rawVar fn) r a = true) (live : LiveArg (Fused T fd) a)
    (evaluated : Own.evalArg source a = some value) :
    ∃ word, operand.eval target = some word ∧ SlotVal addresses r value word ∧ ArgReads bound operand := by
  cases r with
  | false =>
    have tagged : Lower.operand f a = .ok (some operand) := by
      rw [← Rt.Proof.operandAt_false]; exact lowered
    have live' : LiveArg (Omit T fn fd) a := by
      intro y equal omitted
      subst a
      rcases omitted with fused | raw
      · exact live y rfl fused
      · simp [Cfg.Rc.Raw.argFits, raw] at fits
    obtain ⟨word, hw, hv, hr⟩ := fused_operand_word related tagged live' evaluated
    exact ⟨word, hw, SlotVal.tagged.2 hv, hr⟩
  | true =>
    cases a with
    | var y =>
      simp only [Lower.operandAt, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at lowered
      subst operand
      simp only [Own.evalArg] at evaluated
      have raw : T.rawVar fn y = true := by simpa [Cfg.Rc.Raw.argFits] using fits
      obtain ⟨word, hw, hv⟩ := raws.word evaluated raw
      refine ⟨word, hw, SlotVal.raw.2 hv, ?_⟩
      intro y' equal
      cases equal
      exact related.dom evaluated
    | lit literal =>
      have rawLowered : Lower.rawOperand f (.lit literal) = .ok (some operand) := lowered
      cases literal with
      | nat n =>
        simp only [Own.evalArg, Option.some.injEq] at evaluated
        subst value
        by_cases small : n < 2 ^ 64
        · simp only [Lower.rawOperand, small, ↓reduceIte, pure, Except.pure, Except.ok.injEq,
            Option.some.injEq] at rawLowered
          subst operand
          exact ⟨UInt64.ofNat n, rfl, SlotVal.raw.2 ⟨small, rfl⟩, ArgReads.imm _ _⟩
        · simp [Lower.rawOperand, small, pure, Except.pure] at rawLowered
      | str s => simp [Lower.rawOperand, throw, throwThe, MonadExceptOf.throw] at rawLowered
    | erased =>
      have rawLowered : Lower.rawOperand f .erased = .ok (some operand) := lowered
      simp [Lower.rawOperand, pure, Except.pure] at rawLowered

/-- **Operands at positions.** -/
theorem slot_operands_words {addresses : AddressMap} {T : Tables} {fn : Nat} {fd : Cfg.Fun}
    {bound : Nat} {source : Own.Env} {target : Lir.Env}
    (related : FusedWords addresses (Omit T fn fd) bound source target)
    (raws : RawWords (T.rawVar fn) source target) {f : Fir.FunId} :
    ∀ {rs : List Bool} {args : List Fir.Arg} {operands : List Lir.Arg},
      Lower.operandsAt f rs args = .ok (some operands) →
      Cfg.Rc.Raw.argsFit (T.rawVar fn) rs args = true → (∀ a ∈ args, LiveArg (Fused T fd) a) →
      ∀ {values : List Own.RVal}, Own.evalArgs source args = some values →
      ∃ words, Lir.evalArgs target operands = some words ∧ SlotsRel addresses rs values words ∧
        ∀ operand ∈ operands, ArgReads bound operand
  | rs, [], operands, lowered, _, _, values, evaluated => by
    simp only [Lower.operandsAt, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at lowered
    subst operands
    simp only [Own.evalArgs, Option.some.injEq] at evaluated
    subst values
    exact ⟨[], rfl, .nil _, by simp⟩
  | rs, a :: args, operands, lowered, fits, live, values, evaluated => by
    simp only [Cfg.Rc.Raw.argsFit, Bool.and_eq_true] at fits
    rw [Lower.operandsAt.eq_2] at lowered
    generalize hhead : Lower.operandAt f (rs.headD false) a = first at lowered
    generalize hrest : Lower.operandsAt f rs.tail args = rest at lowered
    simp only [bind, Except.bind] at lowered
    cases first with
    | error e => cases lowered
    | ok oa =>
      cases rest with
      | error e => cases lowered
      | ok oas =>
        simp only [pure, Except.pure, Except.ok.injEq] at lowered
        cases oa with
        | none => simp at lowered
        | some operand =>
          cases oas with
          | none => simp at lowered
          | some tail =>
            simp only [Option.some.injEq] at lowered
            subst operands
            simp only [Own.evalArgs] at evaluated
            cases hva : Own.evalArg source a with
            | none => simp [hva] at evaluated
            | some value =>
              cases hvas : Own.evalArgs source args with
              | none => simp [hva, hvas] at evaluated
              | some vs =>
                simp only [hva, hvas, Option.some.injEq] at evaluated
                subst values
                obtain ⟨word, hw, hv, hr⟩ := slot_operand_word related raws hhead fits.1
                  (live a (by simp)) hva
                obtain ⟨words, hws, hvs, hrs⟩ := slot_operands_words related raws hrest fits.2
                  (fun a' member => live a' (by simp [member])) hvas
                refine ⟨word :: words, by simp [hw, hws], .cons hv hvs, ?_⟩
                intro operand' member
                rcases List.mem_cons.mp member with rfl | member
                · exact hr
                · exact hrs operand' member

/-! ## Binding parameters at positions -/

/-- A raw register bound to its word: the tagged relation, which omits it, is unchanged. -/
theorem FusedWords.bind_raw {addresses : AddressMap} {D : Nat → Prop} {bound : Nat}
    {source : Own.Env} {target : Lir.Env} (related : FusedWords addresses D bound source target)
    {x : Nat} (real : x < bound) (omitted : D x) (value : Own.RVal) (word : Lir.Word) :
    FusedWords addresses D bound (source.insert x value) (target.insert x word) := by
  refine (related.bind_omitted real omitted value).agree ?_
  intro y v lookup live
  have ne : y ≠ x := fun e => live (e ▸ omitted)
  exact Lir.env_insert_ne _ _ (Ne.symm ne)

/-- **Parameters bound at their positions.** The flags are the parameters' own raw flags, so
each raw parameter is omitted from the tagged relation and held by the raw one. -/
theorem slots_bindParams {addresses : AddressMap} {T : Tables} {fn : Nat} {fd : Cfg.Fun}
    {bound : Nat} :
    ∀ {params : List Nat} {values : List Own.RVal} {words : List Lir.Word}
      {source : Own.Env} {target : Lir.Env},
      FusedWords addresses (Omit T fn fd) bound source target →
      RawWords (T.rawVar fn) source target →
      SlotsRel addresses (params.map (T.rawVar fn)) values words →
      params.length = values.length → (∀ x ∈ params, x < bound) →
      ∃ after, Lir.bindParams target params words = some after ∧
        FusedWords addresses (Omit T fn fd) bound (Own.bindAll source params values) after ∧
        RawWords (T.rawVar fn) (Own.bindAll source params values) after
  | [], [], [], _, _, related, raws, _, _, _ => ⟨_, rfl, related, raws⟩
  | x :: params, value :: values, word :: words, source, target, related, raws, .cons hv tail,
      length, real => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at length
    have hx : x < bound := real x (by simp)
    simp only [List.map_cons, List.headD_cons] at hv
    have step : FusedWords addresses (Omit T fn fd) bound (source.insert x value) (target.insert x word) ∧
        RawWords (T.rawVar fn) (source.insert x value) (target.insert x word) := by
      have same : ∀ y, y < bound → y ≠ x → (target.insert x word)[y]? = target[y]? :=
        fun y _ ne => Lir.env_insert_ne _ _ (Ne.symm ne)
      cases flag : T.rawVar fn x with
      | false =>
        rw [flag] at hv
        exact ⟨related.bind hx (SlotVal.tagged.1 hv),
          raws.insert_tagged related.dom flag value same⟩
      | true =>
        rw [flag] at hv
        exact ⟨related.bind_raw hx (.inr flag) value word,
          raws.insert_raw related.dom (SlotVal.raw.1 hv) (Lir.env_insert_self ..) same⟩
    obtain ⟨after, binding, words', raws'⟩ := slots_bindParams step.1 step.2
      (by simpa using tail) length (fun y member => real y (by simp [member]))
    exact ⟨after, binding, words', raws'⟩
  | [], _ :: _, _, _, _, _, _, _, length, _ => by simp at length
  | _ :: _, [], _, _, _, _, _, _, length, _ => by simp at length
  | _ :: _, _ :: _, [], _, _, _, _, hrel, _, _ => by cases hrel

end IxCC.Cfg.Rc.Proof.Physical.Bridge

namespace IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC IxCC.Rt.Rc.Procs
open IxCC.Rt.Lower (Tables)

/-- `slots_bindParams` at an already selected binding. -/
theorem slots_boundParams {addresses : AddressMap} {T : Tables} {fn : Nat} {fd : Cfg.Fun}
    {bound : Nat} {params : List Nat} {values : List Own.RVal} {words : List Lir.Word}
    {source : Own.Env} {target after : Lir.Env}
    (related : FusedWords addresses (Omit T fn fd) bound source target)
    (raws : RawWords (T.rawVar fn) source target)
    (represented : SlotsRel addresses (params.map (T.rawVar fn)) values words)
    (length : params.length = values.length) (real : ∀ x ∈ params, x < bound)
    (binding : Lir.bindParams target params words = some after) :
    FusedWords addresses (Omit T fn fd) bound (Own.bindAll source params values) after ∧
      RawWords (T.rawVar fn) (Own.bindAll source params values) after := by
  obtain ⟨actual, actualBinding, w, r⟩ := slots_bindParams related raws represented length real
  have equal : actual = after := Option.some.inj (actualBinding.symm.trans binding)
  subst equal
  exact ⟨w, r⟩

end IxCC.Cfg.Rc.Proof.Physical.Bridge

namespace IxCC.Cfg.Rc.Proof.Physical.Bridge
open IxCC.Rt.Lower (Tables)
open IxCC.Rt.Proof (Fused LiveArg)

/-- An argument at a tagged position that the fusion analysis keeps is kept by the tagged
relation over the omitted registers. -/
theorem live_omit {T : Tables} {fn : Nat} {fd : Cfg.Fun} {a : Fir.Arg}
    (live : LiveArg (Fused T fd) a) (fits : Cfg.Rc.Raw.argFits (T.rawVar fn) false a = true) :
    LiveArg (Omit T fn fd) a := by
  intro y equal omitted
  subst a
  rcases omitted with fused | raw
  · exact live y rfl fused
  · simp [Cfg.Rc.Raw.argFits, raw] at fits

/-- Registers no instruction or terminator of the function reads raw. -/
theorem live_omit_of_noRaw {T : Tables} {fn : Nat} {fd : Cfg.Fun} {a : Fir.Arg}
    (live : LiveArg (Fused T fd) a) (noRaw : ∀ y, T.rawVar fn y = false) :
    LiveArg (Omit T fn fd) a := by
  intro y equal omitted
  rcases omitted with fused | raw
  · exact live y equal fused
  · rw [noRaw] at raw; cases raw

end IxCC.Cfg.Rc.Proof.Physical.Bridge
