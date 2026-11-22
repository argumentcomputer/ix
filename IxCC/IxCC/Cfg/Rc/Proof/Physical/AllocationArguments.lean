import IxCC.Cfg.Rc.Proof.Physical.Placement
import IxCC.Rt.Proof.StepFrame

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Rt IxCC.Rt.Rc.Procs
open IxCC.Rt.Proof (ListRel)

/-- Operand lowering reads the current physical address map, including
recycled live addresses. Nat literals keep the existing bounded encoding. -/
theorem operand_word {addresses : AddressMap} {bound : Nat}
    {source : Own.Env} {target : Lir.Env}
    (related : EnvWordsBelow addresses bound source target)
    {f : Fir.FunId} {a : Fir.Arg} {operand : Lir.Arg} {value : Own.RVal}
    (lowered : Lower.operand f a = .ok (some operand))
    (real : ∀ x, a = .var x → x < bound)
    (evaluated : Own.evalArg source a = some value) :
    ∃ word, operand.eval target = some word ∧ valueWord addresses value = some word := by
  cases a with
  | var x =>
    simp only [Lower.operand, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at lowered
    subst operand
    obtain ⟨word, hw, hr⟩ := related x value (real x rfl) evaluated
    exact ⟨word, hr, hw⟩
  | lit literal =>
    cases literal with
    | nat n =>
      simp only [Own.evalArg, Option.some.injEq] at evaluated
      subst value
      cases hn : natWord n with
      | none => simp [Lower.operand, hn, pure, Except.pure] at lowered
      | some word =>
        simp only [Lower.operand, hn, Option.map_some, pure, Except.pure,
          Except.ok.injEq, Option.some.injEq] at lowered
        subst operand
        exact ⟨word, rfl, hn⟩
    | str s => simp [Lower.operand, throw, throwThe, MonadExceptOf.throw] at lowered
  | erased =>
    simp only [Lower.operand, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at lowered
    subst operand
    simp only [Own.evalArg, Option.some.injEq] at evaluated
    subst value
    exact ⟨erasedWord, rfl, rfl⟩

theorem operands_words {addresses : AddressMap} {bound : Nat}
    {source : Own.Env} {target : Lir.Env}
    (related : EnvWordsBelow addresses bound source target) {f : Fir.FunId} :
    ∀ {args : List Fir.Arg} {operands : List Lir.Arg},
      Lower.operands f args = .ok (some operands) →
      (∀ x, Fir.Arg.var x ∈ args → x < bound) →
      ∀ {fields : List Own.RVal}, Own.evalArgs source args = some fields →
      ∃ words, Lir.evalArgs target operands = some words ∧
        ListRel (fun value word => valueWord addresses value = some word) fields words
  | [], operands, lowered, _, fields, evaluated => by
    simp only [Lower.operands, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at lowered
    subst operands
    simp only [Own.evalArgs, Option.some.injEq] at evaluated
    subst fields
    exact ⟨[], rfl, .nil⟩
  | a :: args, operands, lowered, real, fields, evaluated => by
    simp only [Lower.operands, bind, Except.bind] at lowered
    cases ha : Lower.operand f a with
    | error e => simp [ha] at lowered
    | ok oa =>
      cases has : Lower.operands f args with
      | error e => simp [ha, has] at lowered
      | ok oas =>
        simp only [ha, has, pure, Except.pure, Except.ok.injEq] at lowered
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
              | some values =>
                simp only [hva, hvas, Option.some.injEq] at evaluated
                subst fields
                obtain ⟨word, hw, hv⟩ := operand_word related ha
                  (fun x hx => real x (by simp [hx])) hva
                obtain ⟨words, hws, hvs⟩ := operands_words related has
                  (fun x hx => real x (by simp [hx])) hvas
                exact ⟨word :: words, by simp [hw, hws], .cons hv hvs⟩

private theorem evalArgs_at {env : Lir.Env} :
    ∀ {args : List Lir.Arg} {words : List Lir.Word}, Lir.evalArgs env args = some words →
      ∀ {i : Nat} {arg : Lir.Arg}, args[i]? = some arg → arg.eval env = words[i]?
  | [], _, h, i, arg, hi => by simp at hi
  | a :: args, words, h, i, arg, hi => by
    simp only [Lir.evalArgs_cons] at h
    cases ha : a.eval env with
    | none => simp [ha] at h
    | some word =>
      cases hs : Lir.evalArgs env args with
      | none => simp [ha, hs] at h
      | some tail =>
        simp [ha, hs] at h
        subst words
        cases i with
        | zero =>
          have same : a = arg := by simpa using hi
          subst arg
          exact ha
        | succ i => exact evalArgs_at hs (by simpa using hi)

/-- The actual wrapper parameter binding supplies every published payload
word at its numeric field register. -/
theorem allocation_bind_arguments {addresses : AddressMap} {fields : List Own.RVal}
    {words : List Lir.Word}
    (related : ListRel (fun value word => valueWord addresses value = some word) fields words) :
    ∃ env : Lir.Env, Lir.bindParams {} (List.range fields.length) words = some env ∧
      (∀ (i : Nat), i < fields.length → env[i]? = some (words[i]?.getD 0)) ∧
      (∀ (i : Nat) (value : Own.RVal), fields[i]? = some value →
        valueWord addresses value = some (words[i]?.getD 0)) := by
  obtain ⟨env, binding⟩ := Rt.Proof.bindParams_some ({} : Lir.Env)
    (ps := List.range fields.length) (ws := words)
    (by simpa using related.length_eq)
  have readings := Rt.Proof.evalArgs_bindParams List.nodup_range binding
  refine ⟨env, binding, ?_, ?_⟩
  · intro i hi
    have indexed : ((List.range fields.length).map Lir.Arg.v)[i]? = some (.v i) := by simp [hi]
    have read := evalArgs_at readings indexed
    have wi : i < words.length := by rw [← related.length_eq]; exact hi
    have hw : words[i]? = some words[i] := List.getElem?_eq_getElem wi
    simpa [Lir.Arg.eval, hw] using read
  · intro i value hv
    obtain ⟨word, hw, represented⟩ := related.get hv
    simpa [hw] using represented




end IxCC.Cfg.Rc.Native
