import Ix.Compiler.X86.ScalarSimulation

namespace Ix.Compiler.X86.Scalar

theorem Atom.total {value : Atom} {values : Array Word} (valid : value.valid values.size = true) :
    ∃ word, value.eval values = some word := by
  cases value with
  | constant word => exact ⟨word, rfl⟩
  | var index =>
      have bound : index < values.size := by simpa [Atom.valid] using valid
      exact ⟨values[index], Array.getElem?_eq_getElem bound⟩

theorem arguments_total {arguments : Array Atom} {values : Array Word}
    (small : arguments.size ≤ 2) (valid : arguments.all (·.valid values.size) = true) :
    ∃ supplied, arguments.mapM (Atom.eval values) = some supplied ∧ supplied.size = arguments.size := by
  rcases array_le_two arguments small with rfl | ⟨first, rfl⟩ | ⟨first, second, rfl⟩
  · exact ⟨#[], by simp [Array.mapM_eq_mapM_toList], rfl⟩
  · have firstValid := Array.all_eq_true.mp valid 0 (by simp)
    obtain ⟨word, evaluated⟩ := Atom.total firstValid
    change first.eval values = some word at evaluated
    exact ⟨#[word], by simp [Array.mapM_eq_mapM_toList, evaluated], rfl⟩
  · have firstValid := Array.all_eq_true.mp valid 0 (by simp)
    have secondValid := Array.all_eq_true.mp valid 1 (by simp)
    obtain ⟨left, leftValue⟩ := Atom.total firstValid
    obtain ⟨right, rightValue⟩ := Atom.total secondValid
    change first.eval values = some left at leftValue
    change second.eval values = some right at rightValue
    exact ⟨#[left, right], by simp [Array.mapM_eq_mapM_toList, leftValue, rightValue], rfl⟩

theorem Expr.total {functions : Array Function} {current : Nat}
    (callees : ∀ index, index < current → ∀ function, functions[index]? = some function →
      ∀ values : Array Word, values.size = function.parameters → ∃ result, Evaluates functions function.body values result)
    (expression : Expr) (values : Array Word) (valid : expression.valid functions current values.size = true) :
    ∃ result, Evaluates functions expression values result := by
  induction expression generalizing values with
  | atom source =>
      obtain ⟨value, found⟩ := Atom.total valid
      exact ⟨some value, .atom found⟩
  | add left right =>
      simp only [Expr.valid, Bool.and_eq_true] at valid
      obtain ⟨a, leftValue⟩ := Atom.total valid.1
      obtain ⟨b, rightValue⟩ := Atom.total valid.2
      exact ⟨ExactNat.add a b, .add leftValue rightValue⟩
  | sub left right =>
      simp only [Expr.valid, Bool.and_eq_true] at valid
      obtain ⟨a, leftValue⟩ := Atom.total valid.1
      obtain ⟨b, rightValue⟩ := Atom.total valid.2
      exact ⟨some (ExactNat.sub a b), .sub leftValue rightValue⟩
  | letE value body ihValue ihBody =>
      simp only [Expr.valid, Bool.and_eq_true] at valid
      obtain ⟨first, evaluated⟩ := ihValue values valid.1.2
      cases first with
      | none => exact ⟨none, .letOverflow evaluated⟩
      | some first =>
          obtain ⟨result, rest⟩ := ihBody (values.push first) (by simpa using valid.2)
          exact ⟨result, .letE evaluated rest⟩
  | branch scrutinee zero successor ihZero ihSuccessor =>
      simp only [Expr.valid, Bool.and_eq_true] at valid
      obtain ⟨value, found⟩ := Atom.total valid.1.1
      by_cases empty : value = 0
      · subst value
        obtain ⟨result, taken⟩ := ihZero values valid.1.2
        exact ⟨result, .zero found taken⟩
      · obtain ⟨result, taken⟩ := ihSuccessor values valid.2
        exact ⟨result, .successor found empty taken⟩
  | call function arguments =>
      simp only [Expr.valid, Bool.and_eq_true, decide_eq_true_eq] at valid
      cases found : functions[function]? with
      | none => simp only [found, Bool.false_eq_true, and_false] at valid
      | some callee =>
          obtain ⟨supplied, mapped, size⟩ := arguments_total valid.1.1.2 valid.1.2
          have arity : supplied.size = callee.parameters := by
            rw [size]
            simpa only [found, beq_iff_eq] using valid.2
          obtain ⟨result, evaluated⟩ := callees function valid.1.1.1 callee found supplied arity
          exact ⟨result, .call found mapped arity evaluated⟩

/-- Accepted nonrecursive functions have a result for every well-formed
runtime argument array. `none` is the explicit arithmetic fallback result. -/
theorem Checked.function_total (checked : Checked) (index : Nat) (function : Function)
    (found : checked.program.functions[index]? = some function) (values : Array Word)
    (arity : values.size = function.parameters) :
    ∃ result, Evaluates checked.program.functions function.body values result := by
  induction index using Nat.strongRecOn generalizing function values with
  | ind index ih =>
      apply Expr.total (fun callee smaller body located supplied suppliedArity => ih callee smaller body located supplied suppliedArity)
      simpa only [arity] using (checked.function_valid found).2

end Ix.Compiler.X86.Scalar
