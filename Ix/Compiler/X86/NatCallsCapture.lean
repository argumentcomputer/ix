import Ix.Compiler.X86.NatCallsSyntax

namespace Ix.Compiler.X86.NatCalls

/-- Static capture expressions cannot refer to the caller's Nat parameter.
Callees may use their own parameter, supplied by a closed argument. -/
def Expr.closed : Expr → Bool
  | .argument => false
  | .constant _ => true
  | .successor value | .call _ value => value.closed

theorem Expr.closed_evaluate {expression : Expr} (closed : expression.closed = true)
    (functions : Array Function) (fuel left right : Nat) :
    evaluate functions fuel expression left = evaluate functions fuel expression right := by
  induction fuel generalizing expression left right with
  | zero => rfl
  | succ fuel ih =>
      cases expression with
      | argument => simp [Expr.closed] at closed
      | constant value => rfl
      | successor value => simp only [evaluate, ih (expression := value) closed left right]
      | call function value => simp only [evaluate, ih (expression := value) closed left right]

structure StaticCapture (functions : Array Function) (expression : Expr) (fuel : Nat) where
  closed : expression.closed = true
  word : Word
  evaluated : evaluate functions fuel expression 0 = .ok word.toNat

/-- Check exact capture representation while retaining its original
expression for native emission. The initializer is not replaced by its Nat
result, and no open expression is evaluated using a guessed argument. -/
def checkCapture (functions : Array Function) (expression : Expr) (fuel : Nat) :
    Except Error (StaticCapture functions expression fuel) := do
  if closed : expression.closed = true then
    match evaluated : evaluate functions fuel expression 0 with
    | .error error => throw error
    | .ok number =>
      let word := UInt64.ofNat number
      if exact : word.toNat = number then
        return { closed, word, evaluated := by simpa [exact] using evaluated }
      else throw .wordOverflow
  else throw .dynamicCapture

theorem StaticCapture.evaluates {functions expression fuel}
    (capture : StaticCapture functions expression fuel) (argument : Nat) :
    evaluate functions fuel expression argument = .ok capture.word.toNat :=
  (expression.closed_evaluate capture.closed functions fuel argument 0).trans capture.evaluated

end Ix.Compiler.X86.NatCalls
