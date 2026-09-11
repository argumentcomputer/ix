import Ix.Compiler.X86.ScalarObject

namespace Ix.Compiler.X86.Scalar

def Atom.natEval (values : Array Nat) : Atom → Option Nat
  | .var index => values[index]?
  | .constant word => some word.toNat

/-- Unbounded source arithmetic. Successful word execution refines this
relation; an overflowing intermediate returns the separate fallback tag. -/
inductive NatEvaluates (functions : Array Function) : Expr → Array Nat → Nat → Prop where
  | atom {values : Array Nat} {source : Atom} {value : Nat}
      (found : source.natEval values = some value) : NatEvaluates functions (.atom source) values value
  | add {values : Array Nat} {left right : Atom} {a b : Nat}
      (leftValue : left.natEval values = some a) (rightValue : right.natEval values = some b) :
      NatEvaluates functions (.add left right) values (a + b)
  | sub {values : Array Nat} {left right : Atom} {a b : Nat}
      (leftValue : left.natEval values = some a) (rightValue : right.natEval values = some b) :
      NatEvaluates functions (.sub left right) values (a - b)
  | letE {values : Array Nat} {value body : Expr} {bound result : Nat}
      (first : NatEvaluates functions value values bound)
      (rest : NatEvaluates functions body (values.push bound) result) :
      NatEvaluates functions (.letE value body) values result
  | zero {values : Array Nat} {scrutinee : Atom} {zero successor : Expr} {result : Nat}
      (scrutineeValue : scrutinee.natEval values = some 0) (taken : NatEvaluates functions zero values result) :
      NatEvaluates functions (.branch scrutinee zero successor) values result
  | successor {values : Array Nat} {scrutinee : Atom} {zero successor : Expr} {value result : Nat}
      (scrutineeValue : scrutinee.natEval values = some value) (positive : value ≠ 0)
      (taken : NatEvaluates functions successor values result) :
      NatEvaluates functions (.branch scrutinee zero successor) values result
  | call {values supplied : Array Nat} {function : Nat} {arguments : Array Atom} {callee : Function} {result : Nat}
      (found : functions[function]? = some callee)
      (argumentsAt : arguments.mapM (Atom.natEval values) = some supplied)
      (arity : supplied.size = callee.parameters) (evaluated : NatEvaluates functions callee.body supplied result) :
      NatEvaluates functions (.call function arguments) values result

theorem Atom.toNat {source : Atom} {values : Array Word} {word : Word}
    (found : source.eval values = some word) : source.natEval (values.map UInt64.toNat) = some word.toNat := by
  cases source <;> simp_all [Atom.eval, Atom.natEval]

theorem list_mapM_transform {α β γ : Type} {f : α → Option β} {g : α → Option γ} (convert : β → γ)
    (related : ∀ item value, f item = some value → g item = some (convert value))
    {items : List α} {values : List β} (mapped : items.mapM f = some values) :
    items.mapM g = some (values.map convert) := by
  induction items generalizing values with
  | nil => simp at mapped; subst values; simp
  | cons item items ih =>
      cases first : f item with
      | none => simp [List.mapM_cons, first] at mapped
      | some value =>
          cases rest : items.mapM f with
          | none => simp [List.mapM_cons, first, rest] at mapped
          | some tail =>
              simp [List.mapM_cons, first, rest] at mapped
              subst values
              simp [List.mapM_cons, related item value first, ih rest]

theorem array_mapM_transform {α β γ : Type} {f : α → Option β} {g : α → Option γ} (convert : β → γ)
    (related : ∀ item value, f item = some value → g item = some (convert value))
    {items : Array α} {values : Array β} (mapped : items.mapM f = some values) :
    items.mapM g = some (values.map convert) := by
  have lists : items.toList.mapM f = some values.toList := by
    have same := congrArg (Option.map Array.toList) mapped
    change (Array.toList <$> items.mapM f) = some values.toList at same
    simpa only [Array.toList_mapM, Option.map_some] using same
  have transformed := list_mapM_transform convert related lists
  simp only [Array.mapM_eq_mapM_toList, transformed]
  change some ((values.toList.map convert).toArray) = some (values.map convert)
  apply congrArg some
  apply Array.toList_inj.mp
  simp

/-- No successful native result silently wraps. Every successful path,
including all nested calls and joins, computes the exact source Nat. -/
theorem Evaluates.exact {functions : Array Function} {expression : Expr} {values : Array Word} {result : Option Word}
    (evaluated : Evaluates functions expression values result) :
    ∀ word, result = some word → NatEvaluates functions expression (values.map UInt64.toNat) word.toNat := by
  induction evaluated with
  | atom found =>
      intro word same; cases Option.some.inj same
      exact .atom (Atom.toNat found)
  | add left right =>
      intro word same
      have sum := ExactNat.add_some_iff.mp same
      rw [sum]
      exact .add (Atom.toNat left) (Atom.toNat right)
  | sub left right =>
      intro word same; cases Option.some.inj same
      rw [ExactNat.sub_toNat]
      exact .sub (Atom.toNat left) (Atom.toNat right)
  | letE first rest ihFirst ihRest =>
      intro word same
      exact .letE (ihFirst _ rfl) (by simpa using ihRest word same)
  | letOverflow => intro word impossible; contradiction
  | zero found taken ih =>
      intro word same
      exact .zero (Atom.toNat found) (ih word same)
  | @successor values scrutinee zero successor value result found positive taken ih =>
      intro word same
      exact .successor (Atom.toNat found) (by intro equal; apply positive; exact UInt64.toNat_inj.mp equal) (ih word same)
  | call found argumentsAt arity evaluated ih =>
      intro word same
      exact .call found (array_mapM_transform UInt64.toNat (fun _ _ h => Atom.toNat h) argumentsAt)
        (by simpa using arity) (ih word same)

def encodeArguments (values : Array Nat) : Option (Array Word) := values.mapM ExactNat.encode

theorem encodeArguments_exact {values : Array Nat} {words : Array Word} (encoded : encodeArguments values = some words) :
    words.map UInt64.toNat = values := by
  have mapped := array_mapM_transform UInt64.toNat (f := ExactNat.encode) (g := some)
    (fun _ _ encoded => by rw [ExactNat.encode_some_iff.mp encoded]) encoded
  have pureMap : values.mapM (some : Nat → Option Nat) = some values := by
    have lists (items : List Nat) : items.mapM (some : Nat → Option Nat) = some items := by
      induction items with
      | nil => rfl
      | cons head tail ih => simp [List.mapM_cons, ih]
    simp [Array.mapM_eq_mapM_toList, lists]
  rw [pureMap] at mapped
  exact (Option.some.inj mapped).symm

end Ix.Compiler.X86.Scalar
