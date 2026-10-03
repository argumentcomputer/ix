import Ix.Compile.SourceContract.Elab

/-!
# Resource review probes

Programs from the phase 1.5 review of the resource checker, one namespace
each. `Tests.Ix.SourceContract.Review` compiles every namespace's definitions
through `ix compile`'s resource path with the Lean core profile and checks the
verdict: each violation must be rejected; each control must be accepted.
-/

set_option linter.unusedVariables false

namespace Tests.Ix.SourceContract.ReviewFixture

/-! ## Strict arguments (review F1) -/

/- Violation: `sel` is a user helper, so a strict call evaluates `bump xs`
(a unique move of `xs`) and also passes `xs` on. -/
namespace A01
def bump (! xs : List Nat) : ! List Nat :=
  match xs with
  | [] => []
  | h :: t => (h + 1) :: t
def sel (b : Bool) (x y : List Nat) : List Nat :=
  match b with
  | true => x
  | false => y
def g (b : Bool) (! xs : List Nat) : List Nat := sel b (bump xs) xs
end A01

/- Violation: the dead redex argument `bump xs` moves `xs`, which is then
returned as unique. -/
namespace A04
def bump (! xs : List Nat) : ! List Nat :=
  match xs with
  | [] => []
  | h :: t => (h + 1) :: t
def g (! xs : List Nat) : ! List Nat := (fun (_y : List Nat) => xs) (bump xs)
end A04

/- Violation: `ign` never uses its second parameter, but a strict call still
evaluates `bump xs`. -/
namespace B07
def bump (! xs : List Nat) : ! List Nat :=
  match xs with
  | [] => []
  | h :: t => (h + 1) :: t
def ign (b : Bool) (_d : List Nat) : Bool :=
  match b with
  | true => true
  | false => false
def g (! xs : List Nat) : ! List Nat × Bool := (xs, ign true (bump xs))
end B07

/- Violation: `[1, 2]` is allocated once, yet every call of the closure would
return it as unique. -/
namespace A03b
def keep (! xs : List Nat) : ! List Nat := xs
def mk (_u : Unit) : Nat :=
  let g : (v : Unit) → ! List Nat := (fun (y : List Nat) => fun (_ : Unit) => y) [1, 2]
  (keep (g ())).length + (keep (g ())).length
end A03b

/- Control: a matcher's alternatives are evaluated by need, so each branch
moves `xs` once. -/
namespace M01
def keep (! xs : List Nat) : ! List Nat := xs
def pick (b : Bool) (! xs : List Nat) : ! List Nat :=
  match b with
  | true => keep xs
  | false => keep xs
end M01

/- Control: a match on a local list inspects it (OS-25). -/
namespace M02
def nonEmpty (~ xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | _ :: _ => 1
end M02

/- Control: a recursor application whose minors ignore their hypotheses is
a case split, moving `u` once per branch. -/
namespace I06
def keep (! xs : List Nat) : ! List Nat := xs
noncomputable def f (xs : List Nat) (! u : List Nat) : ! List Nat :=
  @List.rec Nat (fun _ => List Nat) (keep u) (fun _ _ _ => keep u) xs
end I06

/-! ## Captured immediates (review F2) -/

/- Violation: a reusable closure moves its captured unique `String` on every
call: two unique transfers of one heap object. -/
namespace A05b
def keep (! s : String) : ! String := s
def mk (! s : String) : Unit → ! String := fun _ => keep s
def use (! s : String) : Nat :=
  let g := mk s
  (keep (g ())).length + (keep (g ())).length
end A05b

/- Violation: the same with a let-bound closure returned twice. -/
namespace X07
def keep (! s : String) : ! String := s
def f (! s : String) : String × String :=
  let h : (u : Unit) → ! String := fun _ => keep s
  (keep (h ()), keep (h ()))
end X07

/- Control (OS-09): a linear immediate read by a curried closure; its
linearity has no run-time meaning (named assumption). -/
namespace OS09
def lin (1 x : Nat) (1 y : Nat) : Nat := x + y
end OS09

end Tests.Ix.SourceContract.ReviewFixture
