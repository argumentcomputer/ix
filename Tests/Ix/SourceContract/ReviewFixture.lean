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

/-! ## Induction hypotheses (review F4) -/

/- Violation if the consumer computes hypotheses: the hypothesis is passed to
a dead beta-redex binder; an eager recursor moves `u` once per element. -/
namespace I08
def keep (! xs : List Nat) : ! List Nat := xs
noncomputable def f (xs : List Nat) (! u : List Nat) : ! List Nat :=
  @List.rec Nat (fun _ => List Nat) (keep u) (fun _ _ ih => (fun (_z : List Nat) => keep u) ih) xs
end I08

/- Violation if the consumer computes hypotheses: the hypothesis is used only
in an erased argument. -/
namespace I01
def keep (! xs : List Nat) : ! List Nat := xs
def drop0 (0 _n : List Nat) (! u : List Nat) : ! List Nat := u
noncomputable def f (xs : List Nat) (! u : List Nat) : ! List Nat :=
  @List.rec Nat (fun _ => List Nat) (keep u) (fun _ _ ih => drop0 ih (keep u)) xs
end I01

/-! ## Unfolding equations (review F3) -/

/- Violation: `dup` moves `xs` twice; a forged profile binds it to a
`sorry`-proved false equation, which must not be admitted. -/
namespace E04
def keep (! xs : List Nat) : ! List Nat := xs
def dup (! xs : List Nat) : List Nat × List Nat := (keep xs, keep xs)
theorem dup_eq : ∀ (xs : List Nat), dup xs = ([], []) := sorry
end E04

/- Violation: `dup` moves `xs` twice; a true but different equation exists,
yet `ix compile --equations` binds only realized `eq_def` theorems (none for a
non-recursive definition), so `dup` is checked by its own body. -/
namespace E01
def keep (! xs : List Nat) : ! List Nat := xs
def dup (! xs : List Nat) : ! List Nat :=
  (fun (_a : List Nat) (b : List Nat) => b) (keep xs) (keep xs)
theorem dup_eq : ∀ (xs : List Nat), dup xs = xs := fun _ => rfl
end E01

/- Control (Q06): well-founded recursion with a unique accumulator, checked
through its realized `eq_def`, whose proof uses only standard axioms. -/
namespace Q06
def down (n : Nat) (! acc : List Nat) : ! List Nat :=
  if n = 0 then acc else down (n - 1) (n :: acc)
termination_by n
decreasing_by omega
end Q06

/-! ## Case-split fields (review F5) -/

/- Violation unless fields are owned references: a field of the matched
unique pair is kept while the pair itself is moved uniquely (its projection
twin P02 is rejected). -/
namespace P03
def keepP (! p : List Nat × List Nat) : ! (List Nat × List Nat) := p
def f (! p : List Nat × List Nat) : List Nat × (List Nat × List Nat) :=
  match p with
  | (a, _) => (a, keepP p)
end P03

/- Violation unless fields are owned references: the tail of a unique list is
used after the list is moved (and possibly reused in place). -/
namespace C09
def bump (! xs : List Nat) : ! List Nat :=
  match xs with
  | [] => []
  | h :: t => (h + 1) :: t
def f (! xs : List Nat) : ! List Nat × List Nat :=
  match xs with
  | [] => ([], [])
  | _ :: t => (bump xs, t)
end C09

/-! ## Native implementations (review F7) -/

/- Violation if model bodies were inlined: `String.push`'s Lean body is a
model; its declared result is shared, so `keep` cannot take it as unique. -/
namespace S02
def keep (! s : String) : ! String := s
def f (s : String) : String × String := (keep (s.push (Char.ofNat 97)), s)
end S02

end Tests.Ix.SourceContract.ReviewFixture
