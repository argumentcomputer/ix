/-
  The clique library's own fixtures (`Ix.Compile.Pass.Clique`), for the
  suites `clique-recognition` and `clique-transport`
  (`Tests/Ix/Compile/Clique/{Recognition,Transport}.lean`).

  Like the twin families, they stay out of the environment every other
  suite reads with `get_env!`: the `TwinsFixtures` root
  (`Tests/Ix/Compile/Twins/Fixtures.lean`) imports this module and the
  suites load it at run time (`Tests.Ix.Compile.Twins.fixturesEnv`). The
  adversarial declarations below carry the names of encoding constants
  (`match_1`, `brecOn`, `below`) on purpose.

  * Recognition controls: user values of a clique's packing type, repeated
    fixed arguments, a user `Nat` dispatcher, a `partial_fixpoint` clique
    and its canonical twin whose functional passes a user projection of the
    packing type, a well-founded clique whose body states a user relation
    on the packing type, and the frozen outputs of the deleted shape routes.
  * `Adversarial`: user declarations named like encoding constants (a
    `match_1` with an ordinary body, two matcher-shaped `match_1`s of one
    type whose bodies differ, `below`/`brecOn` of a non-recursive
    structure). The
    suites build the remaining adversarial inputs (a decoy `f._f`, an
    altered `brecOn`, a matcher whose body is not an eliminator) from these
    and the twin families, as overlays of the environment.
-/

namespace Tests.Ix.Compile.Clique.Fixtures

def userPair : PProd Nat Nat := ⟨17, 29⟩
def userFirst (p : PProd Nat Nat) : Nat := p.fst
def repeatedPFPacked (a b : Nat) : PProd Nat Nat := ⟨a, b⟩
def repeatedPFFirst (a : Nat) : Nat := (repeatedPFPacked a a).fst
def repeatedPFSecond (a : Nat) : Nat := (repeatedPFPacked a a).snd
def repeatedWFPacked (a b : Nat) : PSum Nat Nat → Nat
  | .inl n => a + n
  | .inr n => b + n
def repeatedWFFirst (a n : Nat) : Nat := repeatedWFPacked a a (.inl n)
def repeatedWFSecond (a n : Nat) : Nat := repeatedWFPacked a a (.inr n)

namespace RepeatedStructural
mutual
def first (a b : Nat) : Nat → Nat
  | 0 => a
  | n + 1 => second a b n
def second (a b : Nat) : Nat → Nat
  | 0 => b
  | n + 1 => first a b n
end
end RepeatedStructural
def sideRank : PSum Nat Nat → Nat
  | .inl _ => 0
  | .inr _ => 1
set_option warn.classDefReducibility false in
def userWF (α : Type) (rank : α → Nat) : WellFoundedRelation α :=
  invImage rank (inferInstance : WellFoundedRelation Nat)

def wgLeft : PSum (PSigma fun _ : Nat => Nat) (PSigma fun _ : Nat => Nat) :=
  .inl ⟨7, 11⟩
def wgRight : PSum (PSigma fun _ : Nat => Nat) (PSigma fun _ : Nat => Nat) :=
  .inr ⟨7, 11⟩

private def userNatDispatch (_motive : Nat → Type) (_n : Nat)
    (_zero : Unit → Nat) (_succ : Nat → Nat) : Nat := 17

abbrev UserFn := Nat → Option Nat
def userFns : PProd (Nat → Option Nat) (Nat → Option Nat) :=
  ⟨fun _ => some 17, fun _ => some 29⟩
def applyUserProjection (q : PProd (Nat → Option Nat) (Nat → Option Nat))
    (select : PProd (Nat → Option Nat) (Nat → Option Nat) → (Nat → Option Nat))
    (n : Nat) : Option Nat := select q n

mutual
def actualFirst (q : PProd (Nat → Option Nat) (Nat → Option Nat)) (n : Nat) : Option Nat :=
  if n = 0 then applyUserProjection q (fun p => p.fst) n else actualSecond q (n - 1)
partial_fixpoint
def actualSecond (q : PProd (Nat → Option Nat) (Nat → Option Nat)) (n : Nat) : Option Nat :=
  if n = 0 then some 31 else actualFirst q (n - 1)
partial_fixpoint
end

example (q : PProd (Nat → Option Nat) (Nat → Option Nat)) (n : Nat) :
    actualFirst q n =
      (if n = 0 then applyUserProjection q (fun p => p.fst) n else actualSecond q (n - 1)) :=
  actualFirst.eq_def q n

example (q : PProd (Nat → Option Nat) (Nat → Option Nat)) (n : Nat) :
    actualSecond q n = (if n = 0 then some 31 else actualFirst q (n - 1)) :=
  actualSecond.eq_def q n

mutual
def actualSecondTwin (q : PProd (Nat → Option Nat) (Nat → Option Nat)) (n : Nat) : Option Nat :=
  if n = 0 then some 31 else actualFirstTwin q (n - 1)
partial_fixpoint
def actualFirstTwin (q : PProd (Nat → Option Nat) (Nat → Option Nat)) (n : Nat) : Option Nat :=
  if n = 0 then applyUserProjection q (fun p => p.fst) n else actualSecondTwin q (n - 1)
partial_fixpoint
end

def ignoreRecursive (_ : Nat → Option Nat) (q : PProd (Nat → Option Nat) (Nat → Option Nat))
    (select : PProd (Nat → Option Nat) (Nat → Option Nat) → Nat → Option Nat) : Nat → Option Nat := select q

/-- The user projection shares an application with the actual recursive
binder and shadows its printed name. Neither fact grants ownership. -/
def binderMentionControl (r : PProd (Nat → Option Nat) (Nat → Option Nat)) :
    PProd (Nat → Option Nat) (Nat → Option Nat) :=
  ⟨ignoreRecursive r.fst userFns (fun r => r.fst), fun _ => some 31⟩

def userTag {α : Type} (_ : α) : Nat := 17

namespace FixedP0
mutual
def first (α : Type) (a : α) (b n : Nat) : Option Nat :=
  if n = 0 then some (userTag a + b) else second b α a (n - 1)
partial_fixpoint
def second (b : Nat) (α : Type) (a : α) (n : Nat) : Option Nat :=
  if n = 0 then some (userTag a + b + 1) else first α a b (n - 1)
partial_fixpoint
end
end FixedP0

namespace FixedP1
mutual
def second (b : Nat) (α : Type) (a : α) (n : Nat) : Option Nat :=
  if n = 0 then some (userTag a + b + 1) else first α a b (n - 1)
partial_fixpoint
def first (α : Type) (a : α) (b n : Nat) : Option Nat :=
  if n = 0 then some (userTag a + b) else second b α a (n - 1)
partial_fixpoint
end
end FixedP1

mutual
def actualWFFirst (n : Nat) : Prop :=
  if n = 0 then
    (userWF (PSum Nat Nat) sideRank).rel (PSum.inl 0) (PSum.inr 0)
  else actualWFSecond (n - 1)
termination_by n
def actualWFSecond (n : Nat) : Prop :=
  if n = 0 then True else actualWFFirst (n - 1)
termination_by n
end

/-! Frozen outputs of the deleted shape routes (`transportWFShape`,
`transportPFShape`). They were recorded by running those routes on the
clique above, at the last revision that still had them, just before the
commit that introduced these definitions deleted them (the ownership
boundary that replaced them is in the module docstrings of
`Ix/Compile/Pass/Clique/WFConjugation.lean` and `PFConjugation.lean`). Each
is the user-facing part of the old route's output on the clique with
`σ = [1, 0]`, kept so that the negative controls still show what the
shape-based recognition did, without keeping the code that did it:

* WF (`actualWFFirst`/`actualWFSecond`): the user's predicate
  `(userWF (PSum Nat Nat) sideRank).rel (PSum.inl 0) (PSum.inr 0)` (`0 < 1`)
  came out with its injections swapped (`1 < 0`);
* PF (`actualFirst`/`actualSecond`): the user's selector `fun p => p.fst`
  passed to `applyUserProjection` came out as `fun p => p.snd` (`some 17`
  became `some 29`). -/
def frozenOldWFPredicate : Prop := (userWF (PSum Nat Nat) sideRank).rel (PSum.inr 0) (PSum.inl 0)
def frozenOldPFSelector : PProd (Nat → Option Nat) (Nat → Option Nat) → (Nat → Option Nat) :=
  fun p => p.snd

example : actualWFFirst 0 := by
  rw [actualWFFirst]
  exact (show (0 : Nat) < 1 by decide)

/-! ## Adversarial declarations

User declarations named like encoding constants. The library recognises
encodings by their declarations and by the block's authenticated family,
never by name (`Structural.lean`: "A matcher is recognised by its
declaration, not by its name", "The `below`/`brecOn` family is
authenticated, never found by name"; `Recover.lean`: the member's
functional must be one the `brecOn` applications pass). -/
namespace Adversarial

universe u

/-- A user definition named like a matcher, with an ordinary body. -/
def helper.match_1 (n : Nat) : Nat := n + 1

/-- A user function that does a case split (it is not an eliminator: its
body applies `Nat.casesOn`, which is a definition, not a recursor). -/
def userCases (motive : Nat → Sort u) (n : Nat)
    (zero : Unit → motive 0) (succ : (k : Nat) → motive (k + 1)) : motive n :=
  Nat.casesOn (motive := motive) n (zero ()) succ

/-- A matcher-shaped declaration (two closure parameters, a motive, one
discriminant, alternatives concluding in the motive) whose body is a
`casesOn`: the shape the library accepts. -/
def Shape.good.match_1 (_F _G : Nat → Prop) (motive : Nat → Sort u) (n : Nat)
    (zero : Unit → motive 0) (succ : (k : Nat) → motive (k + 1)) : motive n :=
  Nat.casesOn (motive := motive) n (zero ()) succ

/-- The same type, with a body that applies a user function instead of an
eliminator. -/
def Shape.bad.match_1 (_F _G : Nat → Prop) (motive : Nat → Sort u) (n : Nat)
    (zero : Unit → motive 0) (succ : (k : Nat) → motive (k + 1)) : motive n :=
  userCases motive n zero succ

/-- A non-recursive structure: Lean generates no `below`/`brecOn` for it,
so the two definitions after it carry those names outside any family. -/
structure Pair where
  fst : Nat
  snd : Nat

def Pair.below (_p : Pair) : Type := Unit
def Pair.brecOn (p : Pair) (_F : Nat → Nat) : Nat := p.fst

end Adversarial

end Tests.Ix.Compile.Clique.Fixtures
