/- Fixture of the caller-independence gate (`Tests/Ix/Compile/CallerIndependence.lean`,
suite `compile-caller-independence`), elaborated at run time and in no Lake library.

Each case is a block, the rest of its logical unit, and dependents that are not auxiliaries of the
unit; the gate compiles the block's unit with and without the dependents.

- `T`: an inductive block. `T.a.hinj` is an on-demand auxiliary of its unit (a reserved name Lean
  realises when a later declaration asks for it, here `useHinj`).
- `WP`/`WQ`: the same two-function well-founded clique in both member orders, so that one of
  them is changed (transported under the switch). Each has an external caller that unfolds
  Lean's encoding (`*.caller` mentions the member and `all₀._mutual`) and equation lemmas realised
  by a later proof (`*.useEqns`, by `simp`).
- `SA`/`SB`: a mutual block that splits (`SA` has a field into `SB`); O11a rewrites
  `SA._sizeOf_1` through `SB._sizeOf_inst`. Dependents: `SA.depth`, `sizeA`.
- `Unrelated`: constants that reference none of the above, used in place of the dependents. -/
set_option Elab.async false

namespace CallerInd

/-! ## An inductive block with an on-demand auxiliary -/

inductive T where
  | a : Nat → T
  | b : T → T

theorem useHinj {x y : Nat} (h : T.a x = T.a y) : x = y := T.a.hinj h

def T.depth : T → Nat
  | .a _ => 0
  | .b t => t.depth + 1

theorem T.depth_b (t : T) : (T.b t).depth = t.depth + 1 := rfl

/-! ## A well-founded clique, in both member orders, with external unfolding callers -/

namespace WP
mutual
def wa (n : Nat) : Nat := if h : n ≤ 1 then n else wb (n - 2) + 1
def wb (n : Nat) : Nat := if h : n = 0 then 0 else wa (n - 1) + 2
end
theorem useEqns : wa 3 = 3 := by simp [wa, wb]
theorem caller (n : Nat) : wa n = wa._mutual (PSum.inl n) := by delta wa; rfl
end WP

namespace WQ
mutual
def wb (n : Nat) : Nat := if h : n = 0 then 0 else wa (n - 1) + 2
def wa (n : Nat) : Nat := if h : n ≤ 1 then n else wb (n - 2) + 1
end
theorem useEqns : wa 3 = 3 := by simp [wa, wb]
theorem caller (n : Nat) : wb n = wb._mutual (PSum.inl n) := by delta wb; rfl
end WQ

/-! ## A split mutual block (O11a) with dependents -/

mutual
inductive SA
  | a : SB → SA
  | stop : SA
inductive SB
  | b : SB → SB
  | leaf : SB
end

def SA.depth : SA → Nat
  | .a _ => 1
  | .stop => 0

theorem sizeA (s : SB) : sizeOf (SA.a s) = 1 + sizeOf s := by simp

/-! ## Unrelated constants -/

namespace Unrelated
inductive U where
  | u : Bool → U
def flip : U → U
  | .u b => .u !b
theorem flip_flip (x : U) : flip (flip x) = x := by cases x; simp [flip]
end Unrelated

end CallerInd
