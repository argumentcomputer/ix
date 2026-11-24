module

public import IxCK.Kernel.Model.SortSyn

@[expose] public section

/-!
# The zero-ness of the sort inferred for a type of a wider syntactic class

`SortSyn` (`Model/SortSyn.lean`) fixes the level of every derivation of a sort for its types.
Where only the zero-ness of that level matters (a `Prop` structure's projection guard), a wider
class suffices: the sort of `∀ x : A, B` is `imax u v`, which is zero exactly where `v` is, so the
binder domain `A` may be anything.

* `SortZ env d D v`: a sort; a `∀` whose opened body is in the class (any domain); an application
  spine whose head's type is literal (`SpineSort`);
* `SortZ.zero_iff`: every derivation's level is zero at an assignment exactly where `v` is;
* `SortSyn.sortZ`: the class contains `SortSyn`; `SortZ.mono`, `SortZ.zero_agree`.
-/

namespace Ix.Kernel.Rules

/-- `imax l r` evaluates to zero exactly where `r` does. -/
theorem evalImax_eq_zero_iff (φ : LevelParam → Nat) (l r : Level) :
    Level.eval φ (.imax l r) = 0 ↔ Level.eval φ r = 0 := by
  show (if Level.eval φ r = 0 then 0 else Max.max (Level.eval φ l) (Level.eval φ r)) = 0 ↔
    Level.eval φ r = 0
  split
  · rename_i h
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rename_i h
    exact ⟨fun h2 => absurd (Nat.max_eq_zero_iff.mp h2).2 h, fun h2 => absurd h2 h⟩

/-- **The zero-ness class**: a sort; a `∀` whose body, opened at the variable of depth `d`, is
in the class (the domain is unconstrained); an application spine whose head's type is literal and
leaves no binder. `v` has the zero-ness of every derivation's sort. -/
inductive SortZ (env : Env md) : Nat → Expr md → Level → Prop
  | sort {d : Nat} {u : Level} : SortZ env d (.sort u) (.succ u)
  | forallE {d : Nat} {ty body : Expr md} {m : BinderMeta} {v : Level} :
      SortZ env (d + 1) (body.instantiate1 (.fvar d ty)) v → SortZ env d (.forallE ty body m) v
  | spine {d : Nat} {e : Expr md} {v : Level} :
      SpineSort env e 0 v → SortZ env d e v

/-- **Every derivation's sort has the class's zero-ness**, at every assignment. -/
theorem SortZ.zero_iff {env : Env md} {d : Nat} {D : Expr md} {v : Level}
    (hs : SortZ env d D v) :
    ∀ {g : Grade} {T : Expr md} {u : Level}, Infer env g d D T → Red env d T (.sort u) →
      ∀ ψ : LevelParam → Nat, Level.eval ψ u = 0 ↔ Level.eval ψ v = 0 := by
  induction hs with
  | sort =>
    intro g T u hI hR ψ
    cases hI
    rw [Red.sort_eq hR]
  | forallE _ ihB =>
    intro g T u hI hR ψ
    cases hI with
    | forallE hIA hRA hIB hRB _ =>
      rw [Red.sort_eq hR, evalImax_eq_zero_iff]
      exact ihB hIB hRB ψ
  | spine hsp =>
    intro g T u hI hR ψ
    have h := hsp.infer hI
    cases h
    rw [Red.sort_eq hR]

/-- The class contains `SortSyn`, at the same level's zero-ness. -/
theorem SortSyn.sortZ {env : Env md} {d : Nat} {D : Expr md} {v : Level}
    (hs : SortSyn env d D v) : ∃ w, SortZ env d D w ∧
      ∀ ψ : LevelParam → Nat, Level.eval ψ v = 0 ↔ Level.eval ψ w = 0 := by
  induction hs with
  | sort => exact ⟨_, .sort, fun _ => Iff.rfl⟩
  | forallE _ _ _ ihB =>
    obtain ⟨w, hw, hiff⟩ := ihB
    exact ⟨w, .forallE hw, fun ψ => (evalImax_eq_zero_iff ψ _ _).trans (hiff ψ)⟩
  | spine hsp => exact ⟨_, .spine hsp, fun _ => Iff.rfl⟩

theorem SortZ.mono {env env' : Env md}
    (hext : ∀ (c : Key md) (ci : ConstantInfo md), env.find? c = some ci → env'.find? c = some ci)
    {d : Nat} {D : Expr md} {v : Level} (hs : SortZ env d D v) : SortZ env' d D v := by
  induction hs with
  | sort => exact .sort
  | forallE _ ihB => exact .forallE ihB
  | spine hsp => exact .spine (hsp.mono hext)

/-- **Two derivations of a sort for a type of the class agree in zero-ness**: at an environment
and at one that keeps its lookups, at any grades and at every assignment. -/
theorem SortZ.zero_agree {env env' : Env md}
    (hext : ∀ (c : Key md) (ci : ConstantInfo md), env.find? c = some ci → env'.find? c = some ci)
    {d : Nat} {D : Expr md} {v : Level} (hs : SortZ env d D v)
    {g g' : Grade} {T T' : Expr md} {u u' : Level}
    (hI : Infer env g d D T) (hR : Red env d T (.sort u))
    (hI' : Infer env' g' d D T') (hR' : Red env' d T' (.sort u')) (ψ : LevelParam → Nat) :
    Level.eval ψ u = 0 ↔ Level.eval ψ u' = 0 :=
  (hs.zero_iff hI hR ψ).trans ((hs.mono hext).zero_iff hI' hR' ψ).symm

end Ix.Kernel.Rules
