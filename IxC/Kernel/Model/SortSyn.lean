module

public import IxC.Kernel.Rules.Inversion

@[expose] public section

/-!
# The sort inferred for a type of a syntactic class is unique

IxC's inference relation `Rules.Infer` has no conversion rule: its rules for a sort, a `∀`, a
variable, a constant and an application read the subject's head, and the type of an application
is the body of the `∀` its head's type reduces to. A sort or a `∀` reduces only to itself
(`Red.rigid`). So for a type of the class `SortSyn` — a sort; a `∀` whose domain and opened body
are in the class; an application spine of `n` arguments over a variable, or a stored constant,
whose type is `n` literal `∀`s and then a literal sort — every derivation
`Infer env g d D T ∧ Red env d T (.sort u)` has the same `u`: the level read off `D`'s syntax
and the head's type. The arguments' typings, confluence and δ are never needed.

* `PiSortTele n T v`: `T` is `n` literal `∀`s and then `.sort v`; kept by `instantiate1` and by
  level instantiation;
* `SpineSort env e n v`: `e` is an application spine whose head's type, with the spine's
  arguments taken, leaves `n` literal `∀`s and then `.sort v`;
* `SpineSort.infer`: every type inferred for such a spine is `PiSortTele n _ v`;
* `SortSyn env d D v`, `SortSyn.sort_eq`: the level of every derivation is `v`;
* `SpineSort.mono`, `SortSyn.mono`: the class is kept along an environment that keeps the
  lookups;
* `SortSyn.sort_agree`, `SortSyn.eval_zero_iff`: two derivations, at two environments the
  second of which keeps the first's lookups, give equal levels, so they agree in zero-ness.
-/

namespace Ix.Kernel.Rules

/-! ## Literal telescopes ending in a sort -/

/-- **`n` literal `∀`s, then the literal sort `.sort v`.** -/
inductive PiSortTele : Nat → Expr md → Level → Prop
  | sort {v : Level} : PiSortTele 0 (.sort v) v
  | forallE {n : Nat} {ty body : Expr md} {m : BinderMeta} {v : Level} :
      PiSortTele n body v → PiSortTele (n + 1) (.forallE ty body m) v

/-- A literal telescope ending in a sort stays one under `instantiate1`. -/
theorem PiSortTele.instantiate1 {n : Nat} {e : Expr md} {v : Level} (h : PiSortTele n e v) :
    ∀ (a : Expr md) (k : Nat), PiSortTele n (e.instantiate1 a k) v := by
  induction h with
  | sort =>
    intro a k
    simp only [Expr.instantiate1]
    exact .sort
  | forallE _ ih =>
    intro a k
    simp only [Expr.instantiate1]
    exact .forallE (ih a (k + 1))

/-- A literal telescope ending in a sort stays one under level instantiation, at the
instantiated level. -/
theorem PiSortTele.instantiateLevelParams {n : Nat} {e : Expr md} {v : Level}
    (h : PiSortTele n e v) (ks : List LevelParam) (us : List Level) :
    PiSortTele n (e.instantiateLevelParams ks us) (Level.subst ks us v) := by
  induction h with
  | sort =>
    simp only [Expr.instantiateLevelParams]
    exact .sort
  | forallE _ ih =>
    simp only [Expr.instantiateLevelParams]
    exact .forallE ih

/-! ## Spines over a head with a literal type -/

/-- **An application spine whose head's type is literal**: a variable whose annotation, or a
stored constant whose type at the node's levels, is, past the spine's arguments, `n` literal
`∀`s and then `.sort v`. -/
inductive SpineSort (env : Env md) : Expr md → Nat → Level → Prop
  | fvar {idx n : Nat} {ty : Expr md} {v : Level} :
      PiSortTele n ty v → SpineSort env (.fvar idx ty) n v
  | const {c : Key md} {us : List Level} {ci : ConstantInfo md} {n : Nat} {v : Level} :
      env.find? c = some ci →
      PiSortTele n (ci.toConstantVal.type.instantiateLevelParams
        ci.toConstantVal.levelParams us) v →
      SpineSort env (.const c us) n v
  | app {f a : Expr md} {n : Nat} {v : Level} :
      SpineSort env f (n + 1) v → SpineSort env (.app f a) n v

/-- **Every type inferred for such a spine is the head's type past the arguments**: `n` literal
`∀`s and then `.sort v`, at every grade. -/
theorem SpineSort.infer {env : Env md} {e : Expr md} {n : Nat} {v : Level}
    (hs : SpineSort env e n v) :
    ∀ {g : Grade} {d : Nat} {T : Expr md}, Infer env g d e T → PiSortTele n T v := by
  induction hs with
  | fvar hty =>
    intro g d T hI
    cases hI
    exact hty
  | const hf hty =>
    intro g d T hI
    cases hI with
    | const hf' _ _ =>
      rw [hf] at hf'
      cases hf'
      exact hty
  | app _ ih =>
    intro g d T hI
    cases hI with
    | app hIf hred _ _ =>
      have h1 := ih hIf
      cases h1 with
      | forallE hb =>
        have he := Red.rigid hred rfl
        obtain ⟨-, hbody, -⟩ := Expr.forallE.inj he
        rw [hbody]
        exact hb.instantiate1 _ 0
    | appSkip hIf hred _ =>
      have h1 := ih hIf
      cases h1 with
      | forallE hb =>
        have he := Red.rigid hred rfl
        obtain ⟨-, hbody, -⟩ := Expr.forallE.inj he
        rw [hbody]
        exact hb.instantiate1 _ 0

/-! ## The class -/

/-- **The syntactic class**: a sort; a `∀` whose domain and opened body (at the variable of
depth `d`) are in the class; an application spine whose head's type is literal (`SpineSort`) and
leaves no binder. `v` is the level of the class's sort. -/
inductive SortSyn (env : Env md) : Nat → Expr md → Level → Prop
  | sort {d : Nat} {u : Level} : SortSyn env d (.sort u) (.succ u)
  | forallE {d : Nat} {ty body : Expr md} {m : BinderMeta} {u v : Level} :
      SortSyn env d ty u → SortSyn env (d + 1) (body.instantiate1 (.fvar d ty)) v →
      SortSyn env d (.forallE ty body m) (.imax u v)
  | spine {d : Nat} {e : Expr md} {v : Level} :
      SpineSort env e 0 v → SortSyn env d e v

/-- **The sort of every derivation is the class's level**: a type of the class infers, at any
grade, a type that reduces to a sort only at `v`. -/
theorem SortSyn.sort_eq {env : Env md} {d : Nat} {D : Expr md} {v : Level}
    (hs : SortSyn env d D v) :
    ∀ {g : Grade} {T : Expr md} {u : Level}, Infer env g d D T → Red env d T (.sort u) →
      u = v := by
  induction hs with
  | sort =>
    intro g T u hI hR
    cases hI
    exact Red.sort_eq hR
  | forallE _ _ ihA ihB =>
    intro g T u hI hR
    cases hI with
    | forallE hIA hRA hIB hRB _ =>
      have e1 := ihA hIA hRA
      have e2 := ihB hIB hRB
      subst e1 e2
      exact Red.sort_eq hR
  | spine hsp =>
    intro g T u hI hR
    have h := hsp.infer hI
    cases h
    exact Red.sort_eq hR

/-! ## Along an environment that keeps the lookups -/

theorem SpineSort.mono {env env' : Env md}
    (hext : ∀ (c : Key md) (ci : ConstantInfo md), env.find? c = some ci → env'.find? c = some ci)
    {e : Expr md} {n : Nat} {v : Level} (hs : SpineSort env e n v) : SpineSort env' e n v := by
  induction hs with
  | fvar hty => exact .fvar hty
  | const hf hty => exact .const (hext _ _ hf) hty
  | app _ ih => exact .app ih

theorem SortSyn.mono {env env' : Env md}
    (hext : ∀ (c : Key md) (ci : ConstantInfo md), env.find? c = some ci → env'.find? c = some ci)
    {d : Nat} {D : Expr md} {v : Level} (hs : SortSyn env d D v) : SortSyn env' d D v := by
  induction hs with
  | sort => exact .sort
  | forallE _ _ ihA ihB => exact .forallE ihA ihB
  | spine hsp => exact .spine (hsp.mono hext)

/-- **Two derivations of a sort for a type of the class agree**: at an environment and at one
that keeps its lookups, at any grades, the two levels are equal. -/
theorem SortSyn.sort_agree {env env' : Env md}
    (hext : ∀ (c : Key md) (ci : ConstantInfo md), env.find? c = some ci → env'.find? c = some ci)
    {d : Nat} {D : Expr md} {v : Level} (hs : SortSyn env d D v)
    {g g' : Grade} {T T' : Expr md} {u u' : Level}
    (hI : Infer env g d D T) (hR : Red env d T (.sort u))
    (hI' : Infer env' g' d D T') (hR' : Red env' d T' (.sort u')) : u = u' :=
  (hs.sort_eq hI hR).trans ((hs.mono hext).sort_eq hI' hR').symm

/-- **The two sorts agree in zero-ness** at every assignment (`SortSyn.sort_agree`). -/
theorem SortSyn.eval_zero_iff {env env' : Env md}
    (hext : ∀ (c : Key md) (ci : ConstantInfo md), env.find? c = some ci → env'.find? c = some ci)
    {d : Nat} {D : Expr md} {v : Level} (hs : SortSyn env d D v)
    {g g' : Grade} {T T' : Expr md} {u u' : Level}
    (hI : Infer env g d D T) (hR : Red env d T (.sort u))
    (hI' : Infer env' g' d D T') (hR' : Red env' d T' (.sort u')) (φ : LevelParam → Nat) :
    Level.eval φ u = 0 ↔ Level.eval φ u' = 0 := by
  rw [hs.sort_agree hext hI hR hI' hR']

end Ix.Kernel.Rules
