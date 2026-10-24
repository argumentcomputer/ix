import Lean
/-! A nested inductive whose result level `Sort u` may be zero, built with
`addDecl` (the `inductive` command rejects that resulting type). `T`'s one
constructor has one proof field, `K (Box T)`, which mentions `Box T`, so the
expanded block has two members: `T` and the auxiliary `Box T`. Lean's kernel
then gives `T` a Prop-only recursor (`elim_only_at_universe_zero`: the level
is not provably nonzero and the expanded block is not a singleton), although
the singleton test on `T` alone would allow large elimination. -/
open Lean Meta Elab Command

universe u

-- `Box.{u} (α : Sort u) : Sort u`, one constructor with one field `α`.
run_meta do
  let u : Level := Level.param `u
  let ty := mkForall `α .default (mkSort u) (mkSort u)
  let ctorTy := mkForall `α .implicit (mkSort u)
    (mkForall `a .default (mkBVar 0) (mkApp (mkConst `NestedSortU.Box [u]) (mkBVar 1)))
  let ctor : Constructor := Constructor.mk `NestedSortU.Box.mk ctorTy
  let it : InductiveType := InductiveType.mk `NestedSortU.Box ty [ctor]
  addDecl (Declaration.inductDecl [`u] 1 [it] false)

/-- A proposition that ignores its argument. -/
def NestedSortU.K (_ : Sort u) : Prop := True → True

-- `T.{u} : Sort u` with `mk : K (Box T) → T`.
run_meta do
  let u : Level := Level.param `u
  let t := mkConst `NestedSortU.T [u]
  let field := mkApp (mkConst `NestedSortU.K [u]) (mkApp (mkConst `NestedSortU.Box [u]) t)
  let ctor : Constructor := Constructor.mk `NestedSortU.T.mk (mkForall `h .default field t)
  let it : InductiveType := InductiveType.mk `NestedSortU.T (mkSort u) [ctor]
  addDecl (Declaration.inductDecl [`u] 0 [it] false)

/-- The recursor eliminates into `Prop` only, and has a motive for `Box T`. -/
theorem NestedSortU.t_rec (x : NestedSortU.T.{u}) : True :=
  NestedSortU.T.rec (motive_1 := fun _ => True) (motive_2 := fun _ => True)
    (fun _ => trivial) (fun _ _ => trivial) x
