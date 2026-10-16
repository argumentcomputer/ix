import Lean
/-! Positivity after whnf (CQX.8). Lane P's reproducer
(`ix-cc-simplify` `scratch/parity/variants/NestedSortUK.lean`, under its own
namespace here). `T`'s one field is `K True (Box T)` with `K a _ := a`: the
field mentions the block before reduction and not after it. Lean's kernel
whnfs a field domain before its occurrence test (`check_positivity`), so it
accepts `T`; the Ix kernels tested the occurrence first and rejected the
whnf'd head `True` ("positivity: not a valid inductive app"). The Rust kernel
is fixed; `Ix.Tc` is not (it is deleted in CQX.2).

The rest is `NestedSortU`'s shape: a nested inductive whose result level
`Sort u` may be zero, built with `addDecl` (the `inductive` command rejects
that resulting type), whose expanded block has two members, `T` and the
auxiliary `Box T`, so Lean's kernel gives `T` a Prop-only recursor
(`elim_only_at_universe_zero`), although the singleton test on `T` alone
would allow large elimination. -/
open Lean Meta Elab Command

universe u

-- `Box.{u} (α : Sort u) : Sort u`, one constructor with one field `α`.
run_meta do
  let u : Level := Level.param `u
  let ty := mkForall `α .default (mkSort u) (mkSort u)
  let ctorTy := mkForall `α .implicit (mkSort u)
    (mkForall `a .default (mkBVar 0) (mkApp (mkConst `NestedSortUK.Box [u]) (mkBVar 1)))
  let ctor : Constructor := Constructor.mk `NestedSortUK.Box.mk ctorTy
  let it : InductiveType := InductiveType.mk `NestedSortUK.Box ty [ctor]
  addDecl (Declaration.inductDecl [`u] 1 [it] false)

/-- A proposition that ignores its second argument. -/
def NestedSortUK.K (a : Prop) (_ : Sort u) : Prop := a

-- `T.{u} : Sort u` with `mk : K True (Box T) → T`.
run_meta do
  let u : Level := Level.param `u
  let t := mkConst `NestedSortUK.T [u]
  let field := mkApp2 (mkConst `NestedSortUK.K [u]) (mkConst ``True)
    (mkApp (mkConst `NestedSortUK.Box [u]) t)
  let ctor : Constructor := Constructor.mk `NestedSortUK.T.mk (mkForall `h .default field t)
  let it : InductiveType := InductiveType.mk `NestedSortUK.T (mkSort u) [ctor]
  addDecl (Declaration.inductDecl [`u] 0 [it] false)

/-- The recursor eliminates into `Prop` only, and has a motive for `Box T`. -/
theorem NestedSortUK.t_rec (x : NestedSortUK.T.{u}) : True :=
  NestedSortUK.T.rec (motive_1 := fun _ => True) (motive_2 := fun _ => True)
    (fun _ => trivial) (fun _ _ => trivial) x
