import Lean
/-! H1 via `addDecl`: the `inductive` command rejects a resulting type
`Sort u` that may be Prop, but the kernel accepts it. Lean's kernel gives
`SU` a Prop-only recursor (two constructors, level not provably non-zero).
aux-gen forces `is_large := true` when the level is not literally zero
(recursor.rs:2520, Recursor.lean:1632). -/
open Lean Meta Elab Command

run_meta do
  let u : Level := Level.param `u
  let ty : Expr := mkConst `SortUD.SU [u]
  let ca : Constructor := Constructor.mk `SortUD.SU.a ty
  let cb : Constructor := Constructor.mk `SortUD.SU.b ty
  let it : InductiveType := InductiveType.mk `SortUD.SU (Expr.sort u) [ca, cb]
  addDecl (Declaration.inductDecl [`u] 0 [it] false)
  mkCasesOn `SortUD.SU
  mkRecOn `SortUD.SU

theorem SortUD.su_cases (x : SortUD.SU.{u}) : x = SortUD.SU.a ∨ x = SortUD.SU.b :=
  SortUD.SU.casesOn (motive := fun x => x = SortUD.SU.a ∨ x = SortUD.SU.b) x
    (Or.inl rfl) (Or.inr rfl)

theorem SortUD.su_rec (x : SortUD.SU.{u}) : True :=
  SortUD.SU.rec (motive := fun _ => True) trivial trivial x
