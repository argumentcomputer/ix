namespace Tests.Ix.CompileCert.LoweringDefs

/-! Fixtures for the projection lowering receipt: projection functions of
structure-likes that the checker's direct route does not take. -/

mutual
  /-- A structure-like member of a mutual block, with a dependent field
  (`vec`'s type mentions the earlier field `n`) and a propositional field. -/
  structure Sized (α : Type u) where
    n : Nat
    vec : Fin n → α
    ok : n = n
    rest : Bag α

  inductive Bag (α : Type u) where
    | empty : Bag α
    | more : Sized α → Bag α
end

/-- A nested structure-like with a universe parameter. -/
structure Rose (α : Type u) where
  root : α
  children : List (Rose α)

end Tests.Ix.CompileCert.LoweringDefs
