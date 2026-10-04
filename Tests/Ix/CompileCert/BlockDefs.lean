namespace Tests.Ix.CompileCert.BlockDefs

inductive Void : Prop

def first {α : Sort u} (a _b : α) : α := a
def firstAlias {α : Sort u} (a _b : α) : α := a
theorem first_eq {α : Sort u} (a b : α) : first a b = a := rfl

structure Pair (α : Type u) where
  fst : α
  snd : α

def getFst {α : Type u} (p : Pair α) : α := p.fst

end Tests.Ix.CompileCert.BlockDefs
