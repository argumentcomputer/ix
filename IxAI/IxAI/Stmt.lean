import IxAICommon.Hash

/-!
# Statements of the toy logic

Propositional formulas over numbered atoms, with a canonical byte encoding. They are the inputs of
the milestone-1 dataset (`IxAI.Data`) and the statements of the toy kernel (`IxAI.Kernel`). The
syntax has no names, so an encoding, and every address computed from it, depends only on content.
-/

namespace IxAI

inductive Stmt where
  | atom (n : Nat)
  | top
  | imp (a b : Stmt)
  | and (a b : Stmt)
  deriving DecidableEq, Hashable, Repr, Inhabited

def Stmt.render : Stmt → String
  | .atom n => s!"P{n}"
  | .top => "⊤"
  | .imp a b => s!"({a.render} → {b.render})"
  | .and a b => s!"({a.render} ∧ {b.render})"

instance : ToString Stmt := ⟨Stmt.render⟩

def Stmt.encode (b : ByteArray) : Stmt → ByteArray
  | .atom n => Enc.enc (b.push 0) n
  | .top => b.push 1
  | .imp x y => y.encode (x.encode (b.push 2))
  | .and x y => y.encode (x.encode (b.push 3))

instance : Enc Stmt := ⟨Stmt.encode⟩

end IxAI
