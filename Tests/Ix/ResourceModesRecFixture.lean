set_option Elab.async false
/-! The resource-mode suite's fixture of recursive, mutual, nested and indexed inductive types
(the mode-repair branch, V7): five honest programs, each matching on a value of such a type,
compiled by `Tests/Ix/ResourceModes.lean`'s record cases (`recTypeCasesTest`). -/
namespace ModeRecFixture

inductive E | c₀ | c₁

-- a list-like inductive
inductive L | nil | cons (h : E) (t : L)
def headOr (d : E) : L → E
  | .nil => d
  | .cons h _ => h
def mainL : E := headOr E.c₀ (.cons E.c₁ .nil)

-- a recursive definition on `L`, with its `eq_def` theorem realized for `Subject.runTable`
def lenL : L → Nat
  | .nil => 0
  | .cons _ t => lenL t + 1
set_option linter.defProp false in
def lenLEqDef := @lenL.eq_def
def mainLenL : Nat := lenL (.cons E.c₁ (.cons E.c₀ .nil))

-- Lean's own `List`
def headOrList (d : E) : List E → E
  | [] => d
  | h :: _ => h
def mainList : E := headOrList E.c₀ [E.c₁]

-- a mutual pair
mutual
inductive A | a0 | a (b : B)
inductive B | b (a : A)
end
def isA0 : A → E
  | .a0 => E.c₀
  | .a _ => E.c₁
def mainA : E := isA0 (.a (.b .a0))

-- a nested inductive
inductive T | leaf | node (cs : List T)
def isLeaf : T → E
  | .leaf => E.c₀
  | .node _ => E.c₁
def mainT : E := isLeaf (.node [])

-- an indexed family
inductive V : Nat → Type | nil : V 0 | cons (h : E) (n : Nat) (t : V n) : V (n + 1)
def isNil : {n : Nat} → V n → E
  | _, .nil => E.c₀
  | _, .cons _ _ _ => E.c₁
def mainV : E := isNil (V.cons E.c₁ 0 V.nil)

end ModeRecFixture
