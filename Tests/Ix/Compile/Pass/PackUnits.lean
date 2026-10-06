/- M1-h fixture (`pack-units` suite), elaborated at run time and in no Lake library: blocks with
eager and on-demand auxiliaries. `Tree.size`'s equation lemmas are realised on demand by
`size_leaf` (a later declaration); `Tree` has `match` and injectivity lemmas; `A`/`B` is a mutual
block whose `sizeOf` family names both members. -/
set_option Elab.async false

namespace PackU
inductive Tree
  | leaf : Tree
  | node : Tree → Tree → Tree

def Tree.size : Tree → Nat
  | .leaf => 1
  | .node l r => l.size + r.size + 1

theorem size_leaf : Tree.size .leaf = 1 := by simp [Tree.size]

theorem node_inj (a b c d : Tree) (h : Tree.node a b = Tree.node c d) : a = c :=
  (Tree.node.inj h).1

mutual
inductive A
  | a : B → A
  | stop : A
inductive B
  | b : A → B
  | leaf : B
end

def useA : A → Nat
  | .a _ => 1
  | .stop => 0
end PackU
