module
import Lean

namespace Tests.Ix.Compile.Mutual

-- Alpha-equivalent pair (A ≅ B under renaming)
namespace AlphaCollapse
mutual
  inductive A | a : B → A
  inductive B | b : A → B
end

--set_option pp.all true
--#print A.rec
--#eval show Lean.MetaM Unit from do
--  let ci ← Lean.getConstInfo ``A.rec
--  let .recInfo cv := ci | return
--  IO.println s!"{repr cv.type}"


-- Over-merged variant: A2≅B2, C2 references B2 (C2 is external SCC)
mutual
  inductive A2 | a : B2 → A2
  inductive B2 | b : A2 → B2
  inductive C2 | c : B2 → C2
end

-- Self-referential: collapses to same compiled form as A and B
mutual
  inductive A' | a' : A' → A'
  --inductive B' | a' : B' → B'
end
end AlphaCollapse


-- Over-merged: A/B form one SCC, C references both but not vice versa.
-- A and B are NOT alpha-equivalent (B has 2 A fields).
namespace OverMerge
mutual
  inductive A | a : B → A
  inductive B | b : A → A → B
  inductive C | c : A → B → C
end
-- Reordered: B2,C2,A2 (same structure, different declaration order)
mutual
  inductive B2 | b : A2 → A2 → B2
  inductive C2 | c : A2 → B2 → C2
  inductive A2 | a : B2 → A2
end
-- Split: C3 separate (it's in a different SCC than A3/B3)
mutual
  inductive B3 | b : A3 → A3 → B3
  inductive A3 | a : B3 → A3
end
inductive C3 where | c : A3 → B3 → C3
end OverMerge

--#print OverMerge.A3.below.rec
--#eval show Lean.MetaM Unit from do
--  let ci ← Lean.getConstInfo ``OverMerge.C3.c
--  let .ctorInfo cv := ci | return
--  IO.println s!"{repr cv.type}"

namespace OverMergeSplit
mutual
  inductive A | a : B → A
  inductive B | b : A → A → B
end
mutual
  inductive C | c : A → B → C
end
end OverMergeSplit

namespace OverMerge2
mutual
  inductive A | a : B → A
  inductive B | b : A → A → B
  inductive C | c : A -> D -> C
  inductive D | c : B -> C -> D
end
-- Reordered: D2,C2,B2,A2
mutual
  inductive D2 | c : B2 → C2 → D2
  inductive C2 | c : A2 → D2 → C2
  inductive B2 | b : A2 → A2 → B2
  inductive A2 | a : B2 → A2
end
-- Split into two minimal SCCs
mutual
  inductive B3 | b : A3 → A3 → B3
  inductive A3 | a : B3 → A3
end
mutual
  inductive C3 | c : A3 → D3 → C3
  inductive D3 | c : B3 → C3 → D3
end
end OverMerge2

namespace OverMerge2Split
mutual
  inductive A | a : B → A
  inductive B | b : A → A → B
end
mutual
  inductive C | c : A -> D -> C
  inductive D | c : B -> C -> D
end
end OverMerge2Split

-- Over-merged + alpha-collapse: A ≅ B, C is external. Equivalent to BLE/BLI/BLO.
namespace OverMergeAlphaCollapse
mutual
  inductive A | a : B → A
  inductive B | b : A → B
  inductive C | c : A → B → C
end
-- Reordered: C2,B2,A2
mutual
  inductive C2 | c : A2 → B2 → C2
  inductive B2 | b : A2 → B2
  inductive A2 | a : B2 → A2
end
-- Split: A3≅B3 in mutual, C3 separate
mutual
  inductive A3 | a : B3 → A3
  inductive B3 | b : A3 → B3
end
inductive C3 where | c : A3 → B3 → C3
end OverMergeAlphaCollapse

-- Alpha-collapse n=3: A→B→C→A cycle, all collapse to one.
namespace AlphaCollapse3
mutual
  inductive A | a : B → A
  inductive B | b : C → B
  inductive C | c : A → C
end
-- Reordered: C2,A2,B2
mutual
  inductive C2 | c : A2 → C2
  inductive A2 | a : B2 → A2
  inductive B2 | b : C2 → B2
end




end AlphaCollapse3

-- Alpha-collapse n=4: W→X→Y→Z→W cycle, all collapse to one.
namespace AlphaCollapse4
mutual
  inductive W | w : X → W
  inductive X | x : Y → X
  inductive Y | y : Z → Y
  inductive Z | z : W → Z
end
-- Reordered: Z2,Y2,X2,W2
mutual
  inductive Z2 | z : W2 → Z2
  inductive Y2 | y : Z2 → Y2
  inductive X2 | x : Y2 → X2
  inductive W2 | w : X2 → W2
end
end AlphaCollapse4

-- Over-merged with structures: 5 types, 2 SCCs.
-- EqC/EqP form one SCC, IneqC/IneqP/UnsatP form another.
-- IneqP references EqC (cross-SCC dependency).
namespace OverMergedStructs
mutual
  structure EqC where
    val : Nat
    proof : EqP
  inductive EqP where
    | base : Nat → EqP
    | combine : EqC → EqC → EqP
  structure IneqC where
    val : Nat
    strict : Bool
    proof : IneqP
  inductive IneqP where
    | base : Nat → IneqP
    | fromEq : EqC → IneqP
    | combine : IneqC → IneqC → IneqP
  inductive UnsatP where
    | ineq : IneqC → UnsatP
end
end OverMergedStructs
namespace OverMergedStructs2
mutual
  structure EqC where
    val : Nat
    proof : EqP
  inductive EqP where
    | base : Nat → EqP
    | combine : EqC → EqC → EqP
  structure IneqC where
    val : Nat
    strict : Bool
    proof : IneqP
  inductive IneqP where
    | base : Nat → IneqP
    | fromEq : EqC → IneqP
    | ofDiseqSplit : UnsatP -> IneqP
    | combine : IneqC → IneqC → IneqP
  inductive UnsatP where
    | ineq : IneqC → UnsatP
end
end OverMergedStructs2

end Tests.Ix.Compile.Mutual
