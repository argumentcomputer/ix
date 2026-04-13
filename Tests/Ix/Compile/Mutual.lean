module
public import Lean

namespace Tests.Ix.Compile.Mutual

-- Alpha-equivalent pair (A ≅ B under renaming)
namespace AlphaCollapse
mutual
  public inductive A | a : B → A
  public inductive B | b : A → B
end

--set_option pp.all true
--#print A.brecOn
--#eval show Lean.MetaM Unit from do
--  let ci ← Lean.getConstInfo ``A.below.a
--  let .ctorInfo cv := ci | return
--  IO.println s!"{repr cv.type}"


-- Over-merged variant: A2≅B2, C2 references B2 (C2 is external SCC)
mutual
  public inductive A2 | a : B2 → A2
  public inductive B2 | b : A2 → B2
  public inductive C2 | c : B2 → C2
end

-- Self-referential: collapses to same compiled form as A and B
mutual
  public inductive A' | a' : A' → A'
  --public inductive B' | a' : B' → B'
end
end AlphaCollapse


-- Over-merged: A/B form one SCC, C references both but not vice versa.
-- A and B are NOT alpha-equivalent (B has 2 A fields).
namespace OverMerge
mutual
  public inductive A | a : B → A
  public inductive B | b : A → A → B
  public inductive C | c : A → B → C
end
-- Reordered: B2,C2,A2 (same structure, different declaration order)
mutual
  public inductive B2 | b : A2 → A2 → B2
  public inductive C2 | c : A2 → B2 → C2
  public inductive A2 | a : B2 → A2
end
-- Split: C3 separate (it's in a different SCC than A3/B3)
mutual
  public inductive B3 | b : A3 → A3 → B3
  public inductive A3 | a : B3 → A3
end
public inductive C3 where | c : A3 → B3 → C3
end OverMerge

--#print OverMerge.A3.below.rec
--#eval show Lean.MetaM Unit from do
--  let ci ← Lean.getConstInfo ``OverMerge.C3.c
--  let .ctorInfo cv := ci | return
--  IO.println s!"{repr cv.type}"

namespace OverMergeSplit
mutual
  public inductive A | a : B → A
  public inductive B | b : A → A → B
end
mutual
  public inductive C | c : A → B → C
end
end OverMergeSplit

namespace OverMerge2
mutual
  public inductive A | a : B → A
  public inductive B | b : A → A → B
  public inductive C | c : A -> D -> C
  public inductive D | c : B -> C -> D
end
-- Reordered: D2,C2,B2,A2
mutual
  public inductive D2 | c : B2 → C2 → D2
  public inductive C2 | c : A2 → D2 → C2
  public inductive B2 | b : A2 → A2 → B2
  public inductive A2 | a : B2 → A2
end
-- Split into two minimal SCCs
mutual
  public inductive B3 | b : A3 → A3 → B3
  public inductive A3 | a : B3 → A3
end
mutual
  public inductive C3 | c : A3 → D3 → C3
  public inductive D3 | c : B3 → C3 → D3
end
end OverMerge2

namespace OverMerge2Split
mutual
  public inductive A | a : B → A
  public inductive B | b : A → A → B
end
mutual
  public inductive C | c : A -> D -> C
  public inductive D | c : B -> C -> D
end
end OverMerge2Split

-- Over-merged + alpha-collapse: A ≅ B, C is external. Equivalent to BLE/BLI/BLO.
namespace OverMergeAlphaCollapse
mutual
  public inductive A | a : B → A
  public inductive B | b : A → B
  public inductive C | c : A → B → C
end
-- Reordered: C2,B2,A2
mutual
  public inductive C2 | c : A2 → B2 → C2
  public inductive B2 | b : A2 → B2
  public inductive A2 | a : B2 → A2
end
-- Split: A3≅B3 in mutual, C3 separate
mutual
  public inductive A3 | a : B3 → A3
  public inductive B3 | b : A3 → B3
end
public inductive C3 where | c : A3 → B3 → C3
end OverMergeAlphaCollapse

-- Alpha-collapse n=3: A→B→C→A cycle, all collapse to one.
namespace AlphaCollapse3
mutual
  public inductive A | a : B → A
  public inductive B | b : C → B
  public inductive C | c : A → C
end
-- Reordered: C2,A2,B2
mutual
  public inductive C2 | c : A2 → C2
  public inductive A2 | a : B2 → A2
  public inductive B2 | b : C2 → B2
end
end AlphaCollapse3

-- Alpha-collapse n=4: W→X→Y→Z→W cycle, all collapse to one.
namespace AlphaCollapse4
mutual
  public inductive W | w : X → W
  public inductive X | x : Y → X
  public inductive Y | y : Z → Y
  public inductive Z | z : W → Z
end
-- Reordered: Z2,Y2,X2,W2
mutual
  public inductive Z2 | z : W2 → Z2
  public inductive Y2 | y : Z2 → Y2
  public inductive X2 | x : Y2 → X2
  public inductive W2 | w : X2 → W2
end
end AlphaCollapse4

-- Over-merged with structures: 5 types, 2 SCCs.
-- EqC/EqP form one SCC, IneqC/IneqP/UnsatP form another.
-- IneqP references EqC (cross-SCC dependency).
namespace OverMergedStructs
mutual
  public structure EqC where
    val : Nat
    proof : EqP
  public inductive EqP where
    | base : Nat → EqP
    | combine : EqC → EqC → EqP
  public structure IneqC where
    val : Nat
    strict : Bool
    proof : IneqP
  public inductive IneqP where
    | base : Nat → IneqP
    | fromEq : EqC → IneqP
    | combine : IneqC → IneqC → IneqP
  public inductive UnsatP where
    | ineq : IneqC → UnsatP
end
end OverMergedStructs
namespace OverMergedStructs2
mutual
  public structure EqC where
    val : Nat
    proof : EqP
  public inductive EqP where
    | base : Nat → EqP
    | combine : EqC → EqC → EqP
  public structure IneqC where
    val : Nat
    strict : Bool
    proof : IneqP
  public inductive IneqP where
    | base : Nat → IneqP
    | fromEq : EqC → IneqP
    | ofDiseqSplit : UnsatP -> IneqP
    | combine : IneqC → IneqC → IneqP
  public inductive UnsatP where
    | ineq : IneqC → UnsatP
end
end OverMergedStructs2

end Tests.Ix.Compile.Mutual
