/-! A3V-IPB reproducer (A3v follow-up, 2026-10-03): unchanged Prop blocks whose
`IndPredBelow` family Ix regenerates. `ix validate-lean --local` on this file:
phase 6 (oracle leg) and phase 8 (provenance) name the auxiliaries whose Ix
form differs from Lean's by address, in both switch states (Neighbours'
`F8NoSplit`); `IX_VALIDATE_EXPLAIN=1` says how they differ. One namespace per
shape, so the failing names say which shapes trigger it. -/
namespace IPB

-- the Neighbours shape: a mutual Prop pair nesting a Prop container
namespace MutNested
inductive PBox (p : Prop) : Prop
  | mk : p → PBox p
mutual
inductive A : Prop
  | mk : PBox B → A
inductive B : Prop
  | leaf
  | s : A → B
end
end MutNested

-- a single Prop inductive nesting a Prop container
namespace Nested
inductive PBox (p : Prop) : Prop
  | mk : p → PBox p
inductive A : Prop
  | leaf
  | mk : PBox A → A
end Nested

-- a mutual Prop pair, no nesting
namespace Mut
mutual
inductive A : Prop
  | mk : B → A
inductive B : Prop
  | leaf
  | s : A → B
end
end Mut

end IPB
