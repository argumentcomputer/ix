/-! A0 (WB-B4, BB-F4 neighbour): the users of BB-F4 over a NON-nested alpha
pair. The audit saw `r := @A.rec` accepted by both kernels here, but its
compiled form was an eta wrapper whose collapsed member's motive and minors
were dropped bound variables: `r` applied to member-specific minors would
compute with the kept member's minors (the B4 miscompile through a partial
application). Both compilers now refuse it with the eta-refusal message;
the fully applied users of the same pair are in `Neighbours.lean`. -/
namespace F4FlatAlphaUsers
mutual
inductive A : Type where
  | z
  | s : B → A
inductive B : Type where
  | z
  | s : A → B
end
noncomputable def r := @A.rec
end F4FlatAlphaUsers
