/- Producer planning: a real conservative cycle, recursive potential producers,
and a mixed direct/aliased cross field. Elaborated at test runtime. -/
set_option Elab.async false
set_option genSizeOf false
namespace O11aProducers.Cycle
mutual
inductive A where | a : B → A | stop : A
inductive B where | b : B → B | leaf : B
end
noncomputable def caller (x : A) : Nat :=
  @A.rec (fun _ => Nat) (fun _ => Nat) (fun _ ih => ih + 1) 0
    (fun _ ih => ih + 1) 0 x
noncomputable def unrelated (x : A) : Nat :=
  @A.rec (fun _ => Nat) (fun _ => Nat) (fun _ ih => ih + 2) 0
    (fun _ ih => ih + 2) 0 x
-- The source graph sees caller; zeta reduction makes the domain just B.
noncomputable def B.sizeFn
    (x : (let _unused : Nat := caller A.stop; B)) : Nat :=
  @B.rec (fun _ => Nat) (fun _ => Nat) (fun _ ih => ih + 1) 0
    (fun _ ih => ih + 1) 0 x
@[instance_reducible] noncomputable def B._sizeOf_inst : SizeOf B := ⟨B.sizeFn⟩
noncomputable def good (x : A) : Nat :=
  @A.rec (fun _ => Nat) (fun _ => Nat) (fun _ ih => ih + 1) 0
    (fun _ ih => ih + 1) 0 x
end O11aProducers.Cycle

set_option genSizeOf true
namespace O11aProducers.Chain
mutual
inductive X where | x : Y → X | stop : X
inductive Y where | y : Z → Y | stop : Y
inductive Z where | z : Z → Z | leaf : Z
end
end O11aProducers.Chain

namespace O11aProducers.Mixed
abbrev Id' (α : Type) : Type := α
mutual
inductive A where | direct : B → A | hidden : Id' B → A | stop : A
inductive B where | b : B → B | leaf : B
end
end O11aProducers.Mixed
