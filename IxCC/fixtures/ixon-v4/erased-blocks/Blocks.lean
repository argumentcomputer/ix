/-! Mutual and nested inductive blocks for the relevance check's tests of constructor fields
written erased (`IxCCTests.Recheck.ErasedBlocks`). No mode is written here: the tests write a
constructor field erased below the kernel, as a kernel that sees no mode accepts it. -/

namespace ErasedBlocks

inductive E where
  | c0 | c1 | c2

def next : E → E
  | .c0 => .c1
  | .c1 => .c2
  | .c2 => .c0

def useE (y : E) : E := y

/-! ## The minors of a block's second recursor -/

mutual
inductive A where
  | a0 : A
  | a1 : True → B → A
inductive B where
  | b0 : B
  | b1 : E → B
end

/-- `B.rec` on `b1 c₁`, its minor for `b1` the η-short `useE`: `c₁`. `B.rec` takes the minors of
`a0`, `a1`, `b0`, `b1` (positions 2-5) and has rules for `b0` and `b1` only. -/
noncomputable def mainB : E :=
  @B.rec (fun _ => E) (fun _ => E) E.c0 (fun _ _ _ => E.c0) E.c0 useE (B.b1 E.c1)

/-! ## A field of one member whose type is another member -/

mutual
inductive A2 where
  | a1 : B2 → A2
inductive B2 where
  | b0 : B2
  | b1 : B2
end

/-- `A2.rec` on `a1 b1`, its minor returning the induction hypothesis `B2.rec … b1`: `c₂`. -/
noncomputable def mainM2 : E :=
  @A2.rec (fun _ => E) (fun _ => E) (fun _ ih => ih) E.c1 E.c2 (A2.a1 B2.b1)

/-! ## Nested blocks (stored as mutual blocks with auxiliary types) -/

inductive O (α : Type) where
  | none : O α
  | some : α → O α

inductive Tree where
  | leaf : Tree
  | node : O Tree → Tree

/-- `node (some (node none))` through `Tree.rec`: `next c₁ = c₂`. -/
noncomputable def mainN : E :=
  @Tree.rec (fun _ => E) (fun _ => E) E.c0 (fun _ ih => ih) E.c1 (fun _ ih => next ih)
    (Tree.node (O.some (Tree.node O.none)))

/-- The auxiliary recursor directly, on `some (node none)`: `c₂`. -/
noncomputable def mainN1 : E :=
  @Tree.rec_1 (fun _ => E) (fun _ => E) E.c0 (fun _ ih => ih) E.c1 (fun _ ih => next ih)
    (O.some (Tree.node O.none))

inductive L (α : Type) where
  | nil : L α
  | cons : α → L α → L α

inductive Rose where
  | leaf : Rose
  | node : L Rose → Rose

/-- `node (cons leaf nil)`: the `cons` minor returns `next` of the head's hypothesis: `c₁`. -/
noncomputable def mainR : E :=
  @Rose.rec (fun _ => E) (fun _ => E) E.c0 (fun _ ih => ih) E.c2 (fun _ _ ih _ => next ih)
    (Rose.node (L.cons Rose.leaf L.nil))

/-- One root per constructor of `E`, so that every one is emitted. -/
def r0 : E := E.c0
def r1 : E := E.c1
def r2 : E := E.c2

end ErasedBlocks
