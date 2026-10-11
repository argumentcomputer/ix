/- M1-h fixture (`o11a-decline` suite), elaborated at run time and in no Lake library.
O11a's side conditions other than an absent instance, each on a mutual block that the condensation
splits (the upper member has a field into the lower one, nothing of the lower member mentions the
upper one), so Lean's `X._sizeOf_1` is the recursion O11a reads:

- `N`: the valid neighbour, the shape O11a rewrites (no parameters, no indices, a plain cross field);
- `P`: the block has a parameter (the cross target `PB α` is parametric);
- `I`: the cross target is indexed (the field `IB 0`);
- `R`: the cross field is reflexive (`Nat → RB`).

`NB.sizeOfAlt` (the lower component's recursion with another telescope) and `NB.sizeOfWrapped`
(not `λ t. NB.rec … t`) are the size functions the test puts into `NB._sizeOf_inst` for the
telescope and shape conditions. The `viaRec` functions are users' occurrences of the same recursors
(not the `sizeOf` recursion): nothing may be recorded for them. -/
set_option Elab.async false

namespace O11aSide
mutual
inductive NA
  | a : NB → NA
  | stop : NA
inductive NB
  | b : NB → NB
  | leaf : NB
end

mutual
inductive PA (α : Type)
  | a : PB α → PA α
  | stop : α → PA α
inductive PB (α : Type)
  | b : PB α → PB α
  | leaf : PB α
end

mutual
inductive IA
  | a : IB 0 → IA
  | stop : IA
inductive IB : Nat → Type
  | b {n : Nat} : IB n → IB (n + 1)
  | leaf : IB 0
end

mutual
inductive RA
  | a : (Nat → RB) → RA
  | stop : RA
inductive RB
  | b : RB → RB
  | leaf : RB
end

noncomputable def NA.viaRec (x : NA) : Nat :=
  @NA.rec (fun _ => Nat) (fun _ => Nat) (fun _ ih => ih + 1) 0 (fun _ ih => ih + 1) 0 x

noncomputable def PA.viaRec (x : PA Nat) : Nat :=
  @PA.rec Nat (fun _ => Nat) (fun _ => Nat) (fun _ ih => ih + 1) (fun _ => 0)
    (fun _ ih => ih + 1) 0 x

noncomputable def NB.sizeOfAlt (t : NB) : Nat :=
  @NB.rec (fun _ => Nat) (fun _ => Nat) (fun _ ih => ih + 1) 0 (fun _ ih => ih + 1) 1 t

noncomputable def NB.sizeOfWrapped (t : NB) : Nat := Nat.succ (NB.sizeOfAlt t)
end O11aSide
