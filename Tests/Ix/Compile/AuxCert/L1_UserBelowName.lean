/-! L1 (code-review lead "FieldBelow", generalised; class B + A in closure mode).
Only the name `below` triggers it: user definitions/fields named `brecOn`, `below_1`, `below_2`,
`brecOn_1`, `brecOn_2`, `rec_1`, `binductionOn`, `ibelow`, and on a Prop inductive `noConfusion`,
`noConfusionType`, `ctorIdx`, `sizeOf_spec`, `injEq`, `inj` all pass (63 shapes, 4 fail).
Failing: `def T.below` on an enum (H1_def_enum_below), on a Prop inductive (H1_def_prop_below), a
structure field `below : Nat → Type` (H1_field_below), a field `below : Prop` (H1_pfield_below).
Whole file: check-rs `use_below: universe param count: expected 1, got 0`; certified rejects 1.
Closure `--consts T.below` / `--consts use_below`: block FAILED T: missing constant: T.rec. -/
inductive T where
  | a
  | b
def T.below (_ : T) : Type := Nat
theorem use_below : T.below T.a = Nat := rfl
