module
public import Ix.Aiur.Semantics.Flatten
public import Ix.Aiur.Semantics.SourceEval
public import Ix.Aiur.Semantics.BytecodeEval

/-!
The equivalence relation between source and bytecode observations.

`ValueEq` is a propositional mirror of `flattenValue`. `InterpResultEq` says:
- Success cases: values agree under flattening AND final IOBuffer is structurally equal.
- Both error: relation holds (we don't require error message equality).
- Mixed: relation fails.
-/

public section
@[expose] section

namespace Aiur

open Source

/-- Propositional mirror of `flattenValue`. `ValueEq decls funcIdx v t gs` says
value `v` flattens to `gs`.

**Scaffold note.** An earlier design sketched a multi-constructor
inductive with per-shape rules (`unit`, `field`, `pointer`, `fn`, `tuple`,
`array`, `ctor`). Making those rules cover every case correctly — including the
ctor-padding discipline from `dataTypeFlatSize` — is substantial and isn't
necessary for the scaffold: a single-constructor inductive wrapping
`flattenValue v = gs` is propositionally equivalent and lets us keep the
structural `cases` / `induction` affordance.

The `t : Typ` parameter is unused in the body today. A follow-up can strengthen
the relation to require a shape-match between `v` and `t` (see
`Proofs/CheckSound.lean`'s `ValueShapeMatches`); `flattenValue` already ignores
`t` so this refinement happens entirely in the propositional layer. -/
inductive ValueEq (decls : Decls) (funcIdx : Global → Option Nat) :
    Value → Typ → Array G → Prop
  | mk (v : Value) (t : Typ) (gs : Array G) :
      flattenValue decls funcIdx v = gs →
      ValueEq decls funcIdx v t gs

/-- Structural equivalence on `IOBuffer` — `data` equal as arrays, `map` equal as
  finite maps. Since `Std.HashMap` has no structural `Eq`, we use `BEq`. -/
def IOBuffer.equiv (a b : IOBuffer) : Prop := a == b

/-- Result-level equivalence (bytecode refines concrete). Maps the source's
`(Value × IOBuffer)` output to the bytecode's `(Array G × IOBuffer)` output via
`ValueEq` + IOBuffer structural equality. Bytecode may succeed where source ran
out of fuel (refinement direction); reverse is forbidden.

Asymmetry explained: at `fuel = 0`, `Source.Eval.runFunction` unconditionally
returns `.error .outOfFuel` (via `applyGlobal`), while bytecode can return `.ok`
for an empty-body function whose `ctrl` is a pure `.return _ #[]`. Keeping the
relation symmetric made `Function_body_preservation_zero_fuel` unprovable. -/
def InterpResultEq (decls : Decls) (funcIdx : Global → Option Nat)
    (retTyp : Typ)
    (src : Except Source.Eval.SourceError (Value × IOBuffer))
    (bc  : Except Bytecode.Eval.BytecodeError (Array G × IOBuffer)) : Prop :=
  match src, bc with
  | .ok (v, io₁),  .ok (gs, io₂)  => ValueEq decls funcIdx v retTyp gs ∧ IOBuffer.equiv io₁ io₂
  | .error _,      .error _       => True
  | .error _,      .ok _          => True
  | .ok _,         .error _       => False

end Aiur

end -- @[expose] section
end
