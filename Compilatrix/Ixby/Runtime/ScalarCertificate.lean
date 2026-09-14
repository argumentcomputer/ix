import Compilatrix.Ixby.Runtime.ScalarFunction

namespace Compilatrix.Ixby.Runtime

open Ix.Ixby

structure ScalarLinks where
  add : FunctionId
  sub : FunctionId
  mul : FunctionId
  inverse : FunctionId
  equal : FunctionId
  first : FunctionId
  second : FunctionId
  fieldBox : Constructor
  fieldId : CtorId

/-- A certificate about seven concrete generated functions, with the field
projection layout bound to this program's declaration table. -/
structure ScalarCertificate (program : Program) (links : ScalarLinks) : Type where
  add : ScalarFunction.Checked program links.add (ScalarFunction.direct 2 .extAdd)
  sub : ScalarFunction.Checked program links.sub (ScalarFunction.direct 2 .extSub)
  mul : ScalarFunction.Checked program links.mul (ScalarFunction.direct 2 .extMul)
  inverse : ScalarFunction.Checked program links.inverse (ScalarFunction.direct 1 .extInverse)
  equal : ScalarFunction.Checked program links.equal (ScalarFunction.direct 2 .extEq)
  first : ScalarFunction.Checked program links.first (ScalarFunction.projection .extFst links.fieldBox)
  second : ScalarFunction.Checked program links.second (ScalarFunction.projection .extSnd links.fieldBox)
  field : program.getConstructor links.fieldBox = .ok { id := links.fieldId, fields := 1 }

def certifyScalars (program : Program) (links : ScalarLinks) :
    Except String (ScalarCertificate program links) := do
  let add ← ScalarFunction.check program links.add (ScalarFunction.direct 2 .extAdd)
  let sub ← ScalarFunction.check program links.sub (ScalarFunction.direct 2 .extSub)
  let mul ← ScalarFunction.check program links.mul (ScalarFunction.direct 2 .extMul)
  let inverse ← ScalarFunction.check program links.inverse (ScalarFunction.direct 1 .extInverse)
  let equal ← ScalarFunction.check program links.equal (ScalarFunction.direct 2 .extEq)
  let first ← ScalarFunction.check program links.first (ScalarFunction.projection .extFst links.fieldBox)
  let second ← ScalarFunction.check program links.second (ScalarFunction.projection .extSnd links.fieldBox)
  match found : program.getConstructor links.fieldBox with
  | .error _ => throw "missing scalar runtime field layout"
  | .ok actual =>
    if same : actual = { id := links.fieldId, fields := 1 } then
      return { add, sub, mul, inverse, equal, first, second, field := same ▸ found }
    else throw "scalar runtime field layout differs"

namespace ScalarCertificate

open Representation ScalarFunction

variable {program : Program} {links : ScalarLinks} (certificate : ScalarCertificate program links)
  (limits : Limits) (room : 3 ≤ limits.locals)

include certificate room

theorem extAdd (a b : ExtGoldilocks) :
    run limits program 3 (start links.add #[.scalar (.extField a), .scalar (.extField b)]) =
      .ok (.scalar (.extField (a.add b))) :=
  certificate.add.binary limits room _ _ _ (eval_extAdd limits a b)

theorem extSub (a b : ExtGoldilocks) :
    run limits program 3 (start links.sub #[.scalar (.extField a), .scalar (.extField b)]) =
      .ok (.scalar (.extField (a.sub b))) :=
  certificate.sub.binary limits room _ _ _ (eval_extSub limits a b)

theorem extMul (a b : ExtGoldilocks) :
    run limits program 3 (start links.mul #[.scalar (.extField a), .scalar (.extField b)]) =
      .ok (.scalar (.extField (a.mul b))) :=
  certificate.mul.binary limits room _ _ _ (eval_extMul limits a b)

theorem extInverse (a : ExtGoldilocks) :
    run limits program 3 (start links.inverse #[.scalar (.extField a)]) =
      .ok (.scalar (.extField a.inverse)) :=
  certificate.inverse.unary limits (by omega) _ _ (eval_extInverse limits a)

theorem extEq (a b : ExtGoldilocks) :
    run limits program 3 (start links.equal #[.scalar (.extField a), .scalar (.extField b)]) =
      .ok (.scalar (.bool (a == b))) :=
  certificate.equal.binary limits room _ _ _ (eval_extEq limits a b)

theorem extFst (a : ExtGoldilocks) :
    run limits program 4 (start links.first #[.scalar (.extField a)]) =
      .ok (.ctor links.fieldId #[.scalar (.field a.c0)]) :=
  certificate.first.project limits room _ _ links.fieldId certificate.field (eval_extFst limits a)

theorem extSnd (a : ExtGoldilocks) :
    run limits program 4 (start links.second #[.scalar (.extField a)]) =
      .ok (.ctor links.fieldId #[.scalar (.field a.c1)]) :=
  certificate.second.project limits room _ _ links.fieldId certificate.field (eval_extSnd limits a)

/-- Whole-program source-operation agreement when the certified multiplication
helper is exported. The only execution premises are ordinary image/input
admission, entry selection, and sufficient local capacity. -/
theorem extMul_evaluates (a b : ExtGoldilocks) (entry : program.entry = links.mul)
    (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes
      [.scalar (.extField a), .scalar (.extField b)] = .ok ()) :
    Evaluates limits program #[.scalar (.extField a), .scalar (.extField b)]
      (.scalar (.extField (a.mul b))) :=
  certificate.mul.binary_evaluates limits room _ _ _ entry admitted inputs (eval_extMul limits a b)

theorem extInverse_evaluates (a : ExtGoldilocks) (entry : program.entry = links.inverse)
    (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [.scalar (.extField a)] = .ok ()) :
    Evaluates limits program #[.scalar (.extField a)] (.scalar (.extField a.inverse)) :=
  certificate.inverse.unary_evaluates limits (by omega) _ _ entry admitted inputs (eval_extInverse limits a)

theorem extFst_evaluates (a : ExtGoldilocks) (entry : program.entry = links.first)
    (admitted : validateProgram limits program = .ok ())
    (inputs : validateInputValues limits program limits.inputNodes [.scalar (.extField a)] = .ok ()) :
    Evaluates limits program #[.scalar (.extField a)] (.ctor links.fieldId #[.scalar (.field a.c0)]) :=
  certificate.first.project_evaluates limits room _ _ links.fieldId certificate.field
    entry admitted inputs (eval_extFst limits a)

end ScalarCertificate

end Compilatrix.Ixby.Runtime
