module
public import Ix.MultiStark.Verify.Fri.Fold
public import Ix.MultiStark.Verify.Protocol.Arithmetic

/-! FRI's row equation is literal Lagrange interpolation over the ordered
two-adic row. The numerator uses the challenge; inverse denominators contain
only differences of fixed row points. No challenge/row-point inequality is
assumed. The canonical modular operations and their guarded inverses are
specified separately from cryptographic low-degree soundness. -/

public section
@[expose] section

namespace MultiStark.Verify.Protocol

/-- Low-to-high binary digits, selected by their numeric positions. Folding
this sequence as a big-endian word reverses exactly the requested low bits. -/
def lowBits (value bits : Nat) : List Nat :=
  (List.range bits).map (fun position => value / 2 ^ position % 2)

def bitReverse (value bits : Nat) : Nat :=
  (lowBits value bits).foldl (fun acc bit => acc * 2 + bit) 0

def PolynomialValue (coefficients : List Ext) (point : Ext) : Ext :=
  coefficients.foldr (fun coefficient tail => coefficient.add (point.mul tail)) Arithmetic.zero

def RowPoints (index logHeight logArity : Nat) (result : Array Field) : Prop :=
  logHeight + logArity ≤ 32 ∧ index < 2 ^ logHeight ∧
    ∃ group step, TwoAdicGenerator (logHeight + logArity) group ∧ TwoAdicGenerator logArity step ∧
      (Array.range (2 ^ logArity)).map (fun column =>
        (group.pow (bitReverse index logHeight)).mul (step.pow (bitReverse column logArity))) = result

/-- Removing the selected position preserves the order of every other
factor, including duplicate point VALUES at distinct positions. -/
def otherRowPoints (indexed : List (Field × Nat)) (selected : Nat) : List Field :=
  indexed.filterMap (fun (point, index) => if selected = index then none else some point)

def LagrangeNumerator (others : List Field) (point initial : Ext) : Ext :=
  others.foldl (fun product xj => product.mul (point.sub (Arithmetic.embed xj))) initial

def LagrangeDenominator (others : List Field) (xi initial : Field) : Field :=
  others.foldl (fun product xj => product.mul (xi.sub xj)) initial

def InterpolationSum (allPoints : List (Field × Nat)) (point : Ext) :
    List Field → List Ext → Nat → Ext → Ext → Prop
  | [], [], _, initial, result => initial = result
  | xi :: points, yi :: values, index, initial, result =>
    let others := otherRowPoints allPoints index
    ∃ inverse, BaseInverse (LagrangeDenominator others xi 1) inverse ∧
      InterpolationSum allPoints point points values (index + 1)
        (initial.add (yi.mul (Arithmetic.scale (LagrangeNumerator others point Arithmetic.one) inverse))) result
  | _, _, _, _, _ => False

def Interpolation (points : Array Field) (values : Array Ext) (point result : Ext) : Prop :=
  points.size = values.size ∧ points ≠ #[] ∧
    InterpolationSum points.toList.zipIdx point points.toList values.toList 0 Arithmetic.zero result

def RowFold (limits : Fri.Limits) (index logHeight logArity : Nat) (beta : Ext)
    (values : Array Ext) (result : Ext) : Prop :=
  logArity ≤ 32 ∧ 2 ^ logArity ≤ limits.foldArity ∧ values.size = 2 ^ logArity ∧
    ∃ points, RowPoints index logHeight logArity points ∧ Interpolation points values beta result

end MultiStark.Verify.Protocol
