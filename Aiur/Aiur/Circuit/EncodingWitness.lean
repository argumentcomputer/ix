import Aiur.Circuit.InactiveWitness
import Aiur.Circuit.ExpressionCorrectness

namespace Aiur

theorem WireValue.decode_injective [NatCast F] [Zero F] [DecidableEq F] {decls : Declarations}
    (checked : checkDeclarations decls = .ok ()) {left right : WireValue F} {value : Value F}
    (first : left.decode decls = some value) (second : right.decode decls = some value) : left = right := by
  have a := WireValue.encode_decode first (fun _ => Declarations.layout_namesUnique checked)
  have b := WireValue.encode_decode second (fun _ => Declarations.layout_namesUnique checked)
  exact Option.some.inj (a.symm.trans b)

theorem WireValue.decode_sized [NatCast F] [Zero F] [DecidableEq F] {decls : Declarations}
    (checked : checkDeclarations decls = .ok ()) {wire : WireValue F} {value : Value F}
    (decoded : wire.decode decls = some value) : wire.Sized decls :=
  Value.encode_sized (WireValue.encode_decode decoded (fun _ => Declarations.layout_namesUnique checked))

theorem DecodesValues.wires_unique [NatCast F] [Zero F] [DecidableEq F] {decls : Declarations}
    (checked : checkDeclarations decls = .ok ()) {left right : List (WireValue F)} {values : List (Value F)}
    (first : DecodesValues decls left values) (second : DecodesValues decls right values) : left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | cons head tail ih =>
      cases second with
      | cons head' tail' => simp [WireValue.decode_injective checked head head', ih tail']

theorem DecodesEnvironment.types [NatCast F] [Zero F] [DecidableEq F] {decls : Declarations}
    {wires : List (String × WireValue F)} {values : Environment F}
    (decoded : DecodesEnvironment decls wires values) :
    environmentTypes values = wires.map (fun binding => (binding.1, binding.2.type)) := by
  induction decoded with
  | nil => rfl
  | cons head tail ih => simp [environmentTypes, head.1, (WireValue.decode_spec head.2).1] at ih ⊢; exact ih

theorem DecodesValues.each [NatCast F] [Zero F] [DecidableEq F] {decls : Declarations}
    {wires : List (WireValue F)} {values : List (Value F)} (decoded : DecodesValues decls wires values) :
    ∀ wire ∈ wires, ∃ value, wire.decode decls = some value := by
  induction decoded with
  | nil => simp
  | cons head tail ih => simpa using And.intro ⟨_, head⟩ ih

namespace Circuit.Compiler

variable {F : Type} {rom : WireROM F}

/-- Allocate an opaque result with a canonical encoding of the evaluated value. -/
theorem freshValue_decoded_complete [Field F] [DecidableEq F] {decls : Declarations}
    (checked : checkDeclarations decls = .ok ()) (tags : decls.tagsValid F = true)
    {type : Ty} {vars : WireValue Var} {before after : BuildState F}
    (compiled : freshValue decls type before = .ok (vars, after))
    {calls : Circuit.CallRelation F} {initial : Var → F}
    (layout : before.WellFormed) (valid : before.Valid rom calls initial)
    (value : Value F) (shape : value.type = type) (formed : value.wellFormed decls = true) :
    ∃ assignment, Extension rom calls before after initial assignment ∧
      Bounded (F := F) after.nextVar (vars.map ArithExpr.var) ∧
      (vars.map assignment).decode decls = some value := by
  obtain ⟨typeLayout, expanded, _⟩ := freshValue_eq compiled
  obtain ⟨words, encoded⟩ := (Declarations.layout_describes expanded).encode_total shape formed
  let desired : WireValue F := ⟨type, words⟩
  obtain ⟨assignment, ext, bound, assigned⟩ := freshValue_complete compiled layout valid desired rfl
    ⟨typeLayout, expanded, Layout.encode_length encoded⟩
  refine ⟨assignment, ext, bound, ?_⟩
  rw [assigned]
  exact WireValue.decode_of_layout checked expanded
    (Layout.decode_encode (Declarations.layout_tagSafe tags expanded) encoded)

theorem Extension.environment [Field F] [DecidableEq F] {decls : Declarations}
    {calls : Circuit.CallRelation F} {before after : BuildState F} {a b : Var → F}
    (extension : Extension rom calls before after a b) {locals : Locals F} {environment : Environment F}
    (bounded : LocalsBounded before.nextVar locals)
    (decoded : DecodesEnvironment decls (localsEnvironment locals a) environment) :
    DecodesEnvironment decls (localsEnvironment locals b) environment := by
  rwa [extension.locals bounded]

theorem Extension.decoded_value [Field F] [DecidableEq F] {decls : Declarations}
    {calls : Circuit.CallRelation F} {before after : BuildState F} {a b : Var → F}
    (extension : Extension rom calls before after a b) {wire : Symbolic F} {value : Value F}
    (bounded : Bounded before.nextVar wire)
    (decoded : (wire.map (ArithExpr.denote a)).decode decls = some value) :
    (wire.map (ArithExpr.denote b)).decode decls = some value := by
  rwa [extension.value bounded]

theorem Extension.decoded_values [Field F] [DecidableEq F] {decls : Declarations}
    {calls : Circuit.CallRelation F} {before after : BuildState F} {a b : Var → F}
    (extension : Extension rom calls before after a b) {wires : List (Symbolic F)} {values : List (Value F)}
    (bounded : ∀ wire ∈ wires, Bounded before.nextVar wire)
    (decoded : DecodesValues decls (wires.map (WireValue.map (ArithExpr.denote a))) values) :
    DecodesValues decls (wires.map (WireValue.map (ArithExpr.denote b))) values := by
  rwa [extension.values bounded]

theorem constrainValue_decoded_complete [Field F] [DecidableEq F] {decls : Declarations}
    (checked : checkDeclarations decls = .ok ()) {calls : Circuit.CallRelation F}
    {enable : ArithExpr F} {left right : Symbolic F} {before after : BuildState F}
    (compiled : constrainValue enable left right before = .ok ((), after)) {assignment : Var → F}
    (layout : before.WellFormed) (valid : before.Valid rom calls assignment)
    (enableBound : enable.inBounds before.nextVar = true)
    (leftBound : Bounded before.nextVar left) (rightBound : Bounded before.nextVar right)
    {value : Value F}
    (leftDecode : (left.map (ArithExpr.denote assignment)).decode decls = some value)
    (rightDecode : (right.map (ArithExpr.denote assignment)).decode decls = some value) :
    Extension rom calls before after assignment assignment :=
  constrainValue_complete compiled layout valid enableBound leftBound rightBound
    (Or.inr (WireValue.decode_injective checked leftDecode rightDecode))

end Circuit.Compiler
end Aiur
