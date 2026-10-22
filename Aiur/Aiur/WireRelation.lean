import Aiur.EncodingTypes
import Aiur.WireFacts

namespace Aiur

@[simp] theorem WireValue.decode_field [NatCast F] [Zero F] [DecidableEq F]
    (decls : Declarations) (value : F) : (WireValue.field value).decode decls = some (.field value) := by
  simp [WireValue.decode, WireValue.field, Declarations.layout, Ty.checkNames,
    Declarations.expand, Ty.layoutWith, Except.toOption, Layout.decode, Value.hasType,
    Value.type, Value.wellFormed, bind, Except.bind, Option.bind]

/-- A list of flat encodings and the corresponding nominal source values. -/
def DecodesValues [NatCast F] [Zero F] [DecidableEq F] (decls : Declarations)
    (wires : List (WireValue F)) (values : List (Value F)) : Prop :=
  List.Forall₂ (fun wire value => wire.decode decls = some value) wires values

namespace DecodesValues

theorem types [NatCast F] [Zero F] [DecidableEq F] {decls : Declarations}
    {wires : List (WireValue F)} {values : List (Value F)} (decoded : DecodesValues decls wires values) :
    values.map Value.type = wires.map WireValue.type := by
  induction decoded with
  | nil => rfl
  | cons head tail ih => simp [(WireValue.decode_spec head).1, ih]

theorem wellFormed [NatCast F] [Zero F] [DecidableEq F] {decls : Declarations}
    {wires : List (WireValue F)} {values : List (Value F)} (decoded : DecodesValues decls wires values) :
    ∀ value ∈ values, value.wellFormed decls = true := by
  induction decoded with
  | nil => simp
  | cons head tail ih => simpa using And.intro (WireValue.decode_spec head).2.1 ih

theorem unique [NatCast F] [Zero F] [DecidableEq F] {decls : Declarations}
    {wires : List (WireValue F)} {values other : List (Value F)}
    (decoded : DecodesValues decls wires values) (also : DecodesValues decls wires other) : values = other := by
  induction decoded generalizing other with
  | nil => cases also; rfl
  | cons head tail ih =>
      cases also with
      | cons head' tail' => simp [Option.some.inj (head.symm.trans head'), ih tail']

theorem exists_of_each [NatCast F] [Zero F] [DecidableEq F] {decls : Declarations}
    {wires : List (WireValue F)} (decoded : ∀ wire ∈ wires, ∃ value, wire.decode decls = some value) :
    ∃ values, DecodesValues decls wires values := by
  induction wires with
  | nil => exact ⟨[], .nil⟩
  | cons wire wires ih =>
      obtain ⟨value, head⟩ := decoded wire (by simp)
      obtain ⟨values, tail⟩ := ih (fun w h => decoded w (by simp [h]))
      exact ⟨value :: values, .cons head tail⟩

theorem getElem [NatCast F] [Zero F] [DecidableEq F] {decls : Declarations}
    {wires : List (WireValue F)} {values : List (Value F)} (decoded : DecodesValues decls wires values)
    {index : Nat} {wire : WireValue F} (found : wires[index]? = some wire) :
    ∃ value, values[index]? = some value ∧ wire.decode decls = some value := by
  induction decoded generalizing index with
  | nil => simp at found
  | cons head tail ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst wire
          exact ⟨_, rfl, head⟩
      | succ index => exact ih (by simpa using found)

end DecodesValues

/-- Environments preserve binding order and names while decoding their values. -/
def DecodesEnvironment [NatCast F] [Zero F] [DecidableEq F] (decls : Declarations)
    (wires : List (String × WireValue F)) (values : Environment F) : Prop :=
  List.Forall₂ (fun wire value => wire.1 = value.1 ∧ wire.2.decode decls = some value.2) wires values

namespace DecodesEnvironment

theorem append [NatCast F] [Zero F] [DecidableEq F] {decls : Declarations}
    {left right : List (String × WireValue F)} {first second : Environment F}
    (head : DecodesEnvironment decls left first) (tail : DecodesEnvironment decls right second) :
    DecodesEnvironment decls (left ++ right) (first ++ second) := by
  induction head with
  | nil => exact tail
  | cons h hs ih => exact .cons h ih

theorem wellFormed [NatCast F] [Zero F] [DecidableEq F] {decls : Declarations}
    {wires : List (String × WireValue F)} {values : Environment F}
    (decoded : DecodesEnvironment decls wires values) : values.WellFormed decls := by
  induction decoded with
  | nil => simp [Environment.WellFormed]
  | cons head tail ih =>
      simp only [Environment.WellFormed, List.mem_cons, forall_eq_or_imp] at ih ⊢
      exact ⟨(WireValue.decode_spec head.2).2.1, ih⟩

theorem find [NatCast F] [Zero F] [DecidableEq F] {decls : Declarations}
    {wires : List (String × WireValue F)} {values : Environment F}
    (decoded : DecodesEnvironment decls wires values) (name : String)
    {wire : String × WireValue F} (found : wires.find? (·.1 == name) = some wire) :
    ∃ value, values.find? (·.1 == name) = some (wire.1, value) ∧ wire.2.decode decls = some value := by
  induction decoded with
  | nil => simp at found
  | @cons x y xs ys head tail ih =>
      by_cases same : x.1 = name
      · have sameWire : x = wire := by simpa [List.find?_cons, same] using found
        subst wire
        refine ⟨y.2, ?_, head.2⟩
        have yName : y.1 = name := head.1.symm.trans same
        simp only [List.find?_cons, yName, beq_self_eq_true, ↓reduceIte]
        exact congrArg some (Prod.ext head.1.symm rfl)
      · have tailFound : xs.find? (·.1 == name) = some wire := by
          simpa [List.find?_cons, same] using found
        obtain ⟨value, result, decoded⟩ := ih tailFound
        refine ⟨value, ?_, decoded⟩
        simpa [List.find?_cons, ← head.1, same] using result

end DecodesEnvironment

theorem DecodesValues.environment [NatCast F] [Zero F] [DecidableEq F] {decls : Declarations}
    {wires : List (WireValue F)} {values : List (Value F)} (decoded : DecodesValues decls wires values)
    (names : List String) : DecodesEnvironment decls (names.zip wires) (names.zip values) := by
  induction decoded generalizing names with
  | nil => simp [DecodesEnvironment]
  | cons head tail ih =>
      cases names with
      | nil => exact .nil
      | cons name names => exact .cons ⟨rfl, head⟩ (ih names)

end Aiur
