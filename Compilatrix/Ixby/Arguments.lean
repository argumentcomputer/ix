import Compilatrix.Ixby.SymbolicData

namespace Compilatrix.Ixby

theorem Data.fields_eq_of_equal {xs ys : List Data}
    (accepted : Data.equalFields xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [Data.equalFields]
  | cons x xs ih =>
      cases ys with
      | nil => simp [Data.equalFields] at accepted
      | cons y ys =>
          simp only [Data.equalFields, Bool.and_eq_true] at accepted
          cases Data.eq_of_equal _ _ accepted.1
          cases ih accepted.2
          rfl

/-- Runtime data admission, without source or target evaluation. The exact
input encoding and the bounded data decoder are checked once per argument
array; a reusable program certificate supplies all execution reasoning. -/
structure Arguments (source : Source) (config : Config) (depth : Nat) where
  data : Array Data
  raw : Array Ix.Ixby.Value
  arity : data.size = source.parameters
  sameSize : raw.size = data.size
  positive : 0 < depth
  encoded : data.mapM (encodeData source config config.depth) = .ok raw
  decoded : raw.toList.mapM (decodeData source depth) = some data.toList

def Arguments.check (source : Source) (config : Config) (depth : Nat)
    (data : Array Data) : Except String (Arguments source config depth) := do
  if positive : 0 < depth then
    if arity : data.size = source.parameters then
      admitData config.limits config.limits.inputNodes data.toList
      match encoded : data.mapM (encodeData source config config.depth) with
      | .error error => throw error
      | .ok raw =>
          let _ ← (Ix.Ixby.validateInputValues config.limits
            { functions := #[], constructors := constructorTable source }
            config.limits.inputNodes raw.toList).mapError
              (fun error => s!"Ixby argument value limit: {reprStr error}")
          if sameSize : raw.size = data.size then
            match decoded : raw.toList.mapM (decodeData source depth) with
            | none => throw "Ixby arguments cannot be decoded at the supplied ABI depth"
            | some observed =>
                if equal : Data.equalFields observed data.toList then
                  have same := Data.fields_eq_of_equal equal
                  return { data, raw, arity, sameSize, positive, encoded, decoded := same ▸ decoded }
                else throw "Ixby argument encoding/decoding disagreement"
          else throw "Ixby argument encoding changed arity"
    else throw "Ixby input arity mismatch"
  else throw "Ixby argument observation depth must be positive"

def Arguments.dataAt {source config depth} (args : Arguments source config depth) (i : Nat) : Data :=
  args.data[i]?.getD .erased

def Arguments.rawAt {source config depth} (args : Arguments source config depth) (i : Nat) : Ix.Ixby.Value :=
  args.raw[i]?.getD (.ctor (boxId 0) #[])

theorem Arguments.represented {source config depth} (args : Arguments source config depth) (i : Nat) :
    decodeData source depth (args.rawAt i) = some (args.dataAt i) := by
  have point := SymbolicData.mapM_getElem? args.decoded i
  simp only [Array.getElem?_toList] at point
  cases raw : args.raw[i]? with
  | none =>
      have data : args.data[i]? = none := by simpa [raw] using point.symm
      cases depth with
      | zero => have := args.positive; omega
      | succ depth =>
          have boxSame : (boxId 0 == boxId 0) = true := by decide
          simp [Arguments.rawAt, Arguments.dataAt, raw, data, decodeData, boxSame]
  | some value =>
      have bound := (Array.getElem?_eq_some_iff.mp raw).1
      cases data : args.data[i]? with
      | none =>
          have size := Array.getElem?_eq_none_iff.mp data
          have same := args.sameSize
          omega
      | some value => simpa [Arguments.rawAt, Arguments.dataAt, raw, data] using point

/-- Enumeration of the admitted array is exact, including parameter order. -/
theorem Arguments.raw_range {source config depth} (args : Arguments source config depth) :
    ((List.range source.parameters).map args.rawAt).toArray = args.raw := by
  apply Array.ext
  · simp [args.sameSize, args.arity]
  · intro i left right
    simp [Arguments.rawAt, List.getElem_toArray, List.getElem_map, List.getElem_range,
      Array.getElem?_eq_getElem right]

theorem Arguments.data_range {source config depth} (args : Arguments source config depth) :
    (List.range source.parameters).map args.dataAt = args.data.toList := by
  apply List.ext_getElem
  · simp [args.arity]
  · intro i left right
    have bound : i < args.data.size := by simpa using right
    simp [Arguments.dataAt, List.getElem_map, List.getElem_range,
      Array.getElem?_eq_getElem bound]

end Compilatrix.Ixby
