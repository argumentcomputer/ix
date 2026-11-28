import IxCC.Ixon.Serialize

/-!
# Generic reader laws

Reader specifications over `IxCC.Ixon.Serialize` that the IxIR
readers reuse, moved unchanged (names kept) from the retired Ixon v2
expression and constant modules.
-/

namespace IxCC.Ixon

def boolOfByte? : UInt8 → Option Bool
  | 0 => some false
  | 1 => some true
  | _ => none

def getDecodedU8 (what : String) (decode : UInt8 → Option α) : GetM α := do
  let b ← getU8
  match decode b with
  | some value => return value
  | none => throw s!"{what}: invalid byte {b}"

namespace ExprLaws

theorem GetSpec.map {get : GetM α} {input : ByteArray} {value : α}
    (h : GetSpec get input value) (f : α → β) :
    GetSpec (f <$> get) input (f value) := by
  let finish : α → GetM β := fun decoded => pure (f decoded)
  have hfinish : GetSpec (finish value) ByteArray.empty (f value) :=
    GetSpec.pure _
  have htotal := GetSpec.bind (next := finish) h hfinish
  simpa [finish] using htotal

end ExprLaws

namespace ConstLaws

theorem getDecodedU8_spec (what : String) (decode : UInt8 → Option α)
    (encode : α → UInt8) (hdecode : ∀ value, decode (encode value) = some value)
    (value : α) :
    GetSpec (getDecodedU8 what decode) (u8Bytes (encode value)) value := by
  intro pre suffix
  simp only [getDecodedU8, StateT.run_bind]
  rw [getU8_spec (encode value) pre suffix]
  simp only [bind, Except.bind]
  rw [hdecode value]
  rfl

end ConstLaws

end IxCC.Ixon
