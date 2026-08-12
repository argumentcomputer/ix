import Navigatrix.Ixon.Serialize

/-!
# Universe levels

Unchanged from ix's Ixon — the v2 codec for `Univ` is byte-identical
(only `Expr` rolls in v2), modulo the strict-decoding discipline from
`Serialize` plus telescope canonicity: a run-length-encoded succ chain
must be maximal, so a decoded succ base may not itself be a succ.
-/

namespace Navigatrix.Ixon

/-- Universe levels for Lean's type system. -/
inductive Univ where
  | zero : Univ
  | succ : Univ → Univ
  | max : Univ → Univ → Univ
  | imax : Univ → Univ → Univ
  | var : UInt64 → Univ
  deriving BEq, Repr, Inhabited, Hashable

namespace Univ

def FLAG_ZERO_SUCC : UInt8 := 0
def FLAG_MAX : UInt8 := 1
def FLAG_IMAX : UInt8 := 2
def FLAG_VAR : UInt8 := 3

/-- Count successive `.succ` constructors. -/
def succCount : Univ → UInt64
  | .succ inner => 1 + inner.succCount
  | _ => 0

/-- Get the base of a `.succ` chain. -/
def succBase : Univ → Univ
  | .succ inner => inner.succBase
  | u => u

end Univ

partial def putUniv : Univ → PutM Unit
  | .zero => putTag2 ⟨Univ.FLAG_ZERO_SUCC, 0⟩
  | u@(.succ _) => do
    putTag2 ⟨Univ.FLAG_ZERO_SUCC, u.succCount⟩
    putUniv u.succBase
  | .max a b => do
    putTag2 ⟨Univ.FLAG_MAX, 0⟩
    putUniv a
    putUniv b
  | .imax a b => do
    putTag2 ⟨Univ.FLAG_IMAX, 0⟩
    putUniv a
    putUniv b
  | .var idx => putTag2 ⟨Univ.FLAG_VAR, idx⟩

partial def getUniv : GetM Univ := do
  let tag ← getTag2
  match tag.flag with
  | 0 =>
    if tag.size == 0 then
      return .zero
    else
      let base ← getUniv
      match base with
      | .succ _ => throw "getUniv: non-canonical succ chain"
      | _ => pure ()
      let mut result := base
      for _ in [0:tag.size.toNat] do
        result := .succ result
      return result
  | 1 => return .max (← getUniv) (← getUniv)
  | 2 => return .imax (← getUniv) (← getUniv)
  | 3 => return .var tag.size
  | f => throw s!"getUniv: invalid flag {f}"

instance : Serialize Univ where
  put := putUniv
  get := getUniv

/-! Elaboration-time roundtrip and canonicity checks. -/

private def univRoundtrips (u : Univ) : Bool :=
  match (de (ser u) : Except String Univ) with
  | .ok u' => u' == u
  | .error _ => false

#guard univRoundtrips .zero
#guard univRoundtrips (.succ (.succ .zero))
#guard univRoundtrips (.succ (.max (.var 0) (.var 1)))
#guard univRoundtrips (.max (.var 0) (.succ (.var 1)))
#guard univRoundtrips (.imax .zero (.var 40))

private def univRejects (bytes : Array UInt8) : Bool :=
  match (de (ByteArray.mk bytes) : Except String Univ) with
  | .ok _ => false
  | .error _ => true

-- succ(size 1) over a base that is itself an encoded succ: non-canonical
#guard univRejects #[0x01, 0x01, 0x00]

end Navigatrix.Ixon
