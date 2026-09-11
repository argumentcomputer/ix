import Ix.Compiler.Ixon.Serialize

/-!
# Content addresses

32-byte blake3 hashes of canonical artifact serializations. Ixon identity
follows ix's `docs/Ixon.md` and `docs/kernel_identity.md`; backend IRs have
independently versioned domains. This module is the pure data side;
`Ix.Compiler.Ixon.Hash` supplies BLAKE3 computation through the current FFI
ledger entry.
-/

namespace Ix.Compiler.Ixon

/-- A content address whose 32-byte wire invariant is enforced by the type. -/
structure Address where
  hash : ByteArray
  hash_size : hash.size = 32
  deriving DecidableEq

namespace Address

/-- Construct an address from a function over its 32 byte positions. -/
def ofFn (f : Fin 32 → UInt8) : Address :=
  ⟨⟨Array.ofFn f⟩, by simp [ByteArray.size]⟩

/-- Construct a test/scaffolding address by repeating one byte. -/
def replicate (b : UInt8) : Address :=
  ofFn fun _ => b

/-- Read one of an address's 32 bytes. -/
def get (a : Address) (i : Fin 32) : UInt8 :=
  a.hash[i.val]'(a.hash_size.symm ▸ i.isLt)

/-- Synthetic address for member `idx` of a mutual block. This is shared by
the source evaluator's opaque-member oracle identity and the erased program's
environment key. It remains v1 scaffolding until members receive real content
addresses. -/
def memberAddr (block : Address) (idx : Nat) : Address :=
  ofFn fun i =>
    if i.val < 24 then block.get i
    else block.get i ^^^
      UInt8.ofNat (((idx + 1) >>> (8 * (i.val - 24))) % 256)

/-- Lowercase fixed-width hexadecimal, matching ix's catalog/report spelling. -/
def toHex (a : Address) : String :=
  a.hash.data.foldl (fun output byte =>
    output ++ hexDigitRepr (byte.toNat / 16) ++
      hexDigitRepr (byte.toNat % 16)) ""

@[simp] theorem data_ofFn (f : Fin 32 → UInt8) :
    (ofFn f).hash.data = Array.ofFn f := by
  rfl

@[simp] theorem get_mk (data : Array UInt8) (h : data.size = 32)
    (i : Fin 32) :
    (Address.mk ⟨data⟩ h).get i = data[i.val]'(by omega) := by
  rfl

@[simp] theorem get_ofFn (f : Fin 32 → UInt8) (i : Fin 32) :
    (ofFn f).get i = f i := by
  rw [show ofFn f = Address.mk ⟨Array.ofFn f⟩
      (by simp [ByteArray.size]) from rfl]
  rw [get_mk]
  rw [Array.getElem_ofFn]

@[simp] theorem memberAddr_get (block : Address) (idx : Nat) (i : Fin 32) :
    (memberAddr block idx).get i =
      if i.val < 24 then block.get i
      else block.get i ^^^
        UInt8.ofNat (((idx + 1) >>> (8 * (i.val - 24))) % 256) := by
  simp [memberAddr]

@[simp] theorem get_replicate (b : UInt8) (i : Fin 32) :
    (replicate b).get i = b := by
  rw [show replicate b =
      Address.mk ⟨Array.ofFn (fun _ : Fin 32 => b)⟩
        (by simp [ByteArray.size]) from rfl]
  rw [get_mk]
  rw [Array.getElem_ofFn]

/-- Construct from a byte array, checking the length. -/
def ofBytes? (bytes : ByteArray) : Option Address :=
  if h : bytes.size = 32 then some ⟨bytes, h⟩ else none

end Address

instance : Inhabited Address := ⟨Address.replicate 0⟩

instance : BEq Address := ⟨fun a b => a.hash.data == b.hash.data⟩

instance : Hashable Address := ⟨fun a => hash a.hash.data⟩

instance : Repr Address :=
  ⟨fun a _ => "Address " ++ repr a.hash.data⟩

instance : ToString Address := ⟨Address.toHex⟩

instance : Serialize Address where
  put a := putBytes a.hash
  get := do
    let bytes ← getBytes 32
    match Address.ofBytes? bytes with
    | some a => return a
    | none => throw "internal: getBytes returned a non-32-byte address"

namespace Address

/-- Address equality reflected by the compact byte-array `BEq` instance. -/
theorem eq_of_beq {a b : Address} (h : (a == b) = true) : a = b := by
  cases a with
  | mk ah ahs =>
    cases b with
    | mk bh bhs =>
      simp only [BEq.beq] at h
      have hab : ah.data = bh.data := (beq_iff_eq).mp h
      have : ah = bh := ByteArray.ext hab
      cases this
      rfl

instance : ReflBEq Address where
  rfl := by
    intro address
    change (address.hash.data == address.hash.data) = true
    exact (beq_iff_eq).mpr rfl

instance : LawfulBEq Address where
  eq_of_beq := Address.eq_of_beq

theorem ofBytes?_hash (a : Address) : Address.ofBytes? a.hash = some a := by
  cases a with
  | mk hash hash_size =>
    simp [Address.ofBytes?, hash_size]

theorem put_spec (a : Address) :
    PutSpec (Serialize.put a) a.hash := by
  exact putBytes_spec a.hash

theorem get_spec (a : Address) :
    GetSpec (Serialize.get (self := inferInstance) : GetM Address) a.hash a := by
  intro pre suffix
  change (do
    let bytes ← getBytes 32
    match Address.ofBytes? bytes with
    | some a => return a
    | none => throw "internal: getBytes returned a non-32-byte address").run
      ⟨pre ++ a.hash ++ suffix, pre.size⟩ = _
  simp only [StateT.run_bind]
  have hread := getBytes_spec a.hash pre suffix
  rw [a.hash_size] at hread
  rw [hread]
  simp only [bind, Except.bind]
  rw [ofBytes?_hash]
  simp [a.hash_size]
  rfl

/-- The fixed-width address codec decodes every address it encodes. -/
theorem roundtripLaw : Ixon.RoundtripLaw Address := by
  intro a
  change runGet Serialize.get (runPut (Serialize.put a)) = .ok a
  rw [runPut_eq_of_spec (put_spec a)]
  exact runGet_eq_ok_of_spec (get_spec a)

/-- Every accepted address byte string is its unique 32-byte spelling. -/
theorem canonicalLaw : Ixon.CanonicalLaw Address := by
  intro input a h
  change runPut (Serialize.put a) = input
  rw [runPut_eq_of_spec (put_spec a)]
  change runGet (do
    let bytes ← getBytes 32
    match Address.ofBytes? bytes with
    | some a => return a
    | none => throw "internal: getBytes returned a non-32-byte address") input = .ok a at h
  by_cases hlen : 32 ≤ input.size
  · have hextract : (input.extract 0 32).size = 32 := by
      simp [ByteArray.size_extract, hlen]
    simp [runGet, getBytes, hlen, Address.ofBytes?, hextract] at h
    by_cases hfull : 32 = input.size
    · simp only [hfull, if_pos] at h
      change Except.ok _ = Except.ok a at h
      cases h
      have hall := ByteArray.extract_append_eq_right
        (a := ByteArray.empty) (b := input) (i := 0) (j := input.size)
        (by simp) (by simp)
      exact hall
    · simp only [hfull] at h
      change (Except.error _ : Except String Address) = Except.ok a at h
      contradiction
  · simp [runGet, getBytes, hlen] at h
    change (Except.error _ : Except String Address) = Except.ok a at h
    contradiction

end Address

/-! Elaboration-time invariant and codec checks. -/

private def bytes (n : Nat) (b : UInt8) : ByteArray :=
  ⟨(List.replicate n b).toArray⟩

#guard (Address.ofBytes? (bytes 31 0xAA)).isNone
#guard (Address.ofBytes? (bytes 32 0xAA)).isSome
#guard (Address.ofBytes? (bytes 33 0xAA)).isNone

#guard ser (Address.replicate 0xAB) == bytes 32 0xAB

private def rejects (input : ByteArray) : Bool :=
  match (de input : Except String Address) with
  | .ok _ => false
  | .error _ => true

#guard rejects (bytes 31 0xAB)
#guard rejects (bytes 33 0xAB)

end Ix.Compiler.Ixon
