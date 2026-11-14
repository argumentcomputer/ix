import IxVMRefinement.L1.ByteStream
import IxVMRefinement.Obs.Ingress

/-! # What the loaders hashed

`Ingress::load_verified_blob(addr)` and `Ingress::load_verified_constant(addr)` read a byte
stream from the host (`IxVMCompat::io_get_info`, `IxByteStream::read_finite_byte_stream`) and
check it with `Blake3::verify_bytes_against(bytes, *addr)`. Every accepting derivation:
* hashed the bytes it returns (or deserializes): `Hashed calls bytes`, from the
  `Blake3::hash` call inside the check;
* pins the 32 entries of the address value `*addr` to `Blake3.Pure.digest bytes` (the stream has
  fewer than `2^32` bytes, so BLAKE3's length bound holds), whatever produced that value;
* so, when `addr` points to a represented address (`RepAddressRef`), that address is
  `Address.blake3Pure bytes`.
`load_verified_constant` also exposes its `IxonDeserialize::get_constant` sub-derivation on the
stream, whose rest is empty.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics

namespace IxVM.Refinement.L1

open IxVM (F)
open IxVM.Refinement.Obs

/-! ## Addresses -/

/-- The address with these 32 bytes. -/
def ixAddr (d : Vector UInt8 32) : Address := ⟨⟨d.toArray⟩⟩

/-- `Address.blake3Pure` is `Blake3.Pure.digest` of the bytes. -/
theorem blake3Pure_eq (bytes : List UInt8) :
    Address.blake3Pure ⟨bytes.toArray⟩ = ixAddr (Blake3.Pure.digest bytes) := by
  first
  | rfl
  | (simp [Address.blake3Pure, Blake3.Pure.hash, ixAddr]; done)
  | (unfold Address.blake3Pure Blake3.Pure.hash ixAddr; simp)

/-- **A `Blake3::hash` call on a stream gives `Hashed`.** -/
theorem hashed_of_call {cs : List (Call F)} {inp : SourceValue F} {m : Heap F}
    {bytes : List UInt8} (hc : (⟨"Blake3::hash", [inp], m⟩ : Call F) ∈ cs)
    (hs : Stream m bytes inp) : Hashed cs ⟨bytes.toArray⟩ :=
  ⟨_, hc, rfl, inp, rfl, by first | exact hs | simpa using hs⟩

theorem load_of_cell {h : Heap F} {ty : Aiur.Ty} {n : Nat} {v raw : SourceValue F}
    (cell : h[n]? = some v) (hl : loadValue h (.ptr ty n) = .ok raw) : raw = v := by
  by_cases ht : v.type = ty
  · subst ht
    have e : loadValue h (.ptr v.type n) = .ok v := by
      simp [loadValue, cell, bind, Except.bind, pure, Except.pure]
    exact ok_inj (hl.symm.trans e)
  · simp [loadValue, cell, ht, bind, Except.bind, pure, Except.pure] at hl

/-- The value a represented address pointer loads. -/
theorem load_repAddressRef {h : Heap F} {ty : Aiur.Ty} {addr : Vector UInt8 32}
    {a raw : SourceValue F} (ha : Aiur.Library.Bytes.RepAddressRef ty h addr a)
    (hl : loadValue h a = .ok raw) : raw = digestV addr := by
  obtain ⟨n, v, rfl, cell, hv⟩ := ha
  rw [load_of_cell cell hl]
  exact hv

theorem native_of_lt {bytes : List UInt8} (h : bytes.length < 4294967296) :
    Blake3.Pure.NativeInput bytes := by
  show bytes.length < 2 ^ 64
  have : (4294967296 : Nat) < 2 ^ 64 := by norm_num
  omega

/-! ## The checked reads -/

/-- The common part of the loaders: an `io_get_info`, a finite read, and the check. -/
theorem checked_read {raw ch idx len inp v : SourceValue F} {h m1 m2 m3 : Heap F}
    {cs1 cs2 cs3 : List (Call F)}
    (ev1 : ObsFn W "IxVMCompat::io_get_info" [ch, raw] h (.tuple [idx, len]) m1 cs1)
    (ev2 : ObsFn W "IxByteStream::read_finite_byte_stream" [ch, idx, len] m1 inp m2 cs2)
    (ev3 : ObsFn W "Blake3::verify_bytes_against" [inp, raw] m2 v m3 cs3) :
    ∃ bytes : List UInt8, bytes.length < 4294967296 ∧ Heap.Extends h m2 ∧
      Heap.Extends m2 m3 ∧ Stream m2 bytes inp ∧
      (⟨"Blake3::hash", [inp], m2⟩ : Call F) ∈ cs3 ∧
      ∀ i, (hi : i < 32) → projectValue raw i = .ok (bv (Blake3.Pure.digest bytes)[i]) := by
  have hm1 := io_get_info_spec ev1
  subst hm1
  obtain ⟨ext1, bytes, hlen, -, hst⟩ := read_finite_byte_stream_spec ev2
  obtain ⟨ext2, hcall, hproj⟩ := verify_spec hst ev3
  refine ⟨bytes, hlen, ext1, ext2, hst, hcall, ?_⟩
  intro i hi
  rw [hproj i hi, Aiur.Library.Blake3.hash_model_spec bytes (native_of_lt hlen)]

/-- **`Ingress::load_verified_blob(addr)`** returns a stream of bytes the derivation hashed,
whose BLAKE3 digest the 32 entries of `*addr` are. -/
theorem load_verified_blob_spec {a raw r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ld : loadValue h a = .ok raw)
    (ev : ObsFn W "Ingress::load_verified_blob" [a] h r h' cs) :
    Heap.Extends h h' ∧ ∃ bytes : List UInt8, bytes.length < 4294967296 ∧ Stream h' bytes r ∧
      Hashed cs ⟨bytes.toArray⟩ ∧
      ∀ i, (hi : i < 32) → projectValue raw i = .ok (bv (Blake3.Pure.digest bytes)[i]) := by
  obtain ⟨v1, m14, cs24, x_idx, x_len, v55, m56, cs66, v92, m93, cs103, ld11, ev26, ev68, ev105,
    he123, he124, hc125⟩ := «Ingress::load_verified_blob».obs ev
  obtain rfl := ok_inj (ld.symm.trans ld11)
  obtain ⟨bytes, hlen, ext1, ext2, hst, hcall, hproj⟩ := checked_read ev26 ev68 ev105
  have hashed : Hashed cs ⟨bytes.toArray⟩ :=
    hashed_of_call (by rw [hc125]; simp [hcall]) hst
  subst he123 he124
  exact ⟨ext1.trans ext2, bytes, hlen, hst.mono ext2, hashed, hproj⟩

/-- **`load_verified_blob` on a represented address**: the address is `Address.blake3Pure` of
bytes the derivation hashed, and the result is a stream of them. -/
theorem load_verified_blob_addr {ty : Aiur.Ty} {addr : Vector UInt8 32} {a r : SourceValue F}
    {h h' : Heap F} {cs : List (Call F)} (ha : Aiur.Library.Bytes.RepAddressRef ty h addr a)
    (ev : ObsFn W "Ingress::load_verified_blob" [a] h r h' cs) :
    Heap.Extends h h' ∧ ∃ bytes : List UInt8, Stream h' bytes r ∧ Hashed cs ⟨bytes.toArray⟩ ∧
      Address.blake3Pure ⟨bytes.toArray⟩ = ixAddr addr := by
  obtain ⟨n, v, rfl, cell, hv⟩ := ha
  have ld : loadValue h (.ptr ty n) = .ok v := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, ld11, -⟩ := «Ingress::load_verified_blob».obs ev
    have e := load_of_cell cell ld11
    subst e
    exact ld11
  obtain ⟨ext, bytes, -, hst, hashed, hproj⟩ := load_verified_blob_spec ld ev
  refine ⟨ext, bytes, hst, hashed, ?_⟩
  rw [blake3Pure_eq, digest_eq_of_proj hv hproj]

/-- **`Ingress::load_verified_constant(addr)`** deserializes bytes the derivation hashed, whose
BLAKE3 digest the 32 entries of `*addr` are: its result and heap are those of a
`IxonDeserialize::get_constant` sub-derivation on the stream of those bytes, which leaves an
empty rest. -/
theorem load_verified_constant_spec {a raw r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} (ld : loadValue h a = .ok raw)
    (ev : ObsFn W "Ingress::load_verified_constant" [a] h r h' cs) :
    ∃ (bytes : List UInt8) (inp rest : SourceValue F) (m : Heap F) (cs' : List (Call F)),
      bytes.length < 4294967296 ∧ Heap.Extends h m ∧ Stream m bytes inp ∧
      Hashed cs ⟨bytes.toArray⟩ ∧
      (∀ i, (hi : i < 32) → projectValue raw i = .ok (bv (Blake3.Pure.digest bytes)[i])) ∧
      ObsFn W "IxonDeserialize::get_constant" [inp] m (.tuple [r, rest]) h' cs' ∧
      loadValue h' rest = .ok (.construct Names.«Lists::Node<Field>» "Nil" []) ∧
      (⟨"IxonDeserialize::get_constant", [inp], m⟩ : Call F) ∈ cs := by
  obtain ⟨v1, m14, cs24, x_idx, x_len, v55, m56, cs66, v92, m93, cs103, m123, cs133, x_constant,
    x_rest, ld11, ev26, ev68, ev105, ev135, ld167, he173, he174, hc175⟩ :=
    «Ingress::load_verified_constant».obs ev
  obtain rfl := ok_inj (ld.symm.trans ld11)
  obtain ⟨bytes, hlen, ext1, ext2, hst, hcall, hproj⟩ := checked_read ev26 ev68 ev105
  have hashed : Hashed cs ⟨bytes.toArray⟩ :=
    hashed_of_call (by rw [hc175]; simp [hcall]) hst
  have hget : (⟨"IxonDeserialize::get_constant", [v55], m93⟩ : Call F) ∈ cs := by
    rw [hc175]
    simp
  subst he173 he174
  exact ⟨bytes, v55, x_rest, m93, cs133, hlen, ext1.trans ext2, hst.mono ext2, hashed, hproj,
    ev135, ld167, hget⟩

/-- **`load_verified_constant` on a represented address**: the address is `Address.blake3Pure`
of bytes the derivation hashed, and the result is what `get_constant` read from them. -/
theorem load_verified_constant_addr {ty : Aiur.Ty} {addr : Vector UInt8 32}
    {a r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ha : Aiur.Library.Bytes.RepAddressRef ty h addr a)
    (ev : ObsFn W "Ingress::load_verified_constant" [a] h r h' cs) :
    ∃ (bytes : List UInt8) (inp rest : SourceValue F) (m : Heap F) (cs' : List (Call F)),
      Heap.Extends h m ∧ Stream m bytes inp ∧ Hashed cs ⟨bytes.toArray⟩ ∧
      Address.blake3Pure ⟨bytes.toArray⟩ = ixAddr addr ∧
      ObsFn W "IxonDeserialize::get_constant" [inp] m (.tuple [r, rest]) h' cs' ∧
      loadValue h' rest = .ok (.construct Names.«Lists::Node<Field>» "Nil" []) ∧
      (⟨"IxonDeserialize::get_constant", [inp], m⟩ : Call F) ∈ cs := by
  obtain ⟨n, v, rfl, cell, hv⟩ := ha
  have ld : loadValue h (.ptr ty n) = .ok v := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ld11, -⟩ :=
      «Ingress::load_verified_constant».obs ev
    have e := load_of_cell cell ld11
    subst e
    exact ld11
  obtain ⟨bytes, inp, rest, m, cs', -, ext, hst, hashed, hproj, hget, hrest, hmem⟩ :=
    load_verified_constant_spec ld ev
  refine ⟨bytes, inp, rest, m, cs', ext, hst, hashed, ?_, hget, hrest, hmem⟩
  rw [blake3Pure_eq, digest_eq_of_proj hv hproj]

end IxVM.Refinement.L1
