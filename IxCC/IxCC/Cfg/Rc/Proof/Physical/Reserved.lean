import IxCC.Cfg.Rc.Proof.Physical.PublishFrame
import IxCC.Rt.Rc.Gen.Proof.Scanned

/-! Reserved allocator storage has a real unique header and permissions, but
no payload meaning yet. Publication establishes the missing Gen.LiveCell fields
before the wrapper exposes its returned address. -/
set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Lir
open IxCC.Rt.Proof
open IxCC.Rt IxCC.Rt.Rc
open IxCC.Rt.Rc.Procs
open IxCC.Rt.Rc.Gen (fieldsClass)

structure ReservedCell (mem : X86.Memory) (address : Word) (body : Own.Body) : Prop where
  fields_positive : 0 < body.fields.length
  fields_small : body.fields.length ≤ maxFields
  tag : body.ctor.tag ≤ Rt.maxTag
  nobj : body.ctor.nobj = body.fields.length
  nscalar : body.ctor.nscalar = 0
  shared : body.ctor.fieldKinds = List.replicate body.fields.length .shared
  nonzero : address ≠ 0
  aligned : address.toNat % 8 = 0
  fit : address.toNat + classBytes (fieldsClass body.fields.length) < 2^63
  readable : ∀ j < classBytes (fieldsClass body.fields.length),
    mem.readable (address + UInt64.ofNat j) = true
  writable : ∀ j < classBytes (fieldsClass body.fields.length),
    mem.writable (address + UInt64.ofNat j) = true
  header : mem.read .w32 address = UInt64.ofNat
    (headerLow body.fields.length (fieldsClass body.fields.length) body.ctor.tag)
  count : mem.read .w32 (address + 4) = 0

theorem ReservedCell.publish {mem : X86.Memory} {address : Word} {body : Own.Body}
    (reserved : ReservedCell mem address body) (addresses : AddressMap) (words : Nat → Word)
    (values : ∀ j value, body.fields[j]? = some value → valueWord addresses value = some (words j)) :
    Gen.LiveCell addresses (publishFields mem address words (List.range body.fields.length)) address 1 body := by
  obtain ⟨_, _, hlow, _⟩ := Gen.fieldsClass_spec reserved.fields_positive reserved.fields_small
  have fit : address.toNat + 8 * (body.fields.length + 1) < 2^63 := by
    have := reserved.fit
    omega
  have frame := publishFields_headerFrame fit words mem
  have hnobj : body.ctor.nobj ≤ maxFields := by rw [reserved.nobj]; exact reserved.fields_small
  have hclass : Gen.classOf body.ctor = fieldsClass body.fields.length := by
    rw [Gen.classOf_fields reserved.nscalar hnobj, reserved.nobj]
  have hbytes : Gen.cellBytesOf body.ctor = classBytes (fieldsClass body.fields.length) := by
    rw [Gen.cellBytesOf_fields reserved.nscalar hnobj, reserved.nobj]
  refine {
    positive := by decide
    bounded := by decide
    layout := by
      rw [Gen.layoutOf_fields reserved.nscalar, reserved.nobj]
      exact Gen.ofFields_ok_fields reserved.fields_positive reserved.fields_small reserved.tag
    arity := by simp [reserved.nobj, reserved.nscalar]
    shared := by rw [reserved.shared, reserved.nobj]
    nonzero := reserved.nonzero
    aligned := reserved.aligned
    fit := by rw [hbytes]; exact reserved.fit
    readable := ?_
    writable := ?_
    header := ?_
    count := ?_
    fields := ?_ }
  · intro j hj; rw [frame.readable]; exact reserved.readable j (by rwa [hbytes] at hj)
  · intro j hj; rw [frame.writable]; exact reserved.writable j (by rwa [hbytes] at hj)
  · rw [hclass, reserved.nobj, ← reserved.header]
    apply X86.Memory.readLittle_congr
    intro j hj
    apply frame.bytes_eq
    simp only [X86.Width.bytes] at hj
    omega
  · change (publishFields mem address words (List.range body.fields.length)).read .w32 (address+4) = 0
    rw [← reserved.count]
    apply X86.Memory.readLittle_congr
    intro j hj
    rw [cell_offset4]
    apply frame.bytes_eq
    simp only [X86.Width.bytes] at hj
    omega
  · intro j value lookup
    have bound := (List.getElem?_eq_some_iff.mp lookup).1
    refine ⟨words j, ?_, ?_⟩
    · simp only [Gen.fieldWord, show j < body.ctor.nobj by rw [reserved.nobj]; exact bound, ite_true]
      exact values j value lookup
    have published := publishFields_word (List.range body.fields.length) address words fit
      (fun i hi => List.mem_range.mp hi) List.nodup_range (List.mem_range.mpr bound)
      (mem := mem) (by
        intro byte hb
        rw [fieldAddress_byte]
        apply reserved.readable
        omega)
    simpa only [fieldAddress, show 8 * (j + 1) = 8 + 8 * j by omega] using published


end IxCC.Cfg.Rc.Native
