import IxCC.Cfg.Rc.Proof.Physical.ReservedHeader

set_option autoImplicit false
namespace IxCC.Cfg.Rc.Native
open IxCC.Lir
open IxCC.Rt IxCC.Rt.Rc IxCC.Rt.Proof IxCC.Rt.Rc.Procs

/-- The actual final allocator header store creates reserved storage. It
does not grant a payload interpretation; ReservedCell.publish supplies that
only after executing all field stores. Both free-pop and bump paths end in
this same store, and preceding context writes preserve permissions. -/
theorem reserve_header (mem : X86.Memory) (address : Word) (body : Own.Body)
    (positive : 0 < body.fields.length) (small : body.fields.length < 32)
    (tagBound : body.ctor.tag ≤ maxTag) (nobj : body.ctor.nobj = body.fields.length)
    (nscalar : body.ctor.nscalar = 0)
    (shared : body.ctor.fieldKinds = List.replicate body.fields.length .shared)
    (nonzero : address ≠ 0) (aligned : address.toNat % 8 = 0)
    (fit : address.toNat + cellBytes body.fields.length < 2^63)
    (readable : ∀ j < cellBytes body.fields.length, mem.readable (address + UInt64.ofNat j) = true)
    (writable : ∀ j < cellBytes body.fields.length, mem.writable (address + UInt64.ofNat j) = true) :
    ReservedCell (mem.write .w64 address
      (dynamicHeader body.fields.length (smallClass body.fields.length) body.ctor.tag 1)) address body := by
  have represented := wordAt_write64 (v := dynamicHeader body.fields.length
    (smallClass body.fields.length) body.ctor.tag 1) (m := mem) (b := address) (by
      intro j hj
      apply readable
      simp only [cellBytes]
      omega)
  have header := unique_header_reads small tagBound represented
  refine {
    fields_positive := positive
    fields_small := small
    tag := tagBound
    nobj
    nscalar
    shared
    nonzero
    aligned
    fit
    readable := ?_
    writable := ?_
    header := header.1
    count := header.2 }
  · simpa [X86.Memory.write] using readable
  · simpa [X86.Memory.write] using writable


end IxCC.Cfg.Rc.Native
