import Compilatrix.Rt.Rc.Layout
import Compilatrix.Rt.Readback

/-! Constructor-tree readback for dynamic headers. The same observation is
used for immortal and counted cells; liveness is a separate heap invariant. -/

namespace Compilatrix.Rt.Rc

open Compilatrix.Lir (Word)

/-- Readback observes the constructor shape and fields independently of its
size class and reference count. Heap liveness remains a separate invariant. -/
theorem readback_cell_header {sig : Sig} {fuel : Nat} {m : X86.Memory}
    {i n cls tag rc : Nat} {w : Word} {tys : List FoTy}
    (hw : w &&& 1 ≠ 1) (hh : m.read64? w = .ok (header n cls tag rc))
    (hn : n < 256) (hcls : cls < 256) (ht : tag < 65536) (hr : rc < 2 ^ 32)
    (hc : sig.ctor? i tag = some tys) (hl : tys.length = n) (hpos : 0 < n) :
    readback sig (fuel + 1) m (.ind i) w =
      (tys.zipIdx.mapM fun (t, j) =>
        match m.read64? (w + UInt64.ofNat (8 + 8 * j)) with
        | .ok v => readback sig fuel m t v
        | .error _ => none).map (.ctor tag) := by
  conv => lhs; unfold readback
  simp [hw, hh, header_scan hn hcls ht hr, header_tag hn hcls ht hr, hc, hl, hpos]
  rfl

end Compilatrix.Rt.Rc
