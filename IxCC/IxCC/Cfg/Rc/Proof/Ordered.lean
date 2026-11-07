import IxCC.Cfg.Rc.Proof.ProgramSound
import IxCC.Cfg.Proof.Layout

set_option autoImplicit false
namespace IxCC.Cfg.Rc

theorem checked_dense {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    (checked : checkProgram F bodies P = true) {f : Nat} {fd : Cfg.Fun}
    (lookup : P.base.fun? f = some fd) : f < P.base.size := by
  have size := generate_size (checkProgram_parts checked).2
  by_cases h : f < P.base.size
  · exact h
  · have absent := (checked_reserved_absent checked (f := f) (by omega)).1
    rw [absent] at lookup
    cases lookup

/-- Reuse the existing block-builder ordering theorem for an arbitrary single
function. No duplicated edge-order proof or new layout assumption is needed. -/
theorem function_forward (f : Nat) (fd : Own.Fun) {b : Nat} {block : Block} {edge : Edge}
    (lookup : (Cfg.Lower.function f fd).block? b = some block)
    (member : edge ∈ block.term.edges) (forward : edge.back = false) : b < edge.target := by
  let singleton : Own.Program := {
    funs := Src.NatMap.leaf.insert f fd
    size := f + 1
    exports := []
    ctors := []
    known := {} }
  have found : (Cfg.lower singleton).fun? f = some (Cfg.Lower.function f fd) := by
    rw [Cfg.Proof.lower_fun?]
    simp [singleton, Own.Program.fun?, Src.NatMap.get?_insert_self]
  exact (Cfg.Proof.lower_ordered singleton).forward found lookup member forward

theorem checked_ordered {F : Fir.Program} {bodies : Src.NatMap Own.Plain.Code} {P : Program}
    (checked : checkProgram F bodies P = true) : Cfg.Ordered P.base where
  dense := checked_dense checked
  forward := by
    intro f fd b block edge lookup blockLookup member forward
    have size := generate_size (checkProgram_parts checked).2
    have bound : f < F.size := by rw [← size]; exact checked_dense checked lookup
    obtain ⟨actual, table, actualLookup, tableLookup, source, body, sourceLookup, bodyLookup,
      lowering, bounds, collected⟩ := checked_entry checked bound
    have same : actual = fd := Option.some.inj (actualLookup.symm.trans lookup)
    have exactLower : fd = lowerFunction F.size f source body := same.symm.trans lowering
    rw [exactLower] at blockLookup
    exact function_forward f _ blockLookup member forward


end IxCC.Cfg.Rc
