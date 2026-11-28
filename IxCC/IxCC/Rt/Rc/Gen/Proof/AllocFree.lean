import IxCC.Rt.Rc.Gen.Procs
import IxCC.Rt.Rc.Proof.AllocFree

/-! The free-list path of allocation by layout: the head of the layout's class is popped and the
popped cell's header initialised; the payload is the caller's to write. -/
namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open IxCC.Rt.Proof
open Lir

def allocProgram (L : CellLayout) : Program := { funcs := #[alloc L], main := 0 }
def headAddress (context : Word) (cls : Nat) : Word :=
  context + 0 + dispWord (Int.ofNat (8 * cls))

/-- The class of an allocated layout, in the bounds the allocation proofs use. -/
theorem layout_class {L : CellLayout} {cls : Nat} (hL : L.ok = true) (hcl : L.cls? = some cls) :
    2 ≤ cls ∧ cls ≤ maxClass ∧ 16 ≤ classBytes cls ∧ classBytes cls ≤ 536870912 ∧
      8 * L.words ≤ classBytes cls := by
  obtain ⟨h2, hm, hw⟩ := CellLayout.cls_spec hL hcl
  have hmax := classWords_le_max hm
  rw [maxCellWords_eq] at hmax
  have hpos := (CellLayout.ok_bounds hL).1
  unfold classBytes CellLayout.words at *
  omega

/-- Writes performed by the free-pop path, in execution order. -/
def reserveFree (mem : X86.Memory) (context cell next : Word) (L : CellLayout) (cls : Nat) :
    X86.Memory :=
  (mem.write .w64 (headAddress context cls) next).write .w64 cell (dynamicHeader L.nobj cls L.tag 1)

theorem alloc_free_initial (mem : X86.Memory) (context : Word) (L : CellLayout) (cls : Nat)
    (hL : L.ok = true) (hcl : L.cls? = some cls) :
    State.initial (allocProgram L) [] mem context = some (allocState mem context {} 0 0) := by
  simp [State.initial, enter, allocProgram, alloc_eq hL hcl, allocFunc, bindParams, allocState]

theorem alloc_free (mem : X86.Memory) (context cell next : Word) (L : CellLayout) (cls clock : Nat)
    (hL : L.ok = true) (hcl : L.cls? = some cls)
    (hnonzero : cell ≠ 0)
    (hhead : loadWord mem .w64 .zero (headAddress context cls) = some cell)
    (hnext : loadWord mem .w64 .zero cell = some next)
    (hwhead : ∀ j < 8, mem.writable (headAddress context cls + UInt64.ofNat j) = true)
    (hwcell : ∀ j < 8, mem.writable (cell + UInt64.ofNat j) = true) :
    eval (allocProgram L) clock [] mem context =
      .ok ([cell], reserveFree mem context cell next L cls) := by
  have hb := alloc_eq hL hcl
  let e0 : Env := {}
  let e1 := e0.insert 0 cell
  let e2 := e1.insert 1 next
  let e3 := e2.insert 5 cell
  let m1 := mem.write .w64 (headAddress context cls) next
  let m2 := reserveFree mem context cell next L cls
  have he1 : e1[0]? = some cell := by simp [e1]
  have he2 : e2[0]? = some cell := by
    simp only [e2, e1, Std.HashMap.getElem?_insert]
    rfl
  have hshead := write?_ok (w := .w64) (v := next) hwhead
  have hhead' : loadWord mem .w64 .zero
      (context + dispWord (8 * (cls : Int))) = some cell := by
    simpa [headAddress] using hhead
  have hshead' : mem.write? .w64
      (context + dispWord (8 * (cls : Int))) next = .ok m1 := by
    simpa [headAddress, m1] using hshead
  have hscell : m1.write? .w64 cell (dynamicHeader L.nobj cls L.tag 1) = .ok m2 := by
    apply write?_ok (w := .w64)
    simpa [m1, X86.Memory.write, X86.Width.bytes] using hwcell
  apply (runs_eval (alloc_free_initial mem context L cls hL hcl)).eq
  apply Sem.Reaches.free (s' := allocState mem context e1 0 1)
  · apply semStep_next.mpr
    simp [step, allocProgram, allocState, hb, allocFunc, Procs.ctx,
      Stmt.exec, Rhs.eval, Addr.eval, headAddress, e1, e0, hhead']
  apply Sem.Reaches.free (s' := allocState mem context e1 1 0)
  · apply semStep_next.mpr
    simp [step, allocProgram, allocState, hb, allocFunc, v, i, to,
      Arg.eval, evalArgs, takeEdge, bindParams, he1, Cond.holds, truncate_w64, hnonzero]
  apply Sem.Reaches.free (s' := allocState mem context e2 1 1)
  · apply semStep_next.mpr
    simp [step, allocProgram, allocState, hb, allocFunc, cellAddr,
      Stmt.exec, Rhs.eval, Addr.eval, dispWord, he1, hnext, e2]
  apply Sem.Reaches.free (s' := allocState m1 context e2 1 2)
  · apply semStep_next.mpr
    simp [step, allocProgram, allocState, hb, allocFunc, Procs.ctx,
      v, Stmt.exec, Addr.eval, Arg.eval, headAddress, hshead', e2, m1]
  apply Sem.Reaches.free (s' := allocState m1 context e3 5 0)
  · apply semStep_next.mpr
    simp [step, allocProgram, allocState, hb, allocFunc, to, v,
      Arg.eval, evalArgs, takeEdge, bindParams, he2, e3]
  apply Sem.Reaches.free (s' := allocState m2 context e3 5 1)
  · apply semStep_next.mpr
    simp [step, allocProgram, allocState, hb, allocFunc, cellAddr,
      Stmt.exec, Addr.eval, Arg.eval, dispWord, e3, hscell]
  apply Sem.Reaches.final
  have done : semStep (allocProgram L) (allocState m2 context e3 5 1) = .done ([cell], m2) := by
    apply semStep_done.mpr
    simp [step, allocProgram, allocState, hb, allocFunc, v, evalArgs, Arg.eval, e3]
  rw [done]
  exact .done

/-- A word outside the class-head and popped-header writes is preserved. -/
theorem reserveFree_word {mem : X86.Memory} {context cell next address value : Word}
    {L : CellLayout} {cls : Nat} (hword : WordAt mem address value)
    (hheadfit : (headAddress context cls).toNat + 8 ≤ 2^64)
    (hcellfit : cell.toNat + 8 ≤ 2^64) (hfit : address.toNat + 8 ≤ 2^64)
    (hhead : address.toNat + 8 ≤ (headAddress context cls).toNat ∨
      (headAddress context cls).toNat + 8 ≤ address.toNat)
    (hcell : address.toNat + 8 ≤ cell.toNat ∨ cell.toNat + 8 ≤ address.toNat) :
    WordAt (reserveFree mem context cell next L cls) address value := by
  exact (hword.write_disjoint hheadfit hfit hhead).write_disjoint hcellfit hfit hcell

end IxCC.Rt.Rc.Gen
