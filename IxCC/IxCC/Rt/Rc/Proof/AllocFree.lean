import IxCC.Rt.Rc.Procs
import IxCC.Rt.Proof.Mem
import IxCC.Rt.Proof.Words
import IxCC.Lir.Proof.Run

/-! Free-list allocator path, exact existing ordinary-Lir implementation.
Returns reserved storage with initialized header; payload publication and
abstract fresh-location allocation are distinct later obligations. -/
namespace IxCC.Rt.Rc.Procs
open Lir
open IxCC.Rt.Proof

def allocProgram (fields tag : Nat) : Program := { funcs := #[alloc fields tag], main := 0 }
def allocState (mem : X86.Memory) (context : Word) (env : Env) (label pos : Nat := 0) : State :=
  { mem, ctx := context, stack := [{ fn := 0, label, pos, env }] }
def headAddress (context : Word) (fields : Nat) : Word :=
  context + 0 + dispWord (Int.ofNat (8 * smallClass fields))

/-- Writes performed by the free-pop path, in execution order. The class head
is advanced before the popped cell header changes; payload bytes remain old. -/
def reserveFree (mem : X86.Memory) (context cell next : Word) (fields tag : Nat) : X86.Memory :=
  (mem.write .w64 (headAddress context fields) next).write .w64 cell
    (dynamicHeader fields (smallClass fields) tag 1)

theorem alloc_free_initial (mem : X86.Memory) (context : Word) (fields tag : Nat)
    (hpos : 0 < fields) (hsmall : fields < 32) (htag : tag ≤ maxTag) :
    State.initial (allocProgram fields tag) [] mem context = some (allocState mem context {} 0 0) := by
  have hzero : fields ≠ 0 := by omega
  simp [State.initial, enter, allocProgram, alloc, hzero,
    Nat.not_le.mpr hsmall, Nat.not_lt.mpr htag, bindParams, allocState]

theorem alloc_free (mem : X86.Memory) (context cell next : Word) (fields tag clock : Nat)
    (hpos : 0 < fields) (hsmall : fields < 32) (htag : tag ≤ maxTag)
    (hnonzero : cell ≠ 0)
    (hhead : loadWord mem .w64 .zero (headAddress context fields) = some cell)
    (hnext : loadWord mem .w64 .zero cell = some next)
    (hwhead : ∀ j < 8, mem.writable (headAddress context fields + UInt64.ofNat j) = true)
    (hwcell : ∀ j < 8, mem.writable (cell + UInt64.ofNat j) = true) :
    eval (allocProgram fields tag) clock [] mem context =
      .ok ([cell], reserveFree mem context cell next fields tag) := by
  have hzero : fields ≠ 0 := by omega
  have hlarge : ¬ 32 ≤ fields := Nat.not_le.mpr hsmall
  have htagBad : ¬ maxTag < tag := Nat.not_lt.mpr htag
  let e0 : Env := {}
  let e1 := e0.insert 0 cell
  let e2 := e1.insert 1 next
  let e3 := e2.insert 5 cell
  let m1 := mem.write .w64 (headAddress context fields) next
  let m2 := reserveFree mem context cell next fields tag
  have he1 : e1[0]? = some cell := by simp [e1]
  have he2 : e2[0]? = some cell := by
    simp only [e2, e1, Std.HashMap.getElem?_insert]
    rfl
  have hshead := write?_ok (w := .w64) (v := next) hwhead
  have hhead' : loadWord mem .w64 .zero
      (context + dispWord (8 * (smallClass fields : Int))) = some cell := by
    simpa [headAddress] using hhead
  have hshead' : mem.write? .w64
      (context + dispWord (8 * (smallClass fields : Int))) next = .ok m1 := by
    simpa [headAddress, m1] using hshead
  have hscell : m1.write? .w64 cell (dynamicHeader fields (smallClass fields) tag 1) =
      .ok m2 := by
    apply write?_ok (w := .w64)
    simpa [m1, X86.Memory.write, X86.Width.bytes] using hwcell
  apply (runs_eval (alloc_free_initial mem context fields tag hpos hsmall htag)).eq
  apply Sem.Reaches.free (s' := allocState mem context e1 0 1)
  · apply semStep_next.mpr
    simp [step, allocProgram, allocState, alloc, hzero, hlarge, htagBad, Procs.ctx,
      Stmt.exec, Rhs.eval, Addr.eval, headAddress, e1, e0, hhead']
  apply Sem.Reaches.free (s' := allocState mem context e1 1 0)
  · apply semStep_next.mpr
    simp [step, allocProgram, allocState, alloc, hzero, hlarge, htagBad, v, i, to,
      Arg.eval, evalArgs, takeEdge, bindParams, he1, Cond.holds, truncate_w64, hnonzero]
  apply Sem.Reaches.free (s' := allocState mem context e2 1 1)
  · apply semStep_next.mpr
    simp [step, allocProgram, allocState, alloc, hzero, hlarge, htagBad, cellAddr,
      Stmt.exec, Rhs.eval, Addr.eval, dispWord, he1, hnext, e2]
  apply Sem.Reaches.free (s' := allocState m1 context e2 1 2)
  · apply semStep_next.mpr
    simp [step, allocProgram, allocState, alloc, hzero, hlarge, htagBad, Procs.ctx,
      v, Stmt.exec, Addr.eval, Arg.eval, headAddress, hshead', e2, m1]
  apply Sem.Reaches.free (s' := allocState m1 context e3 5 0)
  · apply semStep_next.mpr
    simp [step, allocProgram, allocState, alloc, hzero, hlarge, htagBad, to, v,
      Arg.eval, evalArgs, takeEdge, bindParams, he2, e3]
  apply Sem.Reaches.free (s' := allocState m2 context e3 5 1)
  · apply semStep_next.mpr
    simp [step, allocProgram, allocState, alloc, hzero, hlarge, htagBad, cellAddr,
      Stmt.exec, Addr.eval, Arg.eval, dispWord, e3, hscell]
  apply Sem.Reaches.final
  have done : semStep (allocProgram fields tag) (allocState m2 context e3 5 1) = .done ([cell], m2) := by
    apply semStep_done.mpr
    simp [step, allocProgram, allocState, alloc, hzero, hlarge, htagBad, v, evalArgs, Arg.eval, e3]
  rw [done]
  exact .done

/-- A word outside the class-head and popped-header writes is preserved.
This is the frame obligation used for payload and other live-cell words. -/
theorem reserveFree_word {mem : X86.Memory} {context cell next address value : Word}
    {fields tag : Nat} (hword : WordAt mem address value)
    (hheadfit : (headAddress context fields).toNat + 8 ≤ 2^64)
    (hcellfit : cell.toNat + 8 ≤ 2^64) (hfit : address.toNat + 8 ≤ 2^64)
    (hhead : address.toNat + 8 ≤ (headAddress context fields).toNat ∨
      (headAddress context fields).toNat + 8 ≤ address.toNat)
    (hcell : address.toNat + 8 ≤ cell.toNat ∨ cell.toNat + 8 ≤ address.toNat) :
    WordAt (reserveFree mem context cell next fields tag) address value := by
  exact (hword.write_disjoint hheadfit hfit hhead).write_disjoint hcellfit hfit hcell



end IxCC.Rt.Rc.Procs
