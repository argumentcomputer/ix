import IxCC.Rt.Rc.Proof.Detach

/-! Actual finished-parent block9: save predecessor, read class head, push the
dead parent, and resume predecessor. Its 9→6 edge costs one target charge. -/
namespace IxCC.Rt.Rc.Procs
open Lir
open IxCC.Rt.Proof

def freeHeadAddress (context cls : Word) : Word := context + cls*8
def recycleParent (mem : X86.Memory) (context cls address oldHead : Word) : X86.Memory :=
  (mem.write .w64 address oldHead).write .w64 (freeHeadAddress context cls) address

theorem finished_parent_recycle (mem : X86.Memory) (context cls address predecessor oldHead : Word)
    (env : Env) (ha : env[8]? = some address) (hc : env[10]? = some cls)
    (hp : loadWord mem .w64 .zero (address+8) = some predecessor)
    (hh : loadWord mem .w64 .zero (freeHeadAddress context cls) = some oldHead)
    (hwa : ∀ j < 8, mem.writable (address+UInt64.ofNat j) = true)
    (hwh : ∀ j < 8, mem.writable (freeHeadAddress context cls+UInt64.ofNat j) = true) :
    Sem.Star (semStep releaseProgram) (releaseState mem context env 9 0) 1
      (releaseState (recycleParent mem context cls address oldHead) context
        (((env.insert 15 predecessor).insert 16 oldHead).insert 8 predecessor) 6 0) := by
  let e1 := env.insert 15 predecessor
  let e2 := e1.insert 16 oldHead
  let m1 := mem.write .w64 address oldHead
  let m2 := recycleParent mem context cls address oldHead
  have hc1 : e1[10]? = some cls := by
    simp only [e1, Std.HashMap.getElem?_insert]
    change env[10]? = some cls
    exact hc
  have hc2 : e2[10]? = some cls := by
    simp only [e2, e1, Std.HashMap.getElem?_insert]
    change env[10]? = some cls
    exact hc
  have ha2 : e2[8]? = some address := by
    simp only [e2, e1, Std.HashMap.getElem?_insert]
    change env[8]? = some address
    exact ha
  have hp2 : e2[15]? = some predecessor := by
    simp only [e2, e1, Std.HashMap.getElem?_insert]
    rfl
  have hh2 : e2[16]? = some oldHead := by
    simp only [e2, Std.HashMap.getElem?_insert]
    rfl
  have hh' : loadWord mem .w64 .zero (context+cls*8) = some oldHead := hh
  have hw1 := write?_ok (w := .w64) (v := oldHead) hwa
  have hw2 : m1.write? .w64 (context+cls*8) address = .ok m2 := by
    apply write?_ok (w := .w64)
    simpa [m1, X86.Memory.write, X86.Width.bytes, freeHeadAddress] using hwh
  apply Sem.Star.free (s' := releaseState mem context e1 9 1)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, cellAddr, Stmt.exec, Rhs.eval,
      Addr.eval, dispWord, ha, hp, e1]
  apply Sem.Star.free (s' := releaseState mem context e2 9 2)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, Stmt.exec, Rhs.eval,
      Addr.eval, dispWord, X86.Scale.word, hc1, hh', e2]
  apply Sem.Star.free (s' := releaseState m1 context e2 9 3)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, cellAddr, v, Stmt.exec,
      Addr.eval, Arg.eval, dispWord, ha2, hh2, hw1, m1]
  apply Sem.Star.free (s' := releaseState m2 context e2 9 4)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, v, Stmt.exec,
      Addr.eval, Arg.eval, dispWord, X86.Scale.word, ha2, hc2, hw2]
  apply Sem.Star.charge
    (s' := releaseState m2 context (e2.insert 8 predecessor) 6 0)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, v, to, Arg.eval, evalArgs,
      takeEdge, bindParams, hp2]
  exact .refl _

/-- Class-head/object disjointness is explicit: a free-list push cannot
overwrite its own context head when establishing the resulting link. -/
theorem recycled_link {mem : X86.Memory} {context cls address oldHead : Word}
    (hr : ∀ j < 8, mem.readable (address+UInt64.ofNat j) = true)
    (ha : address.toNat + 8 ≤ 2^64)
    (hh : (freeHeadAddress context cls).toNat + 8 ≤ 2^64)
    (hsep : address.toNat+8 ≤ (freeHeadAddress context cls).toNat ∨
      (freeHeadAddress context cls).toNat+8 ≤ address.toNat) :
    WordAt (recycleParent mem context cls address oldHead) address oldHead := by
  exact (wordAt_write64 hr).write_disjoint hh ha hsep

theorem recycled_head {mem : X86.Memory} {context cls address oldHead : Word}
    (hr : ∀ j < 8, mem.readable (freeHeadAddress context cls+UInt64.ofNat j) = true) :
    WordAt (recycleParent mem context cls address oldHead) (freeHeadAddress context cls) address := by
  apply wordAt_write64
  simpa [X86.Memory.write] using hr




end IxCC.Rt.Rc.Procs
