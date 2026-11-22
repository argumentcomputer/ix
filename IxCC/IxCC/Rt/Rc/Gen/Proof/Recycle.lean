import IxCC.Rt.Rc.Gen.Proof.Detach

/-! Block 9 of the general release: read the finished parent's class, save its predecessor, push
it onto its class's list, and resume the predecessor. Its 9→6 edge costs one target charge. -/
namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open Lir
open IxCC.Rt.Proof

theorem finished_parent_recycle (mem : X86.Memory) (context cls address predecessor oldHead : Word)
    (env : Env) (ha : env[8]? = some address)
    (hc : loadWord mem .w8 .zero (address+1) = some cls)
    (hp : loadWord mem .w64 .zero (address+8) = some predecessor)
    (hh : loadWord mem .w64 .zero (freeHeadAddress context cls) = some oldHead)
    (hwa : ∀ j < 8, mem.writable (address+UInt64.ofNat j) = true)
    (hwh : ∀ j < 8, mem.writable (freeHeadAddress context cls+UInt64.ofNat j) = true) :
    Sem.Star (semStep releaseProgram) (releaseState mem context env 9 0) 1
      (releaseState (recycleParent mem context cls address oldHead) context
        ((((env.insert 11 cls).insert 15 predecessor).insert 16 oldHead).insert 8 predecessor) 6 0) := by
  let e0 := env.insert 11 cls
  let e1 := e0.insert 15 predecessor
  let e2 := e1.insert 16 oldHead
  let m1 := mem.write .w64 address oldHead
  let m2 := recycleParent mem context cls address oldHead
  have ha0 : e0[8]? = some address := by
    simp only [e0, Std.HashMap.getElem?_insert]
    change env[8]? = some address
    exact ha
  have hc1 : e1[11]? = some cls := by
    simp only [e1, e0, Std.HashMap.getElem?_insert]; rfl
  have hc2 : e2[11]? = some cls := by
    simp only [e2, e1, e0, Std.HashMap.getElem?_insert]; rfl
  have ha2 : e2[8]? = some address := by
    simp only [e2, e1, e0, Std.HashMap.getElem?_insert]
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
  apply Sem.Star.free (s' := releaseState mem context e0 9 1)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, cellAddr, Stmt.exec, Rhs.eval,
      Addr.eval, dispWord, ha, hc, e0]
  apply Sem.Star.free (s' := releaseState mem context e1 9 2)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, cellAddr, Stmt.exec, Rhs.eval,
      Addr.eval, dispWord, ha0, hp, e1]
  apply Sem.Star.free (s' := releaseState mem context e2 9 3)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, Stmt.exec, Rhs.eval,
      Addr.eval, dispWord, X86.Scale.word, hc1, hh', e2]
  apply Sem.Star.free (s' := releaseState m1 context e2 9 4)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, cellAddr, v, Stmt.exec,
      Addr.eval, Arg.eval, dispWord, ha2, hh2, hw1, m1]
  apply Sem.Star.free (s' := releaseState m2 context e2 9 5)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, v, Stmt.exec,
      Addr.eval, Arg.eval, dispWord, X86.Scale.word, ha2, hc2, hw2]
  apply Sem.Star.charge
    (s' := releaseState m2 context (e2.insert 8 predecessor) 6 0)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, v, to, Arg.eval, evalArgs,
      takeEdge, bindParams, hp2]
  exact .refl _

end IxCC.Rt.Rc.Gen
