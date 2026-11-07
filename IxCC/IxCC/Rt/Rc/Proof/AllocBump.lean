import IxCC.Rt.Rc.Proof.AllocFree

namespace IxCC.Rt.Rc.Procs
open Lir
open IxCC.Rt.Proof

def bumpAddress (context : Word) : Word := context + dispWord bumpOff
def limitAddress (context : Word) : Word := context + dispWord limitOff
def reserveBump (mem : X86.Memory) (context cell next : Word) (fields tag : Nat) : X86.Memory :=
  (mem.write .w64 (bumpAddress context) next).write .w64 cell
    (dynamicHeader fields (smallClass fields) tag 1)
def bumpEnv (cell limit : Word) : Env := ((({} : Env).insert 0 0).insert 2 cell).insert 3 limit

/-- Empty class head takes the existing bump path and reads its two context
words. No memory writes or clock charges have occurred at this boundary. -/
theorem alloc_bump_prefix (mem : X86.Memory) (context cell limit : Word) (fields tag : Nat)
    (hpos : 0 < fields) (hsmall : fields < 32) (htag : tag ≤ maxTag)
    (hhead : loadWord mem .w64 .zero (headAddress context fields) = some 0)
    (hbump : loadWord mem .w64 .zero (bumpAddress context) = some cell)
    (hlimit : loadWord mem .w64 .zero (limitAddress context) = some limit) :
    Sem.Star (semStep (allocProgram fields tag)) (allocState mem context {} 0 0) 0
      (allocState mem context (bumpEnv cell limit) 2 2) := by
  have hz : fields ≠ 0 := by omega
  have hl : ¬ 32 ≤ fields := Nat.not_le.mpr hsmall
  have ht : ¬ maxTag < tag := Nat.not_lt.mpr htag
  have hh : loadWord mem .w64 .zero
      (context + dispWord (8 * (smallClass fields : Int))) = some 0 := by
    simpa [headAddress] using hhead
  apply Sem.Star.free (s' := allocState mem context (({} : Env).insert 0 0) 0 1)
  · apply semStep_next.mpr
    simp [step, allocProgram, allocState, alloc, hz, hl, ht, Procs.ctx,
      Stmt.exec, Rhs.eval, Addr.eval, hh]
  apply Sem.Star.free (s' := allocState mem context (({} : Env).insert 0 0) 2 0)
  · apply semStep_next.mpr
    simp [step, allocProgram, allocState, alloc, hz, hl, ht, v, i, to,
      Arg.eval, evalArgs, takeEdge, bindParams, Cond.holds]
  apply Sem.Star.free (s' := allocState mem context ((({} : Env).insert 0 0).insert 2 cell) 2 1)
  · apply semStep_next.mpr
    have hb : loadWord mem .w64 .zero (context + dispWord bumpOff) = some cell := hbump
    simp [step, allocProgram, allocState, alloc, hz, hl, ht, Procs.ctx,
      Stmt.exec, Rhs.eval, Addr.eval, hb]
  apply Sem.Star.free (s' := allocState mem context (bumpEnv cell limit) 2 2)
  · apply semStep_next.mpr
    have he : loadWord mem .w64 .zero (context + dispWord limitOff) = some limit := hlimit
    simp [step, allocProgram, allocState, alloc, hz, hl, ht, Procs.ctx,
      Stmt.exec, Rhs.eval, Addr.eval, bumpEnv, he]
  exact .refl _

theorem alloc_bump (mem : X86.Memory) (context cell limit : Word) (fields tag clock : Nat)
    (hpos : 0 < fields) (hsmall : fields < 32) (htag : tag ≤ maxTag)
    (hhead : loadWord mem .w64 .zero (headAddress context fields) = some 0)
    (hbump : loadWord mem .w64 .zero (bumpAddress context) = some cell)
    (hlimit : loadWord mem .w64 .zero (limitAddress context) = some limit)
    (hcarry : ¬ cell + UInt64.ofNat (cellBytes fields) < cell)
    (hfit : Cond.holds .ule .w64 (cell + UInt64.ofNat (cellBytes fields)) limit = true)
    (hwctx : ∀ j < 8, mem.writable (bumpAddress context + UInt64.ofNat j) = true)
    (hwcell : ∀ j < 8, mem.writable (cell + UInt64.ofNat j) = true) :
    eval (allocProgram fields tag) clock [] mem context =
      .ok ([cell], reserveBump mem context cell (cell + UInt64.ofNat (cellBytes fields)) fields tag) := by
  have hz : fields ≠ 0 := by omega
  have hl : ¬ 32 ≤ fields := Nat.not_le.mpr hsmall
  have ht : ¬ maxTag < tag := Nat.not_lt.mpr htag
  let next := cell + UInt64.ofNat (cellBytes fields)
  let e1 := bumpEnv cell limit
  let e2 := e1.insert 4 next
  let e3 := e2.insert 5 cell
  let m1 := mem.write .w64 (bumpAddress context) next
  let m2 := reserveBump mem context cell next fields tag
  have hc : e1[2]? = some cell := by simp only [e1, bumpEnv, Std.HashMap.getElem?_insert]; rfl
  have he : e2[3]? = some limit := by simp only [e2, e1, bumpEnv, Std.HashMap.getElem?_insert]; rfl
  have hc2 : e2[2]? = some cell := by simp only [e2, e1, bumpEnv, Std.HashMap.getElem?_insert]; rfl
  have hsctx : mem.write? .w64 (context + dispWord bumpOff) next = .ok m1 :=
    write?_ok (w := .w64) hwctx
  have hscell : m1.write? .w64 cell (dynamicHeader fields (smallClass fields) tag 1) = .ok m2 := by
    apply write?_ok (w := .w64)
    simpa [m1, X86.Memory.write, X86.Width.bytes] using hwcell
  apply (runs_eval (alloc_free_initial mem context fields tag hpos hsmall htag)).eq
  have finish : Sem.Reaches (semStep (allocProgram fields tag)) (allocState mem context e1 2 2)
      clock (.ok ([cell], m2)) := by
    apply Sem.Reaches.free (s' := allocState mem context e2 3 0)
    · apply semStep_next.mpr
      simp [step, allocProgram, allocState, alloc, hz, hl, ht, v, i, to,
        Arg.eval, Ovf.eval, evalArgs, takeEdge, bindParams, hc, hcarry, e2, next]
    apply Sem.Reaches.free (s' := allocState mem context e2 4 0)
    · apply semStep_next.mpr
      simp [step, allocProgram, allocState, alloc, hz, hl, ht, v, to,
        Arg.eval, evalArgs, takeEdge, bindParams, he, e2, next, hfit]
    apply Sem.Reaches.free (s' := allocState m1 context e2 4 1)
    · apply semStep_next.mpr
      simp [step, allocProgram, allocState, alloc, hz, hl, ht, v, Procs.ctx,
        Stmt.exec, Addr.eval, Arg.eval, e2, hsctx]
    apply Sem.Reaches.free (s' := allocState m1 context e3 5 0)
    · apply semStep_next.mpr
      simp [step, allocProgram, allocState, alloc, hz, hl, ht, v, to,
        Arg.eval, evalArgs, takeEdge, bindParams, hc2, e3]
    apply Sem.Reaches.free (s' := allocState m2 context e3 5 1)
    · apply semStep_next.mpr
      simp [step, allocProgram, allocState, alloc, hz, hl, ht, cellAddr,
        Stmt.exec, Addr.eval, Arg.eval, dispWord, e3, hscell]
    apply Sem.Reaches.final
    have done : semStep (allocProgram fields tag) (allocState m2 context e3 5 1) = .done ([cell], m2) := by
      apply semStep_done.mpr
      simp [step, allocProgram, allocState, alloc, hz, hl, ht, v, evalArgs, Arg.eval, e3]
    rw [done]
    exact .done
  simpa [e1, m2, next] using Sem.Reaches.star
    (alloc_bump_prefix mem context cell limit fields tag hpos hsmall htag hhead hbump hlimit) finish


end IxCC.Rt.Rc.Procs
