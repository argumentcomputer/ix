import IxCC.Rt.Rc.Gen.Proof.Pending
import IxCC.Rt.Rc.Proof.Detach
import IxCC.Rt.Rc.Proof.Recycle
import IxCC.Rt.Proof.Words
import IxCC.Lir.Proof.Run

/-! The last reference to a cell, blocks 5, 12 and 11 of the general release: the scan byte is
read; a cell with scanned fields is detached (its first child read, the parent link stored in its
place, the countdown `scan − 1` stored in its count word) with one charged back edge; a cell
without scanned fields is recycled at once onto its class's list, with one charged back edge. -/
namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open Lir
open IxCC.Rt.Proof

def releaseProgram : Program := { funcs := #[dec], main := 0 }

theorem detach_count {scan : Nat} (hpos : 0 < scan) (hsmall : scan < 256) :
    X86.Width.w64.truncate (UInt64.ofNat scan - 1) = UInt64.ofNat (scan-1) := by
  rw [truncate_w64]
  apply UInt64.toNat_inj.mp
  rw [sub_toNat_of_le]
  · simp only [UInt64.toNat_ofNat']
    change scan % 2^64 - 1 = (scan-1) % 2^64
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · rw [UInt64.toNat_ofNat']
    change 1 ≤ scan % 2^64
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

theorem scan_branch (mem : X86.Memory) (context address : Word) (env : Env) (scan : Nat)
    (hsmall : scan < 256)
    (ha : env[1]? = some address)
    (hscan : loadWord mem .w8 .zero address = some (UInt64.ofNat scan)) :
    Sem.Star (semStep releaseProgram) (releaseState mem context env 5 0) 0
      (releaseState mem context (env.insert 5 (UInt64.ofNat scan)) (if scan = 0 then 11 else 12) 0) := by
  let e1 := env.insert 5 (UInt64.ofNat scan)
  have h5 : e1[5]? = some (UInt64.ofNat scan) := by simp only [e1, Std.HashMap.getElem?_insert]; rfl
  have hz : (UInt64.ofNat scan == 0) = decide (scan = 0) := by
    by_cases hs : scan = 0
    · subst hs; rfl
    · have : UInt64.ofNat scan ≠ 0 := by
        intro he
        have := congrArg UInt64.toNat he
        rw [UInt64.toNat_ofNat'] at this
        simp at this
        omega
      simp [hs, this]
  apply Sem.Star.free (s' := releaseState mem context e1 5 1)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, cellAddr, Stmt.exec, Rhs.eval,
      Addr.eval, dispWord, ha, hscan, e1]
  apply Sem.Star.free (s' := releaseState mem context e1 (if scan = 0 then 11 else 12) 0)
  · apply semStep_next.mpr
    by_cases hs : scan = 0
    · subst hs
      simp [step, releaseProgram, releaseState, dec, v, i, to, Arg.eval, evalArgs, takeEdge,
        bindParams, h5, Cond.holds, truncate_w64]
    · have hne : UInt64.ofNat scan ≠ 0 := by
        intro he
        have := congrArg UInt64.toNat he
        rw [UInt64.toNat_ofNat'] at this
        simp at this
        omega
      simp [step, releaseProgram, releaseState, dec, v, i, to, Arg.eval, evalArgs, takeEdge,
        bindParams, h5, Cond.holds, truncate_w64, hs, hne]
  exact .refl _

theorem unique_detach (mem : X86.Memory) (context address predecessor child : Word)
    (env : Env) (scan : Nat) (hpos : 0 < scan) (hsmall : scan < 256)
    (ha : env[1]? = some address) (hp : env[2]? = some predecessor)
    (hscan : loadWord mem .w8 .zero address = some (UInt64.ofNat scan))
    (hchild : loadWord mem .w64 .zero (address+8) = some child)
    (hwlink : ∀ j < 8, mem.writable ((address+8)+UInt64.ofNat j) = true)
    (hwcount : ∀ j < 4, mem.writable ((address+4)+UInt64.ofNat j) = true) :
    Sem.Star (semStep releaseProgram) (releaseState mem context env 5 0) 1
      (releaseState (detachParent mem address predecessor scan) context
        (((detachEnv env scan child).insert 1 child).insert 2 address) 1 0) := by
  have hbranch := scan_branch mem context address env scan hsmall ha hscan
  simp only [show scan ≠ 0 by omega, ↓reduceIte] at hbranch
  let e1 := env.insert 5 (UInt64.ofNat scan)
  let e2 := e1.insert 6 child
  let e3 := detachEnv env scan child
  let m1 := mem.write .w64 (address+8) predecessor
  let m2 := detachParent mem address predecessor scan
  have ha1 : e1[1]? = some address := by
    simp only [e1, Std.HashMap.getElem?_insert]
    change env[1]? = some address
    exact ha
  have ha3 : e3[1]? = some address := by
    simp only [e3, detachEnv, Std.HashMap.getElem?_insert]
    change env[1]? = some address
    exact ha
  have hp3 : e3[2]? = some predecessor := by
    simp only [e3, detachEnv, Std.HashMap.getElem?_insert]
    change env[2]? = some predecessor
    exact hp
  have hc3 : e3[6]? = some child := by simp only [e3, detachEnv, Std.HashMap.getElem?_insert]; rfl
  have hs : X86.Width.w64.truncate (UInt64.ofNat scan-1) = UInt64.ofNat (scan-1) :=
    detach_count hpos hsmall
  have hs' : UInt64.ofNat scan-1 = UInt64.ofNat (scan-1) := by simpa using hs
  have he3 : e2.insert 7 (UInt64.ofNat scan-1) = e3 := by rw [hs']; rfl
  have hw1 := write?_ok (w := .w64) (v := predecessor) hwlink
  have hw2 : m1.write? .w32 (address+4) (UInt64.ofNat (scan-1)) = .ok m2 := by
    apply write?_ok
    intro j hj
    simpa [m1, X86.Memory.write] using hwcount j (by simpa [X86.Width.bytes] using hj)
  suffices rest : Sem.Star (semStep releaseProgram) (releaseState mem context e1 12 0) 1
      (releaseState m2 context ((e3.insert 1 child).insert 2 address) 1 0) by
    simpa using hbranch.trans rest
  apply Sem.Star.free (s' := releaseState mem context e2 12 1)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, cellAddr, Stmt.exec, Rhs.eval,
      Addr.eval, dispWord, ha1, hchild, e2, e1]
  apply Sem.Star.free (s' := releaseState mem context e3 12 2)
  · apply semStep_next.mpr
    have h5 : e2[5]? = some (UInt64.ofNat scan) := by simp only [e2, e1, Std.HashMap.getElem?_insert]; rfl
    simp [step, releaseProgram, releaseState, dec, v, i, Stmt.exec, Rhs.eval,
      Arg.eval, BinOp.eval, h5, he3]
  apply Sem.Star.free (s' := releaseState m1 context e3 12 3)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, v, cellAddr, Stmt.exec,
      Addr.eval, Arg.eval, dispWord, ha3, hp3, hw1, m1]
  apply Sem.Star.free (s' := releaseState m2 context e3 12 4)
  · apply semStep_next.mpr
    have h7 : e3[7]? = some (UInt64.ofNat (scan-1)) := by simp [e3, detachEnv]
    simp [step, releaseProgram, releaseState, dec, v, cellAddr, Stmt.exec,
      Addr.eval, Arg.eval, dispWord, ha3, h7, hw2]
  apply Sem.Star.charge (s' := releaseState m2 context ((e3.insert 1 child).insert 2 address) 1 0)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, v, to, Arg.eval, evalArgs,
      takeEdge, bindParams, hc3, ha3]
  exact .refl _

/-- A cell without scanned fields: block 11 recycles it onto its class's list and resumes the
parent chain, with one charged back edge. -/
theorem scalar_recycle (mem : X86.Memory) (context address predecessor cls oldHead : Word)
    (env : Env) (ha : env[1]? = some address) (hp : env[2]? = some predecessor)
    (hscan : loadWord mem .w8 .zero address = some 0)
    (hc : loadWord mem .w8 .zero (address+1) = some cls)
    (hh : loadWord mem .w64 .zero (freeHeadAddress context cls) = some oldHead)
    (hwa : ∀ j < 8, mem.writable (address+UInt64.ofNat j) = true)
    (hwh : ∀ j < 8, mem.writable (freeHeadAddress context cls+UInt64.ofNat j) = true) :
    Sem.Star (semStep releaseProgram) (releaseState mem context env 5 0) 1
      (releaseState (recycleParent mem context cls address oldHead) context
        ((((env.insert 5 0).insert 17 cls).insert 18 oldHead).insert 8 predecessor) 6 0) := by
  have hbranch := scan_branch mem context address env 0 (by decide) ha (by simpa using hscan)
  simp only [↓reduceIte] at hbranch
  let e0 := env.insert 5 (UInt64.ofNat 0)
  let e1 := e0.insert 17 cls
  let e2 := e1.insert 18 oldHead
  let m1 := mem.write .w64 address oldHead
  let m2 := recycleParent mem context cls address oldHead
  have ha0 : e0[1]? = some address := by
    simp only [e0, Std.HashMap.getElem?_insert]
    change env[1]? = some address
    exact ha
  have hc1 : e1[17]? = some cls := by simp only [e1, Std.HashMap.getElem?_insert]; rfl
  have hc2 : e2[17]? = some cls := by
    simp only [e2, e1, Std.HashMap.getElem?_insert]; rfl
  have ha2 : e2[1]? = some address := by
    simp only [e2, e1, e0, Std.HashMap.getElem?_insert]
    change env[1]? = some address
    exact ha
  have hp2 : e2[2]? = some predecessor := by
    simp only [e2, e1, e0, Std.HashMap.getElem?_insert]
    change env[2]? = some predecessor
    exact hp
  have hh2 : e2[18]? = some oldHead := by simp only [e2, Std.HashMap.getElem?_insert]; rfl
  have hh' : loadWord mem .w64 .zero (context+cls*8) = some oldHead := hh
  have hw1 := write?_ok (w := .w64) (v := oldHead) hwa
  have hw2 : m1.write? .w64 (context+cls*8) address = .ok m2 := by
    apply write?_ok (w := .w64)
    simpa [m1, X86.Memory.write, X86.Width.bytes, freeHeadAddress] using hwh
  have he0 : (env.insert 5 0) = e0 := rfl
  rw [he0]
  suffices rest : Sem.Star (semStep releaseProgram) (releaseState mem context e0 11 0) 1
      (releaseState m2 context (e2.insert 8 predecessor) 6 0) by
    simpa using hbranch.trans rest
  apply Sem.Star.free (s' := releaseState mem context e1 11 1)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, cellAddr, Stmt.exec, Rhs.eval,
      Addr.eval, dispWord, ha0, hc, e1]
  apply Sem.Star.free (s' := releaseState mem context e2 11 2)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, Stmt.exec, Rhs.eval,
      Addr.eval, dispWord, X86.Scale.word, hc1, hh', e2]
  apply Sem.Star.free (s' := releaseState m1 context e2 11 3)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, cellAddr, v, Stmt.exec,
      Addr.eval, Arg.eval, dispWord, ha2, hh2, hw1, m1]
  apply Sem.Star.free (s' := releaseState m2 context e2 11 4)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, v, Stmt.exec,
      Addr.eval, Arg.eval, dispWord, X86.Scale.word, ha2, hc2, hw2]
  apply Sem.Star.charge (s' := releaseState m2 context (e2.insert 8 predecessor) 6 0)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, v, to, Arg.eval, evalArgs,
      takeEdge, bindParams, hp2]
  exact .refl _

end IxCC.Rt.Rc.Gen
