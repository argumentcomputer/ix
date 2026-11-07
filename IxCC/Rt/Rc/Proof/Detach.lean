import IxCC.Rt.Rc.Proof.Pending
import IxCC.Rt.Rc.Procs
import IxCC.Rt.Proof.Words
import IxCC.Lir.Proof.Run

/-! Actual unique-parent block5, including its charged backedge. The theorem
records one target charge; it does not pretend that Own's release stutter is
free in the target. Inputs are concrete register/load/permission facts. -/
namespace IxCC.Rt.Rc.Procs
open Lir
open IxCC.Rt.Proof

def releaseProgram : Program := { funcs := #[dec], main := 0 }
def releaseState (mem : X86.Memory) (context : Word) (env : Env) (label pos : Nat) : State :=
  { mem, ctx := context, stack := [{ fn := 0, label, pos, env }] }

theorem detach_count {fields : Nat} (hpos : 0 < fields) (hsmall : fields < 32) :
    X86.Width.w64.truncate (UInt64.ofNat fields - 1) = UInt64.ofNat (fields-1) := by
  rw [truncate_w64]
  apply UInt64.toNat_inj.mp
  rw [sub_toNat_of_le]
  · simp only [UInt64.toNat_ofNat']
    change fields % 2^64 - 1 = (fields-1) % 2^64
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · rw [UInt64.toNat_ofNat']
    change 1 ≤ fields % 2^64
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

def detachEnv (env : Env) (fields : Nat) (child : Word) : Env :=
  ((env.insert 5 (UInt64.ofNat fields)).insert 6 child).insert 7 (UInt64.ofNat (fields-1))

theorem unique_detach (mem : X86.Memory) (context address predecessor child : Word)
    (env : Env) (fields : Nat) (hpos : 0 < fields) (hsmall : fields < 32)
    (ha : env[1]? = some address) (hp : env[2]? = some predecessor)
    (hscan : loadWord mem .w8 .zero address = some (UInt64.ofNat fields))
    (hchild : loadWord mem .w64 .zero (address+8) = some child)
    (hwlink : ∀ j < 8, mem.writable ((address+8)+UInt64.ofNat j) = true)
    (hwscan : mem.writable address = true) :
    Sem.Star (semStep releaseProgram) (releaseState mem context env 5 0) 1
      (releaseState (detachParent mem address predecessor fields) context
        (((detachEnv env fields child).insert 1 child).insert 2 address) 1 0) := by
  let e1 := env.insert 5 (UInt64.ofNat fields)
  let e2 := e1.insert 6 child
  let e3 := detachEnv env fields child
  let m1 := mem.write .w64 (address+8) predecessor
  let m2 := detachParent mem address predecessor fields
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
  have hs : X86.Width.w64.truncate (UInt64.ofNat fields-1) = UInt64.ofNat (fields-1) := detach_count hpos hsmall
  have hs' : UInt64.ofNat fields-1 = UInt64.ofNat (fields-1) := by simpa using hs
  have he3 : e2.insert 7 (UInt64.ofNat fields-1) = e3 := by rw [hs']; rfl
  have hw1 := write?_ok (w := .w64) (v := predecessor) hwlink
  have hw2 : m1.write? .w8 address (UInt64.ofNat (fields-1)) = .ok m2 := by
    apply write?_ok
    intro j hj
    have : j = 0 := by simp only [X86.Width.bytes] at hj; omega
    subst j
    simpa [m1, X86.Memory.write] using hwscan
  apply Sem.Star.free (s' := releaseState mem context e1 5 1)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, cellAddr, Stmt.exec, Rhs.eval,
      Addr.eval, dispWord, ha, hscan, e1]
  apply Sem.Star.free (s' := releaseState mem context e2 5 2)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, cellAddr, Stmt.exec, Rhs.eval,
      Addr.eval, dispWord, ha1, hchild, e2]
  apply Sem.Star.free (s' := releaseState mem context e3 5 3)
  · apply semStep_next.mpr
    have h5 : e2[5]? = some (UInt64.ofNat fields) := by simp only [e2, e1, Std.HashMap.getElem?_insert]; rfl
    simp [step, releaseProgram, releaseState, dec, v, i, Stmt.exec, Rhs.eval,
      Arg.eval, BinOp.eval, h5, he3]
  apply Sem.Star.free (s' := releaseState m1 context e3 5 4)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, v, cellAddr, Stmt.exec,
      Addr.eval, Arg.eval, dispWord, ha3, hp3, hw1, m1]
  apply Sem.Star.free (s' := releaseState m2 context e3 5 5)
  · apply semStep_next.mpr
    have h7 : e3[7]? = some (UInt64.ofNat (fields-1)) := by simp [e3, detachEnv]
    simp [step, releaseProgram, releaseState, dec, v, cellAddr, Stmt.exec,
      Addr.eval, Arg.eval, dispWord, ha3, h7, hw2]
  apply Sem.Star.charge (s' := releaseState m2 context ((e3.insert 1 child).insert 2 address) 1 0)
  · apply semStep_next.mpr
    simp [step, releaseProgram, releaseState, dec, v, to, Arg.eval, evalArgs,
      takeEdge, bindParams, hc3, ha3]
  exact .refl _


end IxCC.Rt.Rc.Procs
