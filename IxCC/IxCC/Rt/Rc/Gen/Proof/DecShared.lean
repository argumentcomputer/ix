import IxCC.Rt.Rc.Gen.Proof.CountOps
import IxCC.Rt.Rc.Proof.Memory
import IxCC.Lir.Proof.Run

/-! Full shared-decrement entry/exit execution. The unique-parent continuation
has a different invariant and is intentionally not claimed by this theorem. -/
namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open IxCC.Rt.Proof
open Lir

def decProgram : Program := { funcs := #[dec], main := 0 }
def decState (mem : X86.Memory) (context : Word) (env : Env) (label pos : Nat := 0) : State :=
  { mem, ctx := context, stack := [{ fn := 0, label, pos, env }] }
def decEnv (address : Word) : Env := ({} : Env).insert 0 address
def decDispatchEnv (address : Word) : Env := ((decEnv address).insert 1 address).insert 2 0

theorem dec_initial (mem : X86.Memory) (context address : Word) :
    State.initial decProgram [address] mem context =
      some (decState mem context (decEnv address) 0 0) := by
  simp [State.initial, enter, decProgram, dec, bindParams, decState, decEnv]

theorem dec_entry (mem : X86.Memory) (context address : Word) :
    step decProgram (decState mem context (decEnv address) 0 0) =
      .next (decState mem context (decDispatchEnv address) 1 0) false := by
  simp [step, decProgram, decState, decEnv, decDispatchEnv, dec, v, i, to,
    Arg.eval, evalArgs, takeEdge, bindParams]

theorem dec_done (mem : X86.Memory) (context : Word) (env : Env) (clock : Nat)
    (hzero : env[8]? = some 0) :
    Sem.Reaches (semStep decProgram) (decState mem context env 6 0) clock (.ok ([], mem)) := by
  apply Sem.Reaches.free (s' := decState mem context env 10 0)
  · apply semStep_next.mpr
    simp [step, decProgram, decState, dec, v, i, to, Arg.eval, evalArgs,
      takeEdge, bindParams, hzero, Cond.holds]
  · apply Sem.Reaches.final
    have last : semStep decProgram (decState mem context env 10 0) = .done ([], mem) := by
      apply semStep_done.mpr
      simp [step, decProgram, decState, dec, evalArgs]
    rw [last]
    exact .done

theorem dec_dynamic_prefix (mem : X86.Memory) (context address count : Word)
    (hp : Cond.holds .tnz .w64 address 1 = false)
    (hr : loadWord mem .w32 .zero (address + 4) = some count)
    (hs : Cond.holds .slt .w32 count 0 = false) :
    Sem.Star (semStep decProgram) (decState mem context (decEnv address) 0 0) 0
      (decState mem context ((decDispatchEnv address).insert 3 count) 3 0) := by
  have haddress : (decDispatchEnv address)[1]? = some address := by
    simp only [decDispatchEnv, Std.HashMap.getElem?_insert]
    rfl
  apply Sem.Star.free (semStep_next.mpr (dec_entry mem context address))
  apply Sem.Star.free (s' := decState mem context (decDispatchEnv address) 2 0)
  · apply semStep_next.mpr
    simp [step, decProgram, decState, dec, v, i, to, Arg.eval, evalArgs,
      takeEdge, bindParams, haddress, hp]
  apply Sem.Star.free (s' := decState mem context ((decDispatchEnv address).insert 3 count) 2 1)
  · apply semStep_next.mpr
    simp [step, decProgram, decState, dec, v, cellAddr,
      Stmt.exec, Rhs.eval, Addr.eval, dispWord, haddress, hr]
  apply Sem.Star.free (s' := decState mem context ((decDispatchEnv address).insert 3 count) 3 0)
  · apply semStep_next.mpr
    simp [step, decProgram, decState, dec, v, i, to, Arg.eval, evalArgs, takeEdge, bindParams, hs]
  exact .refl _

theorem dec_shared (mem : X86.Memory) (context address count : Word) (clock : Nat)
    (hp : Cond.holds .tnz .w64 address 1 = false)
    (hr : loadWord mem .w32 .zero (address + 4) = some count)
    (hs : Cond.holds .slt .w32 count 0 = false)
    (hn : Cond.holds .eq .w32 count 0 = false)
    (hw : ∀ j < 4, mem.writable ((address + 4) + UInt64.ofNat j) = true) :
    eval decProgram clock [address] mem context =
      .ok ([], storeCount mem address (X86.Width.w32.truncate (count-1))) := by
  let e1 := (decDispatchEnv address).insert 3 count
  let next := X86.Width.w32.truncate (count-1)
  let e2 := e1.insert 4 next
  let m2 := storeCount mem address next
  have hparent : e2[2]? = some 0 := by
    simp only [e2, e1, decDispatchEnv, Std.HashMap.getElem?_insert]
    rfl
  apply (runs_eval (dec_initial mem context address)).eq
  have finish : Sem.Reaches (semStep decProgram) (decState mem context e1 3 0) clock (.ok ([], m2)) := by
    apply Sem.Reaches.free (s' := decState mem context e1 4 0)
    · apply semStep_next.mpr
      simp [step, decProgram, decState, e1, dec, v, i, to, Arg.eval, evalArgs, takeEdge, bindParams, hn]
    apply Sem.Reaches.free (s' := decState mem context e2 4 1)
    · apply semStep_next.mpr
      exact dec_sub_step mem context count e1 (by simp [e1])
    apply Sem.Reaches.free (s' := decState m2 context e2 4 2)
    · apply semStep_next.mpr
      exact dec_store_step mem context address next e2
        (by simp only [e2, e1, decDispatchEnv, Std.HashMap.getElem?_insert]; rfl)
        (by simp [e2]) hw
    apply Sem.Reaches.free (s' := decState m2 context (e2.insert 8 0) 6 0)
    · apply semStep_next.mpr
      simp [step, decProgram, decState, dec, v, to, evalArgs, Arg.eval, takeEdge, bindParams, hparent]
    exact dec_done m2 context (e2.insert 8 0) clock (by simp)
  simpa [e1, m2, next] using Sem.Reaches.star (dec_dynamic_prefix mem context address count hp hr hs) finish

theorem dec_shared_frame (mem : X86.Memory) (context address count : Word) (clock : Nat)
    (hp : Cond.holds .tnz .w64 address 1 = false)
    (hr : loadWord mem .w32 .zero (address + 4) = some count)
    (hs : Cond.holds .slt .w32 count 0 = false)
    (hn : Cond.holds .eq .w32 count 0 = false)
    (hw : ∀ j < 4, mem.writable ((address + 4) + UInt64.ofNat j) = true)
    (hfit : address.toNat + 8 ≤ 2^64) :
    ∃ result, eval decProgram clock [address] mem context = .ok ([], result) ∧
      CountFrame mem result address := by
  exact ⟨_, dec_shared mem context address count clock hp hr hs hn hw,
    storeCount_frame mem address _ hfit⟩



end IxCC.Rt.Rc.Gen
