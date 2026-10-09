import Compilatrix.Rt.Rc.Proof.Steps
import Compilatrix.Rt.Rc.Proof.CountOps
import Compilatrix.Rt.Rc.Proof.Memory
import Compilatrix.Lir.Proof.Run

namespace Compilatrix.Rt.Rc.Procs
open Lir

def incProgram : Program := { funcs := #[inc], main := 0 }
def incState (mem : X86.Memory) (context : Word) (env : Env) (label pos : Nat := 0) : State :=
  { mem, ctx := context, stack := [{ fn := 0, label, pos, env }] }
def incEnv (address : Word) : Env := ({} : Env).insert 0 address

theorem inc_initial (mem : X86.Memory) (context address : Word) :
    State.initial incProgram [address] mem context =
      some (incState mem context (incEnv address) 0 0) := by
  simp [State.initial, enter, incProgram, inc, bindParams, incState, incEnv]

theorem inc_immediate (mem : X86.Memory) (context address : Word) (clock : Nat)
    (h : Cond.holds .tnz .w64 address 1 = true) :
    eval incProgram clock [address] mem context = .ok ([], mem) := by
  apply (runs_eval (inc_initial mem context address)).eq
  apply Sem.Reaches.free (s' := incState mem context (incEnv address) 5 0)
  · apply semStep_next.mpr
    exact inc_immediate_step mem context address (incEnv address) (by simp [incEnv]) h
  · apply Sem.Reaches.final
    rw [show semStep incProgram (incState mem context (incEnv address) 5 0) = .done ([], mem) by
      apply semStep_done.mpr; exact inc_return_step mem context (incEnv address)]
    exact .done

/-- Pointer path through the header read, before distinguishing static from
dynamic. Conditions are concrete branch/load facts, not unknown simulations. -/
theorem inc_pointer_prefix (mem : X86.Memory) (context address count : Word)
    (hp : Cond.holds .tnz .w64 address 1 = false)
    (hr : loadWord mem .w32 .zero (address + 4) = some count) :
    Sem.Star (semStep incProgram) (incState mem context (incEnv address) 0 0) 0
      (incState mem context ((incEnv address).insert 1 count) 1 1) := by
  apply Sem.Star.free (s' := incState mem context (incEnv address) 1 0)
  · apply semStep_next.mpr
    simp [step, incProgram, incState, incEnv, inc, v, i, to, Arg.eval, evalArgs, takeEdge, bindParams, hp]
  · apply Sem.Star.free (s' := incState mem context ((incEnv address).insert 1 count) 1 1)
    · apply semStep_next.mpr
      simp [step, incProgram, incState, incEnv, inc, v, cellAddr,
        Stmt.exec, Rhs.eval, Addr.eval, dispWord, hr]
    · exact .refl _

theorem inc_static (mem : X86.Memory) (context address count : Word) (clock : Nat)
    (hp : Cond.holds .tnz .w64 address 1 = false)
    (hr : loadWord mem .w32 .zero (address + 4) = some count)
    (hs : Cond.holds .slt .w32 count 0 = true) :
    eval incProgram clock [address] mem context = .ok ([], mem) := by
  apply (runs_eval (inc_initial mem context address)).eq
  have pre := inc_pointer_prefix mem context address count hp hr
  have finish : Sem.Reaches (semStep incProgram)
      (incState mem context ((incEnv address).insert 1 count) 1 1) clock (.ok ([], mem)) := by
    apply Sem.Reaches.free (s' := incState mem context ((incEnv address).insert 1 count) 5 0)
    · apply semStep_next.mpr
      simp [step, incProgram, incState, inc, v, i, to, Arg.eval, evalArgs, takeEdge, bindParams, hs]
    · apply Sem.Reaches.final
      rw [show semStep incProgram (incState mem context ((incEnv address).insert 1 count) 5 0) = .done ([], mem) by
        apply semStep_done.mpr; exact inc_return_step mem context _]
      exact .done
  simpa using Sem.Reaches.star pre finish

theorem inc_dynamic_prefix (mem : X86.Memory) (context address count : Word)
    (hp : Cond.holds .tnz .w64 address 1 = false)
    (hr : loadWord mem .w32 .zero (address + 4) = some count)
    (hs : Cond.holds .slt .w32 count 0 = false) :
    Sem.Star (semStep incProgram) (incState mem context (incEnv address) 0 0) 0
      (incState mem context ((incEnv address).insert 1 count) 2 0) := by
  have branch : Sem.Star (semStep incProgram)
      (incState mem context ((incEnv address).insert 1 count) 1 1) 0
      (incState mem context ((incEnv address).insert 1 count) 2 0) := by
    apply Sem.Star.free (s' := incState mem context ((incEnv address).insert 1 count) 2 0)
    · apply semStep_next.mpr
      simp [step, incProgram, incState, inc, v, i, to, Arg.eval, evalArgs, takeEdge, bindParams, hs]
    · exact .refl _
  exact (inc_pointer_prefix mem context address count hp hr).trans branch

theorem inc_overflow (mem : X86.Memory) (context address count : Word) (clock : Nat)
    (hp : Cond.holds .tnz .w64 address 1 = false)
    (hr : loadWord mem .w32 .zero (address + 4) = some count)
    (hs : Cond.holds .slt .w32 count 0 = false)
    (hm : Cond.holds .eq .w32 count (UInt64.ofNat (maxCount-1)) = true) :
    eval incProgram clock [address] mem context = .resource .heap := by
  apply (runs_eval (inc_initial mem context address)).eq
  have finish : Sem.Reaches (semStep incProgram)
      (incState mem context ((incEnv address).insert 1 count) 2 0) clock (.resource .heap) := by
    apply Sem.Reaches.free (s' := incState mem context ((incEnv address).insert 1 count) 4 0)
    · apply semStep_next.mpr
      simp [step, incProgram, incState, inc, v, i, to, Arg.eval, evalArgs, takeEdge, bindParams, hm]
    · apply Sem.Reaches.final
      rw [show semStep incProgram (incState mem context ((incEnv address).insert 1 count) 4 0) = .fail .heap by
        apply semStep_fail.mpr; exact inc_overflow_step mem context _]
      exact .fail
  simpa using Sem.Reaches.star (inc_dynamic_prefix mem context address count hp hr hs) finish

theorem inc_dynamic (mem : X86.Memory) (context address count : Word) (clock : Nat)
    (hp : Cond.holds .tnz .w64 address 1 = false)
    (hr : loadWord mem .w32 .zero (address + 4) = some count)
    (hs : Cond.holds .slt .w32 count 0 = false)
    (hm : Cond.holds .eq .w32 count (UInt64.ofNat (maxCount-1)) = false)
    (hw : ∀ j < 4, mem.writable ((address + 4) + UInt64.ofNat j) = true) :
    eval incProgram clock [address] mem context =
      .ok ([], storeCount mem address (X86.Width.w32.truncate (count+1))) := by
  let e1 := (incEnv address).insert 1 count
  let next := X86.Width.w32.truncate (count+1)
  let e2 := e1.insert 2 next
  let m2 := storeCount mem address next
  apply (runs_eval (inc_initial mem context address)).eq
  have finish : Sem.Reaches (semStep incProgram) (incState mem context e1 2 0) clock (.ok ([], m2)) := by
    apply Sem.Reaches.free (s' := incState mem context e1 3 0)
    · apply semStep_next.mpr
      simp [step, incProgram, incState, e1, inc, v, i, to, Arg.eval, evalArgs, takeEdge, bindParams, hm]
    apply Sem.Reaches.free (s' := incState mem context e2 3 1)
    · apply semStep_next.mpr
      exact inc_add_step mem context count e1 (by simp [e1])
    apply Sem.Reaches.free (s' := incState m2 context e2 3 2)
    · apply semStep_next.mpr
      exact inc_store_step mem context address next e2
        (by simp only [e2, e1, incEnv, Std.HashMap.getElem?_insert]; rfl)
        (by simp [e2]) hw
    apply Sem.Reaches.free (s' := incState m2 context e2 5 0)
    · apply semStep_next.mpr
      simp [step, incProgram, incState, inc, to, evalArgs, takeEdge, bindParams]
    apply Sem.Reaches.final
    rw [show semStep incProgram (incState m2 context e2 5 0) = .done ([], m2) by
      apply semStep_done.mpr; exact inc_return_step m2 context e2]
    exact .done
  simpa [e1, m2, next] using Sem.Reaches.star (inc_dynamic_prefix mem context address count hp hr hs) finish

theorem inc_dynamic_frame (mem : X86.Memory) (context address count : Word) (clock : Nat)
    (hp : Cond.holds .tnz .w64 address 1 = false)
    (hr : loadWord mem .w32 .zero (address + 4) = some count)
    (hs : Cond.holds .slt .w32 count 0 = false)
    (hm : Cond.holds .eq .w32 count (UInt64.ofNat (maxCount-1)) = false)
    (hw : ∀ j < 4, mem.writable ((address + 4) + UInt64.ofNat j) = true)
    (hfit : address.toNat + 8 ≤ 2^64) :
    ∃ result, eval incProgram clock [address] mem context = .ok ([], result) ∧
      CountFrame mem result address := by
  exact ⟨_, inc_dynamic mem context address count clock hp hr hs hm hw,
    storeCount_frame mem address _ hfit⟩






end Compilatrix.Rt.Rc.Procs
