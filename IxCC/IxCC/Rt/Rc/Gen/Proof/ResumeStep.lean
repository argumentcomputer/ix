import IxCC.Rt.Rc.Gen.Proof.ReleaseInvariant
import IxCC.Rt.Rc.Gen.Proof.CursorPreserve
import IxCC.Rt.Rc.Proof.ResumeStep

namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open IxCC.Rt.Proof
open Lir
open IxCC.Own IxCC.Own.Rc

/-- Concrete block 8 plus logical token transfer and countdown advancement. The child load is
derived from the cursor's scanned suffix. -/
theorem ReleaseInvariant.resume_step
    {cmax heap addresses mem external frame tail context base bump limit slots lists}
    (h : ReleaseInvariant cmax heap addresses mem external none (frame :: tail)
      context base bump limit slots lists)
    (hv : frame.visited < frame.original.ctor.nobj)
    (hlen : frame.visited < frame.original.fields.length)
    (env : Env) (ha : env[8]? = some frame.address)
    (hc : env[10]? = some (UInt64.ofNat frame.original.ctor.nobj))
    (hr : env[9]? = some (UInt64.ofNat (frame.original.ctor.nobj-frame.visited))) :
    ∃ word,
      valueWord addresses frame.original.fields[frame.visited] = some word ∧
      let scan := UInt64.ofNat frame.original.ctor.nobj
      let remaining := UInt64.ofNat (frame.original.ctor.nobj-frame.visited)
      let newMem := resumeParent mem frame.address remaining
      Sem.Star (semStep releaseProgram) (releaseState mem context env 8 0) 1
        (releaseState newMem context
          (((resumeEnv env scan remaining word).insert 1 word).insert 2 frame.address) 1 0) ∧
      PendingCursor addresses frame.before newMem frame.address (cursorHead tail)
        frame.original (frame.visited+1) ∧
      Balance heap external
        (frame.original.fields[frame.visited] ::
          cursorTokens (advanceFrame frame :: tail)) := by
  have hp := h.cursors.2.1
  have hget : frame.original.fields[frame.visited]? = some frame.original.fields[frame.visited] :=
    List.getElem?_eq_getElem hlen
  obtain ⟨word, hw, hload⟩ := hp.next_child hv hget
  have hbytes := hp.bytes
  have hwrite : ∀ j < 4, mem.writable ((frame.address+4)+UInt64.ofNat j) = true := by
    intro j hj
    rw [cell_offset4]
    exact (h.cursor_access frame (by simp) (4+j) (by omega)).2
  have hrun := resume_child mem context frame.address
    (UInt64.ofNat frame.original.ctor.nobj)
    (UInt64.ofNat (frame.original.ctor.nobj-frame.visited)) word env ha hc hr hload hwrite
  refine ⟨word, hw, hrun, hp.advance hv h.cursors.2.2.1, ?_⟩
  have hb : Balance heap external (cursorTokens (frame :: tail)) := by simpa using h.balance
  rw [cursorTokens_advance frame tail hlen] at hb
  exact hb

end IxCC.Rt.Rc.Gen
