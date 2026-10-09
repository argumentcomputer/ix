import Compilatrix.Rt.Rc.Proof.ReleaseInvariant
import Compilatrix.Rt.Rc.Proof.CursorPreserve

namespace Compilatrix.Rt.Rc.Procs
open Lir
open Compilatrix.Own Compilatrix.Own.Rc

def advanceFrame (frame : CursorFrame) : CursorFrame :=
  {frame with visited := frame.visited+1}

theorem cursorTokens_advance (frame : CursorFrame) (tail : List CursorFrame)
    (hv : frame.visited < frame.original.fields.length) :
    cursorTokens (frame :: tail) =
      frame.original.fields[frame.visited] :: cursorTokens (advanceFrame frame :: tail) := by
  simp only [cursorTokens, List.map_cons, flattenPending, CursorFrame.suffix, advanceFrame]
  rw [List.drop_eq_getElem_cons hv]
  rfl

/-- Concrete block8 plus logical token transfer and cursor-byte advancement.
The child load is derived from the existing suffix representation. -/
theorem ReleaseInvariant.resume_step
    {heap addresses mem external frame tail context base bump limit slots lists}
    (h : ReleaseInvariant heap addresses mem external none (frame :: tail)
      context base bump limit slots lists)
    (hv : frame.visited < frame.original.fields.length)
    (env : Env) (ha : env[8]? = some frame.address)
    (hc : env[10]? = some (UInt64.ofNat (smallClass frame.original.fields.length)))
    (hr : env[9]? = some (UInt64.ofNat (frame.original.fields.length-frame.visited))) :
    ∃ word,
      valueWord addresses frame.original.fields[frame.visited] = some word ∧
      let cls := UInt64.ofNat (smallClass frame.original.fields.length)
      let remaining := UInt64.ofNat (frame.original.fields.length-frame.visited)
      let newMem := resumeParent mem frame.address remaining
      Sem.Star (semStep releaseProgram) (releaseState mem context env 8 0) 1
        (releaseState newMem context
          (((resumeEnv env cls remaining word).insert 1 word).insert 2 frame.address) 1 0) ∧
      PendingCursor addresses frame.before newMem frame.address (cursorHead tail)
        frame.original (frame.visited+1) ∧
      Balance heap external
        (frame.original.fields[frame.visited] :: cursorTokens (advanceFrame frame :: tail)) := by
  have hp := h.cursors.2.1
  have hget : frame.original.fields[frame.visited]? = some frame.original.fields[frame.visited] :=
    List.getElem?_eq_getElem hv
  obtain ⟨word, hw, hload⟩ := hp.next_child hget
  have hwrite : mem.writable frame.address = true := by
    have hh := (h.cursor_access frame (by simp) 0 (by simp [cellBytes]; omega)).2
    simpa using hh
  have hrun := resume_child mem context frame.address
    (UInt64.ofNat (smallClass frame.original.fields.length))
    (UInt64.ofNat (frame.original.fields.length-frame.visited)) word env ha hc hr
    (by simpa only [smallClass] using hload) hwrite
  refine ⟨word, hw, hrun, hp.advance hv h.cursors.2.2.1, ?_⟩
  have hb : Balance heap external (cursorTokens (frame :: tail)) := by simpa using h.balance
  rw [cursorTokens_advance frame tail hv] at hb
  exact hb



end Compilatrix.Rt.Rc.Procs
