import IxCC.Rt.Rc.Proof.CutpointRank
import IxCC.Rt.Rc.Gen.Proof.ResumeStep

/-! The two cutpoints of the general release, their invariant and their moves. A move is an actual
finite target path with one source release, or an administrative stutter, possibly also dropping
scalar tokens: the scalar words of a released cell are literal tokens of the abstract release
(`Own.Rc.dropAll` consumes them without effect) that the target never reads. -/
namespace IxCC.Rt.Rc.Gen
open IxCC.Rt.Rc.Procs
open IxCC.Rt.Proof
open Lir
open IxCC.Own IxCC.Own.Rc

/-- All changing state at the two real loop cutpoints. -/
structure ReleasePoint where
  heap : Heap
  mem : X86.Memory
  current : Option RVal
  frames : List CursorFrame
  slots : List Slot
  lists : Nat → List Word
  env : Env

def ReleasePoint.state (p : ReleasePoint) (context : Word) : State :=
  releaseState p.mem context p.env (if p.current.isSome then 1 else 6) 0

def ReleasePoint.rank (p : ReleasePoint) : ReleaseRank :=
  cutpointRank p.heap p.current p.frames

def ReleasePoint.Valid (p : ReleasePoint) (cmax : Nat) (addresses : AddressMap)
    (external : Nat → Nat) (context base bump limit : Word) : Prop :=
  ReleaseInvariant cmax p.heap addresses p.mem external p.current p.frames context base bump limit
    p.slots p.lists ∧
  match p.current with
  | some value => ∃ word, valueWord addresses value = some word ∧
      p.env[1]? = some word ∧ p.env[2]? = some (cursorHead p.frames)
  | none => p.env[8]? = some (cursorHead p.frames)

/-- Actual finite target path plus one exact source release or administrative stutter, each
possibly also consuming scalar tokens. -/
def ReleasePoint.Move (cmax : Nat) (addresses : AddressMap) (external : Nat → Nat)
    (context base bump limit : Word) (before after : ReleasePoint) : Prop :=
  after.Valid cmax addresses external context base bump limit ∧
  ReleaseLess after.rank before.rank ∧
  (∃ charges, Sem.Star (semStep releaseProgram) (before.state context) charges (after.state context)) ∧
  ∃ lits, ScalarTokens lits ∧
  (match before.current with
   | some value => releaseOne before.heap value (cursorTokens before.frames) =
       some (after.heap, lits ++ after.current.toList ++ cursorTokens after.frames)
   | none => after.heap = before.heap ∧
       lits ++ after.current.toList ++ cursorTokens after.frames = cursorTokens before.frames)

/-- Popping a finished frame decreases the rank, whatever scalar tokens its suffix still holds. -/
theorem cutpoint_pop_decreases (heap : Heap) (top : CursorFrame) (tail : List CursorFrame) :
    ReleaseLess (cutpointRank heap none tail) (cutpointRank heap none (top :: tail)) := by
  have ht : (cursorTokens (top :: tail)).length = top.suffix.length + (cursorTokens tail).length := by
    simp [cursorTokens, flattenPending]
  show Prod.Lex _ _ (mass heap, (cursorTokens tail).length, 2*(tail.map CursorFrame.suffix).length+1)
    (mass heap, (cursorTokens (top :: tail)).length,
      2*((top :: tail).map CursorFrame.suffix).length+1)
  rcases Nat.eq_zero_or_pos top.suffix.length with he | hp
  · have hl : (cursorTokens (top :: tail)).length = (cursorTokens tail).length := by omega
    rw [hl]
    exact Prod.Lex.right _ (Prod.Lex.right _ (by simp))
  · exact Prod.Lex.right _ (Prod.Lex.left _ _
      (show (cursorTokens tail).length < (cursorTokens (top :: tail)).length by omega))

theorem ReleasePoint.Move.dropAll_eq {cmax addresses external context base bump limit before after}
    (h : ReleasePoint.Move cmax addresses external context base bump limit before after) :
    dropAll before.heap (before.current.toList ++ cursorTokens before.frames) =
      dropAll after.heap (after.current.toList ++ cursorTokens after.frames) := by
  obtain ⟨lits, hl, hs⟩ := h.2.2.2
  cases hc : before.current with
  | none =>
    simp only [hc] at hs
    simp only [Option.toList_none, List.nil_append]
    rw [← hs.2, hs.1, List.append_assoc, dropAll_scalars hl]
  | some value =>
    simp only [hc] at hs
    simp only [Option.toList_some, List.cons_append, List.nil_append]
    rw [dropAll, hs]
    simp only
    rw [List.append_assoc, dropAll_scalars hl]

end IxCC.Rt.Rc.Gen
