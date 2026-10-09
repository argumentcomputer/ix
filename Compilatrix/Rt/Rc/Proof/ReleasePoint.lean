import Compilatrix.Rt.Rc.Proof.CutpointRank

namespace Compilatrix.Rt.Rc.Procs
open Lir
open Compilatrix.Own Compilatrix.Own.Rc

/-- All changing state at the two real loop cutpoints. Fixed addresses,
external roots, context and region bounds belong to Valid, not the rank. -/
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

def ReleasePoint.Valid (p : ReleasePoint) (addresses : AddressMap) (external : Nat → Nat)
    (context base bump limit : Word) : Prop :=
  ReleaseInvariant p.heap addresses p.mem external p.current p.frames context base bump limit p.slots p.lists ∧
  match p.current with
  | some value => ∃ word, valueWord addresses value = some word ∧
      p.env[1]? = some word ∧ p.env[2]? = some (cursorHead p.frames)
  | none => p.env[8]? = some (cursorHead p.frames)

/-- Actual finite target path plus one exact source release or administrative
stutter. This predicate states the conclusion sought from concrete case lemmas;
it is never an input to the final progress theorem. -/
def ReleasePoint.Move (addresses : AddressMap) (external : Nat → Nat)
    (context base bump limit : Word) (before after : ReleasePoint) : Prop :=
  after.Valid addresses external context base bump limit ∧
  ReleaseLess after.rank before.rank ∧
  (∃ charges, Sem.Star (semStep releaseProgram) (before.state context) charges (after.state context)) ∧
  (match before.current with
   | some value => releaseOne before.heap value (cursorTokens before.frames) =
       some (after.heap, after.current.toList ++ cursorTokens after.frames)
   | none => after.heap = before.heap ∧
       after.current.toList ++ cursorTokens after.frames = cursorTokens before.frames)

end Compilatrix.Rt.Rc.Procs
