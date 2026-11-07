import IxCC.Rt.Rc.Proof.LoopControl
import IxCC.Rt.Rc.Proof.ResumeStep

namespace IxCC.Rt.Rc.Procs
open IxCC.Own IxCC.Own.Rc

def cutpointControl (current : Option RVal) (frames : List CursorFrame) : ReleaseControl :=
  match current with
  | some value => .current value (frames.map CursorFrame.suffix)
  | none => .advance (frames.map CursorFrame.suffix)

def cutpointRank (heap : Heap) (current : Option RVal) (frames : List CursorFrame) : ReleaseRank :=
  releaseRank heap (cutpointControl current frames)

theorem cutpoint_tokens (current : Option RVal) (frames : List CursorFrame) :
    (cutpointControl current frames).tokens = current.toList ++ cursorTokens frames := by
  cases current <;> rfl

theorem cutpoint_release_decreases {heap heap' : Heap} {value : RVal}
    {frames frames' : List CursorFrame} {current' : Option RVal}
    (h : releaseOne heap value (cursorTokens frames) =
      some (heap', current'.toList ++ cursorTokens frames')) :
    ReleaseLess (cutpointRank heap' current' frames') (cutpointRank heap (some value) frames) := by
  apply release_rank_decreases
  simpa only [cutpoint_tokens, cursorTokens] using h

theorem cutpoint_recycle_decreases (heap : Heap) (top : CursorFrame) (frames : List CursorFrame)
    (hv : top.visited = top.original.fields.length) :
    ReleaseLess (cutpointRank heap none frames) (cutpointRank heap none (top :: frames)) := by
  have hs : top.suffix = [] := by simp [CursorFrame.suffix, hv]
  simpa only [cutpointRank, cutpointControl, List.map_cons, hs] using
    recycle_rank_decreases heap (frames.map CursorFrame.suffix)

theorem cutpoint_resume_decreases (heap : Heap) (top : CursorFrame) (frames : List CursorFrame)
    (hv : top.visited < top.original.fields.length) :
    ReleaseLess (cutpointRank heap (some top.original.fields[top.visited]) (advanceFrame top :: frames))
      (cutpointRank heap none (top :: frames)) := by
  have hs : top.suffix = top.original.fields[top.visited] :: (advanceFrame top).suffix := by
    simpa only [CursorFrame.suffix, advanceFrame] using
      List.drop_eq_getElem_cons hv
  simpa only [cutpointRank, cutpointControl, List.map_cons, hs] using
    resume_rank_decreases heap top.original.fields[top.visited] (advanceFrame top).suffix
      (frames.map CursorFrame.suffix)





end IxCC.Rt.Rc.Procs
