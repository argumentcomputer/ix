module

public import Ix.Sharing.FamilyPrototype
import all Ix.Sharing.Exact.UniformSearchLocal

@[expose] public section

/-! A proved closure-local evaluator for the offline family prototype.
Positions are prepared once per component. Each subset allocates only local
closure rows; the DAG-sized base tables remain read-only. This does not change
the family, numeric domain, trace counters, or production sharing entry.

The checks are representation checks, never a choice between families. A
failed check retains the original evaluator. The area/TBase evaluator and
hashed availability are deliberately outside this checkpoint. -/

namespace Ix.Sharing.FamilyPrototype

open Ix.Sharing.Exact

/-- Two immutable position tables with the exact hypotheses of `phiE_eq_L2`.
The proof fields are erased from native code. -/
structure LocalPositions (cx : SCtx) where
  area : Array Nat
  closure : Array Nat
  ready : LocalSearch.Ready cx area closure
  members : LocalSearch.MembersIn cx area

/-- Preparation is outside the subset-cost closure. Invalid contexts retain
the specification evaluator instead of assuming a new well-formedness premise. -/
def localPositions (cx : SCtx) : Option (LocalPositions cx) :=
  if h : localSearchOK cx = true then
    let n := cx.up.prep.dag.size
    let posA := setPositions (Array.replicate n 0) cx.area
    let posC := setPositions (Array.replicate n 0) cx.closure
    if hm : cx.members.all (fun m => (posOf posA m).isSome) = true then
      some {
        area := posA
        closure := posC
        ready := by
          obtain ⟨_, _, _, _, _, _, _, _, ha, hc⟩ := LocalSearch.localSearchOK_spec h
          obtain ⟨hsA, hsC⟩ := LocalSearch.localSearchOK_inc h
          exact ⟨h, LocalSearch.setPositions_posFn cx.area n hsA ha,
            LocalSearch.setPositions_posFn cx.closure n hsC hc⟩
        members := by
          intro m hmem
          exact Array.all_eq_true'.mp hm m (Array.contains_iff_mem.mp hmem)
      }
    else none
  else none

/-- Full-closure cost and its existing work field, using local rows when
preparation succeeds. The base context and position arrays are read-only. -/
def localPhi (cx : SCtx) (positions : Option (LocalPositions cx))
    (avail : Nat → Bool) (stored : Array Nat) : Nat × Nat :=
  match positions with
  | none => cx.phiE avail stored
  | some p => phiEL2 cx p.area p.closure avail stored

theorem localPhi_eq (cx : SCtx) (positions : Option (LocalPositions cx))
    (avail : Nat → Bool) (stored : Array Nat) :
    localPhi cx positions avail stored = cx.phiE avail stored := by
  cases positions with
  | none => rfl
  | some p => exact (LocalSearch.phiE_eq_L2 p.ready p.members avail stored).symm

/-- The original component recipe with one prepared evaluator. Every trace
field, including the mathematical evaluation count, is unchanged. -/
def componentFast (cfg : Config) (ex : Expanded) (stage : UStage)
    (width index : Nat) (members : Array Nat) : ComponentTrace :=
  let cx := componentContext ex stage members
  let positions := localPositions cx
  let eval := localPhi cx positions
  let baseline := (eval (fun _ => false) #[]).1
  let cost : Cost := fun set => ((eval set.contains set).1 : _root_.Int) - (baseline : _root_.Int)
  let m := members.size
  let exact := m ≤ cfg.experimentK
  { width, index, exact, members, areaSize := cx.area.size, closureSize := cx.closure.size,
    rows := table cfg cost members.toList,
    evaluations := if exact then 2 ^ m else m * (m + 1) / 2 + m + 1 }

/-- Compiled prototype calls prepare positions once per component. This is
equality of the whole trace, not only the selected rows or their costs. -/
@[csimp] theorem component_eq_fast : @component = @componentFast := by
  funext cfg ex stage width index members
  simp only [component, componentFast, localPhi_eq]
  rfl

end Ix.Sharing.FamilyPrototype
