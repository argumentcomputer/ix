import Aiur.Plonk.Sound
import Aiur.Plonk.Link

/-!
# Templates realised by emitted gates

A checked cone template is about slot valuations; the emitted constraint
system is about wire values. `Realised T wire gates` says every row of `T`
is a one-lane gate row whose gnark gate, with slot `s` read as wire
`wire s`, satisfies `gates`. Then every satisfying wire assignment `w` gives
`T.RelationsHold (w ∘ wire)` (`relationsHold_of_realised`), which is the
hypothesis of `constraint_of_cone` and `message_of_cone`.
-/

namespace Aiur.Plonk

open Aiur.Tiling (Template Lane Row Role)
open Lower (Fr)

/-- The gnark gate of a one-lane gate row through `wire`. -/
def rowGate (wire : Nat → Nat) : Row Fr → Option (Gate Fr)
  | .gate [lane] false _ =>
      match lane.c0, lane.c1, lane.c2, lane.c3 with
      | some a, some b, some c, none => if lane.qid = 0 then some (Lane.toGate wire lane a b c) else none
      | _, _, _, _ => none
  | _ => none

def Realised (T : Template Fr) (wire : Nat → Nat) (gates : Gate Fr → Prop) : Prop :=
  ∀ row ∈ T.rows, ∃ g, rowGate wire row = some g ∧ gates g

theorem relationsHold_of_realised {T : Template Fr} {wire : Nat → Nat} {gates : Gate Fr → Prop}
    (h : Realised T wire gates) {w : Nat → Fr} (hold : ∀ g, gates g → g.Holds w) :
    T.RelationsHold (w ∘ wire) := by
  intro rel hrel
  simp only [Template.relations, List.mem_flatMap] at hrel
  obtain ⟨row, hrow, hrel⟩ := hrel
  obtain ⟨g, hg, hmem⟩ := h row hrow
  unfold rowGate at hg
  split at hg
  · rename_i lane roles
    split at hg
    · rename_i a b c h0 h1 h2 h3
      split at hg
      · rename_i hid
        simp only [Option.some.injEq] at hg
        subst hg
        simp only [Row.relations, List.map_cons, List.map_nil] at hrel
        cases roles with
        | nil => simp at hrel
        | cons role rest =>
            simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at hrel
            subst hrel
            exact (Lane.toGate_holds_iff wire w T.idVar lane h0 h1 h2 h3 hid).mp (hold _ hmem)
      · exact absurd hg (by simp)
    · exact absurd hg (by simp)
  · exact absurd hg (by simp)

end Aiur.Plonk
