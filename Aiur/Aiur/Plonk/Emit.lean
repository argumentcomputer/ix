import Aiur.Plonk.Realise

/-!
# Lowered gates as emitted gates

A lowered gate over references becomes a gnark gate through a wire map
`wireOf : Ref → Nat` (`LGate.inst`). `realisedB T sr gs` checks, without
reference to any wire map, that every row of the cone template `T` is a
one-lane row whose cells are the references `sr s` of some gate of `gs` with
the same coefficients. Then `T` is `Realised` by the instantiated gates for
every wire map (`realised_of_realisedB`).
-/

namespace Aiur.Plonk

open Aiur.Tiling (Template Lane Row)
open Lower (LGate Ref)

def Lower.LGate.inst {F : Type} (wireOf : Ref → Nat) (g : LGate F) : Gate F :=
  ⟨wireOf g.a, wireOf g.b, wireOf g.c, g.L, g.R, g.O, g.M, g.C⟩

section Generic

variable {F : Type} [Field F] [DecidableEq F]

/-- The lane is gate `g` with slot `s` read as reference `sr s`. -/
def laneMatches (sr : Nat → Ref) (lane : Lane F) (g : LGate F) : Bool :=
  match lane.c0, lane.c1, lane.c2, lane.c3 with
  | some a, some b, some c, none =>
      sr a == g.a && sr b == g.b && sr c == g.c && lane.q0 == g.L && lane.q1 == g.R &&
        lane.q2 == g.O && lane.qm == g.M && lane.qc == g.C && lane.qid == 0
  | _, _, _, _ => false

def rowMatches (sr : Nat → Ref) (gs : List (LGate F)) : Row F → Bool
  | .gate [lane] false _ => gs.any (laneMatches sr lane)
  | _ => false

def realisedB (T : Template F) (sr : Nat → Ref) (gs : List (LGate F)) : Bool :=
  T.rows.all (rowMatches sr gs)

theorem rowGate_of_matches {sr : Nat → Ref} {lane : Lane F} {g : LGate F} (h : laneMatches sr lane g = true)
    (wireOf : Ref → Nat) (roles : List Tiling.Role) :
    rowGate (wireOf ∘ sr) (.gate [lane] false roles) = some (g.inst wireOf) := by
  unfold laneMatches at h
  split at h
  · rename_i a b c h0 h1 h2 h3
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨ha, hb⟩, hc⟩, hL⟩, hR⟩, hO⟩, hM⟩, hC⟩, hid⟩ := h
    simp [rowGate, h0, h1, h2, h3, hid, Lane.toGate, Lower.LGate.inst, Function.comp, ha, hb, hc, hL, hR, hO, hM, hC]
  · exact absurd h (by simp)

theorem realised_of_realisedB {T : Template F} {sr : Nat → Ref} {gs : List (LGate F)}
    (h : realisedB T sr gs = true) (wireOf : Ref → Nat) :
    Realised T (wireOf ∘ sr) (· ∈ gs.map (Lower.LGate.inst wireOf)) := by
  intro row hrow
  have hm := List.all_eq_true.mp h row hrow
  unfold rowMatches at hm
  split at hm
  · rename_i lane roles
    obtain ⟨g, hg, hl⟩ := List.any_eq_true.mp hm
    exact ⟨g.inst wireOf, rowGate_of_matches hl wireOf roles, List.mem_map.mpr ⟨g, hg, rfl⟩⟩
  · exact absurd hm (by simp)

end Generic

end Aiur.Plonk
