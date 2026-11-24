import Aiur.Plonk.Scs
import Aiur.Tiling.Sound

/-!
# One-lane template rows are gnark gates

A lane with no fourth cell and no invocation coefficient denotes the gate
`qm·x0·x1 + q0·x0 + q1·x1 + q2·x2 + qc`. Instantiating its cells through a
wire map `wire` gives a `Gate` that holds exactly when the lane's relation
holds under `w ∘ wire`.
-/

namespace Aiur.Plonk

open Aiur.Tiling (Lane Poly Mono)

variable {F : Type} [Field F] [DecidableEq F]

def Lane.toGate (wire : Nat → Nat) (lane : Lane F) (a b c : Nat) : Gate F :=
  ⟨wire a, wire b, wire c, lane.q0, lane.q1, lane.q2, lane.qm, lane.qc⟩

theorem Lane.poly_denote_gate (idv : Nat) (lane : Lane F) {a b c : Nat}
    (h0 : lane.c0 = some a) (h1 : lane.c1 = some b) (h2 : lane.c2 = some c) (h3 : lane.c3 = none)
    (hid : lane.qid = 0) (val : Nat → F) :
    (Lane.poly idv lane).denote val =
      lane.qm * (val a * val b) + lane.q0 * val a + lane.q1 * val b + lane.q2 * val c + lane.qc := by
  simp only [Lane.poly, h0, h1, h2, h3, hid, if_true, Tiling.cellPoly, Poly.denote, List.map_append,
    List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Mono.eval,
    Mono.eval_insert]
  have hm : ((Mono.insert a [b]).map val).prod = val a * val b := by
    have := Mono.eval_insert val a [b]
    simp only [Mono.eval, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
    exact this
  simp [Mono.eval, hm]
  try ring

theorem Lane.toGate_holds_iff (wire : Nat → Nat) (w : Nat → F) (idv : Nat) (lane : Lane F) {a b c : Nat}
    (h0 : lane.c0 = some a) (h1 : lane.c1 = some b) (h2 : lane.c2 = some c) (h3 : lane.c3 = none)
    (hid : lane.qid = 0) :
    (Lane.toGate wire lane a b c).Holds w ↔ (Lane.poly idv lane).denote (w ∘ wire) = 0 := by
  rw [Lane.poly_denote_gate idv lane h0 h1 h2 h3 hid]
  simp only [Gate.Holds, Lane.toGate, Function.comp]
  constructor <;> intro h <;> linear_combination h

end Aiur.Plonk
