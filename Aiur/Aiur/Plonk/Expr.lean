import Aiur.Plonk.Template

/-!
# The wide circuit of a uniform table means the table

For a table that reads no fixed column and no selector, constraint `j` of
`Table.wideCircuit` at the cell view of row `r` is the table's constraint
value at row `r`. Hence `Template.Checked.constraints_hold` on that circuit
is `Table.Holds`.
-/

namespace Aiur.Plonk

/-- Cell atom `2c + n` on row `r`: column `c` of row `r` (`n = 0`) or of the
cyclically next row (`n = 1`). -/
def cellView {F : Type} (rows : Nat) (main : Nat → Nat → F) (r : Nat) (k : Nat) : F :=
  main (if k % 2 = 1 then (r + 1) % rows else r) (k / 2)

def Node.readsRow {F : Type} : Node F → Prop
  | .fixed .. | .first | .last | .transition => False
  | _ => True

def Table.NoFixed {F : Type} (t : Table F) : Prop :=
  ∀ (i : Nat) (n : Node F), t.nodes[i]? = some n → Node.readsRow n

theorem Table.expr_denote {F : Type} [Field F] (t : Table F) (nf : t.NoFixed)
    (main : Nat → Nat → F) (r : Nat) :
    ∀ i, (t.expr i).denote (cellView t.rows main r) = t.value main r i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rw [Table.expr, Table.value]
    cases h : t.nodes[i]? with
    | none => simp [Scalar.Circuit.ArithExpr.denote]
    | some n =>
      have hi := nf i n h
      cases n with
      | const v => simp [Scalar.Circuit.ArithExpr.denote]
      | main c n =>
          cases n <;> simp [Scalar.Circuit.ArithExpr.denote, cellView, Nat.mul_add_div]
      | fixed => exact hi.elim
      | first => exact hi.elim
      | last => exact hi.elim
      | transition => exact hi.elim
      | add a b =>
          by_cases ha : a < i <;> by_cases hb : b < i <;>
            simp [ha, hb, Scalar.Circuit.ArithExpr.denote, ih]
      | sub a b =>
          by_cases ha : a < i <;> by_cases hb : b < i <;>
            simp [ha, hb, Scalar.Circuit.ArithExpr.denote, ih]
      | mul a b =>
          by_cases ha : a < i <;> by_cases hb : b < i <;>
            simp [ha, hb, Scalar.Circuit.ArithExpr.denote, ih]
      | neg a =>
          by_cases ha : a < i <;> simp [ha, Scalar.Circuit.ArithExpr.denote, ih]

theorem Table.holds_of_wide {F : Type} [Field F] (t : Table F) (nf : t.NoFixed)
    (main : Nat → Nat → F) (r : Nat)
    (h : t.wideCircuit.Holds (cellView t.rows main r)) : t.Holds main r := by
  intro j hj
  have := h _ (List.mem_map.mpr ⟨j, hj, rfl⟩)
  rwa [Table.expr_denote t nf] at this

end Aiur.Plonk
