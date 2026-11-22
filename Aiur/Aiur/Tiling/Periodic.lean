import Aiur.Tiling.Copy
import Aiur.Tiling.Narrow

/-!
# The periodic-shard narrow circuit (v2 layout)

One shard `s` of the v2 layout (`aiur-template-backend.md`, "v2 layout") is a
`Circuit` over `W` main cells (`L = W/4` lanes) and a fixed matrix shared by
all shards of one layout. Only two constants differ between shards: the
copy-label offset and the invocation-id offset (`s·Lₛ` and `s·Iₛ` for shard
`s` of a uniform layout).

* **Gates.** Lane `l` has `lin_l = q0·x_{4l} + q1·x_{4l+1} + q2·x_{4l+2} +
  q3·x_{4l+3} + qc` and a product coefficient `qm_l`. Span flags `M_{l,l'}`
  (`l ≤ l'`) give the `L` degree-3 constraints
  `C_l = qm_l·x_{4l}·x_{4l+1} + Σ_{l' ≥ l} M_{l,l'}·lin_{l'}`.
* **Lane messages.** `push(mk_l + mc_l·x_{4l}, [ts_l, x_{4l+1}, x_{4l+2}, x_{4l+3}])`.
* **Row message.** `push(mk + mc·x_0, [ts, x_1 + rkey + kf·idOffset, x_2, …])`.
* **Copy.** `push(mult_j, [3 + 4·(label_j + labelOffset), x_j])`.

This file gives the circuit and its per-row semantics: a span's relation
(`span_holds`), the message entries, and the separation of packed copy keys
across shards and from message buses (`copyKey_inj`, `copyKey_ne_bus`),
which lets `copy_class` run per shard. Opening one fixed matrix for several
shard circuits is a multi-stark matter and stays in the STARK trust base.
-/

namespace Aiur.Tiling.Periodic

open Aiur.Scalar.Circuit (ArithExpr Var Satisfies)

variable {F : Type}

/-! ## Fixed columns (relative to the first fixed column) -/

def lanes (W : Nat) : Nat := W / 4

def gateCol (l m : Nat) : Nat := 6 * l + m

/-- Flags of lane `l`: one per lane `l' ∈ [l, L)`. -/
def flagBlock (W l : Nat) : Nat := lanes W - l

/-- Span flags `M_{l,l'}`, `l ≤ l' < L`, in row-major triangular order. -/
def flagCol (W l l' : Nat) : Nat := 6 * lanes W + ((List.range l).map (flagBlock W)).sum + (l' - l)

def flagCount (W : Nat) : Nat := ((List.range (lanes W)).map (flagBlock W)).sum

/-- Lane message columns `ts, mk, mc` of lane `l`. -/
def laneMsgCol (W l k : Nat) : Nat := 6 * lanes W + flagCount W + 3 * l + k

/-- Row message columns `ts, mk, mc, rkey, kf`. -/
def rowMsgCol (W k : Nat) : Nat := 9 * lanes W + flagCount W + k

def labelCol (W j : Nat) : Nat := rowMsgCol W 5 + j

def multCol (W j : Nat) : Nat := rowMsgCol W 5 + W + j

def fixedWidth (W : Nat) : Nat := rowMsgCol W 5 + 2 * W

example : fixedWidth 8 = 42 := rfl

/-! ## The circuit -/

section Circuit

variable [Zero F] [One F] [NatCast F]

def fx (W k : Nat) : ArithExpr F := .var (W + k)

def cell (j : Nat) : ArithExpr F := .var j

/-- `lin_l`: the linear part of lane `l`. -/
def laneLin (W l : Nat) : ArithExpr F :=
  .add (.add (.add (.add (.mul (fx W (gateCol l 1)) (cell (4 * l)))
    (.mul (fx W (gateCol l 2)) (cell (4 * l + 1)))) (.mul (fx W (gateCol l 3)) (cell (4 * l + 2))))
    (.mul (fx W (gateCol l 4)) (cell (4 * l + 3)))) (fx W (gateCol l 5))

def flagged (W l : Nat) : List Nat → ArithExpr F
  | [] => .const 0
  | l' :: ls => .add (.mul (fx W (flagCol W l l')) (laneLin W l')) (flagged W l ls)

/-- `C_l = qm_l·x_{4l}·x_{4l+1} + Σ_{l ≤ l' < L} M_{l,l'}·lin_{l'}`. -/
def spanConstraint (W l : Nat) : ArithExpr F :=
  .add (.mul (.mul (fx W (gateCol l 0)) (cell (4 * l))) (cell (4 * l + 1)))
    (flagged W l (List.range' l (lanes W - l)))

def laneMessage (W l : Nat) : Lookup F where
  multiplicity := .add (fx W (laneMsgCol W l 1)) (.mul (fx W (laneMsgCol W l 2)) (cell (4 * l)))
  args := [fx W (laneMsgCol W l 0), cell (4 * l + 1), cell (4 * l + 2), cell (4 * l + 3)]

/-- The row message of a shard whose invocation ids start at `idOffset`. -/
def rowMessage (W idOffset : Nat) : Lookup F where
  multiplicity := .add (fx W (rowMsgCol W 1)) (.mul (fx W (rowMsgCol W 2)) (cell 0))
  args := fx W (rowMsgCol W 0) ::
    .add (.add (cell 1) (fx W (rowMsgCol W 3))) (.mul (fx W (rowMsgCol W 4)) (.const ((idOffset : Nat) : F))) ::
    (List.range (W - 2)).map fun j => cell (j + 2)

/-- The packed copy tuple of cell `j` in a shard whose labels start at `labelOffset`. -/
def copyLookup (W labelOffset j : Nat) : Lookup F where
  multiplicity := fx W (multCol W j)
  args := [.add (.const ((COPY : Nat) : F)) (.mul (.const ((4 : Nat) : F))
      (.add (fx W (labelCol W j)) (.const ((labelOffset : Nat) : F)))), cell j]

def narrowCircuit (W labelOffset idOffset : Nat) : Circuit F where
  width := W
  fixedWidth := fixedWidth W
  constraints := (List.range (lanes W)).map (spanConstraint W)
  lookups := rowMessage W idOffset :: ((List.range (lanes W)).map (laneMessage W) ++
    (List.range W).map (copyLookup W labelOffset))

end Circuit

/-! ## Per-row semantics -/

section Semantics

variable [Field F]

def lin (W l : Nat) (a : Var → F) : F :=
  a (W + gateCol l 1) * a (4 * l) + a (W + gateCol l 2) * a (4 * l + 1) +
    a (W + gateCol l 3) * a (4 * l + 2) + a (W + gateCol l 4) * a (4 * l + 3) + a (W + gateCol l 5)

theorem laneLin_denote (W l : Nat) (a : Var → F) : (laneLin W l : ArithExpr F).denote a = lin W l a := by
  simp [laneLin, lin, fx, cell, ArithExpr.denote]

theorem flagged_denote (W l : Nat) (ls : List Nat) (a : Var → F) :
    (flagged W l ls : ArithExpr F).denote a = (ls.map fun l' => a (W + flagCol W l l') * lin W l' a).sum := by
  induction ls with
  | nil => simp [flagged, ArithExpr.denote]
  | cons l' ls ih => simp [flagged, ArithExpr.denote, ih, laneLin_denote, fx]

theorem spanConstraint_denote (W l : Nat) (a : Var → F) :
    (spanConstraint W l : ArithExpr F).denote a =
      a (W + gateCol l 0) * a (4 * l) * a (4 * l + 1) +
        ((List.range' l (lanes W - l)).map fun l' => a (W + flagCol W l l') * lin W l' a).sum := by
  simp [spanConstraint, ArithExpr.denote, flagged_denote, fx, cell]

theorem range'_split (l e n : Nat) (le : l ≤ e) (en : e ≤ n) :
    List.range' l (n - l) = List.range' l (e - l) ++ List.range' e (n - e) := by
  have := (List.range'_append_1 (s := l) (m := e - l) (n := n - e)).symm
  rw [show l + (e - l) = e by omega] at this
  rw [show n - l = (e - l) + (n - e) by omega, this]

/-- **Spans.** If the flags of lane `l` select exactly the lanes `[l, e)`,
the row enforces the span relation `qm_l·x_{4l}·x_{4l+1} + Σ_{l ≤ l' < e} lin_{l'} = 0`. -/
theorem span_holds {W l e : Nat} {a : Var → F}
    (holds : Satisfies ((narrowCircuit W 0 0 : Circuit F).constraints) a)
    (hl : l < e) (he : e ≤ lanes W)
    (flags : ∀ l', l ≤ l' → l' < lanes W → a (W + flagCol W l l') = if l' < e then 1 else 0) :
    a (W + gateCol l 0) * a (4 * l) * a (4 * l + 1) +
      ((List.range' l (e - l)).map fun l' => lin W l' a).sum = 0 := by
  have h := holds (spanConstraint W l) (List.mem_map.mpr ⟨l, List.mem_range.mpr (by omega), rfl⟩)
  rw [spanConstraint_denote, range'_split l e (lanes W) hl.le he, List.map_append,
    List.sum_append] at h
  have inside : ((List.range' l (e - l)).map fun l' => a (W + flagCol W l l') * lin W l' a) =
      (List.range' l (e - l)).map fun l' => lin W l' a := by
    apply List.map_congr_left
    intro l' hl'
    obtain ⟨lo, hi⟩ : l ≤ l' ∧ l' < e := by
      rw [List.mem_range'_1] at hl'; omega
    rw [flags l' lo (by omega), if_pos hi, one_mul]
  have outside : ((List.range' e (lanes W - e)).map fun l' => a (W + flagCol W l l') * lin W l' a).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hx
    rw [List.mem_range'_1] at hl'
    rw [flags l' (by omega) (by omega), if_neg (by omega), zero_mul]
  rw [inside, outside, add_zero] at h
  exact h

/-- The constraints of a shard do not depend on its offsets. -/
theorem constraints_shard (W labelOffset idOffset : Nat) :
    (narrowCircuit W labelOffset idOffset : Circuit F).constraints =
      (narrowCircuit W 0 0 : Circuit F).constraints := rfl

theorem laneMessage_entry (W l : Nat) (a : Var → F) :
    (laneMessage W l : Lookup F).entry a =
      Finsupp.single [a (W + laneMsgCol W l 0), a (4 * l + 1), a (4 * l + 2), a (4 * l + 3)]
        (a (W + laneMsgCol W l 1) + a (W + laneMsgCol W l 2) * a (4 * l)) := by
  simp [Lookup.entry, Lookup.tuple, laneMessage, ArithExpr.denote, fx, cell]

theorem rowMessage_entry (W idOffset : Nat) (a : Var → F) :
    (rowMessage W idOffset : Lookup F).entry a =
      Finsupp.single (a (W + rowMsgCol W 0) ::
          (a 1 + a (W + rowMsgCol W 3) + a (W + rowMsgCol W 4) * ((idOffset : Nat) : F)) ::
          (List.range (W - 2)).map fun j => a (j + 2))
        (a (W + rowMsgCol W 1) + a (W + rowMsgCol W 2) * a 0) := by
  simp [Lookup.entry, Lookup.tuple, rowMessage, ArithExpr.denote, fx, cell, List.map_map,
    Function.comp_def]

/-- The packed copy key of global label `n`. -/
def copyKey (n : Nat) : Nat := COPY + 4 * n

theorem copyLookup_entry (W labelOffset j : Nat) (a : Var → F) (label : Nat)
    (hlabel : a (W + labelCol W j) = (label : F)) :
    (copyLookup W labelOffset j : Lookup F).entry a =
      Finsupp.single [((copyKey (label + labelOffset) : Nat) : F), a j] (a (W + multCol W j)) := by
  simp [Lookup.entry, Lookup.tuple, copyLookup, ArithExpr.denote, fx, cell, hlabel, copyKey]

variable [DecidableEq F]

/-- **Shard separation.** Packed copy keys of distinct global labels below the
bound differ, so with disjoint label ranges per shard a copy class lies in
one shard and `copy_class` applies to it unchanged. -/
theorem copyKey_inj {bound : Nat} (small : SmallCast F bound) {n n' : Nat}
    (hb : copyKey n < bound) (hb' : copyKey n' < bound)
    (h : ((copyKey n : Nat) : F) = (copyKey n' : Nat)) : n = n' := by
  have e := small.inj hb hb' h
  simp only [copyKey, COPY] at e
  omega

/-- Copy keys are `3 mod 4`, bus codes `tag + 4·sub` with `tag ∈ {1, 2}` are
not, so the copy bus and the message buses are disjoint below `bound`. -/
theorem copyKey_ne_code {bound : Nat} (small : SmallCast F bound) {n code : Nat}
    (hcode : code % 4 = 1 ∨ code % 4 = 2) (hb : copyKey n < bound) (hb' : code < bound) :
    ((copyKey n : Nat) : F) ≠ (code : F) := by
  intro h
  have e := small.inj hb hb' h
  simp only [copyKey, COPY] at e
  omega

end Semantics

end Aiur.Tiling.Periodic
