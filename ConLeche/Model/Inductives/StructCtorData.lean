module

public import ConLeche.Model.Inductives.StructStageFormer
public section

/-!
# The constructor's stage data (task #175 W4c, P3 module 6, part 3)

`CtorData`: the constructor type's peeled reading — the binder data
`ds` (parameters then fields), whose codomain bits are zero exactly at
a squash instance, ending in the family applied to the parameter
variables — with its gradings, bounds and level dependence; derived
from the constructor's `checkConstantVal` run at the environment
holding the former (`ctorData_of`), crossed to later stages
(`CtorData.cross`).

`ctorFrames`: the field chain graded at the constructor's parameter
frame (from the field-sort runs), and the two parameter frames
identified (from the binder pins) — the semantic content the former's
real leaf and the constructor's leaf consume.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps StructParts)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## Kit -/

/-- A spine of position-indexed variables reads to the frame's own
`bvar`s. -/
theorem denoteMetaSpine_indexed {acval : Name → (Name → Nat) → AnnotTerm} {d : Nat} :
    ∀ (fvs : List Expr) (off : Nat),
      (∀ (j : Nat) (x : Expr), fvs[j]? = some x →
        ∃ ty, x = Expr.fvar (off + j) ty) →
      DenoteMetaSpine acval env φ d fvs
        ((List.range fvs.length).map fun j => AnnotTerm.bvar (d - 1 - (off + j)))
  | [], _, _ => .nil
  | x :: fvs, off, h => by
    obtain ⟨nm, ty, rfl⟩ := h 0 x rfl
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    refine .cons (by rw [denoteMeta_fvar]) ?_
    have hmap : (List.range fvs.length).map
          ((fun j => AnnotTerm.bvar (d - 1 - (off + j))) ∘ Nat.succ)
        = (List.range fvs.length).map fun j => AnnotTerm.bvar (d - 1 - (off + 1 + j)) := by
      apply List.map_congr_left
      intro j _
      show AnnotTerm.bvar (d - 1 - (off + (j + 1))) = AnnotTerm.bvar (d - 1 - (off + 1 + j))
      congr 1; omega
    rw [hmap]
    exact denoteMetaSpine_indexed fvs (off + 1) fun j y hy => by
        obtain ⟨ty', hy'⟩ := h (j + 1) y (by simpa using hy)
        exact ⟨ty', by rw [hy']; congr 1; omega⟩

/-- The parameter-variable spine of the constructor's opened body, in
the reading's spelling. -/
@[expose] def paramBvars (nP nF : Nat) : List AnnotTerm :=
  (List.range nP).map fun k => AnnotTerm.bvar (nP + nF - 1 - k)

omit [SetTheory V] in
theorem consList_range_reverse :
    ∀ (n : Nat) (ρ : Nat → V),
      consList ((List.range n).reverse.map ρ) (fun j => ρ (j + n)) = ρ := by
  intro n
  induction n with
  | zero => intro ρ; funext j; simp
  | succ n ih =>
    intro ρ
    rw [List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.map_cons, consList_cons]
    have hcons : cons (ρ n) (fun j => ρ (j + (n + 1))) = fun j => ρ (j + n) := by
      funext j
      cases j with
      | zero => rw [cons_zero, Nat.zero_add]
      | succ j => rw [cons_succ]; congr 1; omega
    rw [hcons]
    exact ih ρ

/-- The prefix and suffix of a peeled binder list, as the reversed
context's parts. -/
theorem reverse_map_take_drop (ds : List (Nat × Nat × AnnotTerm)) (nP : Nat) :
    ((ds.map (·.2.2)).reverse)
      = (((ds.drop nP).map (·.2.2)).reverse) ++ (((ds.take nP).map (·.2.2)).reverse) := by
  rw [← List.reverse_append, ← List.map_append, List.take_append_drop]

/-! ## The constructor's data -/

end ConLeche.Model
