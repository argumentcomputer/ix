module

public import ConLeche.Verify.InferLemmas

@[expose] public section

/-!
# `defEqList` / `recFireComparands` inversions (task #161, S1)

THE SEPARATION's shared base: three lemmas that were filed in
`SetR/Bridge/Iota.lean` (the R lane's `IotaStepR` discharge) but are
**model-free** — pure inversions of the checker's `defEqList` run and of
`recFireComparands`, naming no `EnvS`, no valuation and no relation of
the `Infer`/`DefEq` family.  Both lanes consume them: `Bridge/Iota.lean`
for `iota_stepR`, `Interp/Steps/IotaRows.lean` for the graded lane's
`IotaStep` (design census §3.3, edge 13).

Statements verbatim from their old home; the namespace is unchanged.
-/

namespace ConLeche.Semantics
variable {mode : CheckMode} {env : Env}

/-- The level comparand reads no arguments, in either fire branch. -/
theorem recFireComparands_fst_nil (rl : RecRule) (lps : List Name)
    (us : List Level) (cvjLps : List Name) (args : List Expr) (rP : Nat) :
    (recFireComparands rl lps us cvjLps args rP).1
      = (recFireComparands rl lps us cvjLps [] rP).1 := by
  unfold recFireComparands
  cases rl.fire <;> rfl

/-- A successful `defEqList`'s components — the form the nested pin
premise needs, since only *one* index's comparand is known to denote
(the rule hypothesises exactly that one). -/
theorem defEqListFueled_get {env : Env} {fuel d : Nat} :
    ∀ {as bs : List Expr}, defEqListFueled mode env fuel d as bs = .ok true →
      ∀ i, i < as.length →
        isDefEqCore mode env fuel d (as.getD i default) (bs.getD i default)
          = .ok true := by
  intro as
  induction as with
  | nil => intro bs h i hi; exact absurd hi (by simp)
  | cons x xs ih =>
    intro bs h i hi
    cases bs with
    | nil => simp [defEqListFueled, defEqList, pure, Except.pure] at h
    | cons y ys =>
      obtain ⟨hxy, htail⟩ := defEqList_step_inv h
      match i with
      | 0 => exact hxy
      | j + 1 => simpa using ih htail j (by simpa using hi)

/-- A successful `defEqList` relates lists of equal length. -/
theorem defEqListFueled_length {env : Env} {fuel d : Nat} :
    ∀ {as bs : List Expr}, defEqListFueled mode env fuel d as bs = .ok true →
      as.length = bs.length := by
  intro as
  induction as with
  | nil =>
    intro bs h
    cases bs with
    | nil => rfl
    | cons _ _ => simp [defEqListFueled, defEqList, pure, Except.pure] at h
  | cons x xs ih =>
    intro bs h
    cases bs with
    | nil => simp [defEqListFueled, defEqList, pure, Except.pure] at h
    | cons y ys => simpa using ih (defEqList_step_inv h).2


end ConLeche.Semantics
