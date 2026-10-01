module

public import ConLeche.Kernel.Inductives.StructInstallF
public import ConLeche.Verify.InstList

public section

/-!
# The one-pass telescope operations equal their sequential specs

The direct simple-structure install's hot loops run the `*F`/`*A`
variants (`Expr.instPisAtF`, `Expr.instLamsAtF`, `openPisAtFvarsF`,
`domsMatchAuxA`, `checkStructDomsAtFA`, `checkStructFieldUnivFA`, and
the threaded `structProjResid`); every lemma here identifies one of
them **unconditionally** with the sequential function the Model/Verify
layers keep seeing.  The `Go` cores accumulate the pending
substitutions and apply them in a single `instantiateList` pass per
node; `instantiateList_cons` (task #50) is exactly the step that peels
one accumulated substitution back off, and the wrappers fall back to
the sequential spec whenever the raw telescope is shorter than the
argument list, which makes the equalities unconditional.
-/

namespace ConLeche

open Expr in
theorem instPisAtFGo_sound :
    ∀ (args : List Expr) (e : Expr) (acc : List Expr)
      {r : List Expr × Expr},
      instPisAtFGo acc args e = some r →
      instPisAt args (e.instantiateList acc) = some r
  | [], e, acc, r, h => by
    simp only [instPisAtFGo, Option.some.injEq] at h
    simp only [instPisAt, ← h]
  | a :: as, .forallE dom body bi, acc, r, h => by
    simp only [instPisAtFGo, Option.map_eq_some_iff] at h
    obtain ⟨⟨ds, rest⟩, hgo, rfl⟩ := h
    have ih := instPisAtFGo_sound as body (a :: acc) hgo
    rw [instantiateList_cons] at ih
    simp only [instantiateList, instPisAt, ih, Option.map_some]

open Expr in
theorem instPisAtF_eq (args : List Expr) (e : Expr) :
    instPisAtF args e = instPisAt args e := by
  unfold instPisAtF
  match h : instPisAtFGo [] args e with
  | some r =>
    have := instPisAtFGo_sound args e [] h
    rw [instantiateList_nil] at this
    exact this.symm
  | none => rfl

open Expr in
theorem instLamsAtFGo_sound :
    ∀ (args : List Expr) (e : Expr) (acc : List Expr)
      {r : List Expr × Expr},
      instLamsAtFGo acc args e = some r →
      instLamsAt args (e.instantiateList acc) = some r
  | [], e, acc, r, h => by
    simp only [instLamsAtFGo, Option.some.injEq] at h
    simp only [instLamsAt, ← h]
  | a :: as, .lam dom body bi, acc, r, h => by
    simp only [instLamsAtFGo, Option.map_eq_some_iff] at h
    obtain ⟨⟨ds, rest⟩, hgo, rfl⟩ := h
    have ih := instLamsAtFGo_sound as body (a :: acc) hgo
    rw [instantiateList_cons] at ih
    simp only [instantiateList, instLamsAt, ih, Option.map_some]

open Expr in
theorem instLamsAtF_eq (args : List Expr) (e : Expr) :
    instLamsAtF args e = instLamsAt args e := by
  unfold instLamsAtF
  match h : instLamsAtFGo [] args e with
  | some r =>
    have := instLamsAtFGo_sound args e [] h
    rw [instantiateList_nil] at this
    exact this.symm
  | none => rfl

open Expr in
theorem openPisAtFvarsFGo_sound :
    ∀ (n : Nat) (e : Expr) (i : Nat) (acc : List Expr)
      {r : List Expr × Expr},
      openPisAtFvarsFGo acc n e i = some r →
      openPisAtFvars n (e.instantiateList acc) i = some r
  | 0, e, i, acc, r, h => by
    simp only [openPisAtFvarsFGo, Option.some.injEq] at h
    simp only [openPisAtFvars, ← h]
  | n + 1, .forallE dom body bi, i, acc, r, h => by
    simp only [openPisAtFvarsFGo] at h
    split at h
    case _ fvs e' hgo =>
      have ih := openPisAtFvarsFGo_sound n body (i + 1)
        (Expr.fvar i (dom.instantiateList acc) :: acc) hgo
      rw [instantiateList_cons] at ih
      simp only [instantiateList, openPisAtFvars, ih]
      exact h
    case _ => exact nomatch h

open Expr in
theorem openPisAtFvarsF_eq (n : Nat) (e : Expr) (i : Nat) :
    openPisAtFvarsF n e i = openPisAtFvars n e i := by
  unfold openPisAtFvarsF
  match h : openPisAtFvarsFGo [] n e i with
  | some r =>
    have := openPisAtFvarsFGo_sound n e i [] h
    rw [instantiateList_nil] at this
    exact this.symm
  | none => rfl

theorem domsMatchAuxA_eq (g : Nat → Expr → Expr)
    (bs₁ bs₂ : List (Expr × BinderMeta)) (o₁ o₂ n : Nat) :
    domsMatchAuxA g bs₁.toArray bs₂.toArray o₁ o₂ n
      = domsMatchAux g bs₁ bs₂ o₁ o₂ n := by
  simp only [domsMatchAuxA, domsMatchAux, List.getElem?_toArray]

section
variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

theorem checkStructDomsAtFA_eq (ops : CheckerOps m) (fe : FEnv)
    (off : Nat) (fvs doms : List Expr) :
    ∀ j, checkStructDomsAtFA ops fe off fvs.toArray doms.toArray j
      = checkStructDomsAtF ops fe off fvs doms j
  | 0 => rfl
  | j + 1 => by
    simp only [checkStructDomsAtFA, checkStructDomsAtF,
      List.getElem?_toArray, checkStructDomsAtFA_eq ops fe off fvs doms j]

end

open Expr in
theorem instPisAtLift_append :
    ∀ (xs ys : List Expr) (e : Expr),
      instPisAtLift (xs ++ ys) e = (instPisAtLift xs e).bind (instPisAtLift ys)
  | [], ys, e => by simp only [List.nil_append, instPisAtLift, Option.bind_some]
  | x :: xs, ys, .forallE dom body bi => by
    simp only [List.cons_append, instPisAtLift,
      instPisAtLift_append xs ys (body.instantiate1Lift x)]
  | x :: xs, ys, .bvar _ | x :: xs, ys, .fvar _ _ | x :: xs, ys, .sort _
  | x :: xs, ys, .const _ _ | x :: xs, ys, .app _ _ | x :: xs, ys, .lam _ _ _
  | x :: xs, ys, .letE _ _ _ | x :: xs, ys, .lit _
  | x :: xs, ys, .proj _ _ _ => rfl
