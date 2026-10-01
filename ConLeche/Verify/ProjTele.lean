module

import ConLeche.Verify.InstSpine
public import ConLeche.Verify.InferLemmas
public import ConLeche.Verify.ProjSlots
/- `ConLeche.Kernel.PropWhen` seals its representation on purpose (the
`Std.HashMap` pattern, task #194): the datum's module is `public` but not
`@[expose]`d, so a `cases`-then-`rfl` proof cannot see the reduct.
`import all` restores that view HERE only. -/
import all ConLeche.Kernel.PropWhen

public section

/-!
# The dummy Π-telescope over a projection body (task #175 S1)

The projection table stores, per field, a **body**
`F_i[p⃗ ↦ bvars, f_j ↦ .proj T j (bvar 0)]` scoped at `nP + 1`, and a
`.proj` use instantiates it in one `instantiateList`
(`ProjEntry.typeAt`).  The reading (`denoteMeta`) has no clause for a
loose `bvar`, so the proof side reads the body through a syntactic
device: `projTele (nP + 1) body`, the body under `nP + 1` closed
binders of domain `Sort 0`.  Its reading opens the body at fresh
variables exactly as a stored telescope's did, and the checker's
`instantiateList` is that telescope's `instPisAt` peel along the
arguments and the subject (`instPisAt_projTele`,
`instPisAt_typeAt`) — so the tower law's typing clause keeps its
`peelPis` shape (`TowerEntryLaw`, `ConLeche/Model/Annot/EnvModelM.lean`)
with the stored type replaced by the telescope over the stored body.
The binder domains are never consumed by the peel or by the law;
they are a syntactic carrier for the reading only.
-/

namespace ConLeche

open Expr

/-- `k` closed `Sort 0` binders (bit `.never`) over `body`. -/
@[expose] def projTele : Nat → Expr → Expr
  | 0, body => body
  | k + 1, body =>
    .forallE (.sort .zero) (projTele k body) ⟨.never⟩

theorem projTele_instantiate1 :
    ∀ (k : Nat) (body a : Expr) (c : Nat),
      (projTele k body).instantiate1 a c = projTele k (body.instantiate1 a (c + k))
  | 0, body, a, c => by simp [projTele]
  | k + 1, body, a, c => by
    simp only [projTele, instantiate1]
    rw [projTele_instantiate1 k body a (c + 1),
      show c + 1 + k = c + (k + 1) from by omega]

/-- **The peel of the telescope is the instantiation spine of the
body**: `instPisAt` along `k` arguments peels the `k` dummy binders
and lands on `instSpine args (k - 1) body`. -/
theorem instPisAt_projTele :
    ∀ (args : List Expr) (body : Expr),
      Expr.instPisAt args (projTele args.length body)
        = some (List.replicate args.length (.sort .zero),
            Expr.instSpine args (args.length - 1) body)
  | [], body => by simp [projTele, Expr.instPisAt, Expr.instSpine]
  | a :: as, body => by
    simp only [List.length_cons, projTele, Expr.instPisAt, projTele_instantiate1,
      Nat.zero_add, instPisAt_projTele as, Option.map_some, List.replicate_succ,
      Nat.add_sub_cancel]
    rfl

theorem projTele_hasFvar : ∀ (k : Nat) (body : Expr),
    (projTele k body).hasFvar = body.hasFvar
  | 0, _ => rfl
  | k + 1, body => by simp [projTele, Expr.hasFvar, projTele_hasFvar k body]

theorem projTele_looseBVarsBounded : ∀ (k : Nat) (body : Expr) (c : Nat),
    (projTele k body).looseBVarsBounded c = body.looseBVarsBounded (c + k)
  | 0, _, _ => rfl
  | k + 1, body, c => by
    simp only [projTele, looseBVarsBounded, Bool.true_and,
      projTele_looseBVarsBounded k body (c + 1)]
    congr 1
    omega

theorem projTele_constsResolve : ∀ (k : Nat) (body : Expr) (env : Env),
    (projTele k body).constsResolve env = body.constsResolve env
  | 0, _, _ => rfl
  | k + 1, body, env => by
    simp [projTele, Expr.constsResolve, projTele_constsResolve k body env]

theorem projTele_instantiateLevelParams : ∀ (k : Nat) (body : Expr)
    (ks : List Name) (us : List Level),
    (projTele k body).instantiateLevelParams ks us
      = projTele k (body.instantiateLevelParams ks us)
  | 0, _, _, _ => rfl
  | k + 1, body, ks, us => by
    simp only [projTele, Expr.instantiateLevelParams,
      projTele_instantiateLevelParams k body ks us]
    rfl

/-- The telescope mentions no slot its body does not. -/
theorem Expr.NoProjAt.projTele (T : Name) (i : Nat) :
    ∀ (k : Nat) (body : Expr), Expr.NoProjAt T i body →
      Expr.NoProjAt T i (projTele k body)
  | 0, _, h => h
  | k + 1, body, h =>
    Expr.noProjAt_forallE.mpr ⟨Expr.noProjAt_sort, Expr.NoProjAt.projTele T i k body h⟩

theorem projTele_stripPis : ∀ (k : Nat) (body : Expr),
    (projTele k body).stripPis k
      = some (List.replicate k ((.sort .zero : Expr), (⟨.never⟩ : BinderMeta)), body)
  | 0, _ => rfl
  | k + 1, body => by
    simp [projTele, Expr.stripPis, projTele_stripPis k body, List.replicate_succ]

/-- **The projection's type is the telescope's peel** (task #175 S1):
`ProjEntry.typeAt`'s single `instantiateList` is `instPisAt` of the
telescope over the level-instantiated body along the subject type's
arguments and the subject. -/
theorem instPisAt_typeAt (entry : ProjEntry) (us : List Level)
    {targs : List Expr} (hlen : targs.length = entry.numParams) (pe : Expr) :
    Expr.instPisAt (targs ++ [pe])
        (projTele (entry.numParams + 1)
          (entry.body.instantiateLevelParams entry.levelParams us))
      = some (List.replicate (entry.numParams + 1) (.sort .zero),
          entry.typeAt us targs pe) := by
  rw [ProjEntry.typeAt_eq_instSpine entry us hlen pe]
  have hl : (targs ++ [pe]).length = entry.numParams + 1 := by simp [hlen]
  have := instPisAt_projTele (targs ++ [pe])
    (entry.body.instantiateLevelParams entry.levelParams us)
  rw [hl, Nat.add_sub_cancel] at this
  exact this

end ConLeche
