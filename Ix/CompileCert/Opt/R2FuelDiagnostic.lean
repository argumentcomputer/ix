import Ix.CompileCert.Opt.Rewrite
import Ix.CompileCert.Canon.Cache
import Std.Data.HashMap.Lemmas

/-!
UNCOMPILED source diagnostic. No runtime, theorem endpoint or cache policy is changed.
The runtime equations are exact ce9/efe Translate; they are unchanged at f7.

A warm state is reached by an actual call from entirely empty caches. Reusing
its name-only expansion at smaller fuel can disagree with the existing pure
core's error. No distinct keys, hash collision or externally poisoned cache
are involved. This does not assert that the callback comes from an accepted
compiler source, nor refute the final source-domain conversion theorem.
-/

namespace Ix.CompileCert.Opt.ReachableFuel

open Ix (Name Expr)
open Ix.Compile.Pass (Expansion RwState RwM)

private theorem run_bind {α β : Type} (m : RwM α) (k : α → RwM β) (s : RwState) :
    (m >>= k).run s = (m.run s >>= fun p => (k p.1).run p.2) := rfl

private theorem run_pure {α : Type} (a : α) (s : RwState) :
    (pure a : RwM α).run s = .ok (a, s) := rfl

private theorem run_get (s : RwState) :
    (get : RwM RwState).run s = .ok (s, s) := rfl

private theorem run_modify (f : RwState → RwState) (s : RwState) :
    (modify f : RwM PUnit).run s = .ok (PUnit.unit, f s) := rfl

private theorem run_lift {α : Type} (x : Except String α) (s : RwState) :
    (liftM x : RwM α).run s = x.map (fun a => (a, s)) := by
  cases x <;> rfl

private theorem run_throw {α : Type} (message : String) (s : RwState) :
    (throw message : RwM α).run s = .error message := rfl

def atom (literal : Lean.Literal) (address : Address) : Expr := .lit literal address

def input (literal : Lean.Literal) (address : Address) : Expansion :=
  ⟨#[], atom literal address, 0, true⟩

def ready (literal : Lean.Literal) (address : Address) : Expansion :=
  { input literal address with needsRewrite := false }

def lookup (literal : Lean.Literal) (address : Address) :
    Name → Except String (Option Expansion) := fun _ => .ok (some (input literal address))

def cold : RwState := { base := 0 }

def afterAtom (literal : Lean.Literal) (address : Address) : RwState :=
  { cold with cache := cold.cache.insert (atom literal address, false, none) (atom literal address) }

def warm (name : Name) (literal : Lean.Literal) (address : Address) : RwState :=
  { afterAtom literal address with exps := cold.exps.insert name (ready literal address) }

theorem cold_expansion_empty (name : Name) : cold.exps.get? name = none :=
  Std.HashMap.getElem?_emptyWithCapacity

theorem cold_expression_empty (literal : Lean.Literal) (address : Address) :
    cold.cache.get? (atom literal address, false, none) = none :=
  Std.HashMap.getElem?_emptyWithCapacity

theorem warm_exact_entry (name : Name) (literal : Lean.Literal) (address : Address) :
    (warm name literal address).exps.get? name = some (ready literal address) :=
  Std.HashMap.getElem?_insert_self

/-- This equality retains the full returned state, not only the value. -/
theorem cold_atom_run (literal : Lean.Literal) (address : Address) :
    (Ix.Compile.Pass.rw (lookup literal address) 1 false (atom literal address)).run cold =
      .ok (atom literal address, afterAtom literal address) := by
  rw [Ix.Compile.Pass.rw.eq_def]
  simp [run_bind, run_pure, run_get, run_modify, atom, cold, afterAtom,
    Std.HashMap.get?_eq_getElem?]

/-- The displayed warm state is produced by the actual runtime from cold. -/
theorem cold_high_run (name : Name) (literal : Lean.Literal) (address : Address) :
    (Ix.Compile.Pass.expansionOf (lookup literal address) 2 name).run cold =
      .ok (some (ready literal address), warm name literal address) := by
  rw [Ix.Compile.Pass.expansionOf.eq_def]
  simp only [run_bind, run_get, run_lift, run_modify, run_pure,
    cold_expansion_empty, lookup, input, ↓reduceIte,
    Except.map, Except.bind]
  change ((Ix.Compile.Pass.rw (lookup literal address) 1 false
    (atom literal address)).run cold >>= fun p =>
      .ok (some { input literal address with value := p.1, needsRewrite := false },
        { p.2 with site := none, exps := p.2.exps.insert name
          { input literal address with value := p.1, needsRewrite := false } })) = _
  rw [cold_atom_run]
  rfl

theorem warm_low_run (name : Name) (literal : Lean.Literal) (address : Address) :
    (Ix.Compile.Pass.expansionOf (lookup literal address) 1 name).run
      (warm name literal address) =
      .ok (some (ready literal address), warm name literal address) := by
  rw [Ix.Compile.Pass.expansionOf.eq_def]
  simp only [run_bind, run_get, warm_exact_entry, run_pure, Except.bind]

theorem pure_low_error (name : Name) (literal : Lean.Literal) (address : Address) :
    expansionOfP (lookup literal address) cold.opt? false 1 name =
      .error "Pass 3 rewrite: recursion bound exhausted" := by
  rw [expansionOfP.eq_def]
  simp [lookup, input, rwP.eq_def]

/-- Cold low fuel still fails: the disagreement is introduced by a reachable hit. -/
theorem cold_low_error (name : Name) (literal : Lean.Literal) (address : Address) :
    (Ix.Compile.Pass.expansionOf (lookup literal address) 1 name).run cold =
      .error "Pass 3 rewrite: recursion bound exhausted" := by
  rw [Ix.Compile.Pass.expansionOf.eq_def]
  simp [run_bind, run_get, run_lift, run_modify, run_pure, run_throw,
    cold_expansion_empty, lookup, input, cold, Ix.Compile.Pass.rw.eq_def]

/-- Sufficient-fuel positive neighbour, with exactly the same callback and input. -/
theorem pure_high_result (name : Name) (literal : Lean.Literal) (address : Address) :
    expansionOfP (lookup literal address) cold.opt? false 2 name =
      .ok (some (ready literal address)) := by
  rw [expansionOfP.eq_def]
  simp [lookup, input, ready, atom, rwP.eq_def]

theorem reachable_smaller_fuel_disagrees (name : Name) (literal : Lean.Literal)
    (address : Address) :
    ∃ reached : RwState,
      (Ix.Compile.Pass.expansionOf (lookup literal address) 2 name).run cold =
        .ok (some (ready literal address), reached) ∧
      ((Ix.Compile.Pass.expansionOf (lookup literal address) 1 name).run reached).map Prod.fst ≠
        expansionOfP (lookup literal address) cold.opt? false 1 name := by
  refine ⟨warm name literal address, cold_high_run name literal address, ?_⟩
  rw [warm_low_run, pure_low_error]
  intro equality
  cases equality

/-- The immediate same-fuel invariant needed to justify a positive expansion
cache hit against the existing pure core. This is a diagnostic predicate,
not a new premise added to any public compiler theorem. -/
def ReplaysAt (expansion? : Name → Except String (Option Expansion))
    (hook : Hook) (inPlace : Bool) (fuel : Nat)
    (memo : Std.HashMap Name Expansion) : Prop :=
  ∀ name value, memo.get? name = some value →
    expansionOfP expansion? hook inPlace fuel name = .ok (some value)

theorem cold_replaysAt (expansion? : Name → Except String (Option Expansion))
    (hook : Hook) (inPlace : Bool) (fuel : Nat) :
    ReplaysAt expansion? hook inPlace fuel cold.exps := by
  intro name value found
  rw [cold_expansion_empty] at found
  cases found

/-- Actual cold reachability alone cannot establish that invariant at every
later, smaller fuel. The failure is derived, not assumed as a caller premise. -/
theorem warm_not_replaysAt (name : Name) (literal : Lean.Literal) (address : Address) :
    ¬ ReplaysAt (lookup literal address) cold.opt? false 1
      (warm name literal address).exps := by
  intro valid
  have replay := valid name (ready literal address) (warm_exact_entry name literal address)
  rw [pure_low_error] at replay
  cases replay

end Ix.CompileCert.Opt.ReachableFuel
