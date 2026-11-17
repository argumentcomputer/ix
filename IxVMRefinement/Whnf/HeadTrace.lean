import IxC.Kernel.Model.HeadDeltaBeta
import IxVMRefinement.Decl.Common
import IxVMRefinement.Whnf.Delta

/-! # Operational traces retained by definition unfolding and licensed beta chains

The definition arm of the actual `red_unfold` observation produces a certified delta trace.
A telescope of licensed lambdas produces a certified beta trace. These are stronger conclusions
than their `Rules.Red` projections: consumers comparing independent head computations retain the
operational evidence needed by `HeadDeltaBeta.Trace.forall_unique` and `.sort_unique`.

This file does not claim that arbitrary `whnf` or inference observations use only these steps.
-/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics
open Ix.Kernel.HeadDeltaBeta (Certified)

/-- The definition arm of an observed unfolding retains its exact head step, at any depth.
The represented loaded definition is the one stored by the selected environment. -/
theorem red_unfold_definition_trace {c : ScopedCtx}
    (hcore : ScopedCoreFacts c) {v lvls x : SourceValue F} {h h' : Heap F}
    {calls : List (Call F)} (good : CoreGood c calls)
    (ev : ObsFn W "KernelWhnf::red_unfold" [v, lvls] h (.tuple [.field 1, x]) h' calls)
    {cv : KConstantVal} {value : KExpr} {hint : Ix.Kernel.ReducibilityHint}
    {us : List KLevel} (hci : c.ci h v (.defnInfo cv value hint))
    (hus : LvListRep h us lvls) (hf : c.env.find? cv.name = some (.defnInfo cv value hint))
    (d : Nat) :
    c.tmc h' (value.instantiateLevelParams cv.levelParams us) x ∧
      Certified c.env d (.const cv.name us) (value.instantiateLevelParams cv.levelParams us) := by
  have spec := Registry.induction c (scoped_steps c hcore) (.whnf .red_unfold)
    [v, lvls] h (.tuple [.field 1, x]) h' calls ev
  rcases spec v lvls rfl good _ us hci hus 1 x rfl NatAux.field_one_ne_zero with
    ⟨_, cv', V', hn', heq, hlen, htm⟩ | ⟨_, cv', V', heq, _, _⟩
  · cases heq
    have hd : Ix.Kernel.unfoldDefinition c.env (.const cv.name us) =
        some (value.instantiateLevelParams cv.levelParams us) := by
      simpa only [Ix.Kernel.Expr.mkAppN] using unfold_const_mkAppN [] hf hlen
    exact ⟨htm, .cons (.delta hd) (.delta hd) .refl⟩
  · cases heq

/-- The existing never-data beta telescope producer also retains an operational trace. -/
theorem beta_strip_trace {env : Ix.Kernel.Env .anon} {d : Nat} :
    ∀ (As : List KExpr) (L D : KExpr) (rest : List KExpr),
      Specs.Whnf.stripLams As.length L = some D → WhnfAux.LamsNv As.length L →
      Certified env d (Ix.Kernel.Expr.mkAppN L (As ++ rest))
        (Ix.Kernel.Expr.mkAppN (D.instantiateList As.reverse 0) rest)
  | [], L, D, rest, hs, _ => by
    have : L = D := by simpa [Specs.Whnf.stripLams] using hs
    subst this
    rw [List.reverse_nil, Ix.Kernel.Expr.instantiateList_nil]
    exact .refl
  | A :: As, L, D, rest, hs, hn => by
    cases L
    case lam T B m =>
      have hs' : Specs.Whnf.stripLams As.length B = some D := hs
      have hn' : m.pw.isNever = true ∧ WhnfAux.LamsNv As.length B := hn
      obtain ⟨hs'', hn''⟩ := WhnfAux.strip_instantiate1 As.length B D A 0 hs' hn'.2
      have hrec := beta_strip_trace (env := env) (d := d) As (B.instantiate1 A 0) _ rest hs'' hn''
      have hstep : Certified env d (.app (.lam T B m) A) (B.instantiate1 A 0) :=
        .cons .beta (.betaGate hn'.1) .refl
      refine (hstep.mkAppN (As ++ rest)).trans ?_
      rw [List.reverse_cons, Ix.Kernel.Expr.instantiateList_append_one, List.length_reverse]
      exact hrec
    all_goals simp [Specs.Whnf.stripLams] at hs

end IxVM.Refinement.Core
