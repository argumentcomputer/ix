module

public import IxC.Kernel.TypeChecker

@[expose] public section

/-!
# A reference normalizer

`nfRef mode env fuel depth e` normalizes `e` with the kernel's fueled `whnf`,
with the structure of IxVM's evaluator (`KernelEval::eval_nf` and
`eval_nf_spine`, `IxVM/IxVM/Source/KernelEval.lean`):

* reduce the head with `whnf`;
* under a `lam` or a `forallE`, normalize the domain, then the body opened
  with a fresh variable of the (unnormalized) domain, and close it again;
* along an application spine, normalize the arguments;
* under a `proj`, normalize the structure.

`fuel` bounds both `whnf` and the depth of the recursion; running out is an
error. An `eval` claim's value relation is stated with it: at some fuel, the
input's value normalizes to the output's value (`IxVM.Refinement.EvalValues`).

`eraseMeta` forgets binder and let metadata (contracts, the `PropWhen`
annotation, display data), which IxVM's structural comparison
(`KernelCheck::kexpr_struct_eq`) does not see.

Only cheap facts are proved here (`nfGo_zero`, `nfGo_of_whnf_sort`).
-/

namespace Ix.Kernel

mutual
  /-- `eval_nf`: reduce the head, then normalize under binders, or along the
  spine. `budget` bounds the recursion. -/
  def nfGo (mode : CheckMode) (env : Env md) (fuel : Nat) : Nat → Nat → Expr md → CheckM md (Expr md)
    | 0, _, _ => throw (.notImplemented "normalization budget exhausted")
    | budget + 1, depth, e => do
      match ← whnf mode env fuel depth e with
      | .lam ty body mb => do
        let ty' ← nfGo mode env fuel budget depth ty
        let body' ← nfGo mode env fuel budget (depth + 1) (body.instantiate1 (.fvar depth ty))
        pure (.lam ty' (body'.abstract1 depth) mb)
      | .forallE ty body mb => do
        let ty' ← nfGo mode env fuel budget depth ty
        let body' ← nfGo mode env fuel budget (depth + 1) (body.instantiate1 (.fvar depth ty))
        pure (.forallE ty' (body'.abstract1 depth) mb)
      | w => nfSpine mode env fuel budget depth w

  /-- `eval_nf_spine`: along an application spine normalize the arguments,
  and under a projection the structure; any other head is left as it is. -/
  def nfSpine (mode : CheckMode) (env : Env md) (fuel : Nat) : Nat → Nat → Expr md → CheckM md (Expr md)
    | 0, _, _ => throw (.notImplemented "normalization budget exhausted")
    | budget + 1, depth, .app f a => do
      pure (.app (← nfSpine mode env fuel budget depth f) (← nfGo mode env fuel budget depth a))
    | budget + 1, depth, .proj s i e => do
      pure (.proj s i (← nfGo mode env fuel budget depth e))
    | _ + 1, _, e => pure e
end

/-- **The reference normalizer**: `nfGo` on the annotated form of `e`
(`annotateCore`, which $\zeta$-reduces `letE` and populates sort-annotation
metadata for `whnf`), with `fuel` bounding `annotateCore`, `whnf` and the
recursion. -/
def nfRef (mode : CheckMode) (env : Env md) (fuel depth : Nat) (e : Expr md) : CheckM md (Expr md) := do
  nfGo mode env fuel fuel depth (← annotateCore mode env fuel depth e)

/-- **Binder and let metadata erased**: every `lam`, `forallE` and `letE`
carries the default metadata. -/
def Expr.eraseMeta : Expr md → Expr md
  | .fvar idx ty => .fvar idx ty.eraseMeta
  | .app f a => .app f.eraseMeta a.eraseMeta
  | .lam ty body _ => .lam ty.eraseMeta body.eraseMeta default
  | .forallE ty body _ => .forallE ty.eraseMeta body.eraseMeta default
  | .letE ty value body _ => .letE ty.eraseMeta value.eraseMeta body.eraseMeta default
  | .proj s i e => .proj s i e.eraseMeta
  | e => e

/-- With no budget left, normalization fails. -/
theorem nfGo_zero (mode : CheckMode) (env : Env md) (fuel depth : Nat) (e : Expr md) :
    nfGo mode env fuel 0 depth e = throw (.notImplemented "normalization budget exhausted") := by
  simp [nfGo]

/-- A term whose head normal form is a sort normalizes to that sort. -/
theorem nfGo_of_whnf_sort {mode : CheckMode} {env : Env md} {fuel budget depth : Nat} {e : Expr md} {u : Level}
    (h : whnf mode env fuel depth e = .ok (.sort u)) :
    nfGo mode env fuel (budget + 2) depth e = .ok (.sort u) := by
  simp [nfGo, nfSpine, h, bind, Except.bind, pure, Except.pure]

end Ix.Kernel
