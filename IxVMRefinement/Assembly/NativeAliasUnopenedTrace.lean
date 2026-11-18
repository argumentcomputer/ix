import IxVMRefinement.Assembly.NativeAliasOpenTraceExamples
import IxVMRefinement.Assembly.NativeAliasTrace

/-! # The telescope walk on unopened bodies, at the relation alias

`BinderTrace` steps under a binder on the body as it stands, with its loose bound variable. The
beta step of the head trace does not lift its argument, so an argument with a loose bound
variable is captured when it is substituted beneath a binder. At the relation alias
`∀ (α : Type), Rel α` that walk builds a term whose third domain is the second binder, and it
does not relate the declared type to the telescope the circuit builds, which the opened-body
walk does (`AliasTelescopeExamples.rel_openBinderTrace`). -/

set_option linter.unusedVariables false

namespace IxVM.Refinement.Decl.AliasTelescopeExamples

open Ix.Kernel
open IxVM.Refinement.Core
open Ix.Kernel.HeadDeltaBeta (Trace Step)

/-- The term the walk on unopened bodies builds: its third domain is the second binder. -/
def relTeleUnopened : KExpr :=
  .forallE type0 (.forallE (.bvar 0) (.forallE (.bvar 0) (.sort .zero) nv) nv) nv

/-- The walk on unopened bodies builds the term whose third domain is the second binder. -/
theorem rel_unopened_trace (Rel : Key .anon) :
    BinderTrace (relEnv Rel) 3 (relFormer Rel) relTeleUnopened := by
  have h3 : BinderTrace (relEnv Rel) 0 (.sort .zero) (.sort .zero) := .done .refl
  have h2 : BinderTrace (relEnv Rel) 1 (.forallE (.bvar 0) (.sort .zero) nv)
      (.forallE (.bvar 0) (.sort .zero) nv) :=
    BinderTrace.step (E := .forallE (.bvar 0) (.sort .zero) nv) (T := .bvar 0)
      (B := .sort .zero) (R := .sort .zero) (bm := nv) .refl h3
  have h1 : BinderTrace (relEnv Rel) 2 (.app (.const Rel []) (.bvar 0))
      (.forallE (.bvar 0) (.forallE (.bvar 0) (.sort .zero) nv) nv) :=
    BinderTrace.step (E := .app (.const Rel []) (.bvar 0)) (T := .bvar 0)
      (B := .forallE (.bvar 0) (.sort .zero) nv) (R := .forallE (.bvar 0) (.sort .zero) nv)
      (bm := nv) (rel_head_trace Rel (.bvar 0)) h2
  exact BinderTrace.step (E := relFormer Rel) (T := type0)
    (B := .app (.const Rel []) (.bvar 0))
    (R := .forallE (.bvar 0) (.forallE (.bvar 0) (.sort .zero) nv) nv) (bm := nv) .refl h1

/-- **The walk on unopened bodies does not relate the declared type to the circuit's
telescope.** -/
theorem rel_unopened_trace_false (Rel : Key .anon) :
    ¬ BinderTrace (relEnv Rel) 3 (relFormer Rel) relTele := by
  intro h
  have hpre : PrefixEq 3 relTele relTeleUnopened :=
    h.prefixEq (fun _ _ hf => hf) (rel_unopened_trace Rel)
  have hdom : (Expr.bvar 1 : KExpr) = Expr.bvar 0 := hpre.2.2.2.2.1
  exact absurd (Expr.bvar.inj hdom) (by decide)

end IxVM.Refinement.Decl.AliasTelescopeExamples
