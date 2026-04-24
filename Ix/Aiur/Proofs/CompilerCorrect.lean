module
public import Ix.Aiur.Proofs.CompilerPreservation
public import Ix.Aiur.Proofs.CompilerProgress
public import Ix.Aiur.Proofs.CheckSound
public import Ix.Aiur.Semantics.WellFormed

/-!
`compile_correct`, the final theorem.

Combines `compile_progress` (progress) and `compile_preservation`
(preservation) into the headline theorem of the verified compiler.
-/

public section

namespace Aiur

open Source

/-- **The verified-compiler theorem.**

For every well-formed source `t`:
(a) *Progress* — compilation succeeds.
(b) *Preservation* — the bytecode output of every **entry point** is
    semantically equivalent to the source under `InterpResultEq`, composed
    through source → simplify → concretize → lower → dedup → bytecode.

The preservation clause is restricted to entry functions (`f.entry = true`).
By `Source.Function.notPolyEntry`, entries are forced to be monomorphic
(`params = []`). Together with the transitive call graph from entries —
which `concretize` fully concretizes — this gives a per-entry monomorphism
property without requiring a global `FullyMonomorphic t` `WellFormed` field.

`InterpResultEq` is asymmetric: source-ok → bytecode-ok-and-equivalent;
bytecode permitted to over-succeed where source errors. -/
theorem Toplevel.compile_correct
    (t : Source.Toplevel) (hwf : WellFormed t) :
    -- (a) Progress: compilation succeeds.
    (∃ ct decls, t.mkDecls = .ok decls ∧ t.compile = .ok ct)
    ∧
    -- (b) Preservation, scoped to entry functions.
    (∀ ct decls,
      t.mkDecls = .ok decls →
      t.compile = .ok ct →
      ∀ (name : Lean.Name) (funIdx : Bytecode.FunIdx)
        (_hname : ct.getFuncIdx name = some funIdx)
        {f : Source.Function}
        (_hsrc : decls.getByKey (Global.mk name) = some (.function f))
        -- Restrict to entry points. By `Source.Function.notPolyEntry`,
        -- this forces `f.params = []` (no polymorphic public entries).
        (_hentry : f.entry = true)
        (args : List Value) (io₀ : IOBuffer) (fuel : Nat) (retTyp : Typ)
        -- Args contain no first-class function values. Caller-known property
        -- of the call site; no internal repository invariant constrains it.
        (_hargsFnFree : ∀ v ∈ args, Value.FnFree v),
      InterpResultEq decls ct.globalFuncIdx retTyp
        (Source.Eval.runFunction decls (Global.mk name) args io₀ fuel)
        (Bytecode.Eval.runFunction ct.bytecode funIdx
          (Flatten.args decls ct.globalFuncIdx args) io₀ fuel)) := by
  -- BLOCKED-FullyMono: `compile_progress` and `compile_preservation`
  -- internally invoke `_under_fullymono` lemma chains that take a global
  -- `FullyMonomorphic t` hypothesis. With `fullyMonomorphic` dropped from
  -- `WellFormed` (refactor 2026-04-28), this hypothesis is no longer
  -- supplied by `hwf`. For polymorphic source code (e.g. IxVM `List<T>`),
  -- it is structurally FALSE — but per `Source.Function.notPolyEntry`,
  -- entries are mono, and the transitive call graph from entries gets
  -- monomorphized by `concretize`. The CORRECT closure derives a per-entry
  -- monomorphism certificate from `concretize`'s drained-mono output (NOTES.md
  -- "Phase X2 — simulation rewrite of S3"). For now we sorry the
  -- `FullyMonomorphic t` witness explicitly, marking it as the single
  -- temporary bottleneck. Composition through `compile_progress` and
  -- `compile_preservation` is real.
  have hFullyMono : FullyMonomorphic t := by sorry
  refine ⟨?_, ?_⟩
  · -- (a) Progress.
    exact Toplevel.compile_progress t hwf hFullyMono
  · -- (b) Preservation, scoped to entry functions.
    intros ct decls hdecls hct name funIdx hname f hsrc hentry args io₀ fuel retTyp
                hargsFnFree
    -- Derive `f.params = []` from `_hentry + notPolyEntry` (no FullyMono needed
    -- for this specific entry).
    have _hparams_empty : f.params = [] := by
      rcases f.notPolyEntry with h | h
      · exact h
      · rw [h] at hentry; cases hentry
    -- Derive _hcdNameAgrees internally via concretize_nameAgrees + checkAndSimplify chain.
    have hcdNameAgrees : ∀ (concDecls : Concrete.Decls),
        t.checkAndSimplify.toOption.bind (·.concretize.toOption) = some concDecls →
        ∀ (key : Global) (g : Concrete.Function),
          (key, Concrete.Declaration.function g) ∈ concDecls.pairs.toList → key = g.name := by
      intro concDecls hcd key g hmem
      have ⟨tds, hts, hconc⟩ : ∃ tds : Typed.Decls,
          t.checkAndSimplify = .ok tds ∧ tds.concretize = .ok concDecls := by
        cases hts : t.checkAndSimplify with
        | error _ => simp [hts, Except.toOption] at hcd
        | ok tds =>
          cases hconc : tds.concretize with
          | error _ => simp [hts, hconc, Except.toOption] at hcd
          | ok cd =>
            simp [hts, hconc, Except.toOption] at hcd
            subst hcd
            exact ⟨tds, rfl, hconc⟩
      have htdna := checkAndSimplify_preserves_nameAgrees hts
      exact concretize_nameAgrees htdna hconc key g hmem
    -- Derive _hconcRetFnFree via type-soundness.
    have hconcRetFnFree : ∀ (concDecls : Concrete.Decls) v io,
        t.checkAndSimplify.toOption.bind (·.concretize.toOption) = some concDecls →
        Concrete.Eval.runFunction concDecls (Global.mk name) args io₀ fuel = .ok (v, io) →
          Value.FnFree v := by
      intro concDecls v io hcd hrun
      have ⟨tds, hts, hconc⟩ : ∃ tds : Typed.Decls,
          t.checkAndSimplify = .ok tds ∧ tds.concretize = .ok concDecls := by
        cases hts : t.checkAndSimplify with
        | error _ => simp [hts, Except.toOption] at hcd
        | ok tds =>
          cases hconc : tds.concretize with
          | error _ => simp [hts, hconc, Except.toOption] at hcd
          | ok cd =>
            simp [hts, hconc, Except.toOption] at hcd
            subst hcd
            exact ⟨tds, rfl, hconc⟩
      have hparamsEmpty : ∀ g f, tds.getByKey g = some (.function f) → f.params = [] :=
        typedDecls_params_empty_of_fullyMonomorphic hFullyMono hdecls hts
      have hFOR : Concrete.Decls.FirstOrderReturn concDecls :=
        concretize_preserves_FirstOrderReturn (hwf.firstOrderReturn _ hts) hparamsEmpty hconc
      have hunique : Typed.Decls.ConcretizeUniqueNames tds := hwf.noNameCollisions _ hts
      have htdDt : Typed.Decls.DtNameIsKey tds :=
        checkAndSimplify_preserves_dtNameIsKey hts
      have htdCtorPresent : Typed.Decls.CtorPresent tds :=
        checkAndSimplify_preserves_ctorPresent hts
      have hRefClosed : Concrete.Decls.RefClosed concDecls :=
        concretize_produces_refClosed hFullyMono hts hconc hunique htdDt htdCtorPresent
      have hTermRefsDt : Concrete.Decls.TermRefsDt concDecls :=
        concretize_preserves_TermRefsDt hwf.noTermRefsToFunctions hts hparamsEmpty hconc
      exact Concrete.Eval.runFunction_preserves_FnFree concDecls (Global.mk name)
        args io₀ fuel hFOR hRefClosed hTermRefsDt hargsFnFree v io hrun
    have hsrc' : decls.getByKey (Global.mk name) ≠ none := by
      rw [hsrc]; exact Option.some_ne_none _
    exact Toplevel.compile_preservation t ct decls hdecls hct hFullyMono
      name funIdx hname hsrc' args io₀ fuel retTyp hargsFnFree hconcRetFnFree hcdNameAgrees

end Aiur

end
