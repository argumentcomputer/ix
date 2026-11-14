import IxVMRefinement.Core.Specs.Subst
import IxVMRefinement.Core.Specs.Levels
import IxVMRefinement.Core.Specs.LevelOps
import IxVMRefinement.Core.Specs.Whnf
import IxVMRefinement.Core.Specs.DefEq
import IxVMRefinement.Core.Specs.Infer
import IxVMRefinement.Core.Specs.Nat
import IxVMRefinement.Core.Specs.Roles
import IxVMRefinement.Core.Specs.Callees

/-! # The spec registry, the induction hypothesis, and the harness

**The registry.** Every function of the core, and every function outside it whose answer the
core reads, has one spec (`SpecFn`), stated in its family's file under
`IxVMRefinement/Core/Specs/` and frozen there. `Fn` names them: one constructor per family,
each carrying the family's own enumeration, so `Fn.name` and `Fn.spec` reduce by `rfl` to the
function's symbol and spec (`Fn.spec (.whnf .whnf) = Specs.Whnf.whnf`).

**The induction hypothesis.** `IH c calls`: every registered spec holds of every observed
derivation with fewer calls than `calls`. A function's callees' calls are a strict part of its
own (`ObsExpr.call` adds the callee's entry), so a step lemma reads its callees' specs from `IH`
(`IH.get`).

**The harness.** `Registry.induction`: from one step per registered function, every observed
derivation of a registered function satisfies its spec. The packages prove the steps in their
own files; the induction is closed once, by listing them. A function whose spec is proved
without the induction (a loader, a level comparison, a library function) is a step that ignores
`IH`.

**How a package adds a step lemma** (in its own file; nothing here changes):

```
import IxVMRefinement.Core.Registry
namespace IxVM.Refinement.Core
open Aiur.Generic.SourceSemantics

theorem whnf_core_step (c : Ctx) (hc : CoreFacts c) {args h r h' calls}
    (ev : ObsFn W "KernelWhnf::whnf_core" args h r h' calls) (ih : IH c calls) :
    Specs.Whnf.whnf_core c args h r h' calls := by
  intro rc e types hargs good hrc d Γ htypes E hE
  subst hargs
  obtain ⟨cs, m, rfl, ev', rfl⟩ := Obs.«KernelWhnf::whnf_core».obs ev   -- the path lemma
  have := ih.get (.whnf .whnf_with_spine) (by simp) ev'                  -- a callee's spec
  …
```
-/

namespace IxVM.Refinement.Core

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics

/-- **The registered functions**, by family. -/
inductive Fn where
  | subst (f : Specs.Subst.Fn)
  | levels (f : Specs.Levels.Fn)
  | levelOps (f : Specs.LevelOps.Fn)
  | whnf (f : Specs.Whnf.Fn)
  | defEq (f : Specs.DefEq.Fn)
  | infer (f : Specs.Infer.Fn)
  | nat (f : Specs.Nat.Fn)
  | roles (f : Specs.Roles.Fn)
  | callees (f : Specs.Callees.Fn)

/-- A registered function's symbol (the name its observed derivations carry). -/
def Fn.name : Fn → String
  | .subst f => f.name
  | .levels f => f.name
  | .levelOps f => f.name
  | .whnf f => f.name
  | .defEq f => f.name
  | .infer f => f.name
  | .nat f => f.name
  | .roles f => f.name
  | .callees f => f.name

/-- A registered function's spec. -/
def Fn.spec : Fn → SpecFn
  | .subst f => f.spec
  | .levels f => f.spec
  | .levelOps f => f.spec
  | .whnf f => f.spec
  | .defEq f => f.spec
  | .infer f => f.spec
  | .nat f => f.spec
  | .roles f => f.spec
  | .callees f => f.spec

/-- **The spec of a symbol**: every registered function of that name satisfies its spec (`True`
for a symbol nothing registers). -/
def Spec (n : String) : SpecFn :=
  fun c args h r h' calls => ∀ f : Fn, f.name = n → f.spec c args h r h' calls

/-- **The induction hypothesis**: every registered spec holds of every observed derivation with
fewer calls. -/
def IH (c : Ctx) (calls : List (Call F)) : Prop :=
  ∀ (f : Fn) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F) (h' : Heap F)
    (cs : List (Call F)), cs.length < calls.length → ObsFn W f.name args h r h' cs →
      f.spec c args h r h' cs

/-- A callee's spec, from the induction hypothesis. -/
theorem IH.get {c : Ctx} {calls : List (Call F)} (ih : IH c calls) (f : Fn)
    {args : List (SourceValue F)} {h : Heap F} {r : SourceValue F} {h' : Heap F}
    {cs : List (Call F)} (hlt : cs.length < calls.length) (ev : ObsFn W f.name args h r h' cs) :
    f.spec c args h r h' cs :=
  ih f args h r h' cs hlt ev

/-- The induction hypothesis at more calls gives it at fewer. -/
theorem IH.mono {c : Ctx} {calls₁ calls₂ : List (Call F)} (ih : IH c calls₂)
    (hle : calls₁.length ≤ calls₂.length) : IH c calls₁ :=
  fun f args h r h' cs hlt ev => ih f args h r h' cs (Nat.lt_of_lt_of_le hlt hle) ev

/-- **One step per registered function**: its spec, from the induction hypothesis at its
derivation's calls. -/
def Steps (c : Ctx) : Prop :=
  ∀ (f : Fn) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F) (h' : Heap F)
    (cs : List (Call F)), ObsFn W f.name args h r h' cs → IH c cs → f.spec c args h r h' cs

/-- **The harness**: the steps give every registered spec, for every observed derivation (one
strong induction on the number of calls, `ObsFn.strong_induction`). -/
theorem Registry.induction (c : Ctx) (step : Steps c) :
    ∀ (f : Fn) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F) (h' : Heap F)
      (cs : List (Call F)), ObsFn W f.name args h r h' cs → f.spec c args h r h' cs := by
  have key := ObsFn.strong_induction (world := W)
    (fun n args h r h' cs => ∀ f : Fn, f.name = n → f.spec c args h r h' cs)
    (fun n args h r h' cs ev ihn f hf => by
      subst hf
      exact step f args h r h' cs ev
        (fun f' args' h₁ r' h₂ cs' hlt ev' => ihn _ _ _ _ _ _ hlt ev' f' rfl))
  exact fun f args h r h' cs ev => key _ _ _ _ _ _ ev f rfl

/-- **The harness, by symbol.** -/
theorem Registry.spec (c : Ctx) (step : Steps c) :
    ∀ (n : String) (args : List (SourceValue F)) (h : Heap F) (r : SourceValue F) (h' : Heap F)
      (cs : List (Call F)), ObsFn W n args h r h' cs → Spec n c args h r h' cs := by
  intro n args h r h' cs ev f hf
  subst hf
  exact Registry.induction c step f args h r h' cs ev

end IxVM.Refinement.Core
