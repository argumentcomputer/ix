/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.LocalState

/-!
# Local-state preservation by general inference

Every uncached constructor and both inference-cache partitions preserve
caller locals and the allocation-counter bound, including partial failures.
Scope bodies may append fresh declarations; actual cleanup restores the
incoming context. Universe instantiation changes only the intern table, and
constant lookup uses the maintained loader-counter contract.

Recursive inference, reduction, conversion and projection remain contracts
of the mutual execution proof. These structural effects do not assert the
semantic validity of computed or cached types. The production ingress
loader must separately establish its counter contract.
-/

namespace Ix.Kernel.Consistency
namespace FramesLocalState

theorem get : FramesLocalState (get : TcM .anon (TcState .anon)) := fun _ _ => .refl _

theorem modify (f : TcState .anon → TcState .anon)
    (frame : ∀ before, LocalStateFrame before (f before)) :
    FramesLocalState (modify f : TcM .anon PUnit) := fun before _ => frame before

theorem intern (term : KExpr .anon) : FramesLocalState (TcM.intern term) :=
  runIntern (internExprM term)

theorem withInferOnly {action : TcM .anon α} (body : FramesLocalState action) :
    FramesLocalState (TcM.withInferOnly action) := by
  intro before valid
  rw [withInferOnly_eq]
  have inner := body {before with inferOnly := true}
    ⟨valid.coherent, valid.allocated, valid.loader⟩
  cases run : action {before with inferOnly := true} <;>
    rw [run] at inner <;> exact ⟨inner.counter, inner.context, inner.loader⟩

theorem ctxAddrForLbr (lbr : UInt64) : FramesLocalState (TcM.ctxAddrForLbr (m := .anon) lbr) := by
  unfold TcM.ctxAddrForLbr
  apply bind get
  intro state
  split
  · exact pure _
  · dsimp only
    split
    · exact pure _
    · apply bind (modify
        (fun later => {later with ctxAddrCache :=
          (later.ctxAddrCache.insert (state.ctxId, lbr) (TcM.ctxAddrForLbrUncached state lbr))})
        (fun _ => ⟨Nat.le_refl _, .refl _, rfl⟩))
      intro _
      exact pure _

theorem inferKey (term : KExpr .anon) : FramesLocalState (TcM.inferKey term) :=
  bind (ctxAddrForLbr term.lbr) (fun _ => pure _)

theorem cacheInferResult (inferOnly : Bool) (key : Address × Address) (type : KExpr .anon)
    (methods : Methods .anon) :
    FramesLocalState ((RecM.cacheInferResult inferOnly key type).run methods) := by
  intro before _
  simp only [ReaderT.run, cacheInferResult_eq]
  cases inferOnly <;> exact ⟨Nat.le_refl _, .refl _, rfl⟩

theorem lookupVar (index : UInt64) : FramesLocalState (TcM.lookupVar (m := .anon) index) := by
  unfold TcM.lookupVar
  apply bind get
  intro state
  dsimp only
  split
  · exact throw _
  · exact runIntern _

theorem isEagerReduce (term : KExpr .anon) : FramesLocalState (TcM.isEagerReduce term) := by
  unfold TcM.isEagerReduce
  generalize term.collectSpine = pair
  rcases pair with ⟨head, args⟩
  dsimp only
  split
  · exact pure _
  · split
    · apply bind get
      intro state
      exact pure _
    · exact pure _

theorem prims (methods : Methods .anon) : FramesLocalState ((RecM.prims (m := .anon)).run methods) := by
  unfold RecM.prims
  simp only [ReaderT.run_bind]
  exact bind get (fun _ => pure _)

theorem lazyIngressAddr (addr : Address) : FramesLocalState (TcM.lazyIngressAddr (m := .anon) addr) := by
  intro before valid
  unfold TcM.lazyIngressAddr
  cases loader : before.lazyFault with
  | none => exact .refl _
  | some fault =>
      dsimp only
      by_cases already : before.faultedAddrs.contains addr = true
      · rw [if_pos already]; exact .refl _
      · rw [if_neg already]
        have counter := valid.loader fault loader addr before.env
        cases run : fault addr before.env <;> rw [run] at counter <;>
          exact ⟨counter, .refl _, loader.symm⟩

theorem tryGetConst (id : KId .anon) : FramesLocalState (TcM.tryGetConst id) := by
  unfold TcM.tryGetConst
  apply bind get
  intro state
  cases found : state.env.get? id with
  | some constant => exact pure _
  | none =>
      apply bind get
      intro checked
      apply bind (lazyIngressAddr id.addr)
      intro _
      apply bind get
      intro loaded
      cases found : loaded.env.get? id with
      | some constant => exact pure _
      | none =>
          cases checked.lazyFault.isSome
          · exact pure _
          · exact throw _

theorem getConst (id : KId .anon) : FramesLocalState (TcM.getConst id) := by
  unfold TcM.getConst
  apply bind (tryGetConst id)
  intro result
  cases result
  · exact throw _
  · exact pure _

theorem ensureSortWhnf {methods : Methods .anon}
    (whnf : ∀ term, FramesLocalState ((RecM.whnf term).run methods)) (type : KExpr .anon) :
    FramesLocalState ((RecM.ensureSortWhnf type).run methods) := by
  unfold RecM.ensureSortWhnf
  simp only [ReaderT.run_bind]
  apply bind (whnf type)
  intro result
  cases result <;> first | exact pure _ | exact throw _

theorem ensureSortDirect {methods : Methods .anon}
    (whnf : ∀ term, FramesLocalState ((RecM.whnf term).run methods)) (type : KExpr .anon) :
    FramesLocalState ((RecM.ensureSortDirect type).run methods) := by
  cases type <;> simp only [RecM.ensureSortDirect]
  all_goals first | exact pure _ | exact ensureSortWhnf whnf _

theorem ensureForallWhnf {methods : Methods .anon}
    (whnf : ∀ term, FramesLocalState ((RecM.whnf term).run methods)) (type : KExpr .anon) :
    FramesLocalState ((RecM.ensureForallWhnf type).run methods) := by
  unfold RecM.ensureForallWhnf
  simp only [ReaderT.run_bind]
  apply bind (whnf type)
  intro result
  cases result <;> first | exact pure _ | exact throw _

theorem ensureForallDirect {methods : Methods .anon}
    (whnf : ∀ term, FramesLocalState ((RecM.whnf term).run methods)) (type : KExpr .anon) :
    FramesLocalState ((RecM.ensureForallDirect type).run methods) := by
  cases type <;> simp only [RecM.ensureForallDirect]
  all_goals first | exact pure _ | exact ensureForallWhnf whnf _

end FramesLocalState

/-- Every uncached inference branch restores caller locals under the local
state contracts of its recursive calls and lookup/projection helpers. -/
theorem inferUncached_framesLocalState
    {inferRec : KExpr .anon → RecM .anon (KExpr .anon)} {methods : Methods .anon}
    (recursive : ∀ term, FramesLocalState ((inferRec term).run methods))
    (whnf : ∀ term, FramesLocalState ((RecM.whnf term).run methods))
    (conversion : ∀ left right, FramesLocalState ((RecM.isDefEqCall left right).run methods))
    (projection : ∀ id field major type,
      FramesLocalState ((RecM.inferProj id field major type).run methods))
    (inferOnly : Bool) (term : KExpr .anon) :
    FramesLocalState ((RecM.inferUncached inferRec inferOnly term).run methods) := by
  cases term with
  | var index name info => simpa [RecM.inferUncached] using FramesLocalState.lookupVar index
  | fvar id name info =>
      unfold RecM.inferUncached
      simp only [ReaderT.run_bind]
      apply FramesLocalState.bind FramesLocalState.get
      intro state
      split
      · exact FramesLocalState.pure _
      · exact FramesLocalState.throw _
  | sort level info =>
      simpa [RecM.inferUncached, TcM.intern] using
        FramesLocalState.runIntern (internExprM (KExpr.mkSort (KUniv.mkSucc level)))
  | const id levels info =>
      unfold RecM.inferUncached
      simp only [ReaderT.run_bind, ReaderT.run_monadLift]
      apply FramesLocalState.bind (FramesLocalState.getConst id)
      intro constant
      split
      · exact FramesLocalState.throw _
      · exact FramesLocalState.instantiateUnivParams constant.ty levels
  | nat value raw info =>
      unfold RecM.inferUncached
      simp only [ReaderT.run_bind, ReaderT.run_monadLift]
      apply FramesLocalState.bind (FramesLocalState.prims methods)
      intro primitives
      simpa using FramesLocalState.intern (.mkConst primitives.nat #[])
  | str value raw info =>
      unfold RecM.inferUncached
      simp only [ReaderT.run_bind, ReaderT.run_monadLift]
      apply FramesLocalState.bind (FramesLocalState.prims methods)
      intro primitives
      simpa using FramesLocalState.intern (.mkConst primitives.string #[])
  | prj id field major info =>
      unfold RecM.inferUncached
      simp only [ReaderT.run_bind]
      exact FramesLocalState.bind (recursive major) (projection id field major)
  | app function argument info =>
      unfold RecM.inferUncached
      simp only [ReaderT.run_bind]
      apply FramesLocalState.bind (recursive function)
      intro functionType
      apply FramesLocalState.bind (FramesLocalState.ensureForallDirect whnf functionType)
      intro pair
      rcases pair with ⟨domain, codomain⟩
      cases inferOnly with
      | true => exact FramesLocalState.runIntern _
      | false =>
          apply FramesLocalState.bind (recursive argument)
          intro argumentType
          apply FramesLocalState.bind (FramesLocalState.isEagerReduce argument)
          intro eager
          cases eager with
          | false =>
              simp only [Bool.false_eq_true, if_false]
              apply FramesLocalState.bind (conversion argumentType domain)
              intro equal
              cases equal with
              | true => exact FramesLocalState.runIntern _
              | false =>
                  apply FramesLocalState.bind FramesLocalState.get
                  intro state
                  intro before valid
                  exact .refl _
          | true =>
              simp only [if_true]
              change FramesLocalState ((do
                modify fun state : TcState .anon => {state with eagerReduce := true}
                let equal ← RecM.isDefEqCall argumentType domain
                modify fun state : TcState .anon => {state with eagerReduce := false}
                if !equal then
                  throw (.appTypeMismatch argumentType domain (← get).ctx.size)
                TcM.runIntern (subst codomain argument 0) :
                RecM .anon (KExpr .anon)).run methods)
              simp only [ReaderT.run_bind]
              apply FramesLocalState.bind (FramesLocalState.modify
                (fun state => {state with eagerReduce := true}) (fun _ => ⟨Nat.le_refl _, .refl _, rfl⟩))
              intro _
              apply FramesLocalState.bind (conversion argumentType domain)
              intro equal
              apply FramesLocalState.bind (FramesLocalState.modify
                (fun state => {state with eagerReduce := false}) (fun _ => ⟨Nat.le_refl _, .refl _, rfl⟩))
              intro _
              cases equal with
              | true => exact FramesLocalState.runIntern _
              | false =>
                  apply FramesLocalState.bind FramesLocalState.get
                  intro state
                  intro before valid
                  exact .refl _
  | lam name bi domain body info =>
      unfold RecM.inferUncached
      have scope : FramesLocalState ((RecM.withLctxScope (m := .anon) do
          let (opened, fresh) ← TcM.openBinder name bi domain body
          let bodyType ← inferRec opened
          let reduced ← TcM.runIntern (cheapBetaReduce bodyType)
          let abstracted ← TcM.runIntern (abstractFVars reduced #[fresh])
          TcM.intern (.mkAll RecM.anonN RecM.anonBi domain abstracted)).run methods) := by
        apply PreservesLocalState.withLctxScope
        simp only [ReaderT.run_bind, ReaderT.run_monadLift]
        apply PreservesLocalState.bind (PreservesLocalState.openBinder name bi domain body)
        intro pair
        rcases pair with ⟨opened, fresh⟩
        apply PreservesLocalState.bind (recursive opened).preserves
        intro bodyType
        apply PreservesLocalState.bind (FramesLocalState.runIntern _).preserves
        intro reduced
        apply PreservesLocalState.bind (FramesLocalState.runIntern _).preserves
        intro abstracted
        simpa using (FramesLocalState.intern (.mkAll RecM.anonN RecM.anonBi domain abstracted)).preserves
      cases inferOnly with
      | true => exact scope
      | false =>
          simp only [Bool.not_false, if_true, ReaderT.run_bind]
          exact FramesLocalState.bind (recursive domain) fun domainType =>
            FramesLocalState.bind (FramesLocalState.ensureSortDirect whnf domainType) fun _ => scope
  | all name bi domain body info =>
      unfold RecM.inferUncached
      simp only [ReaderT.run_bind]
      apply FramesLocalState.bind (recursive domain)
      intro domainType
      apply FramesLocalState.bind (FramesLocalState.ensureSortDirect whnf domainType)
      intro domainLevel
      apply PreservesLocalState.withLctxScope
      simp only [ReaderT.run_bind, ReaderT.run_monadLift]
      apply PreservesLocalState.bind (PreservesLocalState.openBinder name bi domain body)
      intro pair
      rcases pair with ⟨opened, fresh⟩
      apply PreservesLocalState.bind (recursive opened).preserves
      intro bodyType
      apply PreservesLocalState.bind (FramesLocalState.ensureSortDirect whnf bodyType).preserves
      intro bodyLevel
      simpa using (FramesLocalState.intern (.mkSort (.mkIMax domainLevel bodyLevel))).preserves
  | letE name domain value body nonDep info =>
      unfold RecM.inferUncached
      have scope : FramesLocalState ((RecM.withLctxScope (m := .anon) do
          let (opened, fresh) ← TcM.openLet name domain value body
          let bodyType ← inferRec opened
          let abstracted ← TcM.runIntern (abstractFVars bodyType #[fresh])
          let substituted ← TcM.runIntern (subst abstracted value 0)
          TcM.runIntern (cheapBetaReduce substituted)).run methods) := by
        apply PreservesLocalState.withLctxScope
        simp only [ReaderT.run_bind, ReaderT.run_monadLift]
        apply PreservesLocalState.bind (PreservesLocalState.openLet name domain value body)
        intro pair
        rcases pair with ⟨opened, fresh⟩
        apply PreservesLocalState.bind (recursive opened).preserves
        intro bodyType
        apply PreservesLocalState.bind (FramesLocalState.runIntern _).preserves
        intro abstracted
        apply PreservesLocalState.bind (FramesLocalState.runIntern _).preserves
        intro substituted
        exact (FramesLocalState.runIntern _).preserves
      cases inferOnly with
      | true => exact scope
      | false =>
          simp only [Bool.not_false, if_true, ReaderT.run_bind]
          apply FramesLocalState.bind (recursive domain)
          intro domainType
          apply FramesLocalState.bind (FramesLocalState.ensureSortDirect whnf domainType)
          intro level
          apply FramesLocalState.bind (recursive value)
          intro valueType
          apply FramesLocalState.bind (conversion valueType domain)
          intro equal
          cases equal with
          | true => exact scope
          | false => exact FramesLocalState.throw _

namespace FramesLocalState

/-- Both cache partitions and the actual outer write preserve the local
frame of the uncached action. The statement also covers failed inference. -/
theorem inferWith {inferRec : KExpr .anon → RecM .anon (KExpr .anon)}
    {methods : Methods .anon} (term : KExpr .anon)
    (uncached : ∀ inferOnly,
      FramesLocalState ((RecM.inferUncached inferRec inferOnly term).run methods)) :
    FramesLocalState ((RecM.inferWith inferRec term).run methods) := by
  unfold RecM.inferWith
  simp only [ReaderT.run_bind, ReaderT.run_monadLift]
  apply bind get
  intro state
  apply bind (inferKey term)
  intro key
  apply bind get
  intro checked
  split
  · exact pure _
  · have miss : FramesLocalState ((do
        let type ← RecM.inferUncached inferRec state.inferOnly term
        RecM.cacheInferResult state.inferOnly key type
        Pure.pure type).run methods) := by
      simp only [ReaderT.run_bind]
      exact bind (uncached state.inferOnly) fun type =>
        bind (cacheInferResult state.inferOnly key type methods) fun _ => pure type
    split
    · simp only [ReaderT.run_bind]
      apply bind get
      intro checkedOnly
      split
      · exact pure _
      · exact miss
    · exact miss

end FramesLocalState

/-- The production one-layer inference body restores locals and maintains
the allocation bound in both policies, including hits and partial errors.
Only recursive inference, reduction, conversion and projection contracts
remain for the mutual execution proof. -/
theorem infer_framesLocalState {methods : Methods .anon}
    (recursive : ∀ term, FramesLocalState (methods.infer term))
    (whnf : ∀ term, FramesLocalState ((RecM.whnf term).run methods))
    (conversion : ∀ left right, FramesLocalState ((RecM.isDefEqCall left right).run methods))
    (projection : ∀ id field major type,
      FramesLocalState ((RecM.inferProj id field major type).run methods))
    (term : KExpr .anon) : FramesLocalState ((RecM.infer term).run methods) :=
  FramesLocalState.inferWith term fun inferOnly =>
    inferUncached_framesLocalState (inferRec := RecM.inferCall) (methods := methods)
      recursive whnf conversion projection inferOnly term

end Ix.Kernel.Consistency

