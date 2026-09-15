/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BetaCacheKeys

/-! Structural WHNF's full and cheap cache partitions. Recursive head calls
use the original flags and publish even during native reduction. -/

namespace Ix.Kernel.Consistency.BetaCoreCache

def lookup (flags : WhnfFlags) (key : Address × Address) (before : TcState .anon) : Option (KExpr .anon) :=
  if flags.isFull then before.env.whnfCoreCache[key]? else before.env.whnfCoreCheapCache[key]?

def write (flags : WhnfFlags) (key : Address × Address) (result : KExpr .anon) (before : TcState .anon) : TcState .anon :=
  if flags.isFull then
    {before with env := {before.env with whnfCoreCache := before.env.whnfCoreCache.insert key result}}
  else
    {before with env := {before.env with whnfCoreCheapCache := before.env.whnfCoreCheapCache.insert key result}}

theorem frame (flags : WhnfFlags) (key : Address × Address) (result : KExpr .anon) (before : TcState .anon) :
    BetaCacheFrame before (write flags key result before) := by
  unfold write
  split
  · exact .core _ _ _
  · exact .cheap _ _ _

theorem intern (flags : WhnfFlags) (key : Address × Address) (result : KExpr .anon) (before : TcState .anon) :
    (write flags key result before).env.intern = before.env.intern := by
  unfold write
  split <;> rfl

theorem published (flags : WhnfFlags) (key : Address × Address) (result : KExpr .anon) (before : TcState .anon) :
    lookup flags key (write flags key result before) = some result := by
  unfold lookup write
  split <;> simp only [Std.HashMap.getElem?_insert_self]

theorem hit {methods : Methods .anon} {before : TcState .anon} {source result : KExpr .anon}
    (flags : WhnfFlags) (entry : StructuralWhnfEntry source)
    (found : lookup flags (betaWhnfKey source before).1 (betaWhnfKey source before).2 = some result) :
    (RecM.whnfCoreWithFlags source flags).run methods before =
      .ok result (betaWhnfKey source before).2 := by
  rw [entry.core flags]
  unfold RecM.whnfCoreWithFlagsNonLeaf
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.whnfKey source) _ before = _
  rw [EStateM.bind, betaWhnfKey_run]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((RecM.isTransientNatLiteralWork source).run methods) _ _ = _
  rw [EStateM.bind, entry.not_transient]
  cases full : flags.isFull <;> simp only [Bool.false_eq_true, Bool.not_false, if_true, if_false]
  all_goals
    rw [ReaderT.run_bind]
    change EStateM.bind (get : TcM .anon (TcState .anon)) _ _ = _
    rw [EStateM.bind]
    simp only [show (get : TcM .anon (TcState .anon)) (betaWhnfKey source before).2 =
      .ok (betaWhnfKey source before).2 (betaWhnfKey source before).2 from rfl]
    simp only [lookup, full, Bool.false_eq_true, if_true, if_false] at found
    rw [found]
    rfl

theorem miss {methods : Methods .anon} {before after : TcState .anon} {source result : KExpr .anon}
    (flags : WhnfFlags) (entry : StructuralWhnfEntry source)
    (absent : lookup flags (betaWhnfKey source before).1 (betaWhnfKey source before).2 = none)
    (reduced : (RecM.whnfCoreWithFlagsUncached source flags).run methods
      (betaWhnfKey source before).2 = .ok result after) :
    (RecM.whnfCoreWithFlags source flags).run methods before =
      .ok result (write flags (betaWhnfKey source before).1 result after) := by
  rw [entry.core flags]
  unfold RecM.whnfCoreWithFlagsNonLeaf
  rw [ReaderT.run_bind]
  change EStateM.bind (TcM.whnfKey source) _ before = _
  rw [EStateM.bind, betaWhnfKey_run]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind ((RecM.isTransientNatLiteralWork source).run methods) _ _ = _
  rw [EStateM.bind, entry.not_transient]
  cases full : flags.isFull <;> simp only [Bool.false_eq_true, Bool.not_false, if_true, if_false]
  all_goals
    rw [ReaderT.run_bind]
    change EStateM.bind (get : TcM .anon (TcState .anon)) _ _ = _
    rw [EStateM.bind]
    simp only [show (get : TcM .anon (TcState .anon)) (betaWhnfKey source before).2 =
      .ok (betaWhnfKey source before).2 (betaWhnfKey source before).2 from rfl]
    simp only [lookup, full, Bool.false_eq_true, if_true, if_false] at absent
    rw [absent]
    simp only
    rw [ReaderT.run_bind]
    change EStateM.bind ((RecM.whnfCoreWithFlagsUncached source flags).run methods) _ _ = _
    rw [EStateM.bind, reduced]
    simp only [write, full, Bool.false_eq_true, if_true, if_false]
    rfl

/-- A successful miss determines the uncached result and its state before
publication, for the full and cheap partitions alike. -/
theorem miss_success {methods : Methods .anon} {before after : TcState .anon} {source result : KExpr .anon}
    (flags : WhnfFlags) (entry : StructuralWhnfEntry source)
    (absent : lookup flags (betaWhnfKey source before).1 (betaWhnfKey source before).2 = none)
    (accepted : (RecM.whnfCoreWithFlags source flags).run methods before = .ok result after) :
    ∃ reduced, (RecM.whnfCoreWithFlagsUncached source flags).run methods
        (betaWhnfKey source before).2 = .ok result reduced ∧
      after = write flags (betaWhnfKey source before).1 result reduced := by
  rw [entry.core flags] at accepted
  unfold RecM.whnfCoreWithFlagsNonLeaf at accepted
  rw [ReaderT.run_bind] at accepted
  change EStateM.bind (TcM.whnfKey source) _ before = _ at accepted
  rw [EStateM.bind, betaWhnfKey_run] at accepted
  simp only at accepted
  rw [ReaderT.run_bind] at accepted
  change EStateM.bind ((RecM.isTransientNatLiteralWork source).run methods) _ _ = _ at accepted
  rw [EStateM.bind, entry.not_transient] at accepted
  cases full : flags.isFull <;>
    simp only [full, Bool.false_eq_true, Bool.not_false, if_true, if_false] at accepted
  all_goals
    rw [ReaderT.run_bind] at accepted
    change EStateM.bind (get : TcM .anon (TcState .anon)) _ _ = _ at accepted
    rw [EStateM.bind] at accepted
    simp only [show (get : TcM .anon (TcState .anon)) (betaWhnfKey source before).2 =
      .ok (betaWhnfKey source before).2 (betaWhnfKey source before).2 from rfl] at accepted
    simp only [lookup, full, Bool.false_eq_true, if_true, if_false] at absent
    rw [absent] at accepted
    simp only at accepted
    rw [ReaderT.run_bind] at accepted
    change EStateM.bind ((RecM.whnfCoreWithFlagsUncached source flags).run methods) _ _ = _ at accepted
    cases raw : (RecM.whnfCoreWithFlagsUncached source flags).run methods (betaWhnfKey source before).2 with
    | error error failed => simp only [EStateM.bind, raw] at accepted; cases accepted
    | ok value reduced =>
        rw [EStateM.bind, raw] at accepted
        have exactRun : EStateM.Result.ok (ε := TcError .anon) value (write flags (betaWhnfKey source before).1 value reduced) =
            .ok result after := by
          simp only [write, full, Bool.false_eq_true, if_true, if_false]
          exact Eq.trans (by rfl) accepted
        obtain ⟨rfl, afterEq⟩ := EStateM.Result.ok.inj exactRun
        exact ⟨reduced, rfl, afterEq.symm⟩

end Ix.Kernel.Consistency.BetaCoreCache
