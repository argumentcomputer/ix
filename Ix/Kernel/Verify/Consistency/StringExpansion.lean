/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.InternInvariant
import Ix.Kernel.Verify.Consistency.ScopedExpr
import Ix.Kernel.Whnf

/-!
# Production string expansion

The candidate list is computed from the source characters and primitive
expressions. One collision condition on that list plus the initial table
discharges every intern call. The result and complete final state follow
from the actual production recursion, without a supplied execution plan.
-/

namespace Ix.Kernel.Consistency

open Theory

namespace StringExpansion

attribute [local irreducible] InternTable.internExpr

def charValue (charOfNat : KExpr .anon) (char : Char) : KExpr .anon :=
  .mkApp charOfNat (RecM.natExprFromValue char.toNat)

def listStep (charOfNat cons : KExpr .anon) (char : Char) (list : KExpr .anon) : KExpr .anon :=
  .mkApp (.mkApp cons (charValue charOfNat char)) list

def listResult (charOfNat cons : KExpr .anon) : List Char → KExpr .anon → KExpr .anon
  | [], list => list
  | char :: chars, list => listResult charOfNat cons chars (listStep charOfNat cons char list)

def listCandidates (charOfNat cons : KExpr .anon) : List Char → KExpr .anon → List (KExpr .anon)
  | [], _ => []
  | char :: chars, list =>
      RecM.natExprFromValue char.toNat :: charValue charOfNat char ::
      KExpr.mkApp cons (charValue charOfNat char) :: listStep charOfNat cons char list ::
      listCandidates charOfNat cons chars (listStep charOfNat cons char list)

theorem listCandidates_length (charOfNat cons : KExpr .anon) (chars : List Char)
    (list : KExpr .anon) : (listCandidates charOfNat cons chars list).length = 4 * chars.length := by
  induction chars generalizing list with
  | nil => rfl
  | cons char chars ih => simp [listCandidates, ih, Nat.mul_add, Nat.add_assoc]

theorem list_run {pool : KExpr .anon → Prop} (faithful : KExpr.KeyCollisionFree pool)
    (methods : Methods .anon) (charOfNat cons : KExpr .anon) (chars : List Char)
    (list : KExpr .anon) {before : TcState .anon}
    (valid : ExpressionInternInvariant pool before.env.intern)
    (allowed : ∀ term ∈ listCandidates charOfNat cons chars list, pool term) :
    (RecM.strLitListToConstructor charOfNat cons chars list).run methods before =
      .ok (listResult charOfNat cons chars list)
        {before with env := {before.env with intern := (internExprList before.env.intern
          (listCandidates charOfNat cons chars list))}} := by
  induction chars generalizing list before with
  | nil => rfl
  | cons char chars ih =>
      let n : KExpr .anon := RecM.natExprFromValue char.toNat
      let c := charValue charOfNat char
      let headApp := KExpr.mkApp cons c
      let next := listStep charOfNat cons char list
      have hn : pool n := allowed n (by simp [n, listCandidates])
      have hc : pool c := allowed c (by simp [c, listCandidates])
      have hp : pool headApp := allowed headApp (by simp [headApp, c, listCandidates])
      have hl : pool next := allowed next (by simp [next, listCandidates])
      let s1 := internExprState before n
      let s2 := internExprState s1 c
      let s3 := internExprState s2 headApp
      let s4 := internExprState s3 next
      have v1 : ExpressionInternInvariant pool s1.env.intern := valid.internExpr hn
      have v2 : ExpressionInternInvariant pool s2.env.intern := v1.internExpr hc
      have v3 : ExpressionInternInvariant pool s3.env.intern := v2.internExpr hp
      have v4 : ExpressionInternInvariant pool s4.env.intern := v3.internExpr hl
      have tailAllowed : ∀ term ∈ listCandidates charOfNat cons chars next, pool term := by
        intro term member
        exact allowed term (by simp [listCandidates, next, member])
      have tailRun := ih next v4 tailAllowed
      unfold RecM.strLitListToConstructor
      rw [ReaderT.run_bind, ReaderT.run_monadLift]
      change EStateM.bind (TcM.intern n) _ before = _
      rw [EStateM.bind, intern_eq valid faithful hn]
      simp only
      rw [ReaderT.run_bind, ReaderT.run_monadLift]
      change EStateM.bind (TcM.intern c) _ s1 = _
      rw [EStateM.bind, intern_eq v1 faithful hc]
      simp only
      rw [ReaderT.run_bind, ReaderT.run_monadLift]
      change EStateM.bind (TcM.intern headApp) _ s2 = _
      rw [EStateM.bind, intern_eq v2 faithful hp]
      simp only
      rw [ReaderT.run_bind, ReaderT.run_monadLift]
      change EStateM.bind (TcM.intern next) _ s3 = _
      rw [EStateM.bind, intern_eq v3 faithful hl]
      simp only
      simpa only [listResult, listCandidates, internExprList, List.foldl_cons,
        s4, s3, s2, s1, internExprState, n, c, headApp, next] using tailRun


def charType (prims : Primitives .anon) : KExpr .anon := .mkConst prims.charType #[]
def charFunction (prims : Primitives .anon) : KExpr .anon := .mkConst prims.charOfNat #[]
def stringFunction (prims : Primitives .anon) : KExpr .anon := .mkConst prims.stringOfList #[]
def nilFunction (prims : Primitives .anon) : KExpr .anon := .mkConst prims.listNil #[.mkZero]
def nilValue (prims : Primitives .anon) : KExpr .anon := .mkApp (nilFunction prims) (charType prims)
def consFunction (prims : Primitives .anon) : KExpr .anon := .mkConst prims.listCons #[.mkZero]
def consValue (prims : Primitives .anon) : KExpr .anon := .mkApp (consFunction prims) (charType prims)

def prefixNodes (prims : Primitives .anon) : List (KExpr .anon) :=
  [charType prims, charFunction prims, stringFunction prims, nilFunction prims,
    nilValue prims, consFunction prims, consValue prims]

def result (prims : Primitives .anon) (value : String) : KExpr .anon :=
  .mkApp (stringFunction prims)
    (listResult (charFunction prims) (consValue prims) value.toList.reverse (nilValue prims))

def candidates (prims : Primitives .anon) (value : String) : List (KExpr .anon) :=
  prefixNodes prims ++
    listCandidates (charFunction prims) (consValue prims) value.toList.reverse (nilValue prims) ++
    [result prims value]

theorem candidates_length (prims : Primitives .anon) (value : String) :
    (candidates prims value).length = 8 + 4 * value.toList.length := by
  simp only [candidates, prefixNodes, List.length_append, List.length_cons, List.length_nil,
    listCandidates_length, List.length_reverse]
  omega

/-- Exact production execution for every string, including empty strings and
repeated characters. No method callback is used by this operation. -/
theorem run {pool : KExpr .anon → Prop} (faithful : KExpr.KeyCollisionFree pool)
    (methods : Methods .anon) (value : String) {before : TcState .anon}
    (valid : ExpressionInternInvariant pool before.env.intern)
    (allowed : ∀ term ∈ candidates before.prims value, pool term) :
    (RecM.strLitToConstructor value).run methods before =
      .ok (result before.prims value)
        {before with env := {before.env with intern := (internExprList before.env.intern
          (candidates before.prims value))}} := by
  let p := before.prims
  have h1 : pool (charType p) := allowed _ (by simp [candidates, prefixNodes, p])
  let s1 := internExprState before (charType p)
  have v1 : ExpressionInternInvariant pool s1.env.intern := valid.internExpr h1
  have h2 : pool (charFunction p) := allowed _ (by simp [candidates, prefixNodes, p])
  let s2 := internExprState s1 (charFunction p)
  have v2 : ExpressionInternInvariant pool s2.env.intern := v1.internExpr h2
  have h3 : pool (stringFunction p) := allowed _ (by simp [candidates, prefixNodes, p])
  let s3 := internExprState s2 (stringFunction p)
  have v3 : ExpressionInternInvariant pool s3.env.intern := v2.internExpr h3
  have h4 : pool (nilFunction p) := allowed _ (by simp [candidates, prefixNodes, p])
  let s4 := internExprState s3 (nilFunction p)
  have v4 : ExpressionInternInvariant pool s4.env.intern := v3.internExpr h4
  have h5 : pool (nilValue p) := allowed _ (by simp [candidates, prefixNodes, p])
  let s5 := internExprState s4 (nilValue p)
  have v5 : ExpressionInternInvariant pool s5.env.intern := v4.internExpr h5
  have h6 : pool (consFunction p) := allowed _ (by simp [candidates, prefixNodes, p])
  let s6 := internExprState s5 (consFunction p)
  have v6 : ExpressionInternInvariant pool s6.env.intern := v5.internExpr h6
  have h7 : pool (consValue p) := allowed _ (by simp [candidates, prefixNodes, p])
  let s7 := internExprState s6 (consValue p)
  have v7 : ExpressionInternInvariant pool s7.env.intern := v6.internExpr h7
  have listAllowed : ∀ term ∈ listCandidates (charFunction p) (consValue p)
      value.toList.reverse (nilValue p), pool term := by
    intro term member
    exact allowed term (by simp [candidates, p, member])
  have lastAllowed : pool (result p value) := allowed _ (by simp [candidates, p])
  let s8 : TcState .anon :=
    {s7 with env := {s7.env with intern := (internExprList s7.env.intern
      (listCandidates (charFunction p) (consValue p) value.toList.reverse (nilValue p)))}}
  have v8 : ExpressionInternInvariant pool s8.env.intern :=
    v7.internExprList _ listAllowed
  have listRun := list_run faithful methods (charFunction p) (consValue p)
    value.toList.reverse (nilValue p) v7 listAllowed
  unfold RecM.strLitToConstructor
  rw [ReaderT.run_bind]
  change EStateM.bind (ReaderT.run RecM.prims methods) _ before = _
  rw [EStateM.bind, show ReaderT.run RecM.prims methods before = .ok p before from rfl]
  simp only
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.intern (charType p)) _ before = _
  rw [EStateM.bind, intern_eq valid faithful h1]
  simp only
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.intern (charFunction p)) _ s1 = _
  rw [EStateM.bind, intern_eq v1 faithful h2]
  simp only
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.intern (stringFunction p)) _ s2 = _
  rw [EStateM.bind, intern_eq v2 faithful h3]
  simp only
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.intern (nilFunction p)) _ s3 = _
  rw [EStateM.bind, intern_eq v3 faithful h4]
  simp only
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.intern (nilValue p)) _ s4 = _
  rw [EStateM.bind, intern_eq v4 faithful h5]
  simp only
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.intern (consFunction p)) _ s5 = _
  rw [EStateM.bind, intern_eq v5 faithful h6]
  simp only
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.intern (consValue p)) _ s6 = _
  rw [EStateM.bind, intern_eq v6 faithful h7]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (RecM.strLitListToConstructor (charFunction p) (consValue p)
      value.toList.reverse (nilValue p)) methods) _ s7 = _
  rw [EStateM.bind, listRun]
  simp only
  rw [ReaderT.run_monadLift]
  change TcM.intern (result p value) s8 = _
  rw [intern_eq v8 faithful lastAllowed]
  simp only [s8, s7, s6, s5, s4, s3, s2, s1, internExprState,
    candidates, prefixNodes, internExprList, List.foldl_append, List.foldl_cons,
    List.foldl_nil, p]

/-- A single finite-support assumption supplies all the internal memberships.
The theorem also preserves the invariant for the complete final table. -/
theorem run_finite (methods : Methods .anon) (value : String) (before : TcState .anon)
    (coherent : before.env.intern.WF)
    (faithful : KExpr.KeyCollisionFree fun term => before.env.intern.ExprSupport term ∨
      term ∈ candidates before.prims value) :
    (RecM.strLitToConstructor value).run methods before =
      .ok (result before.prims value)
        {before with env := {before.env with intern := (internExprList before.env.intern
          (candidates before.prims value))}} ∧
    ExpressionInternInvariant
      (fun term => before.env.intern.ExprSupport term ∨ term ∈ candidates before.prims value)
      (internExprList before.env.intern (candidates before.prims value)) := by
  have valid : ExpressionInternInvariant
      (fun term => before.env.intern.ExprSupport term ∨ term ∈ candidates before.prims value)
      before.env.intern := ⟨coherent, fun _ member => .inl member⟩
  exact ⟨run faithful methods value valid (fun _ member => .inr member),
    valid.internExprList _ (fun _ member => .inr member)⟩


theorem listResult_read {β : Type u} {resolve : Address → Option (ConstRef β)}
    {locals : List FVarId} {depth : Nat} (refs : StringPrimitiveRefs β)
    {charOfNat cons : KExpr .anon} (chars : List Char) {list : KExpr .anon} {source : VExpr β}
    (charReads : readScopedExpr? resolve locals charOfNat depth = some (.const refs.charOfNat []))
    (consReads : readScopedExpr? resolve locals cons depth = some refs.consExpr)
    (listReads : readScopedExpr? resolve locals list depth = some source) :
    readScopedExpr? resolve locals (listResult charOfNat cons chars list) depth =
      some (chars.foldl (fun current char =>
        .app (.app refs.consExpr (refs.charExpr char)) current) source) := by
  induction chars generalizing list source with
  | nil => exact listReads
  | cons char chars ih =>
      apply ih
      simp [listStep, charValue, RecM.natExprFromValue, readScopedExpr?,
        charReads, consReads, listReads, StringPrimitiveRefs.charExpr, KExpr.mkNat]

theorem result_read {β : Type u} {resolve : Address → Option (ConstRef β)}
    (locals : List FVarId) (depth : Nat) (value : String) {refs : StringPrimitiveRefs β}
    (resolved : StringPrimitiveRefs.resolve? resolve = some refs) :
    readScopedExpr? resolve locals (result Primitives.ofAnonAddrs value) depth =
      some (refs.expr value) := by
  obtain ⟨typeResolved, charResolved, stringResolved, nilResolved, consResolved⟩ :=
    StringPrimitiveRefs.resolve?_fields resolved
  have charReads : readScopedExpr? resolve locals (charFunction Primitives.ofAnonAddrs) depth =
      some (.const refs.charOfNat []) := by
    change (do return VExpr.const (← resolve PrimAddrs.canonical.charOfNat) []) = _
    simp [charResolved]
  have typeReads : readScopedExpr? resolve locals (charType Primitives.ofAnonAddrs) depth =
      some (.const refs.charType []) := by
    change (do return VExpr.const (← resolve PrimAddrs.canonical.charType) []) = _
    simp [typeResolved]
  have consFnReads : readScopedExpr? resolve locals (consFunction Primitives.ofAnonAddrs) depth =
      some (.const refs.listCons [.zero]) := by
    change (do return VExpr.const (← resolve PrimAddrs.canonical.listCons) [.zero]) = _
    simp [consResolved]
  have nilFnReads : readScopedExpr? resolve locals (nilFunction Primitives.ofAnonAddrs) depth =
      some (.const refs.listNil [.zero]) := by
    change (do return VExpr.const (← resolve PrimAddrs.canonical.listNil) [.zero]) = _
    simp [nilResolved]
  have stringFnReads : readScopedExpr? resolve locals (stringFunction Primitives.ofAnonAddrs) depth =
      some (.const refs.stringOfList []) := by
    change (do return VExpr.const (← resolve PrimAddrs.canonical.stringOfList) []) = _
    simp [stringResolved]
  have consReads : readScopedExpr? resolve locals (consValue Primitives.ofAnonAddrs) depth =
      some refs.consExpr := by
    simp [consValue, consFnReads, typeReads, StringPrimitiveRefs.consExpr]
  have nilReads : readScopedExpr? resolve locals (nilValue Primitives.ofAnonAddrs) depth =
      some refs.nilExpr := by
    simp [nilValue, nilFnReads, typeReads, StringPrimitiveRefs.nilExpr]
  have listReads := listResult_read refs value.toList.reverse charReads consReads nilReads
  simp only [List.foldl_reverse] at listReads
  unfold result
  rw [readScopedExpr?_mkApp, listReads]
  simp [stringFnReads, StringPrimitiveRefs.expr, StringPrimitiveRefs.listExpr]

/-- The actual output has exactly the string literal's structural reading.
The public hypotheses are canonical primitives, resolvable references,
table coherence and collision freedom on the explicit finite allocation list. -/
theorem read_of_run {β : Type u} {resolve : Address → Option (ConstRef β)}
    {methods : Methods .anon} {value : String} {before after : TcState .anon}
    {output : KExpr .anon} {source : VExpr β}
    (canonical : before.prims = Primitives.ofAnonAddrs)
    (reading : readString? resolve value = some source)
    (coherent : before.env.intern.WF)
    (faithful : KExpr.KeyCollisionFree fun term => before.env.intern.ExprSupport term ∨
      term ∈ candidates before.prims value)
    (accepted : (RecM.strLitToConstructor value).run methods before = .ok output after)
    (locals : List FVarId) (depth : Nat) :
    readScopedExpr? resolve locals output depth = some source ∧ after.env.intern.WF := by
  obtain ⟨run, valid⟩ := run_finite methods value before coherent faithful
  rw [run] at accepted
  cases accepted
  obtain ⟨refs, resolved, rfl⟩ := readString?_parts reading
  exact ⟨by simpa only [canonical] using result_read locals depth value resolved, valid.coherent⟩

end StringExpansion
end Ix.Kernel.Consistency
