/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.Context
import Ix.Kernel.Verify.Subst

/-!
# Reading the production binder walkers

Opening a syntactic binder and registering its fresh free variable preserve
the same model de Bruijn expression. Closing performs the inverse change of
representation. The bounds below prevent production's `UInt64` depth from
wrapping; they impose no semantic typing assumptions.
-/

namespace Ix.Kernel.Consistency

open Theory Theory.Model

universe u
variable {β : Type u}

private theorem bind_success {α γ : Type _} {action : Option α}
    {next : α → Option γ} {result : γ} (run : action.bind next = some result) :
    ∃ intermediate, action = some intermediate ∧ next intermediate = some result := by
  cases action with
  | none => contradiction
  | some value => exact ⟨value, rfl, run⟩

private theorem depth_succ {depth : UInt64} (bound : depth.toNat + 1 < UInt64.size) :
    (depth + 1).toNat = depth.toNat + 1 := by
  rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl, Nat.mod_eq_of_lt bound]

/-- A fresh local replaces exactly the removed syntactic binder, even below
nested binders and in occurrences of older dependent locals. -/
theorem readScopedExpr?_instantiateRevSpec
    {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {body : KExpr .anon} {source : VExpr β} {depth : UInt64} {fresh : FVarId}
    (absent : fresh ∉ locals)
    (bound : depth.toNat + body.size + 1 < UInt64.size)
    (reading : readScopedExpr? resolve locals body (depth.toNat + 1) = some source) :
    readScopedExpr? resolve (fresh :: locals)
      (KExpr.instantiateRevSpec body #[KExpr.mkFVar fresh ()] depth) depth.toNat =
        some source := by
  induction body generalizing source depth with
  | var index name info =>
      simp only [readScopedExpr?] at reading
      split at reading
      next inScope =>
        cases reading
        have next := depth_succ (depth := depth) (by simp only [KExpr.size] at bound; omega)
        by_cases equal : index = depth
        · subst index
          simp [KExpr.instantiateRevSpec, UInt64.lt_iff_toNat_lt, next,
            localIndex?]
        · have smaller : index.toNat < depth.toNat := by
            have : index.toNat ≠ depth.toNat := fun h => equal (UInt64.toNat_inj.mp h)
            omega
          have before : ¬ index ≥ depth := by
            simp only [UInt64.le_iff_toNat_le]; omega
          have beforeNext : ¬ index ≥ depth + 1 := by
            simp only [UInt64.le_iff_toNat_le, next]; omega
          simp [KExpr.instantiateRevSpec, before, beforeNext, readScopedExpr?, smaller]
      · contradiction
  | fvar id name info =>
      rw [readScopedExpr?] at reading
      obtain ⟨index, found, reading⟩ := Option.map_eq_some_iff.mp reading
      cases reading
      simp [KExpr.instantiateRevSpec, readScopedExpr?, localIndex?_fresh absent found,
        Nat.add_assoc, Nat.add_comm 1]
  | sort _ _ | const _ _ _ | nat _ _ _ => exact reading
  | letE _ _ _ _ _ _ _ _ _ | str _ _ _ => contradiction
  | app fn arg info hf ha =>
      rw [readScopedExpr?] at reading
      obtain ⟨f, fReads, reading⟩ := bind_success reading
      obtain ⟨a, aReads, reading⟩ := bind_success reading
      cases reading
      simp only [KExpr.size] at bound
      simp [KExpr.instantiateRevSpec,
        hf (by omega) fReads, ha (by omega) aReads]
  | lam name bi domain body info hd hb | all name bi domain body info hd hb =>
      rw [readScopedExpr?] at reading
      obtain ⟨A, domainReads, reading⟩ := bind_success reading
      obtain ⟨B, bodyReads, reading⟩ := bind_success reading
      cases reading
      simp only [KExpr.size] at bound
      have next := depth_succ (depth := depth) (by omega)
      have bodyBound : (depth + 1).toNat + body.size + 1 < UInt64.size := by
        rw [next]; omega
      have bodyReads' : readScopedExpr? resolve locals body ((depth + 1).toNat + 1) =
          some B := by simpa only [next] using bodyReads
      have bodyOut : readScopedExpr? resolve (fresh :: locals)
          (KExpr.instantiateRevSpec body #[KExpr.mkFVar fresh ()] (depth + 1))
          (depth.toNat + 1) = some B := by
        simpa only [next] using hb bodyBound bodyReads'
      simp [KExpr.instantiateRevSpec, hd (by omega) domainReads, bodyOut]
  | prj id index value info ih =>
      rw [readScopedExpr?] at reading
      obtain ⟨ref, resolved, reading⟩ := bind_success reading
      obtain ⟨value, valueReads, reading⟩ := bind_success reading
      cases reading
      simp only [KExpr.size] at bound
      simp [KExpr.instantiateRevSpec, resolved,
        ih (by omega) valueReads]

private local instance : LawfulBEq FVarId where
  eq_of_beq := by
    intro left right equal
    cases left
    cases right
    congr 1
    exact eq_of_beq equal
  rfl {a} := by
    cases a with
    | mk x => show (x == x) = true; exact beq_self_eq_true x

/-- Closing the newest local restores the syntactic binder without changing
the model expression. Unknown locals and loose variables cannot pass the
source reading. -/
theorem readScopedExpr?_abstractFVarsSpec
    {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {body : KExpr .anon} {source : VExpr β} {depth : UInt64} {fresh : FVarId}
    (bound : depth.toNat + body.size + 1 < UInt64.size)
    (reading : readScopedExpr? resolve (fresh :: locals) body depth.toNat = some source) :
    readScopedExpr? resolve locals
      (KExpr.abstractFVarsSpec body ((∅ : Std.HashMap FVarId UInt64).insert fresh 0)
        1 depth) (depth.toNat + 1) = some source := by
  induction body generalizing source depth with
  | var index name info =>
      simp only [readScopedExpr?] at reading
      split at reading
      next inScope =>
        cases reading
        have before : ¬ index ≥ depth := by
          simp only [UInt64.le_iff_toNat_le]; omega
        simp [KExpr.abstractFVarsSpec, before, readScopedExpr?, show index.toNat <
          depth.toNat + 1 by omega]
      · contradiction
  | fvar id name info =>
      by_cases equal : id = fresh
      · subst id
        simp [readScopedExpr?, localIndex?] at reading
        cases reading
        simp [KExpr.abstractFVarsSpec]
      · simp only [readScopedExpr?, localIndex?, equal, if_false, Option.map_map] at reading
        obtain ⟨index, found, reading⟩ := Option.map_eq_some_iff.mp reading
        cases reading
        simp [KExpr.abstractFVarsSpec, Ne.symm equal,
          readScopedExpr?, found,
          Nat.add_assoc, Nat.add_comm 1]
  | sort _ _ | const _ _ _ | nat _ _ _ => exact reading
  | letE _ _ _ _ _ _ _ _ _ | str _ _ _ => contradiction
  | app fn arg info hf ha =>
      rw [readScopedExpr?] at reading
      obtain ⟨f, fReads, reading⟩ := bind_success reading
      obtain ⟨a, aReads, reading⟩ := bind_success reading
      cases reading
      simp only [KExpr.size] at bound
      simp [KExpr.abstractFVarsSpec,
        hf (by omega) fReads, ha (by omega) aReads]
  | lam name bi domain body info hd hb | all name bi domain body info hd hb =>
      rw [readScopedExpr?] at reading
      obtain ⟨A, domainReads, reading⟩ := bind_success reading
      obtain ⟨B, bodyReads, reading⟩ := bind_success reading
      cases reading
      simp only [KExpr.size] at bound
      have next := depth_succ (depth := depth) (by omega)
      have bodyBound : (depth + 1).toNat + body.size + 1 < UInt64.size := by
        rw [next]; omega
      have bodyReads' : readScopedExpr? resolve (fresh :: locals) body (depth + 1).toNat =
          some B := by simpa only [next] using bodyReads
      have bodyOut : readScopedExpr? resolve locals
          (KExpr.abstractFVarsSpec body ((∅ : Std.HashMap FVarId UInt64).insert fresh 0)
            1 (depth + 1)) (depth.toNat + 1 + 1) = some B := by
        simpa only [next] using hb bodyBound bodyReads'
      simp [KExpr.abstractFVarsSpec, hd (by omega) domainReads, bodyOut]
  | prj id index value info ih =>
      rw [readScopedExpr?] at reading
      obtain ⟨ref, resolved, reading⟩ := bind_success reading
      obtain ⟨value, valueReads, reading⟩ := bind_success reading
      cases reading
      simp only [KExpr.size] at bound
      simp [KExpr.abstractFVarsSpec, resolved,
        ih (by omega) valueReads]

/-- The exact successful-state shape of production binder opening. -/
theorem openBinder_eq (name : Mode.anon.F Name) (bi : Mode.anon.F Lean.BinderInfo)
    (type body : KExpr .anon) (before : TcState .anon) :
    TcM.openBinder name bi type body before =
      if before.env.nextFVarId.toNat + 1 < UInt64.size then
        let fresh : FVarId := ⟨before.env.nextFVarId⟩
        let internedLocal := before.env.intern.internExpr (KExpr.mkFVar fresh name)
        let opened := instantiateRev body #[internedLocal.1] internedLocal.2
        .ok (opened.1, fresh) {before with
          env := {before.env with
            nextFVarId := before.env.nextFVarId + 1
            intern := opened.2}
          lctx := before.lctx.push fresh (.cdecl name bi type)}
      else .error (.other "free-variable id space exhausted") before := by
  unfold TcM.openBinder
  change EStateM.bind TcM.freshFVarId _ before = _
  rw [EStateM.bind, TcM.freshFVarId]
  by_cases room : before.env.nextFVarId.toNat + 1 < UInt64.size
  · simp only [room, if_true]
    rfl
  · simp only [room, if_false]

/-- Finite production resources for one binder opening. Collision freedom is
needed only on the existing table, the new local, and this walker's reach. -/
structure BinderOpeningSupport (before : TcState .anon) (body : KExpr .anon) : Prop where
  constructed : body.Constructed
  bound : body.size + 1 < UInt64.size
  coherent : before.env.intern.WF
  faithful : KExpr.CollisionFree fun term =>
    before.env.intern.ExprSupport term ∨
      term = KExpr.mkFVar ⟨before.env.nextFVarId⟩ () ∨
      KExpr.InstRevReach #[KExpr.mkFVar ⟨before.env.nextFVarId⟩ ()] body 0 term

/-- Successful binder opening preserves the model body and implements the
model's dependent context extension, using the actual allocated id. -/
theorem openBinder_sound
    {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {context : Model.Context β} {type body opened : KExpr .anon}
    {A : AExpr β} {b : VExpr β} {fresh : FVarId} {before after : TcState .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    (support : BinderOpeningSupport before body)
    (agreement : LocalContextReading resolve locals before.lctx context)
    (absent : (⟨before.env.nextFVarId⟩ : FVarId) ∉ locals)
    (typeReads : readScopedExpr? resolve locals type = some A.erase)
    (bodyReads : readScopedExpr? resolve locals body 1 = some b)
    (accepted : TcM.openBinder name bi type body before = .ok (opened, fresh) after) :
    fresh = ⟨before.env.nextFVarId⟩ ∧
      readScopedExpr? resolve (fresh :: locals) opened = some b ∧
      LocalContextReading resolve (fresh :: locals) after.lctx (context.push A) ∧
      after.env.intern.WF := by
  have nameUnit : name = () := Subsingleton.elim _ _
  have biUnit : bi = () := Subsingleton.elim _ _
  subst name bi
  have interned : (before.env.intern.internExpr
      (KExpr.mkFVar ⟨before.env.nextFVarId⟩ ())).1 =
        KExpr.mkFVar ⟨before.env.nextFVarId⟩ () := by
    have keyFaithful : KExpr.KeyCollisionFree (fun term =>
        before.env.intern.ExprSupport term ∨ term = KExpr.mkFVar ⟨before.env.nextFVarId⟩ ()) :=
      KExpr.keyCollisionFree_anon.mpr
      (support.faithful.mono fun term h => h.elim Or.inl (fun equal => .inr (.inl equal)))
    simpa only [KExpr.eraseMeta_anon] using
      before.env.intern.internExpr_eraseMeta support.coherent keyFaithful
  have walk := instantiateRev_spec (fvars := #[KExpr.mkFVar ⟨before.env.nextFVarId⟩ ()])
    support.faithful support.constructed (by simpa using support.bound)
    (fun _ reached => .inr (.inr reached))
    (support.coherent.internExpr (KExpr.mkFVar ⟨before.env.nextFVarId⟩ ()))
    (fun _ member => (InternTable.ExprSupport.of_internExpr member).elim
      Or.inl (fun equal => .inr (.inl equal)))
  rw [openBinder_eq] at accepted
  split at accepted
  · simp only [interned] at accepted
    cases accepted
    refine ⟨rfl, ?_, agreement.push (decl := .cdecl () () type) absent typeReads, walk.2.1⟩
    rw [walk.1]
    exact readScopedExpr?_instantiateRevSpec absent (by simpa using support.bound) bodyReads
  · contradiction

private theorem abstractFVars_singleton_eq (body : KExpr .anon) (fresh : FVarId) :
    abstractFVars body #[fresh] =
      if (!body.hasFVars && body.lbr == 0) then pure body
      else runWalk (abstractFVarsCached body
        ((∅ : Std.HashMap FVarId UInt64).insert fresh 0) 1 0) := by
  unfold abstractFVars
  simp only [show #[fresh].isEmpty = false from rfl, Bool.false_or]
  by_cases fast : (!body.hasFVars && body.lbr == 0) = true
  · simp only [fast, if_true]
  · simp only [fast, ← Array.forIn_toList]
    simp

/-- Exact refinement of the production singleton abstraction, including its
no-free-variable fast path and its memoized recursive walk. -/
theorem abstractFVars_singleton_spec {body : KExpr .anon} {fresh : FVarId}
    {table : InternTable .anon} {support : KExpr .anon → Prop}
    (constructed : body.Constructed) (bound : body.size < UInt64.size)
    (faithful : KExpr.CollisionFree support) (coherent : table.WF)
    (initial : ∀ term, table.ExprSupport term → support term)
    (reachable : ∀ term, KExpr.AbstractReach
      ((∅ : Std.HashMap FVarId UInt64).insert fresh 0) 1 body 0 term → support term) :
    (abstractFVars body #[fresh] table).1 = KExpr.abstractFVarsSpec body
      ((∅ : Std.HashMap FVarId UInt64).insert fresh 0) 1 0 ∧
      (abstractFVars body #[fresh] table).2.WF := by
  rw [abstractFVars_singleton_eq]
  split
  next fast =>
    have noFVars : body.hasFVars = false := by
      have := (Bool.and_eq_true_iff.mp fast).1
      simpa using this
    have noLoose : body.lbr ≤ (0 : UInt64) := by
      rw [eq_of_beq (Bool.and_eq_true_iff.mp fast).2]
      exact UInt64.le_refl _
    exact ⟨(KExpr.abstractFVarsSpec_id constructed (by simpa using bound) noFVars noLoose).symm,
      coherent⟩
  · have post := abstractFVarsCached_spec faithful constructed (depth := 0)
      (by simpa using bound) reachable coherent initial
      (WalkScratchInv.empty support _)
    exact ⟨post.result, post.wf⟩

/-- Production abstraction recovers the model body under the closed binder. -/
theorem abstractFVars_readScopedExpr?
    {resolve : Address → Option (ConstRef β)} {locals : List FVarId}
    {body : KExpr .anon} {fresh : FVarId} {source : VExpr β}
    {table : InternTable .anon}
    (constructed : body.Constructed) (bound : body.size + 1 < UInt64.size)
    (coherent : table.WF)
    (faithful : KExpr.CollisionFree fun term => table.ExprSupport term ∨
      KExpr.AbstractReach ((∅ : Std.HashMap FVarId UInt64).insert fresh 0) 1 body 0 term)
    (reading : readScopedExpr? resolve (fresh :: locals) body = some source) :
    readScopedExpr? resolve locals (abstractFVars body #[fresh] table).1 1 = some source ∧
      (abstractFVars body #[fresh] table).2.WF := by
  obtain ⟨result, coherent⟩ := abstractFVars_singleton_spec constructed (by omega)
    faithful coherent (fun _ => Or.inl) (fun _ => Or.inr)
  refine ⟨?_, coherent⟩
  rw [result]
  exact readScopedExpr?_abstractFVarsSpec (by simpa using bound) reading

end Ix.Kernel.Consistency
