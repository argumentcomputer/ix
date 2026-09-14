/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Ingress

/-!
# Exact state effects of anonymous ingress

Conversion and publication may change loaded declarations, block membership
and intern tables. Every other checker-owned environment field, including
all inference and reduction caches and the fresh-variable counter, is
preserved on both success and partial failure. The proof follows the actual
finite conversion loops, their scratch caches and cyclic-sharing rejection.

Source interpretation, address integrity and finite intern collision bounds
remain separate semantic obligations.
-/

namespace Ix.Kernel

/-- Ingress owns the loaded declarations, block index and intern table. -/
def KEnv.IngressFrame (before after : AnonEnv) : Prop :=
  ∃ consts blocks intern, after = {before with consts, blocks, intern}

namespace KEnv.IngressFrame

theorem refl (state : AnonEnv) : KEnv.IngressFrame state state :=
  ⟨state.consts, state.blocks, state.intern, rfl⟩

theorem trans {before middle after : AnonEnv}
    (first : KEnv.IngressFrame before middle) (second : KEnv.IngressFrame middle after) : KEnv.IngressFrame before after := by
  obtain ⟨consts, blocks, intern, first⟩ := first
  obtain ⟨newConsts, newBlocks, newIntern, second⟩ := second
  refine ⟨newConsts, newBlocks, newIntern, ?_⟩
  rw [second, first]

theorem counter {before after : AnonEnv} (frame : KEnv.IngressFrame before after) :
    after.nextFVarId = before.nextFVarId := by
  obtain ⟨_, _, _, rfl⟩ := frame
  rfl

theorem insert (before : AnonEnv) (id : KId .anon) (constant : KConst .anon) :
    KEnv.IngressFrame before (before.insert id constant) :=
  ⟨_, before.blocks, before.intern, rfl⟩

theorem insertBlock (before : AnonEnv) (id : KId .anon) (members : Array (KId .anon)) :
    KEnv.IngressFrame before (before.insertBlock id members) :=
  ⟨before.consts, _, before.intern, rfl⟩

theorem foldl (items : List α) (before : AnonEnv) (step : AnonEnv → α → AnonEnv)
    (framed : ∀ state item, KEnv.IngressFrame state (step state item)) :
    KEnv.IngressFrame before (items.foldl step before) := by
  induction items generalizing before with
  | nil => exact .refl _
  | cons item rest ih => exact (framed before item).trans (ih (step before item))

end KEnv.IngressFrame

def IngressM.FramesState (action : IngressM α) : Prop :=
  ∀ before, match action before with
    | .ok _ after | .error _ after => KEnv.IngressFrame before after

namespace IngressM.FramesState

theorem pure (value : α) : IngressM.FramesState (Pure.pure value) := fun _ => .refl _
theorem throw (error : String) : IngressM.FramesState (throw error : IngressM α) := fun _ => .refl _
theorem get : IngressM.FramesState (get : IngressM AnonEnv) := fun _ => .refl _

theorem modifyGet (f : AnonEnv → α × AnonEnv)
    (frame : ∀ before, KEnv.IngressFrame before (f before).2) :
    IngressM.FramesState (MonadStateOf.modifyGet f : IngressM α) := fun before => frame before

theorem liftExcept (result : Except String α) : IngressM.FramesState (IngressM.liftExcept result) := by
  cases result <;> first | exact pure _ | exact throw _

theorem bind {action : IngressM α} {next : α → IngressM β}
    (first : IngressM.FramesState action) (rest : ∀ value, IngressM.FramesState (next value)) : IngressM.FramesState (action >>= next) := by
  intro before
  have frame := first before
  change match EStateM.bind action next before with
    | .ok _ after | .error _ after => KEnv.IngressFrame before after
  cases run : action before with
  | error error after => rw [EStateM.bind, run]; simpa only [run] using frame
  | ok value after =>
      rw [run] at frame
      rw [EStateM.bind, run]
      dsimp only
      have final := rest value after
      cases finished : next value after <;> rw [finished] at final <;> exact frame.trans final

theorem internE (expr : KExpr .anon) : IngressM.FramesState (IngressM.internE expr) :=
  fun before => ⟨before.consts, before.blocks, _, rfl⟩

theorem internU (level : KUniv .anon) : IngressM.FramesState (IngressM.internU level) :=
  fun before => ⟨before.consts, before.blocks, _, rfl⟩

theorem forInList (items : List α) (initial : β) (step : α → β → IngressM (ForInStep β))
    (framed : ∀ item value, IngressM.FramesState (step item value)) : IngressM.FramesState (forIn items initial step) := by
  induction items generalizing initial with
  | nil => exact pure _
  | cons item rest ih =>
      rw [List.forIn_cons]
      apply bind (framed item initial)
      intro next
      cases next with
      | done value => exact pure _
      | yield value => exact ih value

theorem forInRange (range : Std.Legacy.Range) (initial : α)
    (step : Nat → α → IngressM (ForInStep α))
    (framed : ∀ index value, IngressM.FramesState (step index value)) : IngressM.FramesState (forIn range initial step) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact forInList _ _ _ framed

theorem forInArray (items : Array α) (initial : β) (step : α → β → IngressM (ForInStep β))
    (framed : ∀ item value, IngressM.FramesState (step item value)) :
    IngressM.FramesState (forIn items initial step) := by
  rcases items with ⟨items⟩
  simp only [List.forIn_toArray]
  exact forInList _ _ _ framed

theorem forInList' (items : List α) (initial : β)
    (step : (item : α) → item ∈ items → β → IngressM (ForInStep β))
    (framed : ∀ item member value, IngressM.FramesState (step item member value)) :
    IngressM.FramesState (forIn' items initial step) := by
  induction items generalizing initial with
  | nil => exact pure _
  | cons item rest ih =>
      rw [List.forIn'_cons]
      apply bind (framed item (by simp) initial)
      intro next
      cases next with
      | done value => exact pure _
      | yield value => exact ih value _ (fun _ _ _ => framed _ _ _)

theorem forInRange' (range : Std.Legacy.Range) (initial : α)
    (step : (index : Nat) → index ∈ range → α → IngressM (ForInStep α))
    (framed : ∀ index member value, IngressM.FramesState (step index member value)) :
    IngressM.FramesState (forIn' range initial step) := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  exact forInList' _ _ _ (fun _ _ _ => framed _ _ _)

theorem ingressUnivTree (root : Ixon.Univ) : IngressM.FramesState (_root_.Ix.Kernel.ingressUnivTree root) := by
  unfold _root_.Ix.Kernel.ingressUnivTree
  apply bind (forInRange _ _ _ ?_)
  · intro state
    dsimp only
    split
    · exact fun _ => .refl _
    · split
      · exact pure _
      · exact throw _
  · intro index pair
    rcases pair with ⟨stack, values⟩
    dsimp only
    split
    · exact pure _
    · generalize stack.back! = frame
      cases frame with
      | process level =>
          cases level <;> first
          | exact pure _
          | exact bind (internU _) (fun _ => pure _)
      | succ | max | imax => exact bind (internU _) (fun _ => pure _)

end IngressM.FramesState

def ConvM.FramesState (action : ConvM α) : Prop := ∀ memo, IngressM.FramesState (action.run memo)

namespace ConvM.FramesState

theorem pure (value : α) : ConvM.FramesState (Pure.pure value) := by
  intro memo
  exact IngressM.FramesState.pure _

theorem throw (error : String) : ConvM.FramesState (throw error : ConvM α) := by
  intro memo
  exact IngressM.FramesState.throw _

theorem get : ConvM.FramesState (get : ConvM ConvState) := by
  intro memo
  exact IngressM.FramesState.pure _

theorem modify (f : ConvState → ConvState) : ConvM.FramesState (_root_.modify f : ConvM PUnit) := by
  intro memo
  exact IngressM.FramesState.pure _

theorem bind {action : ConvM α} {next : α → ConvM β}
    (first : ConvM.FramesState action) (rest : ∀ value, ConvM.FramesState (next value)) :
    ConvM.FramesState (action >>= next) := by
  intro memo
  simp only [StateT.run_bind]
  exact IngressM.FramesState.bind (first memo) (fun pair => rest pair.1 pair.2)

theorem lift {action : IngressM α} (frame : IngressM.FramesState action) :
    ConvM.FramesState (monadLift action : ConvM α) := by
  intro memo
  simp only [StateT.run_monadLift]
  exact IngressM.FramesState.bind frame (fun _ => IngressM.FramesState.pure _)

theorem forInList (items : List α) (initial : β) (step : α → β → ConvM (ForInStep β))
    (framed : ∀ item value, ConvM.FramesState (step item value)) : ConvM.FramesState (forIn items initial step) := by
  induction items generalizing initial with
  | nil => exact pure _
  | cons item rest ih =>
      rw [List.forIn_cons]
      apply bind (framed item initial)
      intro next
      cases next with
      | done value => exact pure _
      | yield value => exact ih value

theorem forInRange (range : Std.Legacy.Range) (initial : α)
    (step : Nat → α → ConvM (ForInStep α))
    (framed : ∀ index value, ConvM.FramesState (step index value)) : ConvM.FramesState (forIn range initial step) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact forInList _ _ _ framed

theorem forInArray (items : Array α) (initial : β) (step : α → β → ConvM (ForInStep β))
    (framed : ∀ item value, ConvM.FramesState (step item value)) : ConvM.FramesState (forIn items initial step) := by
  rcases items with ⟨items⟩
  simp only [List.forIn_toArray]
  exact forInList _ _ _ framed

theorem ingressUnivIdx (ctx : IngressCtx) (index : UInt64) :
    ConvM.FramesState (_root_.Ix.Kernel.ingressUnivIdx ctx index) := by
  unfold _root_.Ix.Kernel.ingressUnivIdx
  apply bind get
  intro memo
  split
  · exact pure _
  · split
    · apply bind (lift (IngressM.FramesState.ingressUnivTree _))
      intro level
      exact bind (modify _) (fun _ => pure _)
    · exact fun memo before => .refl _

theorem ingressUnivArgs (ctx : IngressCtx) (indices : Array UInt64) :
    ConvM.FramesState (_root_.Ix.Kernel.ingressUnivArgs ctx indices) := by
  unfold _root_.Ix.Kernel.ingressUnivArgs
  apply bind (forInArray _ _ _ ?_)
  · intro result
    exact pure _
  · intro index state
    exact bind (ingressUnivIdx ctx index) (fun _ => pure _)

theorem ingressExpr (env : Ixon.Env) (ctx : IngressCtx) (root : Ixon.Expr) :
    ConvM.FramesState (_root_.Ix.Kernel.ingressExpr env ctx root) := by
  unfold _root_.Ix.Kernel.ingressExpr
  apply bind (forInRange _ _ _ ?_)
  · intro state
    dsimp only
    split
    · exact fun _ _ => .refl _
    · split
      · split
        · exact fun _ _ => .refl _
        · exact pure _
      · exact throw _
  · intro index state
    rcases state with ⟨stack, values, active⟩
    dsimp only
    split
    · exact pure _
    · generalize stack.back! = frame
      cases frame with
      | process expr =>
          cases expr with
          | share idx =>
              apply bind get
              intro memo
              split
              · exact pure _
              · split
                · split
                  · exact fun _ _ => .refl _
                  · exact pure _
                · exact fun _ _ => .refl _
          | var idx => exact bind (lift (IngressM.FramesState.internE _)) (fun _ => pure _)
          | sort idx =>
              exact bind (ingressUnivIdx ctx idx) fun _ =>
                bind (lift (IngressM.FramesState.internE _)) (fun _ => pure _)
          | ref idx levels | recur idx levels =>
              dsimp only
              split
              · exact bind (ingressUnivArgs ctx levels) fun _ =>
                  bind (lift (IngressM.FramesState.internE _)) (fun _ => pure _)
              · exact fun _ _ => .refl _
          | nat idx =>
              dsimp only
              split
              · split
                · exact bind (lift (IngressM.FramesState.internE _)) (fun _ => pure _)
                · exact fun _ _ => .refl _
              · exact fun _ _ => .refl _
          | str idx =>
              dsimp only
              split
              · split
                · split
                  · exact bind (lift (IngressM.FramesState.internE _)) (fun _ => pure _)
                  · exact fun _ _ => .refl _
                · exact fun _ _ => .refl _
              · exact fun _ _ => .refl _
          | prj idx field value =>
              dsimp only
              split
              · exact pure _
              · exact fun _ _ => .refl _
          | app | lam | all | letE => exact pure _
      | appDone | lamDone | allDone | letDone | prjDone =>
          exact bind (lift (IngressM.FramesState.internE _)) (fun _ => pure _)
      | cacheShare idx => exact bind (modify _) (fun _ => pure _)

end ConvM.FramesState

namespace KEnv.IngressFrame

theorem insertEntriesState (before : AnonEnv) (entries : Array Entry) :
    KEnv.IngressFrame before (_root_.Ix.Kernel.insertEntriesState before entries) :=
  foldl _ _ _ (fun state entry => insert state entry.1 entry.2)

theorem insertMutsEntriesState (before : AnonEnv) (entries : Array Entry) :
    KEnv.IngressFrame before (_root_.Ix.Kernel.insertMutsEntriesState before entries) := by
  unfold _root_.Ix.Kernel.insertMutsEntriesState
  dsimp only
  split
  · exact (insertBlock _ _ _).trans (insertEntriesState _ _)
  · exact insertEntriesState _ _

end KEnv.IngressFrame

namespace IngressM.FramesState

theorem guardReserved (entries : Array Entry) :
    IngressM.FramesState (_root_.Ix.Kernel.guardReserved entries) := by
  unfold _root_.Ix.Kernel.guardReserved
  apply bind (forInArray _ _ _ ?_)
  · intro _; exact pure _
  · intro entry state
    rcases entry with ⟨id, constant⟩
    dsimp only
    split <;> exact fun _ => .refl _

theorem insertStandaloneEntries (entries : Array Entry) :
    IngressM.FramesState (_root_.Ix.Kernel.insertStandaloneEntries entries) := by
  unfold _root_.Ix.Kernel.insertStandaloneEntries
  apply bind (guardReserved entries)
  intro _
  apply modifyGet
  intro before
  dsimp only
  rw [← Array.foldl_toList]
  exact KEnv.IngressFrame.foldl _ _ _ fun state entry =>
    (KEnv.IngressFrame.insert state entry.1 entry.2).trans
      (KEnv.IngressFrame.insertBlock _ _ _)

theorem insertMutsEntries (entries : Array Entry) :
    IngressM.FramesState (_root_.Ix.Kernel.insertMutsEntries entries) := by
  unfold _root_.Ix.Kernel.insertMutsEntries
  exact bind (guardReserved entries) fun _ => modifyGet _ fun before =>
    KEnv.IngressFrame.insertMutsEntriesState before entries

theorem ingressDefnAnon (env : Ixon.Env) (defn : Ixon.Definition)
    (id : KId .anon) (constant : Ixon.Constant) (block : KId .anon)
    (mutCtx : Array (KId .anon)) (hints : Option Lean.ReducibilityHints) :
    IngressM.FramesState (_root_.Ix.Kernel.ingressDefnAnon env defn id constant block mutCtx hints) := by
  unfold _root_.Ix.Kernel.ingressDefnAnon
  apply bind (ConvM.FramesState.ingressExpr _ _ _ {})
  intro typed
  exact bind (ConvM.FramesState.ingressExpr _ _ _ typed.2) (fun _ => pure _)

theorem ingressRecursorAnon (env : Ixon.Env) (recursor : Ixon.Recursor)
    (id : KId .anon) (constant : Ixon.Constant) (block : KId .anon)
    (mutCtx : Array (KId .anon)) :
    IngressM.FramesState (_root_.Ix.Kernel.ingressRecursorAnon env recursor id constant block mutCtx) := by
  unfold _root_.Ix.Kernel.ingressRecursorAnon
  apply bind (ConvM.FramesState.ingressExpr _ _ _ {})
  intro typed
  apply bind (forInArray _ _ _ ?_)
  · intro _; exact pure _
  · intro rule state
    exact bind (ConvM.FramesState.ingressExpr _ _ _ _) (fun _ => pure _)

theorem ingressAnonInductive (env : Ixon.Env) (ind : Ixon.Inductive)
    (id : KId .anon) (constant : Ixon.Constant) (block : KId .anon)
    (index : UInt64) (ctorAddrs : Array Address) (mutCtx : Array (KId .anon)) :
    IngressM.FramesState
      (_root_.Ix.Kernel.ingressAnonInductive env ind id constant block index ctorAddrs mutCtx) := by
  unfold _root_.Ix.Kernel.ingressAnonInductive
  split
  · exact fun _ => .refl _
  · apply bind (ConvM.FramesState.ingressExpr _ _ _ {})
    intro typed
    apply bind (forInRange' _ _ _ ?_)
    · intro _; exact pure _
    · intro position member state
      exact bind (ConvM.FramesState.ingressExpr _ _ _ _) (fun _ => pure _)

theorem ingressAnonStandalone (env : Ixon.Env) (addr : Address) (constant : Ixon.Constant) :
    IngressM.FramesState (_root_.Ix.Kernel.ingressAnonStandalone env addr constant) := by
  unfold _root_.Ix.Kernel.ingressAnonStandalone
  dsimp only
  split
  · exact bind (ingressDefnAnon _ _ _ _ _ _ _) fun entries =>
      bind (insertStandaloneEntries entries) fun _ => pure _
  · exact bind (ingressRecursorAnon _ _ _ _ _ _) fun entries =>
      bind (insertStandaloneEntries entries) fun _ => pure _
  · apply bind (ConvM.FramesState.ingressExpr _ _ _ {})
    intro typed
    simp only [pure_bind]
    exact bind (insertStandaloneEntries _) fun _ => pure _
  · apply bind (ConvM.FramesState.ingressExpr _ _ _ {})
    intro typed
    simp only [pure_bind]
    exact bind (insertStandaloneEntries _) fun _ => pure _
  · exact fun _ => .refl _

theorem prepareAnonBlock (env : Ixon.Env) (constant : Ixon.Constant) (addr : Address) :
    IngressM.FramesState (_root_.Ix.Kernel.prepareAnonBlock env constant addr) := by
  unfold _root_.Ix.Kernel.prepareAnonBlock
  split
  · dsimp only
    apply bind (forInRange' _ _ _ ?_)
    · intro _; exact pure _
    · intro index member state
      split
      · apply bind
        · split <;> exact fun _ => .refl _
        · intro _
          exact bind (ingressDefnAnon _ _ _ _ _ _ _) (fun _ => pure _)
      · apply bind
        · split <;> exact fun _ => .refl _
        · intro _
          exact bind (ingressRecursorAnon _ _ _ _ _ _) (fun _ => pure _)
      · apply bind
        · split <;> exact fun _ => .refl _
        · intro _
          apply bind (forInRange' _ _ _ ?_)
          · intro _
            exact bind (ingressAnonInductive _ _ _ _ _ _ _ _) (fun _ => pure _)
          · intro position present state
            split <;> exact fun _ => .refl _
  · exact fun _ => .refl _

theorem ingressAnonBlockWithTrace (env : Ixon.Env) (constant : Ixon.Constant) (addr : Address) :
    IngressM.FramesState (_root_.Ix.Kernel.ingressAnonBlockWithTrace env constant addr) := by
  unfold _root_.Ix.Kernel.ingressAnonBlockWithTrace
  exact bind (prepareAnonBlock env constant addr) fun trace =>
    bind (insertMutsEntries trace.allEntries) fun _ => pure _

theorem ingressAnonBlock (env : Ixon.Env) (constant : Ixon.Constant) (addr : Address) :
    IngressM.FramesState (_root_.Ix.Kernel.ingressAnonBlock env constant addr) := by
  unfold _root_.Ix.Kernel.ingressAnonBlock
  exact bind (ingressAnonBlockWithTrace env constant addr) fun _ => pure _

/-- The actual lazy callback changes only ingress-owned fields, for every
input and both outcomes. No callback-specific frame is assumed. -/
theorem ingressAnonAddrShallow (env : Ixon.Env) (addr : Address) (verify : Bool) :
    IngressM.FramesState (_root_.Ix.Kernel.ingressAnonAddrShallow env addr verify) := by
  unfold _root_.Ix.Kernel.ingressAnonAddrShallow
  apply bind (liftExcept _)
  intro found
  cases found with
  | none => exact pure _
  | some constant =>
      dsimp only
      split
      · apply bind get
        intro before
        split
        · exact pure _
        · apply bind (liftExcept _)
          intro block
          cases block with
          | none => exact fun _ => .refl _
          | some blockConstant => exact bind (ingressAnonBlock _ _ _) fun _ => pure _
      · exact bind (ingressAnonStandalone _ _ _) fun _ => pure _

end IngressM.FramesState

end Ix.Kernel
