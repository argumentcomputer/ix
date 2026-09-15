/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Ix.Kernel.Verify.Consistency.BlockCache
import Ix.Kernel.Driver
import Init.Data.Range.Lemmas

/-!
# Intern-table coherence through production ingress

Both outcomes of the bounded conversion machines preserve key coherence.
No collision-freedom or semantic source-agreement premise is needed for this
structural invariant. Failed conversion retains its coherent partial state.
-/

namespace Ix.Kernel.Consistency

private def InternCoherent (action : InternIngressM α) : Prop :=
  ∀ before, before.WF → match action before with
    | .ok _ after | .error _ after => after.WF

private theorem intern_pure (value : α) : InternCoherent (pure value) :=
  fun _ coherent => coherent

private theorem intern_throw (err : IngressErr) : InternCoherent (throw err : InternIngressM α) :=
  fun _ coherent => coherent

private theorem intern_throw_bind (err : IngressErr) (next : α → InternIngressM β) :
    InternCoherent ((throw err : InternIngressM α) >>= next) := fun _ coherent => coherent

private theorem intern_bind {action : InternIngressM α} {next : α → InternIngressM β}
    (first : InternCoherent action) (rest : ∀ value, InternCoherent (next value)) :
    InternCoherent (action >>= next) := by
  intro before coherent
  have preserved := first before coherent
  change (match EStateM.bind action next before with
    | .ok _ after | .error _ after => after.WF)
  rw [EStateM.bind]
  cases run : action before <;> rw [run] at preserved
  · exact rest _ _ preserved
  · exact preserved

private theorem intern_expr (term : KExpr .anon) : InternCoherent (InternIngressM.internE term) :=
  fun _ coherent => coherent.internExpr term

private theorem intern_univ (level : KUniv .anon) : InternCoherent (InternIngressM.internU level) :=
  fun _ coherent => coherent.internUniv level

private def ConvCoherent (action : InternConvM α) : Prop :=
  ∀ cache, InternCoherent (action cache)

private theorem conv_pure (value : α) : ConvCoherent (pure value) :=
  fun _ => intern_pure _

private theorem conv_throw (err : IngressErr) : ConvCoherent (throw err : InternConvM α) :=
  fun _ => intern_throw _

private theorem conv_throw_bind (err : IngressErr) (next : α → InternConvM β) :
    ConvCoherent ((throw err : InternConvM α) >>= next) := fun _ _ coherent => coherent

private theorem conv_bind {action : InternConvM α} {next : α → InternConvM β}
    (first : ConvCoherent action) (rest : ∀ value, ConvCoherent (next value)) :
    ConvCoherent (action >>= next) := by
  intro cache
  change InternCoherent (EStateM.bind (action cache) (fun (value, cache) => next value cache))
  exact intern_bind (first cache) (fun (value, cache) => rest value cache)

private theorem conv_lift {action : InternIngressM α} (coherent : InternCoherent action) :
    ConvCoherent (liftM action) := by
  intro cache
  exact intern_bind coherent (fun _ => intern_pure _)

private theorem conv_get : ConvCoherent (get : InternConvM ConvState) :=
  fun _ => intern_pure _

private theorem conv_modify (update : ConvState → ConvState) :
    ConvCoherent (modify update : InternConvM Unit) := fun _ => intern_pure _

private theorem forIn_keeps {m : Type → Type} [Monad m]
    (P : {α : Type} → m α → Prop)
    (hpure : ∀ {α} (value : α), P (pure value))
    (hbind : ∀ {α β} {action : m α} {next : α → m β},
      P action → (∀ value, P (next value)) → P (action >>= next))
    (items : List α) (initial : β) (body : α → β → m (ForInStep β))
    (step : ∀ item state, P (body item state)) : P (forIn items initial body) := by
  induction items generalizing initial with
  | nil => simpa only [List.forIn_nil] using hpure initial
  | cons item rest ih =>
      rw [List.forIn_cons]
      apply hbind (step item initial)
      intro result
      cases result with
      | done state => exact hpure state
      | yield state => exact ih state

private theorem array_forIn_keeps {m : Type → Type} [Monad m]
    (P : {α : Type} → m α → Prop)
    (hpure : ∀ {α} (value : α), P (pure value))
    (hbind : ∀ {α β} {action : m α} {next : α → m β},
      P action → (∀ value, P (next value)) → P (action >>= next))
    (items : Array α) (initial : β) (body : α → β → m (ForInStep β))
    (step : ∀ item state, P (body item state)) : P (forIn items initial body) := by
  rw [← Array.forIn_toList]
  exact forIn_keeps P hpure hbind items.toList initial body step

private theorem forIn'_keeps {m : Type → Type} [Monad m]
    (P : {α : Type} → m α → Prop)
    (hpure : ∀ {α} (value : α), P (pure value))
    (hbind : ∀ {α β} {action : m α} {next : α → m β},
      P action → (∀ value, P (next value)) → P (action >>= next))
    (items : List α) (initial : β) (body : (item : α) → item ∈ items → β → m (ForInStep β))
    (step : ∀ item member state, P (body item member state)) : P (forIn' items initial body) := by
  induction items generalizing initial with
  | nil => simpa only [List.forIn'_nil] using hpure initial
  | cons item rest ih =>
      rw [List.forIn'_cons]
      apply hbind (step item (List.mem_cons_self) initial)
      intro result
      cases result with
      | done state => exact hpure state
      | yield state =>
          exact ih state _ (fun item member state => step item (List.mem_cons_of_mem _ member) state)

private theorem range_forIn'_keeps {m : Type → Type} [Monad m]
    (P : {α : Type} → m α → Prop)
    (hpure : ∀ {α} (value : α), P (pure value))
    (hbind : ∀ {α β} {action : m α} {next : α → m β},
      P action → (∀ value, P (next value)) → P (action >>= next))
    (range : Std.Legacy.Range) (initial : β)
    (body : (item : Nat) → item ∈ range → β → m (ForInStep β))
    (step : ∀ item member state, P (body item member state)) : P (forIn' range initial body) := by
  rw [Std.Legacy.Range.forIn'_eq_forIn'_range']
  exact forIn'_keeps P hpure hbind _ initial _ (fun item _ state => step item _ state)

private theorem convertUnivStep_coherent (stack : Array UFrame) (values : Array (KUniv .anon)) :
    InternCoherent (convertUnivStep stack values) := by
  dsimp only [convertUnivStep]
  cases stack.back! with
  | process level =>
      cases level <;> first
        | exact intern_pure _
        | exact intern_bind (intern_univ _) (fun _ => intern_pure _)
  | succ | max | imax => exact intern_bind (intern_univ _) (fun _ => intern_pure _)

private theorem convertUnivLoop_coherent (fuel : Nat) (stack : Array UFrame)
    (values : Array (KUniv .anon)) : InternCoherent (convertUnivLoop fuel stack values) := by
  induction fuel generalizing stack values with
  | zero =>
      unfold convertUnivLoop
      split
      · cases values.back? <;> first | exact intern_pure _ | exact intern_throw _
      · exact intern_throw _
  | succ fuel ih =>
      unfold convertUnivLoop
      split
      · cases values.back? <;> first | exact intern_pure _ | exact intern_throw _
      · exact intern_bind (convertUnivStep_coherent stack values) (fun (stack, values) => ih stack values)

/-- Actual universe conversion preserves coherent keys, on both outcomes. -/
theorem convertUnivTree_coherent (root : Ixon.Univ) (before : InternTable .anon)
    (coherent : before.WF) :
    match convertUnivTree root before with
    | .ok _ after | .error _ after => after.WF := by
  unfold convertUnivTree
  have preserved := convertUnivLoop_coherent (2 * univIngressSize root) #[.process root] #[] before coherent
  cases run : convertUnivLoop (2 * univIngressSize root) #[.process root] #[] before <;>
    rw [run] at preserved <;> exact preserved

private theorem convertUnivIdx_coherent (ctx : IngressCtx) (idx : UInt64) :
    ConvCoherent (convertUnivIdx ctx idx) := by
  unfold convertUnivIdx
  apply conv_bind conv_get
  intro cache
  cases cache.univCache[idx]? with
  | some value => exact conv_pure _
  | none =>
      cases ctx.univs[idx.toNat]? with
      | none => exact conv_throw _
      | some level =>
          have tree : InternCoherent (convertUnivTree level) := by
            intro before coherent
            have preserved := convertUnivTree_coherent level before coherent
            cases run : convertUnivTree level before <;> rw [run] at preserved <;> exact preserved
          apply conv_bind (conv_lift tree)
          intro value
          exact conv_bind (conv_modify _) (fun _ => conv_pure _)

private theorem convertUnivArgs_coherent (ctx : IngressCtx) (idxs : Array UInt64) :
    ConvCoherent (convertUnivArgs ctx idxs) := by
  unfold convertUnivArgs
  apply conv_bind _ (fun _ => conv_pure _)
  apply array_forIn_keeps (@ConvCoherent) (@conv_pure) (@conv_bind)
  intro idx out
  exact conv_bind (convertUnivIdx_coherent ctx idx) (fun _ => conv_pure _)

private theorem convertExprStep_coherent (source : Ixon.Env) (ctx : IngressCtx)
    (stack : Array EFrame) (values : Array (KExpr .anon)) :
    ConvCoherent (convertExprStep source ctx stack values) := by
  dsimp only [convertExprStep]
  cases stack.back! with
  | process term =>
      cases term with
      | share idx =>
          apply conv_bind conv_get
          intro cache
          cases cache.exprCache[idx]? with
          | some value => exact conv_pure _
          | none => cases ctx.sharing[idx.toNat]? <;> first
              | exact conv_pure _
              | exact conv_throw_bind _ _
      | var idx => exact conv_bind (conv_lift (intern_expr _)) (fun _ => conv_pure _)
      | sort idx =>
          exact conv_bind (convertUnivIdx_coherent ctx idx)
            (fun _ => conv_bind (conv_lift (intern_expr _)) (fun _ => conv_pure _))
      | ref idx arguments =>
          dsimp only
          cases ctx.refs[idx.toNat]? with
          | none => exact conv_throw_bind _ _
          | some addr =>
              dsimp only
              exact conv_bind (convertUnivArgs_coherent ctx arguments)
                (fun _ => conv_bind (conv_lift (intern_expr _)) (fun _ => conv_pure _))
      | recur idx arguments =>
          dsimp only
          cases ctx.mutCtx[idx.toNat]? with
          | none => exact conv_throw_bind _ _
          | some id =>
              exact conv_bind (convertUnivArgs_coherent ctx arguments)
                (fun _ => conv_bind (conv_lift (intern_expr _)) (fun _ => conv_pure _))
      | nat idx =>
          dsimp only
          cases ctx.refs[idx.toNat]? with
          | none => exact conv_throw_bind _ _
          | some addr =>
              dsimp only
              cases source.getBlob? addr with
              | none => exact conv_throw_bind _ _
              | some bytes => exact conv_bind (conv_lift (intern_expr _)) (fun _ => conv_pure _)
      | str idx =>
          dsimp only
          cases ctx.refs[idx.toNat]? with
          | none => exact conv_throw_bind _ _
          | some addr =>
              dsimp only
              cases source.getBlob? addr with
              | none => exact conv_throw_bind _ _
              | some bytes =>
                  dsimp only
                  cases String.fromUTF8? bytes with
                  | none => exact conv_throw_bind _ _
                  | some value => exact conv_bind (conv_lift (intern_expr _)) (fun _ => conv_pure _)
      | app | lam | all | letE => exact conv_pure _
      | prj idx field value =>
          dsimp only
          cases ctx.refs[idx.toNat]? <;> first
          | exact conv_pure _
          | exact conv_throw_bind _ _
  | appDone | lamDone | allDone | letDone | prjDone =>
      exact conv_bind (conv_lift (intern_expr _)) (fun _ => conv_pure _)
  | cacheShare idx => exact conv_bind (conv_modify _) (fun _ => conv_pure _)

private theorem convertExprLoop_coherent (source : Ixon.Env) (ctx : IngressCtx)
    (fuel : Nat) (stack : Array EFrame) (values : Array (KExpr .anon)) :
    ConvCoherent (convertExprLoop source ctx fuel stack values) := by
  induction fuel generalizing stack values with
  | zero =>
      unfold convertExprLoop
      split
      · cases values.back? with
        | none => exact conv_throw _
        | some value =>
            dsimp only
            split
            · exact conv_throw_bind _ _
            · exact conv_pure _
      · exact conv_throw _
  | succ fuel ih =>
      unfold convertExprLoop
      split
      · cases values.back? with
        | none => exact conv_throw _
        | some value =>
            dsimp only
            split
            · exact conv_throw_bind _ _
            · exact conv_pure _
      · exact conv_bind (convertExprStep_coherent source ctx stack values)
          (fun (stack, values) => ih stack values)

private theorem convertExpr_preserves (source : Ixon.Env) (ctx : IngressCtx) (root : Ixon.Expr) :
    ConvCoherent (convertExpr source ctx root) := by
  unfold convertExpr
  exact convertExprLoop_coherent source ctx _ _ _

/-- Expression conversion preserves coherent intern keys independently of
the source's semantic validity, including failure with partial progress. -/
theorem convertExpr_coherent (source : Ixon.Env) (ctx : IngressCtx) (root : Ixon.Expr)
    (cache : ConvState) (before : InternTable .anon) (coherent : before.WF) :
    match convertExpr source ctx root cache before with
    | .ok _ after | .error _ after => after.WF := by
  have preserved := convertExpr_preserves source ctx root cache before coherent
  cases run : convertExpr source ctx root cache before <;> rw [run] at preserved <;> exact preserved

private theorem convertDefnAnon_preserves (source : Ixon.Env) (defn : Ixon.Definition)
    (constant : Ixon.Constant) (block : KId .anon) (mutCtx : Array (KId .anon))
    (hints : Option Lean.ReducibilityHints) :
    InternCoherent (convertDefnAnon source defn constant block mutCtx hints) := by
  unfold convertDefnAnon
  apply intern_bind (convertExpr_preserves source _ defn.typ {})
  intro result
  exact intern_bind (convertExpr_preserves source _ defn.value result.2) (fun _ => intern_pure _)

private theorem convertRecursorAnon_preserves (source : Ixon.Env) (rec : Ixon.Recursor)
    (constant : Ixon.Constant) (block : KId .anon) (mutCtx : Array (KId .anon)) :
    InternCoherent (convertRecursorAnon source rec constant block mutCtx) := by
  unfold convertRecursorAnon
  apply intern_bind (convertExpr_preserves source _ rec.typ {})
  intro result
  apply intern_bind _ (fun _ => intern_pure _)
  apply array_forIn_keeps (@InternCoherent) (@intern_pure) (@intern_bind)
  intro rule state
  exact intern_bind (convertExpr_preserves source _ rule.rhs _) (fun _ => intern_pure _)

private theorem convertAnonInductive_preserves (source : Ixon.Env) (ind : Ixon.Inductive)
    (self : KId .anon) (constant : Ixon.Constant) (block : KId .anon) (idx : UInt64)
    (ctorAddrs : Array Address) (mutCtx : Array (KId .anon)) :
    InternCoherent (convertAnonInductive source ind self constant block idx ctorAddrs mutCtx) := by
  unfold convertAnonInductive
  split
  · exact intern_throw_bind _ _
  · apply intern_bind (convertExpr_preserves source _ ind.typ {})
    intro result
    apply intern_bind _ (fun _ => intern_pure _)
    apply range_forIn'_keeps (@InternCoherent) (@intern_pure) (@intern_bind)
    intro cidx member state
    exact intern_bind (convertExpr_preserves source _ _ _) (fun _ => intern_pure _)

private theorem convertAnonStandalone_preserves (source : Ixon.Env) (addr : Address)
    (constant : Ixon.Constant) : InternCoherent (convertAnonStandalone source addr constant) := by
  unfold convertAnonStandalone
  cases constant.info with
  | defn defn => exact convertDefnAnon_preserves source defn constant _ _ _
  | recr rec => exact convertRecursorAnon_preserves source rec constant _ _
  | axio axio => exact intern_bind (convertExpr_preserves source _ axio.typ {}) (fun _ => intern_pure _)
  | quot quot => exact intern_bind (convertExpr_preserves source _ quot.typ {}) (fun _ => intern_pure _)
  | muts | dPrj | iPrj | rPrj | cPrj => exact intern_throw _

private theorem convertAnonBlock_preserves (source : Ixon.Env) (constant : Ixon.Constant)
    (addr : Address) : InternCoherent (convertAnonBlock source constant addr) := by
  unfold convertAnonBlock
  cases constant.info with
  | defn | recr | axio | quot | dPrj | iPrj | rPrj | cPrj => exact intern_throw _
  | muts members =>
      apply intern_bind _ (fun _ => intern_pure _)
      apply range_forIn'_keeps (@InternCoherent) (@intern_pure) (@intern_bind)
      intro idx member state
      dsimp only
      cases members[idx] with
      | defn defn =>
          apply intern_bind
          · split
            · exact intern_throw _
            · exact intern_pure _
          · intro _
            exact intern_bind (convertDefnAnon_preserves source defn constant _ _ _)
              (fun _ => intern_pure _)
      | recr rec =>
          apply intern_bind
          · split
            · exact intern_throw _
            · exact intern_pure _
          · intro _
            exact intern_bind (convertRecursorAnon_preserves source rec constant _ _)
              (fun _ => intern_pure _)
      | indc ind =>
          apply intern_bind
          · split
            · exact intern_throw _
            · exact intern_pure _
          · intro _
            apply intern_bind
            · apply range_forIn'_keeps (@InternCoherent) (@intern_pure) (@intern_bind)
              intro cidx member state
              apply intern_bind
              · split
                · exact intern_throw _
                · exact intern_pure _
              · intro _; exact intern_pure _
            · intro _
              exact intern_bind (convertAnonInductive_preserves source ind _ constant _ _ _ _)
                (fun _ => intern_pure _)

/-- Standalone conversion derives coherence for definitions, recursors,
axioms, and quotients, including failed conversion and rejected source forms. -/
theorem convertAnonStandalone_coherent (source : Ixon.Env) (addr : Address)
    (constant : Ixon.Constant) (before : InternTable .anon) (coherent : before.WF) :
    match convertAnonStandalone source addr constant before with
    | .ok _ after | .error _ after => after.WF := by
  have preserved := convertAnonStandalone_preserves source addr constant before coherent
  cases run : convertAnonStandalone source addr constant before <;>
    rw [run] at preserved <;> exact preserved

/-- Every block member and constructor uses the same coherent intern tables;
an error in a later member retains the coherent effects of earlier members. -/
theorem convertAnonBlock_coherent (source : Ixon.Env) (constant : Ixon.Constant)
    (addr : Address) (before : InternTable .anon) (coherent : before.WF) :
    match convertAnonBlock source constant addr before with
    | .ok _ after | .error _ after => after.WF := by
  have preserved := convertAnonBlock_preserves source constant addr before coherent
  cases run : convertAnonBlock source constant addr before <;> rw [run] at preserved <;> exact preserved

private def IngressCoherent (action : IngressM α) : Prop :=
  ∀ before, before.intern.WF → match action before with
    | .ok _ after | .error _ after => after.intern.WF

private theorem ingress_pure (value : α) : IngressCoherent (pure value) := fun _ coherent => coherent

private theorem ingress_throw (err : IngressErr) : IngressCoherent (throw err : IngressM α) :=
  fun _ coherent => coherent

private theorem ingress_bind {action : IngressM α} {next : α → IngressM β}
    (first : IngressCoherent action) (rest : ∀ value, IngressCoherent (next value)) :
    IngressCoherent (action >>= next) := by
  intro before coherent
  have preserved := first before coherent
  change (match EStateM.bind action next before with
    | .ok _ after | .error _ after => after.intern.WF)
  rw [EStateM.bind]
  cases run : action before <;> rw [run] at preserved
  · exact rest _ _ preserved
  · exact preserved

private theorem ingress_liftExcept (result : Except IngressErr α) :
    IngressCoherent (IngressM.liftExcept result) := by
  cases result with
  | ok value => exact ingress_pure value
  | error err => exact ingress_throw err

private theorem ingress_runIntern {action : InternIngressM α} (preserves : InternCoherent action) :
    IngressCoherent (IngressM.runIntern action) := by
  intro before coherent
  have preserved := preserves before.intern coherent
  unfold IngressM.runIntern
  cases run : action before.intern <;> rw [run] at preserved <;> exact preserved

private theorem insert_list_intern (entries : List Entry) (before : AnonEnv) :
    (entries.foldl (fun env entry => env.insert entry.1 entry.2) before).intern = before.intern := by
  induction entries generalizing before with
  | nil => rfl
  | cons entry rest ih => exact ih (before.insert entry.1 entry.2)

/-- Publication does not access the intern tables, regardless of declaration
overlap. Coherence and cache preservation have different requirements. -/
theorem insertMutsEntriesState_intern (entries : Array Entry) (before : AnonEnv) :
    (insertMutsEntriesState before entries).intern = before.intern := by
  unfold insertMutsEntriesState insertEntriesState
  rw [insert_list_intern]
  split <;> rfl

private theorem insertMutsEntries_preserves (entries : Array Entry) :
    IngressCoherent (insertMutsEntries entries) := by
  unfold insertMutsEntries
  apply ingress_bind
  · intro before coherent
    rw [guardReserved_state]
    cases checkReserved entries <;> exact coherent
  · intro _ before coherent
    change (insertMutsEntriesState before entries).intern.WF
    rw [insertMutsEntriesState_intern]
    exact coherent

private theorem ingressAnonStandalone_preserves (source : Ixon.Env) (addr : Address)
    (constant : Ixon.Constant) : IngressCoherent (ingressAnonStandalone source addr constant) := by
  unfold ingressAnonStandalone
  apply ingress_bind (ingress_runIntern (convertAnonStandalone_preserves source addr constant))
  intro concrete
  apply ingress_bind _ (fun _ => ingress_pure _)
  intro before coherent
  rw [insertStandaloneEntries_singleton]
  cases reservedMarkerName addr <;> exact coherent

/-- Preparation derives post-state coherence from the pre-state invariant. -/
theorem prepareAnonBlock_coherent (source : Ixon.Env) (constant : Ixon.Constant)
    (addr : Address) (before : AnonEnv) (coherent : before.intern.WF) :
    match prepareAnonBlock source constant addr before with
    | .ok _ after | .error _ after => after.intern.WF := by
  have preserved := ingress_runIntern (convertAnonBlock_preserves source constant addr) before coherent
  unfold prepareAnonBlock
  cases run : IngressM.runIntern (convertAnonBlock source constant addr) before <;>
    rw [run] at preserved <;> exact preserved

private theorem ingressAnonBlockWithTrace_preserves (source : Ixon.Env) (constant : Ixon.Constant)
    (addr : Address) : IngressCoherent (ingressAnonBlockWithTrace source constant addr) := by
  unfold ingressAnonBlockWithTrace
  apply ingress_bind (ingress_runIntern (convertAnonBlock_preserves source constant addr))
  intro trace
  exact ingress_bind (insertMutsEntries_preserves trace.allEntries) (fun _ => ingress_pure _)

private theorem ingressAnonBlock_preserves (source : Ixon.Env) (constant : Ixon.Constant)
    (addr : Address) : IngressCoherent (ingressAnonBlock source constant addr) := by
  unfold ingressAnonBlock
  exact ingress_bind (ingressAnonBlockWithTrace_preserves source constant addr) (fun _ => ingress_pure _)

/-- Block publication preserves coherent intern tables on success and error,
without a freshness or compatibility premise on the declaration map. -/
theorem ingressAnonBlock_coherent (source : Ixon.Env) (constant : Ixon.Constant)
    (addr : Address) (before : AnonEnv) (coherent : before.intern.WF) :
    match ingressAnonBlock source constant addr before with
    | .ok _ after | .error _ after => after.intern.WF := by
  have preserved := ingressAnonBlock_preserves source constant addr before coherent
  cases run : ingressAnonBlock source constant addr before <;> rw [run] at preserved <;> exact preserved

private theorem ingressAnonAddrShallow_preserves (source : Ixon.Env) (addr : Address) (verify : Bool) :
    IngressCoherent (ingressAnonAddrShallow source addr verify) := by
  unfold ingressAnonAddrShallow
  apply ingress_bind (ingress_liftExcept _)
  intro optional
  cases optional with
  | none => exact ingress_pure _
  | some constant =>
      dsimp only
      cases ingressBlockAddr? addr constant.info with
      | none => exact ingress_bind (ingressAnonStandalone_preserves source addr constant) (fun _ => ingress_pure _)
      | some blockAddr =>
          apply ingress_bind (fun _ coherent => coherent)
          intro state
          split
          · exact ingress_pure _
          · apply ingress_bind (ingress_liftExcept _)
            intro optional
            cases optional with
            | none => exact ingress_throw _
            | some blockConstant =>
                exact ingress_bind (ingressAnonBlock_preserves source blockConstant blockAddr) (fun _ => ingress_pure _)

/-- The actual shallow loader preserves coherence on both outcomes, even
when materialization fails or the requested projection is already recorded. -/
theorem ingressAnonAddrShallow_coherent (source : Ixon.Env) (addr : Address) (verify : Bool)
    (before : AnonEnv) (coherent : before.intern.WF) :
    match ingressAnonAddrShallow source addr verify before with
    | .ok _ after | .error _ after => after.intern.WF := by
  have preserved := ingressAnonAddrShallow_preserves source addr verify before coherent
  cases run : ingressAnonAddrShallow source addr verify before <;> rw [run] at preserved <;> exact preserved

/-- Fault dispatch preserves coherence with the actual ingress callback.
Its fault-history update retains the post-conversion intern tables. -/
theorem lazyIngressAddr_coherent {before : TcState .anon} {addr : Address}
    (source : Ixon.Env) (verify : Bool)
    (installed : before.lazyFault = some (fun address => ingressAnonAddrShallow source address verify))
    (coherent : before.env.intern.WF) :
    match TcM.lazyIngressAddr addr before with
    | .ok _ after | .error _ after => after.env.intern.WF := by
  unfold TcM.lazyIngressAddr
  rw [installed]
  dsimp only
  by_cases faulted : before.faultedAddrs.contains addr = true
  · rw [if_pos faulted]
    exact coherent
  · rw [if_neg faulted]
    have preserved := ingressAnonAddrShallow_coherent source addr verify before.env coherent
    cases run : ingressAnonAddrShallow source addr verify before.env <;>
      rw [run] at preserved <;> exact preserved

/-- Loaded hits, actual lazy faults, misses, and errors all retain coherent
intern tables. No assertion about the callback's final state is an input. -/
theorem tryGetConst_coherent {before : TcState .anon} {id : KId .anon}
    (source : Ixon.Env) (verify : Bool)
    (installed : before.lazyFault = some (fun address => ingressAnonAddrShallow source address verify))
    (coherent : before.env.intern.WF) :
    match TcM.tryGetConst id before with
    | .ok _ after | .error _ after => after.env.intern.WF := by
  unfold TcM.tryGetConst
  change (match (EStateM.bind (get : TcM .anon (TcState .anon)) _ :
    TcM .anon (Option (KConst .anon))) before with
    | .ok _ after | .error _ after => after.env.intern.WF)
  rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) before = .ok before before from rfl]
  dsimp only
  cases before.env.get? id with
  | some concrete => exact coherent
  | none =>
      change (match (EStateM.bind (TcM.lazyIngressAddr id.addr) _ :
        TcM .anon (Option (KConst .anon))) before with
        | .ok _ after | .error _ after => after.env.intern.WF)
      have preserved := lazyIngressAddr_coherent (addr := id.addr) source verify installed coherent
      cases fault : TcM.lazyIngressAddr id.addr before with
      | error err after =>
          rw [EStateM.bind, fault]
          simpa only [fault] using preserved
      | ok value after =>
          rw [fault] at preserved
          rw [EStateM.bind, fault]
          change (match (EStateM.bind (get : TcM .anon (TcState .anon)) _ :
            TcM .anon (Option (KConst .anon))) after with
            | .ok _ state | .error _ state => state.env.intern.WF)
          rw [EStateM.bind, show (get : TcM .anon (TcState .anon)) after = .ok after after from rfl]
          dsimp only
          cases after.env.get? id with
          | some concrete => exact preserved
          | none => cases before.lazyFault.isSome <;> exact preserved

/-- Hard lookup derives post-state coherence from pre-state coherence and
the installed production loader, for success and every error path. -/
theorem getConst_coherent {before : TcState .anon} {id : KId .anon}
    (source : Ixon.Env) (verify : Bool)
    (installed : before.lazyFault = some (fun address => ingressAnonAddrShallow source address verify))
    (coherent : before.env.intern.WF) :
    match TcM.getConst id before with
    | .ok _ after | .error _ after => after.env.intern.WF := by
  unfold TcM.getConst
  change (match (EStateM.bind (TcM.tryGetConst id) _ : TcM .anon (KConst .anon)) before with
    | .ok _ after | .error _ after => after.env.intern.WF)
  have preserved := tryGetConst_coherent (id := id) source verify installed coherent
  cases tried : TcM.tryGetConst id before with
  | error err after =>
      rw [EStateM.bind, tried]
      simpa only [tried] using preserved
  | ok optional after =>
      rw [tried] at preserved
      rw [EStateM.bind, tried]
      cases optional <;> exact preserved

/-- The production lazy checker's initial intern tables are coherent. -/
theorem newLazyAnon_intern_coherent (source : Ixon.Env) :
    (TcState.newLazyAnon source).env.intern.WF :=
  InternTable.WF.empty

/-- Build the post-lookup walker resource from coherence before loading.
Finite collision freedom and level resources remain data requirements; the
coherence field is established by the actual lookup, including block loading. -/
theorem UniverseInstantiationSupport.afterVerifiedGetConst
    {before after : TcState .anon} {id : KId .anon} {concrete : KConst .anon}
    {arguments : Array (KUniv .anon)}
    (loader : VerifiedLazySupport before id.addr) (coherent : before.env.intern.WF)
    (run : TcM.getConst id before = .ok concrete after)
    (faithful : KExpr.CollisionFree fun candidate => after.env.intern.ExprSupport candidate ∨
      KExpr.InstUnivReach arguments concrete.ty candidate)
    (levels : UniverseSubstitutionSupport arguments concrete.ty) :
    UniverseInstantiationSupport after concrete.ty arguments := by
  have preserved := getConst_coherent (id := id) loader.source true loader.installed coherent
  rw [run] at preserved
  exact ⟨preserved, faithful, levels⟩

end Ix.Kernel.Consistency
