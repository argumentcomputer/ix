import Init.Data.Range.Lemmas
import Ix.Tc.Verify.Whnf.StructEta.ScopedClassifier

/-!
# Recursion-classifier and major-inductive helper effects

`computedIsRec` and `getMajorInductiveId` sit on the last effectful prefix of
the struct-eta reducer.  This slice verifies their concrete environment reads
and recursion-classification cache transactions before assigning either
helper a semantic result contract.

The `isRecCache` write rule is intentionally provenance-indexed.  A cached
`false` enables struct eta, while the provisional `true` entry suppresses
re-entrant eta.  Physical insertion alone is therefore not evidence that
either Boolean is semantically valid.
-/

namespace Ix.Tc

namespace RecM

namespace IsRecCacheUpdate

/-- Installing one provenance-certified recursion result changes only the
physical `isRecCache` partition and preserves the complete WHNF invariant. -/
theorem insert_whnfStateInv
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {ind : Address} {value : Bool}
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s)
    (hnew : CacheProvenance semantics (CacheAuthority.stable world) support
      (.isRec ind value)) :
    WhnfStateInv layer semantics trProj world support uvars Delta
      {s with env := {s.env with
        isRecCache := s.env.isRecCache.insert ind value}} := by
  rcases hI with ⟨hkernel, hctx, hlayer⟩
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact hkernel.core.of_consts_eq rfl (by
        simpa using hkernel.core.intern)
    · simpa using hkernel.internSupport
    · exact hkernel.caches.insertIsRec hnew
    · exact hkernel.equivalences
  · exact hctx.of_fields_eq rfl rfl rfl rfl (by simp)
  · cases layer <;> simpa [WhnfLayer.StateOK] using hlayer

/-- Removing a recursion result cannot invalidate any retained cache entry;
this is the exact cleanup update used after a caught `computeIsRec` error. -/
theorem erase_whnfStateInv
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {ind : Address}
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s) :
    WhnfStateInv layer semantics trProj world support uvars Delta
      {s with env := {s.env with
        isRecCache := s.env.isRecCache.erase ind}} := by
  rcases hI with ⟨hkernel, hctx, hlayer⟩
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact hkernel.core.of_consts_eq rfl (by
        simpa using hkernel.core.intern)
    · simpa using hkernel.internSupport
    · exact hkernel.caches.eraseIsRec
    · exact hkernel.equivalences
  · exact hctx.of_fields_eq rfl rfl rfl rfl (by simp)
  · cases layer <;> simpa [WhnfLayer.StateOK] using hlayer

end IsRecCacheUpdate

end RecM

namespace TcM

/-- Required constant lookup preserves an arbitrary invariant whenever the
installed lazy-fault hook does.  A no-hook miss is converted to the same
state-preserving `unknownConst` error as production. -/
theorem getConst_wf {I : TcState .anon → Prop}
    (hfault : LazyFaultPreserves I) (id : KId .anon) (s : TcState .anon) :
    TcM.WF I s (TcM.getConst id) (fun _ _ => True) := by
  unfold TcM.getConst
  apply TcM.WF.bind (TcM.tryGetConst_wf hfault id s)
  intro found after _
  cases found with
  | none => exact TcM.WF.throw fun _ => trivial
  | some c => exact TcM.WF.pure fun _ => trivial

/-- Mutual-block lookup has the same fast-read/fault/retry state contract as
constant lookup, but retains production's optional post-fault miss. -/
theorem tryGetBlock_wf {I : TcState .anon → Prop}
    (hfault : LazyFaultPreserves I) (id : KId .anon) (s : TcState .anon) :
    TcM.WF I s (TcM.tryGetBlock id) (fun _ _ => True) := by
  unfold TcM.tryGetBlock
  apply TcM.WF.bind
    (Q₁ := fun read after => read = after)
    (TcM.WF.get fun _ => rfl)
  intro read before hread
  subst read
  split
  · exact TcM.WF.pure fun _ => trivial
  · apply TcM.WF.bind
      (Q₁ := fun _ _ => True)
      (TcM.lazyIngressAddr_wf hfault id.addr before)
    intro _ afterFault _
    apply TcM.WF.bind
      (Q₁ := fun read after => read = after)
      (TcM.WF.get fun _ => rfl)
    intro read after hread
    subst read
    exact TcM.WF.pure fun _ => trivial

end TcM

namespace RecM

/-- State-only contract for the recursive WHNF calls made by helper scans.

This is intentionally not inferred for every expression from `Methods.WF`:
that record needs finite support and a structural translation for each input.
Later closure supplies this contract from an execution-indexed census of the
actual constructor and recursor-type intermediates. -/
def WhnfCallbackPreserves (I : TcState .anon → Prop)
    (methods : Methods .anon) : Prop :=
  ∀ e s, TcM.WF I s (methods.whnf e) (fun _ _ => True)

/-- Every direct declaration reference reachable in this finite execution
support has already crossed the trusted-world admission boundary.  This is a
run-scoped property, not a claim that every entry of the immutable catalog is
trusted. -/
def TrustedReferences (world : VerifyWorld) (support : RunSupport) : Prop :=
  ∀ {source : KExpr .anon} {id : KId .anon},
    support source → source.References id → world.trusted id

/-- Result-support contract for the exact predecessor-table WHNF callbacks
crossed by helper scans.  Unlike `WhnfCallbackPreserves`, this retains the
finite result witness needed to authorize declaration references selected
from the callback result. -/
def WhnfCallbackSupports (support : RunSupport) (I : TcState .anon → Prop)
    (methods : Methods .anon) : Prop :=
  ∀ e s, TcM.WF I s (methods.whnf e) (fun result _ => support result)

/-- Public name for the finite telescope-body support consumed by the
binder-aware constructor and recursor scans.  The implementation theorem
currently lives in `ScopedClassifier`; this alias keeps that staging detail out
of the recursion-classifier interface. -/
abbrev ConstructorTelescopeInputSupport :=
  ScratchTelescopeInputSupport

/-- Admission-owned typed input for a constructor declaration actually
returned by the production lookup.

The execution equation is essential: an arbitrary catalog entry does not
justify invoking WHNF on an arbitrary expression.  Conversely, this boundary
owns no state fact and cannot choose a constructor independently of the
lookup.  A later admission refinement derives the field from the checked
constructor declaration after resolving its universe parameters. -/
structure ConstructorTelescopeInputOracle
    (trProj : RawProjRel) (world : VerifyWorld)
    (support : RunSupport) : Prop where
  found :
    ∀ {uvars : Nat} {Delta : KVLCtx}
      {ctorId : KId .anon} {before after : TcState .anon}
      {name : Mode.anon.F Name}
      {levelParams : Mode.anon.F (Array Name)}
      {isUnsafe : Bool} {lvls : UInt64} {induct : KId .anon}
      {cidx params fields : UInt64} {ty : KExpr .anon},
    TcM.tryGetConst ctorId before =
        .ok (some (.ctor name levelParams isUnsafe lvls induct cidx params
          fields ty)) after →
      support ty ∧ ∃ tyV,
        TrKExprS world.venv uvars world.nameOf trProj Delta ty tyV

namespace WhnfCallbackSupports

/-- Forgetting finite result support recovers the state-only callback
contract used by the existing helper proofs. -/
theorem preserves
    {support : RunSupport} {I : TcState .anon → Prop}
    {methods : Methods .anon}
    (h : WhnfCallbackSupports support I methods) :
    WhnfCallbackPreserves I methods := by
  intro e s
  exact TcM.WF.mono (h e s) (fun _ _ _ => trivial)
    (fun _ _ _ => trivial)

end WhnfCallbackSupports

/-- Explicit authority for the two recursion-classification writes made by
`computedIsRec`.  The final certificate is indexed by the exact successful
classifier execution; inserting a Boolean into the physical map is not, by
itself, evidence that the Boolean has the cache semantics chosen by the
caller.

The classifier inputs are supplied by production's preceding inductive and
mutual-block lookups.  This record owns only the semantic cache boundary;
the theorem below proves that those are the values actually passed to the
recorded `computeIsRec` execution. -/
structure IsRecCacheWriteOracle
    (semantics : CacheSemantics) (world : VerifyWorld)
    (support : RunSupport) (methods : Methods .anon)
    (ind : KId .anon) : Prop where
  provisional :
    CacheProvenance semantics (CacheAuthority.stable world) support
      (.isRec ind.addr true)
  computed : ∀ {ctors : Array (KId .anon)} {nParams : Nat}
      {blockAddrs : Array Address} {before after : TcState .anon}
      {value : Bool},
    (computeIsRec ctors nParams blockAddrs).run methods before =
        .ok value after →
      CacheProvenance semantics (CacheAuthority.stable world) support
        (.isRec ind.addr value)

namespace IsRecCacheWriteOracle

/-- Construct both classifier-write certificates from trusted operational
cache ownership.

The successful `computeIsRec` equation remains in the record so callers can
tie the written Boolean to the value production actually returned.  It is not
needed to establish cache validity: the `.isRec` family is deliberately only
an operational gate.  Conservative/provisional `true` suppresses struct eta,
and any path enabled by `false` must still pass the independent
`IotaSuccessOracle` semantic proof. -/
theorem of_trusted
    {semantics : CacheSemantics} {world : VerifyWorld}
    {support : RunSupport} {methods : Methods .anon}
    {ind : KId .anon}
    (htrusted : world.trusted ind)
    (hvalid : ∀ value,
      semantics.Valid (CacheAuthority.stable world) support
        (.isRec ind.addr value)) :
    IsRecCacheWriteOracle semantics world support methods ind where
  provisional :=
    CacheProvenance.isRec_of_trusted htrusted (hvalid true)
  computed := by
    intro ctors nParams blockAddrs before after value hrun
    exact CacheProvenance.isRec_of_trusted htrusted (hvalid value)

end IsRecCacheWriteOracle

/-- Strengthen a concrete `TcM` triple with the execution equation selected
by its actual outcome.  This is used at semantic write boundaries where the
certificate must be tied to the value that production really computed. -/
private theorem wf_with_run_eq
    {I : TcState .anon → Prop} {s : TcState .anon} {x : TcM .anon α}
    {Q : α → TcState .anon → Prop}
    {E : TcError .anon → TcState .anon → Prop}
    (hx : TcM.WF I s x Q E) :
    TcM.WF I s x
      (fun value after => Q value after ∧ x s = .ok value after)
      (fun err after => E err after ∧ x s = .error err after) := by
  intro hI
  have hpost := hx hI
  cases hrun : x s with
  | ok value after =>
      rw [hrun] at hpost
      exact ⟨hpost.1, hpost.2, rfl⟩
  | error err after =>
      rw [hrun] at hpost
      exact ⟨hpost.1, hpost.2, rfl⟩

/-- A finite `RecM` list loop preserves an invariant if each exact body
invocation does.  `done` exits immediately; `yield` continues from the body's
partial post-state. -/
private theorem forIn_list_state_wf
    {I : TcState .anon → Prop} {methods : Methods .anon}
    {f : α → β → RecM .anon (ForInStep β)}
    (hstep : ∀ a b s,
      TcM.WF I s ((f a b).run methods) (fun _ _ => True)) :
    ∀ (xs : List α) (init : β) (s : TcState .anon),
      TcM.WF I s ((forIn (m := RecM .anon) xs init f).run methods)
        (fun _ _ => True)
  | [], init, s => by
      exact TcM.WF.pure fun _ => trivial
  | a :: xs, init, s => by
      rw [List.forIn_cons, ReaderT.run_bind]
      apply TcM.WF.bind (hstep a init s)
      intro action after _
      cases action with
      | done result => exact TcM.WF.pure fun _ => trivial
      | yield next => exact forIn_list_state_wf hstep xs next after

/-- Fixed-reader composition without exposing the representation of
`ReaderT.run` to every helper proof. -/
private theorem reader_bind_state_wf
    {I : TcState .anon → Prop} {methods : Methods .anon}
    {x : RecM .anon α} {f : α → RecM .anon β}
    {Q₁ : α → TcState .anon → Prop}
    {Q₂ : β → TcState .anon → Prop}
    {E : TcError .anon → TcState .anon → Prop}
    (hx : TcM.WF I s (x.run methods) Q₁ E)
    (hf : ∀ a after, Q₁ a after →
      TcM.WF I after ((f a).run methods) Q₂ E) :
    TcM.WF I s ((x >>= f).run methods) Q₂ E := by
  rw [ReaderT.run_bind]
  exact TcM.WF.bind hx hf

/-- Fixed-reader form of non-backtracking exception handling.  The handler
starts in the body's exact partial post-state. -/
private theorem reader_tryCatch_state_wf
    {I : TcState .anon → Prop} {methods : Methods .anon}
    {x : RecM .anon α} {handler : TcError .anon → RecM .anon α}
    {Q : α → TcState .anon → Prop}
    {E₁ E₂ : TcError .anon → TcState .anon → Prop}
    (hx : TcM.WF I s (x.run methods) Q E₁)
    (hh : ∀ err after, E₁ err after →
      TcM.WF I after ((handler err).run methods) Q E₂) :
    TcM.WF I s ((tryCatch x handler).run methods) Q E₂ := by
  change TcM.WF I s
    (EStateM.tryCatch (x.run methods)
      (fun err => (handler err).run methods)) Q E₂
  exact TcM.WF.tryCatch hx hh

/-- Fixed-reader state rule for the total bounded-loop driver. -/
private theorem runBounded_state_wf
    {I : TcState .anon → Prop} {methods : Methods .anon}
    {step : σ → RecM .anon (BoundedStep σ α)}
    (hstep : ∀ state s,
      TcM.WF I s ((step state).run methods) (fun _ _ => True)) :
    ∀ fuel state s,
      TcM.WF I s ((runBounded step fuel state).run methods)
        (fun _ _ => True)
  | 0, state, s => by
      rw [runBounded]
      exact TcM.WF.throw fun _ => trivial
  | fuel + 1, state, s => by
      rw [runBounded, ReaderT.run_bind]
      apply TcM.WF.bind (hstep state s)
      intro action after _
      cases action with
      | done result => exact TcM.WF.pure fun _ => trivial
      | next next => exact runBounded_state_wf hstep fuel next after

/-- State preservation for the bounded constructor-field scan used by
`computeIsRec`. -/
private theorem computeIsRecFields_wf
    {I : TcState .anon → Prop}
    (hwhnf : WhnfCallbackPreserves I methods)
    (blockAddrs : Array Address) :
    ∀ fuel ty s,
      TcM.WF I s
        ((runBounded (fun ty => do
            let w ← whnfRec ty
            match w with
            | .all _ _ dom body _ =>
              if exprMentionsAnyAddr dom blockAddrs = true then
                pure (.done true)
              else pure (.next body)
            | _ => pure (.done false)) fuel ty).run methods)
        (fun _ _ => True)
  | 0, ty, s => by
      rw [runBounded]
      exact TcM.WF.throw fun _ => trivial
  | fuel + 1, ty, s => by
      rw [runBounded, ReaderT.run_bind]
      apply TcM.WF.bind (Q₁ := fun _ _ => True)
      · rw [ReaderT.run_bind]
        apply TcM.WF.bind (Q₁ := fun _ _ => True)
          (Q₂ := fun _ _ => True) (hwhnf ty s)
        intro reduced after _
        cases reduced <;>
          try exact TcM.WF.pure (Q := fun _ _ => True) (fun _ => trivial)
        case all name bi dom body info =>
          simp only
          split <;>
            exact TcM.WF.pure (Q := fun _ _ => True) (fun _ => trivial)
      · intro action after _
        cases action with
        | done result => exact TcM.WF.pure fun _ => trivial
        | next next =>
            exact computeIsRecFields_wf hwhnf blockAddrs fuel next after

/-- List form of the parameter-prefix loop exposed after range normalization. -/
private theorem computeIsRecParamsList_wf
    {I : TcState .anon → Prop}
    (hwhnf : WhnfCallbackPreserves I methods)
    (indices : List Nat) (ty : KExpr .anon) (s : TcState .anon) :
    TcM.WF I s
      ((forIn (m := RecM .anon) indices ty (fun _ ty => do
          let w ← whnfRec ty
          match w with
          | .all _ _ _ body _ => pure (ForInStep.yield body)
          | _ => pure (ForInStep.done ty))).run methods)
      (fun _ _ => True) := by
  apply forIn_list_state_wf
  intro _ current before
  rw [ReaderT.run_bind]
  apply TcM.WF.bind (Q₁ := fun _ _ => True) (hwhnf current before)
  intro reduced after _
  cases reduced <;>
    exact TcM.WF.pure (Q := fun _ _ => True) (fun _ => trivial)

/-- The parameter-prefix range loop preserves state whether it peels all
requested foralls or breaks early on a non-forall callback result. -/
private theorem computeIsRecParams_wf
    {I : TcState .anon → Prop}
    (hwhnf : WhnfCallbackPreserves I methods)
    (range : _root_.Std.Legacy.Range) (ty : KExpr .anon)
    (s : TcState .anon) :
    TcM.WF I s
      ((forIn (m := RecM .anon) range ty (fun _ ty => do
          let w ← whnfRec ty
          match w with
          | .all _ _ _ body _ => pure (ForInStep.yield body)
          | _ => pure (ForInStep.done ty))).run methods)
      (fun _ _ => True) := by
  rw [_root_.Std.Legacy.Range.forIn_eq_forIn_range']
  exact computeIsRecParamsList_wf hwhnf _ ty s

/-- Finite support closure needed when a verified WHNF result exposes the
body of a declaration telescope.  This is deliberately narrower than
constructor closure of the whole run support. -/
abbrev MajorTelescopeInputSupport :=
  ScratchTelescopeInputSupport

/-- Binder-correct public major-inductive scan.  Recursive WHNF calls are
instantiated from the predecessor method table at the dynamically extended
context, and the `finally` block restores the exact caller context on every
success or error. -/
theorem getMajorInductiveId_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {methods : Methods .anon}
    (hmethods :
      Methods.WFAt layer semantics trProj world support uvars methods)
    (hinputs : MajorTelescopeInputSupport support)
    (hfault : ∀ {Delta : KVLCtx},
      TcM.LazyFaultPreserves
        (WhnfStateInv layer semantics trProj world support uvars Delta))
    (hreferences : TrustedReferences world support)
    {Delta : KVLCtx} {recTy : KExpr .anon} {recTyV : Lean4Lean.VExpr}
    {s : TcState .anon} (skip : UInt64)
    (hrecSupport : support recTy)
    (hrecTr :
      TrKExprS world.venv uvars world.nameOf trProj Delta recTy recTyV) :
    TcM.WF
      (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((getMajorInductiveId recTy skip).run methods)
      (fun id _ => world.trusted id) :=
  scratch_getMajorInductiveId_wf hmethods hinputs hfault hreferences skip
    hrecSupport hrecTr

/-- A constant spine head is a direct reference of the complete application
spine.  The private worker follows `collectSpine.go` so the proof does not
depend on any reconstruction or array-order lemma. -/
private theorem collectSpineGo_const_references
    {id : KId .anon} {us : Array (KUniv .anon)}
    {info : ExprInfo .anon} :
    ∀ (e : KExpr .anon) (acc args : Array (KExpr .anon)),
      KExpr.collectSpine.go e acc = (.const id us info, args) →
      e.References id
  | .app f a appInfo, acc, args, h => by
      simp only [KExpr.collectSpine.go] at h
      exact Or.inl (collectSpineGo_const_references f (acc.push a) args h)
  | .const actual actualUs actualInfo, acc, args, h => by
      simp only [KExpr.collectSpine.go] at h
      cases h
      rfl
  | .var .., _, _, h
  | .fvar .., _, _, h
  | .sort .., _, _, h
  | .lam .., _, _, h
  | .all .., _, _, h
  | .letE .., _, _, h
  | .prj .., _, _, h
  | .nat .., _, _, h
  | .str .., _, _, h => by
      simp only [KExpr.collectSpine.go] at h
      cases h

/-- Public `collectSpine` form of the direct-head reference lemma. -/
theorem collectSpine_const_references
    {e : KExpr .anon} {id : KId .anon}
    {us : Array (KUniv .anon)} {info : ExprInfo .anon}
    {args : Array (KExpr .anon)}
    (h : e.collectSpine = (.const id us info, args)) :
    e.References id :=
  collectSpineGo_const_references e #[] args h

/-- Compatibility spelling for callers that emphasize the trusted result.
The binder-correct public theorem already carries that result contract. -/
theorem getMajorInductiveId_trusted_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {methods : Methods .anon}
    (hmethods :
      Methods.WFAt layer semantics trProj world support uvars methods)
    (hinputs : MajorTelescopeInputSupport support)
    (hfault : ∀ {Delta : KVLCtx},
      TcM.LazyFaultPreserves
        (WhnfStateInv layer semantics trProj world support uvars Delta))
    (hreferences : TrustedReferences world support)
    {Delta : KVLCtx} {recTy : KExpr .anon} {recTyV : Lean4Lean.VExpr}
    {s : TcState .anon} (skip : UInt64)
    (hrecSupport : support recTy)
    (hrecTr :
      TrKExprS world.venv uvars world.nameOf trProj Delta recTy recTyV) :
    TcM.WF
      (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((getMajorInductiveId recTy skip).run methods)
      (fun id _ => world.trusted id) :=
  getMajorInductiveId_wf hmethods hinputs hfault hreferences skip hrecSupport
    hrecTr

/-- The production mutual-block census preserves an arbitrary invariant on
hits, misses, and lazy-ingress errors.  The returned array deliberately has
no semantic postcondition yet; this theorem owns only concrete state effects. -/
theorem discoverBlockInductives_wf
    {I : TcState .anon → Prop} (hfault : TcM.LazyFaultPreserves I)
    (methods : Methods .anon) (blockId : KId .anon) (s : TcState .anon) :
    TcM.WF I s ((discoverBlockInductives blockId).run methods)
      (fun _ _ => True) := by
  rw [discoverBlockInductives_equation, ReaderT.run_bind,
    ReaderT.run_monadLift]
  apply TcM.WF.bind (TcM.tryGetBlock_wf hfault blockId s)
  intro found after _
  cases found with
  | none => exact TcM.WF.pure fun _ => trivial
  | some members =>
      simp
      rw [← Array.forIn_toList]
      generalize members.toList = ids
      generalize (#[] : Array (KId .anon)) = acc
      induction ids generalizing acc after with
      | nil =>
          simpa using
            (TcM.WF.pure (I := I) (s := after) (a := acc)
              (fun _ => trivial))
      | cons id ids ih =>
          rw [List.forIn_cons, ReaderT.run_bind]
          apply TcM.WF.bind (Q₁ := fun _ _ => True)
          · rw [ReaderT.run_bind, ReaderT.run_monadLift]
            apply TcM.WF.bind (TcM.tryGetConst_wf hfault id after)
            intro found afterLookup _
            cases found with
            | none => exact TcM.WF.pure fun _ => trivial
            | some c =>
                cases c <;> exact TcM.WF.pure fun _ => trivial
          · intro step afterStep _
            cases step with
            | done next => exact TcM.WF.pure fun _ => trivial
            | yield next => exact ih afterStep next

/-- `computeIsRec` preserves the exact caller context while scanning every
constructor telescope.  Each successful constructor lookup is tied to its
finite, typed admission input; the binder-aware inner theorem restores the
caller's context on success and on partial errors. -/
theorem computeIsRec_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    (hmethods :
      Methods.WFAt layer semantics trProj world support uvars methods)
    (hinputs : ConstructorTelescopeInputSupport support)
    (hctorInputs : ConstructorTelescopeInputOracle trProj world support)
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta))
    (ctors : Array (KId .anon)) (nParams : Nat)
    (blockAddrs : Array Address) (s : TcState .anon) :
    TcM.WF
      (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((computeIsRec ctors nParams blockAddrs).run methods)
      (fun _ _ => True) := by
  unfold computeIsRec
  simp
  apply TcM.WF.bind (Q₁ := fun _ _ => True)
  · rw [← Array.forIn_toList]
    apply forIn_list_state_wf
    intro ctorId acc before
    rw [ReaderT.run_bind, ReaderT.run_monadLift]
    apply TcM.WF.bind
      (Q₁ := fun found after =>
        TcM.tryGetConst ctorId before = .ok found after)
      (TcM.WF.mono
        (TcM.WF.with_run_eq
          (TcM.tryGetConst_wf hfault ctorId before))
        (fun _ _ h => h.2) (fun _ _ _ => trivial))
    intro found afterLookup hlookup
    cases found with
    | none => exact TcM.WF.pure fun _ => trivial
    | some c =>
        cases c <;>
          try exact TcM.WF.pure (Q := fun _ _ => True) (fun _ => trivial)
        case ctor name levelParams isUnsafe lvls induct cidx params fields ty =>
          simp only
          rw [ReaderT.run_bind]
          obtain ⟨htySupport, tyV, htyTr⟩ :=
            hctorInputs.found (uvars := uvars) (Delta := Delta) hlookup
          apply TcM.WF.bind
            (scratch_computeIsRecCtor_wf hmethods hinputs nParams blockAddrs
              htySupport htyTr)
          intro found afterCtor _
          cases found <;> simp <;>
            exact TcM.WF.pure (Q := fun _ _ => True) (fun _ => trivial)
  · intro result after _
    rcases result with ⟨answer, _marker⟩
    cases answer with
    | none =>
        simp only
        simpa only [ReaderT.run] using
          (TcM.WF.pure
            (I := WhnfStateInv layer semantics trProj world support uvars Delta)
            (s := after)
            (Q := fun _ _ => True) (fun _ => trivial))
    | some value =>
        simp only
        simpa only [ReaderT.run] using
          (TcM.WF.pure
            (I := WhnfStateInv layer semantics trProj world support uvars Delta)
            (s := after)
            (Q := fun _ _ => True) (fun _ => trivial))

/-- One named recursion-cache write preserves the fixed-world invariant when
its exact value has semantic provenance. -/
theorem cacheIsRec_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {ind : KId .anon} {value : Bool} {s : TcState .anon}
    (hwrite : CacheProvenance semantics (CacheAuthority.stable world) support
      (.isRec ind.addr value)) :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((cacheIsRec ind value).run methods) (fun _ _ => True) := by
  unfold cacheIsRec
  exact TcM.WF.modifyGet
    (fun hI => IsRecCacheUpdate.insert_whnfStateInv hI hwrite)
    (fun _ => trivial)

/-- The named cleanup seam removes only the selected recursion entry and
therefore needs no replacement certificate. -/
theorem eraseCachedIsRec_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {ind : KId .anon} {s : TcState .anon} :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((eraseCachedIsRec ind).run methods) (fun _ _ => True) := by
  unfold eraseCachedIsRec
  exact TcM.WF.modifyGet
    (fun hI => IsRecCacheUpdate.erase_whnfStateInv hI)
    (fun _ => trivial)

/-- The classifier transaction commits the value produced by the exact
`computeIsRec` execution.  If that execution throws, cleanup starts from its
partial post-state, erases the provisional marker, and rethrows. -/
theorem computedIsRecClassify_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {ind : KId .anon} {ctors : Array (KId .anon)} {nParams : Nat}
    {blockAddrs : Array Address} {s : TcState .anon}
    (hmethods :
      Methods.WFAt layer semantics trProj world support uvars methods)
    (hinputs : ConstructorTelescopeInputSupport support)
    (hctorInputs : ConstructorTelescopeInputOracle trProj world support)
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta))
    (hwrites : IsRecCacheWriteOracle semantics world support methods ind) :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((computedIsRecClassify ind ctors nParams blockAddrs).run methods)
      (fun _ _ => True) := by
  unfold computedIsRecClassify
  apply reader_tryCatch_state_wf (E₁ := fun _ _ => True)
  · rw [ReaderT.run_bind]
    apply TcM.WF.bind
      (Q₁ := fun value after =>
        True ∧
          (computeIsRec ctors nParams blockAddrs).run methods s =
            .ok value after)
      (TcM.WF.mono
        (wf_with_run_eq
          (computeIsRec_wf hmethods hinputs hctorInputs hfault
            ctors nParams blockAddrs s))
        (fun _ _ h => h) (fun _ _ _ => trivial))
    intro value afterCompute hcompute
    rw [ReaderT.run_bind]
    apply TcM.WF.bind
      (cacheIsRec_wf (methods := methods) (s := afterCompute)
        (hwrites.computed hcompute.2))
    intro _ afterWrite _
    exact TcM.WF.pure fun _ => trivial
  · intro err afterError _
    rw [ReaderT.run_bind]
    apply TcM.WF.bind
      (eraseCachedIsRec_wf (methods := methods) (ind := ind)
        (s := afterError))
    intro _ afterErase _
    exact TcM.WF.throw (fun _ => trivial)

/-- Cache-miss state preservation follows production's exact transaction
boundary: the provisional marker precedes block discovery, so discovery
errors retain it; only classifier errors enter `computedIsRecClassify`'s
cleanup handler. -/
theorem computedIsRecMiss_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {ind : KId .anon} {params : UInt64} {ctors : Array (KId .anon)}
    {block : KId .anon} {s : TcState .anon}
    (hmethods :
      Methods.WFAt layer semantics trProj world support uvars methods)
    (hinputs : ConstructorTelescopeInputSupport support)
    (hctorInputs : ConstructorTelescopeInputOracle trProj world support)
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta))
    (hwrites : IsRecCacheWriteOracle semantics world support methods ind) :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((computedIsRecMiss ind params ctors block).run methods)
      (fun _ _ => True) := by
  unfold computedIsRecMiss
  rw [ReaderT.run_bind]
  apply TcM.WF.bind
    (cacheIsRec_wf (methods := methods) (s := s) hwrites.provisional)
  intro _ afterProvisional _
  rw [ReaderT.run_bind]
  apply TcM.WF.bind
    (discoverBlockInductives_wf hfault methods block afterProvisional)
  intro blockInds afterDiscovery _
  exact computedIsRecClassify_wf hmethods hinputs hctorInputs hfault hwrites

/-- The complete cached recursion classifier preserves the fixed-world WHNF
invariant on cache hits, lazy lookup failures, non-inductive errors,
block-discovery failures, successful classification, and caught classifier
errors. -/
theorem computedIsRec_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {ind : KId .anon} {s : TcState .anon}
    (hmethods :
      Methods.WFAt layer semantics trProj world support uvars methods)
    (hinputs : ConstructorTelescopeInputSupport support)
    (hctorInputs : ConstructorTelescopeInputOracle trProj world support)
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta))
    (hwrites : IsRecCacheWriteOracle semantics world support methods ind) :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((computedIsRec ind).run methods) (fun _ _ => True) := by
  unfold computedIsRec
  rw [ReaderT.run_bind]
  apply TcM.WF.bind
    (Q₁ := fun observed after => observed = after)
    (TcM.WF.get fun _ => rfl)
  intro observed afterRead hread
  subst observed
  cases hcache : afterRead.env.isRecCache[ind.addr]? with
  | some value =>
      simp only
      exact TcM.WF.pure fun _ => trivial
  | none =>
      simp only [pure_bind]
      rw [ReaderT.run_bind, ReaderT.run_monadLift]
      change TcM.WF _ afterRead (TcM.getConst ind >>= _) _
      apply TcM.WF.bind (TcM.getConst_wf hfault ind afterRead)
      intro entry afterLookup _
      cases entry with
      | defn =>
          simp only [ReaderT.run]
          exact TcM.WF.throw (fun _ => trivial)
      | recr =>
          simp only [ReaderT.run]
          exact TcM.WF.throw (fun _ => trivial)
      | axio =>
          simp only [ReaderT.run]
          exact TcM.WF.throw (fun _ => trivial)
      | quot =>
          simp only [ReaderT.run]
          exact TcM.WF.throw (fun _ => trivial)
      | ctor =>
          simp only [ReaderT.run]
          exact TcM.WF.throw (fun _ => trivial)
      | indc name levelParams lvls params indices isUnsafe block memberIdx
          ty ctors leanAll =>
          simpa only [ReaderT.run] using
            (computedIsRecMiss_wf (s := afterLookup) hmethods hinputs
              hctorInputs hfault hwrites)

end RecM

end Ix.Tc
