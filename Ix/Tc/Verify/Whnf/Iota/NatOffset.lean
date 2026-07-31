import Ix.Tc.Verify.Whnf.Runtime.LazyIngress

/-!
# State closure for iota's Nat-offset preprocessing

`tryIotaWithFlags` invokes `cleanupNatOffsetMajor` before the recursive major
callback, and `tryIotaAfterMajorWhnf` invokes it again afterward.  Earlier
operational slices proved the String-literal miss, but the production helper
accepts an arbitrary expression.

Both bounded parsers used by the cleanup are read-only.  This slice proves
that fact for every input and every invariant, then closes the complete
cleanup helper without leaving it as an iota runtime premise.
-/

namespace Ix.Tc
namespace RecM

set_option maxHeartbeats 800000

attribute [local irreducible] strLitToConstructor
  tryIotaAfterCleanup tryIotaAfterMajorWhnf

/-- A successful optional expression result is a certified input for the
next predecessor-table callback.  Misses generate no new input obligation.

This postcondition is shared by K-synthesis and Nat-offset cleanup: both may
replace the original iota major with freshly constructed syntax, and
`Methods.WF` may be invoked on that replacement only after finite support and
a structural translation have been recovered. -/
def OptionalGeneratedInput (trProj : RawProjRel) (world : VerifyWorld)
    (support : RunSupport) (uvars : Nat) (Delta : KVLCtx) :
    Option (KExpr .anon) → Prop
  | none => True
  | some result =>
      ∃ resultV, support result ∧
        TrKExprS world.venv uvars world.nameOf trProj Delta result resultV

/-- Reading the primitive table through `RecM.prims` changes no state. -/
theorem prims_state_wf {I : TcState .anon → Prop}
    (methods : Methods .anon) (s : TcState .anon) :
    TcM.WF I s (prims.run methods) (fun _ _ => True) :=
  fun hI => ⟨hI, trivial⟩

/-- Primitive-address classification for binary Nat arithmetic is a
read-only primitive-table query. -/
theorem isNatBinArithAddr_state_wf {I : TcState .anon → Prop}
    (methods : Methods .anon) (addr : Address) (s : TcState .anon) :
    TcM.WF I s ((isNatBinArithAddr addr).run methods) (fun _ _ => True) := by
  unfold isNatBinArithAddr
  rw [ReaderT.run_bind]
  apply TcM.WF.bind (prims_state_wf methods s)
  intro _ _ _
  exact TcM.WF.pure (fun _ => trivial)

/-- The two mutually recursive Nat-offset readers preserve an arbitrary
state invariant.  The conjunction follows the production mutual recursion:
`natOffsetFuel` calls the literal reader for an additive RHS, while the
literal reader calls itself on predecessor and binary-arithmetic operands. -/
theorem natOffsetReaders_state_wf (fuel : Nat) :
    (∀ (I : TcState .anon → Prop) (methods : Methods .anon)
        (e : KExpr .anon) (s : TcState .anon),
      TcM.WF I s ((natOffsetFuel fuel e).run methods) (fun _ _ => True)) ∧
    (∀ (I : TcState .anon → Prop) (methods : Methods .anon)
        (e : KExpr .anon) (s : TcState .anon),
      TcM.WF I s ((evalNatOffsetLiteralFuel fuel e).run methods)
        (fun _ _ => True)) := by
  induction fuel with
  | zero =>
      constructor <;> intro I methods e s <;>
        exact TcM.WF.pure (fun _ => trivial)
  | succ fuel ih =>
      constructor
      · intro I methods e s
        unfold natOffsetFuel
        rcases hspine : e.collectSpine with ⟨head, args⟩
        cases head with
        | const id us info =>
            rw [ReaderT.run_bind]
            apply TcM.WF.bind (prims_state_wf methods s)
            intro p after _
            by_cases hsucc :
                (id.addr == p.natSucc.addr && args.size == 1) = true
            · simp only [hsucc, if_true]
              rw [ReaderT.run_bind]
              apply TcM.WF.bind (ih.1 I methods args[0]! after)
              intro found afterOffset _
              cases found with
              | none =>
                  exact TcM.WF.pure (Q := fun _ _ => True)
                    (fun _ => trivial)
              | some pair =>
                  rcases pair with ⟨base, offset⟩
                  exact TcM.WF.pure (Q := fun _ _ => True)
                    (fun _ => trivial)
            · simp only [hsucc, pure_bind]
              by_cases hadd :
                  (id.addr == p.natAdd.addr && args.size == 2) = true
              · simp only [hadd, if_true]
                simp only [Bool.false_eq_true, if_false]
                rw [ReaderT.run_bind]
                apply TcM.WF.bind (ih.2 I methods args[1]! after)
                intro rhs afterRhs _
                cases rhs with
                | none =>
                    exact TcM.WF.pure (Q := fun _ _ => True)
                      (fun _ => trivial)
                | some rhs =>
                    rw [ReaderT.run_bind]
                    apply TcM.WF.bind
                      (ih.1 I methods args[0]! afterRhs)
                    intro found afterOffset _
                    cases found with
                    | none =>
                        exact TcM.WF.pure (Q := fun _ _ => True)
                          (fun _ => trivial)
                    | some pair =>
                        rcases pair with ⟨base, offset⟩
                        exact TcM.WF.pure (Q := fun _ _ => True)
                          (fun _ => trivial)
              · simp only [hadd]
                exact TcM.WF.pure (Q := fun _ _ => True)
                  (fun _ => trivial)
        | _ => exact TcM.WF.pure (fun _ => trivial)
      · intro I methods e s
        unfold evalNatOffsetLiteralFuel
        rw [ReaderT.run_bind]
        apply TcM.WF.bind (prims_state_wf methods s)
        intro p after _
        cases hextract : extractNatValue e p with
        | some value =>
            exact TcM.WF.pure (Q := fun _ _ => True) (fun _ => trivial)
        | none =>
            simp only [pure_bind]
            rcases hspine : e.collectSpine with ⟨head, args⟩
            cases head with
            | const id us info =>
                by_cases hpred :
                    (id.addr == p.natPred.addr && args.size == 1) = true
                · simp only [hpred, if_true]
                  rw [ReaderT.run_bind]
                  apply TcM.WF.bind (ih.2 I methods args[0]! after)
                  intro value afterValue _
                  cases value <;>
                    exact TcM.WF.pure (Q := fun _ _ => True)
                      (fun _ => trivial)
                · simp only [hpred]
                  simp only [Bool.false_eq_true, if_false]
                  rw [ReaderT.run_bind]
                  apply TcM.WF.bind
                    (isNatBinArithAddr_state_wf methods id.addr after)
                  intro answer afterAddr _
                  by_cases hbinary :
                      (answer && args.size == 2) = true
                  · simp only [hbinary, if_true]
                    rw [ReaderT.run_bind]
                    apply TcM.WF.bind
                      (ih.2 I methods args[0]! afterAddr)
                    intro left afterLeft _
                    cases left with
                    | none =>
                        exact TcM.WF.pure (Q := fun _ _ => True)
                          (fun _ => trivial)
                    | some left =>
                        rw [ReaderT.run_bind]
                        apply TcM.WF.bind
                          (ih.2 I methods args[1]! afterLeft)
                        intro right afterRight _
                        cases right <;>
                          exact TcM.WF.pure (Q := fun _ _ => True)
                            (fun _ => trivial)
                  · simp only [hbinary]
                    exact TcM.WF.pure (Q := fun _ _ => True)
                      (fun _ => trivial)
            | _ => exact TcM.WF.pure (fun _ => trivial)

/-- The public bounded Nat-offset parser preserves any invariant. -/
theorem natOffset_state_wf {I : TcState .anon → Prop}
    (methods : Methods .anon) (e : KExpr .anon) (depth : Nat)
    (s : TcState .anon) :
    TcM.WF I s ((natOffset e depth).run methods) (fun _ _ => True) := by
  unfold natOffset
  exact (natOffsetReaders_state_wf (256 - depth)).1 I methods e s

/-- The public bounded literal evaluator preserves any invariant. -/
theorem evalNatOffsetLiteral_state_wf {I : TcState .anon → Prop}
    (methods : Methods .anon) (e : KExpr .anon) (depth : Nat)
    (s : TcState .anon) :
    TcM.WF I s ((evalNatOffsetLiteral e depth).run methods)
      (fun _ _ => True) := by
  unfold evalNatOffsetLiteral
  exact (natOffsetReaders_state_wf (256 - depth)).2 I methods e s

/-- One-layer Nat-literal constructor expansion reads only the primitive
table and leaves the state unchanged. -/
theorem natToConstructor_state_wf {I : TcState .anon → Prop}
    (methods : Methods .anon) (value : Nat) (s : TcState .anon) :
    TcM.WF I s ((natToConstructor value).run methods) (fun _ _ => True) := by
  unfold natToConstructor
  rw [ReaderT.run_bind]
  apply TcM.WF.bind (prims_state_wf methods s)
  intro _ _ _
  split <;> exact TcM.WF.pure (fun _ => trivial)

/-- Building the non-interned `Nat.succ` syntax reads only the primitive
table and therefore preserves every state invariant. -/
theorem mkNatSucc_state_wf {I : TcState .anon → Prop}
    (methods : Methods .anon) (e : KExpr .anon) (s : TcState .anon) :
    TcM.WF I s ((mkNatSucc e).run methods) (fun _ _ => True) := by
  unfold mkNatSucc
  rw [ReaderT.run_bind]
  apply TcM.WF.bind (prims_state_wf methods s)
  intro _ _ _
  exact TcM.WF.pure (fun _ => trivial)

/-- Building the non-interned `Nat.add` syntax has the same read-only
primitive-table effect. -/
theorem mkNatAdd_state_wf {I : TcState .anon → Prop}
    (methods : Methods .anon) (a b : KExpr .anon) (s : TcState .anon) :
    TcM.WF I s ((mkNatAdd a b).run methods) (fun _ _ => True) := by
  unfold mkNatAdd
  rw [ReaderT.run_bind]
  apply TcM.WF.bind (prims_state_wf methods s)
  intro _ _ _
  exact TcM.WF.pure (fun _ => trivial)

/-- Finite semantic input authority for the expression generated by one
successful Nat-offset cleanup.

The oracle is indexed by the actual production execution and assumes neither
state preservation nor callback behavior.  A later primitive/parser trace
construction supplies this field; K1 uses it only to recover the support and
structural translation required by `Methods.WF` for the selected major. -/
structure NatOffsetCleanupInputOracle (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) : Prop where
  generated :
    ∀ {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
      {source : KExpr .anon} {sourceV : Lean4Lean.VExpr}
      {before after : TcState .anon} {result : KExpr .anon},
    support source →
    TrKExprS world.venv uvars world.nameOf trProj Delta source sourceV →
    (cleanupNatOffsetMajor source).run methods before =
      .ok (some result) after →
    OptionalGeneratedInput trProj world support uvars Delta (some result)

/-- The complete production Nat-offset cleanup is state-safe on hits,
misses, and every bounded-parser branch. -/
theorem cleanupNatOffsetMajor_state_wf {I : TcState .anon → Prop}
    (methods : Methods .anon) (e : KExpr .anon) (s : TcState .anon) :
    TcM.WF I s ((cleanupNatOffsetMajor e).run methods) (fun _ _ => True) := by
  unfold cleanupNatOffsetMajor
  rw [ReaderT.run_bind]
  apply TcM.WF.bind (evalNatOffsetLiteral_state_wf methods e 0 s)
  intro literal afterLiteral _
  cases hsome : literal.isSome with
  | true => exact TcM.WF.pure (fun _ => trivial)
  | false =>
      simp only [Bool.false_eq_true, if_false, pure_bind]
      rw [ReaderT.run_bind]
      apply TcM.WF.bind (natOffset_state_wf methods e 0 afterLiteral)
      intro offsetResult afterOffset _
      cases hoffset : offsetResult with
      | none =>
          exact TcM.WF.pure (Q := fun _ _ => True) (fun _ => trivial)
      | some pair =>
          rcases pair with ⟨base, offset⟩
          by_cases hzero : (offset == 0) = true
          · simp only [hzero, if_true]
            exact TcM.WF.pure (Q := fun _ _ => True) (fun _ => trivial)
          · simp only [hzero]
            by_cases hpredZero : (offset - 1 == 0) = true
            · simp only [hpredZero, if_true]
              simp only [Bool.false_eq_true, if_false]
              rw [ReaderT.run_bind]
              apply TcM.WF.bind
                (mkNatSucc_state_wf methods base afterOffset)
              intro result afterResult _
              exact TcM.WF.pure (Q := fun _ _ => True) (fun _ => trivial)
            · simp only [hpredZero]
              simp only [Bool.false_eq_true, if_false]
              rw [ReaderT.run_bind]
              apply TcM.WF.bind
                (mkNatAdd_state_wf methods base
                  (natExprFromValue (offset - 1)) afterOffset)
              intro pred afterPred _
              rw [ReaderT.run_bind]
              apply TcM.WF.bind
                (mkNatSucc_state_wf methods pred afterPred)
              intro result afterResult _
              exact TcM.WF.pure (Q := fun _ _ => True) (fun _ => trivial)

/-- Combine the unconditional state proof with the execution-indexed cleanup
input authority.  On a miss the optional postcondition is vacuous; on a hit
the oracle is tied to the exact value and post-state returned by production. -/
theorem cleanupNatOffsetMajor_input_wf
    {I : TcState .anon → Prop} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    (inputs : NatOffsetCleanupInputOracle trProj world support)
    {source : KExpr .anon} {sourceV : Lean4Lean.VExpr}
    (hsourceSupport : support source)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV)
    (s : TcState .anon) :
    TcM.WF I s ((cleanupNatOffsetMajor source).run methods)
      (fun result _ =>
        OptionalGeneratedInput trProj world support uvars Delta result) := by
  apply TcM.WF.mono
    (TcM.WF.with_run_eq
      (cleanupNatOffsetMajor_state_wf methods source s))
  · intro result after hpost
    cases result with
    | none => trivial
    | some result =>
        exact inputs.generated hsourceSupport hsource hpost.2
  · intro _ _ _
    trivial

/-! ## Exhaustive post-major state assembly -/

/-- State boundary for the actual ordinary-constructor rule application.
Unlike a whole-iota premise, this owns only universe instantiation and the
three finite argument folds after production has selected a constructor. -/
def TryApplyIotaCtorPreserves (I : TcState .anon → Prop)
    (methods : Methods .anon) : Prop :=
  ∀ recr recUs spine ctorArgs cidx ctorFields transient s,
    TcM.WF I s
      ((tryApplyIotaCtor recr recUs spine ctorArgs cidx ctorFields transient).run
        methods)
      (fun _ _ => True)

/-- State boundary for the struct-eta fallback.  Classifier/RebuildTail construct this
from lazy ingress, callbacks, recursion-cache writes, and finite rebuild
requests. -/
def StructEtaIotaPreserves (I : TcState .anon → Prop)
    (methods : Methods .anon) : Prop :=
  ∀ recId recr recUs spine s,
    TcM.WF I s ((tryStructEtaIota recId recr recUs spine).run methods)
      (fun _ _ => True)

/-- Input-indexed state boundary for the one struct-eta fallback selected by
the surrounding iota dispatcher.  Unlike `StructEtaIotaPreserves`, this does
not grant authority over unrelated recursors or argument spines. -/
def SelectedStructEtaIotaPreserves (I : TcState .anon → Prop)
    (methods : Methods .anon) (recId : KId .anon) (recr : IotaInfo .anon)
    (recUs : Array (KUniv .anon)) (spine : Array (KExpr .anon)) : Prop :=
  ∀ s, TcM.WF I s
    ((tryStructEtaIota recId recr recUs spine).run methods)
    (fun _ _ => True)

/-- Exhaust the actual constructor lookup and dispatch.  Lazy lookup is
proved directly; only the two genuine successful tails remain as inputs. -/
theorem tryIotaCtorOrStructEta_state_wf
    {I : TcState .anon → Prop} {methods : Methods .anon}
    (hfault : TcM.LazyFaultPreserves I)
    (happly : TryApplyIotaCtorPreserves I methods)
    (recId : KId .anon) (recr : IotaInfo .anon)
    (recUs : Array (KUniv .anon)) (spine : Array (KExpr .anon))
    (hstruct : SelectedStructEtaIotaPreserves I methods recId recr recUs
      spine)
    (majorWhnf : KExpr .anon) (transient : Bool) (s : TcState .anon) :
    TcM.WF I s
      ((tryIotaCtorOrStructEta recId recr recUs spine majorWhnf transient).run
        methods)
      (fun _ _ => True) := by
  unfold tryIotaCtorOrStructEta
  rcases hspine : majorWhnf.collectSpine with ⟨ctorHead, ctorArgs⟩
  cases ctorHead with
  | const ctorId ctorUs ctorInfo =>
      rw [ReaderT.run_bind, ReaderT.run_monadLift]
      apply TcM.WF.bind (TcM.tryGetConst_wf hfault ctorId s)
      intro found afterLookup _
      cases found with
      | none =>
          simp only
          exact hstruct afterLookup
      | some declaration =>
          cases hinfo : declaration.iotaCtorInfo? with
          | none =>
              simp only [hinfo]
              exact hstruct afterLookup
          | some pair =>
              rcases pair with ⟨cidx, ctorFields⟩
              simp only [hinfo, pure_bind]
              rw [ReaderT.run_bind]
              apply TcM.WF.bind
                (happly recr recUs spine ctorArgs cidx ctorFields transient
                  afterLookup)
              intro result afterApply _
              exact TcM.WF.pure (fun _ => trivial)
  | _ => exact hstruct s

/-- A StringExpansion finite String plan can be selected at the state where expansion
actually runs.  This avoids assuming that cleanup left the primitive table
equal to an earlier snapshot; its invariant supplies the canonical table
fact at the exact callback state. -/
theorem strLitToConstructor_context_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (strings : ProjectionStringPlanContext trProj world support)
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    (hmethods :
      Methods.WFAt .noAccel semantics trProj world support uvars methods)
    (value : String) (s : TcState .anon) :
    TcM.WF
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta) s
      ((strLitToConstructor value).run methods)
      (fun expanded _ =>
        support expanded ∧
          ∃ expandedV,
            TrKExprS world.venv uvars world.nameOf trProj Delta expanded
              expandedV) := by
  intro hI
  have plan := strings.plan s.prims hI.noAccel_primitives value
  have hrun :
      RecM.WF .noAccel semantics trProj world support uvars Delta s
        (strLitToConstructor value)
        (fun expanded _ =>
          support expanded ∧
            ∃ expandedV,
              TrKExprS world.venv uvars world.nameOf trProj Delta expanded
                expandedV) :=
    strLitToConstructor_plan_wf
      (semantics := semantics) (trProj := trProj) (world := world)
      (support := support) strings.collisionFree plan
  exact hrun methods hmethods hI

/-- Exhaust the named post-cleanup seam: String expansion and its recursive
callback are concrete; every resulting shape enters the already exhausted
constructor/struct-eta dispatcher. -/
theorem tryIotaAfterCleanup_state_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (strings : ProjectionStringPlanContext trProj world support)
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    (hmethods :
      Methods.WFAt .noAccel semantics trProj world support uvars methods)
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta))
    (happly : TryApplyIotaCtorPreserves
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta)
      methods)
    {flags : WhnfFlags} {recId : KId .anon} {recr : IotaInfo .anon}
    {recUs : Array (KUniv .anon)} {spine : Array (KExpr .anon)}
    (hstruct : SelectedStructEtaIotaPreserves
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta)
      methods recId recr recUs spine)
    (majorWhnf : KExpr .anon) (majorWasNatLit : Bool)
    (s : TcState .anon) :
    TcM.WF
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta) s
      ((tryIotaAfterCleanup flags recId recr recUs spine majorWhnf
        majorWasNatLit).run methods)
      (fun _ _ => True) := by
  let I := WhnfStateInv .noAccel semantics trProj world support uvars Delta
  have hdispatch : ∀ major after,
      TcM.WF I after
        ((tryIotaCtorOrStructEta recId recr recUs spine major
          majorWasNatLit).run methods)
        (fun _ _ => True) :=
    fun major after =>
      tryIotaCtorOrStructEta_state_wf hfault happly
        recId recr recUs spine hstruct major majorWasNatLit after
  unfold tryIotaAfterCleanup
  cases majorWhnf with
  | str value blob info =>
      rw [ReaderT.run_bind]
      apply TcM.WF.bind
        (strLitToConstructor_context_wf strings hmethods value s)
      intro expanded afterExpansion hexpanded
      rcases hexpanded with ⟨hexpandedSupport, expandedV, hexpandedTr⟩
      cases hcheap : flags.cheapRec with
      | false =>
          simp only [Bool.false_eq_true, if_false]
          rw [ReaderT.run_bind]
          apply TcM.WF.bind
            (hmethods.whnf hexpandedSupport hexpandedTr)
          intro reduced afterWhnf _
          exact hdispatch reduced afterWhnf
      | true =>
          simp only [if_true]
          rw [ReaderT.run_bind]
          apply TcM.WF.bind
            (hmethods.whnfCoreFlags hexpandedSupport hexpandedTr)
          intro reduced afterWhnf _
          exact hdispatch reduced afterWhnf
  | var idx name info => exact hdispatch (.var idx name info) s
  | fvar id name info => exact hdispatch (.fvar id name info) s
  | sort level info => exact hdispatch (.sort level info) s
  | const id us info => exact hdispatch (.const id us info) s
  | app fn arg info => exact hdispatch (.app fn arg info) s
  | lam name bi ty body info => exact hdispatch (.lam name bi ty body info) s
  | all name bi ty body info => exact hdispatch (.all name bi ty body info) s
  | letE name ty value body nondep info =>
      exact hdispatch (.letE name ty value body nondep info) s
  | prj id field value info => exact hdispatch (.prj id field value info) s
  | nat value blob info => exact hdispatch (.nat value blob info) s

/-- The complete post-major preprocessing stage preserves the fixed K1
invariant.  Nat conversion and both cleanup passes are now concrete.  String
conversion uses the finite StringExpansion plan and the predecessor method-table
contract for its one policy-selected callback. -/
theorem tryIotaAfterMajorWhnf_state_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport}
    (strings : ProjectionStringPlanContext trProj world support)
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    (hmethods :
      Methods.WFAt .noAccel semantics trProj world support uvars methods)
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta))
    (happly : TryApplyIotaCtorPreserves
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta)
      methods)
    {flags : WhnfFlags} {recId : KId .anon} {recr : IotaInfo .anon}
    {recUs : Array (KUniv .anon)} {spine : Array (KExpr .anon)}
    (hstruct : SelectedStructEtaIotaPreserves
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta)
      methods recId recr recUs spine)
    {majorWhnf0 : KExpr .anon} {s : TcState .anon} :
    TcM.WF
      (WhnfStateInv .noAccel semantics trProj world support uvars Delta) s
      ((tryIotaAfterMajorWhnf flags recId recr recUs spine majorWhnf0).run
        methods)
      (fun _ _ => True) := by
  let I := WhnfStateInv .noAccel semantics trProj world support uvars Delta
  have hfinish : ∀ major transient after,
      TcM.WF I after
        ((tryIotaAfterCleanup flags recId recr recUs spine major transient).run
          methods)
        (fun _ _ => True) :=
    fun major transient after =>
      tryIotaAfterCleanup_state_wf strings hmethods hfault happly hstruct
        major transient after
  unfold tryIotaAfterMajorWhnf
  cases majorWhnf0 with
  | nat value blob info =>
      rw [ReaderT.run_bind]
      apply TcM.WF.bind (natToConstructor_state_wf methods value s)
      intro major afterNat _
      rw [ReaderT.run_bind]
      apply TcM.WF.bind
        (cleanupNatOffsetMajor_state_wf methods major afterNat)
      intro cleaned afterCleanup _
      cases cleaned with
      | none => exact hfinish major true afterCleanup
      | some cleanedMajor => exact hfinish cleanedMajor true afterCleanup
  | str value blob info =>
      simp only [pure_bind]
      rw [ReaderT.run_bind]
      apply TcM.WF.bind
        (cleanupNatOffsetMajor_state_wf methods (.str value blob info) s)
      intro cleaned afterCleanup _
      cases cleaned with
      | none => exact hfinish (.str value blob info) false afterCleanup
      | some cleanedMajor => exact hfinish cleanedMajor false afterCleanup
  | var idx name info =>
      simp only [pure_bind]
      rw [ReaderT.run_bind]
      apply TcM.WF.bind
        (cleanupNatOffsetMajor_state_wf methods (.var idx name info) s)
      intro cleaned afterCleanup _
      cases cleaned with
      | none => exact hfinish (.var idx name info) false afterCleanup
      | some cleanedMajor => exact hfinish cleanedMajor false afterCleanup
  | fvar id name info =>
      simp only [pure_bind]
      rw [ReaderT.run_bind]
      apply TcM.WF.bind
        (cleanupNatOffsetMajor_state_wf methods (.fvar id name info) s)
      intro cleaned afterCleanup _
      cases cleaned with
      | none => exact hfinish (.fvar id name info) false afterCleanup
      | some cleanedMajor => exact hfinish cleanedMajor false afterCleanup
  | sort level info =>
      simp only [pure_bind]
      rw [ReaderT.run_bind]
      apply TcM.WF.bind
        (cleanupNatOffsetMajor_state_wf methods (.sort level info) s)
      intro cleaned afterCleanup _
      cases cleaned with
      | none => exact hfinish (.sort level info) false afterCleanup
      | some cleanedMajor => exact hfinish cleanedMajor false afterCleanup
  | const id us info =>
      simp only [pure_bind]
      rw [ReaderT.run_bind]
      apply TcM.WF.bind
        (cleanupNatOffsetMajor_state_wf methods (.const id us info) s)
      intro cleaned afterCleanup _
      cases cleaned with
      | none => exact hfinish (.const id us info) false afterCleanup
      | some cleanedMajor => exact hfinish cleanedMajor false afterCleanup
  | app fn arg info =>
      simp only [pure_bind]
      rw [ReaderT.run_bind]
      apply TcM.WF.bind
        (cleanupNatOffsetMajor_state_wf methods (.app fn arg info) s)
      intro cleaned afterCleanup _
      cases cleaned with
      | none => exact hfinish (.app fn arg info) false afterCleanup
      | some cleanedMajor => exact hfinish cleanedMajor false afterCleanup
  | lam name bi ty body info =>
      simp only [pure_bind]
      rw [ReaderT.run_bind]
      apply TcM.WF.bind
        (cleanupNatOffsetMajor_state_wf methods
          (.lam name bi ty body info) s)
      intro cleaned afterCleanup _
      cases cleaned with
      | none => exact hfinish (.lam name bi ty body info) false afterCleanup
      | some cleanedMajor => exact hfinish cleanedMajor false afterCleanup
  | all name bi ty body info =>
      simp only [pure_bind]
      rw [ReaderT.run_bind]
      apply TcM.WF.bind
        (cleanupNatOffsetMajor_state_wf methods
          (.all name bi ty body info) s)
      intro cleaned afterCleanup _
      cases cleaned with
      | none => exact hfinish (.all name bi ty body info) false afterCleanup
      | some cleanedMajor => exact hfinish cleanedMajor false afterCleanup
  | letE name ty value body nondep info =>
      simp only [pure_bind]
      rw [ReaderT.run_bind]
      apply TcM.WF.bind
        (cleanupNatOffsetMajor_state_wf methods
          (.letE name ty value body nondep info) s)
      intro cleaned afterCleanup _
      cases cleaned with
      | none =>
          exact hfinish (.letE name ty value body nondep info) false
            afterCleanup
      | some cleanedMajor => exact hfinish cleanedMajor false afterCleanup
  | prj id field value info =>
      simp only [pure_bind]
      rw [ReaderT.run_bind]
      apply TcM.WF.bind
        (cleanupNatOffsetMajor_state_wf methods (.prj id field value info) s)
      intro cleaned afterCleanup _
      cases cleaned with
      | none => exact hfinish (.prj id field value info) false afterCleanup
      | some cleanedMajor => exact hfinish cleanedMajor false afterCleanup

end RecM
end Ix.Tc
