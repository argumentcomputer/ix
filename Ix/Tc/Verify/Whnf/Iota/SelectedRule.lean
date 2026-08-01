import Ix.Tc.Verify.Whnf.Iota.ArgumentExecution

/-!
# Checked execution of one selected iota rule

ArgumentExecution composes the three argument loops after a concrete rule RHS already
exists.  This slice includes production's universe-instantiation call and
fixes the loop arrays to the exact prefix/constructor-field/trailing slices
computed by `tryIotaWithFlags`.

The adversarial boundary is explicit.  Ambient admission currently records a
registered `VDefEq` RHS and a `Pattern.RHS` independently.  Neither existing
relation says that applying the former to production's three slices yields
the latter under the match captures.  `IotaRhsApplicationAligned` names that
missing certificate instead of deriving a false equality.  Given the
certificate, the selected-rule trace proves exact production execution,
state/intern framing, finite support, and source-to-result `WhnfMeaning`.
-/

namespace Ix.Tc

open Lean4Lean (VDefEq VExpr)

namespace WhnfMeaning

/-- Two concrete expressions quotient-translated to the same Theory target
have a `WhnfMeaning` relation.  This is the quotient/quotient counterpart of
ArgumentExecution's `ofStructuralQuot`. -/
theorem ofQuot
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} (hDelta : KVLCtx.WF world.venv uvars Delta)
    {source result : KExpr .anon} {target : VExpr}
    (hsource : TrKExpr world.venv uvars world.nameOf trProj Delta
      source target)
    (hresult : TrKExpr world.venv uvars world.nameOf trProj Delta
      result target) :
    WhnfMeaning trProj world uvars Delta source result := by
  obtain ⟨sourceV, hsourceS, hsourceEq⟩ := hsource
  obtain ⟨resultV, hresultS, hresultEq⟩ := hresult
  exact ⟨sourceV, resultV, hsourceS, hresultS,
    hsourceEq.trans world.venvWF hDelta hresultEq.symm⟩

end WhnfMeaning

namespace RecM
namespace ApplyIotaArgsTrace

/-- Quotient translation of the unreduced concrete application sequence.
Unlike `sourceTr`, this accepts the universe-instantiated RHS relation
produced by RuleInstantiation, whose structural representative need not use the registered
RHS's exact Theory syntax. -/
theorem sourceQuot
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {transient : Bool} {start final : KExpr .anon}
    {startV finalV : VExpr} {s sf : TcState .anon}
    {args : List (KExpr .anon)}
    (h : ApplyIotaArgsTrace layer semantics trProj world support uvars Delta
      methods transient start startV s args final finalV sf)
    (theory : WhnfTheory trProj world uvars)
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    {replacement : KExpr .anon}
    (hstart : TrKExpr world.venv uvars world.nameOf trProj Delta replacement
      startV) :
    TrKExpr world.venv uvars world.nameOf trProj Delta
      (args.foldl KExpr.mkApp replacement) finalV := by
  induction h generalizing replacement with
  | nil => exact hstart
  | @cons result resultV s arg argV A B next s1 rest final finalV sf
      hfun harg hargTr hrun hpost hframe hnextSupport hmeaning tail ih =>
      have hargQ := hargTr.trKExpr world.venvWF.ordered
        theory.literalWF theory.projections.wf hDelta
      have happQ : TrKExpr world.venv uvars world.nameOf trProj Delta
          (KExpr.mkApp replacement arg) (.app resultV argV) := by
        rw [KExpr.mkApp_shape]
        exact TrKExpr.app world.venvWF hDelta hfun harg hstart hargQ
      rw [List.foldl_cons]
      exact ih happQ

/-- ArgumentExecution acceptance generalized to a quotient-translated initial RHS. -/
theorem acceptanceQuot
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {transient : Bool} {start final : KExpr .anon}
    {startV finalV : VExpr} {s sf : TcState .anon}
    {args : List (KExpr .anon)}
    (h : ApplyIotaArgsTrace layer semantics trProj world support uvars Delta
      methods transient start startV s args final finalV sf)
    (theory : WhnfTheory trProj world uvars)
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s)
    (hstartSupport : support start)
    (hstartTr : TrKExpr world.venv uvars world.nameOf trProj Delta start
      startV) :
    (args.foldlM (m := RecM .anon)
        (fun result arg => applyIotaArg result arg transient) start).run
          methods s = .ok final sf ∧
      WhnfStateInv layer semantics trProj world support uvars Delta sf ∧
      InternUpdateFrame s sf ∧
      support final ∧
      TrKExpr world.venv uvars world.nameOf trProj Delta final finalV ∧
      WhnfMeaning trProj world uvars Delta
        (args.foldl KExpr.mkApp start) final := by
  have hsourceQ := h.sourceQuot theory hDelta hstartTr
  have hfinalQ := h.finalQuot theory hDelta hstartTr
  exact ⟨h.evalList, h.finalInv hI, h.frame,
    h.finalSupport hstartSupport, hfinalQ,
    WhnfMeaning.ofQuot hDelta hsourceQ hfinalQ⟩

/-- Quotient-aware complete contract for the exact three-array helper
sequence. -/
theorem threeArrayAcceptanceQuot
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {transient : Bool} {start middle1 middle2 final : KExpr .anon}
    {startV middleV1 middleV2 finalV : VExpr}
    {s s1 s2 sf : TcState .anon}
    {first second third : Array (KExpr .anon)}
    (hfirst : ApplyIotaArgsTrace layer semantics trProj world support uvars
      Delta methods transient start startV s first.toList middle1 middleV1 s1)
    (hsecond : ApplyIotaArgsTrace layer semantics trProj world support uvars
      Delta methods transient middle1 middleV1 s1 second.toList middle2
        middleV2 s2)
    (hthird : ApplyIotaArgsTrace layer semantics trProj world support uvars
      Delta methods transient middle2 middleV2 s2 third.toList final finalV
        sf)
    (theory : WhnfTheory trProj world uvars)
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s)
    (hstartSupport : support start)
    (hstartTr : TrKExpr world.venv uvars world.nameOf trProj Delta start
      startV) :
    (do
        let result ← applyIotaArgs start first transient
        let result ← applyIotaArgs result second transient
        applyIotaArgs result third transient).run methods s = .ok final sf ∧
      WhnfStateInv layer semantics trProj world support uvars Delta sf ∧
      InternUpdateFrame s sf ∧
      support final ∧
      TrKExpr world.venv uvars world.nameOf trProj Delta final finalV ∧
      WhnfMeaning trProj world uvars Delta
        (((first.toList ++ second.toList) ++ third.toList).foldl
          KExpr.mkApp start) final := by
  have htrace := hfirst.three hsecond hthird
  have hsemantic :=
    htrace.acceptanceQuot theory hDelta hI hstartSupport hstartTr
  exact ⟨evalThreeArrays hfirst hsecond hthird, hsemantic.2⟩

end ApplyIotaArgsTrace
end RecM

namespace TcM

/-- A successful universe-instantiation run preserves the complete K1
invariant, changes only the intern table, and returns an expression in the
walk's finite support.  RuleInstantiation used the walker equation semantically; this is
the state/resource half needed before the three ArgumentExecution traces can start. -/
theorem instantiateUnivParams_whnf_of_run
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx}
    {us : Array (KUniv .anon)} {e result : KExpr .anon}
    {s after : TcState .anon}
    (hcollision : support.CollisionFree)
    (hreach : ∀ x, KExpr.InstUnivReach us e x → support x)
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s)
    (hrun : TcM.instantiateUnivParams e us s = .ok result after) :
    KExpr.instantiateUnivParamsSpec e us = .ok result ∧
      WhnfStateInv layer semantics trProj world support uvars Delta after ∧
      InternUpdateFrame s after ∧
      support result := by
  have hwalk := TcM.instantiateUnivParams_wf hcollision.expr hreach
    ⟨hI.1.core.intern, hI.1.internSupport.expr⟩
  rw [hrun] at hwalk
  have hspec := hwalk.2.1
  have hframe : InternUpdateFrame s after := hwalk.2.2.1
  have hunivs := hwalk.2.2.2
  have hconsts : after.env.consts = s.env.consts := by
    simpa [InternUpdateFrame] using
      congrArg (fun state : TcState .anon => state.env.consts) hframe
  have henv : after.env =
      { s.env with intern := after.env.intern } := by
    simpa [InternUpdateFrame] using
      congrArg (fun state : TcState .anon => state.env) hframe
  have hcover : support.CoversIntern after.env.intern := {
    expr := hwalk.1.2
    univ := by
      intro u hu
      exact hI.1.internSupport.univ u (by
        simpa only [InternTable.UnivSupport, hunivs] using hu)
  }
  have hcaches : CacheInvariant semantics (.stable world) support after.env := by
    rw [henv]
    exact hI.1.caches.of_intern_update
  have hkernel : KernelStateWF semantics trProj world support after := {
    core := hI.1.core.of_consts_eq hconsts hwalk.1.1
    internSupport := hcover
    caches := hcaches
    equivalences := by
      have hequiv := congrArg TcState.equivManager hframe
      simpa [InternUpdateFrame] using hequiv ▸ hI.1.equivalences
  }
  have hIafter := hframe.whnfStateInv hkernel hI
  have hresultSupport : support result := by
    by_cases hempty : us.isEmpty
    · have heq : e = result := by
        simpa [KExpr.instantiateUnivParamsSpec, hempty] using hspec
      rw [← heq]
      exact hreach e (KExpr.InstUnivReach.self us e)
    · have hspec' : KExpr.instUnivSpec e us = .ok result := by
        simpa [KExpr.instantiateUnivParamsSpec, hempty] using hspec
      exact hreach result (KExpr.InstUnivReach.spec hspec')
  exact ⟨hspec, hIafter, hframe, hresultSupport⟩

end TcM

namespace RecM

/-- The missing admission-side coherence fact: the Theory application index
obtained by applying the registered equation RHS to production's exact
argument slices is the pattern RHS under the match's levels and captures.
Current `RawRecursorRuleRel` and `RawRecursorRulePatternRel` do not imply this
equation because they record their RHS values independently. -/
def IotaRhsApplicationAligned
    (pattern : RecursorRulePattern) (levels : List Lean4Lean.VLevel)
    (captures : (RecursorIotaPattern pattern.recursorName pattern.majorIdx
      pattern.constructorName
      (pattern.constructorParams.toNat +
        pattern.constructorFields.toNat)).Path → VExpr)
    (applied : VExpr) : Prop :=
  applied = pattern.rhs.apply levels captures

/-- Exact successful execution certificate for `applyIotaRule`.  Its three
trace indices are definitionally production's prefix, constructor-field, and
trailing slices; callers cannot silently replace one with a convenient list.
The initial Theory index is left abstract so RuleInstantiation can later identify it with
the instantiated registered RHS. -/
structure ApplyIotaRuleTrace
    (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (Delta : KVLCtx) (methods : Methods .anon)
    (rule : RecRule .anon) (recUs : Array (KUniv .anon))
    (recr : IotaInfo .anon) (spine ctorArgs : Array (KExpr .anon))
    (ctorFields : Nat) (transient : Bool) (startV : VExpr)
    (s : TcState .anon) (final : KExpr .anon) (finalV : VExpr)
    (sf : TcState .anon) : Type where
  rhs : KExpr .anon
  after : TcState .anon
  middle1 : KExpr .anon
  middle2 : KExpr .anon
  middleV1 : VExpr
  middleV2 : VExpr
  s1 : TcState .anon
  s2 : TcState .anon
  instantiate : TcM.instantiateUnivParams rule.rhs recUs s = .ok rhs after
  prefixTrace : ApplyIotaArgsTrace layer semantics trProj world support uvars
    Delta methods transient rhs startV after
      (iotaPrefixArgs recr spine).toList middle1 middleV1 s1
  fieldTrace : ApplyIotaArgsTrace layer semantics trProj world support uvars
    Delta methods transient middle1 middleV1 s1
      (iotaFieldArgs ctorArgs ctorFields).toList middle2 middleV2 s2
  trailingTrace : ApplyIotaArgsTrace layer semantics trProj world support uvars
    Delta methods transient middle2 middleV2 s2
      (iotaTrailingArgs recr spine).toList final finalV sf

namespace ApplyIotaRuleTrace

/-- Erase the certificate to the exact extracted production helper run. -/
theorem eval
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {rule : RecRule .anon} {recUs : Array (KUniv .anon)}
    {recr : IotaInfo .anon} {spine ctorArgs : Array (KExpr .anon)}
    {ctorFields : Nat} {transient : Bool} {startV : VExpr}
    {s : TcState .anon} {final : KExpr .anon} {finalV : VExpr}
    {sf : TcState .anon}
    (h : ApplyIotaRuleTrace layer semantics trProj world support uvars Delta
      methods rule recUs recr spine ctorArgs ctorFields transient startV s
      final finalV sf) :
    (applyIotaRule rule recUs recr spine ctorArgs ctorFields transient).run
      methods s = .ok final sf := by
  unfold applyIotaRule
  rw [ReaderT.run_bind, ReaderT.run_monadLift]
  change EStateM.bind (TcM.instantiateUnivParams rule.rhs recUs) _ s = _
  unfold EStateM.bind
  rw [h.instantiate]
  simp only
  exact ApplyIotaArgsTrace.evalThreeArrays h.prefixTrace h.fieldTrace
    h.trailingTrace

/-- Production's parameter-free universe-instantiation path returns the rule
body and leaves state untouched.  The equalities are recovered from the
trace's observed run, so later proofs cannot posit a different RHS even on
this fast path. -/
theorem emptyInstantiation
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {rule : RecRule .anon} {recUs : Array (KUniv .anon)}
    {recr : IotaInfo .anon} {spine ctorArgs : Array (KExpr .anon)}
    {ctorFields : Nat} {transient : Bool} {startV : VExpr}
    {s : TcState .anon} {final : KExpr .anon} {finalV : VExpr}
    {sf : TcState .anon}
    (h : ApplyIotaRuleTrace layer semantics trProj world support uvars Delta
      methods rule recUs recr spine ctorArgs ctorFields transient startV s
      final finalV sf)
    (hempty : recUs.isEmpty = true) :
    h.rhs = rule.rhs ∧ h.after = s := by
  have hrun := h.instantiate
  rw [TcM.instantiateUnivParams, if_pos hempty] at hrun
  have hinj := EStateM.Result.ok.inj hrun
  exact ⟨hinj.1.symm, hinj.2.symm⟩

/-- Resource/state facts for the universe-instantiation prefix of the trace. -/
theorem instantiatePost
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {rule : RecRule .anon} {recUs : Array (KUniv .anon)}
    {recr : IotaInfo .anon} {spine ctorArgs : Array (KExpr .anon)}
    {ctorFields : Nat} {transient : Bool} {startV : VExpr}
    {s : TcState .anon} {final : KExpr .anon} {finalV : VExpr}
    {sf : TcState .anon}
    (h : ApplyIotaRuleTrace layer semantics trProj world support uvars Delta
      methods rule recUs recr spine ctorArgs ctorFields transient startV s
      final finalV sf)
    (hcollision : support.CollisionFree)
    (hreach : ∀ x, KExpr.InstUnivReach recUs rule.rhs x → support x)
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s) :
    KExpr.instantiateUnivParamsSpec rule.rhs recUs = .ok h.rhs ∧
      WhnfStateInv layer semantics trProj world support uvars Delta h.after ∧
      InternUpdateFrame s h.after ∧
      support h.rhs :=
  TcM.instantiateUnivParams_whnf_of_run hcollision hreach hI h.instantiate

/-- Complete selected-rule contract before relating the applied registered
RHS back to the original recursor application. -/
theorem acceptance
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {rule : RecRule .anon} {recUs : Array (KUniv .anon)}
    {recr : IotaInfo .anon} {spine ctorArgs : Array (KExpr .anon)}
    {ctorFields : Nat} {transient : Bool} {startV : VExpr}
    {s : TcState .anon} {final : KExpr .anon} {finalV : VExpr}
    {sf : TcState .anon}
    (h : ApplyIotaRuleTrace layer semantics trProj world support uvars Delta
      methods rule recUs recr spine ctorArgs ctorFields transient startV s
      final finalV sf)
    (theory : WhnfTheory trProj world uvars)
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    (hcollision : support.CollisionFree)
    (hreach : ∀ x, KExpr.InstUnivReach recUs rule.rhs x → support x)
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s)
    (hrhsTr : TrKExpr world.venv uvars world.nameOf trProj Delta h.rhs
      startV) :
    (applyIotaRule rule recUs recr spine ctorArgs ctorFields transient).run
        methods s = .ok final sf ∧
      WhnfStateInv layer semantics trProj world support uvars Delta sf ∧
      InternUpdateFrame s sf ∧
      support final ∧
      TrKExpr world.venv uvars world.nameOf trProj Delta final finalV ∧
      WhnfMeaning trProj world uvars Delta
        ((((iotaPrefixArgs recr spine).toList ++
          (iotaFieldArgs ctorArgs ctorFields).toList) ++
          (iotaTrailingArgs recr spine).toList).foldl
            KExpr.mkApp h.rhs) final := by
  obtain ⟨hspec, hafterI, hinstFrame, hrhsSupport⟩ :=
    h.instantiatePost hcollision hreach hI
  have hargs := ApplyIotaArgsTrace.threeArrayAcceptanceQuot
    h.prefixTrace h.fieldTrace h.trailingTrace theory hDelta hafterI
      hrhsSupport hrhsTr
  obtain ⟨hargsRun, hfinalI, hargsFrame, hfinalSupport, hfinalTr,
    hmeaning⟩ := hargs
  exact ⟨h.eval, hfinalI, hinstFrame.trans hargsFrame, hfinalSupport,
    hfinalTr, hmeaning⟩

/-- Parameter-free selected-rule contract.  Since production does not invoke
the universe walker, no collision or walker-reach premise is needed; support
of the unchanged registered body is the exact resource assumption. -/
theorem acceptance_empty
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {rule : RecRule .anon} {recUs : Array (KUniv .anon)}
    {recr : IotaInfo .anon} {spine ctorArgs : Array (KExpr .anon)}
    {ctorFields : Nat} {transient : Bool} {startV : VExpr}
    {s : TcState .anon} {final : KExpr .anon} {finalV : VExpr}
    {sf : TcState .anon}
    (h : ApplyIotaRuleTrace layer semantics trProj world support uvars Delta
      methods rule recUs recr spine ctorArgs ctorFields transient startV s
      final finalV sf)
    (hempty : recUs.isEmpty = true)
    (theory : WhnfTheory trProj world uvars)
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s)
    (hruleSupport : support rule.rhs)
    (hruleTr : TrKExpr world.venv uvars world.nameOf trProj Delta rule.rhs
      startV) :
    (applyIotaRule rule recUs recr spine ctorArgs ctorFields transient).run
        methods s = .ok final sf ∧
      WhnfStateInv layer semantics trProj world support uvars Delta sf ∧
      InternUpdateFrame s sf ∧
      support final ∧
      TrKExpr world.venv uvars world.nameOf trProj Delta final finalV ∧
      WhnfMeaning trProj world uvars Delta
        ((((iotaPrefixArgs recr spine).toList ++
          (iotaFieldArgs ctorArgs ctorFields).toList) ++
          (iotaTrailingArgs recr spine).toList).foldl
            KExpr.mkApp h.rhs) final := by
  obtain ⟨hrhs, hafter⟩ := h.emptyInstantiation hempty
  have hafterI : WhnfStateInv layer semantics trProj world support uvars
      Delta h.after := by simpa only [hafter] using hI
  have hrhsSupport : support h.rhs := by
    simpa only [hrhs] using hruleSupport
  have hrhsTr : TrKExpr world.venv uvars world.nameOf trProj Delta h.rhs
      startV := by simpa only [hrhs] using hruleTr
  have hargs := ApplyIotaArgsTrace.threeArrayAcceptanceQuot
    h.prefixTrace h.fieldTrace h.trailingTrace theory hDelta hafterI
      hrhsSupport hrhsTr
  obtain ⟨hargsRun, hfinalI, hargsFrame, hfinalSupport, hfinalTr,
    hmeaning⟩ := hargs
  have hinstFrame : InternUpdateFrame s h.after := by
    simpa only [hafter] using InternUpdateFrame.refl s
  exact ⟨h.eval, hfinalI, hinstFrame.trans hargsFrame, hfinalSupport,
    hfinalTr, hmeaning⟩

/-- A parameter-free admitted rule starts at its registered Theory RHS.
Unlike the nonempty theorem below, this is a direct embedding of the stored
structural translation: production returns the rule body unchanged, and the
registered equation has universe arity zero. -/
theorem registeredStartQuot_empty
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {methods : Methods .anon}
    {id : KId .anon} {recursor : KConst .anon}
    {rule : RecRule .anon} {defeq : VDefEq}
    {recUs : Array (KUniv .anon)}
    {recr : IotaInfo .anon} {spine ctorArgs : Array (KExpr .anon)}
    {ctorFields : Nat} {transient : Bool} {startV : VExpr}
    {s : TcState .anon} {final : KExpr .anon} {finalV : VExpr}
    {sf : TcState .anon}
    (h : ApplyIotaRuleTrace layer semantics trProj world support 0 []
      methods rule recUs recr spine ctorArgs ctorFields transient startV s
      final finalV sf)
    (hregistered : RegisteredRecursorRuleRhsRel world.venv world.nameOf
      trProj id recursor rule defeq)
    (theory : WhnfTheory trProj world 0)
    (hempty : recUs.isEmpty = true)
    (harity : defeq.uvars = 0)
    (hstartV : startV = defeq.rhs) :
    TrKExpr world.venv 0 world.nameOf trProj [] h.rhs startV := by
  obtain ⟨hrhs, _⟩ := h.emptyInstantiation hempty
  have hstruct := hregistered.rhsStructural
  rw [harity] at hstruct
  have hquot := hstruct.trKExpr world.venvWF.ordered theory.literalWF
    theory.projections.wf (by trivial)
  simpa only [hrhs, hstartV] using hquot

/-- Registered-rule specialization for production's parameter-free path.
The unchanged rule body must be in support, but no universe-instantiation
collision or reachability premise is necessary. -/
theorem registeredAcceptance_empty
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {methods : Methods .anon}
    {id : KId .anon} {recursor : KConst .anon}
    {rule : RecRule .anon} {defeq : VDefEq}
    {recUs : Array (KUniv .anon)}
    {recr : IotaInfo .anon} {spine ctorArgs : Array (KExpr .anon)}
    {ctorFields : Nat} {transient : Bool} {startV : VExpr}
    {s : TcState .anon} {final : KExpr .anon} {finalV : VExpr}
    {sf : TcState .anon}
    (h : ApplyIotaRuleTrace layer semantics trProj world support 0 []
      methods rule recUs recr spine ctorArgs ctorFields transient startV s
      final finalV sf)
    (hregistered : RegisteredRecursorRuleRhsRel world.venv world.nameOf
      trProj id recursor rule defeq)
    (theory : WhnfTheory trProj world 0)
    (hempty : recUs.isEmpty = true)
    (harity : defeq.uvars = 0)
    (hI : WhnfStateInv layer semantics trProj world support 0 [] s)
    (hruleSupport : support rule.rhs)
    (hstartV : startV = defeq.rhs) :
    (applyIotaRule rule recUs recr spine ctorArgs ctorFields transient).run
        methods s = .ok final sf ∧
      WhnfStateInv layer semantics trProj world support 0 [] sf ∧
      InternUpdateFrame s sf ∧
      support final ∧
      TrKExpr world.venv 0 world.nameOf trProj [] final finalV ∧
      WhnfMeaning trProj world 0 []
        ((((iotaPrefixArgs recr spine).toList ++
          (iotaFieldArgs ctorArgs ctorFields).toList) ++
          (iotaTrailingArgs recr spine).toList).foldl
            KExpr.mkApp h.rhs) final := by
  apply h.acceptance_empty hempty theory (by trivial) hI hruleSupport
  obtain ⟨hrhs, _⟩ := h.emptyInstantiation hempty
  simpa only [hrhs] using
    (h.registeredStartQuot_empty hregistered theory hempty harity hstartV)

/-- RuleInstantiation supplies the trace's initial quotient translation for a nonempty
universe instantiation of an admitted registered rule.  This theorem is
closed-context because the registered rule body is admitted closed; the
future open-context theorem must explicitly weaken that witness. -/
theorem registeredStartQuot_nonempty
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {methods : Methods .anon}
    {id : KId .anon} {recursor : KConst .anon}
    {rule : RecRule .anon} {defeq : VDefEq}
    {recUs : Array (KUniv .anon)}
    {recr : IotaInfo .anon} {spine ctorArgs : Array (KExpr .anon)}
    {ctorFields : Nat} {transient : Bool} {startV : VExpr}
    {s : TcState .anon} {final : KExpr .anon} {finalV : VExpr}
    {sf : TcState .anon}
    (h : ApplyIotaRuleTrace layer semantics trProj world support uvars []
      methods rule recUs recr spine ctorArgs ctorFields transient startV s
      final finalV sf)
    (hregistered : RegisteredRecursorRuleRhsRel world.venv world.nameOf
      trProj id recursor rule defeq)
    (theory : WhnfTheory trProj world uvars)
    (hnonempty : recUs.isEmpty = false)
    (hus : ∀ level ∈ recUs, (KUniv.toVLevel level).WF uvars)
    (harity : defeq.uvars = recUs.size)
    (hcollision : support.CollisionFree)
    (hreach : ∀ x, KExpr.InstUnivReach recUs rule.rhs x → support x)
    (hI : WhnfStateInv layer semantics trProj world support uvars [] s)
    (hfaithful : ∀ left right,
      KExpr.LevelReach recUs rule.rhs left →
      KExpr.LevelReach recUs rule.rhs right → left.AddrFaithful right)
    (hsize : ∀ level, KExpr.LevelReach recUs rule.rhs level →
      level.size < UInt64.size)
    (hstartV : startV =
      defeq.rhs.instL (recUs.toList.map KUniv.toVLevel)) :
    TrKExpr world.venv uvars world.nameOf trProj [] h.rhs startV := by
  have hresult := hregistered.instantiateUnivParams_nonempty
    world.venvWF theory.literalWF theory.projections hnonempty hus harity
    hcollision.expr hreach
    ⟨hI.1.core.intern, hI.1.internSupport.expr⟩ h.instantiate hfaithful hsize
  simpa only [hstartV] using hresult

/-- Registered-rule specialization of `acceptance`: RuleInstantiation and the successful
production instantiator jointly discharge the initial quotient premise. -/
theorem registeredAcceptance_nonempty
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {methods : Methods .anon}
    {id : KId .anon} {recursor : KConst .anon}
    {rule : RecRule .anon} {defeq : VDefEq}
    {recUs : Array (KUniv .anon)}
    {recr : IotaInfo .anon} {spine ctorArgs : Array (KExpr .anon)}
    {ctorFields : Nat} {transient : Bool} {startV : VExpr}
    {s : TcState .anon} {final : KExpr .anon} {finalV : VExpr}
    {sf : TcState .anon}
    (h : ApplyIotaRuleTrace layer semantics trProj world support uvars []
      methods rule recUs recr spine ctorArgs ctorFields transient startV s
      final finalV sf)
    (hregistered : RegisteredRecursorRuleRhsRel world.venv world.nameOf
      trProj id recursor rule defeq)
    (theory : WhnfTheory trProj world uvars)
    (hnonempty : recUs.isEmpty = false)
    (hus : ∀ level ∈ recUs, (KUniv.toVLevel level).WF uvars)
    (harity : defeq.uvars = recUs.size)
    (hcollision : support.CollisionFree)
    (hreach : ∀ x, KExpr.InstUnivReach recUs rule.rhs x → support x)
    (hI : WhnfStateInv layer semantics trProj world support uvars [] s)
    (hfaithful : ∀ left right,
      KExpr.LevelReach recUs rule.rhs left →
      KExpr.LevelReach recUs rule.rhs right → left.AddrFaithful right)
    (hsize : ∀ level, KExpr.LevelReach recUs rule.rhs level →
      level.size < UInt64.size)
    (hstartV : startV =
      defeq.rhs.instL (recUs.toList.map KUniv.toVLevel)) :
    (applyIotaRule rule recUs recr spine ctorArgs ctorFields transient).run
        methods s = .ok final sf ∧
      WhnfStateInv layer semantics trProj world support uvars [] sf ∧
      InternUpdateFrame s sf ∧
      support final ∧
      TrKExpr world.venv uvars world.nameOf trProj [] final finalV ∧
      WhnfMeaning trProj world uvars []
        ((((iotaPrefixArgs recr spine).toList ++
          (iotaFieldArgs ctorArgs ctorFields).toList) ++
          (iotaTrailingArgs recr spine).toList).foldl
            KExpr.mkApp h.rhs) final := by
  apply h.acceptance theory (by trivial) hcollision hreach hI
  exact h.registeredStartQuot_nonempty hregistered theory hnonempty hus
    harity hcollision hreach hI hfaithful hsize hstartV

/-- A checked pattern reduction plus the explicit RHS-alignment certificate
relates the original concrete recursor application directly to the trace's
final concrete result. -/
theorem checkedMeaning
    {trProj : RawProjRel} {world : VerifyWorld}
    {uvars : Nat} {Delta : KVLCtx}
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    {id : KId .anon} {recursor : KConst .anon}
    {rule : RecRule .anon} {pattern : RecursorRulePattern}
    (hpattern : RawRecursorRulePatternRel world.venv world.catalog
      world.nameOf id recursor rule pattern)
    {source final : KExpr .anon} {sourceV sourceType finalV : VExpr}
    (hsourceTr : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV)
    (hsourceType : world.venv.HasType uvars Delta.toCtx sourceV sourceType)
    {levels : List Lean4Lean.VLevel}
    {captures : (RecursorIotaPattern pattern.recursorName pattern.majorIdx
      pattern.constructorName
      (pattern.constructorParams.toNat +
        pattern.constructorFields.toNat)).Path → VExpr}
    (hmatch : Lean4Lean.Pattern.Matches
      (RecursorIotaPattern pattern.recursorName pattern.majorIdx
        pattern.constructorName
        (pattern.constructorParams.toNat +
          pattern.constructorFields.toNat))
      sourceV levels captures)
    (hchecks : pattern.checks.OK
      (world.venv.IsDefEqU uvars Delta.toCtx) levels captures)
    (haligned : IotaRhsApplicationAligned pattern levels captures finalV)
    (hfinalTr : TrKExpr world.venv uvars world.nameOf trProj Delta final
      finalV) :
    WhnfMeaning trProj world uvars Delta source final := by
  have hsourceFinal := hpattern.checkedReduction world.venvWF hDelta.toCtx
    hmatch hsourceType hchecks
  change finalV = pattern.rhs.apply levels captures at haligned
  rw [← haligned] at hsourceFinal
  obtain ⟨resultV, hresultTr, hresultEq⟩ := hfinalTr
  exact ⟨sourceV, resultV, hsourceTr, hresultTr,
    hsourceFinal.trans world.venvWF hDelta hresultEq.symm⟩

/-- Checked selected-rule execution for a parameter-free registered rule.
This closes the fast path end to end while retaining the admission-side RHS
alignment premise that is also required by the nonempty path. -/
theorem checkedAcceptance_empty
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {methods : Methods .anon}
    {id : KId .anon} {recursor : KConst .anon}
    {rule : RecRule .anon} {defeq : VDefEq}
    {recUs : Array (KUniv .anon)}
    {recr : IotaInfo .anon} {spine ctorArgs : Array (KExpr .anon)}
    {ctorFields : Nat} {transient : Bool} {startV : VExpr}
    {s : TcState .anon} {final : KExpr .anon} {finalV : VExpr}
    {sf : TcState .anon}
    (h : ApplyIotaRuleTrace layer semantics trProj world support 0 []
      methods rule recUs recr spine ctorArgs ctorFields transient startV s
      final finalV sf)
    (hregistered : RegisteredRecursorRuleRhsRel world.venv world.nameOf
      trProj id recursor rule defeq)
    (theory : WhnfTheory trProj world 0)
    (hempty : recUs.isEmpty = true)
    (harity : defeq.uvars = 0)
    (hI : WhnfStateInv layer semantics trProj world support 0 [] s)
    (hruleSupport : support rule.rhs)
    (hstartV : startV = defeq.rhs)
    {pattern : RecursorRulePattern}
    (hpattern : RawRecursorRulePatternRel world.venv world.catalog
      world.nameOf id recursor rule pattern)
    {source : KExpr .anon} {sourceV sourceType : VExpr}
    (hsourceTr : TrKExprS world.venv 0 world.nameOf trProj [] source
      sourceV)
    (hsourceType : world.venv.HasType 0 [] sourceV sourceType)
    {levels : List Lean4Lean.VLevel}
    {captures : (RecursorIotaPattern pattern.recursorName pattern.majorIdx
      pattern.constructorName
      (pattern.constructorParams.toNat +
        pattern.constructorFields.toNat)).Path → VExpr}
    (hmatch : Lean4Lean.Pattern.Matches
      (RecursorIotaPattern pattern.recursorName pattern.majorIdx
        pattern.constructorName
        (pattern.constructorParams.toNat +
          pattern.constructorFields.toNat))
      sourceV levels captures)
    (hchecks : pattern.checks.OK
      (world.venv.IsDefEqU 0 []) levels captures)
    (haligned : IotaRhsApplicationAligned pattern levels captures finalV) :
    (applyIotaRule rule recUs recr spine ctorArgs ctorFields transient).run
        methods s = .ok final sf ∧
      WhnfStateInv layer semantics trProj world support 0 [] sf ∧
      InternUpdateFrame s sf ∧
      support final ∧
      WhnfMeaning trProj world 0 [] source final := by
  have hacc := h.registeredAcceptance_empty hregistered theory hempty
    harity hI hruleSupport hstartV
  obtain ⟨hrun, hfinalI, hframe, hfinalSupport, hfinalTr, hfoldMeaning⟩ :=
    hacc
  exact ⟨hrun, hfinalI, hframe, hfinalSupport,
    checkedMeaning (by trivial) hpattern hsourceTr hsourceType hmatch
      hchecks haligned hfinalTr⟩

/-- Headline SelectedRule contract.  One selected nonempty-universe rule executes
through production's exact slices and is semantically sound for the original
recursor application, conditional only on the explicit admission-side RHS
alignment that the current oracle does not yet store. -/
theorem checkedAcceptance_nonempty
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {methods : Methods .anon}
    {id : KId .anon} {recursor : KConst .anon}
    {rule : RecRule .anon} {defeq : VDefEq}
    {recUs : Array (KUniv .anon)}
    {recr : IotaInfo .anon} {spine ctorArgs : Array (KExpr .anon)}
    {ctorFields : Nat} {transient : Bool} {startV : VExpr}
    {s : TcState .anon} {final : KExpr .anon} {finalV : VExpr}
    {sf : TcState .anon}
    (h : ApplyIotaRuleTrace layer semantics trProj world support uvars []
      methods rule recUs recr spine ctorArgs ctorFields transient startV s
      final finalV sf)
    (hregistered : RegisteredRecursorRuleRhsRel world.venv world.nameOf
      trProj id recursor rule defeq)
    (theory : WhnfTheory trProj world uvars)
    (hnonempty : recUs.isEmpty = false)
    (hus : ∀ level ∈ recUs, (KUniv.toVLevel level).WF uvars)
    (harity : defeq.uvars = recUs.size)
    (hcollision : support.CollisionFree)
    (hreach : ∀ x, KExpr.InstUnivReach recUs rule.rhs x → support x)
    (hI : WhnfStateInv layer semantics trProj world support uvars [] s)
    (hfaithful : ∀ left right,
      KExpr.LevelReach recUs rule.rhs left →
      KExpr.LevelReach recUs rule.rhs right → left.AddrFaithful right)
    (hsize : ∀ level, KExpr.LevelReach recUs rule.rhs level →
      level.size < UInt64.size)
    (hstartV : startV =
      defeq.rhs.instL (recUs.toList.map KUniv.toVLevel))
    {pattern : RecursorRulePattern}
    (hpattern : RawRecursorRulePatternRel world.venv world.catalog
      world.nameOf id recursor rule pattern)
    {source : KExpr .anon} {sourceV sourceType : VExpr}
    (hsourceTr : TrKExprS world.venv uvars world.nameOf trProj [] source
      sourceV)
    (hsourceType : world.venv.HasType uvars [] sourceV sourceType)
    {levels : List Lean4Lean.VLevel}
    {captures : (RecursorIotaPattern pattern.recursorName pattern.majorIdx
      pattern.constructorName
      (pattern.constructorParams.toNat +
        pattern.constructorFields.toNat)).Path → VExpr}
    (hmatch : Lean4Lean.Pattern.Matches
      (RecursorIotaPattern pattern.recursorName pattern.majorIdx
        pattern.constructorName
        (pattern.constructorParams.toNat +
          pattern.constructorFields.toNat))
      sourceV levels captures)
    (hchecks : pattern.checks.OK
      (world.venv.IsDefEqU uvars []) levels captures)
    (haligned : IotaRhsApplicationAligned pattern levels captures finalV) :
    (applyIotaRule rule recUs recr spine ctorArgs ctorFields transient).run
        methods s = .ok final sf ∧
      WhnfStateInv layer semantics trProj world support uvars [] sf ∧
      InternUpdateFrame s sf ∧
      support final ∧
      WhnfMeaning trProj world uvars [] source final := by
  have hacc := h.registeredAcceptance_nonempty hregistered theory hnonempty
    hus harity hcollision hreach hI hfaithful hsize hstartV
  obtain ⟨hrun, hfinalI, hframe, hfinalSupport, hfinalTr, hfoldMeaning⟩ :=
    hacc
  exact ⟨hrun, hfinalI, hframe, hfinalSupport,
    checkedMeaning (by trivial) hpattern hsourceTr hsourceType hmatch
      hchecks haligned hfinalTr⟩

end ApplyIotaRuleTrace

end RecM

end Ix.Tc
