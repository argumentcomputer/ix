import Ix.Tc.Verify.Whnf.Iota.ArgumentBranches

/-!
# Semantic execution of iota argument lists

Ordinary iota applies three consecutive argument segments to an instantiated
rule RHS: parameters/motives/minors from the source spine, constructor fields,
and the source's trailing over-application.  Nat-literal iota uses the same
segments, but beta-reduces transient lambda intermediates without interning.

The one-argument branches proved in Substitution/ArgumentBranches therefore cannot be composed by
tracking structural syntax alone: a transient beta result generally is not a
structural translation of the Theory application that preceded it.  This
slice tracks the result in the quotient relation `TrKExpr` instead.  Each
successful step records its exact production run, invariant/frame facts,
finite support, and `WhnfMeaning`; induction then transports the quotient
translation through every intermediate.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

namespace KExpr

/-- The transient substitution fast path is syntax-independent: once the
stored loose-bvar bound is below the current depth, no constructor inspection
or rebuilding occurs. -/
theorem substNoIntern_of_lbr_le {body arg : KExpr m} {depth : UInt64}
    (h : body.lbr ≤ depth) : substNoIntern body arg depth = body := by
  cases body <;> simp_all [substNoIntern]

/-- Closed-at-cutoff terms are unchanged by the local lift used at a
transient substitution hit. -/
theorem liftNoIntern_of_lbr_le {e : KExpr m} {shift cutoff : UInt64}
    (h : e.lbr ≤ cutoff) :
    substNoIntern.liftNoIntern e shift cutoff = e := by
  cases e <;> simp_all [substNoIntern.liftNoIntern]

end KExpr

namespace WhnfMeaning

/-- If a source has a quotient translation and reduces with `WhnfMeaning`,
the concrete result has the same quotient translation.  Structural
translation uniqueness reconciles the source representative stored in the
meaning proof with the representative stored in the quotient. -/
theorem resultQuot
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    (theory : WhnfTheory trProj world uvars)
    {Delta : KVLCtx} (hDelta : KVLCtx.WF world.venv uvars Delta)
    {source result : KExpr .anon} {target : VExpr}
    (hsource : TrKExpr world.venv uvars world.nameOf trProj Delta
      source target)
    (hmeaning : WhnfMeaning trProj world uvars Delta source result) :
    TrKExpr world.venv uvars world.nameOf trProj Delta result target := by
  obtain ⟨sourceV, resultV, hsourceS, hresultS, hdefeq⟩ := hmeaning
  have hsourceQ := hsourceS.trKExpr world.venvWF.ordered
    theory.literalWF theory.projections.wf hDelta
  have hctx := KVLCtx.IsDefEq.refl world.venvWF hDelta
  have hsourceEq := hsourceQ.uniq world.venvWF theory.literalWF
    theory.projections hctx hsource
  have hresultEq := hdefeq.symm.trans world.venvWF hDelta hsourceEq
  exact (hresultS.trKExpr world.venvWF.ordered theory.literalWF
    theory.projections.wf hDelta).defeq world.venvWF hDelta hresultEq

/-- A structural source and a quotient-translated result at the same Theory
expression form a `WhnfMeaning` proof.  The quotient's representative may
differ syntactically; its stored equality supplies the semantic bridge. -/
theorem ofStructuralQuot
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {source result : KExpr .anon} {target : VExpr}
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta
      source target)
    (hresult : TrKExpr world.venv uvars world.nameOf trProj Delta
      result target) :
    WhnfMeaning trProj world uvars Delta source result := by
  obtain ⟨resultV, hresultS, hresultEq⟩ := hresult
  exact ⟨target, resultV, hsource, hresultS, hresultEq.symm⟩

end WhnfMeaning

namespace RecM

/-- The extracted production loop is exactly a left-to-right monadic fold.
This equation fixes argument order independently of the three array slices
selected by ordinary iota. -/
theorem applyIotaArgs_eq_foldlM (result : KExpr m)
    (args : Array (KExpr m)) (transient : Bool) :
    applyIotaArgs result args transient =
      args.foldlM (m := RecM m)
        (fun result arg => applyIotaArg result arg transient) result := by
  unfold applyIotaArgs
  simp [Array.forIn_yield_eq_foldlM]

/-- A successful, semantically justified execution of `applyIotaArg` over a
list in production order.  The Theory index is the unreduced left-associated
application.  Concrete intermediates may instead be beta-reduced terms; the
step meaning is what relates the two views. -/
inductive ApplyIotaArgsTrace
    (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (Delta : KVLCtx) (methods : Methods .anon)
    (transient : Bool) :
    KExpr .anon → VExpr → TcState .anon →
      List (KExpr .anon) → KExpr .anon → VExpr →
      TcState .anon → Prop
  | nil (result resultV s) :
      ApplyIotaArgsTrace layer semantics trProj world support uvars Delta
        methods transient result resultV s [] result resultV s
  | cons {result resultV s arg argV A B next s1 rest final finalV sf}
      (hfun : world.venv.HasType uvars Delta.toCtx resultV
        (.forallE A B))
      (harg : world.venv.HasType uvars Delta.toCtx argV A)
      (hargTr : TrKExprS world.venv uvars world.nameOf trProj Delta arg argV)
      (hrun : (applyIotaArg result arg transient).run methods s =
        .ok next s1)
      (hpost : WhnfStateInv layer semantics trProj world support uvars Delta
        s1)
      (hframe : InternUpdateFrame s s1)
      (hnextSupport : support next)
      (hmeaning : WhnfMeaning trProj world uvars Delta
        (KExpr.mkApp result arg) next)
      (tail : ApplyIotaArgsTrace layer semantics trProj world support uvars
        Delta methods transient next (.app resultV argV) s1 rest final
        finalV sf) :
      ApplyIotaArgsTrace layer semantics trProj world support uvars Delta
        methods transient result resultV s (arg :: rest) final finalV sf

namespace ApplyIotaArgsTrace

/-- One justified argument step is a singleton trace. -/
theorem singleton
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {transient : Bool} {result next : KExpr .anon}
    {resultV argV A B : VExpr} {arg : KExpr .anon}
    {s s1 : TcState .anon}
    (hfun : world.venv.HasType uvars Delta.toCtx resultV (.forallE A B))
    (harg : world.venv.HasType uvars Delta.toCtx argV A)
    (hargTr : TrKExprS world.venv uvars world.nameOf trProj Delta arg argV)
    (hrun : (applyIotaArg result arg transient).run methods s = .ok next s1)
    (hpost : WhnfStateInv layer semantics trProj world support uvars Delta s1)
    (hframe : InternUpdateFrame s s1)
    (hnextSupport : support next)
    (hmeaning : WhnfMeaning trProj world uvars Delta
      (KExpr.mkApp result arg) next) :
    ApplyIotaArgsTrace layer semantics trProj world support uvars Delta
      methods transient result resultV s [arg] next (.app resultV argV) s1 :=
  .cons hfun harg hargTr hrun hpost hframe hnextSupport hmeaning
    (.nil next (.app resultV argV) s1)

/-- Sequential traces concatenate without losing their intermediate state or
quotient Theory index. -/
theorem append
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {transient : Bool} {start middle final : KExpr .anon}
    {startV middleV finalV : VExpr} {s sm sf : TcState .anon}
    {first second : List (KExpr .anon)}
    (hfirst : ApplyIotaArgsTrace layer semantics trProj world support uvars
      Delta methods transient start startV s first middle middleV sm)
    (hsecond : ApplyIotaArgsTrace layer semantics trProj world support uvars
      Delta methods transient middle middleV sm second final finalV sf) :
    ApplyIotaArgsTrace layer semantics trProj world support uvars Delta
      methods transient start startV s (first ++ second) final finalV sf := by
  induction hfirst with
  | nil => exact hsecond
  | cons hfun harg hargTr hrun hpost hframe hnextSupport hmeaning tail ih =>
      exact .cons hfun harg hargTr hrun hpost hframe hnextSupport hmeaning
        (ih hsecond)

/-- Three-way specialization matching ordinary iota's prefix, constructor
field, and trailing-spine segments. -/
theorem three
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {transient : Bool} {start middle1 middle2 final : KExpr .anon}
    {startV middleV1 middleV2 finalV : VExpr}
    {s s1 s2 sf : TcState .anon}
    {first second third : List (KExpr .anon)}
    (hfirst : ApplyIotaArgsTrace layer semantics trProj world support uvars
      Delta methods transient start startV s first middle1 middleV1 s1)
    (hsecond : ApplyIotaArgsTrace layer semantics trProj world support uvars
      Delta methods transient middle1 middleV1 s1 second middle2 middleV2 s2)
    (hthird : ApplyIotaArgsTrace layer semantics trProj world support uvars
      Delta methods transient middle2 middleV2 s2 third final finalV sf) :
    ApplyIotaArgsTrace layer semantics trProj world support uvars Delta
      methods transient start startV s ((first ++ second) ++ third) final
        finalV sf :=
  (hfirst.append hsecond).append hthird

/-- Quotient-aware package for ArgumentBranches's transient non-lambda branch.  The
`expectedV` head may differ from the structural translation `resultV` of the
concrete intermediate; this is exactly what happens after an earlier
transient beta step. -/
theorem transientNonLambdaSingletonQuot
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {result arg : KExpr .anon}
    {expectedV resultV argV expectedA expectedB A B : VExpr}
    {s : TcState .anon}
    (hnonlam : IotaArgNonLambda result)
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s)
    (hresultSupport : support (KExpr.mkApp result arg))
    (hexpectedTy : world.venv.HasType uvars Delta.toCtx expectedV
      (.forallE expectedA expectedB))
    (hexpectedArgTy : world.venv.HasType uvars Delta.toCtx argV expectedA)
    (hresultTy : world.venv.HasType uvars Delta.toCtx resultV
      (.forallE A B))
    (hargTy : world.venv.HasType uvars Delta.toCtx argV A)
    (hresultTr : TrKExprS world.venv uvars world.nameOf trProj Delta
      result resultV)
    (hargTr : TrKExprS world.venv uvars world.nameOf trProj Delta arg argV) :
    ApplyIotaArgsTrace layer semantics trProj world support uvars Delta
      methods true result expectedV s [arg] (KExpr.mkApp result arg)
        (.app expectedV argV) s := by
  obtain ⟨hrun, hmeaning⟩ := applyIotaArg_true_nonlam_semantic
    (sourceInfo := (KExpr.mkApp result arg).info)
    hnonlam methods s hresultTy hargTy hresultTr hargTr
  apply singleton hexpectedTy hexpectedArgTy hargTr hrun hI
    (InternUpdateFrame.refl s) hresultSupport
  rw [KExpr.mkApp_shape]
  exact hmeaning

/-- Structural specialization of `transientNonLambdaSingletonQuot`. -/
theorem transientNonLambdaSingleton
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {result arg : KExpr .anon} {resultV argV A B : VExpr}
    {s : TcState .anon}
    (hnonlam : IotaArgNonLambda result)
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s)
    (hresultSupport : support (KExpr.mkApp result arg))
    (hresultTy : world.venv.HasType uvars Delta.toCtx resultV
      (.forallE A B))
    (hargTy : world.venv.HasType uvars Delta.toCtx argV A)
    (hresultTr : TrKExprS world.venv uvars world.nameOf trProj Delta
      result resultV)
    (hargTr : TrKExprS world.venv uvars world.nameOf trProj Delta arg argV) :
    ApplyIotaArgsTrace layer semantics trProj world support uvars Delta
      methods true result resultV s [arg] (KExpr.mkApp result arg)
        (.app resultV argV) s :=
  transientNonLambdaSingletonQuot hnonlam hI hresultSupport
    hresultTy hargTy hresultTy hargTy hresultTr hargTr

/-- Package ArgumentBranches's ordinary interned branch as a singleton executor trace.
The returned state is existential because the intern table may grow. -/
theorem internedSingleton
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {result arg : KExpr .anon} {resultV argV A B : VExpr}
    {s : TcState .anon}
    (hcollision : support.CollisionFree)
    (hresultSupport : support (KExpr.mkApp result arg))
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s)
    (hresultTy : world.venv.HasType uvars Delta.toCtx resultV
      (.forallE A B))
    (hargTy : world.venv.HasType uvars Delta.toCtx argV A)
    (hresultTr : TrKExprS world.venv uvars world.nameOf trProj Delta
      result resultV)
    (hargTr : TrKExprS world.venv uvars world.nameOf trProj Delta arg argV) :
    ∃ s1,
      ApplyIotaArgsTrace layer semantics trProj world support uvars Delta
        methods false result resultV s [arg] (KExpr.mkApp result arg)
          (.app resultV argV) s1 := by
  obtain ⟨s1, hrun, hpost, hframe, hmeaning⟩ :=
    applyIotaArg_false_semantic
      (sourceInfo := (KExpr.mkApp result arg).info)
      hcollision hresultSupport hI methods hresultTy hargTy hresultTr hargTr
  refine ⟨s1, singleton hresultTy hargTy hargTr hrun hpost hframe
    hresultSupport ?_⟩
  rw [KExpr.mkApp_shape]
  exact hmeaning

/-- Quotient-aware package for Substitution's transient beta branch.  The concrete
lambda is translated structurally for the beta proof, while `expectedV` is
the quotient-level head inherited from all preceding argument steps. -/
theorem transientLambdaSingletonQuot
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {ty body arg : KExpr .anon} {info : ExprInfo .anon}
    {expectedV expectedA expectedB A bodyV argV B : VExpr}
    {univ : Lean4Lean.VLevel}
    {s : TcState .anon}
    (hexpectedTy : world.venv.HasType uvars Delta.toCtx expectedV
      (.forallE expectedA expectedB))
    (hexpectedArgTy : world.venv.HasType uvars Delta.toCtx argV expectedA)
    (projections : TrProjOK world.venv uvars trProj)
    (hty : TrKExprS world.venv uvars world.nameOf trProj Delta ty A)
    (hbody : TrKExprS world.venv uvars world.nameOf trProj
      ((none, .vlam A) :: Delta) body bodyV)
    (harg : TrKExprS world.venv uvars world.nameOf trProj Delta arg argV)
    (hA : world.venv.HasType uvars Delta.toCtx A (.sort univ))
    (hbodyTy : world.venv.HasType uvars (A :: Delta.toCtx) bodyV B)
    (hargTy : world.venv.HasType uvars Delta.toCtx argV A)
    (hbodyCon : KExpr.Constructed body)
    (hargCon : KExpr.Constructed arg)
    (hbig : Delta.bvars + body.size + arg.size < UInt64.size)
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s)
    (hresultSupport : support (substNoIntern body arg 0)) :
    ApplyIotaArgsTrace layer semantics trProj world support uvars Delta
      methods true (.lam name bi ty body info) expectedV s [arg]
        (substNoIntern body arg 0) (.app expectedV argV) s := by
  have hrun :
      (applyIotaArg (.lam name bi ty body info) arg true).run methods s =
        .ok (substNoIntern body arg 0) s := by
    rw [Ix.Tc.RecM.applyIotaArg_true_lam]
    rfl
  have hmeaning := WhnfMeaning.betaNoIntern (trProj := trProj)
    (world := world) (uvars := uvars) (Delta := Delta)
    (projections := projections)
    (nm := name) (bi := bi)
    (lamMd := info) (appMd :=
      (KExpr.mkApp (.lam name bi ty body info) arg).info)
    (bodyV := bodyV) (B := B)
    hty hbody harg hA hbodyTy hargTy hbodyCon hargCon hbig
  apply singleton hexpectedTy hexpectedArgTy harg hrun hI
    (InternUpdateFrame.refl s) hresultSupport
  rw [KExpr.mkApp_shape]
  exact hmeaning

/-- Structural-head specialization of `transientLambdaSingletonQuot`.  Its
Theory index is the unreduced application, whereas its concrete result is the
exact non-interning substitution returned by production. -/
theorem transientLambdaSingleton
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {ty body arg : KExpr .anon} {info : ExprInfo .anon}
    {A bodyV argV B : VExpr} {univ : Lean4Lean.VLevel}
    {s : TcState .anon}
    (projections : TrProjOK world.venv uvars trProj)
    (hty : TrKExprS world.venv uvars world.nameOf trProj Delta ty A)
    (hbody : TrKExprS world.venv uvars world.nameOf trProj
      ((none, .vlam A) :: Delta) body bodyV)
    (harg : TrKExprS world.venv uvars world.nameOf trProj Delta arg argV)
    (hA : world.venv.HasType uvars Delta.toCtx A (.sort univ))
    (hbodyTy : world.venv.HasType uvars (A :: Delta.toCtx) bodyV B)
    (hargTy : world.venv.HasType uvars Delta.toCtx argV A)
    (hbodyCon : KExpr.Constructed body)
    (hargCon : KExpr.Constructed arg)
    (hbig : Delta.bvars + body.size + arg.size < UInt64.size)
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s)
    (hresultSupport : support (substNoIntern body arg 0)) :
    ApplyIotaArgsTrace layer semantics trProj world support uvars Delta
      methods true (.lam name bi ty body info) (.lam A bodyV) s [arg]
        (substNoIntern body arg 0) (.app (.lam A bodyV) argV) s :=
  transientLambdaSingletonQuot
    (Lean4Lean.VEnv.HasType.lam hA hbodyTy) hargTy projections
    hty hbody harg hA hbodyTy hargTy hbodyCon hargCon hbig hI
    hresultSupport

/-- Erase a trace to the exact list-fold execution. -/
theorem evalList
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {transient : Bool} {start final : KExpr .anon}
    {startV finalV : VExpr} {s sf : TcState .anon}
    {args : List (KExpr .anon)}
    (h : ApplyIotaArgsTrace layer semantics trProj world support uvars Delta
      methods transient start startV s args final finalV sf) :
    (args.foldlM (m := RecM .anon)
      (fun result arg => applyIotaArg result arg transient) start).run
        methods s = .ok final sf := by
  induction h with
  | nil => rfl
  | cons hfun harg hargTr hrun hpost hframe hnextSupport hmeaning tail ih =>
      rw [List.foldlM_cons, ReaderT.run_bind]
      change EStateM.bind
        (ReaderT.run (applyIotaArg _ _ _) methods) _ _ = _
      unfold EStateM.bind
      rw [hrun]
      exact ih

/-- Array form matching the actual production helper. -/
theorem evalArray
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {transient : Bool} {start final : KExpr .anon}
    {startV finalV : VExpr} {s sf : TcState .anon}
    {args : Array (KExpr .anon)}
    (h : ApplyIotaArgsTrace layer semantics trProj world support uvars Delta
      methods transient start startV s args.toList final finalV sf) :
    (applyIotaArgs start args transient).run methods s = .ok final sf := by
  rw [applyIotaArgs_eq_foldlM]
  simpa only [← Array.foldlM_toList] using h.evalList

/-- The concrete unreduced application fold structurally translates to the
Theory application index carried by the trace. -/
theorem sourceTr
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {transient : Bool} {start final : KExpr .anon}
    {startV finalV : VExpr} {s sf : TcState .anon}
    {args : List (KExpr .anon)}
    (h : ApplyIotaArgsTrace layer semantics trProj world support uvars Delta
      methods transient start startV s args final finalV sf)
    {replacement : KExpr .anon}
    (hstart : TrKExprS world.venv uvars world.nameOf trProj Delta replacement
      startV) :
    TrKExprS world.venv uvars world.nameOf trProj Delta
      (args.foldl KExpr.mkApp replacement) finalV := by
  induction h generalizing replacement with
  | nil => exact hstart
  | cons hfun harg hargTr hrun hpost hframe hnextSupport hmeaning tail ih =>
      rw [List.foldl_cons]
      apply ih
      rw [KExpr.mkApp_shape]
      exact .app hfun harg hstart hargTr

/-- The actual concrete result quotient-translates to the unreduced Theory
application index.  This is the central invariant: transient beta and direct
application rebuilding are both admitted by the same induction. -/
theorem finalQuot
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
    (hstart : TrKExpr world.venv uvars world.nameOf trProj Delta start
      startV) :
    TrKExpr world.venv uvars world.nameOf trProj Delta final finalV := by
  induction h with
  | nil => exact hstart
  | @cons result resultV s arg argV A B next s1 rest final finalV sf
      hfun harg hargTr hrun hpost hframe hnextSupport hmeaning tail ih =>
      have hargQ := hargTr.trKExpr world.venvWF.ordered
        theory.literalWF theory.projections.wf hDelta
      have happQ : TrKExpr world.venv uvars world.nameOf trProj Delta
          (KExpr.mkApp result arg) (.app resultV argV) := by
        rw [KExpr.mkApp_shape]
        exact TrKExpr.app world.venvWF hDelta hfun harg hstart hargQ
      have hnextQ := hmeaning.resultQuot theory hDelta happQ
      exact ih hnextQ

/-- Every successful step preserves the complete fixed-layer invariant. -/
theorem finalInv
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {transient : Bool} {start final : KExpr .anon}
    {startV finalV : VExpr} {s sf : TcState .anon}
    {args : List (KExpr .anon)}
    (h : ApplyIotaArgsTrace layer semantics trProj world support uvars Delta
      methods transient start startV s args final finalV sf)
    (hI : WhnfStateInv layer semantics trProj world support uvars Delta s) :
    WhnfStateInv layer semantics trProj world support uvars Delta sf := by
  induction h with
  | nil => exact hI
  | cons hfun harg hargTr hrun hpost hframe hnextSupport hmeaning tail ih =>
      exact ih hpost

/-- All per-argument intern-only frames compose.  Transient steps contribute
the reflexive frame, while ordinary steps may grow the intern table. -/
theorem frame
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {transient : Bool} {start final : KExpr .anon}
    {startV finalV : VExpr} {s sf : TcState .anon}
    {args : List (KExpr .anon)}
    (h : ApplyIotaArgsTrace layer semantics trProj world support uvars Delta
      methods transient start startV s args final finalV sf) :
    InternUpdateFrame s sf := by
  induction h with
  | nil => exact InternUpdateFrame.refl _
  | cons hfun harg hargTr hrun hpost hframe hnextSupport hmeaning tail ih =>
      exact hframe.trans ih

/-- Finite support is threaded through beta results and rebuilt
applications, so the final reducer output is admissible as a WHNF step. -/
theorem finalSupport
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    {transient : Bool} {start final : KExpr .anon}
    {startV finalV : VExpr} {s sf : TcState .anon}
    {args : List (KExpr .anon)}
    (h : ApplyIotaArgsTrace layer semantics trProj world support uvars Delta
      methods transient start startV s args final finalV sf)
    (hstart : support start) : support final := by
  induction h with
  | nil => exact hstart
  | cons hfun harg hargTr hrun hpost hframe hnextSupport hmeaning tail ih =>
      exact ih hnextSupport

/-- Complete semantic postcondition of a certified list execution. -/
theorem acceptance
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
    (hstartTr : TrKExprS world.venv uvars world.nameOf trProj Delta start
      startV) :
    (args.foldlM (m := RecM .anon)
        (fun result arg => applyIotaArg result arg transient) start).run
          methods s = .ok final sf ∧
      WhnfStateInv layer semantics trProj world support uvars Delta sf ∧
      InternUpdateFrame s sf ∧
      support final ∧
      WhnfMeaning trProj world uvars Delta
        (args.foldl KExpr.mkApp start) final := by
  have hstartQ := hstartTr.trKExpr world.venvWF.ordered
    theory.literalWF theory.projections.wf hDelta
  exact ⟨h.evalList, h.finalInv hI, h.frame, h.finalSupport hstartSupport,
    WhnfMeaning.ofStructuralQuot (h.sourceTr hstartTr)
      (h.finalQuot theory hDelta hstartQ)⟩

/-- Execute three certified arrays through the same sequence of helper calls
used by ordinary iota.  This is stronger than merely executing their
concatenated list: it exposes both intermediate production states. -/
theorem evalThreeArrays
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
        sf) :
    (do
      let result ← applyIotaArgs start first transient
      let result ← applyIotaArgs result second transient
      applyIotaArgs result third transient).run methods s = .ok final sf := by
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (applyIotaArgs start first transient) methods) _ s = _
  unfold EStateM.bind
  rw [hfirst.evalArray]
  simp only
  rw [ReaderT.run_bind]
  change EStateM.bind
    (ReaderT.run (applyIotaArgs middle1 second transient) methods) _ s1 = _
  unfold EStateM.bind
  rw [hsecond.evalArray]
  simp only
  exact hthird.evalArray

/-- Complete ArgumentExecution contract for production's three iota argument segments.
The operational conclusion uses three actual `applyIotaArgs` calls; the
semantic conclusion uses their single left-associated Theory application
sequence and retains trailing over-application. -/
theorem threeArrayAcceptance
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
    (hstartTr : TrKExprS world.venv uvars world.nameOf trProj Delta start
      startV) :
    (do
        let result ← applyIotaArgs start first transient
        let result ← applyIotaArgs result second transient
        applyIotaArgs result third transient).run methods s = .ok final sf ∧
      WhnfStateInv layer semantics trProj world support uvars Delta sf ∧
      InternUpdateFrame s sf ∧
      support final ∧
      WhnfMeaning trProj world uvars Delta
        (((first.toList ++ second.toList) ++ third.toList).foldl
          KExpr.mkApp start) final := by
  have htrace := hfirst.three hsecond hthird
  have hsemantic := htrace.acceptance theory hDelta hI hstartSupport hstartTr
  exact ⟨evalThreeArrays hfirst hsecond hthird, hsemantic.2⟩

end ApplyIotaArgsTrace

end RecM

end Ix.Tc
