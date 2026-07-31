import Ix.Tc.Verify.Infer.Callbacks

/-!
# Sort exposure for inference

Lambda, forall, and let inference validate types by exposing the universe of
an inferred type.  This module proves the syntactic sort fast path and the
direct-WHNF fallback against one shared semantic view.
-/

namespace Ix.Tc

/-- Finite descent resources for a supported concrete sort.  Smart universe
constructors compare addresses throughout their argument subtrees and use
`UInt64` offsets, so support of the enclosing expression alone is not enough
to justify them. -/
def SortComponentResources (support : RunSupport) : Prop :=
  ∀ {u : KUniv .anon} {info : ExprInfo .anon},
    support (.sort u info) →
      u.size < UInt64.size ∧
        ∀ x, KUniv.Sub x u → support.univ x

/-- Semantic and finite-resource result of exposing a sort.  The view
connects the caller's quotient translation to the selected Theory sort and
retains exactly the subtree support needed by later smart constructors. -/
structure SortView (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (Delta : KVLCtx) (inputV : Lean4Lean.VExpr)
    (result : KUniv .anon) : Prop where
  sizeBound : result.size < UInt64.size
  subtermSupport : ∀ x, KUniv.Sub x result → support.univ x
  levelWF : result.toVLevel.WF uvars
  inputEq : world.venv.IsDefEqU uvars Delta.toCtx inputV
    (.sort result.toVLevel)

theorem SortView.rootSupport
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {inputV : Lean4Lean.VExpr} {result : KUniv .anon}
    (h : SortView world support uvars Delta inputV result) :
    support.univ result :=
  h.subtermSupport result .refl

namespace SortView

/-- The simplifying concrete `mkIMax` denotes Theory `imax`.  Every address
comparison made by the smart constructor is covered by the two finite
subterm footprints retained in the sort views. -/
theorem mkIMax_equiv
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {DeltaA DeltaB : KVLCtx} {inputA inputB : Lean4Lean.VExpr}
    {a b : KUniv .anon}
    (hcf : support.CollisionFree)
    (ha : SortView world support uvars DeltaA inputA a)
    (hb : SortView world support uvars DeltaB inputB b) :
    (KUniv.mkIMax a b).toVLevel ≈
      .imax a.toVLevel b.toVLevel := by
  apply KUniv.toVLevel_mkIMax
  · intro x y hx hy
    apply hcf.univ.addrFaithful
    · rcases hx with hx | hx
      · exact ha.subtermSupport x hx
      · exact hb.subtermSupport x hx
    · rcases hy with hy | hy
      · exact ha.subtermSupport y hy
      · exact hb.subtermSupport y hy
  · exact ha.sizeBound
  · exact hb.sizeBound

end SortView

namespace RecM

private theorem ensureSortWhnf_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon} {input : KExpr .anon}
    {inputCoreV inputV : Lean4Lean.VExpr}
    (hwhnf : DirectWhnf.WFAt semantics trProj world support uvars)
    (hresources : SortComponentResources support)
    (hinputSupport : support input)
    (hinputCore : TrKExprS world.venv uvars world.nameOf trProj Delta input
      inputCoreV)
    (hinputEq : world.venv.IsDefEqU uvars Delta.toCtx inputCoreV inputV) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (ensureSortWhnf input)
      (fun result _ => SortView world support uvars Delta inputV result) := by
  unfold ensureSortWhnf
  apply RecM.WF.bind (hwhnf hinputSupport hinputCore)
  intro reduced after hred
  rcases hred with
    ⟨hreducedSupport, reducedV, hreducedTr, hcoreReduced⟩
  cases reduced <;> simp only
  case sort result info =>
    cases hreducedTr with
    | sort hlevel =>
        obtain ⟨hsize, hsubterms⟩ := hresources hreducedSupport
        exact RecM.WF.pure fun hI =>
          { sizeBound := hsize
            subtermSupport := hsubterms
            levelWF := hlevel
            inputEq := hinputEq.symm.trans world.venvWF hI.2.1.wf.toCtx
              hcoreReduced }
  all_goals
    exact RecM.WF.throw fun _ => trivial

/-- Both production paths through `ensureSortDirect` return a well-formed
universe whose Theory sort is definitionally equal to the caller's input
translation. -/
theorem ensureSortDirect_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon} {input : KExpr .anon}
    {inputV : Lean4Lean.VExpr}
    (hwhnf : DirectWhnf.WFAt semantics trProj world support uvars)
    (hresources : SortComponentResources support)
    (hinputSupport : support input)
    (hinput : TrKExpr world.venv uvars world.nameOf trProj Delta input
      inputV) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (ensureSortDirect input)
      (fun result _ => SortView world support uvars Delta inputV result) := by
  obtain ⟨inputCoreV, hinputCore, hinputEq⟩ := hinput
  cases input <;> simp only [ensureSortDirect]
  case sort result info =>
    apply RecM.WF.pure
    intro _
    obtain ⟨hsize, hsubterms⟩ := hresources hinputSupport
    cases hinputCore with
    | sort hlevel =>
        exact {
          sizeBound := hsize
          subtermSupport := hsubterms
          levelWF := hlevel
          inputEq := hinputEq.symm }
  all_goals
    exact ensureSortWhnf_wf hwhnf hresources hinputSupport hinputCore hinputEq

end RecM

end Ix.Tc
