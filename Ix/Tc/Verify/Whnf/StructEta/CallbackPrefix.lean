import Ix.Tc.Verify.Whnf.StructEta.Rebuild

/-!
# Struct-eta callback-prefix preservation

The struct-eta control-flow trace crosses two inference back-edges under
`TcM.withInferOnly` and one WHNF back-edge, with all three errors caught as
optional misses.  This slice first proves the reusable state-preservation
adapters for those exact production wrappers.  The adapters preserve the
full fixed-world invariant on success and error; they do not claim that a
caught callback is state-pure.
-/

namespace Ix.Tc

namespace TcM

/-- Exact execution equation for the infer-only scope.  The callback sees
`inferOnly = true`; the caller's previous flag is restored on both outcomes,
while every other callback mutation remains visible. -/
theorem withInferOnly_eq (f : TcM .anon α) (s : TcState .anon) :
    TcM.withInferOnly f s =
      match f {s with inferOnly := true} with
      | .ok a after => .ok a {after with inferOnly := s.inferOnly}
      | .error err after =>
          .error err {after with inferOnly := s.inferOnly} := by
  unfold TcM.withInferOnly
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s = .ok s s from rfl]
  simp only
  change EStateM.bind
    (modify (fun st : TcState .anon => {st with inferOnly := true}) :
      TcM .anon PUnit) _ s = _
  unfold EStateM.bind
  rw [show
    (modify (fun st : TcState .anon => {st with inferOnly := true}) :
      TcM .anon PUnit) s = .ok ⟨⟩ {s with inferOnly := true} from rfl]
  simp only
  unfold tryFinally
  change EStateM.map (fun x : α × PUnit => x.1)
    (tryFinally' f (fun _ =>
      (modify (fun st : TcState .anon =>
        {st with inferOnly := s.inferOnly}) : TcM .anon PUnit)))
      {s with inferOnly := true} = _
  unfold EStateM.map tryFinally' EStateM.instMonadFinally
  simp only
  cases hrun : f {s with inferOnly := true} with
  | ok a after =>
      simp only
      rw [show
        (modify (fun st : TcState .anon =>
          {st with inferOnly := s.inferOnly}) : TcM .anon PUnit) after =
            .ok ⟨⟩ {after with inferOnly := s.inferOnly} from rfl]
  | error err after =>
      simp only
      rw [show
        (modify (fun st : TcState .anon =>
          {st with inferOnly := s.inferOnly}) : TcM .anon PUnit) after =
            .ok ⟨⟩ {after with inferOnly := s.inferOnly} from rfl]

/-- Running a verified callback under production's infer-only scope
preserves the complete WHNF invariant.  Success and error payloads are kept
state-independent because the wrapper restores one operational flag after
the callback has established its postcondition. -/
theorem withInferOnly_whnf_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {f : TcM .anon α} {Q : α → Prop} {E : TcError .anon → Prop}
    (hf : TcM.WF
      (WhnfStateInv layer semantics trProj world support uvars Delta)
      {s with inferOnly := true} f (fun a _ => Q a) (fun err _ => E err)) :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      (TcM.withInferOnly f) (fun a _ => Q a) (fun err _ => E err) := by
  intro hI
  have hEnabled :
      WhnfStateInv layer semantics trProj world support uvars Delta
        {s with inferOnly := true} :=
    hI.of_semantic_fields_eq rfl rfl rfl rfl rfl rfl rfl rfl
  have hcallback := hf hEnabled
  rw [withInferOnly_eq]
  cases hrun : f {s with inferOnly := true} with
  | ok a after =>
      rw [hrun] at hcallback
      exact ⟨hcallback.1.of_semantic_fields_eq rfl rfl rfl rfl rfl rfl rfl rfl,
        hcallback.2⟩
  | error err after =>
      rw [hrun] at hcallback
      exact ⟨hcallback.1.of_semantic_fields_eq rfl rfl rfl rfl rfl rfl rfl rfl,
        hcallback.2⟩

end TcM

namespace RecM

/-- Reader specialization of `inferOnlyRec`: no hidden state exists between
the method-table read and `TcM.withInferOnly`. -/
@[simp] theorem inferOnlyRec_run (e : KExpr .anon)
    (methods : Methods .anon) (s : TcState .anon) :
    (inferOnlyRec e).run methods s =
      TcM.withInferOnly (methods.infer e) s := by
  rfl

/-- Exact non-backtracking behavior of the optional callback wrapper. -/
@[simp] theorem tryOptional_run (x : RecM .anon α)
    (methods : Methods .anon) (s : TcState .anon) :
    (tryOptional x).run methods s =
      match x.run methods s with
      | .ok a after => .ok (some a) after
      | .error _ after => .ok none after := by
  cases hrun : x.run methods s with
  | ok a after =>
      rw [tryOptional_success hrun]
  | error err after =>
      rw [tryOptional_error hrun]

/-- Catching a verified callback preserves its error-side invariant and turns
only the payload into `none`.  A successful payload retains the callback's
postcondition. -/
theorem tryOptional_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {x : RecM .anon α} {Q : α → TcState .anon → Prop}
    (hx : RecM.WF layer semantics trProj world support uvars Delta s x Q) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (tryOptional x)
      (fun result after => match result with
        | some a => Q a after
        | none => True) := by
  intro methods hmethods hI
  have hrunWF := hx methods hmethods hI
  rw [tryOptional_run]
  cases hrun : x.run methods s with
  | ok a after =>
      rw [hrun] at hrunWF
      exact hrunWF
  | error err after =>
      rw [hrun] at hrunWF
      exact ⟨hrunWF.1, trivial⟩

/-- The actual inference back-edge, including infer-only flag restoration,
satisfies the predecessor method table's inference contract. -/
theorem inferOnlyRec_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {methods : Methods .anon}
    (hmethods :
      Methods.WFAt layer semantics trProj world support uvars methods)
    {s : TcState .anon} {e : KExpr .anon} {sourceV : Lean4Lean.VExpr}
    (hsource : support e)
    (htr : TrKExprS world.venv uvars world.nameOf trProj Delta e sourceV) :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((inferOnlyRec e).run methods)
      (fun ty _ => support ty ∧
        InferPost trProj world uvars Delta sourceV ty) := by
  change TcM.WF
    (WhnfStateInv layer semantics trProj world support uvars Delta) s
    (TcM.withInferOnly (methods.infer e)) _
  apply TcM.withInferOnly_whnf_wf
  exact hmethods.infer hsource htr

/-- Successful caught inference retains both finite support and its Theory
typing postcondition; a caught error retains the invariant and returns
`none`. -/
theorem tryOptionalInferOnlyRec_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx}
    {s : TcState .anon} {e : KExpr .anon} {sourceV : Lean4Lean.VExpr}
    (hsource : support e)
    (htr : TrKExprS world.venv uvars world.nameOf trProj Delta e sourceV) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (tryOptional (inferOnlyRec e))
      (fun result _ => match result with
        | some ty => support ty ∧
            InferPost trProj world uvars Delta sourceV ty
        | none => True) := by
  apply RecM.WF.mono
    (tryOptional_wf
      (layer := layer) (semantics := semantics) (s := s)
      (x := inferOnlyRec e)
      (Q := fun ty _ => support ty ∧
        InferPost trProj world uvars Delta sourceV ty) (by
        intro methods hmethods
        exact inferOnlyRec_wf (s := s) hmethods hsource htr))
  · intro result after hresult
    cases result <;> exact hresult
  · intro err after herror
    exact herror

/-- Successful caught WHNF retains finite support and the exact predecessor
method-table WHNF postcondition. -/
theorem tryOptionalWhnfRec_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx}
    {s : TcState .anon} {e : KExpr .anon} {sourceV : Lean4Lean.VExpr}
    (hsource : support e)
    (htr : TrKExprS world.venv uvars world.nameOf trProj Delta e sourceV) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (tryOptional (whnfRec e))
      (fun result _ => match result with
        | some reduced => support reduced ∧
            WhnfPost trProj world uvars Delta sourceV reduced
        | none => True) := by
  apply RecM.WF.mono
    (tryOptional_wf
      (layer := layer) (semantics := semantics) (s := s)
      (x := whnfRec e)
      (Q := fun reduced _ => support reduced ∧
        WhnfPost trProj world uvars Delta sourceV reduced) (by
        intro methods hmethods
        exact
          (hmethods.whnf (s := s) hsource htr)))
  · intro result after hresult
    cases result <;> exact hresult
  · intro err after herror
    exact herror

end RecM
end Ix.Tc
