import Ix.Tc.Verify.Check.FullInference

/-!
# Full inference for untyped leaf ingress

The leaf constructors of `PreTrKExprS` already contain every premise of the
corresponding `TrKExprS` constructor.  They therefore reuse the completed K2
operational proofs directly and strengthen only the postcondition.  The
application and binder constructors remain genuinely new K3 work because
their typed constructors contain the checks full inference must establish.
-/

namespace Ix.Tc

namespace RecM

theorem inferUncached_sort_full_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {inferRec : KExpr .anon → RecM .anon (KExpr .anon)}
    {inferOnly : Bool} {u : KUniv .anon} {info : ExprInfo .anon}
    {sourceV : Lean4Lean.VExpr}
    (theory : WhnfTheory trProj world uvars)
    (hcollision : support.CollisionFree)
    (hresultSupport : support (KExpr.mkSort (KUniv.mkSucc u)))
    (hsource : PreTrKExprS world.venv uvars world.nameOf trProj Delta
      (.sort u info) sourceV) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (inferUncached inferRec inferOnly (.sort u info))
      (fun result _ => FullInferPost trProj world support uvars Delta
        (.sort u info) sourceV result) := by
  cases hsource with
  | sort hu =>
      let htyped : TrKExprS world.venv uvars world.nameOf trProj Delta
          (.sort u info) (.sort u.toVLevel) := .sort hu
      exact RecM.WF.mono
        (inferUncached_sort_wf theory hcollision hresultSupport htyped)
        (fun _ _ hpost => FullInferPost.of_typed htyped hpost)
        (fun _ _ _ => trivial)

theorem inferUncached_var_full_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon}
    {inferRec : KExpr .anon → RecM .anon (KExpr .anon)}
    {inferOnly : Bool} {idx : UInt64} {name : Mode.anon.F Name}
    {info : ExprInfo .anon} {sourceV : Lean4Lean.VExpr}
    (theory : WhnfTheory trProj world uvars)
    (hsource : PreTrKExprS world.venv uvars world.nameOf trProj Delta
      (.var idx name info) sourceV)
    (hmem : WalkerRequest.lift
      s.ctx[s.ctx.size - 1 - idx.toNat]! (idx + 1) 0 ∈ requests)
    (hbig : Delta.bvars +
      s.ctx[s.ctx.size - 1 - idx.toNat]!.size < UInt64.size) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (inferUncached inferRec inferOnly (.var idx name info))
      (fun result _ => FullInferPost trProj world support uvars Delta
        (.var idx name info) sourceV result) := by
  cases hsource with
  | var hfind =>
      let htyped : TrKExprS world.venv uvars world.nameOf trProj Delta
          (.var idx name info) sourceV := .var hfind
      exact RecM.WF.mono
        (inferUncached_var_wf hrun theory htyped hmem hbig)
        (fun _ _ hpost => FullInferPost.of_typed htyped hpost)
        (fun _ _ _ => trivial)

theorem inferUncached_fvar_full_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {inferRec : KExpr .anon → RecM .anon (KExpr .anon)}
    {inferOnly : Bool} {fv : FVarId} {name : Mode.anon.F Name}
    {info : ExprInfo .anon} {sourceV : Lean4Lean.VExpr}
    (theory : WhnfTheory trProj world uvars)
    (hsafe : FVarInferSafety layer semantics trProj world support uvars
      Delta)
    (hsource : PreTrKExprS world.venv uvars world.nameOf trProj Delta
      (.fvar fv name info) sourceV) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (inferUncached inferRec inferOnly (.fvar fv name info))
      (fun result _ => FullInferPost trProj world support uvars Delta
        (.fvar fv name info) sourceV result) := by
  cases hsource with
  | fvar hfind =>
      let htyped : TrKExprS world.venv uvars world.nameOf trProj Delta
          (.fvar fv name info) sourceV := .fvar hfind
      exact RecM.WF.mono (inferUncached_fvar_wf theory hsafe htyped)
        (fun _ _ hpost => FullInferPost.of_typed htyped hpost)
        (fun _ _ _ => trivial)

theorem inferUncached_const_full_wf
    {alpha : Type} {initial : TcState .anon} {program : TcM .anon alpha}
    {requests : List WalkerRequest} {support : RunSupport}
    (hrun : RunAssumptions initial program requests support)
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon}
    {inferRec : KExpr .anon → RecM .anon (KExpr .anon)}
    {inferOnly : Bool} {id : KId .anon}
    {levels : Array (KUniv .anon)} {info : ExprInfo .anon}
    {sourceV : Lean4Lean.VExpr}
    (theory : WhnfTheory trProj world uvars)
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta))
    (hreferences : RecM.TrustedReferences world support)
    (htypes : TrustedConstTypes trProj world)
    (hcensus : ConstInferCensus world support requests)
    (hsourceSupport : support (.const id levels info))
    (hsource : PreTrKExprS world.venv uvars world.nameOf trProj Delta
      (.const id levels info) sourceV) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (inferUncached inferRec inferOnly (.const id levels info))
      (fun result _ => FullInferPost trProj world support uvars Delta
        (.const id levels info) sourceV result) := by
  cases hsource with
  | const hname hlookup hlevels harity =>
      rename_i name ci
      let htyped : TrKExprS world.venv uvars world.nameOf trProj Delta
          (.const id levels info)
          (.const name (levels.toList.map KUniv.toVLevel)) :=
        .const hname hlookup hlevels harity
      exact RecM.WF.mono
        (inferUncached_const_wf hrun theory hfault hreferences htypes
          hcensus hsourceSupport htyped)
        (fun _ _ hpost => FullInferPost.of_typed htyped hpost)
        (fun _ _ _ => trivial)

theorem inferUncached_nat_full_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon}
    {inferRec : KExpr .anon → RecM .anon (KExpr .anon)}
    {inferOnly : Bool} {n : Nat} {blob : Address}
    {info : ExprInfo .anon} {sourceV : Lean4Lean.VExpr}
    (context : LiteralInferContext world support)
    (theory : WhnfTheory trProj world uvars)
    (hsource : PreTrKExprS world.venv uvars world.nameOf trProj Delta
      (.nat n blob info) sourceV) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (inferUncached inferRec inferOnly (.nat n blob info))
      (fun result _ => FullInferPost trProj world support uvars Delta
        (.nat n blob info) sourceV result) := by
  cases hsource with
  | nat hcontains =>
      let htyped : TrKExprS world.venv uvars world.nameOf trProj Delta
          (.nat n blob info) (.natLit n) := .nat hcontains
      exact RecM.WF.mono (inferUncached_nat_wf context theory htyped)
        (fun _ _ hpost => FullInferPost.of_typed htyped hpost)
        (fun _ _ _ => trivial)

theorem inferUncached_str_full_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {s : TcState .anon}
    {inferRec : KExpr .anon → RecM .anon (KExpr .anon)}
    {inferOnly : Bool} {value : String} {blob : Address}
    {info : ExprInfo .anon} {sourceV : Lean4Lean.VExpr}
    (context : LiteralInferContext world support)
    (theory : WhnfTheory trProj world uvars)
    (hsource : PreTrKExprS world.venv uvars world.nameOf trProj Delta
      (.str value blob info) sourceV) :
    RecM.WF .noAccel semantics trProj world support uvars Delta s
      (inferUncached inferRec inferOnly (.str value blob info))
      (fun result _ => FullInferPost trProj world support uvars Delta
        (.str value blob info) sourceV result) := by
  cases hsource with
  | str hcontains =>
      let htyped : TrKExprS world.venv uvars world.nameOf trProj Delta
          (.str value blob info) (.trLiteral (.strVal value)) :=
        .str hcontains
      exact RecM.WF.mono (inferUncached_str_wf context theory htyped)
        (fun _ _ hpost => FullInferPost.of_typed htyped hpost)
        (fun _ _ _ => trivial)

end RecM

end Ix.Tc
