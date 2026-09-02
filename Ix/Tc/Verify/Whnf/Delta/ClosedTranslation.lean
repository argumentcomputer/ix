import Ix.Tc.Verify.Whnf.Delta.CacheSemantics

/-!
# Closed-expression translation under caller contexts

Definition bodies are admitted in the empty mixed context, while delta
unfolding runs in the caller's current context.  Appending an outer mixed
context does not change any variable already resolved in the inner prefix.
This module proves that fact for `KVLCtx`, then transports both structural and
defeq-quotiented expression translations across the append.

The theorem is intentionally stronger than the empty-prefix specialization
needed by delta: it preserves any well-formed inner prefix.  That makes binder
cases compositional and exposes exactly where projection weakening and
closedness are used.
-/

namespace Ix.Tc

open Lean4Lean (VExpr VEnv)

namespace KVLCtx

/-- Append declarations outside every entry of an existing mixed context. -/
def appendOuter : KVLCtx → KVLCtx → KVLCtx
  | [], outer => outer
  | entry :: inner, outer => entry :: appendOuter inner outer

/-- Erasing `vlet` entries and retaining `vlam` types commutes with appending
an outer mixed context. -/
@[simp] theorem toCtx_appendOuter : ∀ (inner outer : KVLCtx),
    (appendOuter inner outer).toCtx = inner.toCtx ++ outer.toCtx
  | [], _ => rfl
  | (ofv, .vlam type) :: inner, outer => by
      simp only [appendOuter, toCtx, List.cons_append, toCtx_appendOuter]
  | (ofv, .vlet type value) :: inner, outer => by
      simp only [appendOuter, toCtx, toCtx_appendOuter]

/-- A successful lookup in an inner prefix is unchanged when an outer mixed
context is appended. -/
theorem find?_append_of_some : ∀ {inner : KVLCtx}
    {v : Nat ⊕ FVarId} {e A : VExpr} (outer : KVLCtx),
    inner.find? v = some (e, A) →
      (appendOuter inner outer).find? v = some (e, A)
  | [], _, _, _, _, h => by
      simp only [find?] at h
      cases h
  | (ofv, d) :: inner, v, e, A, outer, h => by
      simp only [appendOuter, find?] at h ⊢
      cases hnext : next ofv v with
      | none =>
          simpa only [hnext] using h
      | some v' =>
          simp only [hnext, Option.bind_eq_bind] at h ⊢
          cases hfind : find? inner v' with
          | none =>
              simp only [hfind, Option.bind_none] at h
              cases h
          | some value =>
              rcases value with ⟨value, type⟩
              have hfind' :=
                find?_append_of_some (inner := inner) outer hfind
              simpa only [hfind, hfind', Option.bind_some] using h

end KVLCtx

namespace TrKExprS

/-- Structural translation is unchanged by appending an arbitrary outer mixed
context to a well-formed inner prefix.  Concrete de Bruijn indices do not
shift: the new context is outside every variable already resolved by the
prefix. -/
theorem weakRight {env : VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name}
    {trProj : Nat → List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    (henv : env.Ordered)
    (hlit : ∀ l, env.ContainsLits l →
      VExpr.WF env uvars [] (VExpr.trLiteral l))
    (htp : TrProjOK env uvars trProj)
    {m : Mode} {inner : KVLCtx} {e : KExpr m} {e' : VExpr}
    (H : TrKExprS env uvars nameOf trProj inner e e')
    (hinner : KVLCtx.WF env uvars inner)
    (outer : KVLCtx) :
    TrKExprS env uvars nameOf trProj (KVLCtx.appendOuter inner outer) e e' := by
  induction H generalizing outer with
  | var h =>
      exact .var (KVLCtx.find?_append_of_some outer h)
  | fvar h =>
      exact .fvar (KVLCtx.find?_append_of_some outer h)
  | sort h =>
      exact .sort h
  | const hname hlookup hlevels harity =>
      exact .const hname hlookup hlevels harity
  | @app inner f arg info f' arg' A B
      hfunTy hargTy hfun harg ihfun iharg =>
      have hclosed : Lean4Lean.CtxClosed inner.toCtx :=
        Lean4Lean.VEnv.CtxWF.closed henv hinner.toCtx
      refine .app (A := A) (B := B) ?_ ?_
        (ihfun hinner outer) (iharg hinner outer)
      · simpa only [KVLCtx.toCtx_appendOuter, Lean4Lean.VEnv.HasType] using
          hfunTy.weakR henv hclosed outer.toCtx
      · simpa only [KVLCtx.toCtx_appendOuter, Lean4Lean.VEnv.HasType] using
          hargTy.weakR henv hclosed outer.toCtx
  | @lam inner name bi ty body info ty' body'
      hty htyTr hbodyTr ihty ihbody =>
      have hclosed : Lean4Lean.CtxClosed inner.toCtx :=
        Lean4Lean.VEnv.CtxWF.closed henv hinner.toCtx
      have htyOriginal := hty
      obtain ⟨level, htyHasType⟩ := hty
      have hty' :
          env.IsType uvars (KVLCtx.appendOuter inner outer).toCtx ty' := by
        refine ⟨level, ?_⟩
        simpa only [KVLCtx.toCtx_appendOuter, Lean4Lean.VEnv.HasType] using
          htyHasType.weakR henv hclosed outer.toCtx
      have hbodyInner :
          KVLCtx.WF env uvars ((none, .vlam ty') :: inner) :=
        ⟨hinner, nofun, htyOriginal⟩
      exact .lam hty' (ihty hinner outer) (ihbody hbodyInner outer)
  | @all inner name bi ty body info ty' body'
      hty hbodyTy htyTr hbodyTr ihty ihbody =>
      have hclosed : Lean4Lean.CtxClosed inner.toCtx :=
        Lean4Lean.VEnv.CtxWF.closed henv hinner.toCtx
      have htyOriginal := hty
      obtain ⟨level, htyHasType⟩ := hty
      have hty' :
          env.IsType uvars (KVLCtx.appendOuter inner outer).toCtx ty' := by
        refine ⟨level, ?_⟩
        simpa only [KVLCtx.toCtx_appendOuter, Lean4Lean.VEnv.HasType] using
          htyHasType.weakR henv hclosed outer.toCtx
      have hbodyInner :
          KVLCtx.WF env uvars ((none, .vlam ty') :: inner) :=
        ⟨hinner, nofun, htyOriginal⟩
      have hbodyClosed :
          Lean4Lean.CtxClosed
            (KVLCtx.toCtx ((none, Lean4Lean.VLocalDecl.vlam ty') :: inner)) :=
        Lean4Lean.VEnv.CtxWF.closed henv hbodyInner.toCtx
      obtain ⟨bodyLevel, hbodyHasType⟩ := hbodyTy
      have hbodyTy' :
          env.IsType uvars
            (KVLCtx.appendOuter
              ((none, Lean4Lean.VLocalDecl.vlam ty') :: inner) outer).toCtx
              body' := by
        refine ⟨bodyLevel, ?_⟩
        simpa only [KVLCtx.toCtx_appendOuter, Lean4Lean.VEnv.HasType] using
          hbodyHasType.weakR henv hbodyClosed outer.toCtx
      exact .all hty' hbodyTy' (ihty hinner outer)
        (ihbody hbodyInner outer)
  | @letE inner name ty val body nondep info ty' val' body'
      hvalTy htyTr hvalTr hbodyTr ihty ihval ihbody =>
      have hclosed : Lean4Lean.CtxClosed inner.toCtx :=
        Lean4Lean.VEnv.CtxWF.closed henv hinner.toCtx
      have hvalTy' :
          env.HasType uvars (KVLCtx.appendOuter inner outer).toCtx val' ty' := by
        simpa only [KVLCtx.toCtx_appendOuter, Lean4Lean.VEnv.HasType] using
          hvalTy.weakR henv hclosed outer.toCtx
      have hbodyInner :
          KVLCtx.WF env uvars ((none, .vlet ty' val') :: inner) :=
        ⟨hinner, nofun, hvalTy⟩
      exact .letE hvalTy' (ihty hinner outer) (ihval hinner outer)
        (ihbody hbodyInner outer)
  | @prj inner sid field val info structName val' result'
      hname hvalTr hproj ihval =>
      have hclosed : Lean4Lean.CtxClosed inner.toCtx :=
        Lean4Lean.VEnv.CtxWF.closed henv hinner.toCtx
      have hvalWF : VExpr.WF env uvars inner.toCtx val' :=
        hvalTr.wf henv hlit htp.wf hinner
      have hresultWF : VExpr.WF env uvars inner.toCtx result' :=
        htp.wf hproj hvalWF
      have hvalClosed : val'.ClosedN inner.toCtx.length :=
        hvalWF.closedN henv hclosed
      have hresultClosed : result'.ClosedN inner.toCtx.length :=
        hresultWF.closedN henv hclosed
      have hlift :
          Lean4Lean.Ctx.LiftN outer.toCtx.length inner.toCtx.length
            inner.toCtx (inner.toCtx ++ outer.toCtx) :=
        Lean4Lean.Ctx.LiftN.right hclosed outer.toCtx
      have hproj' := htp.weakN hlift hproj
      have hproj'' :
          trProj uvars (KVLCtx.appendOuter inner outer).toCtx structName
            field.toNat val' result' := by
        simpa only [KVLCtx.toCtx_appendOuter,
          hvalClosed.liftN_eq (Nat.le_refl _),
          hresultClosed.liftN_eq (Nat.le_refl _)] using hproj'
      exact .prj hname (ihval hinner outer) hproj''
  | nat h =>
      exact .nat h
  | str h =>
      exact .str h

end TrKExprS

namespace TrKExpr

/-- Defeq-quotiented translation is likewise stable under an arbitrary outer
mixed context. -/
theorem weakRight {env : VEnv} {uvars : Nat}
    {nameOf : Address → Option Lean.Name}
    {trProj : Nat → List VExpr → Lean.Name → Nat → VExpr → VExpr → Prop}
    (henv : env.Ordered)
    (hlit : ∀ l, env.ContainsLits l →
      VExpr.WF env uvars [] (VExpr.trLiteral l))
    (htp : TrProjOK env uvars trProj)
    {m : Mode} {inner : KVLCtx} {e : KExpr m} {e' : VExpr}
    (H : TrKExpr env uvars nameOf trProj inner e e')
    (hinner : KVLCtx.WF env uvars inner)
    (outer : KVLCtx) :
    TrKExpr env uvars nameOf trProj (KVLCtx.appendOuter inner outer) e e' := by
  obtain ⟨structural, hstructural, targetTy, htarget⟩ := H
  have hclosed : Lean4Lean.CtxClosed inner.toCtx :=
    Lean4Lean.VEnv.CtxWF.closed henv hinner.toCtx
  refine ⟨structural, hstructural.weakRight henv hlit htp hinner outer,
    targetTy, ?_⟩
  simpa only [KVLCtx.toCtx_appendOuter, Lean4Lean.VEnv.HasType] using
    htarget.weakR henv hclosed outer.toCtx

end TrKExpr

end Ix.Tc
