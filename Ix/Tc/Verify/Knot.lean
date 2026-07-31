import Ix.Tc.Verify.Whnf

/-!
# Verification of the recursive method knot

The production checker ties six mutually recursive entry points through a
finite method table.  This file isolates the non-circular proof shape:

* `Methods.next methods` is exactly one production method-table layer whose
  recursive calls use `methods`;
* `Methods.LayerWF methods` is the semantic obligation for that one layer;
* `Methods.Closed` says a well-formed smaller table proves the next layer;
* `methodsOut_wf` and `methodsN_wf` close every finite approximation; and
* `TcM.runRec_wf` transports a reader-level proof to the public knot runner.

The remaining K2 work is therefore deliberately visible in `Methods.Closed`:
K1 supplies the four WHNF fields and K2 supplies inference and definitional
equality.  No theorem below assumes the recursive table is already closed.
-/

namespace Ix.Tc

namespace Methods

/-- One unfolded production method-table layer.  Keeping this constructor
named prevents proofs from depending on the presentation of `methodsN`. -/
def next (methods : Methods m) : Methods m where
  whnf e := (RecM.whnf e).run methods
  whnfCore e := (RecM.whnfCore e).run methods
  whnfMode e mode := (RecM.whnfWithNatSuccMode e mode).run methods
  whnfCoreFlags e flags := (RecM.whnfCoreWithFlags e flags).run methods
  infer e := (RecM.infer e).run methods
  isDefEq a b := (RecM.isDefEq a b).run methods

/-- Semantic obligation for one unfolded method-table layer at the universe
count of the active checker run. -/
def LayerWFAt (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (methods : Methods .anon) : Prop :=
  Methods.WFAt layer semantics trProj world support uvars (next methods)

/-- K1's four fields for one unfolded method-table layer at a fixed universe
count.  This is the closure shape used by universe-indexed WHNF and unfold
cache semantics. -/
structure WhnfLayerWFAt (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (methods : Methods .anon) : Prop where
  whnf : ∀ {Delta s e sourceV},
    support e →
    TrKExprS world.venv uvars world.nameOf trProj Delta e sourceV →
    TcM.WF
      (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((RecM.whnf e).run methods)
      (fun result _ => support result ∧
        WhnfPost trProj world uvars Delta sourceV result)
  whnfCore : ∀ {Delta s e sourceV},
    support e →
    TrKExprS world.venv uvars world.nameOf trProj Delta e sourceV →
    TcM.WF
      (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((RecM.whnfCore e).run methods)
      (fun result _ => support result ∧
        WhnfPost trProj world uvars Delta sourceV result)
  whnfMode : ∀ {Delta s e sourceV} {mode : NatSuccMode},
    support e →
    TrKExprS world.venv uvars world.nameOf trProj Delta e sourceV →
    TcM.WF
      (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((RecM.whnfWithNatSuccMode e mode).run methods)
      (fun result _ => support result ∧
        WhnfPost trProj world uvars Delta sourceV result)
  whnfCoreFlags : ∀ {Delta s e sourceV} {flags : WhnfFlags},
    support e →
    TrKExprS world.venv uvars world.nameOf trProj Delta e sourceV →
    TcM.WF
      (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((RecM.whnfCoreWithFlags e flags).run methods)
      (fun result _ => support result ∧
        WhnfPost trProj world uvars Delta sourceV result)

/-- K2's two fields for one unfolded method-table layer at a fixed universe
count. -/
structure InferDefEqLayerWFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) (methods : Methods .anon) : Prop where
  infer : ∀ {Delta s e sourceV},
    support e →
    TrKExprS world.venv uvars world.nameOf trProj Delta e sourceV →
    TcM.WF
      (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((RecM.infer e).run methods)
      (fun ty _ => support ty ∧
        InferPost trProj world uvars Delta sourceV ty)
  isDefEq : ∀ {Delta s a b va vb},
    support a →
    support b →
    TrKExprS world.venv uvars world.nameOf trProj Delta a va →
    TrKExprS world.venv uvars world.nameOf trProj Delta b vb →
    TcM.WF
      (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((RecM.isDefEq a b).run methods)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx va vb)

/-- The fixed-universe K1 and K2 records assemble the exact next layer. -/
theorem LayerWFAt.of_parts
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {methods : Methods .anon}
    (hwhnf :
      WhnfLayerWFAt layer semantics trProj world support uvars methods)
    (hinfer :
      InferDefEqLayerWFAt layer semantics trProj world support uvars methods) :
    LayerWFAt layer semantics trProj world support uvars methods := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hwhnf.whnf
  · exact hwhnf.whnfCore
  · exact hwhnf.whnfMode
  · exact hwhnf.whnfCoreFlags
  · exact hinfer.infer
  · exact hinfer.isDefEq

/-- Exact fixed-universe induction step for the six-method knot. -/
def ClosedAt (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) : Prop :=
  ∀ methods,
    Methods.WFAt layer semantics trProj world support uvars methods →
    LayerWFAt layer semantics trProj world support uvars methods

/-- K1's fixed-universe closure obligation, independent of construction of
the two K2 fields. -/
def WhnfClosedAt (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) : Prop :=
  ∀ methods,
    Methods.WFAt layer semantics trProj world support uvars methods →
    WhnfLayerWFAt layer semantics trProj world support uvars methods

/-- K2's fixed-universe closure obligation. -/
def InferDefEqClosedAt (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) : Prop :=
  ∀ methods,
    Methods.WFAt layer semantics trProj world support uvars methods →
    InferDefEqLayerWFAt layer semantics trProj world support uvars methods

theorem ClosedAt.of_parts
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (hwhnf :
      WhnfClosedAt layer semantics trProj world support uvars)
    (hinfer :
      InferDefEqClosedAt layer semantics trProj world support uvars) :
    ClosedAt layer semantics trProj world support uvars := by
  intro methods hmethods
  exact LayerWFAt.of_parts (hwhnf methods hmethods)
    (hinfer methods hmethods)

/-- Semantic obligation for one unfolded layer over a fixed smaller table. -/
def LayerWF (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (methods : Methods .anon) : Prop :=
  Methods.WF layer semantics trProj world support (next methods)

/-- K1's four fields for one unfolded method-table layer. -/
structure WhnfLayerWF (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (methods : Methods .anon) : Prop where
  whnf : ∀ {uvars Delta s e sourceV},
    support e →
    TrKExprS world.venv uvars world.nameOf trProj Delta e sourceV →
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((RecM.whnf e).run methods)
      (fun result _ => support result ∧
        WhnfPost trProj world uvars Delta sourceV result)
  whnfCore : ∀ {uvars Delta s e sourceV},
    support e →
    TrKExprS world.venv uvars world.nameOf trProj Delta e sourceV →
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((RecM.whnfCore e).run methods)
      (fun result _ => support result ∧
        WhnfPost trProj world uvars Delta sourceV result)
  whnfMode : ∀ {uvars Delta s e sourceV} {mode : NatSuccMode},
    support e →
    TrKExprS world.venv uvars world.nameOf trProj Delta e sourceV →
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((RecM.whnfWithNatSuccMode e mode).run methods)
      (fun result _ => support result ∧
        WhnfPost trProj world uvars Delta sourceV result)
  whnfCoreFlags : ∀ {uvars Delta s e sourceV} {flags : WhnfFlags},
    support e →
    TrKExprS world.venv uvars world.nameOf trProj Delta e sourceV →
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((RecM.whnfCoreWithFlags e flags).run methods)
      (fun result _ => support result ∧
        WhnfPost trProj world uvars Delta sourceV result)

/-- K2's two fields for one unfolded method-table layer. -/
structure InferDefEqLayerWF (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport)
    (methods : Methods .anon) : Prop where
  infer : ∀ {uvars Delta s e sourceV},
    support e →
    TrKExprS world.venv uvars world.nameOf trProj Delta e sourceV →
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((RecM.infer e).run methods)
      (fun ty _ => support ty ∧
        InferPost trProj world uvars Delta sourceV ty)
  isDefEq : ∀ {uvars Delta s a b va vb},
    support a →
    support b →
    TrKExprS world.venv uvars world.nameOf trProj Delta a va →
    TrKExprS world.venv uvars world.nameOf trProj Delta b vb →
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Delta) s
      ((RecM.isDefEq a b).run methods)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx va vb)

/-- The independently proved K1 and K2 fields assemble the exact next-layer
record; no field may use the table it is currently proving. -/
theorem LayerWF.of_parts {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {methods : Methods .anon}
    (hwhnf : WhnfLayerWF layer semantics trProj world support methods)
    (hinfer : InferDefEqLayerWF layer semantics trProj world support methods) :
    LayerWF layer semantics trProj world support methods := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hwhnf.whnf
  · exact hwhnf.whnfCore
  · exact hwhnf.whnfMode
  · exact hwhnf.whnfCoreFlags
  · exact hinfer.infer
  · exact hinfer.isDefEq

/-- The exact induction step required to tie the recursive knot. -/
def Closed (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport) : Prop :=
  ∀ methods, Methods.WF layer semantics trProj world support methods →
    LayerWF layer semantics trProj world support methods

/-- K1 closure obligation, separate from inference and def-eq. -/
def WhnfClosed (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport) : Prop :=
  ∀ methods, Methods.WF layer semantics trProj world support methods →
    WhnfLayerWF layer semantics trProj world support methods

/-- K2 closure obligation, assuming only the smaller table's six contracts. -/
def InferDefEqClosed (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport) : Prop :=
  ∀ methods, Methods.WF layer semantics trProj world support methods →
    InferDefEqLayerWF layer semantics trProj world support methods

theorem Closed.of_parts {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    (hwhnf : WhnfClosed layer semantics trProj world support)
    (hinfer : InferDefEqClosed layer semantics trProj world support) :
    Closed layer semantics trProj world support := by
  intro methods hmethods
  exact LayerWF.of_parts (hwhnf methods hmethods) (hinfer methods hmethods)

/-- The exhausted table changes no state, so it satisfies every method
contract through the permitted error branch. -/
theorem methodsOut_wf (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport) :
    Methods.WF layer semantics trProj world support
      (methodsOut : Methods .anon) := by
  constructor <;> intros <;>
    exact TcM.WF.throw (fun _ => trivial)

/-- Each successor approximation is definitionally one `Methods.next` layer. -/
@[simp] theorem methodsN_succ (n : Nat) :
    (methodsN (m := .anon) (n + 1)) = next (methodsN n) := rfl

/-- Closure of one layer proves every finite production approximation. -/
theorem methodsN_wf {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    (hclosed : Closed layer semantics trProj world support) (n : Nat) :
    Methods.WF layer semantics trProj world support
      (methodsN (m := .anon) n) := by
  induction n with
  | zero => exact methodsOut_wf layer semantics trProj world support
  | succ n ih =>
      simpa [LayerWF, Nat.succ_eq_add_one] using hclosed (methodsN n) ih

/-- The exhausted table satisfies the fixed-universe method contract. -/
theorem methodsOut_wfAt
    (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) :
    Methods.WFAt layer semantics trProj world support uvars
      (methodsOut : Methods .anon) :=
  Methods.WF.atUvars
    (methodsOut_wf layer semantics trProj world support) uvars

/-- Fixed-universe closure proves every finite production approximation. -/
theorem methodsN_wfAt
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (hclosed : ClosedAt layer semantics trProj world support uvars)
    (n : Nat) :
    Methods.WFAt layer semantics trProj world support uvars
      (methodsN (m := .anon) n) := by
  induction n with
  | zero =>
      exact methodsOut_wfAt layer semantics trProj world support uvars
  | succ n ih =>
      simpa [LayerWFAt, Nat.succ_eq_add_one] using
        hclosed (methodsN n) ih

end Methods

namespace TcM

/-- A reader-level proof valid for every semantically closed table applies to
the concrete finite table selected by the current production state. -/
theorem runRec_wf {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Δ : KVLCtx} {s : TcState .anon} {x : RecM .anon α}
    {Q : α → TcState .anon → Prop}
    {E : TcError .anon → TcState .anon → Prop}
    (hclosed : Methods.Closed layer semantics trProj world support)
    (hx : RecM.WF layer semantics trProj world support uvars Δ s x Q E) :
    TcM.WF (WhnfStateInv layer semantics trProj world support uvars Δ) s
      (TcM.runRec x) Q E := by
  simpa [TcM.runRec] using
    hx (methodsN s.recFuel.toNat)
      (Methods.WF.atUvars
        (Methods.methodsN_wf hclosed s.recFuel.toNat) uvars)

/-- Fixed-universe knot closure transports a reader-level proof to the
concrete finite method table selected by the production state. -/
theorem runRec_wfAt
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {x : RecM .anon α} {Q : α → TcState .anon → Prop}
    {E : TcError .anon → TcState .anon → Prop}
    (hclosed :
      Methods.ClosedAt layer semantics trProj world support uvars)
    (hx :
      RecM.WF layer semantics trProj world support uvars Delta s x Q E) :
    TcM.WF
      (WhnfStateInv layer semantics trProj world support uvars Delta) s
      (TcM.runRec x) Q E := by
  simpa [TcM.runRec] using
    hx (methodsN s.recFuel.toNat)
      (Methods.methodsN_wfAt hclosed s.recFuel.toNat)

end TcM

end Ix.Tc
