import Ix.Tc.Verify.DefEq
import Ix.Tc.Verify.RecursiveMethods.CallDomains

/-!
# Run-scoped recursive-method call domains

The original bounded call-domain contract carries the kernel invariant but
not the finite context-digest state domain.  K2S must retain both: a method
may construct or reuse a suffix key only while its concrete pre-state belongs
to `ScopedKernelSuffixModel.StateInScope`, and both success and partial-error
states must remain in that domain.

This module deliberately parallels only the bounded public knot.  The legacy
all-depth/global-model interfaces remain compatibility artifacts and are not
used to justify the scoped schedule below.
-/

namespace Ix.Tc

namespace Methods

/-- Six-field method contract over one finite call domain and one finite
suffix-model state domain. -/
structure ScopedWFAtOn
    {trProj : RawProjRel} {world : VerifyWorld}
    (model : ScopedKernelSuffixModel trProj world)
    (layer : WhnfLayer) (semantics : CacheSemantics)
    (scope : RunSupport) (calls : CallDomain)
    (methods : Methods .anon) : Prop where
  within : calls.Within scope
  whnf : ∀ {Delta s source sourceV},
    calls.whnf source →
    TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta source
      sourceV →
    TcM.WF (ScopedWhnfStateInv model layer semantics scope Delta) s
      (methods.whnf source)
      (fun result _ => scope result ∧
        WhnfPost trProj world model.keys.uvars Delta sourceV result)
  whnfCore : ∀ {Delta s source sourceV},
    calls.whnfCore source →
    TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta source
      sourceV →
    TcM.WF (ScopedWhnfStateInv model layer semantics scope Delta) s
      (methods.whnfCore source)
      (fun result _ => scope result ∧
        WhnfPost trProj world model.keys.uvars Delta sourceV result)
  whnfMode : ∀ {Delta s source sourceV} {mode : NatSuccMode},
    calls.whnfMode source mode →
    TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta source
      sourceV →
    TcM.WF (ScopedWhnfStateInv model layer semantics scope Delta) s
      (methods.whnfMode source mode)
      (fun result _ => scope result ∧
        WhnfPost trProj world model.keys.uvars Delta sourceV result)
  whnfCoreFlags : ∀ {Delta s source sourceV} {flags : WhnfFlags},
    calls.whnfCoreFlags source flags →
    TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta source
      sourceV →
    TcM.WF (ScopedWhnfStateInv model layer semantics scope Delta) s
      (methods.whnfCoreFlags source flags)
      (fun result _ => scope result ∧
        WhnfPost trProj world model.keys.uvars Delta sourceV result)
  infer : ∀ {Delta s source sourceV},
    calls.infer source →
    TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta source
      sourceV →
    TcM.WF (ScopedWhnfStateInv model layer semantics scope Delta) s
      (methods.infer source)
      (fun ty _ => scope ty ∧
        InferPost trProj world model.keys.uvars Delta sourceV ty)
  isDefEq : ∀ {Delta s left right leftV rightV},
    calls.isDefEq left right →
    TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta left
      leftV →
    TrKExprS world.venv model.keys.uvars world.nameOf trProj Delta right
      rightV →
    TcM.WF (ScopedWhnfStateInv model layer semantics scope Delta) s
      (methods.isDefEq left right)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU model.keys.uvars Delta.toCtx leftV rightV)

/-- One domain-changing induction step for the run-scoped production table. -/
def ScopedStepWFAtOn
    {trProj : RawProjRel} {world : VerifyWorld}
    (model : ScopedKernelSuffixModel trProj world)
    (layer : WhnfLayer) (semantics : CacheSemantics)
    (scope : RunSupport) (before after : CallDomain) : Prop :=
  ∀ methods,
    ScopedWFAtOn model layer semantics scope before methods →
    ScopedWFAtOn model layer semantics scope after (Methods.next methods)

/-- A finite call schedule which preserves both the checker invariant and
the scoped suffix-state witness at every selected table depth. -/
structure ScopedCallScheduleAt
    {trProj : RawProjRel} {world : VerifyWorld}
    (model : ScopedKernelSuffixModel trProj world)
    (layer : WhnfLayer) (semantics : CacheSemantics)
    (scope : RunSupport) (calls : Nat → CallDomain) (depth : Nat) : Prop where
  within : ∀ n, n ≤ depth → (calls n).Within scope
  step : ∀ n, n < depth →
    ScopedStepWFAtOn model layer semantics scope (calls n) (calls (n + 1))

/-- The exhausted table changes no state, hence preserves any finite
suffix-state domain on its error outcome. -/
theorem methodsOut_scopedWFAtOn
    {trProj : RawProjRel} {world : VerifyWorld}
    (model : ScopedKernelSuffixModel trProj world)
    (layer : WhnfLayer) (semantics : CacheSemantics)
    (scope : RunSupport) (calls : CallDomain) (within : calls.Within scope) :
    ScopedWFAtOn model layer semantics scope calls
      (methodsOut : Methods .anon) where
  within := within
  whnf _ _ := TcM.WF.throw (fun _ => trivial)
  whnfCore _ _ := TcM.WF.throw (fun _ => trivial)
  whnfMode _ _ := TcM.WF.throw (fun _ => trivial)
  whnfCoreFlags _ _ := TcM.WF.throw (fun _ => trivial)
  infer _ _ := TcM.WF.throw (fun _ => trivial)
  isDefEq _ _ _ := TcM.WF.throw (fun _ => trivial)

namespace ScopedCallScheduleAt

/-- Close exactly the finite production approximation named by this scoped
schedule. -/
theorem methodsN
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {scope : RunSupport} {calls : Nat → CallDomain} {depth : Nat}
    (schedule : ScopedCallScheduleAt model layer semantics scope calls depth) :
    ∀ n, n ≤ depth →
      ScopedWFAtOn model layer semantics scope (calls n)
        (Ix.Tc.methodsN (m := .anon) n)
  | 0, _ =>
      methodsOut_scopedWFAtOn model layer semantics scope (calls 0)
        (schedule.within 0 (Nat.zero_le depth))
  | n + 1, hn => by
      rw [Methods.methodsN_succ]
      exact schedule.step n (Nat.lt_of_succ_le hn)
        (Ix.Tc.methodsN (m := .anon) n)
        (schedule.methodsN n (Nat.le_trans (Nat.le_succ n) hn))

theorem selected
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {scope : RunSupport} {calls : Nat → CallDomain} {depth : Nat}
    (schedule : ScopedCallScheduleAt model layer semantics scope calls depth) :
    ScopedWFAtOn model layer semantics scope (calls depth)
      (Ix.Tc.methodsN (m := .anon) depth) :=
  schedule.methodsN depth (Nat.le_refl depth)

theorem nextSelected
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {scope : RunSupport} {calls : Nat → CallDomain} {depth : Nat}
    (schedule : ScopedCallScheduleAt model layer semantics scope calls
      (depth + 1)) :
    ScopedWFAtOn model layer semantics scope (calls (depth + 1))
      (Methods.next (Ix.Tc.methodsN (m := .anon) depth)) :=
  schedule.step depth (Nat.lt_succ_self depth)
    (Ix.Tc.methodsN (m := .anon) depth)
    (schedule.methodsN depth (Nat.le_succ depth))

end ScopedCallScheduleAt

end Methods

namespace RecM

/-- Reader-level Hoare triple under a finite method-call domain and a finite
suffix-model state domain. -/
def ScopedWFOn
    {trProj : RawProjRel} {world : VerifyWorld}
    (model : ScopedKernelSuffixModel trProj world)
    (layer : WhnfLayer) (semantics : CacheSemantics)
    (scope : RunSupport) (calls : Methods.CallDomain) (Delta : KVLCtx)
    (s : TcState .anon) (action : RecM .anon alpha)
    (Q : alpha → TcState .anon → Prop)
    (E : TcError .anon → TcState .anon → Prop := fun _ _ => True) : Prop :=
  ∀ methods,
    Methods.ScopedWFAtOn model layer semantics scope calls methods →
    TcM.WF (ScopedWhnfStateInv model layer semantics scope Delta) s
      (action.run methods) Q E

namespace ScopedWFOn

theorem pure
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {scope : RunSupport} {calls : Methods.CallDomain} {Delta : KVLCtx}
    {s : TcState .anon} {Q : alpha → TcState .anon → Prop}
    {E : TcError .anon → TcState .anon → Prop} {value : alpha}
    (h : ScopedWhnfStateInv model layer semantics scope Delta s →
      Q value s) :
    ScopedWFOn model layer semantics scope calls Delta s (pure value) Q E :=
  fun _ _ => TcM.WF.pure h

theorem throw
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {scope : RunSupport} {calls : Methods.CallDomain} {Delta : KVLCtx}
    {s : TcState .anon} {Q : alpha → TcState .anon → Prop}
    {E : TcError .anon → TcState .anon → Prop} {err : TcError .anon}
    (h : ScopedWhnfStateInv model layer semantics scope Delta s → E err s) :
    ScopedWFOn model layer semantics scope calls Delta s
      (throw err) Q E :=
  fun _ _ => TcM.WF.throw h

theorem mono
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {scope : RunSupport} {calls : Methods.CallDomain} {Delta : KVLCtx}
    {s : TcState .anon} {action : RecM .anon alpha}
    {Q Q' : alpha → TcState .anon → Prop}
    {E E' : TcError .anon → TcState .anon → Prop}
    (h : ScopedWFOn model layer semantics scope calls Delta s action Q E)
    (hQ : ∀ value after, Q value after → Q' value after)
    (hE : ∀ err after, E err after → E' err after) :
    ScopedWFOn model layer semantics scope calls Delta s action Q' E' :=
  fun methods contract => TcM.WF.mono (h methods contract) hQ hE

theorem withInv
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {scope : RunSupport} {calls : Methods.CallDomain} {Delta : KVLCtx}
    {s : TcState .anon} {action : RecM .anon alpha}
    {Q : alpha → TcState .anon → Prop}
    {E : TcError .anon → TcState .anon → Prop}
    (h : ScopedWFOn model layer semantics scope calls Delta s action Q E) :
    ScopedWFOn model layer semantics scope calls Delta s action
      (fun value after =>
        ScopedWhnfStateInv model layer semantics scope Delta after ∧
          Q value after)
      E :=
  fun methods contract => TcM.WF.withInv (h methods contract)

theorem bind
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {scope : RunSupport} {calls : Methods.CallDomain} {Delta : KVLCtx}
    {s : TcState .anon} {action : RecM .anon alpha}
    {next : alpha → RecM .anon beta}
    {Q1 : alpha → TcState .anon → Prop}
    {Q2 : beta → TcState .anon → Prop}
    {E : TcError .anon → TcState .anon → Prop}
    (haction : ScopedWFOn model layer semantics scope calls Delta s
      action Q1 E)
    (hnext : ∀ value after, Q1 value after →
      ScopedWFOn model layer semantics scope calls Delta after
        (next value) Q2 E) :
    ScopedWFOn model layer semantics scope calls Delta s
      (action >>= next) Q2 E := by
  intro methods contract
  exact TcM.WF.bind (haction methods contract) fun value after hvalue =>
    hnext value after hvalue methods contract

theorem liftTcM
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {scope : RunSupport} {calls : Methods.CallDomain} {Delta : KVLCtx}
    {s : TcState .anon} {action : TcM .anon alpha}
    {Q : alpha → TcState .anon → Prop}
    {E : TcError .anon → TcState .anon → Prop}
    (h : TcM.WF (ScopedWhnfStateInv model layer semantics scope Delta) s
      action Q E) :
    ScopedWFOn model layer semantics scope calls Delta s
      (liftM action) Q E :=
  fun _ _ => h

theorem get
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {scope : RunSupport} {calls : Methods.CallDomain} {Delta : KVLCtx}
    {s : TcState .anon}
    {Q : TcState .anon → TcState .anon → Prop}
    {E : TcError .anon → TcState .anon → Prop}
    (h : ScopedWhnfStateInv model layer semantics scope Delta s → Q s s) :
    ScopedWFOn model layer semantics scope calls Delta s
      (get : RecM .anon (TcState .anon)) Q E :=
  fun _ _ => TcM.WF.get h

end ScopedWFOn

end RecM

namespace TcM

/-- Apply a scoped reader proof to the exact finite table selected by the
state's recursion fuel. -/
theorem runRec_scoped_wfAtOn
    {trProj : RawProjRel} {world : VerifyWorld}
    {model : ScopedKernelSuffixModel trProj world}
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {scope : RunSupport} {calls : Nat → Methods.CallDomain}
    {Delta : KVLCtx} {s : TcState .anon} {action : RecM .anon alpha}
    {Q : alpha → TcState .anon → Prop}
    {E : TcError .anon → TcState .anon → Prop}
    (schedule : Methods.ScopedCallScheduleAt model layer semantics scope
      calls s.recFuel.toNat)
    (haction : RecM.ScopedWFOn model layer semantics scope
      (calls s.recFuel.toNat) Delta s action Q E) :
    TcM.WF (ScopedWhnfStateInv model layer semantics scope Delta) s
      (TcM.runRec action) Q E := by
  simpa [TcM.runRec] using
    haction (Ix.Tc.methodsN (m := .anon) s.recFuel.toNat) schedule.selected

end TcM

end Ix.Tc
