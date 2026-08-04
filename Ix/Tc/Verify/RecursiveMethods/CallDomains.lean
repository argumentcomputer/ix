import Ix.Tc.Verify.Knot

/-!
# Fuel-indexed recursive-method call domains

`RunSupport` is the finite collision and result footprint of one concrete
checker run.  It is not an all-depth method-call domain: successful inference
may construct a value which belongs to the run footprint without recursively
calling inference on that value at the same fuel depth.

This module separates those roles.  `Methods.CallDomain` records which calls
are admitted at one method-table depth, while `Methods.WFAtOn` retains one
fixed finite `RunSupport` for state, collision, cache, and successful-result
facts.  A `CallScheduleAt` supplies a distinct domain for each finite
`methodsN` layer.  Its induction theorem follows the production table exactly
and never asks one domain to be closed under arbitrarily many layers.

The old `Methods.WFAt` contract remains available during migration.  The
conversion theorems below identify it with the special case whose call domain
is the entire run support; `FiniteSupportBoundary` proves why that special case
cannot be the final public interface for sort-producing runs.
-/

namespace Ix.Tc

namespace Methods

/-- Calls admitted at one remaining-recursion-fuel depth.  The policy
arguments are retained because the production table exposes them as distinct
back-edges. -/
structure CallDomain where
  whnf : KExpr .anon → Prop
  whnfCore : KExpr .anon → Prop
  whnfMode : KExpr .anon → NatSuccMode → Prop
  whnfCoreFlags : KExpr .anon → WhnfFlags → Prop
  infer : KExpr .anon → Prop
  isDefEq : KExpr .anon → KExpr .anon → Prop

namespace CallDomain

/-- No recursive calls are admitted. -/
def empty : CallDomain where
  whnf := fun _ => False
  whnfCore := fun _ => False
  whnfMode := fun _ _ => False
  whnfCoreFlags := fun _ _ => False
  infer := fun _ => False
  isDefEq := fun _ _ => False

/-- Admit only inference calls satisfying `admitted`; every other method
field is empty.  This is useful for exact syntax-directed leaves which make
no recursive callbacks. -/
def inferOnly (admitted : KExpr .anon → Prop) : CallDomain where
  whnf := fun _ => False
  whnfCore := fun _ => False
  whnfMode := fun _ _ => False
  whnfCoreFlags := fun _ _ => False
  infer := admitted
  isDefEq := fun _ _ => False

/-- The one-source inference domain. -/
def singletonInfer (source : KExpr .anon) : CallDomain :=
  inferOnly (fun candidate => candidate = source)

/-- The legacy same-support domain, useful only as a migration adapter. -/
def support (scope : RunSupport) : CallDomain where
  whnf := scope
  whnfCore := scope
  whnfMode := fun source _ => scope source
  whnfCoreFlags := fun source _ => scope source
  infer := scope
  isDefEq := fun left right => scope left ∧ scope right

/-- Every admitted input lies in the finite run footprint. -/
structure Within (calls : CallDomain) (scope : RunSupport) : Prop where
  whnf : ∀ {source}, calls.whnf source → scope source
  whnfCore : ∀ {source}, calls.whnfCore source → scope source
  whnfMode : ∀ {source mode}, calls.whnfMode source mode → scope source
  whnfCoreFlags : ∀ {source flags},
    calls.whnfCoreFlags source flags → scope source
  infer : ∀ {source}, calls.infer source → scope source
  isDefEq : ∀ {left right},
    calls.isDefEq left right → scope left ∧ scope right

theorem support_within (scope : RunSupport) :
    (support scope).Within scope where
  whnf h := h
  whnfCore h := h
  whnfMode h := h
  whnfCoreFlags h := h
  infer h := h
  isDefEq h := h

theorem empty_within (scope : RunSupport) : empty.Within scope where
  whnf h := False.elim h
  whnfCore h := False.elim h
  whnfMode h := False.elim h
  whnfCoreFlags h := False.elim h
  infer h := False.elim h
  isDefEq h := False.elim h

theorem inferOnly_within {admitted : KExpr .anon → Prop}
    {scope : RunSupport}
    (hwithin : ∀ {source}, admitted source → scope source) :
    (inferOnly admitted).Within scope where
  whnf h := False.elim h
  whnfCore h := False.elim h
  whnfMode h := False.elim h
  whnfCoreFlags h := False.elim h
  infer h := hwithin h
  isDefEq h := False.elim h

theorem singletonInfer_within {source : KExpr .anon} {scope : RunSupport}
    (hsource : scope source) : (singletonInfer source).Within scope :=
  inferOnly_within fun h => h ▸ hsource

end CallDomain

/-- Six-field semantic contract restricted to the calls admitted at one
finite table depth.  Successful syntax-producing methods still return values
inside the shared finite run footprint. -/
structure WFAtOn (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (scope : RunSupport)
    (uvars : Nat) (calls : CallDomain) (methods : Methods .anon) : Prop where
  within : calls.Within scope
  whnf : ∀ {Delta s source sourceV},
    calls.whnf source →
    TrKExprS world.venv uvars world.nameOf trProj Delta source sourceV →
    TcM.WF (WhnfStateInv layer semantics trProj world scope uvars Delta) s
      (methods.whnf source)
      (fun result _ => scope result ∧
        WhnfPost trProj world uvars Delta sourceV result)
  whnfCore : ∀ {Delta s source sourceV},
    calls.whnfCore source →
    TrKExprS world.venv uvars world.nameOf trProj Delta source sourceV →
    TcM.WF (WhnfStateInv layer semantics trProj world scope uvars Delta) s
      (methods.whnfCore source)
      (fun result _ => scope result ∧
        WhnfPost trProj world uvars Delta sourceV result)
  whnfMode : ∀ {Delta s source sourceV} {mode : NatSuccMode},
    calls.whnfMode source mode →
    TrKExprS world.venv uvars world.nameOf trProj Delta source sourceV →
    TcM.WF (WhnfStateInv layer semantics trProj world scope uvars Delta) s
      (methods.whnfMode source mode)
      (fun result _ => scope result ∧
        WhnfPost trProj world uvars Delta sourceV result)
  whnfCoreFlags : ∀ {Delta s source sourceV} {flags : WhnfFlags},
    calls.whnfCoreFlags source flags →
    TrKExprS world.venv uvars world.nameOf trProj Delta source sourceV →
    TcM.WF (WhnfStateInv layer semantics trProj world scope uvars Delta) s
      (methods.whnfCoreFlags source flags)
      (fun result _ => scope result ∧
        WhnfPost trProj world uvars Delta sourceV result)
  infer : ∀ {Delta s source sourceV},
    calls.infer source →
    TrKExprS world.venv uvars world.nameOf trProj Delta source sourceV →
    TcM.WF (WhnfStateInv layer semantics trProj world scope uvars Delta) s
      (methods.infer source)
      (fun ty _ => scope ty ∧
        InferPost trProj world uvars Delta sourceV ty)
  isDefEq : ∀ {Delta s left right leftV rightV},
    calls.isDefEq left right →
    TrKExprS world.venv uvars world.nameOf trProj Delta left leftV →
    TrKExprS world.venv uvars world.nameOf trProj Delta right rightV →
    TcM.WF (WhnfStateInv layer semantics trProj world scope uvars Delta) s
      (methods.isDefEq left right)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx leftV rightV)

namespace WFAtOn

/-- Every legacy same-support contract is a call-domain contract over the
entire support. -/
theorem ofWFAt
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {uvars : Nat} {methods : Methods .anon}
    (contract : Methods.WFAt layer semantics trProj world scope uvars
      methods) :
    Methods.WFAtOn layer semantics trProj world scope uvars
      (.support scope) methods where
  within := CallDomain.support_within scope
  whnf hcall htr := contract.whnf hcall htr
  whnfCore hcall htr := contract.whnfCore hcall htr
  whnfMode hcall htr := contract.whnfMode hcall htr
  whnfCoreFlags hcall htr := contract.whnfCoreFlags hcall htr
  infer hcall htr := contract.infer hcall htr
  isDefEq hcall hleft hright :=
    contract.isDefEq hcall.1 hcall.2 hleft hright

/-- Conversely, the full-support call domain recovers the legacy contract. -/
theorem toWFAt
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {uvars : Nat} {methods : Methods .anon}
    (contract : Methods.WFAtOn layer semantics trProj world scope uvars
      (.support scope) methods) :
    Methods.WFAt layer semantics trProj world scope uvars methods where
  whnf hsource htr := contract.whnf hsource htr
  whnfCore hsource htr := contract.whnfCore hsource htr
  whnfMode hsource htr := contract.whnfMode hsource htr
  whnfCoreFlags hsource htr := contract.whnfCoreFlags hsource htr
  infer hsource htr := contract.infer hsource htr
  isDefEq hleft hright hleftTr hrightTr :=
    contract.isDefEq ⟨hleft, hright⟩ hleftTr hrightTr

end WFAtOn

/-- The exhausted table satisfies any finite call domain because every field
throws `maxRecFuel` without changing state. -/
theorem methodsOut_wfAtOn
    (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (scope : RunSupport)
    (uvars : Nat) (calls : CallDomain) (within : calls.Within scope) :
    Methods.WFAtOn layer semantics trProj world scope uvars calls
      (methodsOut : Methods .anon) where
  within := within
  whnf _ _ := TcM.WF.throw (fun _ => trivial)
  whnfCore _ _ := TcM.WF.throw (fun _ => trivial)
  whnfMode _ _ := TcM.WF.throw (fun _ => trivial)
  whnfCoreFlags _ _ := TcM.WF.throw (fun _ => trivial)
  infer _ _ := TcM.WF.throw (fun _ => trivial)
  isDefEq _ _ _ := TcM.WF.throw (fun _ => trivial)

/-- One exact, possibly domain-changing induction step for the production
method table. -/
def StepWFAtOn (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (scope : RunSupport)
    (uvars : Nat) (before after : CallDomain) : Prop :=
  ∀ methods,
    Methods.WFAtOn layer semantics trProj world scope uvars before methods →
    Methods.WFAtOn layer semantics trProj world scope uvars after
      (Methods.next methods)

/-- A finite call-domain schedule for `methodsN depth`.  Index zero belongs
to `methodsOut`; index `n+1` describes calls into the `n+1`-layer table and
may route its recursive back-edges only into index `n`. -/
structure CallScheduleAt (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (scope : RunSupport)
    (uvars : Nat) (calls : Nat → CallDomain) (depth : Nat) : Prop where
  within : ∀ n, n ≤ depth → (calls n).Within scope
  step : ∀ n, n < depth →
    StepWFAtOn layer semantics trProj world scope uvars
      (calls n) (calls (n + 1))

namespace CallScheduleAt

/-- A finite schedule closes exactly the corresponding finite production
approximation—there is no quantification over greater fuel depths. -/
theorem methodsN
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {uvars : Nat} {calls : Nat → CallDomain} {depth : Nat}
    (schedule : CallScheduleAt layer semantics trProj world scope uvars
      calls depth) :
    ∀ n, n ≤ depth →
      Methods.WFAtOn layer semantics trProj world scope uvars (calls n)
        (Ix.Tc.methodsN (m := .anon) n)
  | 0, _ =>
      methodsOut_wfAtOn layer semantics trProj world scope uvars (calls 0)
        (schedule.within 0 (Nat.zero_le depth))
  | n + 1, hn => by
      rw [Methods.methodsN_succ]
      exact schedule.step n (Nat.lt_of_succ_le hn)
        (Ix.Tc.methodsN (m := .anon) n)
        (schedule.methodsN n (Nat.le_trans (Nat.le_succ n) hn))

/-- The contract selected at the schedule's terminal depth. -/
theorem selected
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {uvars : Nat} {calls : Nat → CallDomain} {depth : Nat}
    (schedule : CallScheduleAt layer semantics trProj world scope uvars
      calls depth) :
    Methods.WFAtOn layer semantics trProj world scope uvars (calls depth)
      (Ix.Tc.methodsN (m := .anon) depth) :=
  schedule.methodsN depth (Nat.le_refl depth)

/-- The method body executed by `TcM.runRec` sits one layer above its
`methodsN depth` callback table.  A schedule through `depth + 1` therefore
supplies the exact contract for the public body, with no off-by-one appeal to
an all-depth closure. -/
theorem nextSelected
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {uvars : Nat} {calls : Nat → CallDomain} {depth : Nat}
    (schedule : CallScheduleAt layer semantics trProj world scope uvars
      calls (depth + 1)) :
    Methods.WFAtOn layer semantics trProj world scope uvars
      (calls (depth + 1))
      (Methods.next (Ix.Tc.methodsN (m := .anon) depth)) :=
  schedule.step depth (Nat.lt_succ_self depth)
    (Ix.Tc.methodsN (m := .anon) depth)
    (schedule.methodsN depth (Nat.le_succ depth))

end CallScheduleAt

end Methods

namespace RecM

/-- A reader action whose execution does not inspect the recursive method
table.  Constructor-local leaf branches often satisfy this even though their
uniform dispatcher theorem is stated in `RecM`. -/
def MethodIndependent (action : RecM .anon alpha) : Prop :=
  ∀ methods : Methods .anon,
    action.run methods = action.run (methodsOut : Methods .anon)

/-- Reader-level Hoare triple under one explicit method-call domain. -/
def WFOn (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (scope : RunSupport)
    (uvars : Nat) (calls : Methods.CallDomain) (Delta : KVLCtx)
    (s : TcState .anon) (action : RecM .anon alpha)
    (Q : alpha → TcState .anon → Prop)
    (E : TcError .anon → TcState .anon → Prop := fun _ _ => True) : Prop :=
  ∀ methods,
    Methods.WFAtOn layer semantics trProj world scope uvars calls methods →
    TcM.WF (WhnfStateInv layer semantics trProj world scope uvars Delta) s
      (action.run methods) Q E

namespace WFOn

/-- Reuse an existing same-support proof for a method-independent action.
The old contract is needed only for the exhausted table chosen as a proof
witness; execution is then transported to the caller's actual bounded table. -/
theorem ofWF_of_methodIndependent
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {uvars : Nat} {calls : Methods.CallDomain} {Delta : KVLCtx}
    {s : TcState .anon} {action : RecM .anon alpha}
    {Q : alpha → TcState .anon → Prop}
    {E : TcError .anon → TcState .anon → Prop}
    (hindependent : MethodIndependent action)
    (h : RecM.WF layer semantics trProj world scope uvars Delta s
      action Q E) :
    RecM.WFOn layer semantics trProj world scope uvars calls Delta s
      action Q E := by
  intro methods contract
  rw [hindependent methods]
  exact h (methodsOut : Methods .anon)
    (Methods.methodsOut_wfAt layer semantics trProj world scope uvars)

theorem pure
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {uvars : Nat} {calls : Methods.CallDomain} {Delta : KVLCtx}
    {s : TcState .anon} {Q : alpha → TcState .anon → Prop}
    {E : TcError .anon → TcState .anon → Prop} {value : alpha}
    (h : WhnfStateInv layer semantics trProj world scope uvars Delta s →
      Q value s) :
    RecM.WFOn layer semantics trProj world scope uvars calls Delta s
      (pure value) Q E := by
  intro methods contract
  exact TcM.WF.pure h

theorem throw
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {uvars : Nat} {calls : Methods.CallDomain} {Delta : KVLCtx}
    {s : TcState .anon} {Q : alpha → TcState .anon → Prop}
    {E : TcError .anon → TcState .anon → Prop} {err : TcError .anon}
    (h : WhnfStateInv layer semantics trProj world scope uvars Delta s →
      E err s) :
    RecM.WFOn layer semantics trProj world scope uvars calls Delta s
      (throw err) Q E := by
  intro methods contract
  exact TcM.WF.throw h

theorem mono
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {uvars : Nat} {calls : Methods.CallDomain} {Delta : KVLCtx}
    {s : TcState .anon} {action : RecM .anon alpha}
    {Q Q' : alpha → TcState .anon → Prop}
    {E E' : TcError .anon → TcState .anon → Prop}
    (h : RecM.WFOn layer semantics trProj world scope uvars calls Delta s
      action Q E)
    (hQ : ∀ value after, Q value after → Q' value after)
    (hE : ∀ err after, E err after → E' err after) :
    RecM.WFOn layer semantics trProj world scope uvars calls Delta s
      action Q' E' := by
  intro methods contract
  exact TcM.WF.mono (h methods contract) hQ hE

/-- Expose invariant preservation in the success postcondition. -/
theorem withInv
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {uvars : Nat} {calls : Methods.CallDomain} {Delta : KVLCtx}
    {s : TcState .anon} {action : RecM .anon alpha}
    {Q : alpha → TcState .anon → Prop}
    {E : TcError .anon → TcState .anon → Prop}
    (h : RecM.WFOn layer semantics trProj world scope uvars calls Delta s
      action Q E) :
    RecM.WFOn layer semantics trProj world scope uvars calls Delta s action
      (fun value after =>
        WhnfStateInv layer semantics trProj world scope uvars Delta after ∧
          Q value after)
      E := by
  intro methods contract hI
  have hpost := h methods contract hI
  match hrun : action.run methods s with
  | .ok value after =>
      rw [hrun] at hpost
      exact ⟨hpost.1, hpost.1, hpost.2⟩
  | .error err after =>
      rw [hrun] at hpost
      exact hpost

theorem bind
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {uvars : Nat} {calls : Methods.CallDomain} {Delta : KVLCtx}
    {s : TcState .anon} {action : RecM .anon alpha}
    {next : alpha → RecM .anon beta}
    {Q1 : alpha → TcState .anon → Prop}
    {Q2 : beta → TcState .anon → Prop}
    {E : TcError .anon → TcState .anon → Prop}
    (haction : RecM.WFOn layer semantics trProj world scope uvars calls
      Delta s action Q1 E)
    (hnext : ∀ value after, Q1 value after →
      RecM.WFOn layer semantics trProj world scope uvars calls Delta after
        (next value) Q2 E) :
    RecM.WFOn layer semantics trProj world scope uvars calls Delta s
      (action >>= next) Q2 E := by
  intro methods contract
  exact TcM.WF.bind (haction methods contract) fun value after hvalue =>
    hnext value after hvalue methods contract

theorem liftTcM
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {uvars : Nat} {calls : Methods.CallDomain} {Delta : KVLCtx}
    {s : TcState .anon} {action : TcM .anon alpha}
    {Q : alpha → TcState .anon → Prop}
    {E : TcError .anon → TcState .anon → Prop}
    (h : TcM.WF
      (WhnfStateInv layer semantics trProj world scope uvars Delta) s
      action Q E) :
    RecM.WFOn layer semantics trProj world scope uvars calls Delta s
      (liftM action) Q E := by
  intro methods contract
  exact h

/-- Reader-level state observation is independent of the callback table. -/
theorem get
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {uvars : Nat} {calls : Methods.CallDomain} {Delta : KVLCtx}
    {s : TcState .anon}
    {Q : TcState .anon → TcState .anon → Prop}
    {E : TcError .anon → TcState .anon → Prop}
    (h : WhnfStateInv layer semantics trProj world scope uvars Delta s →
      Q s s) :
    RecM.WFOn layer semantics trProj world scope uvars calls Delta s
      (get : RecM .anon (TcState .anon)) Q E := by
  intro methods contract
  exact TcM.WF.get h

end WFOn

end RecM

namespace TcM

/-- Apply a reader proof to the exact finite table selected by a call-domain
schedule. -/
theorem runRec_wfAtOn
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {scope : RunSupport}
    {uvars : Nat} {calls : Nat → Methods.CallDomain}
    {Delta : KVLCtx} {s : TcState .anon} {action : RecM .anon alpha}
    {Q : alpha → TcState .anon → Prop}
    {E : TcError .anon → TcState .anon → Prop}
    (schedule : Methods.CallScheduleAt layer semantics trProj world scope
      uvars calls s.recFuel.toNat)
    (haction : RecM.WFOn layer semantics trProj world scope uvars
      (calls s.recFuel.toNat) Delta s action Q E) :
    TcM.WF (WhnfStateInv layer semantics trProj world scope uvars Delta) s
      (TcM.runRec action) Q E := by
  simpa [TcM.runRec] using
    haction (Ix.Tc.methodsN (m := .anon) s.recFuel.toNat) schedule.selected

end TcM

end Ix.Tc
