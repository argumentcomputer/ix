import Ix.Tc.Verify.Whnf

/-!
# Closing the remaining WHNF runtime contracts

This module discharges the state-safety side of the transient-Nat cache probe
for eagerly ingressed states and exposes the strictly smaller lazy-ingress
obligation needed by the same proof in driver-backed states.
-/

namespace Ix.Tc

namespace TcM

@[simp] theorem pure_apply (a : α) (s : TcState m) :
    (pure a : TcM m α) s = .ok a s := rfl

/-- The exact post-state installed after invoking a lazy-ingress hook.  The
address is marked before the hook runs, and the hook's returned environment
is retained on both success and error, matching `TcM.lazyIngressAddr`. -/
def lazyIngressPost (s : TcState .anon) (addr : Address)
    (env : KEnv .anon) : TcState .anon :=
  { { s with faultedAddrs := s.faultedAddrs.insert addr } with env }

/-- Semantic contract for the driver-owned lazy-ingress hook.

The hook is an arbitrary function stored in `TcState`; its type alone says
nothing about catalog agreement, intern support, cache provenance, or context
reconciliation.  This contract therefore requires the caller's invariant in
the exact environment-carrying post-state on both hook outcomes.  It is a
named implementation-refinement obligation, not an assumption derived from
the presence of the hook. -/
def LazyFaultPreserves (I : TcState .anon → Prop) : Prop :=
  ∀ {s : TcState .anon}
      {fault : Address → EStateM String (KEnv .anon) Bool} {addr : Address},
    s.lazyFault = some fault → I s →
      match fault addr s.env with
      | .ok _ env' => I (lazyIngressPost s addr env')
      | .error _ env' => I (lazyIngressPost s addr env')

/-- The production deduplication/error behavior preserves any invariant whose
installed hook satisfies `LazyFaultPreserves`.  In particular, the address
mark and the hook's partial environment survive an ingress error. -/
theorem lazyIngressAddr_wf {I : TcState .anon → Prop}
    (hfault : LazyFaultPreserves I) (addr : Address) (s : TcState .anon) :
    TcM.WF I s (TcM.lazyIngressAddr addr) (fun _ _ => True) := by
  intro hI
  unfold TcM.lazyIngressAddr
  cases hlazy : s.lazyFault with
  | none => exact ⟨hI, trivial⟩
  | some fault =>
      cases hcontains : s.faultedAddrs.contains addr with
      | true => simpa [hlazy, hcontains] using And.intro hI trivial
      | false =>
          have hpost := hfault (addr := addr) hlazy hI
          cases hrun : fault addr s.env with
          | ok found env' =>
              rw [hrun] at hpost
              simpa [hlazy, hcontains, lazyIngressPost, hrun] using
                And.intro hpost trivial
          | error err env' =>
              rw [hrun] at hpost
              simpa [hlazy, hcontains, lazyIngressPost, hrun] using
                And.intro hpost trivial

/-- Constant lookup preserves the invariant through the real fast hit,
lazy-fault, retry, post-fault miss, and hook-error paths. -/
theorem tryGetConst_wf {I : TcState .anon → Prop}
    (hfault : LazyFaultPreserves I) (id : KId .anon) (s : TcState .anon) :
    TcM.WF I s (TcM.tryGetConst id) (fun _ _ => True) := by
  unfold TcM.tryGetConst
  apply TcM.WF.bind
    (Q₁ := fun read after => read = after)
    (TcM.WF.get fun _ => rfl)
  intro read before hread
  subst read
  split
  · exact TcM.WF.pure fun _ => trivial
  · apply TcM.WF.bind
      (Q₁ := fun read after => read = after)
      (TcM.WF.get fun _ => rfl)
    intro read beforeFault hread
    subst read
    apply TcM.WF.bind
      (Q₁ := fun _ _ => True)
      (lazyIngressAddr_wf hfault id.addr beforeFault)
    intro _ afterFault _
    apply TcM.WF.bind
      (Q₁ := fun read after => read = after)
      (TcM.WF.get fun _ => rfl)
    intro read after hread
    subst read
    split
    · exact TcM.WF.pure fun _ => trivial
    · split
      · exact TcM.WF.throw fun _ => trivial
      · exact TcM.WF.pure fun _ => trivial

/-- An invariant-indexed proof that lazy ingress is absent is a vacuous
instance of the general hook contract. -/
theorem LazyFaultPreserves.of_none {I : TcState .anon → Prop}
    (hnoLazy : ∀ {s}, I s → s.lazyFault = none) :
    LazyFaultPreserves I := by
  intro s fault addr hlazy hI
  rw [hnoLazy hI] at hlazy
  contradiction

/-- Without a lazy ingress hook, constant lookup is a state-pure optional
read, including the miss case. -/
theorem tryGetConst_noLazy {id : KId .anon} {s : TcState .anon}
    (hlazy : s.lazyFault = none) :
    TcM.tryGetConst id s = .ok (s.env.get? id) s := by
  unfold TcM.tryGetConst
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ s = _
  unfold EStateM.bind
  rw [show (get : TcM .anon (TcState .anon)) s = .ok s s from rfl]
  simp only
  cases hget : s.env.get? id with
  | some c => rfl
  | none =>
      simp only [pure_bind]
      change EStateM.bind (get : TcM .anon (TcState .anon)) _ s = _
      unfold EStateM.bind
      rw [show (get : TcM .anon (TcState .anon)) s = .ok s s from rfl]
      simp only [hlazy, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      change EStateM.bind (TcM.lazyIngressAddr id.addr) _ s = _
      unfold EStateM.bind TcM.lazyIngressAddr
      rw [hlazy]
      simp only
      change EStateM.bind (get : TcM .anon (TcState .anon)) _ s = _
      unfold EStateM.bind
      rw [show (get : TcM .anon (TcState .anon)) s = .ok s s from rfl]
      simp [hget]

end TcM

namespace RecM

@[simp] theorem prims_run (methods : Methods m) (s : TcState m) :
    (RecM.prims : RecM m (Primitives m)).run methods s = .ok s.prims s := rfl

/-! ### Linear Nat descriptor ingress -/

/-- The concrete descriptor lookup used by the linear Nat recognizer
preserves an arbitrary invariant through fast lookup, lazy ingress success,
lazy ingress error, and post-ingress miss.  On a hit it also retains the
exact application spine stored in the returned descriptor view. -/
theorem natRecLiteralParts_wf {I : TcState .anon → Prop}
    (hfault : TcM.LazyFaultPreserves I) (methods : Methods .anon)
    (source : KExpr .anon) (s : TcState .anon) :
    TcM.WF I s ((natRecLiteralParts source).run methods)
      (fun result _ => NatRecLiteralPartsPost source result) := by
  unfold natRecLiteralParts
  rcases hcollect : source.collectSpine with ⟨head, spine⟩
  cases head <;> simp only
  all_goals try exact TcM.WF.pure fun _ => trivial
  case const id us info =>
    rw [ReaderT.run_bind]
    apply TcM.WF.bind
      (Q₁ := fun p after => p = after.prims)
    · exact fun hI => ⟨hI, rfl⟩
    · intro p after hp
      subst p
      split
      · exact TcM.WF.pure fun _ => trivial
      · rw [ReaderT.run_bind]
        apply TcM.WF.bind
          (Q₁ := fun _ _ => True)
          (TcM.tryGetConst_wf hfault id after)
        intro found afterLookup _
        cases found with
        | none => exact TcM.WF.pure fun _ => trivial
        | some c =>
            cases c <;> simp only
            all_goals try exact TcM.WF.pure fun _ => trivial
            case recr name levelParams k isUnsafe lvls params indices motives
                minors block memberIdx ty rules leanAll =>
              split
              · exact TcM.WF.pure fun _ => trivial
              · cases hmajor :
                    spine[(params.toNat + motives.toNat + minors.toNat +
                      indices.toNat)]? with
                | none => exact TcM.WF.pure fun _ => trivial
                | some majorExpr =>
                    cases majorExpr <;>
                      try exact TcM.WF.pure fun _ => trivial
                    case nat major blob majorInfo =>
                      apply TcM.WF.pure
                      intro _
                      change source.collectSpine.2 = spine
                      exact congrArg Prod.snd hcollect

namespace NatRecLiteralPartsPreserves

/-- Package the generic lazy-hook theorem as the exact operational premise
consumed by `NatSuccLinearOracle.of_reflection`. -/
theorem of_lazy
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    (hfault : ∀ {uvars : Nat} {Delta : KVLCtx},
      TcM.LazyFaultPreserves
        (WhnfStateInv layer semantics trProj world support uvars Delta)) :
    NatRecLiteralPartsPreserves layer semantics trProj world support := by
  intro uvars Delta source s methods hmethods
  exact natRecLiteralParts_wf (hfault (uvars := uvars) (Delta := Delta))
    methods source s

/-- Eagerly ingressed states are the no-hook specialization of `of_lazy`. -/
theorem eager
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    (hnoLazy : ∀ {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon},
      WhnfStateInv layer semantics trProj world support uvars Delta s →
      s.lazyFault = none) :
    NatRecLiteralPartsPreserves layer semantics trProj world support :=
  of_lazy fun {_ _} => TcM.LazyFaultPreserves.of_none hnoLazy

end NatRecLiteralPartsPreserves

/-- Driver-facing form of the uniform Nat field.  The descriptor lookup's
whole-computation preservation premise is constructed from the exact lazy
hook contract, so callers state only the hook refinement plus the two honest
semantic boundaries: linear Nat.rec reflection and canonical Nat/Bool
result-shape separation. -/
theorem tryReduceNatWithSuccMode_optional_wf_of_lazy_boundaries
    {α : Type} {initial : TcState .anon} {program : TcM .anon α}
    {requests : List WalkerRequest}
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {flags : WhnfFlags}
    (context : ∀ mode,
      NoDeltaPrimitiveContext world support flags mode)
    (hrun : RunAssumptions initial program requests support)
    (theory : ∀ uvars, WhnfTheory trProj world uvars)
    (writes : NatSuccStuckWriteOracle semantics world support)
    (hfault : ∀ {uvars : Nat} {Delta : KVLCtx},
      TcM.LazyFaultPreserves
        (WhnfStateInv .noAccel semantics trProj world support uvars Delta))
    (reflection : NatSuccLinearReflection .noAccel semantics trProj world
      support)
    (shape : NatCollapseRequestCensus.NatBoolResultShapeSeparation world)
    (mode : NatSuccMode) :
    OptionalReduction.WF .noAccel semantics trProj world support
      (fun source => tryReduceNatWithSuccMode source mode) :=
  tryReduceNatWithSuccMode_optional_wf_of_boundaries context hrun theory
    writes (NatRecLiteralPartsPreserves.of_lazy hfault) reflection shape
    mode

/-- The inner recursor classifier preserves an arbitrary invariant through
its sole effectful operation, `tryGetConst`, provided the installed lazy hook
preserves that invariant. -/
theorem isNatLiteralRecursorApp_wf {I : TcState .anon → Prop}
    (hfault : TcM.LazyFaultPreserves I) (methods : Methods .anon)
    (source : KExpr .anon) (s : TcState .anon) :
    TcM.WF I s ((isNatLiteralRecursorApp source).run methods)
      (fun _ _ => True) := by
  unfold isNatLiteralRecursorApp
  rcases hcollect : source.collectSpine with ⟨head, spine⟩
  cases head <;> simp only
  all_goals try exact TcM.WF.pure fun _ => trivial
  case const id us info =>
    rw [ReaderT.run_bind]
    apply TcM.WF.bind
      (Q₁ := fun p after => p = after.prims)
    · exact fun hI => ⟨hI, rfl⟩
    · intro p after hp
      subst p
      split
      · exact TcM.WF.pure fun _ => trivial
      · rw [ReaderT.run_bind]
        apply TcM.WF.bind
          (Q₁ := fun _ _ => True)
          (TcM.tryGetConst_wf hfault id after)
        intro found after _
        cases found with
        | none => exact TcM.WF.pure fun _ => trivial
        | some c =>
            cases c <;> simp only
            all_goals try exact TcM.WF.pure fun _ => trivial
            case recr name levelParams k isUnsafe lvls params indices motives
                minors block memberIdx ty rules leanAll =>
              cases spine[(params + motives + minors + indices).toNat]?
              · exact TcM.WF.pure fun _ => trivial
              · next major =>
                  cases major <;> exact TcM.WF.pure fun _ => trivial

/-- The complete transient-work classifier preserves the invariant across
both of its possible recursor lookups.  The second lookup is reached only
through the production `Nat.succ` shape test, but uses the same lazy hook
contract as the first. -/
theorem isTransientNatLiteralWork_wf {I : TcState .anon → Prop}
    (hfault : TcM.LazyFaultPreserves I) (methods : Methods .anon)
    (source : KExpr .anon) (s : TcState .anon) :
    TcM.WF I s ((isTransientNatLiteralWork source).run methods)
      (fun _ _ => True) := by
  unfold isTransientNatLiteralWork
  rw [ReaderT.run_bind]
  apply TcM.WF.bind
    (Q₁ := fun _ _ => True)
    (isNatLiteralRecursorApp_wf hfault methods source s)
  intro first after _
  cases first with
  | true => exact TcM.WF.pure fun _ => trivial
  | false =>
      simp only [Bool.false_eq_true, if_false]
      rcases hcollect : source.collectSpine with ⟨head, args⟩
      cases head <;> simp only
      all_goals try exact TcM.WF.pure fun _ => trivial
      case const id us info =>
        rw [ReaderT.run_bind]
        apply TcM.WF.bind
          (Q₁ := fun p state => p = state.prims)
        · exact fun hI => ⟨hI, rfl⟩
        · intro p state hp
          subst p
          split
          · exact isNatLiteralRecursorApp_wf hfault methods args[0]! state
          · exact TcM.WF.pure fun _ => trivial

/-- The inner recursor classifier is likewise state-pure without lazy
ingress. -/
theorem isNatLiteralRecursorApp_noLazy {methods : Methods .anon}
    {source : KExpr .anon} {s : TcState .anon}
    (hlazy : s.lazyFault = none) :
    ∃ answer, (isNatLiteralRecursorApp source).run methods s =
      .ok answer s := by
  unfold isNatLiteralRecursorApp
  rcases hcollect : source.collectSpine with ⟨head, spine⟩
  cases head <;> simp only
  all_goals try exact ⟨false, rfl⟩
  case const id us info =>
    rw [ReaderT.run_bind]
    change ∃ answer, EStateM.bind
      ((RecM.prims : RecM .anon (Primitives .anon)).run methods) _ s =
        .ok answer s
    unfold EStateM.bind
    rw [prims_run]
    simp only
    split
    · exact ⟨false, rfl⟩
    · rw [ReaderT.run_bind]
      change ∃ answer, EStateM.bind (TcM.tryGetConst id) _ s =
        .ok answer s
      unfold EStateM.bind
      rw [TcM.tryGetConst_noLazy hlazy]
      cases hconst : s.env.get? id with
      | none => exact ⟨false, rfl⟩
      | some c =>
          cases c with
          | defn => exact ⟨false, rfl⟩
          | axio => exact ⟨false, rfl⟩
          | quot => exact ⟨false, rfl⟩
          | indc => exact ⟨false, rfl⟩
          | ctor => exact ⟨false, rfl⟩
          | recr name levelParams k isUnsafe lvls params indices motives
              minors block memberIdx ty rules leanAll =>
              simp only
              cases hmajor : spine[(params + motives + minors + indices).toNat]?
              · exact ⟨false, rfl⟩
              · next major =>
                  cases major <;>
                    first | exact ⟨false, rfl⟩ | exact ⟨true, rfl⟩

/-- The transient classifier is state-pure when all constants have already
been ingressed. -/
theorem isTransientNatLiteralWork_noLazy {methods : Methods .anon}
    {source : KExpr .anon} {s : TcState .anon}
    (hlazy : s.lazyFault = none) :
    ∃ answer, (isTransientNatLiteralWork source).run methods s =
      .ok answer s := by
  obtain ⟨first, hfirst⟩ := isNatLiteralRecursorApp_noLazy
    (methods := methods) (source := source) hlazy
  unfold isTransientNatLiteralWork
  rw [ReaderT.run_bind]
  change ∃ answer, EStateM.bind
    ((isNatLiteralRecursorApp source).run methods) _ s = .ok answer s
  unfold EStateM.bind
  rw [hfirst]
  cases first with
  | true => exact ⟨true, rfl⟩
  | false =>
      simp only [Bool.false_eq_true, if_false]
      rcases hcollect : source.collectSpine with ⟨head, args⟩
      cases head <;> simp only
      all_goals try exact ⟨false, rfl⟩
      case const id us info =>
        rw [ReaderT.run_bind]
        change ∃ answer, EStateM.bind
          ((RecM.prims : RecM .anon (Primitives .anon)).run methods) _ s =
            .ok answer s
        unfold EStateM.bind
        rw [prims_run]
        simp only
        split
        · exact isNatLiteralRecursorApp_noLazy
            (methods := methods) (source := args[0]!) hlazy
        · exact ⟨false, rfl⟩

namespace TransientNatWork

/-- General lazy-ingress closure of the transient probe.  The formerly
opaque shell premise is reduced to the exact driver hook contract, including
the environment retained by a failing ingress. -/
theorem preserving {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx}
    (hfault : TcM.LazyFaultPreserves
      (WhnfStateInv layer semantics trProj world support uvars Delta))
    (source : KExpr .anon) :
    TransientNatWork.WF layer semantics trProj world support uvars Delta
      source := by
  intro s methods hmethods
  exact isTransientNatLiteralWork_wf hfault methods source s

/-- Eagerly ingressed runs discharge the formerly opaque transient-probe
contract.  The premise is deliberately invariant-indexed so callers cannot
use one initial `lazyFault = none` fact after an unrelated state mutation. -/
theorem eager {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx}
    (hnoLazy : ∀ {s},
      WhnfStateInv layer semantics trProj world support uvars Delta s →
      s.lazyFault = none) (source : KExpr .anon) :
    TransientNatWork.WF layer semantics trProj world support uvars Delta
      source := by
  intro s methods hmethods hI
  obtain ⟨answer, hrun⟩ := isTransientNatLiteralWork_noLazy
    (methods := methods) (source := source) (hnoLazy hI)
  rw [hrun]
  exact ⟨hI, trivial⟩

end TransientNatWork

end RecM

end Ix.Tc
