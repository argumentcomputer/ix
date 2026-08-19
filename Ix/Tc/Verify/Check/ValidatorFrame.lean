import Ix.Tc.Verify.Check.DeclarationValidation
import Ix.Tc.Verify.Whnf.RuntimeContracts

/-!
# State framing for the scoping validators

The validator's memo sets are local worklist arguments, but constant and
projection nodes may invoke lazy ingress.  Scoping soundness therefore does
not by itself show that the checker invariant is available when inference
starts.  This module proves that every validator outcome preserves an
arbitrary state invariant whose installed lazy-fault hook preserves it.
-/

namespace Ix.Tc

namespace RecM

/-- The universe validator is state-pure on every successful and exceptional
path.  Its seen set is an explicit result rather than checker state. -/
theorem validateUnivParamsSeen_go_frame :
    ∀ (bound : Nat) (stack : List (KUniv .anon))
      (seen : Std.HashSet Address) (methods : Methods .anon)
      (I : TcState .anon → Prop) (state : TcState .anon),
    TcM.WF I state
      ((RecM.validateUnivParamsSeen.go bound stack seen).run methods)
      (fun _ _ => True)
  | bound, [], seen, methods, I, state => by
      rw [RecM.validateUnivParamsSeen.go]
      exact TcM.WF.pure fun _ => trivial
  | bound, level :: stack, seen, methods, I, state => by
      rw [RecM.validateUnivParamsSeen.go]
      split
      · exact validateUnivParamsSeen_go_frame bound stack seen methods I state
      · cases level with
        | zero addr =>
            simp only [pure_bind]
            exact validateUnivParamsSeen_go_frame bound stack
              (seen.insert addr) methods I state
        | succ child addr =>
            simp only [pure_bind]
            exact validateUnivParamsSeen_go_frame bound (child :: stack)
              (seen.insert addr) methods I state
        | max left right addr =>
            simp only [pure_bind]
            exact validateUnivParamsSeen_go_frame bound
              (right :: left :: stack) (seen.insert addr) methods I state
        | imax left right addr =>
            simp only [pure_bind]
            exact validateUnivParamsSeen_go_frame bound
              (right :: left :: stack) (seen.insert addr) methods I state
        | param idx name addr =>
            simp only [pure_bind]
            split
            · exact TcM.WF.throw fun _ => trivial
            · exact validateUnivParamsSeen_go_frame bound stack
                (seen.insert addr) methods I state
termination_by _ stack _ _ _ _ => RecM.univWorkSize stack
decreasing_by
  all_goals simp_all [RecM.univWorkSize, KUniv.size]
  all_goals try omega
  all_goals exact KUniv.size_pos _

/-- Public universe-validation framing. -/
theorem validateUnivParamsSeen_frame
    (bound : Nat) (root : KUniv .anon) (seen : Std.HashSet Address)
    (methods : Methods .anon) (I : TcState .anon → Prop)
    (state : TcState .anon) :
    TcM.WF I state
      ((RecM.validateUnivParamsSeen root bound seen).run methods)
      (fun _ _ => True) := by
  rw [RecM.validateUnivParamsSeen_equation]
  exact validateUnivParamsSeen_go_frame bound [root] seen methods I state

/-- List-normalized framing for the constant-universe `for` loop. -/
theorem validateUnivRootsList_frame
    (bound : Nat) :
    ∀ (roots : List (KUniv .anon)) (seen : Std.HashSet Address)
      (methods : Methods .anon) (I : TcState .anon → Prop)
      (state : TcState .anon),
    TcM.WF I state
      ((forIn (m := RecM .anon) roots seen (fun level current => do
        let next ← validateUnivParamsSeen level bound current
        pure (.yield next))).run methods)
      (fun _ _ => True)
  | [], seen, methods, I, state => by
      rw [List.forIn_nil]
      exact TcM.WF.pure fun _ => trivial
  | level :: roots, seen, methods, I, state => by
      rw [List.forIn_cons, ReaderT.run_bind, ReaderT.run_bind, bind_assoc]
      apply TcM.WF.bind
        (validateUnivParamsSeen_frame bound level seen methods I state)
      intro nextSeen nextState _
      exact validateUnivRootsList_frame bound roots nextSeen methods I
        nextState

/-- Array-level framing in the exact shape used by constant validation. -/
theorem validateUnivRootsArray_frame
    (bound : Nat) (roots : Array (KUniv .anon))
    (seen : Std.HashSet Address) (methods : Methods .anon)
    (I : TcState .anon → Prop) (state : TcState .anon) :
    TcM.WF I state
      ((forIn (m := RecM .anon) roots seen (fun level current => do
        let next ← validateUnivParamsSeen level bound current
        pure (.yield next))).run methods)
      (fun _ _ => True) := by
  rw [← Array.forIn_toList]
  exact validateUnivRootsList_frame bound roots.toList seen methods I state

end RecM

namespace TcM

namespace LazyFaultPreserves

/-- Lazy ingress never writes the checker policy bit.  Any semantic hook
frame can therefore be strengthened with a fixed `inferOnly` value on both
successful and partial-error outcomes. -/
theorem withInferOnly
    {I : TcState .anon → Prop} (hfault : LazyFaultPreserves I)
    (policy : Bool) :
    LazyFaultPreserves (fun state => I state ∧ state.inferOnly = policy) := by
  intro state fault addr hlazy hstate
  have hpost := hfault (addr := addr) hlazy hstate.1
  cases hrun : fault addr state.env with
  | ok found after =>
      rw [hrun] at hpost
      exact ⟨hpost, by simpa [lazyIngressPost] using hstate.2⟩
  | error err after =>
      rw [hrun] at hpost
      exact ⟨hpost, by simpa [lazyIngressPost] using hstate.2⟩

end LazyFaultPreserves

/-- Required constant lookup preserves the invariant through hits, lazy
ingress, retry, miss conversion, and hook errors. -/
theorem getConst_frame
    {I : TcState .anon → Prop} (hfault : LazyFaultPreserves I)
    (id : KId .anon) (state : TcState .anon) :
    WF I state (getConst id) (fun _ _ => True) := by
  unfold getConst
  apply WF.bind (tryGetConst_wf hfault id state)
  intro found nextState _
  cases found with
  | none => exact WF.throw fun _ => trivial
  | some _ => exact WF.pure fun _ => trivial

/-- Projection-head existence has the same lazy-ingress frame as optional
constant lookup. -/
theorem hasConst_frame
    {I : TcState .anon → Prop} (hfault : LazyFaultPreserves I)
    (id : KId .anon) (state : TcState .anon) :
    WF I state (hasConst id) (fun _ _ => True) := by
  unfold hasConst
  apply WF.bind (tryGetConst_wf hfault id state)
  intro _ _ _
  exact WF.pure fun _ => trivial

end TcM

namespace RecM

/-- Every expression-validator branch preserves the supplied invariant.
The only non-pure branches are required/optional constant lookups, both of
which are routed through the explicit lazy-fault contract. -/
theorem validateExprWellScoped_go_frame :
    ∀ (bound : Nat) (stack : List (KExpr .anon × UInt64))
      (seenExprs : Std.HashSet (Address × UInt64))
      (seenUnivs : Std.HashSet Address) (methods : Methods .anon)
      (I : TcState .anon → Prop),
    TcM.LazyFaultPreserves I →
    ∀ (state : TcState .anon),
    TcM.WF I state
      ((RecM.validateExprWellScoped.go bound stack seenExprs seenUnivs).run
        methods)
      (fun _ _ => True)
  | bound, [], seenExprs, seenUnivs, methods, I, hfault, state => by
      rw [RecM.validateExprWellScoped.go]
      exact TcM.WF.pure fun _ => trivial
  | bound, (expr, depth) :: stack, seenExprs, seenUnivs, methods, I,
      hfault, state => by
      rw [RecM.validateExprWellScoped.go]
      split
      · exact validateExprWellScoped_go_frame bound stack seenExprs seenUnivs
          methods I hfault state
      · cases expr with
        | var idx name info =>
            simp only [pure_bind]
            split
            · exact TcM.WF.throw fun _ => trivial
            · exact validateExprWellScoped_go_frame bound stack
                (seenExprs.insert ((KExpr.var idx name info).addr, depth))
                seenUnivs methods I hfault state
        | fvar id name info =>
            simp only [pure_bind]
            exact validateExprWellScoped_go_frame bound stack
              (seenExprs.insert ((KExpr.fvar id name info).addr, depth))
              seenUnivs methods I hfault state
        | sort level info =>
            simp only [pure_bind, ReaderT.run_bind]
            apply TcM.WF.bind
              (validateUnivParamsSeen_frame bound level seenUnivs methods I
                state)
            intro nextUnivs nextState _
            exact validateExprWellScoped_go_frame bound stack
              (seenExprs.insert ((KExpr.sort level info).addr, depth))
              nextUnivs methods I hfault nextState
        | const id levels info =>
            simp only [pure_bind, ReaderT.run_bind, ReaderT.run_monadLift]
            apply TcM.WF.bind (TcM.getConst_frame hfault id state)
            intro declaration lookupState _
            split
            · exact TcM.WF.throw fun _ => trivial
            · apply TcM.WF.bind
                (validateUnivRootsArray_frame bound levels seenUnivs methods I
                  lookupState)
              intro nextUnivs nextState _
              exact validateExprWellScoped_go_frame bound stack
                (seenExprs.insert
                  ((KExpr.const id levels info).addr, depth)) nextUnivs
                methods I hfault nextState
        | app fn arg info =>
            simp only [pure_bind]
            exact validateExprWellScoped_go_frame bound
              ((arg, depth) :: (fn, depth) :: stack)
              (seenExprs.insert ((KExpr.app fn arg info).addr, depth))
              seenUnivs methods I hfault state
        | lam name bi type body info =>
            simp only [pure_bind]
            exact validateExprWellScoped_go_frame bound
              ((body, depth + 1) :: (type, depth) :: stack)
              (seenExprs.insert
                ((KExpr.lam name bi type body info).addr, depth))
              seenUnivs methods I hfault state
        | all name bi type body info =>
            simp only [pure_bind]
            exact validateExprWellScoped_go_frame bound
              ((body, depth + 1) :: (type, depth) :: stack)
              (seenExprs.insert
                ((KExpr.all name bi type body info).addr, depth))
              seenUnivs methods I hfault state
        | letE name type value body nonDep info =>
            simp only [pure_bind]
            exact validateExprWellScoped_go_frame bound
              ((body, depth + 1) :: (value, depth) :: (type, depth) :: stack)
              (seenExprs.insert
                ((KExpr.letE name type value body nonDep info).addr, depth))
              seenUnivs methods I hfault state
        | prj id field value info =>
            simp only [pure_bind, ReaderT.run_bind, ReaderT.run_monadLift]
            apply TcM.WF.bind (TcM.hasConst_frame hfault id state)
            intro found nextState _
            cases found with
            | false => exact TcM.WF.throw fun _ => trivial
            | true =>
                exact validateExprWellScoped_go_frame bound
                  ((value, depth) :: stack)
                  (seenExprs.insert
                    ((KExpr.prj id field value info).addr, depth))
                  seenUnivs methods I hfault nextState
        | nat value blob info =>
            simp only [pure_bind]
            exact validateExprWellScoped_go_frame bound stack
              (seenExprs.insert ((KExpr.nat value blob info).addr, depth))
              seenUnivs methods I hfault state
        | str value blob info =>
            simp only [pure_bind]
            exact validateExprWellScoped_go_frame bound stack
              (seenExprs.insert ((KExpr.str value blob info).addr, depth))
              seenUnivs methods I hfault state
termination_by _ stack _ _ _ _ _ _ => RecM.scopedExprWorkSize stack
decreasing_by
  all_goals simp_all [RecM.scopedExprWorkSize, KExpr.treeSize]
  all_goals try omega

/-- Public expression-validator framing from the production empty memo sets. -/
theorem validateExprWellScoped_frame
    (root : KExpr .anon) (rootDepth : UInt64) (bound : Nat)
    (methods : Methods .anon) {I : TcState .anon → Prop}
    (hfault : TcM.LazyFaultPreserves I) (state : TcState .anon) :
    TcM.WF I state
      ((RecM.validateExprWellScoped root rootDepth bound).run methods)
      (fun _ _ => True) := by
  rw [RecM.validateExprWellScoped_equation]
  exact validateExprWellScoped_go_frame bound [(root, rootDepth)] {} {}
    methods I hfault state

/-- Standalone declaration validation preserves the checker invariant on
both outcomes.  The resource witness restricts this theorem to the axiom and
definition shapes owned by K3. -/
theorem validateConstWellScoped_frame
    {support : RunSupport} {c : KConst .anon}
    (hresources : StandaloneValidationResources support c)
    (methods : Methods .anon) {I : TcState .anon → Prop}
    (hfault : TcM.LazyFaultPreserves I) (state : TcState .anon) :
    TcM.WF I state ((RecM.validateConstWellScoped c).run methods)
      (fun _ _ => True) := by
  cases hresources with
  | @«axiom» name levelParams isUnsafe levels type _ _ =>
      unfold RecM.validateConstWellScoped
      simp only [ReaderT.run_bind, KConst.ty, KConst.lvls]
      apply TcM.WF.bind
        (validateExprWellScoped_frame type 0 levels.toNat methods hfault state)
      intro _ _ _
      exact TcM.WF.pure fun _ => trivial
  | @defn name levelParams kind safety hints levels type value leanAll block
      _ _ _ _ =>
      unfold RecM.validateConstWellScoped
      simp only [ReaderT.run_bind, KConst.ty, KConst.lvls]
      apply TcM.WF.bind
        (validateExprWellScoped_frame type 0 levels.toNat methods hfault state)
      intro _ afterType _
      exact validateExprWellScoped_frame value 0 levels.toNat methods hfault
        afterType

end RecM

end Ix.Tc
