import Ix.Tc.Verify.Check.ValidatorFrame

/-!
# State framing for the unsafe-reference traversal

`checkNoUnsafeRefs` is semantically a safety guard.  For K3 its important
operational property is that the iterative expression walk changes checker
state only through optional constant lookup.  Consequently every outcome
preserves any invariant framed by the installed lazy-ingress hook.
-/

namespace Ix.Tc

namespace RecM

/-- The production safety worklist preserves an arbitrary lazy-ingress-framed
state invariant on both success and error. -/
theorem checkNoUnsafeRefs_go_frame :
    ∀ (callerSafety : Ix.DefinitionSafety)
      (stack : List (KExpr .anon))
      (seenExprs seenConsts : Std.HashSet Address)
      (methods : Methods .anon) (I : TcState .anon → Prop),
    TcM.LazyFaultPreserves I →
    ∀ (state : TcState .anon),
      TcM.WF I state
        ((RecM.checkNoUnsafeRefs.go callerSafety stack seenExprs seenConsts).run
          methods)
        (fun _ _ => True)
  | callerSafety, [], seenExprs, seenConsts, methods, I, hfault, state => by
      rw [RecM.checkNoUnsafeRefs.go]
      exact TcM.WF.pure fun _ => trivial
  | callerSafety, expr :: stack, seenExprs, seenConsts, methods, I, hfault,
      state => by
      rw [RecM.checkNoUnsafeRefs.go]
      split
      · simp only [bind_pure]
        exact checkNoUnsafeRefs_go_frame callerSafety stack seenExprs
          seenConsts methods I hfault state
      · cases expr with
        | var idx name info =>
            simp only [pure_bind]
            exact checkNoUnsafeRefs_go_frame callerSafety stack
              (seenExprs.insert (KExpr.var idx name info).addr) seenConsts
              methods I hfault state
        | fvar id name info =>
            simp only [pure_bind]
            exact checkNoUnsafeRefs_go_frame callerSafety stack
              (seenExprs.insert (KExpr.fvar id name info).addr) seenConsts
              methods I hfault state
        | sort level info =>
            simp only [pure_bind]
            exact checkNoUnsafeRefs_go_frame callerSafety stack
              (seenExprs.insert (KExpr.sort level info).addr) seenConsts
              methods I hfault state
        | nat value blob info =>
            simp only [pure_bind]
            exact checkNoUnsafeRefs_go_frame callerSafety stack
              (seenExprs.insert (KExpr.nat value blob info).addr) seenConsts
              methods I hfault state
        | str value blob info =>
            simp only [pure_bind]
            exact checkNoUnsafeRefs_go_frame callerSafety stack
              (seenExprs.insert (KExpr.str value blob info).addr) seenConsts
              methods I hfault state
        | const id levels info =>
            simp only [pure_bind]
            split
            · simp only [bind_pure]
              exact checkNoUnsafeRefs_go_frame callerSafety stack
                (seenExprs.insert (KExpr.const id levels info).addr)
                seenConsts methods I hfault state
            · simp only [ReaderT.run_bind, ReaderT.run_monadLift]
              apply TcM.WF.bind (TcM.tryGetConst_wf hfault id state)
              intro found lookupState _
              split
              · simp only [ReaderT.run_bind]
                exact TcM.WF.throw fun _ => trivial
              · simp only [ReaderT.run_bind]
                exact TcM.WF.throw fun _ => trivial
              · split
                · simp only [ReaderT.run_bind]
                  exact TcM.WF.throw fun _ => trivial
                · exact checkNoUnsafeRefs_go_frame callerSafety stack
                    (seenExprs.insert (KExpr.const id levels info).addr)
                    (seenConsts.insert id.addr) methods I hfault lookupState
              · simp only [ReaderT.run_bind]
                exact TcM.WF.throw fun _ => trivial
              · simp only [ReaderT.run_bind]
                exact TcM.WF.throw fun _ => trivial
              · simp only [ReaderT.run_bind]
                exact TcM.WF.throw fun _ => trivial
              · exact checkNoUnsafeRefs_go_frame callerSafety stack
                  (seenExprs.insert (KExpr.const id levels info).addr)
                  (seenConsts.insert id.addr) methods I hfault lookupState
        | app fn arg info =>
            simp only [pure_bind]
            exact checkNoUnsafeRefs_go_frame callerSafety
              (arg :: fn :: stack)
              (seenExprs.insert (KExpr.app fn arg info).addr) seenConsts
              methods I hfault state
        | lam name bi type body info =>
            simp only [pure_bind]
            exact checkNoUnsafeRefs_go_frame callerSafety
              (body :: type :: stack)
              (seenExprs.insert (KExpr.lam name bi type body info).addr)
              seenConsts methods I hfault state
        | all name bi type body info =>
            simp only [pure_bind]
            exact checkNoUnsafeRefs_go_frame callerSafety
              (body :: type :: stack)
              (seenExprs.insert (KExpr.all name bi type body info).addr)
              seenConsts methods I hfault state
        | letE name type value body nonDep info =>
            simp only [pure_bind]
            exact checkNoUnsafeRefs_go_frame callerSafety
              (body :: value :: type :: stack)
              (seenExprs.insert
                (KExpr.letE name type value body nonDep info).addr)
              seenConsts methods I hfault state
        | prj id field value info =>
            simp only [pure_bind]
            exact checkNoUnsafeRefs_go_frame callerSafety (value :: stack)
              (seenExprs.insert (KExpr.prj id field value info).addr)
              seenConsts methods I hfault state
termination_by _ stack _ _ _ _ _ _ => exprWorkSize stack
decreasing_by
  all_goals simp_all [exprWorkSize, KExpr.treeSize, KExpr.treeSize_pos]
  all_goals try omega

/-- Public safety-traversal frame in the exact shape used twice by the
definition branch of `checkConstMember`. -/
theorem checkNoUnsafeRefs_frame
    (root : KExpr .anon) (callerSafety : Ix.DefinitionSafety)
    (methods : Methods .anon) (I : TcState .anon → Prop)
    (hfault : TcM.LazyFaultPreserves I) (state : TcState .anon) :
    TcM.WF I state ((checkNoUnsafeRefs root callerSafety).run methods)
      (fun _ _ => True) := by
  rw [RecM.checkNoUnsafeRefs_equation]
  exact checkNoUnsafeRefs_go_frame callerSafety [root] {} {} methods I hfault
    state

end RecM

end Ix.Tc
