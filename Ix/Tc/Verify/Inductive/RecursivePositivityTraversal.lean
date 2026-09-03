import Ix.Tc.Verify.Inductive.NestedPositivityTraversal

/-!
# Exhaustive recursive positivity traversal

This module closes the control-flow gap between production's field-domain
entry point and the direct/nested occurrence traces.  A successful run is
classified without a caller-supplied branch premise: root-free expressions
close immediately, foralls recurse after their negative-position guard, and a
terminal constant spine is either a validated active-family occurrence or a
fully expanded nested-family traversal.
-/

namespace Ix.Tc

/-- The WHNF branch discriminator used by positivity after the forall case
has been excluded. Naming it prevents indexed trace constructors from making
the premise depend on unrelated preceding proof terms. -/
def PositivityTerminalForm : KExpr m → Prop
  | .all .. => False
  | _ => True

/-- The two successful constant-headed terminal branches of production
positivity. -/
inductive PositiveApplicationTrace
    (fuel : Nat) (id : KId m) (us : Array (KUniv m))
    (args : Array (KExpr m)) (groups : Array (PositivityGroup m))
    (rootAddrs activeAddrs : Array Address) (methods : Methods m) :
    TcState m → TcState m → Prop
  | direct {initial final : TcState m}
      (active : rootAddrs.contains id.addr = true)
      (valid : ValidPositiveRecursiveApplication id us args groups
        rootAddrs methods initial final) :
      PositiveApplicationTrace fuel id us args groups rootAddrs activeAddrs
        methods initial final
  | nested {initial final : TcState m}
      (inactive : rootAddrs.contains id.addr = false)
      (trace : CompleteNestedPositivityApplicationTrace fuel id us args groups
        rootAddrs activeAddrs methods initial final) :
      PositiveApplicationTrace fuel id us args groups rootAddrs activeAddrs
        methods initial final

/-- Exhaustive successful execution tree for production field-domain
positivity.  The forall constructor recursively retains the same theorem at
strictly smaller fuel and records exact local-context restoration. -/
inductive PositivityDomainTrace
    (groups : Array (PositivityGroup m)) (activeAddrs : Array Address)
    (methods : Methods m) :
    Nat → KExpr m → TcState m → TcState m → Prop
  | rootFree {fuel : Nat} {dom : KExpr m} {rootGroup : PositivityGroup m}
      {state : TcState m}
      (root : groups[0]? = some rootGroup)
      (free : exprMentionsAnyAddr dom rootGroup.addrs = false) :
      PositivityDomainTrace groups activeAddrs methods (fuel + 1) dom state state
  | forall {fuel : Nat} {dom : KExpr m}
      {name : m.F Name} {bi : m.F Lean.BinderInfo}
      {innerDom innerBody innerOpen : KExpr m} {info : ExprInfo m}
      {fv : FVarId} {rootGroup : PositivityGroup m}
      {initial afterWhnf afterOpen afterRecursive final : TcState m}
      (root : groups[0]? = some rootGroup)
      (mentioned :
        exprMentionsAnyAddr dom rootGroup.addrs = true)
      (whnf : (RecM.whnf dom).run methods initial =
        .ok (.all name bi innerDom innerBody info) afterWhnf)
      (domainFree :
        exprMentionsAnyAddr innerDom rootGroup.addrs = false)
      (opening : TcM.openBinderAnon innerDom innerBody afterWhnf =
        .ok (innerOpen, fv) afterOpen)
      (tail : PositivityDomainTrace groups activeAddrs methods fuel innerOpen
        afterOpen afterRecursive)
      (restored : final = { afterRecursive with
        lctx := afterRecursive.lctx.truncate afterWhnf.lctx.size }) :
      PositivityDomainTrace groups activeAddrs methods (fuel + 1) dom initial
        final
  | application {fuel : Nat} {dom w : KExpr m}
      {id : KId m} {us : Array (KUniv m)} {info : ExprInfo m}
      {args : Array (KExpr m)} {rootGroup : PositivityGroup m}
      {initial afterWhnf final : TcState m}
      (root : groups[0]? = some rootGroup)
      (mentioned : exprMentionsAnyAddr dom rootGroup.addrs = true)
      (whnf : (RecM.whnf dom).run methods initial = .ok w afterWhnf)
      (notForall : PositivityTerminalForm w)
      (spine : w.collectSpine = (.const id us info, args))
      (terminal : PositiveApplicationTrace fuel id us args groups
        rootGroup.addrs activeAddrs methods afterWhnf final) :
      PositivityDomainTrace groups activeAddrs methods (fuel + 1) dom initial
        final

namespace RecM

/-- Successful terminal positivity is necessarily a constant-headed spine,
and production's active-address test exhaustively selects the direct or nested
trace. -/
private theorem positivityTerminal_success
    {fuel : Nat} {dom w : KExpr m}
    {groups : Array (PositivityGroup m)} {activeAddrs : Array Address}
    {methods : Methods m} {initial afterWhnf final : TcState m}
    {rootGroup : PositivityGroup m}
    (hroot : groups[0]? = some rootGroup)
    (hmentions : exprMentionsAnyAddr dom rootGroup.addrs = true)
    (hwhnf : (whnf dom).run methods initial = .ok w afterWhnf)
    (hnotForall : PositivityTerminalForm w)
    (hrun : (checkPositivityDomainFuel (fuel + 1) dom groups activeAddrs).run
      methods initial = .ok () final) :
    ∃ id us info args,
      w.collectSpine = (.const id us info, args) ∧
      PositiveApplicationTrace fuel id us args groups rootGroup.addrs
        activeAddrs methods afterWhnf final := by
  have hfull := hrun
  unfold checkPositivityDomainFuel at hrun
  simp only [hroot, hmentions, Bool.not_true, Bool.false_eq_true, if_false]
    at hrun
  rw [ReaderT.run_bind] at hrun
  change EStateM.bind ((whnf dom).run methods) _ initial = _ at hrun
  unfold EStateM.bind at hrun
  rw [hwhnf] at hrun
  cases w with
  | all => contradiction
  | var idx name exprInfo =>
      change EStateM.Result.error _ afterWhnf = .ok () final at hrun
      contradiction
  | fvar id name exprInfo =>
      change EStateM.Result.error _ afterWhnf = .ok () final at hrun
      contradiction
  | sort level exprInfo =>
      change EStateM.Result.error _ afterWhnf = .ok () final at hrun
      contradiction
  | const id us info =>
      simp only [KExpr.collectSpine, KExpr.collectSpine.go] at hrun
      cases hactive : rootGroup.addrs.contains id.addr with
      | true =>
          exact ⟨id, us, info, #[], rfl,
            .direct hactive
              (checkPositiveRecursiveApplication_valid
                (checkPositivityDomainFuel_direct hroot hmentions hwhnf rfl
                  hactive hfull))⟩
      | false =>
          exact ⟨id, us, info, #[], rfl,
            .nested hactive
              (checkNestedPositivityApplicationFuel_complete
                (checkPositivityDomainFuel_nested hroot hmentions hwhnf rfl
                  hactive hfull))⟩
  | app fn arg exprInfo =>
      rcases hspine : (.app fn arg exprInfo : KExpr m).collectSpine with
        ⟨head, args⟩
      simp only [hspine] at hrun
      cases head with
      | const id us info =>
          cases hactive : rootGroup.addrs.contains id.addr with
          | true =>
              exact ⟨id, us, info, args, rfl,
                .direct hactive
                  (checkPositiveRecursiveApplication_valid
                    (checkPositivityDomainFuel_direct hroot hmentions hwhnf
                      hspine hactive hfull))⟩
          | false =>
              exact ⟨id, us, info, args, rfl,
                .nested hactive
                  (checkNestedPositivityApplicationFuel_complete
                    (checkPositivityDomainFuel_nested hroot hmentions hwhnf
                      hspine hactive hfull))⟩
      | var | fvar | sort | app | lam | all | letE | prj | nat | str =>
          change EStateM.Result.error _ afterWhnf = .ok () final at hrun
          contradiction
  | lam name bi type body exprInfo =>
      change EStateM.Result.error _ afterWhnf = .ok () final at hrun
      contradiction
  | letE name type value body nonDep exprInfo =>
      change EStateM.Result.error _ afterWhnf = .ok () final at hrun
      contradiction
  | prj id field value exprInfo =>
      change EStateM.Result.error _ afterWhnf = .ok () final at hrun
      contradiction
  | nat value blob exprInfo =>
      change EStateM.Result.error _ afterWhnf = .ok () final at hrun
      contradiction
  | str value blob exprInfo =>
      change EStateM.Result.error _ afterWhnf = .ok () final at hrun
      contradiction

/-- Every successful production field-domain traversal yields the exhaustive
recursive execution tree above. -/
theorem checkPositivityDomainFuel_success
    (methods : Methods m) :
    ∀ {fuel : Nat} {dom : KExpr m}
        {groups : Array (PositivityGroup m)} {activeAddrs : Array Address}
        {initial final : TcState m},
      (checkPositivityDomainFuel fuel dom groups activeAddrs).run methods
          initial = .ok () final →
      PositivityDomainTrace groups activeAddrs methods fuel dom initial final
  | 0, dom, groups, activeAddrs, initial, final, hrun => by
      simp only [checkPositivityDomainFuel, throw, ReaderT.run] at hrun
      contradiction
  | fuel + 1, dom, groups, activeAddrs, initial, final, hrun => by
      generalize hroot : groups[0]? = root? at hrun
      cases root? with
      | none =>
          simp only [checkPositivityDomainFuel, hroot, throw, ReaderT.run] at hrun
          contradiction
      | some rootGroup =>
          cases hmentions : exprMentionsAnyAddr dom rootGroup.addrs with
          | false =>
              have hsame := checkPositivityDomainFuel_rootFree
                (fuel := fuel) (activeAddrs := activeAddrs)
                (methods := methods) (state := initial)
                hroot hmentions
              rw [hsame] at hrun
              cases hrun
              exact .rootFree hroot hmentions
          | true =>
              have hfull := hrun
              unfold checkPositivityDomainFuel at hrun
              simp only [hroot, hmentions, Bool.not_true, Bool.false_eq_true,
                if_false] at hrun
              rw [ReaderT.run_bind] at hrun
              change EStateM.bind ((whnf dom).run methods) _ initial = _ at hrun
              unfold EStateM.bind at hrun
              cases hwhnf : (whnf dom).run methods initial with
              | error err afterWhnf =>
                  rw [hwhnf] at hrun
                  contradiction
              | ok w afterWhnf =>
                  rw [hwhnf] at hrun
                  cases w with
                  | all name bi innerDom innerBody info =>
                      cases hnegative :
                          exprMentionsAnyAddr innerDom rootGroup.addrs with
                      | true =>
                          simp only [hnegative, if_true, throw, ReaderT.run] at hrun
                          contradiction
                      | false =>
                          rcases checkPositivityDomainFuel_forall_success hroot
                              hmentions hwhnf hnegative hfull with
                            ⟨innerOpen, fv, afterOpen, afterRecursive, hopen,
                              hrecursive, hrestored⟩
                          exact .forall hroot hmentions hwhnf hnegative hopen
                            (checkPositivityDomainFuel_success methods hrecursive)
                            hrestored
                  | var idx name info =>
                      rcases positivityTerminal_success hroot hmentions hwhnf
                          trivial hfull with
                        ⟨id, us, headInfo, args, hspine, hterminal⟩
                      exact .application hroot hmentions hwhnf trivial hspine
                        hterminal
                  | fvar id name info =>
                      rcases positivityTerminal_success hroot hmentions hwhnf
                          trivial hfull with
                        ⟨headId, us, headInfo, args, hspine, hterminal⟩
                      exact .application hroot hmentions hwhnf trivial hspine
                        hterminal
                  | sort level info =>
                      rcases positivityTerminal_success hroot hmentions hwhnf
                          trivial hfull with
                        ⟨id, us, headInfo, args, hspine, hterminal⟩
                      exact .application hroot hmentions hwhnf trivial hspine
                        hterminal
                  | const id us info =>
                      rcases positivityTerminal_success hroot hmentions hwhnf
                          trivial hfull with
                        ⟨headId, headUs, headInfo, args, hspine, hterminal⟩
                      exact .application hroot hmentions hwhnf trivial hspine
                        hterminal
                  | app fn arg info =>
                      rcases positivityTerminal_success hroot hmentions hwhnf
                          trivial hfull with
                        ⟨id, us, headInfo, args, hspine, hterminal⟩
                      exact .application hroot hmentions hwhnf trivial hspine
                        hterminal
                  | lam name bi type body info =>
                      rcases positivityTerminal_success hroot hmentions hwhnf
                          trivial hfull with
                        ⟨id, us, headInfo, args, hspine, hterminal⟩
                      exact .application hroot hmentions hwhnf trivial hspine
                        hterminal
                  | letE name type value body nonDep info =>
                      rcases positivityTerminal_success hroot hmentions hwhnf
                          trivial hfull with
                        ⟨id, us, headInfo, args, hspine, hterminal⟩
                      exact .application hroot hmentions hwhnf trivial hspine
                        hterminal
                  | prj id field value info =>
                      rcases positivityTerminal_success hroot hmentions hwhnf
                          trivial hfull with
                        ⟨headId, us, headInfo, args, hspine, hterminal⟩
                      exact .application hroot hmentions hwhnf trivial hspine
                        hterminal
                  | nat value blob info =>
                      rcases positivityTerminal_success hroot hmentions hwhnf
                          trivial hfull with
                        ⟨id, us, headInfo, args, hspine, hterminal⟩
                      exact .application hroot hmentions hwhnf trivial hspine
                        hterminal
                  | str value blob info =>
                      rcases positivityTerminal_success hroot hmentions hwhnf
                          trivial hfull with
                        ⟨id, us, headInfo, args, hspine, hterminal⟩
                      exact .application hroot hmentions hwhnf trivial hspine
                        hterminal

end RecM
end Ix.Tc
