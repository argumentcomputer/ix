import Ix.Tc.Verify.Check.PreTranslation
import Ix.Tc.Verify.Subst

/-!
# Raw-declaration ingress into `PreTrKExprS`

`RawExprRel` deliberately records the direct syntax translation used before
checking.  In particular, it leaves de Bruijn variables in place and performs
the substitution for a `let` only when leaving the let body.  `PreTrKExprS`,
on the other hand, resolves every variable immediately through `KVLCtx`;
let-bound variables therefore translate directly to their values.

`RawCtxInterp` is the exact bridge between those two views.  Its substitution
maps the raw de Bruijn context to the Theory context represented by `KVLCtx`.
The main theorem below proves that raw translation plus the syntax-only
`KExpr.Scoped` result is sufficient to construct the untyped, well-scoped
translation required by full inference.  No typing judgment is assumed.
-/

namespace Lean4Lean.VExpr

private def Subst.comp (sigma tau : Subst) : Subst :=
  fun index => (sigma index).subst tau

private theorem Subst.comp_lift {sigma tau : Subst} :
    (Subst.comp sigma tau).lift = Subst.comp sigma.lift tau.lift := by
  funext index
  cases index with
  | zero => rfl
  | succ index =>
      simp only [Subst.comp, Subst.lift]
      rw [lift_eq_lift', lift_eq_lift', lift'_subst, subst_lift']
      congr 1
      funext inner
      simp [Subst.lift_r, Subst.lift_l, Lean4Lean.Lift.liftVar,
        Subst.lift, lift_eq_lift']

private theorem subst_subst {e : VExpr} {sigma tau : Subst} :
    (e.subst sigma).subst tau = e.subst (Subst.comp sigma tau) := by
  induction e generalizing sigma tau with
  | bvar => rfl
  | sort => rfl
  | const => rfl
  | app fn arg ihFn ihArg =>
      simp only [subst, ihFn, ihArg]
  | lam type body ihType ihBody =>
      simp only [subst, ihType, ihBody, Subst.comp_lift]
  | forallE type body ihType ihBody =>
      simp only [subst, ihType, ihBody, Subst.comp_lift]

private theorem lift_subst_cons {e : VExpr} {sigma : Subst} {value : VExpr} :
    e.lift.subst (sigma.cons value) = e.subst sigma := by
  rw [lift_eq_lift', subst_lift']
  have hs : Subst.lift_l (.skip .refl) (sigma.cons value) = sigma := by
    funext index
    rfl
  rw [hs]

/-- Substitution commutes with eliminating the head de Bruijn variable. -/
theorem inst_subst_cons (body value : VExpr) (sigma : Subst) :
    (body.inst value).subst sigma =
      body.subst (sigma.cons (value.subst sigma)) := by
  rw [inst_eq, subst_subst]
  congr 1
  funext index
  cases index with
  | zero => simp [Subst.comp, Subst.one, Subst.cons]
  | succ index =>
      simp only [Subst.comp, Subst.one, Subst.cons, Subst.id]
      simpa [VExpr.subst] using
        (lift_subst_cons (e := VExpr.bvar index)
          (sigma := sigma) (value := value.subst sigma))

end Lean4Lean.VExpr

namespace Ix.Tc

open Lean4Lean (VExpr VLocalDecl)

private theorem subst_natLit (value : Nat) (sigma : VExpr.Subst) :
    (VExpr.natLit value).subst sigma = VExpr.natLit value := by
  induction value with
  | zero => rfl
  | succ value ih =>
      simp [VExpr.natLit, VExpr.natSucc, VExpr.natZero, VExpr.subst, ih]

private theorem subst_listCharLit (value : List Char) (sigma : VExpr.Subst) :
    (VExpr.listCharLit value).subst sigma = VExpr.listCharLit value := by
  induction value with
  | nil => rfl
  | cons head tail ih =>
      simp [VExpr.listCharLit, VExpr.listCharNil, VExpr.listCharCons,
        VExpr.charOfNat, VExpr.char, VExpr.subst, subst_natLit, ih]

private theorem subst_trLiteral (literal : Lean.Literal)
    (sigma : VExpr.Subst) :
    (VExpr.trLiteral literal).subst sigma = VExpr.trLiteral literal := by
  cases literal with
  | natVal value => exact subst_natLit value sigma
  | strVal value =>
      simp [VExpr.trLiteral, VExpr.stringOfList, VExpr.subst,
        subst_listCharLit]

/-- Interpretation of the raw de Bruijn context in a translation-side
`KVLCtx`.  Lambda frames retain a Theory binder; let frames disappear from
`KVLCtx.toCtx` and extend the substitution with their value instead. -/
inductive RawCtxInterp : List VExpr -> KVLCtx -> VExpr.Subst -> Prop
  | nil : RawCtxInterp [] [] .id
  | lam {ctx : List VExpr} {Delta : KVLCtx} {sigma : VExpr.Subst}
      (h : RawCtxInterp ctx Delta sigma) (type : VExpr) :
    RawCtxInterp (type :: ctx)
      ((none, .vlam (type.subst sigma)) :: Delta) sigma.lift
  | letE {ctx : List VExpr} {Delta : KVLCtx} {sigma : VExpr.Subst}
      (h : RawCtxInterp ctx Delta sigma) (type value : VExpr) :
    RawCtxInterp (type :: ctx)
      ((none, .vlet (type.subst sigma) (value.subst sigma)) :: Delta)
      (sigma.cons (value.subst sigma))

namespace RawCtxInterp

/-- Every in-range raw de Bruijn variable resolves to the value selected by
the interpretation substitution. -/
theorem find?_inl
    {ctx : List VExpr} {Delta : KVLCtx} {sigma : VExpr.Subst}
    (h : RawCtxInterp ctx Delta sigma) {index : Nat}
    (hindex : index < ctx.length) :
    exists type, Delta.find? (.inl index) = some (sigma index, type) := by
  induction h generalizing index with
  | nil => simp at hindex
  | @lam ctx Delta sigma h type ih =>
      cases index with
      | zero =>
          refine ⟨(type.subst sigma).lift, ?_⟩
          simp [KVLCtx.find?, KVLCtx.next, VExpr.Subst.lift,
            VLocalDecl.value, VLocalDecl.type]
      | succ index =>
          obtain ⟨resultType, hfind⟩ := ih (by simpa using hindex)
          refine ⟨resultType.lift, ?_⟩
          simp only [KVLCtx.find?, KVLCtx.next, Option.bind_eq_bind, hfind,
            Option.bind_some, VExpr.Subst.lift]
          rfl
  | @letE ctx Delta sigma h type value ih =>
      cases index with
      | zero =>
          refine ⟨type.subst sigma, ?_⟩
          simp [KVLCtx.find?, KVLCtx.next, VExpr.Subst.cons,
            VLocalDecl.value, VLocalDecl.type]
      | succ index =>
          obtain ⟨resultType, hfind⟩ := ih (by simpa using hindex)
          refine ⟨resultType, ?_⟩
          simpa [KVLCtx.find?, KVLCtx.next, VExpr.Subst.cons,
            VLocalDecl.depth, VExpr.liftN_zero] using hfind

@[simp] theorem bvars_eq
    {ctx : List VExpr} {Delta : KVLCtx} {sigma : VExpr.Subst}
    (h : RawCtxInterp ctx Delta sigma) : Delta.bvars = ctx.length := by
  induction h <;> simp [KVLCtx.bvars, *]

end RawCtxInterp

namespace RawProjRel

/-- The substitution law needed to move a raw projection witness from the
raw binder/let context to the `KVLCtx` Theory context.  It is explicit because
`RawProjRel` is abstract; closure, typing, or uniqueness alone cannot imply
this representation law. -/
def SubstCompatible (trProj : RawProjRel) : Prop :=
  forall {ctx : List VExpr} {Delta : KVLCtx} {sigma : VExpr.Subst}
      {name : Lean.Name} {field : Nat} {value result : VExpr},
    RawCtxInterp ctx Delta sigma ->
    trProj ctx name field value result ->
    trProj Delta.toCtx name field (value.subst sigma) (result.subst sigma)

theorem none_substCompatible : SubstCompatible RawProjRel.none := by
  intro ctx Delta sigma name field value result hctx hprojection
  exact False.elim hprojection

end RawProjRel

/-- The declaration syntax for which raw ingress needs neither literal
availability nor a projection interpretation.  It is the closed binder core
used by generated recursor types and equations. -/
def KExpr.binderCore : KExpr .anon → Bool
  | .var .. | .sort .. | .const .. => true
  | .app fn argument _ => fn.binderCore && argument.binderCore
  | .lam _ _ type body _ | .all _ _ type body _ =>
      type.binderCore && body.binderCore
  | _ => false

namespace RawExprRel

/-- General substitution-aware ingress theorem.  The size bound rules out
`UInt64` wraparound when the validator descends through a binder. -/
theorem toPre_of_scoped_aux
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address -> Option Lean.Name} {trProj : RawProjRel}
    (hprojection : trProj.SubstCompatible)
    (hliterals : forall literal, env.ContainsLits literal)
    {ctx : List VExpr} {Delta : KVLCtx} {sigma : VExpr.Subst}
    {depth : UInt64} {source : KExpr .anon} {sourceV : VExpr}
    (hraw : RawExprRel env nameOf trProj ctx source sourceV)
    (hctx : RawCtxInterp ctx Delta sigma)
    (hdepth : depth.toNat = ctx.length)
    (hscoped : source.Scoped depth uvars)
    (hbound : depth.toNat + source.size < UInt64.size) :
    PreTrKExprS env uvars nameOf trProj Delta source
      (sourceV.subst sigma) := by
  induction hraw generalizing Delta sigma depth with
  | var =>
      obtain ⟨type, hfind⟩ := hctx.find?_inl (by
        rw [← hdepth]
        exact UInt64.lt_iff_toNat_lt.mp hscoped)
      exact .var hfind
  | sort =>
      exact .sort (KUniv.Scoped.toVLevel_wf hscoped)
  | const hname hlookup harity =>
      exact .const hname hlookup
        (fun level hlevel =>
          KUniv.Scoped.toVLevel_wf (hscoped level hlevel)) harity
  | app hrawFn hrawArg ihFn ihArg =>
      exact .app
        (ihFn hctx hdepth hscoped.1 (by
          change depth.toNat + (_ + _ + 1) < UInt64.size at hbound
          omega))
        (ihArg hctx hdepth hscoped.2 (by
          change depth.toNat + (_ + _ + 1) < UInt64.size at hbound
          omega))
  | @lam ctx name bi type body info typeV bodyV hrawType hrawBody ihType ihBody =>
      have hfull : depth.toNat + (type.size + body.size + 1) < UInt64.size :=
        by simpa [KExpr.size] using hbound
      have hnext : (depth + 1).toNat = depth.toNat + 1 := by
        rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
        exact Nat.mod_eq_of_lt <| Nat.lt_of_le_of_lt
          (Nat.add_le_add_left (by omega : 1 <= type.size + body.size + 1) _)
          hfull
      have htype := ihType hctx hdepth hscoped.1 (by omega)
      have hbody := ihBody (hctx.lam typeV)
        (by simp [hnext, hdepth]) hscoped.2 (by rw [hnext]; omega)
      simpa [VExpr.subst] using
        (PreTrKExprS.lam htype hbody)
  | @all ctx name bi type body info typeV bodyV hrawType hrawBody ihType ihBody =>
      have hfull : depth.toNat + (type.size + body.size + 1) < UInt64.size :=
        by simpa [KExpr.size] using hbound
      have hnext : (depth + 1).toNat = depth.toNat + 1 := by
        rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
        exact Nat.mod_eq_of_lt <| Nat.lt_of_le_of_lt
          (Nat.add_le_add_left (by omega : 1 <= type.size + body.size + 1) _)
          hfull
      have htype := ihType hctx hdepth hscoped.1 (by omega)
      have hbody := ihBody (hctx.lam typeV)
        (by simp [hnext, hdepth]) hscoped.2 (by rw [hnext]; omega)
      simpa [VExpr.subst] using
        (PreTrKExprS.all htype hbody)
  | @letE ctx name type value body nonDep info typeV valueV bodyV
      hrawType hrawValue hrawBody ihType ihValue ihBody =>
      have hfull :
          depth.toNat + (type.size + value.size + body.size + 1) <
            UInt64.size := by simpa [KExpr.size] using hbound
      have hnext : (depth + 1).toNat = depth.toNat + 1 := by
        rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
        exact Nat.mod_eq_of_lt <| Nat.lt_of_le_of_lt
          (Nat.add_le_add_left
            (by omega : 1 <= type.size + value.size + body.size + 1) _)
          hfull
      have htype := ihType hctx hdepth hscoped.1 (by omega)
      have hvalue := ihValue hctx hdepth hscoped.2.1 (by omega)
      have hbody := ihBody (hctx.letE typeV valueV)
        (by simp [hnext, hdepth]) hscoped.2.2 (by rw [hnext]; omega)
      rw [VExpr.inst_subst_cons]
      exact .letE htype hvalue hbody
  | @prj ctx id field value info name ci valueV resultV
      hname hlookup hrawValue hrawProjection ihValue =>
      have hvalue := ihValue hctx hdepth hscoped (by
        change depth.toNat + (value.size + 1) < UInt64.size at hbound
        omega)
      exact .prj hname hvalue (hprojection hctx hrawProjection)
  | nat => simpa [subst_natLit] using (PreTrKExprS.nat (hliterals _))
  | str => simpa [subst_trLiteral] using (PreTrKExprS.str (hliterals _))

/-- Closed declaration ingress: successful scoping turns the exact raw
Theory term into the `PreTrKExprS` witness consumed by full inference. -/
theorem toPre_of_scoped
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address -> Option Lean.Name} {trProj : RawProjRel}
    (hprojection : trProj.SubstCompatible)
    (hliterals : forall literal, env.ContainsLits literal)
    {source : KExpr .anon} {sourceV : VExpr}
    (hraw : RawExprRel env nameOf trProj [] source sourceV)
    (hscoped : source.Scoped 0 uvars)
    (hbound : source.size < UInt64.size) :
    PreTrKExprS env uvars nameOf trProj [] source sourceV := by
  simpa using hraw.toPre_of_scoped_aux hprojection hliterals
    RawCtxInterp.nil rfl hscoped (by simpa using hbound)

/-- Binder-core counterpart of `toPre_of_scoped_aux`.  Excluding literals,
lets, and projections makes their ambient semantic hypotheses unnecessary;
all remaining premises are syntax-only scoping and exact raw translation. -/
theorem toPreBinderCore_of_scoped_aux
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address -> Option Lean.Name} {trProj : RawProjRel}
    {ctx : List VExpr} {Delta : KVLCtx} {sigma : VExpr.Subst}
    {depth : UInt64} {source : KExpr .anon} {sourceV : VExpr}
    (hraw : RawExprRel env nameOf trProj ctx source sourceV)
    (hcore : source.binderCore = true)
    (hctx : RawCtxInterp ctx Delta sigma)
    (hdepth : depth.toNat = ctx.length)
    (hscoped : source.Scoped depth uvars)
    (hbound : depth.toNat + source.size < UInt64.size) :
    PreTrKExprS env uvars nameOf trProj Delta source
      (sourceV.subst sigma) := by
  induction hraw generalizing Delta sigma depth with
  | var =>
      obtain ⟨type, hfind⟩ := hctx.find?_inl (by
        rw [← hdepth]
        exact UInt64.lt_iff_toNat_lt.mp hscoped)
      exact .var hfind
  | sort =>
      exact .sort (KUniv.Scoped.toVLevel_wf hscoped)
  | const hname hlookup harity =>
      exact .const hname hlookup
        (fun level hlevel =>
          KUniv.Scoped.toVLevel_wf (hscoped level hlevel)) harity
  | app hrawFn hrawArg ihFn ihArg =>
      simp only [KExpr.binderCore, Bool.and_eq_true] at hcore
      exact .app
        (ihFn hcore.1 hctx hdepth hscoped.1 (by
          change depth.toNat + (_ + _ + 1) < UInt64.size at hbound
          omega))
        (ihArg hcore.2 hctx hdepth hscoped.2 (by
          change depth.toNat + (_ + _ + 1) < UInt64.size at hbound
          omega))
  | @lam ctx name bi type body info typeV bodyV hrawType hrawBody ihType ihBody =>
      simp only [KExpr.binderCore, Bool.and_eq_true] at hcore
      have hfull : depth.toNat + (type.size + body.size + 1) < UInt64.size :=
        by simpa [KExpr.size] using hbound
      have hnext : (depth + 1).toNat = depth.toNat + 1 := by
        rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
        exact Nat.mod_eq_of_lt <| Nat.lt_of_le_of_lt
          (Nat.add_le_add_left (by omega : 1 <= type.size + body.size + 1) _)
          hfull
      have htype := ihType hcore.1 hctx hdepth hscoped.1 (by omega)
      have hbody := ihBody hcore.2 (hctx.lam typeV)
        (by simp [hnext, hdepth]) hscoped.2 (by rw [hnext]; omega)
      simpa [VExpr.subst] using
        (PreTrKExprS.lam htype hbody)
  | @all ctx name bi type body info typeV bodyV hrawType hrawBody ihType ihBody =>
      simp only [KExpr.binderCore, Bool.and_eq_true] at hcore
      have hfull : depth.toNat + (type.size + body.size + 1) < UInt64.size :=
        by simpa [KExpr.size] using hbound
      have hnext : (depth + 1).toNat = depth.toNat + 1 := by
        rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
        exact Nat.mod_eq_of_lt <| Nat.lt_of_le_of_lt
          (Nat.add_le_add_left (by omega : 1 <= type.size + body.size + 1) _)
          hfull
      have htype := ihType hcore.1 hctx hdepth hscoped.1 (by omega)
      have hbody := ihBody hcore.2 (hctx.lam typeV)
        (by simp [hnext, hdepth]) hscoped.2 (by rw [hnext]; omega)
      simpa [VExpr.subst] using
        (PreTrKExprS.all htype hbody)
  | letE => simp [KExpr.binderCore] at hcore
  | prj => simp [KExpr.binderCore] at hcore
  | nat => simp [KExpr.binderCore] at hcore
  | str => simp [KExpr.binderCore] at hcore

/-- Closed binder-core declarations enter `PreTrKExprS` without requiring an
irrelevant primitive-literal environment. -/
theorem toPreBinderCore_of_scoped
    {env : Lean4Lean.VEnv} {uvars : Nat}
    {nameOf : Address -> Option Lean.Name} {trProj : RawProjRel}
    {source : KExpr .anon} {sourceV : VExpr}
    (hraw : RawExprRel env nameOf trProj [] source sourceV)
    (hcore : source.binderCore = true)
    (hscoped : source.Scoped 0 uvars)
    (hbound : source.size < UInt64.size) :
    PreTrKExprS env uvars nameOf trProj [] source sourceV := by
  simpa using hraw.toPreBinderCore_of_scoped_aux hcore RawCtxInterp.nil rfl
    hscoped (by simpa using hbound)

end RawExprRel

end Ix.Tc
