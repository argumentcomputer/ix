import Ix.Tc.Verify.Infer.BinderScopes
import Ix.Tc.Verify.Infer.Callbacks
import Ix.Tc.Verify.Infer.SortTypes

/-!
# Structural definitional equality

The first recursive DefEq tier compares sorts and matching binders without
normalization.  Binder comparison uses one common freshly allocated fvar for
both bodies.  The second body starts in the second domain's Theory context,
so its proof must be transported into the first domain's context before the
recursive callback is invoked.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

/-- Finite resources needed to open both bodies of one quick binder
comparison with the common production fvar. -/
structure QuickBinderResources (support : RunSupport)
    (name : Mode.anon.F Name) (body1 body2 : KExpr .anon) : Prop where
  left : BinderOpeningResources support name body1
  right : BinderOpeningResources support name body2

/-- Constructor descent needed by `quickDefEq`.  The common fvar carries
the left binder's display name, so each supported body exposes opening
resources for that (anonymous-mode singleton) name rather than only for its
own enclosing node. -/
structure QuickDefEqResources (support : RunSupport) : Prop where
  lambda : ∀ {name bi ty body info},
    support (.lam name bi ty body info) →
      support ty ∧ ∀ commonName,
        BinderOpeningResources support commonName body
  forallE : ∀ {name bi ty body info},
    support (.all name bi ty body info) →
      support ty ∧ ∀ commonName,
        BinderOpeningResources support commonName body

namespace RecM

/-- Soundness of the common-fvar binder comparison.  A successful result
provides both the domain equality and the body equality in the first
domain's context; this is exactly the pair needed by lambda and Pi
congruence. -/
theorem quickBinder_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {name : Mode.anon.F Name} {bi : Mode.anon.F Lean.BinderInfo}
    {ty1 body1 ty2 body2 : KExpr .anon}
    {ty1V body1V ty2V body2V : VExpr}
    (theory : WhnfTheory trProj world uvars)
    (hcollision : support.CollisionFree)
    (hresources : QuickBinderResources support name body1 body2)
    (hty1Support : support ty1) (hty2Support : support ty2)
    (hty1Type : world.venv.IsType uvars Delta.toCtx ty1V)
    (hty1 : TrKExprS world.venv uvars world.nameOf trProj Delta ty1 ty1V)
    (hty2 : TrKExprS world.venv uvars world.nameOf trProj Delta ty2 ty2V)
    (hbody1 : TrKExprS world.venv uvars world.nameOf trProj
      ((none, .vlam ty1V) :: Delta) body1 body1V)
    (hbody2 : TrKExprS world.venv uvars world.nameOf trProj
      ((none, .vlam ty2V) :: Delta) body2 body2V) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (quickBinder name bi ty1 body1 ty2 body2)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx ty1V ty2V ∧
          world.venv.IsDefEqU uvars (ty1V :: Delta.toCtx) body1V body2V) := by
  unfold quickBinder
  apply RecM.WF.bind
    (RecM.isDefEqCall_wf hty1Support hty2Support hty1 hty2)
  intro domainsEqual afterDomains hdomains
  cases domainsEqual with
  | false =>
      simp only [Bool.not_false, if_true]
      exact RecM.WF.pure fun _ h => by contradiction
  | true =>
      simp only [Bool.not_true, Bool.false_eq_true, if_false]
      apply RecM.withLctxScope_openBinder_wf
        (layer := layer) (semantics := semantics) (trProj := trProj)
        (world := world) (uvars := uvars) (Delta := Delta)
        (s := afterDomains) (bi := bi)
        (k := fun body1Open fv => do
          let commonFVar ← TcM.intern (KExpr.mkFVar fv name)
          let body2Open ←
            TcM.runIntern (instantiateRev body2 #[commonFVar])
          isDefEqCall body1Open body2Open)
        (Qinner := fun answer _ => answer = true →
          world.venv.IsDefEqU uvars Delta.toCtx ty1V ty2V ∧
            world.venv.IsDefEqU uvars
              (ty1V :: Delta.toCtx) body1V body2V)
        (Qouter := fun answer _ => answer = true →
          world.venv.IsDefEqU uvars Delta.toCtx ty1V ty2V ∧
            world.venv.IsDefEqU uvars
              (ty1V :: Delta.toCtx) body1V body2V)
        hty1 hty1Type hbody1 hcollision hresources.left
      · intro body1Open fv afterOpen hfv hbody1OpenEq
          hbody1OpenSupport hbody1OpenTr
        subst fv
        let fresh : FVarId := ⟨afterDomains.env.nextFVarId⟩
        let common : KExpr .anon := .mkFVar fresh name
        apply RecM.WF.bind
          (RecM.WF.withInv <| RecM.WF.liftTcM <|
            TcM.intern_whnf_wf hcollision
              (hresources.left.fvarSupport fresh))
        intro commonFVar afterIntern hcommon
        rcases hcommon with ⟨hIIntern, hcommonEq, _⟩
        subst commonFVar
        have hrightBounds := hresources.right.instRevBounds fresh
        apply RecM.WF.bind
          (RecM.WF.withInv <| RecM.WF.liftTcM <|
            TcM.instRev_whnf_wf_of_resources hcollision hrightBounds
              (hresources.right.instRevSupport fresh))
        intro body2Open afterBody2 hbody2Post
        rcases hbody2Post with ⟨hIBody2, hbody2OpenEq, _⟩
        subst body2Open
        have hDelta : KVLCtx.WF world.venv uvars Delta :=
          hIBody2.2.1.wf.1
        have hfresh : fresh ∉ Delta.fvars := by
          exact (hIBody2.2.1.wf.2.1 fresh Delta.fvars rfl).1
        obtain ⟨level, hty1Sort⟩ := hty1Type
        have hdomainTyped : world.venv.IsDefEq uvars Delta.toCtx
            ty1V ty2V (.sort level) :=
          hdomains rfl |>.of_l world.venvWF hDelta.toCtx hty1Sort
        have hcontexts : KVLCtx.IsDefEq world.venv uvars
            ((some (fresh, Delta.fvars), .vlam ty1V) :: Delta)
            ((some (fresh, Delta.fvars), .vlam ty2V) :: Delta) :=
          .cons (KVLCtx.IsDefEq.refl world.venvWF.ordered hDelta)
            (by
              intro fv deps heq
              cases heq
              exact ⟨hfresh, fun _ h => h⟩)
            (.vlam hdomainTyped)
        have hbody2Raw := hbody2.openFVarZero
          (fv := fresh) (deps := Delta.fvars) (name := name)
          hfresh (by simpa using hrightBounds.2.2)
        obtain ⟨body2V', hbody2Retag⟩ := hbody2Raw.defeqDFC
          world.venvWF theory.literalWF theory.projections
          (hcontexts.symm world.venvWF.ordered)
        have hbody2Support : support
            (KExpr.instantiateRevSpec body2 #[common] 0) :=
          hresources.right.instRevSupport fresh _
            (KExpr.InstRevReach.spec ..)
        apply RecM.WF.mono
          (RecM.isDefEqCall_wf hbody1OpenSupport hbody2Support
            hbody1OpenTr (by simpa [common] using hbody2Retag))
        · intro answer final hanswer resultTrue
          have hbody2Bridge : world.venv.IsDefEqU uvars
              (ty1V :: Delta.toCtx) body2V' body2V := by
            simpa [KVLCtx.toCtx] using
              TrKExprS.uniq world.venvWF theory.literalWF
                theory.projections hcontexts hbody2Retag hbody2Raw
          exact ⟨hdomains rfl,
            (hanswer resultTrue).trans world.venvWF
              hcontexts.wf.toCtx hbody2Bridge⟩
        · intro _ _ _
          trivial
      · intro answer after hanswer
        exact hanswer

/-- Soundness of the complete Tier-1 structural probe.  Mismatched
constructors return `false`; the three accepting shapes are justified by
universe equality or the common-fvar binder theorem above. -/
theorem quickDefEq_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {a b : KExpr .anon} {aV bV : VExpr}
    (theory : WhnfTheory trProj world uvars)
    (hcollision : support.CollisionFree)
    (hsorts : SortComponentResources support)
    (hresources : QuickDefEqResources support)
    (haSupport : support a) (hbSupport : support b)
    (ha : TrKExprS world.venv uvars world.nameOf trProj Delta a aV)
    (hb : TrKExprS world.venv uvars world.nameOf trProj Delta b bV) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (quickDefEq a b)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx aV bV) := by
  cases ha <;> cases hb <;> simp only [quickDefEq]
  all_goals
    first
    | exact RecM.WF.pure fun _ h => by contradiction
    | skip
  · rename_i u info1 huWF v info2 hvWF
    obtain ⟨huSize, huSubterms⟩ := hsorts haSupport
    obtain ⟨hvSize, hvSubterms⟩ := hsorts hbSupport
    exact RecM.WF.pure fun _ heq =>
      ⟨_, .sortDF huWF hvWF <|
        univEq_sound
          (hcollision.univ.addrFaithful
            (huSubterms u .refl) (hvSubterms v .refl))
          huSize hvSize heq⟩
  · rename_i name1 bi1 ty1 body1 info1 ty1V body1V
      hty1Type hty1 hbody1 name2 bi2 ty2 body2 info2 ty2V body2V
      hty2Type hty2 hbody2
    obtain ⟨hty1Support, hbody1Resources⟩ :=
      hresources.lambda haSupport
    obtain ⟨hty2Support, hbody2Resources⟩ :=
      hresources.lambda hbSupport
    apply RecM.WF.mono
      (RecM.WF.withInv <| quickBinder_wf theory hcollision
        { left := hbody1Resources name1
          right := hbody2Resources name1 }
        hty1Support hty2Support hty1Type hty1 hty2 hbody1 hbody2)
    · intro answer final hpost hanswer
      rcases hpost with ⟨hI, hsemantic⟩
      rcases hsemantic hanswer with ⟨hdomainEq, hbodyEq⟩
      have hDelta : KVLCtx.WF world.venv uvars Delta := hI.2.1.wf
      obtain ⟨domainLevel, hty1Sort⟩ := hty1Type
      have hdomainTyped : world.venv.IsDefEq uvars Delta.toCtx
          ty1V ty2V (.sort domainLevel) :=
        hdomainEq.of_l world.venvWF hDelta.toCtx hty1Sort
      have hDeltaBody : KVLCtx.WF world.venv uvars
          ((none, .vlam ty1V) :: Delta) :=
        ⟨hDelta, nofun, ⟨domainLevel, hty1Sort⟩⟩
      obtain ⟨bodyTy, hbody1Typed⟩ := hbody1.wf
        world.venvWF.ordered theory.literalWF theory.projections.wf
          hDeltaBody
      have hbodyTyped : world.venv.IsDefEq uvars
          (ty1V :: Delta.toCtx) body1V body2V bodyTy :=
        hbodyEq.of_l world.venvWF hDeltaBody.toCtx (by
          simpa [KVLCtx.toCtx] using hbody1Typed)
      exact (Lean4Lean.VEnv.IsDefEq.lamDF
        hdomainTyped hbodyTyped).toU
    · intro _ _ _
      trivial
  · rename_i name1 bi1 ty1 body1 info1 ty1V body1V
      hty1Type hbody1Type hty1 hbody1 name2 bi2 ty2 body2 info2
      ty2V body2V hty2Type hbody2Type hty2 hbody2
    obtain ⟨hty1Support, hbody1Resources⟩ :=
      hresources.forallE haSupport
    obtain ⟨hty2Support, hbody2Resources⟩ :=
      hresources.forallE hbSupport
    apply RecM.WF.mono
      (RecM.WF.withInv <| quickBinder_wf theory hcollision
        { left := hbody1Resources name1
          right := hbody2Resources name1 }
        hty1Support hty2Support hty1Type hty1 hty2 hbody1 hbody2)
    · intro answer final hpost hanswer
      rcases hpost with ⟨hI, hsemantic⟩
      rcases hsemantic hanswer with ⟨hdomainEq, hbodyEq⟩
      have hDelta : KVLCtx.WF world.venv uvars Delta := hI.2.1.wf
      obtain ⟨domainLevel, hty1Sort⟩ := hty1Type
      have hdomainTyped : world.venv.IsDefEq uvars Delta.toCtx
          ty1V ty2V (.sort domainLevel) :=
        hdomainEq.of_l world.venvWF hDelta.toCtx hty1Sort
      have hDeltaBody : KVLCtx.WF world.venv uvars
          ((none, .vlam ty1V) :: Delta) :=
        ⟨hDelta, nofun, ⟨domainLevel, hty1Sort⟩⟩
      obtain ⟨bodyLevel, hbody1Sort⟩ := hbody1Type
      have hbodyTyped : world.venv.IsDefEq uvars
          (ty1V :: Delta.toCtx) body1V body2V (.sort bodyLevel) :=
        hbodyEq.of_l world.venvWF hDeltaBody.toCtx (by
          simpa [KVLCtx.toCtx] using hbody1Sort)
      exact (Lean4Lean.VEnv.IsDefEq.forallEDF
        hdomainTyped hbodyTyped).toU
    · intro _ _ _
      trivial

namespace DefEqAfterQuick

/-- Semantic contract for the production-owned tail after Tier 1 misses.
Later tier modules refine and discharge this boundary; keeping it generic in
the cache semantics lets the structural proof be reused at the final K2
stack. -/
def WF (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) : Prop :=
  ∀ {Delta s a b aV bV},
    support a → support b →
    TrKExprS world.venv uvars world.nameOf trProj Delta a aV →
    TrKExprS world.venv uvars world.nameOf trProj Delta b bV →
    RecM.WF layer semantics trProj world support uvars Delta s
      (isDefEqInnerAfterQuick a b)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx aV bV)

/-- Tier 1 plus a verified tail establishes the complete recursive-inner
contract.  This theorem follows the exact production seam: a successful
quick result exits immediately, while a miss delegates to the remaining
tiers in the quick comparison's post-state. -/
theorem closesInner
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (theory : WhnfTheory trProj world uvars)
    (hcollision : support.CollisionFree)
    (hsorts : SortComponentResources support)
    (hresources : QuickDefEqResources support)
    (htail : WF layer semantics trProj world support uvars) :
    ∀ {Delta s a b aV bV},
      support a → support b →
      TrKExprS world.venv uvars world.nameOf trProj Delta a aV →
      TrKExprS world.venv uvars world.nameOf trProj Delta b bV →
      RecM.WF layer semantics trProj world support uvars Delta s
        (isDefEqInner a b)
        (fun answer _ => answer = true →
          world.venv.IsDefEqU uvars Delta.toCtx aV bV) := by
  intro Delta s a b aV bV haSupport hbSupport ha hb
  unfold isDefEqInner
  apply RecM.WF.bind
    (quickDefEq_wf theory hcollision hsorts hresources
      haSupport hbSupport ha hb)
  intro quick afterQuick hquick
  cases quick with
  | false =>
      simp only [Bool.false_eq_true, if_false]
      exact htail haSupport hbSupport ha hb
  | true =>
      simp only [if_true]
      exact RecM.WF.pure fun _ _ => hquick rfl

end DefEqAfterQuick

end RecM

end Ix.Tc
