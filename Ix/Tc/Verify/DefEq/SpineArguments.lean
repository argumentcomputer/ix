import Ix.Tc.Verify.DefEq.EqualRankReduction

/-!
# Recursive application-spine arguments

Same-head delta comparison and the later general application comparison use
one left-to-right recursive DefEq loop.  This module proves that loop once
and gives its positive result a compositional Theory meaning.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

namespace RecM

/-- A raw argument pair has supported translations in the current context. -/
def SpineArgInput (trProj : RawProjRel) (world : VerifyWorld)
    (support : RunSupport) (uvars : Nat) (Delta : KVLCtx)
    (left right : KExpr .anon) : Prop :=
  support left ∧ support right ∧
    ∃ leftV rightV,
      TrKExprS world.venv uvars world.nameOf trProj Delta left leftV ∧
      TrKExprS world.venv uvars world.nameOf trProj Delta right rightV

/-- Semantic witness retained for every argument pair after the loop
accepts. -/
def SpineArgDefEq (trProj : RawProjRel) (world : VerifyWorld)
    (uvars : Nat) (Delta : KVLCtx) (left right : KExpr .anon) : Prop :=
  ∃ leftV rightV,
    TrKExprS world.venv uvars world.nameOf trProj Delta left leftV ∧
    TrKExprS world.venv uvars world.nameOf trProj Delta right rightV ∧
    world.venv.IsDefEqU uvars Delta.toCtx leftV rightV

/-- Exact recursive-list loop: invariant preservation and a semantic witness
for every pair when the complete loop returns `true`. -/
theorem allDefEqSpineArgsList_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx}
    (pairs : List (KExpr .anon × KExpr .anon))
    (hinputs : ∀ pair, pair ∈ pairs →
      SpineArgInput trProj world support uvars Delta pair.1 pair.2) :
    ∀ state,
      RecM.WF layer semantics trProj world support uvars Delta state
        (allDefEqSpineArgsList pairs)
        (fun answer _ => answer = true →
          ∀ pair, pair ∈ pairs →
            SpineArgDefEq trProj world uvars Delta pair.1 pair.2) := by
  induction pairs with
  | nil =>
      intro state
      exact RecM.WF.pure fun _ _ pair hmem => by simp at hmem
  | cons pair rest ih =>
      intro state
      rcases pair with ⟨left, right⟩
      obtain ⟨hleftSupport, hrightSupport, leftV, rightV, hleft, hright⟩ :=
        hinputs (left, right) (by simp)
      unfold allDefEqSpineArgsList
      apply RecM.WF.bind
        (RecM.isDefEqCall_wf hleftSupport hrightSupport hleft hright)
      intro answer after hanswer
      cases answer with
      | false =>
          simp only [Bool.not_false, if_true]
          exact RecM.WF.pure fun _ htrue => by contradiction
      | true =>
          simp only [Bool.not_true, Bool.false_eq_true, if_false]
          apply RecM.WF.mono
            (ih (fun tail hmem => hinputs tail (by simp [hmem])) after)
          · intro result final htail hresult candidate hmem
            simp only [List.mem_cons] at hmem
            rcases hmem with rfl | hmem
            · exact ⟨leftV, rightV, hleft, hright, hanswer rfl⟩
            · exact htail hresult candidate hmem
          · intro _ _ _
            trivial

/-- Array wrapper used by both production spine comparators. -/
theorem allDefEqSpineArgs_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    (pairs : Array (KExpr .anon × KExpr .anon))
    (hinputs : ∀ pair, pair ∈ pairs.toList →
      SpineArgInput trProj world support uvars Delta pair.1 pair.2) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (allDefEqSpineArgs pairs)
      (fun answer _ => answer = true →
        ∀ pair, pair ∈ pairs.toList →
          SpineArgDefEq trProj world uvars Delta pair.1 pair.2) := by
  unfold allDefEqSpineArgs
  exact allDefEqSpineArgsList_wf pairs.toList hinputs state

/-- Membership in a zipped list exposes membership of its left component. -/
theorem left_mem_of_pair_mem_zip
    {left right : List α} {a b : α} (h : (a, b) ∈ left.zip right) :
    a ∈ left := by
  induction left generalizing right with
  | nil => simp at h
  | cons x xs ih =>
      cases right with
      | nil => simp at h
      | cons y ys =>
          simp only [List.zip_cons_cons, List.mem_cons] at h ⊢
          rcases h with h | h
          · exact Or.inl (congrArg Prod.fst h)
          · exact Or.inr (ih h)

/-- Membership in a zipped list exposes membership of its right component. -/
theorem right_mem_of_pair_mem_zip
    {left right : List α} {a b : α} (h : (a, b) ∈ left.zip right) :
    b ∈ right := by
  induction left generalizing right with
  | nil => simp at h
  | cons x xs ih =>
      cases right with
      | nil => simp at h
      | cons y ys =>
          simp only [List.zip_cons_cons, List.mem_cons] at h ⊢
          rcases h with h | h
          · exact Or.inl (congrArg Prod.snd h)
          · exact Or.inr (ih h)

namespace TrAppSpine

/-- Lift a positive semantic argument witness to any two translations of the
same raw pair. -/
theorem argumentDefEq
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {left right : KExpr .anon}
    (theory : WhnfTheory trProj world uvars)
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    (h : SpineArgDefEq trProj world uvars Delta left right)
    {leftV rightV : VExpr}
    (hleft : TrKExprS world.venv uvars world.nameOf trProj Delta left leftV)
    (hright : TrKExprS world.venv uvars world.nameOf trProj Delta right
      rightV) :
    world.venv.IsDefEqU uvars Delta.toCtx leftV rightV := by
  obtain ⟨witnessLeft, witnessRight, hwitnessLeft, hwitnessRight,
    hwitness⟩ := h
  have hctx := KVLCtx.IsDefEq.refl world.venvWF.ordered hDelta
  have hleftBridge := hleft.uniq world.venvWF theory.literalWF
    theory.projections hctx hwitnessLeft
  have hrightBridge := hwitnessRight.uniq world.venvWF theory.literalWF
    theory.projections hctx hright
  exact hleftBridge.trans world.venvWF hDelta.toCtx <|
    hwitness.trans world.venvWF hDelta.toCtx hrightBridge

/-- Pointwise equality of two equally long raw spines lifts a semantic
equality of their heads to semantic equality of the complete applications. -/
theorem defEq_of_zip
    {trProj : RawProjRel} {world : VerifyWorld} {uvars : Nat}
    {Delta : KVLCtx} {leftHead rightHead : KExpr .anon}
    {leftArgs rightArgs : List (KExpr .anon)} {leftV rightV : VExpr}
    (theory : WhnfTheory trProj world uvars)
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    (hleft : TrAppSpine world.venv uvars world.nameOf trProj Delta
      leftHead leftArgs leftV)
    (hright : TrAppSpine world.venv uvars world.nameOf trProj Delta
      rightHead rightArgs rightV)
    (hlength : leftArgs.length = rightArgs.length)
    (hhead : ∀ {leftHeadV rightHeadV},
      TrKExprS world.venv uvars world.nameOf trProj Delta leftHead
          leftHeadV →
      TrKExprS world.venv uvars world.nameOf trProj Delta rightHead
          rightHeadV →
      world.venv.IsDefEqU uvars Delta.toCtx leftHeadV rightHeadV)
    (hargs : ∀ pair, pair ∈ leftArgs.zip rightArgs →
      SpineArgDefEq trProj world uvars Delta pair.1 pair.2) :
    world.venv.IsDefEqU uvars Delta.toCtx leftV rightV := by
  induction hleft generalizing rightArgs rightV with
  | head hleftHead =>
      cases hright with
      | head hrightHead => exact hhead hleftHead hrightHead
      | app hprefix hfun harg hargTr => simp at hlength
  | @app leftPrefix leftCurrent leftArg leftArgV A B hleftPrefix
      hleftFun hleftArg hleftArgTr ih =>
      cases hright with
      | head hrightHead => simp at hlength
      | @app rightPrefix rightCurrent rightArg rightArgV A' B'
          hrightPrefix hrightFun hrightArg hrightArgTr =>
          have hprefixLength : leftPrefix.length = rightPrefix.length := by
            simpa only [List.length_append, List.length_singleton,
              Nat.add_right_cancel_iff] using hlength
          have hzip :
              (leftPrefix ++ [leftArg]).zip
                  (rightPrefix ++ [rightArg]) =
                leftPrefix.zip rightPrefix ++ [(leftArg, rightArg)] := by
            simpa using List.zip_append hprefixLength
          have hprefixArgs : ∀ pair,
              pair ∈ leftPrefix.zip rightPrefix →
                SpineArgDefEq trProj world uvars Delta pair.1 pair.2 := by
            intro pair hmem
            exact hargs pair (by rw [hzip]; simp [hmem])
          have hcurrent := ih hrightPrefix hprefixLength hprefixArgs
          have hcurrentTyped :=
            hcurrent.of_l world.venvWF hDelta.toCtx hleftFun
          have hlast : SpineArgDefEq trProj world uvars Delta
              leftArg rightArg :=
            hargs (leftArg, rightArg) (by rw [hzip]; simp)
          have hlastEq := argumentDefEq theory hDelta hlast
            hleftArgTr hrightArgTr
          have hlastTyped :=
            hlastEq.of_l world.venvWF hDelta.toCtx hleftArg
          exact ⟨_, Lean4Lean.VEnv.IsDefEq.appDF hcurrentTyped hlastTyped⟩

end TrAppSpine

end RecM

end Ix.Tc
