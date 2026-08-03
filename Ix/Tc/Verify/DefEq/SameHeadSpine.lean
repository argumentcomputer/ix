import Ix.Tc.Verify.DefEq.SpineArguments

/-!
# Same-head constant spines

This module closes the substantive accepting branch of equal-rank lazy
delta.  Equal constant instances are justified by collision-safe universe
comparison, and successful recursive comparisons of every raw argument are
lifted through the complete typed application spine.
-/

namespace Ix.Tc

open Lean4Lean (VExpr VLevel)

/-- Finite support coverage needed by constant-headed spine comparison. -/
structure SameHeadSpineResources (support : RunSupport) : Prop where
  arguments : ∀ {source head : KExpr .anon}
      {args : Array (KExpr .anon)},
    support source → source.collectSpine = (head, args) →
      ∀ arg, arg ∈ args.toList → support arg
  universes : ∀ {source : KExpr .anon} {id : KId .anon}
      {levels : Array (KUniv .anon)} {info : ExprInfo .anon}
      {args : Array (KExpr .anon)},
    support source →
      source.collectSpine = (.const id levels info, args) →
      ∀ level, level ∈ levels.toList →
        support.univ level ∧ level.size < UInt64.size

namespace RecM

/-- Every accepted pair in the pure universe loop denotes equivalent Theory
levels. -/
theorem allDefEqUniversesList_sound
    {support : RunSupport} (hcollision : support.CollisionFree)
    (pairs : List (KUniv .anon × KUniv .anon))
    (hinputs : ∀ pair, pair ∈ pairs →
      support.univ pair.1 ∧ pair.1.size < UInt64.size ∧
      support.univ pair.2 ∧ pair.2.size < UInt64.size)
    (hresult : allDefEqUniversesList pairs = true) :
    ∀ pair, pair ∈ pairs → pair.1.toVLevel ≈ pair.2.toVLevel := by
  induction pairs with
  | nil =>
      intro pair hmem
      simp at hmem
  | cons pair rest ih =>
      rcases pair with ⟨left, right⟩
      simp only [allDefEqUniversesList, Bool.and_eq_true] at hresult
      intro candidate hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · obtain ⟨hleftSupport, hleftSize, hrightSupport, hrightSize⟩ :=
          hinputs (left, right) (by simp)
        exact univEq_sound
          (hcollision.univ.addrFaithful hleftSupport hrightSupport)
          hleftSize hrightSize hresult.1
      · exact ih
          (fun tail htail => hinputs tail (by simp [htail]))
          hresult.2 candidate hmem

/-- The complete constant-instance gate exposes equal arity and pairwise
semantic universe equality. -/
theorem sameDefEqUniverses_sound
    {support : RunSupport} (hcollision : support.CollisionFree)
    {left right : Array (KUniv .anon)}
    (hleft : ∀ level, level ∈ left.toList →
      support.univ level ∧ level.size < UInt64.size)
    (hright : ∀ level, level ∈ right.toList →
      support.univ level ∧ level.size < UInt64.size)
    (hresult : sameDefEqUniverses left right = true) :
    left.toList.length = right.toList.length ∧
      ∀ pair, pair ∈ left.toList.zip right.toList →
        pair.1.toVLevel ≈ pair.2.toVLevel := by
  rw [sameDefEqUniverses, Bool.and_eq_true] at hresult
  have hlength : left.toList.length = right.toList.length := by
    simpa only [Array.length_toList] using eq_of_beq hresult.1
  refine ⟨hlength, ?_⟩
  have hloop : allDefEqUniversesList (left.toList.zip right.toList) = true := by
    simpa only [Array.toList_zip] using hresult.2
  apply allDefEqUniversesList_sound hcollision _ _ hloop
  intro pair hmem
  obtain ⟨hleftSupport, hleftSize⟩ :=
    hleft pair.1 (left_mem_of_pair_mem_zip hmem)
  obtain ⟨hrightSupport, hrightSize⟩ :=
    hright pair.2 (right_mem_of_pair_mem_zip hmem)
  exact ⟨hleftSupport, hleftSize, hrightSupport, hrightSize⟩

private theorem forall₂_map_of_zip
    {left right : List α} {f : α → β} {g : α → γ}
    {R : β → γ → Prop}
    (hlength : left.length = right.length)
    (hrel : ∀ pair, pair ∈ left.zip right → R (f pair.1) (g pair.2)) :
    List.Forall₂ R (left.map f) (right.map g) := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => exact .nil
      | cons y ys => simp at hlength
  | cons x xs ih =>
      cases right with
      | nil => simp at hlength
      | cons y ys =>
          have htailLength : xs.length = ys.length := by
            simp only [List.length_cons] at hlength
            omega
          apply List.Forall₂.cons
          · exact hrel (x, y) (by simp)
          · apply ih htailLength
            intro pair hmem
            exact hrel pair (by simp [hmem])

/-- Equal anonymous constant addresses plus the certified universe gate give
definitional equality of the two translated constant heads. -/
theorem constantHeadsDefEq
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx}
    (hcollision : support.CollisionFree)
    {leftId rightId : KId .anon}
    {leftLevels rightLevels : Array (KUniv .anon)}
    {leftInfo rightInfo : ExprInfo .anon} {leftV rightV : VExpr}
    (hleftLevels : ∀ level, level ∈ leftLevels.toList →
      support.univ level ∧ level.size < UInt64.size)
    (hrightLevels : ∀ level, level ∈ rightLevels.toList →
      support.univ level ∧ level.size < UInt64.size)
    (hleft : TrKExprS world.venv uvars world.nameOf trProj Delta
      (.const leftId leftLevels leftInfo) leftV)
    (hright : TrKExprS world.venv uvars world.nameOf trProj Delta
      (.const rightId rightLevels rightInfo) rightV)
    (hid : (leftId.addr == rightId.addr) = true)
    (hlevels : sameDefEqUniverses leftLevels rightLevels = true) :
    world.venv.IsDefEqU uvars Delta.toCtx leftV rightV := by
  have hidEq : leftId = rightId :=
    KId.anon_eq_of_addr_eq (eq_of_beq hid)
  subst rightId
  cases hleft with
  | const hleftName hleftConst hleftWF hleftArity =>
      cases hright with
      | const hrightName hrightConst hrightWF hrightArity =>
          have hname := Option.some.inj (hleftName.symm.trans hrightName)
          cases hname
          have hconst :=
            Option.some.inj (hleftConst.symm.trans hrightConst)
          cases hconst
          obtain ⟨hlength, hpairs⟩ := sameDefEqUniverses_sound hcollision
            hleftLevels hrightLevels hlevels
          refine ⟨_, Lean4Lean.VEnv.IsDefEq.constDF hleftConst ?_ ?_ ?_ ?_⟩
          · intro level hmem
            obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hmem
            exact hleftWF raw (by simpa using hraw)
          · intro level hmem
            obtain ⟨raw, hraw, rfl⟩ := List.mem_map.mp hmem
            exact hrightWF raw (by simpa using hraw)
          · simpa only [List.length_map, Array.length_toList] using hleftArity
          · exact forall₂_map_of_zip hlength hpairs

/-- Exact semantic contract for the production same-head helper. -/
def TrySameHeadSpine.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta state left right leftV rightV},
    support left → support right →
    TrKExprS world.venv uvars world.nameOf trProj Delta left leftV →
    TrKExprS world.venv uvars world.nameOf trProj Delta right rightV →
    RecM.WF layer semantics trProj world support uvars Delta state
      (trySameHeadSpine left right)
      (fun result _ => match result with
        | none => True
        | some answer => answer = true →
            world.venv.IsDefEqU uvars Delta.toCtx leftV rightV)

/-- Complete execution and semantic proof of `trySameHeadSpine`. -/
theorem trySameHeadSpine_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {left right : KExpr .anon} {leftV rightV : VExpr}
    (theory : WhnfTheory trProj world uvars)
    (hcollision : support.CollisionFree)
    (hresources : SameHeadSpineResources support)
    (hleftSupport : support left) (hrightSupport : support right)
    (hleft : TrKExprS world.venv uvars world.nameOf trProj Delta left leftV)
    (hright : TrKExprS world.venv uvars world.nameOf trProj Delta right
      rightV) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (trySameHeadSpine left right)
      (fun result _ => match result with
        | none => True
        | some answer => answer = true →
            world.venv.IsDefEqU uvars Delta.toCtx leftV rightV) := by
  rcases hleftCollect : left.collectSpine with ⟨leftHead, leftArgs⟩
  rcases hrightCollect : right.collectSpine with ⟨rightHead, rightArgs⟩
  unfold trySameHeadSpine
  simp only [hleftCollect, hrightCollect]
  cases leftHead <;> try exact RecM.WF.pure fun _ => trivial
  case const leftId leftLevels leftInfo =>
    cases rightHead <;> try exact RecM.WF.pure fun _ => trivial
    case const rightId rightLevels rightInfo =>
      cases hshape :
          (leftId.addr != rightId.addr || leftArgs.size != rightArgs.size) with
      | true =>
          simp only [hshape, if_true]
          exact RecM.WF.pure fun _ => trivial
      | false =>
          simp only [hshape, Bool.false_eq_true, if_false]
          have hshapeParts := Bool.or_eq_false_iff.mp hshape
          have hid : (leftId.addr == rightId.addr) = true := by
            simpa using hshapeParts.1
          have hargsSize : leftArgs.size = rightArgs.size := by
            exact eq_of_beq (by simpa using hshapeParts.2)
          cases huniverses :
              sameDefEqUniverses leftLevels rightLevels with
          | false =>
              simp only [Bool.not_false, if_true]
              exact RecM.WF.pure fun _ => trivial
          | true =>
              simp only [Bool.not_true, Bool.false_eq_true, if_false]
              have hleftSpine :=
                trAppSpine_of_collectSpine hleft hleftCollect
              have hrightSpine :=
                trAppSpine_of_collectSpine hright hrightCollect
              apply RecM.WF.bind <| allDefEqSpineArgs_wf _ (by
                intro pair hmem
                have hmem' : pair ∈
                    leftArgs.toList.zip rightArgs.toList := by
                  simpa only [Array.toList_zip] using hmem
                have hleftMem := left_mem_of_pair_mem_zip hmem'
                have hrightMem := right_mem_of_pair_mem_zip hmem'
                obtain ⟨pairLeftV, pairLeftTy, hpairLeftTyped,
                  hpairLeft⟩ := hleftSpine.argument hleftMem
                obtain ⟨pairRightV, pairRightTy, hpairRightTyped,
                  hpairRight⟩ := hrightSpine.argument hrightMem
                exact ⟨hresources.arguments hleftSupport hleftCollect _
                    hleftMem,
                  hresources.arguments hrightSupport hrightCollect _
                    hrightMem,
                  pairLeftV, pairRightV, hpairLeft, hpairRight⟩)
              intro accepted afterArgs haccepted
              cases accepted with
              | false =>
                  simp only [Bool.not_false, if_true]
                  exact RecM.WF.pure fun _ => trivial
              | true =>
                  simp only [Bool.not_true, Bool.false_eq_true, if_false]
                  exact RecM.WF.pure fun hI _ => by
                    have hDelta : KVLCtx.WF world.venv uvars Delta :=
                      hI.2.1.wf
                    have hhead : ∀ {leftHeadV rightHeadV},
                        TrKExprS world.venv uvars world.nameOf trProj Delta
                            (.const leftId leftLevels leftInfo) leftHeadV →
                        TrKExprS world.venv uvars world.nameOf trProj Delta
                            (.const rightId rightLevels rightInfo) rightHeadV →
                        world.venv.IsDefEqU uvars Delta.toCtx
                          leftHeadV rightHeadV := by
                      intro leftHeadV rightHeadV hleftHead hrightHead
                      exact constantHeadsDefEq hcollision
                        (hresources.universes hleftSupport hleftCollect)
                        (hresources.universes hrightSupport hrightCollect)
                        hleftHead hrightHead hid (by simpa using huniverses)
                    apply TrAppSpine.defEq_of_zip theory hDelta hleftSpine
                      hrightSpine
                    · simpa only [Array.length_toList] using hargsSize
                    · exact hhead
                    · intro pair hmem
                      exact haccepted rfl pair (by
                        simpa only [Array.toList_zip] using hmem)

namespace TrySameHeadSpine

/-- Package the concrete proof as the helper contract. -/
theorem ofResources
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (theory : WhnfTheory trProj world uvars)
    (hcollision : support.CollisionFree)
    (hresources : SameHeadSpineResources support) :
    TrySameHeadSpine.WFAt layer semantics trProj world support uvars := by
  intro Delta state left right leftV rightV hleftSupport hrightSupport
    hleft hright
  exact trySameHeadSpine_wf theory hcollision hresources hleftSupport
    hrightSupport hleft hright

end TrySameHeadSpine

end RecM

end Ix.Tc
