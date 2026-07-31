import Ix.Tc.Verify.DefEq.Structural

/-!
# Eager Bool.true definitional equality

The second recursive tier recognizes the trusted `Bool.true` constant on one
side, normalizes the other side, and recognizes the same constant again.
Acceptance is sound only when the runtime primitive address is tied to the
trusted Theory name; address equality by itself is not authority.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

/-- Minimal trusted binding for the one primitive read by the eager Boolean
tier. -/
structure BoolTruePrimitiveContext (world : VerifyWorld) : Prop where
  table : ∀ prims : Primitives .anon, prims.CanonicalAnon →
    PrimitiveIdAgrees world prims.boolTrue ``Bool.true

/-- The selected verification layer guarantees that every invariant state
uses the canonical anonymous primitive table.  Both production reduction
layers satisfy this; the weaker structural-only layer deliberately does not.
-/
def CanonicalPrimitiveStates (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta s},
    WhnfStateInv layer semantics trProj world support uvars Delta s →
      s.prims.CanonicalAnon

theorem canonicalPrimitiveStates_noAccel
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat} :
    CanonicalPrimitiveStates .noAccel semantics trProj world support
      uvars :=
  fun hI => hI.noAccel_primitives

theorem canonicalPrimitiveStates_accelerated
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat} :
    CanonicalPrimitiveStates .accelerated semantics trProj world support
      uvars :=
  fun hI => hI.accelerated_primitives

namespace RecM

/-- The primitive classifier is state-transparent.  A positive answer pins
the structural translation to the exact Theory constant `Bool.true`; the
proof uses the trusted `nameOf` binding after the runtime table has been
shown canonical. -/
theorem isBoolTrue_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {source : KExpr .anon} {sourceV : VExpr}
    (context : BoolTruePrimitiveContext world)
    (hcanonical : CanonicalPrimitiveStates layer semantics trProj world
      support uvars)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (isBoolTrue source)
      (fun answer after => after = s ∧
        (answer = true → sourceV = VExpr.boolTrue)) := by
  cases hsource <;> simp only [isBoolTrue]
  all_goals
    first
    | exact RecM.WF.pure fun _ => ⟨rfl, fun h => by contradiction⟩
    | skip
  rename_i id us info name ci hname hlookup hlevels harity
  apply RecM.WF.bind (prims_wf (s := s))
  intro runtimePrims after hread
  rcases hread with ⟨hprims, hafter⟩
  subst after
  exact RecM.WF.pure fun hI => ⟨rfl, fun hanswer => by
    obtain ⟨hempty, haddr⟩ := Bool.and_eq_true_iff.mp hanswer
    have hus : us = #[] := Array.empty_of_isEmpty hempty
    subst us
    have hnameEq : name = ``Bool.true := by
      apply Option.some.inj
      calc
        some name = world.nameOf id.addr := hname.symm
        _ = world.nameOf runtimePrims.boolTrue.addr :=
          congrArg world.nameOf (eq_of_beq haddr)
        _ = some ``Bool.true :=
          (context.table runtimePrims (by
            rw [hprims]
            exact hcanonical hI)).2
    subst name
    simp [VExpr.boolTrue]⟩

/-- The closed/eager policy check is a pure state observation. -/
theorem boolTrueReductionAllowed_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    (source : KExpr .anon) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (boolTrueReductionAllowed source) (fun _ after => after = s) := by
  unfold boolTrueReductionAllowed
  cases hfv : source.hasFVars with
  | false =>
      simp only [Bool.not_false, if_true]
      exact RecM.WF.pure fun _ => rfl
  | true =>
      simp only [Bool.not_true, Bool.false_eq_true, if_false]
      apply RecM.WF.bind
        (Q₁ := fun observed after => observed = s ∧ after = s)
        (RecM.WF.get fun _ => ⟨rfl, rfl⟩)
      intro observed after hread
      rcases hread with ⟨rfl, rfl⟩
      exact RecM.WF.pure (E := fun _ _ => True) fun _ => rfl

/-- Direct WHNF contract used by the eager Boolean tier.  K1 supplies this
for the current unfolded layer; keeping it generic avoids confusing the
current reducer with the predecessor-table callback. -/
def DefEqDirectWhnf.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta s source sourceV},
    support source →
    TrKExprS world.venv uvars world.nameOf trProj Delta source sourceV →
    RecM.WF layer semantics trProj world support uvars Delta s
      (whnf source)
      (fun result _ => support result ∧
        WhnfPost trProj world uvars Delta sourceV result)

/-- Normalize one side and recognize its result as trusted `Bool.true`.
A positive answer therefore denotes equality between the original Theory
term and the canonical Boolean literal. -/
theorem whnfThenIsBoolTrue_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {source : KExpr .anon} {sourceV : VExpr}
    (context : BoolTruePrimitiveContext world)
    (hcanonical : CanonicalPrimitiveStates layer semantics trProj world
      support uvars)
    (hwhnf : DefEqDirectWhnf.WFAt layer semantics trProj world support
      uvars)
    (hsourceSupport : support source)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (whnfIsBoolTrue source)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx sourceV VExpr.boolTrue) := by
  unfold whnfIsBoolTrue
  apply RecM.WF.bind
    (RecM.WF.withInv <| hwhnf hsourceSupport hsource)
  intro reduced afterWhnf hwhnfPost
  rcases hwhnfPost with
    ⟨hIWhnf, hreducedSupport, reducedV, hreducedTr, hsourceReduced⟩
  apply RecM.WF.mono
    (isBoolTrue_wf context hcanonical hreducedTr)
  · intro answer final hrecognized hanswer
    exact hrecognized.2 hanswer ▸ hsourceReduced
  · intro _ _ _
    trivial

namespace DefEqAfterBoolTrue

/-- Semantic contract for the tiers following eager Boolean reduction. -/
def WF (layer : WhnfLayer) (semantics : CacheSemantics)
    (trProj : RawProjRel) (world : VerifyWorld) (support : RunSupport)
    (uvars : Nat) : Prop :=
  ∀ {Delta s a b aV bV},
    support a → support b →
    TrKExprS world.venv uvars world.nameOf trProj Delta a aV →
    TrKExprS world.venv uvars world.nameOf trProj Delta b bV →
    RecM.WF layer semantics trProj world support uvars Delta s
      (isDefEqInnerAfterBoolTrue a b)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx aV bV)

end DefEqAfterBoolTrue

/-- Soundness of the symmetric eager-Boolean direction.  This helper is
entered only when the first direction's recognition/policy guard was
unavailable. -/
theorem isDefEqInnerAfterFirstBoolGuardMiss_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {s : TcState .anon}
    {a b : KExpr .anon} {aV bV : VExpr}
    (context : BoolTruePrimitiveContext world)
    (hcanonical : CanonicalPrimitiveStates layer semantics trProj world
      support uvars)
    (hwhnf : DefEqDirectWhnf.WFAt layer semantics trProj world support
      uvars)
    (htail : DefEqAfterBoolTrue.WF layer semantics trProj world support
      uvars)
    (haSupport : support a) (hbSupport : support b)
    (ha : TrKExprS world.venv uvars world.nameOf trProj Delta a aV)
    (hb : TrKExprS world.venv uvars world.nameOf trProj Delta b bV) :
    RecM.WF layer semantics trProj world support uvars Delta s
      (isDefEqInnerAfterFirstBoolGuardMiss a b)
      (fun answer _ => answer = true →
        world.venv.IsDefEqU uvars Delta.toCtx aV bV) := by
  unfold isDefEqInnerAfterFirstBoolGuardMiss
  apply RecM.WF.bind (isBoolTrue_wf context hcanonical ha)
  intro aIsTrue afterA hclassifyA
  rcases hclassifyA with ⟨hafterA, haTrue⟩
  subst afterA
  apply RecM.WF.bind (boolTrueReductionAllowed_wf b)
  intro allowed afterPolicy hafterPolicy
  subst afterPolicy
  cases aIsTrue with
  | false =>
      cases allowed <;>
        simp only [Bool.false_and, Bool.false_eq_true, if_false] <;>
        exact htail haSupport hbSupport ha hb
  | true =>
      cases allowed with
      | false =>
          simp only [Bool.true_and, Bool.false_eq_true, if_false]
          exact htail haSupport hbSupport ha hb
      | true =>
          simp only [Bool.true_and, if_true]
          apply RecM.WF.bind
            (whnfThenIsBoolTrue_wf context hcanonical hwhnf hbSupport hb)
          intro normalizedTrue afterNormalize hnormalized
          cases normalizedTrue with
          | false =>
              simp only [Bool.false_eq_true, if_false]
              exact htail haSupport hbSupport ha hb
          | true =>
              simp only [if_true]
              exact RecM.WF.pure fun _ _ => by
                have haEq := haTrue rfl
                simpa [haEq] using (hnormalized rfl).symm

/-- Discharge the complete eager-Boolean prefix.  If the first guard is
unavailable, production delegates to the symmetric helper above.  If that
guard is available but normalization does not recognize `Bool.true`, the
algorithm intentionally skips the symmetric attempt and continues directly
to the later tiers. -/
theorem DefEqAfterBoolTrue.closesAfterQuick
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (context : BoolTruePrimitiveContext world)
    (hcanonical : CanonicalPrimitiveStates layer semantics trProj world
      support uvars)
    (hwhnf : DefEqDirectWhnf.WFAt layer semantics trProj world support
      uvars)
    (htail : DefEqAfterBoolTrue.WF layer semantics trProj world support
      uvars) :
    DefEqAfterQuick.WF layer semantics trProj world support uvars := by
  intro Delta s a b aV bV haSupport hbSupport ha hb
  unfold isDefEqInnerAfterQuick
  apply RecM.WF.bind (isBoolTrue_wf context hcanonical hb)
  intro bIsTrue afterB hclassifyB
  rcases hclassifyB with ⟨hafterB, hbTrue⟩
  subst afterB
  apply RecM.WF.bind (boolTrueReductionAllowed_wf a)
  intro allowed afterPolicy hafterPolicy
  subst afterPolicy
  cases bIsTrue with
  | false =>
      cases allowed <;>
        simp only [Bool.false_and, Bool.false_eq_true, if_false] <;>
        exact isDefEqInnerAfterFirstBoolGuardMiss_wf
          context hcanonical hwhnf htail haSupport hbSupport ha hb
  | true =>
      cases allowed with
      | false =>
          simp only [Bool.true_and, Bool.false_eq_true, if_false]
          exact isDefEqInnerAfterFirstBoolGuardMiss_wf
            context hcanonical hwhnf htail haSupport hbSupport ha hb
      | true =>
          simp only [Bool.true_and, if_true]
          apply RecM.WF.bind
            (whnfThenIsBoolTrue_wf context hcanonical hwhnf haSupport ha)
          intro normalizedTrue afterNormalize hnormalized
          cases normalizedTrue with
          | false =>
              simp only [Bool.false_eq_true, if_false]
              exact htail haSupport hbSupport ha hb
          | true =>
              simp only [if_true]
              exact RecM.WF.pure fun _ _ => by
                have hbEq := hbTrue rfl
                simpa [hbEq] using hnormalized rfl

/-- Assemble Tier 1 structural comparison and Tier 1b eager Boolean
reduction into the recursive-inner contract, leaving only the post-Boolean
tail as an explicit obligation. -/
theorem DefEqAfterBoolTrue.closesInner
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (theory : WhnfTheory trProj world uvars)
    (hcollision : support.CollisionFree)
    (hsorts : SortComponentResources support)
    (hstructural : QuickDefEqResources support)
    (context : BoolTruePrimitiveContext world)
    (hcanonical : CanonicalPrimitiveStates layer semantics trProj world
      support uvars)
    (hwhnf : DefEqDirectWhnf.WFAt layer semantics trProj world support
      uvars)
    (htail : DefEqAfterBoolTrue.WF layer semantics trProj world support
      uvars) :
    ∀ {Delta s a b aV bV},
      support a → support b →
      TrKExprS world.venv uvars world.nameOf trProj Delta a aV →
      TrKExprS world.venv uvars world.nameOf trProj Delta b bV →
      RecM.WF layer semantics trProj world support uvars Delta s
        (isDefEqInner a b)
        (fun answer _ => answer = true →
          world.venv.IsDefEqU uvars Delta.toCtx aV bV) :=
  DefEqAfterQuick.closesInner theory hcollision hsorts hstructural
    (DefEqAfterBoolTrue.closesAfterQuick context hcanonical hwhnf htail)

end RecM

end Ix.Tc
