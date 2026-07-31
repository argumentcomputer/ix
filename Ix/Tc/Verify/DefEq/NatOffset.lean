import Ix.Tc.Verify.DefEq.LazyDelta

/-!
# Nat-offset comparison

The generalized offset reducer begins with an exact literal/literal case and
then enters the structural zero/parser/rebuilder path.  This module closes
the literal case and leaves the latter path behind a separately named
contract.  In particular, no negative result is assigned semantic meaning.
-/

namespace Ix.Tc

open Lean4Lean (VExpr)

namespace RecM

/-- Exact contract for the structural offset path after the direct pair of
Nat literals has been ruled out. -/
def TryDefEqOffsetAfterLiteral.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta state left right leftV rightV},
    support left → support right →
    TrKExprS world.venv uvars world.nameOf trProj Delta left leftV →
    TrKExprS world.venv uvars world.nameOf trProj Delta right rightV →
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryDefEqOffsetAfterLiteral left right)
      (fun result _ => match result with
        | none => True
        | some answer => answer = true →
            world.venv.IsDefEqU uvars Delta.toCtx leftV rightV)

/-- Positive-result contract for the production Nat-zero recognizer.  The
recognizer is permitted to miss, but acceptance identifies the exact Theory
zero expression. -/
def IsNatZero.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta state source sourceV},
    support source →
    TrKExprS world.venv uvars world.nameOf trProj Delta source sourceV →
    RecM.WF layer semantics trProj world support uvars Delta state
      (isNatZero source)
      (fun answer _ => answer = true → sourceV = VExpr.natZero)

/-- Exact generalized offset contract after the joint zero probe misses. -/
def TryDefEqOffsetAfterZeroMiss.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta state left right leftV rightV},
    support left → support right →
    TrKExprS world.venv uvars world.nameOf trProj Delta left leftV →
    TrKExprS world.venv uvars world.nameOf trProj Delta right rightV →
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryDefEqOffsetAfterZeroMiss left right)
      (fun result _ => match result with
        | none => True
        | some answer => answer = true →
            world.venv.IsDefEqU uvars Delta.toCtx leftV rightV)

/-- Exact decomposition/rebuild contract after both syntactic candidate
guards accept. -/
def TryDefEqOffsetAfterCandidates.WFAt (layer : WhnfLayer)
    (semantics : CacheSemantics) (trProj : RawProjRel)
    (world : VerifyWorld) (support : RunSupport) (uvars : Nat) : Prop :=
  ∀ {Delta state left right leftV rightV},
    support left → support right →
    TrKExprS world.venv uvars world.nameOf trProj Delta left leftV →
    TrKExprS world.venv uvars world.nameOf trProj Delta right rightV →
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryDefEqOffsetAfterCandidates left right)
      (fun result _ => match result with
        | none => True
        | some answer => answer = true →
            world.venv.IsDefEqU uvars Delta.toCtx leftV rightV)

/-- The exact primitive-table authority needed by `isNatZero`.  The full
no-delta table is retained so the existing literal-extraction theorem can be
reused without introducing a second address-to-name proof. -/
structure NatZeroContext (world : VerifyWorld) : Prop where
  table : ∀ (prims : Primitives .anon), prims.CanonicalAnon →
    NoDeltaPrimitiveTableAgrees world prims
  theoryPrimitives : world.venv.HasPrimitives

namespace NatZeroContext

/-- Project the Nat-zero authority from an existing no-delta primitive
context. -/
def ofNoDelta {world : VerifyWorld} {support : RunSupport}
    {flags : WhnfFlags} {natSuccMode : NatSuccMode}
    (context : NoDeltaPrimitiveContext world support flags natSuccMode) :
    NatZeroContext world where
  table := context.table
  theoryPrimitives := context.theoryPrimitives

end NatZeroContext

/-- The actual production Nat-zero recognizer is sound in no-acceleration
mode.  A positive answer is converted to the already-proved canonical
`extractNatLit = some 0` translation theorem. -/
theorem isNatZero_wf
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    {Delta : KVLCtx} {state : TcState .anon}
    {source : KExpr .anon} {sourceV : VExpr}
    (context : NatZeroContext world)
    (hsourceSupport : support source)
    (hsource : TrKExprS world.venv uvars world.nameOf trProj Delta source
      sourceV) :
    RecM.WF .noAccel semantics trProj world support uvars Delta state
      (isNatZero source)
      (fun answer _ => answer = true → sourceV = VExpr.natZero) := by
  unfold isNatZero
  apply RecM.WF.bind (RecM.WF.withInv (prims_wf (s := state)))
  intro runtimePrims afterRead hread
  rcases hread with ⟨hI, hprims, hafterRead⟩
  subst runtimePrims
  subst afterRead
  have htable := context.table state.prims hI.noAccel_primitives
  cases source <;> simp only
  all_goals
    exact RecM.WF.pure fun _ hanswer => by
      have hresult := TrKExprS.of_extractNatLit (n := 0) htable
        context.theoryPrimitives hsource (by simp_all [extractNatLit])
      simpa [VExpr.natLit] using hresult

namespace IsNatZero

/-- Package the concrete recognizer theorem at every universe count. -/
theorem ofContext
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    (context : NatZeroContext world) :
    IsNatZero.WFAt .noAccel semantics trProj world support uvars := by
  intro Delta state source sourceV hsourceSupport hsource
  exact isNatZero_wf context hsourceSupport hsource

end IsNatZero

/-- Close the allocation-free candidate guard.  Rejection returns `none`,
which intentionally carries no semantic obligation; acceptance delegates to
the exact decomposition/rebuild contract. -/
theorem tryDefEqOffsetAfterZeroMiss_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {left right : KExpr .anon} {leftV rightV : VExpr}
    (hafter : TryDefEqOffsetAfterCandidates.WFAt layer semantics trProj
      world support uvars)
    (hleftSupport : support left) (hrightSupport : support right)
    (hleft : TrKExprS world.venv uvars world.nameOf trProj Delta left leftV)
    (hright : TrKExprS world.venv uvars world.nameOf trProj Delta right rightV) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryDefEqOffsetAfterZeroMiss left right)
      (fun result _ => match result with
        | none => True
        | some answer => answer = true →
            world.venv.IsDefEqU uvars Delta.toCtx leftV rightV) := by
  unfold tryDefEqOffsetAfterZeroMiss
  apply RecM.WF.bind (RecM.WF.withInv (prims_wf (s := state)))
  intro runtimePrims afterRead hread
  rcases hread with ⟨hI, hprims, hafterRead⟩
  subst runtimePrims
  subst afterRead
  cases hguard :
      (!natOffsetCandidate state.prims left ||
        !natOffsetCandidate state.prims right) with
  | false =>
      simp only [Bool.false_eq_true, if_false]
      exact hafter hleftSupport hrightSupport hleft hright
  | true =>
      simp only [if_true]
      exact RecM.WF.pure fun _ => trivial

namespace TryDefEqOffsetAfterZeroMiss

/-- Package candidate rejection as the complete post-zero contract. -/
theorem ofCandidates
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (hafter : TryDefEqOffsetAfterCandidates.WFAt layer semantics trProj
      world support uvars) :
    Ix.Tc.RecM.TryDefEqOffsetAfterZeroMiss.WFAt layer semantics trProj world
      support uvars := by
  intro Delta state left right leftV rightV hleftSupport hrightSupport
    hleft hright
  exact tryDefEqOffsetAfterZeroMiss_wf hafter hleftSupport hrightSupport
    hleft hright

end TryDefEqOffsetAfterZeroMiss

/-- Close the zero/zero branch after the literal fast path. -/
theorem tryDefEqOffsetAfterLiteral_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {left right : KExpr .anon} {leftV rightV : VExpr}
    (theory : WhnfTheory trProj world uvars)
    (hzero : IsNatZero.WFAt layer semantics trProj world support uvars)
    (hafter : TryDefEqOffsetAfterZeroMiss.WFAt layer semantics trProj world
      support uvars)
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    (hleftSupport : support left) (hrightSupport : support right)
    (hleft : TrKExprS world.venv uvars world.nameOf trProj Delta left leftV)
    (hright : TrKExprS world.venv uvars world.nameOf trProj Delta right rightV) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryDefEqOffsetAfterLiteral left right)
      (fun result _ => match result with
        | none => True
        | some answer => answer = true →
            world.venv.IsDefEqU uvars Delta.toCtx leftV rightV) := by
  have hleftWF := hleft.wf world.venvWF.ordered theory.literalWF
    theory.projections.wf hDelta
  unfold tryDefEqOffsetAfterLiteral
  apply RecM.WF.bind (hzero hleftSupport hleft)
  intro leftIsZero afterLeft hleftZero
  apply RecM.WF.bind (hzero hrightSupport hright)
  intro rightIsZero afterRight hrightZero
  cases leftIsZero with
  | false =>
      cases rightIsZero <;>
        simp only [Bool.false_and, Bool.false_eq_true, if_false] <;>
        exact hafter hleftSupport hrightSupport hleft hright
  | true =>
      cases rightIsZero with
      | false =>
          simp only [Bool.true_and, Bool.false_eq_true, if_false]
          exact hafter hleftSupport hrightSupport hleft hright
      | true =>
          simp only [Bool.true_and, if_true]
          exact RecM.WF.pure fun _ _ => by
            have hleftValue := hleftZero rfl
            have hrightValue := hrightZero rfl
            subst leftV
            subst rightV
            exact Lean4Lean.VEnv.IsDefEqU.refl hleftWF

namespace TryDefEqOffsetAfterLiteral

/-- Package the zero-prefix proof as the complete post-literal contract. -/
theorem ofZero
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (theory : WhnfTheory trProj world uvars)
    (hzero : IsNatZero.WFAt layer semantics trProj world support uvars)
    (hafter : TryDefEqOffsetAfterZeroMiss.WFAt layer semantics trProj world
      support uvars) :
    Ix.Tc.RecM.TryDefEqOffsetAfterLiteral.WFAt layer semantics trProj world
      support uvars := by
  intro Delta state left right leftV rightV hleftSupport hrightSupport
    hleft hright
  intro methods hmethods hI
  exact (tryDefEqOffsetAfterLiteral_wf theory hzero hafter hI.2.1.wf
    hleftSupport hrightSupport hleft hright) methods hmethods hI

end TryDefEqOffsetAfterLiteral

/-- Close the direct Nat-literal branch of `tryDefEqOffset`.  Equality of the
runtime literal payloads makes the two Theory literals definitionally equal
by reflexivity; every other constructor pair is delegated unchanged. -/
theorem tryDefEqOffset_wf
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat} {Delta : KVLCtx} {state : TcState .anon}
    {left right : KExpr .anon} {leftV rightV : VExpr}
    (theory : WhnfTheory trProj world uvars)
    (hafter : TryDefEqOffsetAfterLiteral.WFAt layer semantics trProj world
      support uvars)
    (hDelta : KVLCtx.WF world.venv uvars Delta)
    (hleftSupport : support left) (hrightSupport : support right)
    (hleft : TrKExprS world.venv uvars world.nameOf trProj Delta left leftV)
    (hright : TrKExprS world.venv uvars world.nameOf trProj Delta right rightV) :
    RecM.WF layer semantics trProj world support uvars Delta state
      (tryDefEqOffset left right)
      (fun result _ => match result with
        | none => True
        | some answer => answer = true →
            world.venv.IsDefEqU uvars Delta.toCtx leftV rightV) := by
  have hleftWF := hleft.wf world.venvWF.ordered theory.literalWF
    theory.projections.wf hDelta
  cases left <;> simp only [tryDefEqOffset, pure_bind]
  all_goals
    first
    | exact hafter hleftSupport hrightSupport hleft hright
    | skip
  cases right
  all_goals
    first
    | exact hafter hleftSupport hrightSupport hleft hright
    | skip
  cases hleft
  cases hright
  exact RecM.WF.pure fun _ hanswer => by
    have hvalues := eq_of_beq hanswer
    cases hvalues
    exact Lean4Lean.VEnv.IsDefEqU.refl hleftWF

namespace TryDefEqOffset

/-- Package the literal-prefix proof as the complete offset contract. -/
theorem ofAfterLiteral
    {layer : WhnfLayer} {semantics : CacheSemantics}
    {trProj : RawProjRel} {world : VerifyWorld} {support : RunSupport}
    {uvars : Nat}
    (theory : WhnfTheory trProj world uvars)
    (hafter : TryDefEqOffsetAfterLiteral.WFAt layer semantics trProj world
      support uvars) :
    Ix.Tc.RecM.TryDefEqOffset.WFAt layer semantics trProj world support
      uvars := by
  intro Delta state left right leftV rightV hleftSupport hrightSupport
    hleft hright
  intro methods hmethods hI
  exact (tryDefEqOffset_wf theory hafter hI.2.1.wf hleftSupport
    hrightSupport hleft hright) methods hmethods hI

/-- Reduce the complete concrete offset contract to the remaining
decomposition/rebuild path. -/
theorem ofContext
    {semantics : CacheSemantics} {trProj : RawProjRel}
    {world : VerifyWorld} {support : RunSupport} {uvars : Nat}
    (theory : WhnfTheory trProj world uvars)
    (zeroContext : NatZeroContext world)
    (hafter : TryDefEqOffsetAfterCandidates.WFAt .noAccel semantics trProj
      world support uvars) :
    Ix.Tc.RecM.TryDefEqOffset.WFAt .noAccel semantics trProj world support
      uvars :=
  ofAfterLiteral theory <|
    TryDefEqOffsetAfterLiteral.ofZero theory
      (IsNatZero.ofContext zeroContext)
      (TryDefEqOffsetAfterZeroMiss.ofCandidates hafter)

end TryDefEqOffset

end RecM

end Ix.Tc
