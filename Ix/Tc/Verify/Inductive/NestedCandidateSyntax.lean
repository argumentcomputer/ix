import Ix.Tc.Verify.Inductive.ExactLeanSyntax
import Ix.Tc.Verify.Inductive.NestedRecursiveFixture
import Lean4Lean.Verify.Environment.InductiveFixtures

/-!
# Lean4Lean candidate produced by nested elimination

The production Ix fixture reaches `Box Tree` and records an auxiliary flat
member whose physical identity remains the external `Box` address plus its
exact specialization key.  Lean4Lean represents the same operation
differently: `ElimNestedInductive.run` creates a fresh family constant and
rewrites both the outer constructor and the copied external constructor to
refer to that constant.

This module executes that real Lean4Lean transformation for the same
monomorphic `Box`/`Tree` shape and retains the exact flattened syntax.  The
fresh auxiliary name is therefore an output of the producer, not a name
chosen by the transport proof.
-/

namespace Ix.Tc.NestedRecursiveFixture

open Lean Meta Elab Term
open Lean4Lean.InductiveReplayFixtures

/-! ## Previously declared external family -/

/-- Kernel metadata source for the external family used by the candidate
eliminator.  It is monomorphic at `Type`, matching the anonymous Ix fixture's
zero universe parameters and `Sort 1` result. -/
inductive LeanBox (α : Type) : Type where
  | wrap : α → LeanBox α

/-- Stored-metadata counterpart of the compiler-shaped Ix source.  Keeping
this declaration at the exact synthetic names used below lets the semantic
nested transaction quote the restored recursors and rules without a
name-renaming premise. -/
inductive LeanTree : Type where
  | node : LeanBox LeanTree → LeanTree

def leanBoxInfo : Lean.ConstantInfo := kernelInductInfo% LeanBox
def leanWrapInfo : Lean.ConstantInfo := kernelCtorInfo% LeanBox.wrap

def leanBoxMap : Lean.ConstMap :=
  (({} : Lean.ConstMap).insert ``LeanBox leanBoxInfo).insert
    ``LeanBox.wrap leanWrapInfo

def leanNestedBaseEnv : Lean.Kernel.Environment :=
  Lean.Kernel.Environment.ofConstants `_ixNestedCandidate leanBoxMap

/-! ## Unflattened source declaration -/

def leanTreeName : Lean.Name := `Ix.Tc.NestedRecursiveFixture.LeanTree
def leanNodeName : Lean.Name := `Ix.Tc.NestedRecursiveFixture.LeanTree.node
def leanTreeExpr : Lean.Expr := .const leanTreeName []
def leanNestedDomain : Lean.Expr := .app (.const ``LeanBox []) leanTreeExpr

def leanTreeSource : Lean.InductiveType :=
  { name := leanTreeName
    type := .sort 1
    ctors := [
      { name := leanNodeName
        type := .forallE `value leanNestedDomain leanTreeExpr .default }] }

def leanNestedEliminationOutcome :=
  (Lean4Lean.ElimNestedInductive.run 1000 0 [leanTreeSource]
      leanNestedBaseEnv).run'
    { lvls := [], newTypes := #[leanTreeSource] }

def leanFlatTypes : List Lean.InductiveType :=
  match leanNestedEliminationOutcome with
  | .ok result => result.types
  | .error _ => []

def leanAuxiliarySource? : Lean.Name → Option Lean.Expr
  | auxiliaryName =>
      match leanNestedEliminationOutcome with
      | .ok result => result.aux2nested.find? auxiliaryName
      | .error _ => none

private def emptyInductiveType : Lean.InductiveType :=
  { name := `_invalidNestedCandidate, type := .sort 0, ctors := [] }

private def emptyConstructor : Lean.Constructor :=
  { name := `_invalidNestedCandidate.ctor, type := .sort 0 }

def leanFlatTree : Lean.InductiveType :=
  match leanFlatTypes with
  | tree :: _ => tree
  | _ => emptyInductiveType

def leanFlatAuxiliary : Lean.InductiveType :=
  match leanFlatTypes with
  | _ :: auxiliary :: _ => auxiliary
  | _ => emptyInductiveType

def leanFlatNode : Lean.Constructor :=
  match leanFlatTree.ctors with
  | constructor :: _ => constructor
  | _ => emptyConstructor

def leanFlatWrap : Lean.Constructor :=
  match leanFlatAuxiliary.ctors with
  | constructor :: _ => constructor
  | _ => emptyConstructor

def leanAuxiliaryName : Lean.Name := leanFlatAuxiliary.name
def leanAuxiliaryConstructorName : Lean.Name := leanFlatWrap.name
def leanAuxiliaryExpr : Lean.Expr := .const leanAuxiliaryName []

private theorem leanNestedEliminationSucceededNative :
    (match leanNestedEliminationOutcome with
      | .ok _ => true
      | .error _ => false) = true := by
  native_decide

/-- The real nested eliminator succeeds on the source declaration. -/
theorem leanNestedEliminationSucceeded :
    ∃ result, leanNestedEliminationOutcome = .ok result := by
  have success := leanNestedEliminationSucceededNative
  generalize houtcome : leanNestedEliminationOutcome = outcome at success ⊢
  cases outcome <;> simp_all

private theorem leanFlatNamesNative :
    leanFlatTypes.map (·.name) = #[leanTreeName, leanAuxiliaryName].toList := by
  native_decide

/-- The flat block retains the original family first and appends exactly one
generated auxiliary in producer order. -/
theorem leanFlatNames :
    leanFlatTypes.map (·.name) = [leanTreeName, leanAuxiliaryName] := by
  simpa using leanFlatNamesNative

private theorem leanFlatTreeTypeNative :
    ExactLeanSyntax.exprCheck leanFlatTree.type (.sort 1) = true := by
  native_decide

theorem leanFlatTreeType : leanFlatTree.type = .sort 1 :=
  ExactLeanSyntax.expr_eq_of_check leanFlatTreeTypeNative

private theorem leanFlatAuxiliaryTypeNative :
    ExactLeanSyntax.exprCheck leanFlatAuxiliary.type (.sort 1) = true := by
  native_decide

theorem leanFlatAuxiliaryType : leanFlatAuxiliary.type = .sort 1 :=
  ExactLeanSyntax.expr_eq_of_check leanFlatAuxiliaryTypeNative

private theorem leanFlatNodeTypeNative :
    ExactLeanSyntax.exprCheck leanFlatNode.type
      (.forallE `value leanAuxiliaryExpr leanTreeExpr .default) = true := by
  native_decide

/-- The outer nested application has been replaced by the generated
auxiliary constant. -/
theorem leanFlatNodeType :
    leanFlatNode.type =
      .forallE `value leanAuxiliaryExpr leanTreeExpr .default :=
  ExactLeanSyntax.expr_eq_of_check leanFlatNodeTypeNative

def leanFlatWrapBinderName : Lean.Name := leanFlatWrap.type.bindingName!

private theorem leanFlatWrapTypeNative :
    ExactLeanSyntax.exprCheck leanFlatWrap.type
      (.forallE leanFlatWrapBinderName leanTreeExpr leanAuxiliaryExpr
        .default) = true := by
  native_decide

/-- The copied `Box.wrap` constructor has its parameter specialized to
`Tree`; its field is the original family and its result is the generated
auxiliary. -/
theorem leanFlatWrapType :
    leanFlatWrap.type =
      .forallE leanFlatWrapBinderName leanTreeExpr leanAuxiliaryExpr
        .default :=
  ExactLeanSyntax.expr_eq_of_check leanFlatWrapTypeNative

private theorem leanAuxiliarySourceNative :
    (match leanAuxiliarySource? leanAuxiliaryName with
      | some source => ExactLeanSyntax.exprCheck source leanNestedDomain
      | none => false) = true := by
  native_decide

/-- The producer's reverse map identifies the fresh flat family with exactly
the pre-flattening `Box Tree` specialization. -/
theorem leanAuxiliarySource :
    leanAuxiliarySource? leanAuxiliaryName = some leanNestedDomain := by
  have success := leanAuxiliarySourceNative
  generalize hsource : leanAuxiliarySource? leanAuxiliaryName = source?
    at success ⊢
  cases source? with
  | none => simp_all
  | some source =>
      simp only at success
      rw [ExactLeanSyntax.expr_eq_of_check success]

/-! ## Constructor-validation candidate -/

/-- Exact statistics of the two-member flattened mutual block. -/
def leanFlatStats : Lean4Lean.AddInductive.InductiveStats where
  levels := []
  resultLevel := .succ .zero
  nindices := #[0, 0]
  indConsts := #[leanTreeExpr, leanAuxiliaryExpr]
  params := #[]
  isNotZero := true

def leanFlatFamilyContext : Lean4Lean.AddInductive.Context where
  env := leanNestedBaseEnv
  lparams := []
  safety := .safe
  allowPrimitive := false
  fuel := { ({} : Lean4Lean.FuelConfig) with
    inductiveFuel := positivityFuel }

def leanFlatDeclarationOutcome :=
  Lean4Lean.AddInductive.declareInductiveTypes leanFlatStats 0
    leanFlatTypes.toArray 1 false leanFlatFamilyContext

def leanFlatConstructorEnv : Lean.Kernel.Environment :=
  match leanFlatDeclarationOutcome with
  | .ok environment => environment
  | .error _ => leanNestedBaseEnv

def leanFlatConstructorContext : Lean4Lean.AddInductive.Context :=
  { leanFlatFamilyContext with env := leanFlatConstructorEnv }

private theorem leanFlatDeclarationSucceededNative :
    (match leanFlatDeclarationOutcome with
      | .ok _ => true
      | .error _ => false) = true := by
  native_decide

/-- Both exact flat families are installed before constructor validation,
matching the staging of `AddInductive.run`. -/
theorem leanFlatDeclarationRun :
    leanFlatDeclarationOutcome = .ok leanFlatConstructorEnv := by
  have success := leanFlatDeclarationSucceededNative
  unfold leanFlatConstructorEnv
  generalize houtcome : leanFlatDeclarationOutcome = outcome at success ⊢
  cases outcome <;> simp_all

private theorem leanTreeTargetNative :
    Lean4Lean.AddInductive.isValidIndApp? leanFlatStats leanTreeExpr =
      some 0 := by
  native_decide

theorem leanTreeTarget :
    Lean4Lean.AddInductive.isValidIndApp? leanFlatStats leanTreeExpr =
      some 0 := leanTreeTargetNative

private theorem leanAuxiliaryTargetNative :
    Lean4Lean.AddInductive.isValidIndApp? leanFlatStats leanAuxiliaryExpr =
      some 1 := by
  native_decide

theorem leanAuxiliaryTarget :
    Lean4Lean.AddInductive.isValidIndApp? leanFlatStats leanAuxiliaryExpr =
      some 1 := leanAuxiliaryTargetNative

private theorem leanTreeOccursNative :
    Lean4Lean.AddInductive.hasIndOcc leanFlatStats.indConsts leanTreeExpr =
      true := by
  native_decide

theorem leanTreeOccurs :
    Lean4Lean.AddInductive.hasIndOcc leanFlatStats.indConsts leanTreeExpr =
      true := leanTreeOccursNative

private theorem leanAuxiliaryOccursNative :
    Lean4Lean.AddInductive.hasIndOcc leanFlatStats.indConsts
      leanAuxiliaryExpr = true := by
  native_decide

theorem leanAuxiliaryOccurs :
    Lean4Lean.AddInductive.hasIndOcc leanFlatStats.indConsts
      leanAuxiliaryExpr = true := leanAuxiliaryOccursNative

/-! ## Exact cross-representation target certificate -/

def nestedCandidateNameOf (address : Address) : Option Lean.Name :=
  if address == treeId.addr then some leanTreeName
  else if address == boxId.addr then some ``LeanBox
  else none

def nestedClosedFVarMatches (_ : FVarId) (_ : Lean.FVarId) : Bool := false

private theorem nestedDomainCandidateCheckNative :
    CandidateSyntax.check nestedCandidateNameOf nestedClosedFVarMatches []
      nestedDomain leanNestedDomain = true := by
  native_decide

/-- Before flattening, the actual ingressed Ix domain and Lean4Lean's nested
source have the same constant/application syntax. -/
theorem nestedDomainCandidateSyntax :
    CandidateSyntaxRel nestedCandidateNameOf
      (fun ixId leanId => nestedClosedFVarMatches ixId leanId = true)
      (fun ixLevel leanLevel =>
        CandidateSyntax.levelMatches [] ixLevel leanLevel = true)
      nestedDomain leanNestedDomain :=
  CandidateSyntax.rel_of_check nestedDomainCandidateCheckNative

private theorem treeCandidateCheckNative :
    CandidateSyntax.check nestedCandidateNameOf nestedClosedFVarMatches []
      treeExpr leanTreeExpr = true := by
  native_decide

/-- The recursively checked field of the copied auxiliary constructor is the
original `Tree` family in both representations.  This is the exact-syntax
link consumed by the inner positivity transport. -/
theorem treeCandidateSyntax :
    CandidateSyntaxRel nestedCandidateNameOf
      (fun ixId leanId => nestedClosedFVarMatches ixId leanId = true)
      (fun ixLevel leanLevel =>
        CandidateSyntax.levelMatches [] ixLevel leanLevel = true)
      treeExpr leanTreeExpr :=
  CandidateSyntax.rel_of_check treeCandidateCheckNative

/-- Evidence that the target accepted by Lean4Lean is exactly the auxiliary
requested and retained by production Ix positivity/flat-block construction.

The certificate keeps both representations visible: candidate syntax first
identifies `Box Tree`, the Lean4Lean eliminator's reverse map identifies the
fresh target with that source, and the Ix request/header/key facts identify
the physical flat member with the same specialization. -/
structure NestedAuxiliaryCandidateTarget : Prop where
  produced : positivityRequest.ProducedBy (positivityFuel - 1) boxId #[]
    #[treeExpr] groups rootGroup.addrs #[treeId.addr] checkerMethods
      nestedWhnfAfter positivityAfter
  fresh : ∃ concrete afterLookup,
    TcM.getConst positivityRequest.id nestedWhnfAfter =
        .ok concrete afterLookup ∧
      concrete.NestedPositiveHeader positivityRequest.nParams
        positivityRequest.nIndices positivityRequest.levels
        positivityRequest.block positivityRequest.ctors ∧
      CompleteFreshNestedPositivityTrace (positivityFuel - 1)
        positivityRequest.universes positivityRequest.arguments groups
        #[treeId.addr] positivityRequest.nParams positivityRequest.block
        positivityRequest.ctors checkerMethods afterLookup positivityAfter
  header : NestedAuxiliaryHeaderRel positivityRequest flatRequest
  present : FlatAuxPresent positivityRequest.key builtFlat
  sourceSyntax : CandidateSyntaxRel nestedCandidateNameOf
    (fun ixId leanId => nestedClosedFVarMatches ixId leanId = true)
    (fun ixLevel leanLevel =>
      CandidateSyntax.levelMatches [] ixLevel leanLevel = true)
    nestedDomain leanNestedDomain
  eliminatedSource :
    leanAuxiliarySource? leanAuxiliaryName = some leanNestedDomain
  outerRewrite : leanFlatNode.type =
    .forallE `value leanAuxiliaryExpr leanTreeExpr .default
  occurs : Lean4Lean.AddInductive.hasIndOcc leanFlatStats.indConsts
    leanAuxiliaryExpr = true
  valid : Lean4Lean.AddInductive.isValidIndApp? leanFlatStats
    leanAuxiliaryExpr = some 1

/-- The concrete nested fixture closes every field of the cross-representation
target certificate without an `InductiveOracle` or a caller-supplied target
trace. -/
theorem nestedAuxiliaryCandidateTarget : NestedAuxiliaryCandidateTarget := by
  rcases nestedAuxiliaryReachability with
    ⟨produced, fresh, auxSeen, flatRun, sound, exact, keyMember, header,
      present⟩
  exact {
    produced
    fresh
    header
    present
    sourceSyntax := nestedDomainCandidateSyntax
    eliminatedSource := leanAuxiliarySource
    outerRewrite := leanFlatNodeType
    occurs := leanAuxiliaryOccurs
    valid := leanAuxiliaryTarget }

end Ix.Tc.NestedRecursiveFixture
