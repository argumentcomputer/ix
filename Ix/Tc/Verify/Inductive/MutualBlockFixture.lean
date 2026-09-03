import Ix.CompileDriver
import Ix.Tc.Verify.Inductive.ConcreteFixture
import Ix.Tc.Verify.Inductive.MutualBlockCertificate

/-!
# Physical mutual `Tree`/`TreeList` fixture

This module compiles the exact kernel metadata already retained by the
Lean4Lean mutual-inductive replay.  It therefore exercises the same pure Ix
compiler used by production instead of maintaining a second handwritten Ixon
encoding of the two families, five constructors, two recursors, and five
rules.

The two compiler results are stored with their production projection layout
and ingressed in dependency order.  The resulting declarations and block
tables are the physical inputs for the mutual checker and semantic-admission
links built in the following modules.
-/

namespace Ix.Tc.MutualTreeFixture

open Lean4Lean.MutualInductiveFixtures
open Lean4Lean.MutualInductiveReplayFixtures
open InductiveConcreteFixture

local instance mutualAnonKIdDecidableEq : DecidableEq (KId .anon) :=
  fun left right =>
    if h : left == right then
      .isTrue (eq_of_beq h)
    else
      .isFalse fun equality => h (by cases equality; exact beq_self_eq_true left)

/-! ## Exact retained kernel input -/

/-- The complete source inventory needed by the two physical compiler blocks.
Constructors remain ordinary environment entries; families and recursors are
the members of their respective mutual SCCs. -/
def leanConstants : Array Lean.ConstantInfo :=
  #[treeKernelInfo, treeListKernelInfo,
    treeLeafKernelInfo, treeNodeKernelInfo, treeBranchKernelInfo,
    treeListNilKernelInfo, treeListConsKernelInfo,
    treeRecKernelInfo, treeListRecKernelInfo]

/-- Canonicalize the retained Lean metadata with one shared canonicalization
state, exactly as the production Lean-to-Ix pipeline does. -/
def canonicalConstants : Array (Ix.Name × Ix.ConstantInfo) :=
  (StateT.run (leanConstants.mapM fun info => do
    let canonical ← Ix.CanonM.canonConst info
    pure (canonical.getCnst.name, canonical)) {}).1

def sourceEnvironment : Ix.Environment :=
  { consts := canonicalConstants.foldl (init := {}) fun constants row =>
      constants.insert row.1 row.2 }

def treeName : Ix.Name := Ix.Name.fromLeanName treeKernelInfo.name
def treeListName : Ix.Name := Ix.Name.fromLeanName treeListKernelInfo.name
def treeLeafName : Ix.Name := Ix.Name.fromLeanName treeLeafKernelInfo.name
def treeNodeName : Ix.Name := Ix.Name.fromLeanName treeNodeKernelInfo.name
def treeBranchName : Ix.Name := Ix.Name.fromLeanName treeBranchKernelInfo.name
def treeListNilName : Ix.Name :=
  Ix.Name.fromLeanName treeListNilKernelInfo.name
def treeListConsName : Ix.Name :=
  Ix.Name.fromLeanName treeListConsKernelInfo.name
def treeRecName : Ix.Name := Ix.Name.fromLeanName treeRecKernelInfo.name
def treeListRecName : Ix.Name :=
  Ix.Name.fromLeanName treeListRecKernelInfo.name

def familyNames : Ix.Set Ix.Name :=
  ({} : Ix.Set Ix.Name).insert treeName |>.insert treeListName

def recursorNames : Ix.Set Ix.Name :=
  ({} : Ix.Set Ix.Name).insert treeRecName |>.insert treeListRecName

/-! ## Production pure compilation -/

def initialCompileEnvironment : Ix.CompileM.CompileEnv :=
  Ix.CompileM.CompileEnv.new sourceEnvironment

/-- The aux-aware production block compiler.  Besides the primary family
block, this regenerates the canonical recursor block in the family block's
class order; compiling the source recursor SCC independently would allow its
structural sort to choose a different, checker-incompatible permutation. -/
def familyAuxCompileOutcome :=
  Ix.CompileM.runBlockWithAux initialCompileEnvironment familyNames treeName

def familyAuxCompileSucceeded : Bool :=
  match familyAuxCompileOutcome with
  | .ok _ => true
  | .error _ => false

private theorem familyAuxCompileSucceededNative :
    familyAuxCompileSucceeded = true := by
  native_decide

theorem familyAuxCompileSucceeded_eq : familyAuxCompileSucceeded = true :=
  familyAuxCompileSucceededNative

def familyAuxCompiled :=
  match familyAuxCompileOutcome with
  | .ok result => result
  | .error _ => default

theorem familyAuxCompileRun :
    familyAuxCompileOutcome = .ok familyAuxCompiled := by
  have success := familyAuxCompileSucceeded_eq
  unfold familyAuxCompileSucceeded at success
  unfold familyAuxCompiled
  generalize houtcome : familyAuxCompileOutcome = outcome at success ⊢
  cases outcome <;> simp_all

def familyAuxBlockResult : Ix.CompileM.BlockResult := familyAuxCompiled.1
def familyAuxBlockState : Ix.CompileM.BlockState := familyAuxCompiled.2.1

def familyBlockResult : Ix.CompileM.BlockResult := familyAuxBlockResult
def familyBlockConstant : Ixon.Constant := familyBlockResult.block

/-- Find one constant stored by the aux-aware compiler tail. -/
def auxConstant? (address : Address) : Option Ixon.Constant :=
  familyAuxBlockState.auxConsts.findSome? fun row =>
    if row.1 == address then some row.2 else none

/-- The generated recursor name resolves to a projection whose parent is the
canonical two-recursor block. -/
def recursorBlockAddress? : Option Address := do
  let projectionAddress ← familyAuxBlockState.auxNameToAddr.get? treeRecName
  let projection ← auxConstant? projectionAddress
  match projection.info with
  | .rPrj recursorProjection => some recursorProjection.block
  | _ => none

def recursorBlockConstant? : Option Ixon.Constant :=
  recursorBlockAddress?.bind auxConstant?

private theorem recursorBlockGeneratedNative :
    recursorBlockConstant?.isSome = true := by
  native_decide

theorem recursorBlockGenerated : recursorBlockConstant?.isSome = true :=
  recursorBlockGeneratedNative

def recursorBlockConstant : Ixon.Constant :=
  recursorBlockConstant?.getD default

/-! ## Exact compiled breadth -/

private def familyCompiledBreadth : Bool :=
  match familyBlockConstant.info with
  | .muts members =>
      members.size == 2 &&
        members.all (fun member => member matches .indc _) &&
        members.foldl (init := 0) (fun count member =>
          match member with
          | .indc ind => count + ind.ctors.size
          | _ => count) == 5 &&
        familyBlockResult.projections.size == 7
  | _ => false

private theorem familyCompiledBreadthNative :
    familyCompiledBreadth = true := by
  native_decide

theorem familyCompiledBreadth_eq : familyCompiledBreadth = true :=
  familyCompiledBreadthNative

private def recursorCompiledBreadth : Bool :=
  match recursorBlockConstant.info with
  | .muts members =>
      members.size == 2 &&
        members.all (fun member =>
          match member with
          | .recr recursor =>
              recursor.motives == 2 && recursor.minors == 5
          | _ => false) &&
        members.foldl (init := 0) (fun count member =>
          match member with
          | .recr recursor => count + recursor.rules.size
          | _ => count) == 5 &&
        (familyAuxBlockState.auxNameToAddr.get? treeRecName).isSome &&
        (familyAuxBlockState.auxNameToAddr.get? treeListRecName).isSome
  | _ => false

private theorem recursorCompiledBreadthNative :
    recursorCompiledBreadth = true := by
  native_decide

theorem recursorCompiledBreadth_eq : recursorCompiledBreadth = true :=
  recursorCompiledBreadthNative

/-! ## Name-address linkage from compiler projections -/

def projectionAddress? (result : Ix.CompileM.BlockResult)
    (name : Ix.Name) : Option Address :=
  result.projections.findSome? fun row =>
    if row.1 == name then some (Address.blake3 (Ixon.ser row.2.1)) else none

def projectionId (result : Ix.CompileM.BlockResult)
    (name : Ix.Name) : KId .anon :=
  ⟨(projectionAddress? result name).getD default, ()⟩

def treeId : KId .anon := projectionId familyBlockResult treeName
def treeListId : KId .anon := projectionId familyBlockResult treeListName
def treeLeafId : KId .anon := projectionId familyBlockResult treeLeafName
def treeNodeId : KId .anon := projectionId familyBlockResult treeNodeName
def treeBranchId : KId .anon := projectionId familyBlockResult treeBranchName
def treeListNilId : KId .anon :=
  projectionId familyBlockResult treeListNilName
def treeListConsId : KId .anon :=
  projectionId familyBlockResult treeListConsName
def treeRecId : KId .anon :=
  ⟨(familyAuxBlockState.auxNameToAddr.get? treeRecName).getD default, ()⟩
def treeListRecId : KId .anon :=
  ⟨(familyAuxBlockState.auxNameToAddr.get? treeListRecName).getD default, ()⟩

private def allNamedProjectionsPresent : Bool :=
  [projectionAddress? familyBlockResult treeName,
    projectionAddress? familyBlockResult treeListName,
    projectionAddress? familyBlockResult treeLeafName,
    projectionAddress? familyBlockResult treeNodeName,
    projectionAddress? familyBlockResult treeBranchName,
    projectionAddress? familyBlockResult treeListNilName,
    projectionAddress? familyBlockResult treeListConsName,
    familyAuxBlockState.auxNameToAddr.get? treeRecName,
    familyAuxBlockState.auxNameToAddr.get? treeListRecName].all Option.isSome

private theorem allNamedProjectionsPresentNative :
    allNamedProjectionsPresent = true := by
  native_decide

theorem allNamedProjectionsPresent_eq :
    allNamedProjectionsPresent = true :=
  allNamedProjectionsPresentNative

/-! ## Compiler-shaped storage and dependency-ordered ingress -/

def familyStored : Ixon.Env × Address :=
  storeBlockWithProjections {} familyBlockConstant

def familyBlockAddress : Address := familyStored.2

def recursorStored : Ixon.Env × Address :=
  storeBlockWithProjections familyStored.1 recursorBlockConstant

def ixonEnvironment : Ixon.Env := recursorStored.1
def recursorBlockAddress : Address := recursorStored.2

def familyIngressOutcome :=
  ingressAnonBlockWithTrace ixonEnvironment familyBlockConstant
    familyBlockAddress ({} : AnonEnv)

def familyIngressResult : AnonBlockIngressTrace :=
  match familyIngressOutcome with
  | .ok result _ => result
  | .error _ _ => default

def familyIngressAfter : AnonEnv :=
  match familyIngressOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def familyIngressSucceeded : Bool :=
  match familyIngressOutcome with
  | .ok _ _ => true
  | .error _ _ => false

private theorem familyIngressSucceededNative :
    familyIngressSucceeded = true := by
  native_decide

theorem familyIngressSucceeded_eq : familyIngressSucceeded = true :=
  familyIngressSucceededNative

theorem familyIngressRun :
    familyIngressOutcome = .ok familyIngressResult familyIngressAfter := by
  have success := familyIngressSucceeded_eq
  unfold familyIngressSucceeded at success
  unfold familyIngressResult familyIngressAfter
  generalize houtcome : familyIngressOutcome = outcome at success ⊢
  cases outcome <;> simp_all

theorem familyIngressExecution : AnonBlockIngressSuccessTrace ixonEnvironment
    familyBlockConstant familyBlockAddress {} familyIngressAfter
      familyIngressResult :=
  AnonBlockIngressSuccessTrace.of_run familyIngressRun

def recursorIngressOutcome :=
  ingressAnonBlockWithTrace ixonEnvironment recursorBlockConstant
    recursorBlockAddress familyIngressAfter

def recursorIngressResult : AnonBlockIngressTrace :=
  match recursorIngressOutcome with
  | .ok result _ => result
  | .error _ _ => default

def recursorIngressAfter : AnonEnv :=
  match recursorIngressOutcome with
  | .ok _ after => after
  | .error _ failed => failed

def recursorIngressSucceeded : Bool :=
  match recursorIngressOutcome with
  | .ok _ _ => true
  | .error _ _ => false

private theorem recursorIngressSucceededNative :
    recursorIngressSucceeded = true := by
  native_decide

theorem recursorIngressSucceeded_eq : recursorIngressSucceeded = true :=
  recursorIngressSucceededNative

theorem recursorIngressRun :
    recursorIngressOutcome =
      .ok recursorIngressResult recursorIngressAfter := by
  have success := recursorIngressSucceeded_eq
  unfold recursorIngressSucceeded at success
  unfold recursorIngressResult recursorIngressAfter
  generalize houtcome : recursorIngressOutcome = outcome at success ⊢
  cases outcome <;> simp_all

theorem recursorIngressExecution : AnonBlockIngressSuccessTrace ixonEnvironment
    recursorBlockConstant recursorBlockAddress familyIngressAfter
      recursorIngressAfter recursorIngressResult :=
  AnonBlockIngressSuccessTrace.of_run recursorIngressRun

/-! ## Retained physical identities -/

def familyBlockId : KId .anon := ⟨familyBlockAddress, ()⟩
def recursorBlockId : KId .anon := ⟨recursorBlockAddress, ()⟩

def familyMembers : Array (KId .anon) :=
  familyIngressResult.allEntries.map (·.1)

def recursorMembers : Array (KId .anon) :=
  recursorIngressResult.allEntries.map (·.1)

theorem familyMembers_eq : familyMembers =
    #[treeListId, treeListNilId, treeListConsId,
      treeId, treeLeafId, treeNodeId, treeBranchId] := by
  native_decide

theorem recursorMembers_eq :
    recursorMembers = #[treeListRecId, treeRecId] := by
  native_decide

private theorem familyMemberInventoryNative :
    familyMembers.size = 7 ∧
      treeId ∈ familyMembers ∧ treeListId ∈ familyMembers ∧
      treeLeafId ∈ familyMembers ∧ treeNodeId ∈ familyMembers ∧
      treeBranchId ∈ familyMembers ∧ treeListNilId ∈ familyMembers ∧
      treeListConsId ∈ familyMembers := by
  native_decide

theorem familyMemberInventory :
    familyMembers.size = 7 ∧
      treeId ∈ familyMembers ∧ treeListId ∈ familyMembers ∧
      treeLeafId ∈ familyMembers ∧ treeNodeId ∈ familyMembers ∧
      treeBranchId ∈ familyMembers ∧ treeListNilId ∈ familyMembers ∧
      treeListConsId ∈ familyMembers :=
  familyMemberInventoryNative

private theorem recursorMemberInventoryNative :
    recursorMembers.size = 2 ∧ treeRecId ∈ recursorMembers ∧
      treeListRecId ∈ recursorMembers := by
  native_decide

theorem recursorMemberInventory :
    recursorMembers.size = 2 ∧ treeRecId ∈ recursorMembers ∧
      treeListRecId ∈ recursorMembers :=
  recursorMemberInventoryNative

private theorem familyBlockLoadedNative :
    recursorIngressAfter.getBlock? familyBlockId = some familyMembers := by
  native_decide

theorem familyBlockLoaded :
    recursorIngressAfter.getBlock? familyBlockId = some familyMembers :=
  familyBlockLoadedNative

private theorem recursorBlockLoadedNative :
    recursorIngressAfter.getBlock? recursorBlockId = some recursorMembers := by
  native_decide

theorem recursorBlockLoaded :
    recursorIngressAfter.getBlock? recursorBlockId = some recursorMembers :=
  recursorBlockLoadedNative

end Ix.Tc.MutualTreeFixture
