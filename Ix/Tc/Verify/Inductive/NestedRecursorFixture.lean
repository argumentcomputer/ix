import Ix.CompileDriver
import Ix.Tc.Verify.Inductive.NestedAdmission

/-!
# Production nested-recursion block for `LeanTree`

The source transaction checks the hand-retained compiler-shaped
`LeanBox`/`LeanTree` family blocks.  This module independently runs the
production aux-aware compiler over the corresponding kernel metadata and
extracts its generated two-recursor block.  Exact address equalities tie the
compiled source projections back to the already checked physical families;
the recursor block is then ingressed and checked after that family block.
-/

namespace Ix.Tc.NestedRecursiveFixture

open InductiveConcreteFixture

local instance nestedRecursorAddressDecidableEq : DecidableEq Address :=
  AnonStructural.addressDecidableEq

local instance nestedRecursorKIdDecidableEq : DecidableEq (KId .anon) :=
  AnonStructural.idDecidableEq

local instance nestedRecursorKConstDecidableEq :
    DecidableEq (KConst .anon) :=
  AnonStructural.constDecidableEq

/-! ## Full production compilation from retained kernel metadata -/

def nestedCompilerConstants : Array Lean.ConstantInfo :=
  #[kernelInductInfo% LeanBox, kernelCtorInfo% LeanBox.wrap,
    kernelInductInfo% LeanTree, kernelCtorInfo% LeanTree.node,
    kernelRecInfo% LeanTree.rec, kernelRecInfo% LeanTree.rec_1]

def nestedCanonicalConstants : Array (Ix.Name × Ix.ConstantInfo) :=
  (StateT.run (nestedCompilerConstants.mapM fun info => do
    let canonical ← Ix.CanonM.canonConst info
    pure (canonical.getCnst.name, canonical)) {}).1

def nestedCompilerEnvironment : Ix.Environment :=
  { consts := nestedCanonicalConstants.foldl (init := {}) fun constants row =>
      constants.insert row.1 row.2 }

def nestedCompilerReferences : Ix.Map Ix.Name (Ix.Set Ix.Name) :=
  nestedCanonicalConstants.foldl (init := {}) fun references row =>
    let (out, _) :=
      Ix.GraphM.run { consts := {} } .init (Ix.graphConst row.2)
    references.insert row.1 out

def nestedCompilerBlocks : Ix.CondensedBlocks :=
  Ix.CondenseM.run nestedCompilerReferences

def nestedCompilerOutcome :=
  Ix.CompileM.compileEnvAux nestedCompilerEnvironment nestedCompilerBlocks

def nestedCompilerResult : Ixon.Env × Nat × Ix.CompileM.CompileEnv :=
  match nestedCompilerOutcome with
  | .ok result => result
  | .error _ => ({}, 0, Ix.CompileM.CompileEnv.new nestedCompilerEnvironment)

def nestedCompiledEnv : Ixon.Env := nestedCompilerResult.1
def nestedCompiledState : Ix.CompileM.CompileEnv := nestedCompilerResult.2.2

private theorem nestedCompilerSucceededNative :
    (match nestedCompilerOutcome with
      | .ok _ => true
      | .error _ => false) = true := by
  native_decide

theorem nestedCompilerRun :
    nestedCompilerOutcome = .ok nestedCompilerResult := by
  have success := nestedCompilerSucceededNative
  unfold nestedCompilerResult
  generalize houtcome : nestedCompilerOutcome = outcome at success ⊢
  cases outcome <;> simp_all

private theorem nestedCompilerGroundedNative :
    nestedCompiledState.ungrounded.isEmpty = true := by
  native_decide

theorem nestedCompilerGrounded :
    nestedCompiledState.ungrounded.isEmpty = true :=
  nestedCompilerGroundedNative

def nestedTreeCompilerName : Ix.Name := Ix.Name.fromLeanName ``LeanTree
def nestedNodeCompilerName : Ix.Name := Ix.Name.fromLeanName ``LeanTree.node
def nestedTreeRecCompilerName : Ix.Name :=
  Ix.Name.fromLeanName ``LeanTree.rec
def nestedTreeRecOneCompilerName : Ix.Name :=
  Ix.Name.fromLeanName ``LeanTree.rec_1

def compiledTreeId : KId .anon :=
  ⟨(nestedCompiledEnv.getAddr? nestedTreeCompilerName).getD default, ()⟩

def compiledNodeId : KId .anon :=
  ⟨(nestedCompiledEnv.getAddr? nestedNodeCompilerName).getD default, ()⟩

def treeRecId : KId .anon :=
  ⟨(nestedCompiledEnv.getAddr? nestedTreeRecCompilerName).getD default, ()⟩

def treeRecOneId : KId .anon :=
  ⟨(nestedCompiledEnv.getAddr? nestedTreeRecOneCompilerName).getD default, ()⟩

def recursorProjectionBlock? (id : KId .anon) : Option Address := do
  let projection ← nestedCompiledEnv.getConst? id.addr
  match projection.info with
  | .rPrj value => some value.block
  | _ => none

def recursorBlockAddress : Address :=
  (recursorProjectionBlock? treeRecId).getD default

def recursorBlockId : KId .anon := ⟨recursorBlockAddress, ()⟩

def recursorBlockConstant : Ixon.Constant :=
  (nestedCompiledEnv.getConst? recursorBlockAddress).getD default

def recursorMembers : Array (KId .anon) := #[treeRecId, treeRecOneId]

def nestedCompiledRecursorBreadth : Bool :=
  match recursorBlockConstant.info with
  | .muts members =>
      members.size == 2 &&
        members.all (fun member => member matches .recr _) &&
        members.foldl (init := 0) (fun count member =>
          match member with
          | .recr recursor => count + recursor.rules.size
          | _ => count) == 2
  | _ => false

/-- The aux-aware compiler reproduces the exact already-ingressed source
addresses and places both restored recursors in one generated block. -/
structure NestedCompiledIdentityFacts : Prop where
  tree : compiledTreeId = treeId
  node : compiledNodeId = nodeId
  primaryPresent :
    nestedCompiledEnv.getAddr? nestedTreeRecCompilerName = some treeRecId.addr
  dependencyPresent :
    nestedCompiledEnv.getAddr? nestedTreeRecOneCompilerName =
      some treeRecOneId.addr
  primaryBlock : recursorProjectionBlock? treeRecId = some recursorBlockAddress
  dependencyBlock :
    recursorProjectionBlock? treeRecOneId = some recursorBlockAddress
  breadth : nestedCompiledRecursorBreadth = true

private theorem nestedCompiledIdentityFactsNative :
    NestedCompiledIdentityFacts := by
  constructor <;> native_decide

theorem nestedCompiledIdentityFacts : NestedCompiledIdentityFacts :=
  nestedCompiledIdentityFactsNative

/-! ## Generated block ingress -/

def recursorIngressOutcome :=
  ingressAnonBlockWithTrace nestedCompiledEnv recursorBlockConstant
    recursorBlockAddress treeIngressAfter

def recursorIngressResult : AnonBlockIngressTrace :=
  match recursorIngressOutcome with
  | .ok result _ => result
  | .error _ _ => default

def recursorIngressAfter : AnonEnv :=
  match recursorIngressOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem recursorIngressSucceededNative :
    (match recursorIngressOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

theorem recursorIngressRun :
    recursorIngressOutcome = .ok recursorIngressResult recursorIngressAfter := by
  have success := recursorIngressSucceededNative
  unfold recursorIngressResult recursorIngressAfter
  generalize houtcome : recursorIngressOutcome = outcome at success ⊢
  cases outcome <;> simp_all

def recursorIngressExecution : AnonBlockIngressSuccessTrace nestedCompiledEnv
    recursorBlockConstant recursorBlockAddress treeIngressAfter
      recursorIngressAfter recursorIngressResult :=
  AnonBlockIngressSuccessTrace.of_run recursorIngressRun

private theorem recursorEntryIdsNative :
    recursorIngressResult.allEntries.map (·.1) = recursorMembers := by
  native_decide

theorem recursorEntryIds :
    recursorIngressResult.allEntries.map (·.1) = recursorMembers :=
  recursorEntryIdsNative

private theorem recursorEntriesUniqueNative :
    EntryKeysUnique recursorIngressResult.allEntries := by
  unfold EntryKeysUnique
  native_decide

theorem recursorEntriesUnique :
    EntryKeysUnique recursorIngressResult.allEntries :=
  recursorEntriesUniqueNative

def treeRecConcrete : KConst .anon :=
  (recursorIngressAfter.get? treeRecId).getD default

def treeRecOneConcrete : KConst .anon :=
  (recursorIngressAfter.get? treeRecOneId).getD default

private theorem treeRecLookupNative :
    recursorIngressAfter.get? treeRecId = some treeRecConcrete := by
  native_decide

theorem treeRecLookup :
    recursorIngressAfter.get? treeRecId = some treeRecConcrete :=
  treeRecLookupNative

private theorem treeRecOneLookupNative :
    recursorIngressAfter.get? treeRecOneId = some treeRecOneConcrete := by
  native_decide

theorem treeRecOneLookup :
    recursorIngressAfter.get? treeRecOneId = some treeRecOneConcrete :=
  treeRecOneLookupNative

/-! ## Production family/recursor checker sequence -/

def nestedRecursorCheckerInitial : TcState .anon :=
  { TcState.ofEnvAnon recursorIngressAfter with
    recFuel := checkerFuel
    fuelBudget := checkerFuel }

private theorem nestedRecursorFamilyBlockLoadedNative :
    nestedRecursorCheckerInitial.env.getBlock? treeBlockId =
      some nestedFamilyMembers := by
  native_decide

theorem nestedRecursorFamilyBlockLoaded :
    nestedRecursorCheckerInitial.env.getBlock? treeBlockId =
      some nestedFamilyMembers :=
  nestedRecursorFamilyBlockLoadedNative

private theorem nestedRecursorBlockLoadedNative :
    nestedRecursorCheckerInitial.env.getBlock? recursorBlockId =
      some recursorMembers := by
  native_decide

theorem nestedRecursorBlockLoaded :
    nestedRecursorCheckerInitial.env.getBlock? recursorBlockId =
      some recursorMembers :=
  nestedRecursorBlockLoadedNative

def nestedRecursorFamilyOutcome :=
  (RecM.checkInductiveBlock treeBlockId nestedFamilyMembers).run
    checkerMethods nestedRecursorCheckerInitial

def nestedRecursorFamilyAfter : TcState .anon :=
  match nestedRecursorFamilyOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem nestedRecursorFamilySucceededNative :
    (match nestedRecursorFamilyOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

theorem nestedRecursorFamilyRun :
    (RecM.checkInductiveBlock treeBlockId nestedFamilyMembers).run
      checkerMethods nestedRecursorCheckerInitial =
        .ok () nestedRecursorFamilyAfter := by
  have success := nestedRecursorFamilySucceededNative
  unfold nestedRecursorFamilyAfter
  generalize houtcome : nestedRecursorFamilyOutcome = outcome at success ⊢
  cases outcome <;> simp_all [nestedRecursorFamilyOutcome]

def nestedRecursorKernelOutcome :=
  (RecM.checkRecursorBlock recursorBlockId recursorMembers).run
    checkerMethods nestedRecursorFamilyAfter

def nestedRecursorKernelAfter : TcState .anon :=
  match nestedRecursorKernelOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem nestedRecursorKernelSucceededNative :
    (match nestedRecursorKernelOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

theorem nestedRecursorKernelRun :
    (RecM.checkRecursorBlock recursorBlockId recursorMembers).run
      checkerMethods nestedRecursorFamilyAfter =
        .ok () nestedRecursorKernelAfter := by
  have success := nestedRecursorKernelSucceededNative
  unfold nestedRecursorKernelAfter
  generalize houtcome : nestedRecursorKernelOutcome = outcome at success ⊢
  cases outcome <;> simp_all [nestedRecursorKernelOutcome]

end Ix.Tc.NestedRecursiveFixture
