import Ix.Tc.Verify.Inductive.ConcreteFixture
import Ix.Tc.Verify.Inductive.NestedAuxiliaryExpansion
import Ix.Tc.Verify.Ingress.AnonStructural

/-!
# Concrete nested-recursive reachability fixture

This fixture isolates the cross-stage E2c obligation with two compiler-shaped
anonymous blocks:

* `Box (α : Sort 1) : Sort 1`, with `wrap : α → Box α`;
* `Tree : Sort 1`, with `node : Box Tree → Tree`.

The same stored `Box Tree` occurrence is consumed first by production strict
positivity and then by production flat-block construction.  The headline
certificate identifies the request extracted from positivity with the exact
auxiliary member retained by the public builder.
-/

namespace Ix.Tc.NestedRecursiveFixture

open InductiveConcreteFixture

local instance anonAddressDecidableEq : DecidableEq Address :=
  AnonStructural.addressDecidableEq

local instance anonKIdDecidableEq : DecidableEq (KId .anon) :=
  AnonStructural.idDecidableEq

local instance anonKExprDecidableEq : DecidableEq (KExpr .anon) :=
  AnonStructural.exprDecidableEq

local instance anonKConstDecidableEq : DecidableEq (KConst .anon) :=
  AnonStructural.constDecidableEq

private structure FlatMemberView where
  id : Address
  isAux : Bool
  specParams : Array AnonStructural.Expr
  ownParams : UInt64
  nIndices : UInt64
  ctors : Array Address
  lvls : UInt64
  indUs : Array AnonStructural.Univ
  occurrenceUs : Array AnonStructural.Univ
  deriving DecidableEq

private def FlatMemberView.ofKernel
    (member : FlatBlockMember .anon) : FlatMemberView :=
  { id := member.id.addr
    isAux := member.isAux
    specParams := member.specParams.map AnonStructural.Expr.ofKernel
    ownParams := member.ownParams
    nIndices := member.nIndices
    ctors := member.ctors.map (·.addr)
    lvls := member.lvls
    indUs := member.indUs.map AnonStructural.Univ.ofKernel
    occurrenceUs := member.occurrenceUs.map AnonStructural.Univ.ofKernel }

private def FlatMemberView.toKernel
    (member : FlatMemberView) : FlatBlockMember .anon :=
  { id := ⟨member.id, ()⟩
    isAux := member.isAux
    specParams := member.specParams.map AnonStructural.Expr.toKernel
    ownParams := member.ownParams
    nIndices := member.nIndices
    ctors := member.ctors.map fun address => ⟨address, ()⟩
    lvls := member.lvls
    indUs := member.indUs.map AnonStructural.Univ.toKernel
    occurrenceUs := member.occurrenceUs.map AnonStructural.Univ.toKernel }

private theorem FlatMemberView.roundtrip (member : FlatBlockMember .anon) :
    (FlatMemberView.ofKernel member).toKernel = member := by
  cases member
  simp [FlatMemberView.ofKernel, FlatMemberView.toKernel, Array.map_map,
    Function.comp_def, AnonStructural.Expr.roundtrip,
    AnonStructural.Univ.roundtrip]

private def flatMemberDecidableEq :
    DecidableEq (FlatBlockMember .anon) :=
  AnonStructural.decidableEqOfRoundtrip FlatMemberView.ofKernel
    FlatMemberView.toKernel FlatMemberView.roundtrip

local instance : DecidableEq (FlatBlockMember .anon) :=
  flatMemberDecidableEq

/-! ## Compiler-shaped anonymous blocks -/

/-- `Box (α : Sort 1) : Sort 1`, with one constructor `wrap : α → Box α`. -/
def boxIxon : Ixon.Inductive :=
  ⟨false, 0, 1, 0, .all (.sort 0) (.sort 0),
    #[⟨false, 0, 0, 1, 1,
      .all (.sort 0)
        (.all (.var 0) (.app (.recur 0 #[]) (.var 1)))⟩]⟩

def boxBlockConstant : Ixon.Constant :=
  ⟨.muts #[.indc boxIxon], #[], #[], #[.succ .zero]⟩

def boxStored : Ixon.Env × Address :=
  storeBlockWithProjections {} boxBlockConstant

def boxIxonEnv : Ixon.Env := boxStored.1
def boxBlockAddress : Address := boxStored.2
def boxBlockId : KId .anon := ⟨boxBlockAddress, ()⟩
def boxId : KId .anon := ⟨indcProjAddr boxBlockAddress 0, ()⟩
def wrapId : KId .anon := ⟨ctorProjAddr boxBlockAddress 0 0, ()⟩

/-- `Tree : Sort 1`, with `node : Box Tree → Tree`. -/
def treeIxon : Ixon.Inductive :=
  ⟨false, 0, 0, 0, .sort 0,
    #[⟨false, 0, 0, 0, 1,
      .all
        (.app (.ref 0 #[]) (.recur 0 #[]))
        (.recur 0 #[])⟩]⟩

def treeBlockConstant : Ixon.Constant :=
  ⟨.muts #[.indc treeIxon], #[], #[boxId.addr], #[.succ .zero]⟩

def treeStored : Ixon.Env × Address :=
  storeBlockWithProjections boxIxonEnv treeBlockConstant

def treeIxonEnv : Ixon.Env := treeStored.1
def treeBlockAddress : Address := treeStored.2
def treeBlockId : KId .anon := ⟨treeBlockAddress, ()⟩
def treeId : KId .anon := ⟨indcProjAddr treeBlockAddress 0, ()⟩
def nodeId : KId .anon := ⟨ctorProjAddr treeBlockAddress 0 0, ()⟩

/-! ## Dependency-ordered anonymous ingress -/

def boxIngressOutcome :=
  ingressAnonBlockWithTrace treeIxonEnv boxBlockConstant boxBlockAddress
    ({} : AnonEnv)

def boxIngressResult : AnonBlockIngressTrace :=
  match boxIngressOutcome with
  | .ok result _ => result
  | .error _ _ => default

def boxIngressAfter : AnonEnv :=
  match boxIngressOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem boxIngressSucceededNative :
    (match boxIngressOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

theorem boxIngressRun :
    boxIngressOutcome = .ok boxIngressResult boxIngressAfter := by
  have success := boxIngressSucceededNative
  unfold boxIngressResult boxIngressAfter
  generalize houtcome : boxIngressOutcome = outcome at success ⊢
  cases outcome <;> simp_all

def boxIngressExecution : AnonBlockIngressSuccessTrace treeIxonEnv
    boxBlockConstant boxBlockAddress {} boxIngressAfter boxIngressResult :=
  AnonBlockIngressSuccessTrace.of_run boxIngressRun

def treeIngressOutcome :=
  ingressAnonBlockWithTrace treeIxonEnv treeBlockConstant treeBlockAddress
    boxIngressAfter

def treeIngressResult : AnonBlockIngressTrace :=
  match treeIngressOutcome with
  | .ok result _ => result
  | .error _ _ => default

def treeIngressAfter : AnonEnv :=
  match treeIngressOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem treeIngressSucceededNative :
    (match treeIngressOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

theorem treeIngressRun :
    treeIngressOutcome = .ok treeIngressResult treeIngressAfter := by
  have success := treeIngressSucceededNative
  unfold treeIngressResult treeIngressAfter
  generalize houtcome : treeIngressOutcome = outcome at success ⊢
  cases outcome <;> simp_all

def treeIngressExecution : AnonBlockIngressSuccessTrace treeIxonEnv
    treeBlockConstant treeBlockAddress boxIngressAfter treeIngressAfter
      treeIngressResult :=
  AnonBlockIngressSuccessTrace.of_run treeIngressRun

/-! ## Exact ingressed declarations and the shared nested occurrence -/

def boxConcrete : KConst .anon :=
  match treeIngressAfter.get? boxId with
  | some concrete => concrete
  | none => default

def wrapConcrete : KConst .anon :=
  match treeIngressAfter.get? wrapId with
  | some concrete => concrete
  | none => default

def treeConcrete : KConst .anon :=
  match treeIngressAfter.get? treeId with
  | some concrete => concrete
  | none => default

def nodeConcrete : KConst .anon :=
  match treeIngressAfter.get? nodeId with
  | some concrete => concrete
  | none => default

def treeExpr : KExpr .anon := KExpr.mkConst treeId #[]
def nestedDomain : KExpr .anon :=
  KExpr.mkApp (KExpr.mkConst boxId #[]) treeExpr

private def boxConcreteHeaderMatches : Bool :=
  match boxConcrete with
  | .indc (params := params) (indices := indices) (lvls := lvls)
      (block := block) (ctors := ctors) .. =>
    decide (params.toNat = 1 ∧ indices.toNat = 0 ∧ lvls.toNat = 0 ∧
      block = boxBlockId ∧ ctors = #[wrapId])
  | _ => false

private theorem boxConcreteHeaderMatchesNative :
    boxConcreteHeaderMatches = true := by
  native_decide

theorem boxConcreteHeader :
    boxConcrete.NestedPositiveHeader 1 0 0 boxBlockId #[wrapId] := by
  have hmatches := boxConcreteHeaderMatchesNative
  generalize hconcrete : boxConcrete = concrete at hmatches ⊢
  cases concrete <;>
    simp_all [boxConcreteHeaderMatches, KConst.NestedPositiveHeader]

private theorem nodeConcreteTypeNative :
    nodeConcrete = .ctor () () false 0 treeId 0 0 1
      (KExpr.mkAll () () nestedDomain treeExpr) := by
  native_decide

theorem nodeConcreteType :
    nodeConcrete = .ctor () () false 0 treeId 0 0 1
      (KExpr.mkAll () () nestedDomain treeExpr) :=
  nodeConcreteTypeNative

/-! ## Production positivity request -/

def checkerFuel : UInt64 := 1024
def checkerMethods : Methods .anon := methodsN checkerFuel.toNat
def checkerInitial : TcState .anon :=
  { TcState.ofEnvAnon treeIngressAfter with
    recFuel := checkerFuel
    fuelBudget := checkerFuel }

def rootGroup : PositivityGroup .anon :=
  { addrs := #[treeId.addr], params := #[], concreteUs := none }

def groups : Array (PositivityGroup .anon) := #[rootGroup]
def positivityFuel : Nat := 32

def positivityOutcome :=
  (RecM.checkPositivityDomainFuel positivityFuel nestedDomain groups
    #[treeId.addr]).run checkerMethods checkerInitial

def positivityAfter : TcState .anon :=
  match positivityOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem positivitySucceededNative :
    (match positivityOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

theorem positivityRun :
    (RecM.checkPositivityDomainFuel positivityFuel nestedDomain groups
      #[treeId.addr]).run checkerMethods checkerInitial =
        .ok () positivityAfter := by
  have success := positivitySucceededNative
  unfold positivityAfter
  generalize houtcome : positivityOutcome = outcome at success ⊢
  cases outcome <;> simp_all [positivityOutcome]

def nestedWhnfOutcome :=
  (RecM.whnf nestedDomain).run checkerMethods checkerInitial

def nestedWhnfResult : KExpr .anon :=
  match nestedWhnfOutcome with
  | .ok result _ => result
  | .error _ _ => default

def nestedWhnfAfter : TcState .anon :=
  match nestedWhnfOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem nestedWhnfSucceededNative :
    (match nestedWhnfOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

theorem nestedWhnfRun :
    (RecM.whnf nestedDomain).run checkerMethods checkerInitial =
      .ok nestedWhnfResult nestedWhnfAfter := by
  have success := nestedWhnfSucceededNative
  unfold nestedWhnfResult nestedWhnfAfter
  generalize houtcome : nestedWhnfOutcome = outcome at success ⊢
  cases outcome <;> simp_all [nestedWhnfOutcome]

private theorem nestedWhnfResultNative : nestedWhnfResult = nestedDomain := by
  native_decide

theorem nestedWhnfResult_eq : nestedWhnfResult = nestedDomain :=
  nestedWhnfResultNative

private theorem nestedMentionsRootNative :
    exprMentionsAnyAddr nestedDomain rootGroup.addrs = true := by
  native_decide

private theorem boxInactiveNative :
    rootGroup.addrs.contains boxId.addr = false := by
  native_decide

private theorem nestedSpineNative : nestedWhnfResult.collectSpine =
    (.const boxId #[] (KExpr.mkConst boxId #[] ()).info, #[treeExpr]) := by
  native_decide

theorem nestedActionRun :
    (RecM.checkNestedPositivityApplicationFuel (positivityFuel - 1) boxId #[]
      #[treeExpr] groups rootGroup.addrs #[treeId.addr]).run checkerMethods
        nestedWhnfAfter = .ok () positivityAfter := by
  have nested := RecM.checkPositivityDomainFuel_nested
    (fuel := positivityFuel - 1) (dom := nestedDomain)
    (w := nestedWhnfResult) (groups := groups)
    (activeAddrs := #[treeId.addr]) (methods := checkerMethods)
    (initial := checkerInitial) (afterWhnf := nestedWhnfAfter)
    (final := positivityAfter) (rootGroup := rootGroup)
    (id := boxId) (us := #[]) (args := #[treeExpr])
    (info := (KExpr.mkConst boxId #[] ()).info)
    (by rfl) nestedMentionsRootNative nestedWhnfRun nestedSpineNative
      boxInactiveNative
  simpa [positivityFuel] using nested positivityRun

def positivityRequest : NestedPositivityAuxiliaryRequest .anon :=
  { id := boxId
    universes := #[]
    arguments := #[treeExpr]
    nParams := 1
    nIndices := 0
    levels := 0
    block := boxBlockId
    ctors := #[wrapId] }

def flatRequest : NestedFlatAuxiliaryRequest .anon :=
  { id := boxId
    occurrenceUs := #[]
    specParams := #[treeExpr]
    ownParams := 1
    nIndices := 0
    ctors := #[wrapId]
    lvls := 0 }

theorem requestHeaderRelation :
    NestedAuxiliaryHeaderRel positivityRequest flatRequest := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem positivityCompleteTrace :
    CompleteNestedPositivityApplicationTrace (positivityFuel - 1) boxId #[]
      #[treeExpr] groups rootGroup.addrs #[treeId.addr] checkerMethods
        nestedWhnfAfter positivityAfter :=
  RecM.checkNestedPositivityApplicationFuel_complete nestedActionRun

def boxLookupOutcome := TcM.getConst boxId nestedWhnfAfter

def boxLookupConcrete : KConst .anon :=
  match boxLookupOutcome with
  | .ok concrete _ => concrete
  | .error _ _ => default

def boxLookupAfter : TcState .anon :=
  match boxLookupOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem boxLookupSucceededNative :
    (match boxLookupOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

theorem boxLookupRun :
    TcM.getConst boxId nestedWhnfAfter =
      .ok boxLookupConcrete boxLookupAfter := by
  have success := boxLookupSucceededNative
  unfold boxLookupConcrete boxLookupAfter
  generalize houtcome : boxLookupOutcome = outcome at success ⊢
  cases outcome <;> simp_all [boxLookupOutcome]

private theorem boxLookupConcreteNative : boxLookupConcrete = boxConcrete := by
  native_decide

theorem boxLookupConcrete_eq : boxLookupConcrete = boxConcrete :=
  boxLookupConcreteNative

/-- The canonical request is not reconstructed from the flat result: it is
the exact request extracted from the complete production positivity trace. -/
theorem positivityRequestProduced :
    positivityRequest.ProducedBy (positivityFuel - 1) boxId #[] #[treeExpr]
      groups rootGroup.addrs #[treeId.addr] checkerMethods nestedWhnfAfter
        positivityAfter := by
  rcases positivityCompleteTrace.producedRequest with ⟨request, produced⟩
  rcases produced with
    ⟨requestId, requestUniverses, requestArguments, concrete, afterLookup,
      lookup, header, argumentsSize, universesSize, branch⟩
  rw [requestId, boxLookupRun] at lookup
  cases lookup
  rw [boxLookupConcrete_eq] at header
  have canonicalHeader := boxConcreteHeader
  have requestHeader :
      request.nParams = 1 ∧ request.nIndices = 0 ∧ request.levels = 0 ∧
        request.block = boxBlockId ∧ request.ctors = #[wrapId] := by
    generalize hconcrete : boxConcrete = loaded at header canonicalHeader
    cases loaded <;>
      simp_all [KConst.NestedPositiveHeader]
  have requestEq : request = positivityRequest := by
    cases request
    simp_all [positivityRequest]
  cases requestEq
  have canonicalLookup :
      TcM.getConst boxId nestedWhnfAfter =
        .ok boxConcrete boxLookupAfter := by
    rw [boxLookupRun, boxLookupConcrete_eq]
  exact ⟨requestId, requestUniverses, requestArguments, boxConcrete,
    boxLookupAfter, canonicalLookup, header, argumentsSize, universesSize,
    branch⟩

private theorem positivityRequestAbsentNative :
    RecM.findNestedPositivityGroup? groups positivityRequest.id.addr
      positivityRequest.universes positivityRequest.arguments
        positivityRequest.nParams = none := by
  native_decide

/-- This fixture exercises the fresh-specialization branch and therefore
retains the recursively expanded external-constructor trace. -/
theorem positivityRequestFreshExpansion :
    ∃ concrete afterLookup,
      TcM.getConst positivityRequest.id nestedWhnfAfter =
          .ok concrete afterLookup ∧
        concrete.NestedPositiveHeader positivityRequest.nParams
          positivityRequest.nIndices positivityRequest.levels
          positivityRequest.block positivityRequest.ctors ∧
        CompleteFreshNestedPositivityTrace (positivityFuel - 1)
          positivityRequest.universes positivityRequest.arguments groups
          #[treeId.addr] positivityRequest.nParams positivityRequest.block
          positivityRequest.ctors checkerMethods afterLookup positivityAfter := by
  rcases positivityRequestProduced with
    ⟨_, _, _, concrete, afterLookup, lookup, header, _, _, branch⟩
  refine ⟨concrete, afterLookup, lookup, header, ?_⟩
  cases branch with
  | inl existing =>
      rcases existing with ⟨group, selected, _⟩
      rw [positivityRequestAbsentNative] at selected
      contradiction
  | inr fresh => exact fresh.2.2.2

/-! ## Production flat-block expansion -/

def flatBuildOutcome :=
  (RecM.buildFlatBlock #[treeId] 0 0).run checkerMethods checkerInitial

def builtFlat : Array (FlatBlockMember .anon) :=
  match flatBuildOutcome with
  | .ok result _ => result
  | .error _ _ => #[]

def flatBuildAfter : TcState .anon :=
  match flatBuildOutcome with
  | .ok _ after => after
  | .error _ failed => failed

private theorem flatBuildSucceededNative :
    (match flatBuildOutcome with
      | .ok _ _ => true
      | .error _ _ => false) = true := by
  native_decide

theorem flatBuildRun :
    (RecM.buildFlatBlock #[treeId] 0 0).run checkerMethods checkerInitial =
      .ok builtFlat flatBuildAfter := by
  have success := flatBuildSucceededNative
  unfold builtFlat flatBuildAfter
  generalize houtcome : flatBuildOutcome = outcome at success ⊢
  cases outcome <;> simp_all [flatBuildOutcome]

def expectedOriginal : FlatBlockMember .anon :=
  { id := treeId
    isAux := false
    specParams := #[]
    ownParams := 0
    nIndices := 0
    ctors := #[nodeId]
    lvls := 0
    indUs := #[]
    occurrenceUs := #[] }

def expectedAuxiliary : FlatBlockMember .anon := flatRequest.member #[]
def expectedFlat : Array (FlatBlockMember .anon) :=
  #[expectedOriginal, expectedAuxiliary]

private theorem builtFlatShapeNative : builtFlat = expectedFlat := by
  native_decide

theorem builtFlatShape : builtFlat = expectedFlat := builtFlatShapeNative

/-- The public builder retains the one nested specialization requested by the
same `Box Tree` occurrence traversed by positivity. -/
theorem requestedAuxiliaryPresent :
    FlatAuxPresent positivityRequest.key builtFlat := by
  rw [builtFlatShape]
  refine ⟨expectedAuxiliary, ?_, ?_⟩
  · simp [expectedFlat]
  · simp [expectedAuxiliary, flatRequest,
      NestedFlatAuxiliaryRequest.member,
      FlatBlockMember.nestedSpecializationKey,
      NestedPositivityAuxiliaryRequest.key,
      NestedPositivityAuxiliaryRequest.parameters, positivityRequest,
      treeExpr]

/-- Complete cross-stage reachability certificate for the adversarial nested
occurrence. The production positivity action traverses the external family,
the request headers agree exactly, and the public flat builder retains the
matching auxiliary under its audited source-order/deduplication invariant. -/
theorem nestedAuxiliaryReachability :
    positivityRequest.ProducedBy (positivityFuel - 1) boxId #[] #[treeExpr]
        groups rootGroup.addrs #[treeId.addr] checkerMethods nestedWhnfAfter
          positivityAfter ∧
      (∃ concrete afterLookup,
        TcM.getConst positivityRequest.id nestedWhnfAfter =
            .ok concrete afterLookup ∧
          concrete.NestedPositiveHeader positivityRequest.nParams
            positivityRequest.nIndices positivityRequest.levels
            positivityRequest.block positivityRequest.ctors ∧
          CompleteFreshNestedPositivityTrace (positivityFuel - 1)
            positivityRequest.universes positivityRequest.arguments groups
            #[treeId.addr] positivityRequest.nParams positivityRequest.block
            positivityRequest.ctors checkerMethods afterLookup
              positivityAfter) ∧
      ∃ auxSeen,
        (RecM.buildFlatBlockWithAuxSeen #[treeId] 0 0).run checkerMethods
            checkerInitial = .ok (builtFlat, auxSeen) flatBuildAfter ∧
          FlatAuxSeenSound builtFlat auxSeen ∧
          FlatAuxQueueExact builtFlat auxSeen ∧
          positivityRequest.key ∈ auxSeen ∧
          NestedAuxiliaryHeaderRel positivityRequest flatRequest ∧
          FlatAuxPresent positivityRequest.key builtFlat := by
  refine ⟨positivityRequestProduced, positivityRequestFreshExpansion, ?_⟩
  rcases RecM.buildFlatBlock_auxiliaryOrder #[treeId] 0 0 checkerMethods
      checkerInitial flatBuildAfter builtFlat flatBuildRun with
    ⟨auxSeen, hrun, sound, exact⟩
  refine ⟨auxSeen, hrun, sound, exact, ?_, requestHeaderRelation,
    requestedAuxiliaryPresent⟩
  have keyList : positivityRequest.key ∈ auxSeen.toList := by
    rw [← exact.key_order]
    rcases requestedAuxiliaryPresent with
      ⟨member, member_mem, aux, key_eq⟩
    apply List.mem_filterMap.mpr
    exact ⟨member, by simpa using member_mem, by simp [aux, key_eq]⟩
  simpa using keyList

end Ix.Tc.NestedRecursiveFixture
