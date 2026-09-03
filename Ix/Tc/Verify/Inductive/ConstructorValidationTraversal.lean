import Ix.Tc.Verify.Inductive.ConstructorPositivityTraversal

/-!
# Production constructor-validation traversal

`ConstructorPositivityTrace` classifies a successful strict-positivity call,
but E2c must also establish that the call is the one selected by production's
complete constructor-validation branch.  This module retains the exact A1–A4
execution around that call: derived metadata, shared-parameter agreement,
safety gating, field-universe validation, and constructor-return validation.
-/

namespace Ix.Tc

/-- Successful constructor-metadata validation together with the exact
physical constructor header selected by its lookup.  The aggregate run alone
does not identify `ctorTy` with a catalog entry; retaining this lookup is what
lets later semantic transport rule out a separately supplied telescope. -/
inductive ConstructorMetadataValidationTrace
    (ctorId inductId : KId m) (expectedCidx indParams : Nat)
    (indLvls : UInt64) (indIsUnsafe : Bool) (methods : Methods m)
    (ctorTy : KExpr m) (ctorFields : Nat) :
    TcState m → TcState m → Prop where
  | success {name : m.F Name} {levelParams : m.F (Array Name)}
      {actualIsUnsafe : Bool} {actualLvls : UInt64}
      {actualInduct : KId m} {actualCidx actualParams actualFields : UInt64}
      {initial afterLookup final : TcState m}
      (fields_eq : ctorFields = actualFields.toNat)
      (lookup : TcM.getConst ctorId initial =
        .ok (.ctor name levelParams actualIsUnsafe actualLvls actualInduct
          actualCidx actualParams actualFields ctorTy) afterLookup)
      (run :
        (RecM.checkCtorMetadataAgainstParent ctorId inductId expectedCidx
          indParams indLvls indIsUnsafe).run methods initial =
            .ok (ctorTy, ctorFields) final) :
      ConstructorMetadataValidationTrace ctorId inductId expectedCidx
        indParams indLvls indIsUnsafe methods ctorTy ctorFields initial final

/-- The safety-controlled positivity stage of one constructor validation. -/
inductive ConstructorPositivityGateTrace
    (ctorTy : KExpr m) (nParams : Nat) (blockAddrs : Array Address)
    (methods : Methods m) : Bool → TcState m → TcState m → Prop
  | safe {initial final : TcState m}
      (run : (RecM.checkPositivity ctorTy nParams blockAddrs).run methods
        initial = .ok () final)
      (trace : ConstructorPositivityTrace ctorTy nParams blockAddrs methods
        initial final) :
      ConstructorPositivityGateTrace ctorTy nParams blockAddrs methods false
        initial final
  | skipped {state : TcState m} :
      ConstructorPositivityGateTrace ctorTy nParams blockAddrs methods true
        state state

/-- Complete successful execution of production's shared one-constructor
A1–A4 helper.  Every intermediate state is retained so a consumer cannot
splice an independently run positivity proof into constructor acceptance. -/
inductive InductiveConstructorValidationTrace
    (ctorId inductId : KId m) (expectedCidx indParams indIndices : Nat)
    (indLvls : UInt64) (indIsUnsafe : Bool) (indTy : KExpr m)
    (indLevel : KUniv m) (blockAddrs : Array Address)
    (methods : Methods m) : TcState m → TcState m → Prop where
  | success {ctorTy : KExpr m} {ctorFields : Nat}
      {initial afterMetadata afterParameters afterPositivity afterUniverses
        final : TcState m}
      (metadata :
        (RecM.checkCtorMetadataAgainstParent ctorId inductId expectedCidx
          indParams indLvls indIsUnsafe).run methods initial =
            .ok (ctorTy, ctorFields) afterMetadata)
      (parameters :
        (RecM.checkParamAgreement indTy ctorTy indParams).run methods
          afterMetadata = .ok () afterParameters)
      (positivity :
        ConstructorPositivityGateTrace ctorTy indParams blockAddrs methods
          indIsUnsafe afterParameters afterPositivity)
      (universes :
        (RecM.checkFieldUniverses ctorTy indParams indLevel).run methods
          afterPositivity = .ok () afterUniverses)
      (returnType :
        (RecM.checkCtorReturnType ctorTy indParams indIndices ctorFields
          inductId.addr indLvls blockAddrs).run methods afterUniverses =
            .ok () final) :
      InductiveConstructorValidationTrace ctorId inductId expectedCidx
        indParams indIndices indLvls indIsUnsafe indTy indLevel blockAddrs
          methods initial final

namespace InductiveConstructorValidationTrace

/-- Erasing the retained A1–A4 trace reproduces the exact shared production
constructor-validation call. -/
theorem run
    (trace : InductiveConstructorValidationTrace ctorId inductId expectedCidx
      indParams indIndices indLvls indIsUnsafe indTy indLevel blockAddrs
        methods initial final) :
    (RecM.checkInductiveConstructor ctorId inductId expectedCidx indParams
      indIndices indLvls indIsUnsafe indTy indLevel blockAddrs).run methods
        initial = .ok () final := by
  cases trace with
  | success metadata parameters positivity universes returnType =>
      unfold RecM.checkInductiveConstructor
      rw [ReaderT.run_bind]
      change EStateM.bind
        ((RecM.checkCtorMetadataAgainstParent ctorId inductId expectedCidx
          indParams indLvls indIsUnsafe).run methods) _ initial = _
      unfold EStateM.bind
      rw [metadata]
      simp only
      rw [ReaderT.run_bind]
      change EStateM.bind
        ((RecM.checkParamAgreement indTy _ indParams).run methods) _ _ = _
      unfold EStateM.bind
      rw [parameters]
      simp only
      cases positivity with
      | safe positivityRun positivityTrace =>
          simp only [Bool.not_false, if_true]
          rw [ReaderT.run_bind]
          change EStateM.bind
            ((RecM.checkPositivity _ indParams blockAddrs).run methods) _ _ = _
          unfold EStateM.bind
          rw [positivityRun]
          simp only
          rw [ReaderT.run_bind]
          change EStateM.bind
            ((RecM.checkFieldUniverses _ indParams indLevel).run methods) _ _ = _
          unfold EStateM.bind
          rw [universes]
          simp only
          exact returnType
      | skipped =>
          simp only [Bool.not_true, Bool.false_eq_true, if_false]
          rw [ReaderT.run_bind]
          change EStateM.bind
            ((RecM.checkFieldUniverses _ indParams indLevel).run methods) _ _ = _
          unfold EStateM.bind
          rw [universes]
          simp only
          exact returnType

end InductiveConstructorValidationTrace

/-- Exact source-ordered traversal of every constructor retained by one
resolved parent header. -/
inductive InductiveConstructorsValidationTrace
    (inductId : KId m) (indParams indIndices : Nat) (indLvls : UInt64)
    (indIsUnsafe : Bool) (indTy : KExpr m) (indLevel : KUniv m)
    (blockAddrs : Array Address) (methods : Methods m) :
    List (KId m) → Nat → TcState m → TcState m → Prop
  | nil {expectedCidx : Nat} {state : TcState m} :
      InductiveConstructorsValidationTrace inductId indParams indIndices
        indLvls indIsUnsafe indTy indLevel blockAddrs methods [] expectedCidx
          state state
  | cons {ctorId : KId m} {ctorIds : List (KId m)} {expectedCidx : Nat}
      {initial afterHead final : TcState m}
      (head : InductiveConstructorValidationTrace ctorId inductId expectedCidx
        indParams indIndices indLvls indIsUnsafe indTy indLevel blockAddrs
          methods initial afterHead)
      (tail : InductiveConstructorsValidationTrace inductId indParams
        indIndices indLvls indIsUnsafe indTy indLevel blockAddrs methods
          ctorIds (expectedCidx + 1) afterHead final) :
      InductiveConstructorsValidationTrace inductId indParams indIndices
        indLvls indIsUnsafe indTy indLevel blockAddrs methods
          (ctorId :: ctorIds) expectedCidx initial final

/-- Exact cache branch used after successful constructor traversal. -/
inductive InductiveRecursorGenerationTrace (block : KId m)
    (methods : Methods m) : TcState m → TcState m → Prop
  | cached {state : TcState m}
      (present : state.env.recursorCache.contains block = true) :
      InductiveRecursorGenerationTrace block methods state state
  | generated {initial final : TcState m}
      (absent : initial.env.recursorCache.contains block = false)
      (run : (RecM.generateBlockRecursors block).run methods initial =
        .ok () final) :
      InductiveRecursorGenerationTrace block methods initial final

/-- Complete successful execution after an inductive header has been loaded.
The retained constructor loop contains a positivity trace for every safe
constructor, while recursor generation remains visibly sequenced afterward. -/
inductive ResolvedInductiveMemberValidationTrace
    (id : KId m) (params indices lvls : UInt64)
    (ctors : Array (KId m)) (block : KId m) (isUnsafe : Bool)
    (ty : KExpr m) (methods : Methods m) : TcState m → TcState m → Prop
  | success {blockInds : Array (KId m)} {indArity : UInt64}
      {indLevel : KUniv m}
      {initial afterDiscovery afterArity afterLevel afterPeers
        afterConstructors final : TcState m}
      (discovery : (RecM.discoverBlockInductives block).run methods initial =
        .ok blockInds afterDiscovery)
      (arity :
        (RecM.checkedMetadataSum "inductive params + indices"
          #[params, indices]).run methods afterDiscovery =
            .ok indArity afterArity)
      (level : (RecM.getResultSortLevel ty indArity.toNat).run methods
        afterArity = .ok indLevel afterLevel)
      (peers :
        (RecM.checkInductivePeerAgreement id block params lvls isUnsafe ty
          indLevel blockInds).run methods afterLevel = .ok () afterPeers)
      (constructors :
        InductiveConstructorsValidationTrace id params.toNat indices.toNat
          lvls isUnsafe ty indLevel (blockInds.map (·.addr)) methods
            ctors.toList 0 afterPeers afterConstructors)
      (recursors : InductiveRecursorGenerationTrace block methods
        afterConstructors final) :
      ResolvedInductiveMemberValidationTrace id params indices lvls ctors
        block isUnsafe ty methods initial final

/-- Complete successful validation of one inductive member, including the
exact header physically returned by production lookup.  Retaining the lookup
equation prevents a resolved-member trace for separately supplied metadata
from being substituted for the declaration selected by `id`. -/
inductive InductiveMemberValidationTrace (id : KId m) (methods : Methods m) :
    TcState m → TcState m → Prop where
  | success {name : m.F Name} {levelParams : m.F (Array Name)}
      {lvls params indices : UInt64} {isUnsafe : Bool} {block : KId m}
      {memberIdx : UInt64} {ty : KExpr m} {ctors : Array (KId m)}
      {leanAll : m.F (Array (KId m))}
      {initial afterLookup final : TcState m}
      (lookup : TcM.getConst id initial =
        .ok (.indc name levelParams lvls params indices isUnsafe block
          memberIdx ty ctors leanAll) afterLookup)
      (resolved : ResolvedInductiveMemberValidationTrace id params indices
        lvls ctors block isUnsafe ty methods afterLookup final) :
      InductiveMemberValidationTrace id methods initial final

/-- Exact source-ordered inductive-member pass selected by block
classification.  Each element retains the production reset immediately before
the exact header lookup and resolved validation. -/
inductive InductiveMembersValidationTrace (methods : Methods m) :
    List (KId m) → TcState m → TcState m → Prop
  | nil {state : TcState m} :
      InductiveMembersValidationTrace methods [] state state
  | cons {id : KId m} {ids : List (KId m)}
      {initial afterReset afterHead final : TcState m}
      (reset : TcM.reset initial = .ok () afterReset)
      (head : InductiveMemberValidationTrace id methods afterReset afterHead)
      (tail : InductiveMembersValidationTrace methods ids afterHead final) :
      InductiveMembersValidationTrace methods (id :: ids) initial final

/-- Complete successful spine of `checkInductiveBlockImpl`.  The initial
untouched-member pass determines the exact source-ordered inductive and
constructor arrays; the inductive pass is recursively decomposed down to each
positivity call.  The standalone constructor pass remains an exact final run
equation and therefore cannot be omitted or reordered. -/
inductive InductiveBlockValidationTrace (block : KId m)
    (members : Array (KId m)) (methods : Methods m) :
    TcState m → TcState m → Prop
  | success {indIds ctorIds : Array (KId m)}
      {initial afterClassification afterInductives final : TcState m}
      (classification :
        (RecM.classifyInductiveBlockMembers block members.toList #[] #[]).run
          methods initial = .ok (indIds, ctorIds) afterClassification)
      (inductives : InductiveMembersValidationTrace methods indIds.toList
        afterClassification afterInductives)
      (constructors :
        (RecM.checkInductiveConstructorMembers ctorIds.toList).run methods
          afterInductives = .ok () final) :
      InductiveBlockValidationTrace block members methods initial final

namespace RecM

/-- Decompose a successful metadata check down to the exact constructor
header returned by production lookup.  Every parent/arity/safety/index guard
is still retained by `trace.run`; this theorem adds the otherwise-lost
physical selection evidence. -/
theorem checkCtorMetadataAgainstParent_success
    {ctorId inductId : KId m} {expectedCidx indParams : Nat}
    {indLvls : UInt64} {indIsUnsafe : Bool} {methods : Methods m}
    {ctorTy : KExpr m} {ctorFields : Nat}
    {initial final : TcState m}
    (hrun :
      (checkCtorMetadataAgainstParent ctorId inductId expectedCidx indParams
        indLvls indIsUnsafe).run methods initial =
          .ok (ctorTy, ctorFields) final) :
    ConstructorMetadataValidationTrace ctorId inductId expectedCidx indParams
      indLvls indIsUnsafe methods ctorTy ctorFields initial final := by
  have fullRun := hrun
  unfold checkCtorMetadataAgainstParent at hrun
  simp only [ReaderT.run_bind, ReaderT.run_monadLift, monadLift_self] at hrun
  change EStateM.bind (TcM.getConst ctorId) _ initial = _ at hrun
  unfold EStateM.bind at hrun
  cases hlookup : TcM.getConst ctorId initial with
  | error err afterLookup =>
      rw [hlookup] at hrun
      contradiction
  | ok concrete afterLookup =>
      rw [hlookup] at hrun
      cases concrete with
      | ctor name levelParams actualIsUnsafe actualLvls actualInduct actualCidx
          actualParams actualFields actualTy =>
          simp only [pure_bind] at hrun
          split at hrun
          · change EStateM.Result.error _ afterLookup =
              .ok (ctorTy, ctorFields) final at hrun
            contradiction
          · split at hrun
            · change EStateM.Result.error _ afterLookup =
                .ok (ctorTy, ctorFields) final at hrun
              contradiction
            · split at hrun
              · change EStateM.Result.error _ afterLookup =
                  .ok (ctorTy, ctorFields) final at hrun
                contradiction
              · split at hrun
                · change EStateM.Result.error _ afterLookup =
                    .ok (ctorTy, ctorFields) final at hrun
                  contradiction
                · split at hrun
                  · change EStateM.Result.error _ afterLookup =
                      .ok (ctorTy, ctorFields) final at hrun
                    contradiction
                  · simp only [pure, ReaderT.run] at hrun
                    cases hrun
                    exact .success rfl hlookup fullRun
      | defn name levelParams kind safety hints lvls ty value leanAll block =>
          change EStateM.Result.error _ afterLookup =
            .ok (ctorTy, ctorFields) final at hrun
          contradiction
      | recr name levelParams k isUnsafe lvls params indices motives minors
          block memberIdx ty rules leanAll =>
          change EStateM.Result.error _ afterLookup =
            .ok (ctorTy, ctorFields) final at hrun
          contradiction
      | axio name levelParams isUnsafe lvls ty =>
          change EStateM.Result.error _ afterLookup =
            .ok (ctorTy, ctorFields) final at hrun
          contradiction
      | quot name levelParams kind lvls ty =>
          change EStateM.Result.error _ afterLookup =
            .ok (ctorTy, ctorFields) final at hrun
          contradiction
      | indc name levelParams lvls params indices isUnsafe block memberIdx ty
          ctors leanAll =>
          change EStateM.Result.error _ afterLookup =
            .ok (ctorTy, ctorFields) final at hrun
          contradiction

/-- Every successful complete constructor-validation call exposes the exact
strict-positivity call selected by its safety flag and all surrounding A1–A4
state transitions. -/
theorem checkInductiveConstructor_success (methods : Methods m)
    {ctorId inductId : KId m} {expectedCidx indParams indIndices : Nat}
    {indLvls : UInt64} {indIsUnsafe : Bool} {indTy : KExpr m}
    {indLevel : KUniv m} {blockAddrs : Array Address}
    {initial final : TcState m}
    (hrun : (checkInductiveConstructor ctorId inductId expectedCidx indParams
      indIndices indLvls indIsUnsafe indTy indLevel blockAddrs).run methods
        initial = .ok () final) :
    InductiveConstructorValidationTrace ctorId inductId expectedCidx indParams
      indIndices indLvls indIsUnsafe indTy indLevel blockAddrs methods initial
        final := by
  unfold checkInductiveConstructor at hrun
  rw [ReaderT.run_bind] at hrun
  change EStateM.bind
    ((checkCtorMetadataAgainstParent ctorId inductId expectedCidx indParams
      indLvls indIsUnsafe).run methods) _ initial = _ at hrun
  unfold EStateM.bind at hrun
  cases hmetadata :
      (checkCtorMetadataAgainstParent ctorId inductId expectedCidx indParams
        indLvls indIsUnsafe).run methods initial with
  | error err afterMetadata =>
      rw [hmetadata] at hrun
      contradiction
  | ok payload afterMetadata =>
      rcases payload with ⟨ctorTy, ctorFields⟩
      rw [hmetadata] at hrun
      simp only at hrun
      rw [ReaderT.run_bind] at hrun
      change EStateM.bind
        ((checkParamAgreement indTy ctorTy indParams).run methods) _
          afterMetadata = _ at hrun
      unfold EStateM.bind at hrun
      cases hparameters :
          (checkParamAgreement indTy ctorTy indParams).run methods
            afterMetadata with
      | error err afterParameters =>
          rw [hparameters] at hrun
          contradiction
      | ok value afterParameters =>
          cases value
          rw [hparameters] at hrun
          cases hunsafe : indIsUnsafe with
          | false =>
              simp only [hunsafe] at hmetadata
              simp only [hunsafe, Bool.not_false, if_true] at hrun
              rw [ReaderT.run_bind] at hrun
              change EStateM.bind
                ((checkPositivity ctorTy indParams blockAddrs).run methods) _
                  afterParameters = _ at hrun
              unfold EStateM.bind at hrun
              cases hpositivity :
                  (checkPositivity ctorTy indParams blockAddrs).run methods
                    afterParameters with
              | error err afterPositivity =>
                  rw [hpositivity] at hrun
                  contradiction
              | ok value afterPositivity =>
                  cases value
                  rw [hpositivity] at hrun
                  rw [ReaderT.run_bind] at hrun
                  change EStateM.bind
                    ((checkFieldUniverses ctorTy indParams indLevel).run
                      methods) _ afterPositivity = _ at hrun
                  unfold EStateM.bind at hrun
                  cases huniverses :
                      (checkFieldUniverses ctorTy indParams indLevel).run
                        methods afterPositivity with
                  | error err afterUniverses =>
                      rw [huniverses] at hrun
                      contradiction
                  | ok value afterUniverses =>
                      cases value
                      rw [huniverses] at hrun
                      exact .success hmetadata hparameters
                        (.safe hpositivity
                          (checkPositivity_success methods hpositivity))
                        huniverses hrun
          | true =>
              simp only [hunsafe] at hmetadata
              simp only [hunsafe, Bool.not_true, Bool.false_eq_true, if_false,
                ReaderT.run_pure, pure_bind] at hrun
              rw [ReaderT.run_bind] at hrun
              change EStateM.bind
                ((checkFieldUniverses ctorTy indParams indLevel).run methods) _
                  afterParameters = _ at hrun
              unfold EStateM.bind at hrun
              cases huniverses :
                  (checkFieldUniverses ctorTy indParams indLevel).run methods
                    afterParameters with
              | error err afterUniverses =>
                  rw [huniverses] at hrun
                  contradiction
              | ok value afterUniverses =>
                  cases value
                  rw [huniverses] at hrun
                  exact .success hmetadata hparameters .skipped huniverses
                    hrun

/-- Every successful source-ordered constructor loop retains every complete
constructor trace at its derived list position. -/
theorem checkInductiveConstructors_success (methods : Methods m)
    {inductId : KId m} {indParams indIndices : Nat} {indLvls : UInt64}
    {indIsUnsafe : Bool} {indTy : KExpr m} {indLevel : KUniv m}
    {blockAddrs : Array Address} :
    ∀ {ctorIds : List (KId m)} {expectedCidx : Nat}
        {initial final : TcState m},
      (checkInductiveConstructors inductId indParams indIndices indLvls
        indIsUnsafe indTy indLevel blockAddrs ctorIds expectedCidx).run methods
          initial = .ok () final →
      InductiveConstructorsValidationTrace inductId indParams indIndices
        indLvls indIsUnsafe indTy indLevel blockAddrs methods ctorIds
          expectedCidx initial final
  | [], expectedCidx, initial, final, hrun => by
      simp only [checkInductiveConstructors, ReaderT.run_pure, pure] at hrun
      cases hrun
      exact .nil
  | ctorId :: ctorIds, expectedCidx, initial, final, hrun => by
      unfold checkInductiveConstructors at hrun
      rw [ReaderT.run_bind] at hrun
      change EStateM.bind
        ((checkInductiveConstructor ctorId inductId expectedCidx indParams
          indIndices indLvls indIsUnsafe indTy indLevel blockAddrs).run
            methods) _ initial = _ at hrun
      unfold EStateM.bind at hrun
      cases hhead :
          (checkInductiveConstructor ctorId inductId expectedCidx indParams
            indIndices indLvls indIsUnsafe indTy indLevel blockAddrs).run
              methods initial with
      | error err afterHead =>
          rw [hhead] at hrun
          contradiction
      | ok value afterHead =>
          cases value
          rw [hhead] at hrun
          exact .cons (checkInductiveConstructor_success methods hhead)
            (checkInductiveConstructors_success methods hrun)

/-- Successful recursor-cache completion exposes whether production reused an
existing canonical generation or executed the generator. -/
theorem ensureInductiveRecursors_success (methods : Methods m)
    {block : KId m} {initial final : TcState m}
    (hrun : (ensureInductiveRecursors block).run methods initial =
      .ok () final) :
    InductiveRecursorGenerationTrace block methods initial final := by
  unfold ensureInductiveRecursors at hrun
  rw [ReaderT.run_bind] at hrun
  change EStateM.bind (get : TcM m (TcState m)) _ initial = _ at hrun
  unfold EStateM.bind at hrun
  rw [show (get : TcM m (TcState m)) initial = .ok initial initial from rfl]
    at hrun
  simp only at hrun
  cases hpresent : initial.env.recursorCache.contains block with
  | false =>
      simp [hpresent] at hrun
      exact .generated hpresent hrun
  | true =>
      simp [hpresent] at hrun
      cases hrun
      exact .cached hpresent

/-- Every successful resolved-member execution retains discovery, numeric
arity, result-level, peer, constructor, and recursor phases in production
order. -/
theorem checkResolvedInductiveMember_success (methods : Methods m)
    {id : KId m} {params indices lvls : UInt64}
    {ctors : Array (KId m)} {block : KId m} {isUnsafe : Bool}
    {ty : KExpr m} {initial final : TcState m}
    (hrun : (checkResolvedInductiveMember id params indices lvls ctors block
      isUnsafe ty).run methods initial = .ok () final) :
    ResolvedInductiveMemberValidationTrace id params indices lvls ctors block
      isUnsafe ty methods initial final := by
  unfold checkResolvedInductiveMember at hrun
  rw [ReaderT.run_bind] at hrun
  change EStateM.bind ((discoverBlockInductives block).run methods) _ initial =
    _ at hrun
  unfold EStateM.bind at hrun
  cases hdiscovery : (discoverBlockInductives block).run methods initial with
  | error err afterDiscovery =>
      rw [hdiscovery] at hrun
      contradiction
  | ok blockInds afterDiscovery =>
      rw [hdiscovery] at hrun
      simp only at hrun
      rw [ReaderT.run_bind] at hrun
      change EStateM.bind
        ((checkedMetadataSum "inductive params + indices"
          #[params, indices]).run methods) _ afterDiscovery = _ at hrun
      unfold EStateM.bind at hrun
      cases harity :
          (checkedMetadataSum "inductive params + indices"
            #[params, indices]).run methods afterDiscovery with
      | error err afterArity =>
          rw [harity] at hrun
          contradiction
      | ok indArity afterArity =>
          rw [harity] at hrun
          simp only at hrun
          rw [ReaderT.run_bind] at hrun
          change EStateM.bind
            ((getResultSortLevel ty indArity.toNat).run methods) _ afterArity =
              _ at hrun
          unfold EStateM.bind at hrun
          cases hlevel :
              (getResultSortLevel ty indArity.toNat).run methods afterArity with
          | error err afterLevel =>
              rw [hlevel] at hrun
              contradiction
          | ok indLevel afterLevel =>
              rw [hlevel] at hrun
              simp only at hrun
              rw [ReaderT.run_bind] at hrun
              change EStateM.bind
                ((checkInductivePeerAgreement id block params lvls isUnsafe
                  ty indLevel blockInds).run methods) _ afterLevel = _ at hrun
              unfold EStateM.bind at hrun
              cases hpeers :
                  (checkInductivePeerAgreement id block params lvls isUnsafe
                    ty indLevel blockInds).run methods afterLevel with
              | error err afterPeers =>
                  rw [hpeers] at hrun
                  contradiction
              | ok value afterPeers =>
                  cases value
                  rw [hpeers] at hrun
                  simp only at hrun
                  rw [ReaderT.run_bind] at hrun
                  change EStateM.bind
                    ((checkInductiveConstructors id params.toNat indices.toNat
                      lvls isUnsafe ty indLevel (blockInds.map (·.addr))
                        ctors.toList 0).run methods) _ afterPeers = _ at hrun
                  unfold EStateM.bind at hrun
                  cases hconstructors :
                      (checkInductiveConstructors id params.toNat indices.toNat
                        lvls isUnsafe ty indLevel (blockInds.map (·.addr))
                          ctors.toList 0).run methods afterPeers with
                  | error err afterConstructors =>
                      rw [hconstructors] at hrun
                      contradiction
                  | ok value afterConstructors =>
                      cases value
                      rw [hconstructors] at hrun
                      simp only at hrun
                      exact .success hdiscovery harity hlevel hpeers
                        (checkInductiveConstructors_success methods
                          hconstructors)
                        (ensureInductiveRecursors_success methods hrun)

/-- Every successful member-validation call is tied to the exact inductive
header returned by production lookup and to its complete resolved validation
trace. -/
theorem checkInductiveMemberImpl_success (methods : Methods m)
    {id : KId m} {initial final : TcState m}
    (hrun : (checkInductiveMemberImpl id).run methods initial = .ok () final) :
    InductiveMemberValidationTrace id methods initial final := by
  unfold checkInductiveMemberImpl at hrun
  simp only [ReaderT.run_bind, ReaderT.run_monadLift, monadLift_self] at hrun
  change EStateM.bind (TcM.getConst id) _ initial = _ at hrun
  unfold EStateM.bind at hrun
  cases hlookup : TcM.getConst id initial with
  | error err afterLookup =>
      rw [hlookup] at hrun
      contradiction
  | ok concrete afterLookup =>
      rw [hlookup] at hrun
      cases concrete with
      | indc name levelParams lvls params indices isUnsafe block memberIdx ty
          ctors leanAll =>
          simp only at hrun
          exact .success hlookup
            (checkResolvedInductiveMember_success methods hrun)
      | defn name levelParams kind safety hints lvls ty value leanAll block =>
          change EStateM.Result.error _ afterLookup = .ok () final at hrun
          contradiction
      | recr name levelParams k isUnsafe lvls params indices motives minors
          block memberIdx ty rules leanAll =>
          change EStateM.Result.error _ afterLookup = .ok () final at hrun
          contradiction
      | axio name levelParams isUnsafe lvls ty =>
          change EStateM.Result.error _ afterLookup = .ok () final at hrun
          contradiction
      | quot name levelParams kind lvls ty =>
          change EStateM.Result.error _ afterLookup = .ok () final at hrun
          contradiction
      | ctor name levelParams isUnsafe lvls induct cidx params fields ty =>
          change EStateM.Result.error _ afterLookup = .ok () final at hrun
          contradiction

/-- Every successful inductive-member list pass retains its exact reset and
complete member trace in source order. -/
theorem checkInductiveMembers_success (methods : Methods m) :
    ∀ {ids : List (KId m)} {initial final : TcState m},
      (checkInductiveMembers ids).run methods initial = .ok () final →
      InductiveMembersValidationTrace methods ids initial final
  | [], initial, final, hrun => by
      simp only [checkInductiveMembers, pure, ReaderT.run] at hrun
      cases hrun
      exact .nil
  | id :: ids, initial, final, hrun => by
      unfold checkInductiveMembers at hrun
      simp only [ReaderT.run_bind, ReaderT.run_monadLift, monadLift_self]
        at hrun
      change EStateM.bind TcM.reset _ initial = _ at hrun
      unfold EStateM.bind at hrun
      cases hreset : TcM.reset initial with
      | error err afterReset =>
          rw [hreset] at hrun
          contradiction
      | ok value afterReset =>
          cases value
          rw [hreset] at hrun
          simp only at hrun
          change EStateM.bind ((checkInductiveMemberImpl id).run methods) _
            afterReset = _ at hrun
          unfold EStateM.bind at hrun
          cases hhead : (checkInductiveMemberImpl id).run methods afterReset with
          | error err afterHead =>
              rw [hhead] at hrun
              contradiction
          | ok value afterHead =>
              cases value
              rw [hhead] at hrun
              exact .cons hreset
                (checkInductiveMemberImpl_success methods hhead)
                (checkInductiveMembers_success methods hrun)

/-- Every successful production block implementation exposes the exact
classification result, all inductive member traces, and the final standalone
constructor pass. -/
theorem checkInductiveBlockImpl_success (methods : Methods m)
    {block : KId m} {members : Array (KId m)}
    {initial final : TcState m}
    (hrun : (checkInductiveBlockImpl block members).run methods initial =
      .ok () final) :
    InductiveBlockValidationTrace block members methods initial final := by
  unfold checkInductiveBlockImpl at hrun
  rw [ReaderT.run_bind] at hrun
  change EStateM.bind
    ((classifyInductiveBlockMembers block members.toList #[] #[]).run methods)
      _ initial = _ at hrun
  unfold EStateM.bind at hrun
  cases hclassification :
      (classifyInductiveBlockMembers block members.toList #[] #[]).run methods
        initial with
  | error err afterClassification =>
      rw [hclassification] at hrun
      contradiction
  | ok classified afterClassification =>
      rcases classified with ⟨indIds, ctorIds⟩
      rw [hclassification] at hrun
      simp only at hrun
      rw [ReaderT.run_bind] at hrun
      change EStateM.bind ((checkInductiveMembers indIds.toList).run methods) _
        afterClassification = _ at hrun
      unfold EStateM.bind at hrun
      cases hinductives :
          (checkInductiveMembers indIds.toList).run methods afterClassification
          with
      | error err afterInductives =>
          rw [hinductives] at hrun
          contradiction
      | ok value afterInductives =>
          cases value
          rw [hinductives] at hrun
          exact .success hclassification
            (checkInductiveMembers_success methods hinductives) hrun

end RecM
end Ix.Tc
