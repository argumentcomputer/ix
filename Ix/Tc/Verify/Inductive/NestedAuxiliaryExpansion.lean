import Ix.Tc.Verify.Inductive.NestedPositivityTraversal

/-!
# Nested positivity requests and flat-block auxiliary expansion

The positivity checker and recursor generator discover the same nested
specialization through different executions.  Positivity works with checked
`Nat` arities after a concrete family lookup; flat-block construction retains
the header's physical `UInt64` metadata and constructs shifted universe
parameters for the auxiliary.

This module keeps those stages distinct.  A successful complete positivity
trace yields an exact `NestedPositivityAuxiliaryRequest`, including whether
the specialization was already active or must be expanded.  A separate
`NestedFlatAuxiliaryRequest` describes the exact member appended by the named
production action `appendNestedAuxiliary`.  `NestedAuxiliaryHeaderRel` is the
small representation bridge that later block traversal must derive from the
two executions of the same loaded header.
-/

namespace Ix.Tc

/-- Equality lawfulness is needed only for the physical `auxSeen` membership
proofs in this module.  Keep it local so the broader positivity traversal
continues to use its smaller trust frontier. -/
local instance : LawfulBEq NestedSpecializationKey :=
  lawfulBEqNestedSpecializationKey

/-- The exact nested-family request exposed by successful positivity.  Its
arity fields are mathematical naturals because they are the values checked by
the positivity precondition. -/
structure NestedPositivityAuxiliaryRequest (m : Mode) where
  id : KId m
  universes : Array (KUniv m)
  arguments : Array (KExpr m)
  nParams : Nat
  nIndices : Nat
  levels : Nat
  block : KId m
  ctors : Array (KId m)

namespace NestedPositivityAuxiliaryRequest

/-- Parameter prefix whose structural addresses identify this auxiliary. -/
def parameters (request : NestedPositivityAuxiliaryRequest m) :
    Array (KExpr m) :=
  request.arguments.extract 0 request.nParams

/-- The exact specialization key shared with flat-block deduplication. -/
def key (request : NestedPositivityAuxiliaryRequest m) :
    NestedSpecializationKey :=
  NestedSpecializationKey.ofApplication request.id.addr request.universes
    request.parameters

/-- A fully applied checked header has exactly its declared parameter prefix. -/
theorem parameters_size (request : NestedPositivityAuxiliaryRequest m)
    (arity : request.arguments.size = request.nParams + request.nIndices) :
    request.parameters.size = request.nParams := by
  simp [parameters, arity]

end NestedPositivityAuxiliaryRequest

/-- Physical header data consumed by the flat-block append action. -/
structure NestedFlatAuxiliaryRequest (m : Mode) where
  id : KId m
  occurrenceUs : Array (KUniv m)
  specParams : Array (KExpr m)
  ownParams : UInt64
  nIndices : UInt64
  ctors : Array (KId m)
  lvls : UInt64

namespace NestedFlatAuxiliaryRequest

/-- Structural identity used by the production `auxSeen` array. -/
def key (request : NestedFlatAuxiliaryRequest m) : NestedSpecializationKey :=
  NestedSpecializationKey.ofApplication request.id.addr request.occurrenceUs
    request.specParams

/-- Exact physical member appended after shifted universes are interned. -/
def member (request : NestedFlatAuxiliaryRequest m)
    (indUs : Array (KUniv m)) : FlatBlockMember m :=
  { id := request.id
    isAux := true
    specParams := request.specParams
    ownParams := request.ownParams
    nIndices := request.nIndices
    ctors := request.ctors
    lvls := request.lvls
    indUs
    occurrenceUs := request.occurrenceUs }

/-- Positivity context installed while recursively checking this auxiliary's
constructors.  The external mutual block supplies the complete address set. -/
def positivityGroup (request : NestedFlatAuxiliaryRequest m)
    (externalAddrs : Array Address) : PositivityGroup m :=
  { addrs := externalAddrs
    params := request.specParams
    concreteUs := some request.occurrenceUs }

@[simp] theorem member_id (request : NestedFlatAuxiliaryRequest m) indUs :
    (request.member indUs).id = request.id := rfl

@[simp] theorem member_isAux (request : NestedFlatAuxiliaryRequest m) indUs :
    (request.member indUs).isAux = true := rfl

@[simp] theorem member_key (request : NestedFlatAuxiliaryRequest m) indUs :
    NestedSpecializationKey.ofApplication (request.member indUs).id.addr
      (request.member indUs).occurrenceUs
      (request.member indUs).specParams = request.key := rfl

end NestedFlatAuxiliaryRequest

/-! ## Exact key/member invariant for the production queue -/

/-- Structural specialization represented by a flat member.  Original
members also have a value here, so consumers must retain the separate
`isAux` guard. -/
def FlatBlockMember.nestedSpecializationKey (member : FlatBlockMember m) :
    NestedSpecializationKey :=
  NestedSpecializationKey.ofApplication member.id.addr member.occurrenceUs
    member.specParams

/-- The flat array contains an auxiliary at exactly this structural key. -/
def FlatAuxPresent (key : NestedSpecializationKey)
    (flat : Array (FlatBlockMember m)) : Prop :=
  ∃ member, member ∈ flat ∧ member.isAux = true ∧
    member.nestedSpecializationKey = key

/-- Every key retained by the production deduplication array is represented
by an actual auxiliary member.  This rules out treating `auxSeen` as an
unrelated oracle for the existing-specialization branch. -/
def FlatAuxSeenSound (flat : Array (FlatBlockMember m))
    (auxSeen : Array NestedSpecializationKey) : Prop :=
  ∀ key, key ∈ auxSeen → FlatAuxPresent key flat

namespace FlatAuxSeenSound

/-- The empty deduplication array is sound for any flat prefix. -/
theorem empty (flat : Array (FlatBlockMember m)) :
    FlatAuxSeenSound flat #[] := by
  intro key member
  simp at member

/-- Appending one matching member/key pair preserves the invariant. -/
theorem push
    {flat : Array (FlatBlockMember m)}
    {auxSeen : Array NestedSpecializationKey}
    (sound : FlatAuxSeenSound flat auxSeen)
    (member : FlatBlockMember m) (key : NestedSpecializationKey)
    (auxiliary : member.isAux = true)
    (key_eq : member.nestedSpecializationKey = key) :
    FlatAuxSeenSound (flat.push member) (auxSeen.push key) := by
  intro candidate candidate_mem
  rcases Array.mem_push.mp candidate_mem with candidate_mem | rfl
  · rcases sound candidate candidate_mem with
      ⟨prior, prior_mem, prior_auxiliary, prior_matches⟩
    exact ⟨prior, Array.mem_push.mpr (.inl prior_mem), prior_auxiliary,
      prior_matches⟩
  · exact ⟨member, Array.mem_push_self, auxiliary, key_eq⟩

end FlatAuxSeenSound

/-- Complete representation-level effect of one successful nested-detection
action.  Production either leaves the pair unchanged or appends one exact
auxiliary member and its previously absent structural key. -/
inductive FlatAuxTransition
    (flat : Array (FlatBlockMember m))
    (auxSeen : Array NestedSpecializationKey) :
    (Array (FlatBlockMember m) × Array NestedSpecializationKey) → Prop where
  | unchanged : FlatAuxTransition flat auxSeen (flat, auxSeen)
  | fresh (request : NestedFlatAuxiliaryRequest m)
      (indUs : Array (KUniv m))
      (not_seen : request.key ∉ auxSeen) :
      FlatAuxTransition flat auxSeen
        (flat.push (request.member indUs), auxSeen.push request.key)

namespace FlatAuxTransition

variable {m : Mode} {flat : Array (FlatBlockMember m)}
  {auxSeen : Array NestedSpecializationKey}
  {result : Array (FlatBlockMember m) × Array NestedSpecializationKey}

/-- Every transition preserves the exact key/member soundness invariant. -/
theorem seenSound
    (transition : FlatAuxTransition flat auxSeen result)
    (sound : FlatAuxSeenSound flat auxSeen) :
    FlatAuxSeenSound result.1 result.2 := by
  cases transition with
  | unchanged => exact sound
  | fresh request indUs not_seen =>
      exact FlatAuxSeenSound.push sound (request.member indUs) request.key rfl
        rfl

/-- Existing flat members remain present after either transition. -/
theorem flat_mem
    (transition : FlatAuxTransition flat auxSeen result)
    {member : FlatBlockMember m} (member_mem : member ∈ flat) :
    member ∈ result.1 := by
  cases transition with
  | unchanged => exact member_mem
  | fresh => exact Array.mem_push.mpr (.inl member_mem)

/-- Existing exact keys remain in the deduplication array. -/
theorem key_mem
    (transition : FlatAuxTransition flat auxSeen result)
    {key : NestedSpecializationKey} (key_mem : key ∈ auxSeen) :
    key ∈ result.2 := by
  cases transition with
  | unchanged => exact key_mem
  | fresh => exact Array.mem_push.mpr (.inl key_mem)

end FlatAuxTransition

/-- Reflexive/transitive, source-ordered closure of exact detector effects.
This is the semantic shape threaded by field, constructor, and queue scans. -/
inductive FlatAuxHistory (m : Mode) :
    (Array (FlatBlockMember m) × Array NestedSpecializationKey) →
    (Array (FlatBlockMember m) × Array NestedSpecializationKey) → Prop where
  | refl (pair) : FlatAuxHistory m pair pair
  | step {before middle after}
      (head : FlatAuxTransition before.1 before.2 middle)
      (tail : FlatAuxHistory m middle after) :
      FlatAuxHistory m before after

namespace FlatAuxHistory

variable {m : Mode}
  {before middle after :
    Array (FlatBlockMember m) × Array NestedSpecializationKey}

/-- Embed one detector effect in the history closure. -/
theorem single (transition : FlatAuxTransition before.1 before.2 after) :
    FlatAuxHistory m before after :=
  .step transition (.refl after)

/-- Compose adjacent source-ordered histories. -/
theorem trans (left : FlatAuxHistory m before middle)
    (right : FlatAuxHistory m middle after) :
    FlatAuxHistory m before after := by
  induction left with
  | refl => exact right
  | step head tail ih => exact .step head (ih right)

/-- Exact key/member soundness is invariant under a whole history. -/
theorem seenSound (history : FlatAuxHistory m before after)
    (sound : FlatAuxSeenSound before.1 before.2) :
    FlatAuxSeenSound after.1 after.2 := by
  induction history with
  | refl => exact sound
  | step head tail ih => exact ih (head.seenSound sound)

/-- Every pre-existing member remains reachable after the history. -/
theorem flat_mem (history : FlatAuxHistory m before after)
    {member : FlatBlockMember m} (member_mem : member ∈ before.1) :
    member ∈ after.1 := by
  induction history with
  | refl => exact member_mem
  | step head tail ih => exact ih (head.flat_mem member_mem)

/-- Every pre-existing key remains reachable after the history. -/
theorem key_mem (history : FlatAuxHistory m before after)
    {key : NestedSpecializationKey} (key_mem : key ∈ before.2) :
    key ∈ after.2 := by
  induction history with
  | refl => exact key_mem
  | step head tail ih => exact ih (head.key_mem key_mem)

end FlatAuxHistory

/-- Flat/member component of a production queue state. -/
def flatAuxQueuePair (state : FlatBlockQueueState m) :
    Array (FlatBlockMember m) × Array NestedSpecializationKey :=
  (state.2.1, state.2.2)

/-- A successful bounded queue callback carries a source-ordered history to
either its next queue state or its final returned pair. -/
def FlatAuxQueueStepHistory (before : FlatBlockQueueState m) :
    RecM.BoundedStep (FlatBlockQueueState m)
      (Array (FlatBlockMember m) × Array NestedSpecializationKey) → Prop
  | .next after =>
      FlatAuxHistory m (flatAuxQueuePair before) (flatAuxQueuePair after)
  | .done result => FlatAuxHistory m (flatAuxQueuePair before) result

/-- Auxiliary keys in their physical flat-block order. -/
def FlatAuxKeyOrder (flat : Array (FlatBlockMember m)) :
    List NestedSpecializationKey :=
  flat.toList.filterMap fun member =>
    if member.isAux then some member.nestedSpecializationKey else none

/-- Exact queue representation: the physical auxiliary order equals the
deduplication order, and no structural key occurs twice. -/
structure FlatAuxQueueExact (flat : Array (FlatBlockMember m))
    (auxSeen : Array NestedSpecializationKey) : Prop where
  key_order : FlatAuxKeyOrder flat = auxSeen.toList
  no_duplicate_keys : auxSeen.toList.Nodup

namespace FlatAuxQueueExact

variable {m : Mode} {flat : Array (FlatBlockMember m)}
  {auxSeen : Array NestedSpecializationKey}
  {result : Array (FlatBlockMember m) × Array NestedSpecializationKey}

/-- An empty pair has the exact queue representation. -/
theorem empty : FlatAuxQueueExact (#[] : Array (FlatBlockMember m)) #[] := by
  constructor <;> simp [FlatAuxKeyOrder]

/-- Appending one non-auxiliary original does not change the exact auxiliary
representation. -/
theorem pushOriginal (exact : FlatAuxQueueExact flat auxSeen)
    (member : FlatBlockMember m) (original : member.isAux = false) :
    FlatAuxQueueExact (flat.push member) auxSeen := by
  constructor
  · simpa [FlatAuxKeyOrder, original] using exact.key_order
  · exact exact.no_duplicate_keys

/-- One exact detector transition preserves physical/source order and
deduplication. -/
theorem transition (exact : FlatAuxQueueExact flat auxSeen)
    (step : FlatAuxTransition flat auxSeen result) :
    FlatAuxQueueExact result.1 result.2 := by
  cases step with
  | unchanged => exact exact
  | fresh request indUs not_seen =>
      have key_not_mem : request.key ∉ auxSeen.toList := by
        simpa using not_seen
      constructor
      · have push_order :
            FlatAuxKeyOrder (flat.push (request.member indUs)) =
              FlatAuxKeyOrder flat ++ [request.key] := by
          simp [FlatAuxKeyOrder, NestedFlatAuxiliaryRequest.member,
            FlatBlockMember.nestedSpecializationKey,
            NestedFlatAuxiliaryRequest.key]
        rw [push_order, exact.key_order]
        change auxSeen.toList ++ [request.key] =
          (auxSeen.push request.key).toList
        rw [Array.toList_push]
      · change (auxSeen.push request.key).toList.Nodup
        rw [Array.toList_push, List.nodup_append]
        refine ⟨exact.no_duplicate_keys, ?_, ?_⟩
        · simp
        · intro left left_mem right right_mem
          simp only [List.mem_singleton] at right_mem
          subst right
          exact fun equality => key_not_mem (equality ▸ left_mem)

/-- A complete source-ordered history preserves the exact representation. -/
theorem history
    {before result :
      Array (FlatBlockMember m) × Array NestedSpecializationKey}
    (exact : FlatAuxQueueExact before.1 before.2)
    (steps : FlatAuxHistory m before result) :
    FlatAuxQueueExact result.1 result.2 := by
  induction steps with
  | refl => exact exact
  | step head tail ih => exact ih (exact.transition head)

end FlatAuxQueueExact

/-- The checked and physical requests came from the same external-family
header.  No arithmetic coercion is implicit: every `UInt64.toNat` equality is
retained for the later no-wrap/representation audit. -/
structure NestedAuxiliaryHeaderRel
    (positivity : NestedPositivityAuxiliaryRequest m)
    (flat : NestedFlatAuxiliaryRequest m) : Prop where
  id : flat.id = positivity.id
  universes : flat.occurrenceUs = positivity.universes
  parameters : flat.specParams = positivity.parameters
  nParams : flat.ownParams.toNat = positivity.nParams
  nIndices : flat.nIndices.toNat = positivity.nIndices
  levels : flat.lvls.toNat = positivity.levels
  ctors : flat.ctors = positivity.ctors

namespace NestedAuxiliaryHeaderRel

/-- Header correspondence identifies exactly the same structural auxiliary;
semantic universe equality or term DefEq cannot merge two requests here. -/
theorem key_eq (relation : NestedAuxiliaryHeaderRel positivity flat) :
    flat.key = positivity.key := by
  unfold NestedFlatAuxiliaryRequest.key
    NestedPositivityAuxiliaryRequest.key
  rw [relation.id, relation.universes, relation.parameters]

/-- The context pushed by flat auxiliary expansion matches the exact
specialization accepted by positivity. -/
theorem positivityFlatIdentity
    (relation : NestedAuxiliaryHeaderRel positivity flat)
    (arity : positivity.arguments.size =
      positivity.nParams + positivity.nIndices)
    (externalAddrs : Array Address) :
    PositivityFlatIdentity (flat.positivityGroup externalAddrs)
      positivity.id.addr positivity.universes positivity.arguments
        positivity.nParams := by
  unfold PositivityFlatIdentity
  constructor
  · change flat.specParams.size = positivity.nParams
    rw [relation.parameters]
    exact positivity.parameters_size arity
  · unfold NestedFlatAuxiliaryRequest.positivityGroup
      PositivityGroup.nestedSpecializationKey?
      nestedApplicationSpecializationKey
    simp only [Option.map_some]
    rw [relation.universes, relation.parameters]
    simp [NestedPositivityAuxiliaryRequest.parameters]

end NestedAuxiliaryHeaderRel

/-- Exact successful fresh branch of the named production append action.  The
generated universe array is existential so the execution trace remains in
`Prop`. -/
def NestedAuxiliaryAppendTrace
    (request : NestedFlatAuxiliaryRequest m)
    (flat : Array (FlatBlockMember m))
    (auxSeen : Array NestedSpecializationKey) (univOffset : UInt64)
    (methods : Methods m) (initial final : TcState m)
    (result : Array (FlatBlockMember m) ×
      Array NestedSpecializationKey) : Prop :=
  ∃ indUs,
    auxSeen.contains request.key = false ∧
      (RecM.mkIndUnivs request.lvls univOffset).run methods initial =
        .ok indUs final ∧
      result = (flat.push (request.member indUs),
        auxSeen.push request.key)

namespace NestedAuxiliaryAppendTrace

/-- The freshly constructed member is present in the returned flat block. -/
theorem member_mem
    (trace : NestedAuxiliaryAppendTrace request flat auxSeen univOffset
      methods initial final result) :
    ∃ indUs, request.member indUs ∈ result.1 := by
  rcases trace with ⟨indUs, _, _, result_eq⟩
  refine ⟨indUs, ?_⟩
  rw [result_eq]
  exact Array.mem_push_self

/-- The exact specialization key is present in the returned deduplication
set. -/
theorem key_mem
    (trace : NestedAuxiliaryAppendTrace request flat auxSeen univOffset
      methods initial final result) :
    request.key ∈ result.2 := by
  rcases trace with ⟨_, _, _, result_eq⟩
  rw [result_eq]
  exact Array.mem_push_self

end NestedAuxiliaryAppendTrace

namespace RecM

/-- Expose one concrete checker bind while classifying the successful nested
detection branches. -/
private theorem runTcBindForFlatAuxiliary {α β : Type}
    (x : TcM m α) (k : α → TcM m β) (state : TcState m) :
    (x >>= k) state = match x state with
      | .ok value after => k value after
      | .error err after => .error err after := by
  show EStateM.bind x k state = _
  unfold EStateM.bind
  cases x state <;> rfl

/-- An already-seen exact specialization is a state-preserving no-op.  In
particular, semantic equality at a different structural key cannot select
this branch. -/
theorem appendNestedAuxiliary_existing
    (request : NestedFlatAuxiliaryRequest m)
    {flat : Array (FlatBlockMember m)}
    {auxSeen : Array NestedSpecializationKey} {univOffset : UInt64}
    {methods : Methods m} {initial : TcState m}
    (seen : auxSeen.contains request.key = true) :
    (appendNestedAuxiliary request.id request.occurrenceUs
      request.specParams request.ownParams request.nIndices request.ctors
      request.lvls flat auxSeen univOffset).run methods initial =
        .ok (flat, auxSeen) initial := by
  unfold NestedFlatAuxiliaryRequest.key at seen
  have seen_mem :
      NestedSpecializationKey.ofApplication request.id.addr
        request.occurrenceUs request.specParams ∈ auxSeen :=
    Array.contains_iff_mem.mp seen
  unfold appendNestedAuxiliary
  simp [seen_mem]
  rfl

/-- Decompose a successful fresh append into shifted-universe construction and
the exact physical member/key pair returned by production. -/
theorem appendNestedAuxiliary_fresh
    (request : NestedFlatAuxiliaryRequest m)
    {flat : Array (FlatBlockMember m)}
    {auxSeen : Array NestedSpecializationKey} {univOffset : UInt64}
    {methods : Methods m} {initial final : TcState m}
    {result : Array (FlatBlockMember m) ×
      Array NestedSpecializationKey}
    (fresh : auxSeen.contains request.key = false)
    (run :
      (appendNestedAuxiliary request.id request.occurrenceUs
        request.specParams request.ownParams request.nIndices request.ctors
        request.lvls flat auxSeen univOffset).run methods initial =
          .ok result final) :
    NestedAuxiliaryAppendTrace request flat auxSeen univOffset methods initial
      final result := by
  unfold NestedFlatAuxiliaryRequest.key at fresh
  unfold appendNestedAuxiliary at run
  simp only [fresh, Bool.false_eq_true, if_false, ReaderT.run_bind,
    ReaderT.run_pure, pure_bind] at run
  change EStateM.bind ((mkIndUnivs request.lvls univOffset).run methods) _
    initial = .ok result final at run
  unfold EStateM.bind at run
  cases huniverses : (mkIndUnivs request.lvls univOffset).run methods initial with
  | error err after =>
      rw [huniverses] at run
      contradiction
  | ok indUs after =>
      rw [huniverses] at run
      cases run
      exact ⟨indUs, fresh, huniverses, rfl⟩

/-- A successful production append is completely classified at the returned
pair: it is either the exact no-op for an existing key or one fresh,
source-ordered member/key append. -/
theorem appendNestedAuxiliary_transition
    (request : NestedFlatAuxiliaryRequest m)
    {flat : Array (FlatBlockMember m)}
    {auxSeen : Array NestedSpecializationKey} {univOffset : UInt64}
    {methods : Methods m} {initial final : TcState m}
    {result : Array (FlatBlockMember m) ×
      Array NestedSpecializationKey}
    (run :
      (appendNestedAuxiliary request.id request.occurrenceUs
        request.specParams request.ownParams request.nIndices request.ctors
        request.lvls flat auxSeen univOffset).run methods initial =
          .ok result final) :
    FlatAuxTransition flat auxSeen result := by
  generalize seen_eq : auxSeen.contains request.key = seen at run
  cases seen with
  | false =>
      rcases appendNestedAuxiliary_fresh request seen_eq run with
        ⟨indUs, _, _, result_eq⟩
      subst result
      apply FlatAuxTransition.fresh request indUs
      intro member
      have contained := Array.contains_iff_mem.mpr member
      rw [seen_eq] at contained
      contradiction
  | true =>
      rw [appendNestedAuxiliary_existing request seen_eq] at run
      cases run
      exact .unchanged

/-- The production append action preserves the key/member invariant in both
branches.  It also establishes that the requested exact key is represented:
the existing branch obtains the witness from the input invariant, while the
fresh branch uses the member actually returned by `mkIndUnivs`. -/
theorem appendNestedAuxiliary_seenSound
    (request : NestedFlatAuxiliaryRequest m)
    {flat : Array (FlatBlockMember m)}
    {auxSeen : Array NestedSpecializationKey} {univOffset : UInt64}
    {methods : Methods m} {initial final : TcState m}
    {result : Array (FlatBlockMember m) ×
      Array NestedSpecializationKey}
    (sound : FlatAuxSeenSound flat auxSeen)
    (run :
      (appendNestedAuxiliary request.id request.occurrenceUs
        request.specParams request.ownParams request.nIndices request.ctors
        request.lvls flat auxSeen univOffset).run methods initial =
          .ok result final) :
    FlatAuxSeenSound result.1 result.2 ∧
      FlatAuxPresent request.key result.1 := by
  generalize seen_eq : auxSeen.contains request.key = seen at run
  cases seen with
  | false =>
      rcases appendNestedAuxiliary_fresh request seen_eq run with
        ⟨indUs, _, _, result_eq⟩
      subst result
      constructor
      · apply FlatAuxSeenSound.push sound
        · rfl
        · rfl
      · exact ⟨request.member indUs, Array.mem_push_self, rfl, rfl⟩
  | true =>
      have seen_mem : request.key ∈ auxSeen :=
        Array.contains_iff_mem.mp seen_eq
      rw [appendNestedAuxiliary_existing request seen_eq] at run
      cases run
      exact ⟨sound, sound request.key seen_mem⟩

/-- Every successful core nested-detection execution has the complete
representation-level effect classified by `FlatAuxTransition`.  The proof
exhausts all production early returns; the only changing branch is the named
append action rather than a callback-wide assumption. -/
theorem tryDetectNestedCore_transition
    (dom : KExpr m) (blockAddrs : Array Address)
    (flat : Array (FlatBlockMember m))
    (auxSeen : Array NestedSpecializationKey) (univOffset : UInt64)
    (paramDepth : Nat) (nRecParams : UInt64)
    (methods : Methods m) (initial final : TcState m)
    (result : Array (FlatBlockMember m) × Array NestedSpecializationKey)
    (run :
      (tryDetectNestedCore dom blockAddrs flat auxSeen univOffset paramDepth
        nRecParams).run methods initial = .ok result final) :
    FlatAuxTransition flat auxSeen result := by
  unfold tryDetectNestedCore at run
  rw [ReaderT.run_bind, runTcBindForFlatAuxiliary] at run
  generalize hpeel_eq :
      (runBounded (fun cur => do
        match cur with
        | .all _ _ innerDom body _ =>
          let (open', _) ← TcM.openBinderAnon innerDom body
          return .next open'
        | _ => return .done cur) maxWhnfFuel.toNat dom).run methods initial =
      peel at run
  cases peel with
  | error err after =>
      simp only at run
      contradiction
  | ok cur after =>
      simp only at run
      rcases hspine : cur.collectSpine with ⟨head, args⟩
      rw [hspine] at run
      cases head
      case const headId occurrenceUs headInfo =>
        simp only at run
        by_cases hblock : blockAddrs.contains headId.addr = true
        · rw [if_pos hblock] at run
          cases run
          exact .unchanged
        · rw [if_neg hblock] at run
          simp only [pure_bind] at run
          by_cases horiginal :
              flat.any (fun mem => mem.id.addr == headId.addr && !mem.isAux) =
                true
          · rw [if_pos horiginal] at run
            cases run
            exact .unchanged
          · rw [if_neg horiginal] at run
            simp only [ReaderT.run_bind, ReaderT.run_monadLift] at run
            change EStateM.bind (TcM.tryGetConst headId) _ after = _ at run
            unfold EStateM.bind at run
            cases hlookup : TcM.tryGetConst headId after with
            | error err afterLookup =>
                rw [hlookup] at run
                contradiction
            | ok concrete afterLookup =>
                rw [hlookup] at run
                cases concrete with
                | none =>
                    simp only [ReaderT.run_pure] at run
                    cases run
                    exact .unchanged
                | some concrete =>
                    cases concrete <;> simp only at run
                    all_goals try {
                      simp only [ReaderT.run_pure] at run
                      cases run
                      exact .unchanged
                    }
                    rename_i indName levelParams extLvls extParams extIndices
                      isUnsafe block memberIdx indTy extCtors leanAll
                    by_cases harity : args.size < extParams.toNat
                    · rw [if_pos harity] at run
                      simp only [ReaderT.run_pure] at run
                      cases run
                      exact .unchanged
                    · rw [if_neg harity] at run
                      by_cases hnested :
                          (!(args.extract 0 extParams.toNat).any
                            (exprMentionsAnyAddr · blockAddrs)) = true
                      · rw [if_pos hnested] at run
                        simp only [ReaderT.run_pure] at run
                        cases run
                        exact .unchanged
                      · rw [if_neg hnested] at run
                        rw [ReaderT.run_bind] at run
                        change EStateM.bind
                          ((checkedNatMetadataSum "nested parameter scope"
                            #[paramDepth, nRecParams.toNat]).run methods) _
                            afterLookup = _ at run
                        unfold EStateM.bind at run
                        cases hbound :
                            (checkedNatMetadataSum "nested parameter scope"
                              #[paramDepth, nRecParams.toNat]).run methods
                                afterLookup with
                        | error err afterBound =>
                            rw [hbound] at run
                            contradiction
                        | ok paramBound afterBound =>
                            rw [hbound] at run
                            simp only at run
                            by_cases hs7 :
                                (!(args.extract 0 extParams.toNat).all
                                  (fun sp => !sp.hasFVars &&
                                    sp.lbr ≤ paramBound)) = true
                            · rw [if_pos hs7] at run
                              simp only [ReaderT.run_pure] at run
                              cases run
                              exact .unchanged
                            · rw [if_neg hs7] at run
                              let request : NestedFlatAuxiliaryRequest m :=
                                { id := headId
                                  occurrenceUs := occurrenceUs
                                  specParams :=
                                    args.extract 0 extParams.toNat
                                  ownParams := extParams
                                  nIndices := extIndices
                                  ctors := extCtors
                                  lvls := extLvls }
                              exact appendNestedAuxiliary_transition request
                                (by simpa [request] using run)
      all_goals try {
        simp only [ReaderT.run_pure] at run
        cases run
        exact .unchanged
      }

/-- The public detector retains the core transition classification after its
production local-context restoration.  Restoration changes only checker
state, never the returned flat block or deduplication array. -/
theorem tryDetectNested_transition
    (dom : KExpr m) (blockAddrs : Array Address)
    (flat : Array (FlatBlockMember m))
    (auxSeen : Array NestedSpecializationKey) (univOffset : UInt64)
    (paramDepth : Nat) (nRecParams : UInt64)
    (methods : Methods m) (initial final : TcState m)
    (result : Array (FlatBlockMember m) × Array NestedSpecializationKey)
    (run :
      (tryDetectNested dom blockAddrs flat auxSeen univOffset paramDepth
        nRecParams).run methods initial = .ok result final) :
    FlatAuxTransition flat auxSeen result := by
  unfold tryDetectNested at run
  rw [ReaderT.run_bind] at run
  change EStateM.bind (get : TcM m (TcState m)) _ initial = _ at run
  unfold EStateM.bind at run
  rw [show (get : TcM m (TcState m)) initial = .ok initial initial from rfl]
    at run
  simp only at run
  rw [ReaderT.run_bind] at run
  change EStateM.bind
    ((tryDetectNestedCore dom blockAddrs flat auxSeen univOffset paramDepth
      nRecParams).run methods) _ initial = _ at run
  unfold EStateM.bind at run
  cases hcore :
      (tryDetectNestedCore dom blockAddrs flat auxSeen univOffset paramDepth
        nRecParams).run methods initial with
  | error err afterCore =>
      rw [hcore] at run
      contradiction
  | ok coreResult afterCore =>
      rw [hcore] at run
      simp only at run
      rw [ReaderT.run_bind] at run
      change EStateM.bind
        ((modify fun s : TcState m =>
          { s with lctx := s.lctx.truncate initial.lctx.size } :
            RecM m Unit).run methods) _ afterCore = _ at run
      unfold EStateM.bind at run
      rw [show (modify fun s : TcState m =>
          { s with lctx := s.lctx.truncate initial.lctx.size } :
            RecM m Unit).run methods afterCore =
        .ok () { afterCore with
          lctx := afterCore.lctx.truncate initial.lctx.size } from rfl] at run
      simp only [ReaderT.run_pure] at run
      have coreTransition := tryDetectNestedCore_transition dom blockAddrs flat
        auxSeen univOffset paramDepth nRecParams methods initial afterCore
        coreResult hcore
      cases run
      exact coreTransition

/-- Every successful public nested detection preserves the exact key/member
soundness invariant. -/
theorem tryDetectNested_seenSound
    (dom : KExpr m) (blockAddrs : Array Address)
    (flat : Array (FlatBlockMember m))
    (auxSeen : Array NestedSpecializationKey) (univOffset : UInt64)
    (paramDepth : Nat) (nRecParams : UInt64)
    (methods : Methods m) (initial final : TcState m)
    (result : Array (FlatBlockMember m) × Array NestedSpecializationKey)
    (sound : FlatAuxSeenSound flat auxSeen)
    (run :
      (tryDetectNested dom blockAddrs flat auxSeen univOffset paramDepth
        nRecParams).run methods initial = .ok result final) :
    FlatAuxSeenSound result.1 result.2 :=
  (tryDetectNested_transition dom blockAddrs flat auxSeen univOffset
    paramDepth nRecParams methods initial final result run).seenSound sound

/-- A successful constructor-field scan is a source-ordered history of the
exact detector effects from its input pair to its returned pair. -/
theorem scanFlatConstructorFields_history
    (allBlockAddrs : Array Address) (nRecParams univOffset : UInt64)
    (paramDepth : Nat) (methods : Methods m) :
    ∀ {remaining : Nat} {cur : KExpr m}
      {pair result :
        Array (FlatBlockMember m) × Array NestedSpecializationKey}
      {initial final : TcState m},
      (scanFlatConstructorFields allBlockAddrs nRecParams univOffset
        paramDepth remaining cur pair).run methods initial =
          .ok result final →
      FlatAuxHistory m pair result
  | 0, cur, pair, result, initial, final, run => by
      simp only [scanFlatConstructorFields, ReaderT.run_pure] at run
      cases run
      exact .refl pair
  | remaining + 1, cur, pair, result, initial, final, run => by
      rw [scanFlatConstructorFields, ReaderT.run_bind,
        runTcBindForFlatAuxiliary] at run
      cases hwhnf : (whnf cur).run methods initial with
      | error err afterWhnf =>
          rw [hwhnf] at run
          contradiction
      | ok w afterWhnf =>
          rw [hwhnf] at run
          cases w with
          | all name bi dom body info =>
              simp only at run
              rw [ReaderT.run_bind] at run
              change EStateM.bind
                ((tryDetectNested dom allBlockAddrs pair.1 pair.2 univOffset
                  paramDepth nRecParams).run methods) _ afterWhnf = _ at run
              unfold EStateM.bind at run
              cases hdetect :
                  (tryDetectNested dom allBlockAddrs pair.1 pair.2 univOffset
                    paramDepth nRecParams).run methods afterWhnf with
              | error err afterDetect =>
                  rw [hdetect] at run
                  contradiction
              | ok detected afterDetect =>
                  rw [hdetect] at run
                  simp only at run
                  rw [ReaderT.run_bind, ReaderT.run_monadLift] at run
                  change EStateM.bind (TcM.openBinderAnon dom body) _
                    afterDetect = _ at run
                  unfold EStateM.bind at run
                  cases hopen : TcM.openBinderAnon dom body afterDetect with
                  | error err afterOpen =>
                      rw [hopen] at run
                      contradiction
                  | ok opened afterOpen =>
                      rcases opened with ⟨openBody, fv⟩
                      rw [hopen] at run
                      simp only at run
                      exact .step
                        (tryDetectNested_transition dom allBlockAddrs pair.1
                          pair.2 univOffset paramDepth nRecParams methods
                          afterWhnf afterDetect detected hdetect)
                        (scanFlatConstructorFields_history allBlockAddrs
                          nRecParams univOffset paramDepth methods run)
          | var idx name info =>
              simp only [ReaderT.run_pure] at run
              cases run
              exact .refl pair
          | fvar id name info =>
              simp only [ReaderT.run_pure] at run
              cases run
              exact .refl pair
          | sort level info =>
              simp only [ReaderT.run_pure] at run
              cases run
              exact .refl pair
          | const id us info =>
              simp only [ReaderT.run_pure] at run
              cases run
              exact .refl pair
          | app fn arg info =>
              simp only [ReaderT.run_pure] at run
              cases run
              exact .refl pair
          | lam name bi dom body info =>
              simp only [ReaderT.run_pure] at run
              cases run
              exact .refl pair
          | letE name ty value body nonDep info =>
              simp only [ReaderT.run_pure] at run
              cases run
              exact .refl pair
          | prj id field value info =>
              simp only [ReaderT.run_pure] at run
              cases run
              exact .refl pair
          | nat value blob info =>
              simp only [ReaderT.run_pure] at run
              cases run
              exact .refl pair
          | str value blob info =>
              simp only [ReaderT.run_pure] at run
              cases run
              exact .refl pair

/-- A successful scan of one constructor retains exactly the history produced
by its field scan; lookup, universe instantiation, parameter substitution,
and lctx restoration cannot modify the returned flat pair. -/
theorem scanFlatConstructor_history
    (allBlockAddrs : Array Address) (nRecParams univOffset : UInt64)
    (member : FlatBlockMember m) (ctorId : KId m)
    (methods : Methods m) (initial final : TcState m)
    (pair result :
      Array (FlatBlockMember m) × Array NestedSpecializationKey)
    (run :
      (scanFlatConstructor allBlockAddrs nRecParams univOffset member ctorId
        pair).run methods initial = .ok result final) :
    FlatAuxHistory m pair result := by
  unfold scanFlatConstructor at run
  rw [ReaderT.run_bind, ReaderT.run_monadLift] at run
  change EStateM.bind (TcM.tryGetConst ctorId) _ initial = _ at run
  unfold EStateM.bind at run
  cases hlookup : TcM.tryGetConst ctorId initial with
  | error err afterLookup =>
      rw [hlookup] at run
      contradiction
  | ok concrete afterLookup =>
      rw [hlookup] at run
      cases concrete with
      | none =>
          simp only [ReaderT.run_pure] at run
          cases run
          exact .refl pair
      | some concrete =>
          cases concrete <;> simp only at run
          all_goals try {
            simp only [ReaderT.run_pure] at run
            cases run
            exact .refl pair
          }
          rename_i ctorName levelParams isUnsafe ctorLvls induct cidx params
            fields ctorTy
          rw [ReaderT.run_bind, ReaderT.run_monadLift] at run
          change EStateM.bind
            (TcM.instantiateUnivParams ctorTy member.occurrenceUs) _
              afterLookup = _ at run
          unfold EStateM.bind at run
          cases hinstantiate :
              TcM.instantiateUnivParams ctorTy member.occurrenceUs afterLookup
                with
          | error err afterInstantiate =>
              rw [hinstantiate] at run
              contradiction
          | ok ctorTyInst afterInstantiate =>
              rw [hinstantiate] at run
              simp only at run
              rw [ReaderT.run_bind] at run
              change EStateM.bind
                ((get : RecM m (TcState m)).run methods) _ afterInstantiate =
                  _ at run
              unfold EStateM.bind at run
              rw [show (get : RecM m (TcState m)).run methods
                afterInstantiate = .ok afterInstantiate afterInstantiate from
                  rfl] at run
              simp only at run
              rw [ReaderT.run_bind] at run
              change EStateM.bind
                ((instantiateFlatConstructorParams member nRecParams
                  member.ownParams.toNat 0 ctorTyInst).run methods) _
                    afterInstantiate = _ at run
              unfold EStateM.bind at run
              cases hparams :
                  (instantiateFlatConstructorParams member nRecParams
                    member.ownParams.toNat 0 ctorTyInst).run methods
                      afterInstantiate with
              | error err afterParams =>
                  rw [hparams] at run
                  contradiction
              | ok cur afterParams =>
                  rw [hparams] at run
                  simp only at run
                  rw [ReaderT.run_bind] at run
                  change EStateM.bind
                    ((scanFlatConstructorFields allBlockAddrs nRecParams
                      univOffset afterInstantiate.lctx.size fields.toNat cur
                        pair).run methods) _ afterParams = _ at run
                  unfold EStateM.bind at run
                  cases hfields :
                      (scanFlatConstructorFields allBlockAddrs nRecParams
                        univOffset afterInstantiate.lctx.size fields.toNat cur
                          pair).run methods afterParams with
                  | error err afterFields =>
                      rw [hfields] at run
                      contradiction
                  | ok fieldResult afterFields =>
                      rw [hfields] at run
                      simp only at run
                      rw [ReaderT.run_bind] at run
                      change EStateM.bind
                        ((modify fun s : TcState m =>
                          { s with lctx :=
                            s.lctx.truncate afterInstantiate.lctx.size } :
                            RecM m Unit).run methods) _ afterFields = _ at run
                      unfold EStateM.bind at run
                      rw [show (modify fun s : TcState m =>
                          { s with lctx :=
                            s.lctx.truncate afterInstantiate.lctx.size } :
                            RecM m Unit).run methods afterFields =
                        .ok () { afterFields with lctx :=
                          (afterFields.lctx.truncate
                            afterInstantiate.lctx.size) } from rfl] at run
                      simp only [ReaderT.run_pure] at run
                      have history :=
                        scanFlatConstructorFields_history allBlockAddrs
                          nRecParams univOffset afterInstantiate.lctx.size
                            methods hfields
                      cases run
                      exact history

/-- A successful constructor-list scan composes the exact per-constructor
histories in source order. -/
theorem scanFlatConstructors_history
    (allBlockAddrs : Array Address) (nRecParams univOffset : UInt64)
    (member : FlatBlockMember m) (methods : Methods m) :
    ∀ {ctorIds : List (KId m)}
      {pair result :
        Array (FlatBlockMember m) × Array NestedSpecializationKey}
      {initial final : TcState m},
      (scanFlatConstructors allBlockAddrs nRecParams univOffset member ctorIds
        pair).run methods initial = .ok result final →
      FlatAuxHistory m pair result
  | [], pair, result, initial, final, run => by
      simp only [scanFlatConstructors, ReaderT.run_pure] at run
      cases run
      exact .refl pair
  | ctorId :: ctorIds, pair, result, initial, final, run => by
      rw [scanFlatConstructors, ReaderT.run_bind] at run
      change EStateM.bind
        ((scanFlatConstructor allBlockAddrs nRecParams univOffset member
          ctorId pair).run methods) _ initial = _ at run
      unfold EStateM.bind at run
      cases hctor :
          (scanFlatConstructor allBlockAddrs nRecParams univOffset member
            ctorId pair).run methods initial with
      | error err afterCtor =>
          rw [hctor] at run
          contradiction
      | ok middle afterCtor =>
          rw [hctor] at run
          simp only at run
          exact (scanFlatConstructor_history allBlockAddrs nRecParams
            univOffset member ctorId methods initial afterCtor pair middle
              hctor).trans
            (scanFlatConstructors_history allBlockAddrs nRecParams univOffset
              member methods run)

/-- One successful production queue callback carries exactly the history
produced by the selected member's source-ordered constructor list. -/
theorem buildFlatBlockQueueStep_history
    (allBlockAddrs : Array Address) (nRecParams univOffset : UInt64)
    (state : FlatBlockQueueState m) (methods : Methods m)
    (initial final : TcState m)
    (output : BoundedStep (FlatBlockQueueState m)
      (Array (FlatBlockMember m) × Array NestedSpecializationKey))
    (run :
      (buildFlatBlockQueueStep allBlockAddrs nRecParams univOffset state).run
        methods initial = .ok output final) :
    FlatAuxQueueStepHistory state output := by
  rcases state with ⟨qi, flat0, auxSeen0⟩
  unfold buildFlatBlockQueueStep at run
  simp only at run
  by_cases hdone : qi ≥ flat0.size
  · rw [if_pos hdone] at run
    simp only [ReaderT.run_pure] at run
    cases run
    exact .refl (flat0, auxSeen0)
  · rw [if_neg hdone] at run
    rw [ReaderT.run_bind] at run
    change EStateM.bind
      ((scanFlatConstructors allBlockAddrs nRecParams univOffset flat0[qi]!
        flat0[qi]!.ctors.toList (flat0, auxSeen0)).run methods) _ initial = _
          at run
    unfold EStateM.bind at run
    cases hscan :
        (scanFlatConstructors allBlockAddrs nRecParams univOffset flat0[qi]!
          flat0[qi]!.ctors.toList (flat0, auxSeen0)).run methods initial with
    | error err afterScan =>
        rw [hscan] at run
        contradiction
    | ok pair afterScan =>
        rw [hscan] at run
        simp only at run
        have history := scanFlatConstructors_history allBlockAddrs nRecParams
          univOffset flat0[qi]! methods hscan
        cases run
        exact history

/-- Generic fuel induction for a bounded flat-block queue whose successful
callbacks expose exact source-ordered histories. -/
theorem runBounded_flatAuxHistory
    (step : FlatBlockQueueState m →
      RecM m (BoundedStep (FlatBlockQueueState m)
        (Array (FlatBlockMember m) × Array NestedSpecializationKey)))
    (step_history : ∀ state methods initial final output,
      (step state).run methods initial = .ok output final →
      FlatAuxQueueStepHistory state output)
    (methods : Methods m) :
    ∀ {fuel : Nat} {state : FlatBlockQueueState m}
      {initial final : TcState m}
      {result : Array (FlatBlockMember m) × Array NestedSpecializationKey},
      (runBounded step fuel state).run methods initial = .ok result final →
      FlatAuxHistory m (flatAuxQueuePair state) result
  | 0, state, initial, final, result, run => by
      simp only [runBounded, throw, ReaderT.run] at run
      contradiction
  | fuel + 1, state, initial, final, result, run => by
      rw [runBounded, ReaderT.run_bind] at run
      change EStateM.bind ((step state).run methods) _ initial = _ at run
      unfold EStateM.bind at run
      cases hstep : (step state).run methods initial with
      | error err afterStep =>
          rw [hstep] at run
          contradiction
      | ok output afterStep =>
          rw [hstep] at run
          cases output with
          | done doneResult =>
              simp only [ReaderT.run_pure] at run
              have history := step_history state methods initial afterStep
                (.done doneResult) hstep
              cases run
              exact history
          | next nextState =>
              simp only at run
              exact (step_history state methods initial afterStep
                (.next nextState) hstep).trans
                (runBounded_flatAuxHistory step step_history methods run)

/-- Seeding original block members preserves the exact auxiliary
representation because every appended seed has `isAux = false`. -/
theorem seedFlatBlockMembers_exact
    (nRecParams univOffset : UInt64) (methods : Methods m) :
    ∀ {indIds : List (KId m)} {flat result : Array (FlatBlockMember m)}
      {auxSeen : Array NestedSpecializationKey}
      {initial final : TcState m},
      FlatAuxQueueExact flat auxSeen →
      (seedFlatBlockMembers nRecParams univOffset indIds flat).run methods
        initial = .ok result final →
      FlatAuxQueueExact result auxSeen
  | [], flat, result, auxSeen, initial, final, exact, run => by
      simp only [seedFlatBlockMembers, ReaderT.run_pure] at run
      cases run
      exact exact
  | indId :: indIds, flat, result, auxSeen, initial, final, exact, run => by
      rw [seedFlatBlockMembers, ReaderT.run_bind, ReaderT.run_monadLift] at run
      change EStateM.bind (TcM.getConst indId) _ initial = _ at run
      unfold EStateM.bind at run
      cases hlookup : TcM.getConst indId initial with
      | error err afterLookup =>
          rw [hlookup] at run
          contradiction
      | ok concrete afterLookup =>
          rw [hlookup] at run
          cases concrete <;> simp only at run
          all_goals try {
            exact seedFlatBlockMembers_exact nRecParams univOffset methods
              exact run
          }
          rename_i indName levelParams lvls ownParams nIndices isUnsafe block
            memberIdx indTy ctors leanAll
          rw [ReaderT.run_bind] at run
          change EStateM.bind ((mkIndUnivs lvls univOffset).run methods) _
            afterLookup = _ at run
          unfold EStateM.bind at run
          cases huniverses : (mkIndUnivs lvls univOffset).run methods
              afterLookup with
          | error err afterUniverses =>
              rw [huniverses] at run
              contradiction
          | ok indUs afterUniverses =>
              rw [huniverses] at run
              simp only at run
              apply seedFlatBlockMembers_exact nRecParams univOffset methods
                (exact.pushOriginal
                  { id := indId
                    isAux := false
                    specParams := mkFlatBlockSpecParams nRecParams
                    ownParams := ownParams
                    nIndices := nIndices
                    ctors := ctors
                    lvls := lvls
                    indUs := indUs
                    occurrenceUs := indUs }
                  rfl)
                run

/-- Every successful production flat-block build has a sound, source-ordered,
duplicate-free auxiliary representation.  This theorem starts from the real
original-member seeding execution and the real bounded queue, with no
whole-callback or `InductiveOracle` premise. -/
theorem buildFlatBlockWithAuxSeen_exact
    (blockInds : Array (KId m)) (nRecParams univOffset : UInt64)
    (methods : Methods m) (initial final : TcState m)
    (result : Array (FlatBlockMember m) × Array NestedSpecializationKey)
    (run :
      (buildFlatBlockWithAuxSeen blockInds nRecParams univOffset).run methods
        initial = .ok result final) :
    FlatAuxSeenSound result.1 result.2 ∧
      FlatAuxQueueExact result.1 result.2 := by
  unfold buildFlatBlockWithAuxSeen at run
  simp only at run
  rw [ReaderT.run_bind] at run
  change EStateM.bind
    ((seedFlatBlockMembers nRecParams univOffset blockInds.toList #[]).run
      methods) _ initial = _ at run
  unfold EStateM.bind at run
  cases hseed :
      (seedFlatBlockMembers nRecParams univOffset blockInds.toList #[]).run
        methods initial with
  | error err afterSeed =>
      rw [hseed] at run
      contradiction
  | ok seeded afterSeed =>
      rw [hseed] at run
      simp only at run
      have history := runBounded_flatAuxHistory
        (buildFlatBlockQueueStep (blockInds.map (·.addr)) nRecParams
          univOffset)
        (fun state methods initial final output stepRun =>
          buildFlatBlockQueueStep_history (blockInds.map (·.addr))
            nRecParams univOffset state methods initial final output stepRun)
        methods run
      have seedExact : FlatAuxQueueExact seeded #[] :=
        seedFlatBlockMembers_exact nRecParams univOffset methods
          FlatAuxQueueExact.empty hseed
      exact ⟨history.seenSound (FlatAuxSeenSound.empty seeded),
        seedExact.history history⟩

/-- The public flat-block wrapper therefore returns a physically
source-ordered, duplicate-free auxiliary list.  The existential `auxSeen` is
the exact array produced by the underlying production run, not a reconstructed
or oracle-supplied catalog. -/
theorem buildFlatBlock_auxiliaryOrder
    (blockInds : Array (KId m)) (nRecParams univOffset : UInt64)
    (methods : Methods m) (initial final : TcState m)
    (flat : Array (FlatBlockMember m))
    (run :
      (buildFlatBlock blockInds nRecParams univOffset).run methods initial =
        .ok flat final) :
    ∃ auxSeen,
      (buildFlatBlockWithAuxSeen blockInds nRecParams univOffset).run methods
        initial = .ok (flat, auxSeen) final ∧
      FlatAuxSeenSound flat auxSeen ∧ FlatAuxQueueExact flat auxSeen := by
  unfold buildFlatBlock at run
  rw [ReaderT.run_bind] at run
  change EStateM.bind
    ((buildFlatBlockWithAuxSeen blockInds nRecParams univOffset).run methods)
      _ initial = _ at run
  unfold EStateM.bind at run
  cases hbuild :
      (buildFlatBlockWithAuxSeen blockInds nRecParams univOffset).run methods
        initial with
  | error err afterBuild =>
      rw [hbuild] at run
      contradiction
  | ok pair afterBuild =>
      rw [hbuild] at run
      simp only [ReaderT.run_pure] at run
      rcases pair with ⟨builtFlat, auxSeen⟩
      have buildExact := buildFlatBlockWithAuxSeen_exact blockInds nRecParams
        univOffset methods initial afterBuild (builtFlat, auxSeen) hbuild
      cases run
      refine ⟨auxSeen, ?_, buildExact.1, buildExact.2⟩
      rfl

end RecM

/-- Proof-relevant evidence that a request is the exact auxiliary request
extracted from one complete successful production nested-positivity run.  The
header fields and fresh/existing classification remain tied to the concrete
lookup selected by that run. -/
def NestedPositivityAuxiliaryRequest.ProducedBy
    (request : NestedPositivityAuxiliaryRequest m)
    (fuel : Nat) (id : KId m) (us : Array (KUniv m))
    (args : Array (KExpr m)) (groups : Array (PositivityGroup m))
    (rootAddrs activeAddrs : Array Address) (methods : Methods m)
    (initial final : TcState m) : Prop :=
  request.id = id ∧ request.universes = us ∧
    request.arguments = args ∧
    ∃ concrete afterLookup,
      TcM.getConst request.id initial = .ok concrete afterLookup ∧
      concrete.NestedPositiveHeader request.nParams request.nIndices
        request.levels request.block request.ctors ∧
      request.arguments.size = request.nParams + request.nIndices ∧
      request.universes.size = request.levels ∧
      ((∃ group,
          RecM.findNestedPositivityGroup? groups request.id.addr
            request.universes request.arguments request.nParams =
              some group ∧
          PositivityFlatIdentity group request.id.addr request.universes
            request.arguments request.nParams ∧
          RecM.positiveIndicesIndependent request.arguments request.nParams
            rootAddrs = true ∧
          final = afterLookup) ∨
        (RecM.findNestedPositivityGroup? groups request.id.addr
            request.universes request.arguments request.nParams = none ∧
          RecM.nestedParametersMentionRoot request.arguments request.nParams
            rootAddrs = true ∧
          RecM.positiveIndicesIndependent request.arguments request.nParams
            rootAddrs = true ∧
          CompleteFreshNestedPositivityTrace fuel request.universes
            request.arguments groups activeAddrs request.nParams
            request.block request.ctors methods afterLookup final))

/-- A complete successful nested application exposes either an already-active
specialization with the flat identity proof, or a fresh exact request whose
constructor expansion was traversed by production. -/
theorem CompleteNestedPositivityApplicationTrace.auxiliaryRequest
    {fuel : Nat} {id : KId m} {us : Array (KUniv m)}
    {args : Array (KExpr m)} {groups : Array (PositivityGroup m)}
    {rootAddrs activeAddrs : Array Address} {methods : Methods m}
    {initial final : TcState m}
    (trace : CompleteNestedPositivityApplicationTrace fuel id us args groups
      rootAddrs activeAddrs methods initial final) :
    ∃ request : NestedPositivityAuxiliaryRequest m,
      request.id = id ∧ request.universes = us ∧
      request.arguments = args ∧
      (∃ concrete afterLookup,
        TcM.getConst request.id initial = .ok concrete afterLookup ∧
        concrete.NestedPositiveHeader request.nParams request.nIndices
          request.levels request.block request.ctors ∧
        request.arguments.size = request.nParams + request.nIndices ∧
        request.universes.size = request.levels ∧
        ((∃ group,
            RecM.findNestedPositivityGroup? groups request.id.addr
              request.universes request.arguments request.nParams =
                some group ∧
            PositivityFlatIdentity group request.id.addr request.universes
              request.arguments request.nParams ∧
            RecM.positiveIndicesIndependent request.arguments request.nParams
              rootAddrs = true ∧
            final = afterLookup) ∨
          (RecM.findNestedPositivityGroup? groups request.id.addr
              request.universes request.arguments request.nParams = none ∧
            RecM.nestedParametersMentionRoot request.arguments request.nParams
              rootAddrs = true ∧
            RecM.positiveIndicesIndependent request.arguments request.nParams
              rootAddrs = true ∧
            CompleteFreshNestedPositivityTrace fuel request.universes
              request.arguments groups activeAddrs request.nParams
              request.block request.ctors methods afterLookup final))) := by
  rcases trace with ⟨concrete, nParams, nIndices, levels, block, ctors,
    afterLookup, lookup, header, argsSize, usSize, checked⟩
  let request : NestedPositivityAuxiliaryRequest m :=
    { id, universes := us, arguments := args, nParams, nIndices, levels,
      block, ctors }
  refine ⟨request, rfl, rfl, rfl, concrete, afterLookup, lookup, header,
    argsSize, usSize, ?_⟩
  cases checked with
  | existing group state selected indicesIndependent =>
      have identity := (RecM.findNestedPositivityGroup?_some selected).2.2
      exact Or.inl ⟨group, selected, identity, indicesIndependent, rfl⟩
  | fresh absent parameterMention indicesIndependent continuation =>
      exact Or.inr ⟨absent, parameterMention, indicesIndependent,
        continuation⟩

/-- Package `auxiliaryRequest` behind the named request-production relation
used by concrete cross-stage reachability fixtures. -/
theorem CompleteNestedPositivityApplicationTrace.producedRequest
    {fuel : Nat} {id : KId m} {us : Array (KUniv m)}
    {args : Array (KExpr m)} {groups : Array (PositivityGroup m)}
    {rootAddrs activeAddrs : Array Address} {methods : Methods m}
    {initial final : TcState m}
    (trace : CompleteNestedPositivityApplicationTrace fuel id us args groups
      rootAddrs activeAddrs methods initial final) :
    ∃ request : NestedPositivityAuxiliaryRequest m,
      request.ProducedBy fuel id us args groups rootAddrs activeAddrs methods
        initial final := by
  simpa only [NestedPositivityAuxiliaryRequest.ProducedBy] using
    trace.auxiliaryRequest

end Ix.Tc
