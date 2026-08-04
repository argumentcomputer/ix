import Ix.Tc.Verify.Inductive.NestedAuxiliaryExpansion
import Ix.Tc.Verify.Env

/-!
# Generated recursor metadata from the certified flat block

Generated recursor types are stateful artifacts: constructing one may intern
expressions, reduce types, and update caches before the next family is visited.
The seven cached header fields are not callbacks, however.  They must be the
positionally corresponding data from the exact flat block plus the checked
block-wide arities.

This module proves that separation directly over the named production loop.
The induction retains the metadata array for the already-visited flat prefix;
it makes no assumption about the expression returned by `buildRecType` or the
state in which that callback succeeds.
-/

namespace Ix.Tc

namespace GeneratedRecursorMetadata

/-- Exact metadata array determined by a validated flat block and its checked
block-wide recursor inputs. -/
def expectedFlat (flat : Array (FlatBlockMember m))
    (recLvls nParams nMinors : UInt64) (blockIsUnsafe : Bool) :
    Array GeneratedRecursorMetadata :=
  flat.map fun member =>
    member.generatedRecursorMetadata flat recLvls nParams nMinors
      blockIsUnsafe

/-- Metadata already constructed for the half-open flat prefix `[0, di)`. -/
def MatchesPrefix (flat : Array (FlatBlockMember m))
    (recLvls nParams nMinors : UInt64) (blockIsUnsafe : Bool) (di : Nat)
    (generated : Array (GeneratedRecursor m)) : Prop :=
  generated.map GeneratedRecursor.metadata =
    (flat.extract 0 di).map fun member =>
      member.generatedRecursorMetadata flat recLvls nParams nMinors
        blockIsUnsafe

end GeneratedRecursorMetadata

/-- Array equality exposes the intended positional contract: every generated
entry has an in-bounds flat member at the same index and carries exactly that
member's seven canonical header fields. -/
theorem GeneratedRecursorMetadata.at_of_expectedFlat
    (flat : Array (FlatBlockMember m))
    (generated : Array (GeneratedRecursor m))
    (recLvls nParams nMinors : UInt64) (blockIsUnsafe : Bool)
    (hmatches : generated.map GeneratedRecursor.metadata =
      GeneratedRecursorMetadata.expectedFlat flat recLvls nParams nMinors
        blockIsUnsafe)
    (i : Nat) (generatedBound : i < generated.size) :
    ∃ flatBound : i < flat.size,
      generated[i].metadata =
        flat[i].generatedRecursorMetadata flat recLvls nParams nMinors
          blockIsUnsafe := by
  have matches' : generated.map GeneratedRecursor.metadata =
      flat.map fun member => member.generatedRecursorMetadata flat recLvls
        nParams nMinors blockIsUnsafe := by
    simpa only [GeneratedRecursorMetadata.expectedFlat] using hmatches
  have sameSize : generated.size = flat.size := by
    have sizes := congrArg Array.size matches'
    simpa only [Array.size_map] using sizes
  have flatBound : i < flat.size := by omega
  refine ⟨flatBound, ?_⟩
  have point := congrArg
    (fun values : Array GeneratedRecursorMetadata => values[i]?) matches'
  simp only [Array.getElem?_map,
    Array.getElem?_eq_getElem generatedBound,
    Array.getElem?_eq_getElem flatBound, Option.map_some] at point
  exact Option.some.inj point

@[simp] theorem initialGeneratedRecursor_metadata
    (member : FlatBlockMember m) (flat : Array (FlatBlockMember m))
    (recLvls nParams nMinors : UInt64) (blockIsUnsafe : Bool)
    (recType : KExpr m) :
    (RecM.initialGeneratedRecursor member flat recLvls nParams nMinors
      blockIsUnsafe recType).metadata =
        member.generatedRecursorMetadata flat recLvls nParams nMinors
          blockIsUnsafe := by
  rfl

/-- Installing equations cannot change any canonical header field. -/
@[simp] theorem GeneratedRecursor.metadata_setRules
    (generated : GeneratedRecursor m) (rules : Array (RecRule m)) :
    ({ generated with rules := rules }).metadata = generated.metadata := by
  rfl

/-- The production rule replacement primitive preserves metadata exactly. -/
@[simp] theorem GeneratedRecursor.metadata_withRules
    (generated : GeneratedRecursor m) (rules : Array (RecRule m)) :
    (generated.withRules rules).metadata = generated.metadata := by
  rfl

/-- The production rule replacement primitive preserves the generated
recursor type exactly. -/
@[simp] theorem GeneratedRecursor.ty_withRules
    (generated : GeneratedRecursor m) (rules : Array (RecRule m)) :
    (generated.withRules rules).ty = generated.ty := by
  rfl

/-- Updating one family through the production rule replacement primitive
preserves the complete positional metadata array, whether or not the index is
in bounds. -/
theorem GeneratedRecursor.map_metadata_modify_withRules
    (generated : Array (GeneratedRecursor m)) (index : Nat)
    (rules : Array (RecRule m)) :
    (generated.modify index (·.withRules rules)).map
        GeneratedRecursor.metadata =
      generated.map GeneratedRecursor.metadata := by
  apply Array.ext
  · simp
  · intro i beforeBound afterBound
    simp only [Array.getElem_map]
    rw [Array.getElem_modify]
    split <;> simp

/-- Merging a complete rule array back into a same-length cache snapshot
preserves every cached header field. -/
theorem GeneratedRecursor.map_metadata_zipWithRules
    (cached generated : Array (GeneratedRecursor m))
    (sameSize : cached.size = generated.size) :
    (cached.zipWith (fun dst src => dst.withRules src.rules) generated).map
        GeneratedRecursor.metadata =
      cached.map GeneratedRecursor.metadata := by
  apply Array.ext
  · simp [sameSize]
  · intro i mergedBound cachedBound
    simp only [Array.getElem_map, Array.getElem_zipWith,
      GeneratedRecursor.metadata_withRules]

/-- Installing a same-length rule batch over immutable ingress headers
preserves every generated recursor type positionally. -/
theorem GeneratedRecursor.map_ty_zipWithRules
    (headers generated : Array (GeneratedRecursor m))
    (sameSize : headers.size = generated.size) :
    (headers.zipWith (fun header src => header.withRules src.rules)
        generated).map (fun recursor => recursor.ty) =
      headers.map (fun recursor => recursor.ty) := by
  apply Array.ext
  · simp [sameSize]
  · intro i installedBound headerBound
    simp only [Array.getElem_map, Array.getElem_zipWith,
      GeneratedRecursor.ty_withRules]

private theorem generatedRecursorMetadata_eq_of_beq
    (left right : GeneratedRecursorMetadata)
    (same : (left == right) = true) : left = right := by
  cases left with
  | mk leftAddr leftLvls leftParams leftMotives leftMinors leftIndices
      leftUnsafe =>
    cases right with
    | mk rightAddr rightLvls rightParams rightMotives rightMinors rightIndices
        rightUnsafe =>
      change (leftAddr == rightAddr &&
        (leftLvls == rightLvls &&
        (leftParams == rightParams &&
        (leftMotives == rightMotives &&
        (leftMinors == rightMinors &&
        (leftIndices == rightIndices && leftUnsafe == rightUnsafe)))))) = true
          at same
      simp only [Bool.and_eq_true, beq_iff_eq] at same
      rcases same with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl

local instance : LawfulBEq GeneratedRecursorMetadata where
  eq_of_beq := generatedRecursorMetadata_eq_of_beq _ _
  rfl := by
    intro metadata
    cases metadata with
    | mk indAddr lvls params motives minors indices isUnsafe =>
      change (indAddr == indAddr &&
        (lvls == lvls &&
        (params == params &&
        (motives == motives &&
        (minors == minors &&
        (indices == indices && isUnsafe == isUnsafe)))))) = true
      simp

namespace RecM

/-- A successful transactional commit rejects a missing, resized, or
metadata-mutated target cache and then discards all callback-written types and
rules. The installed batch consists exactly of immutable ingress headers/types
paired with the locally returned rule arrays. -/
theorem commitGeneratedRecursorRulesAt_artifacts
    (indBlockId : KId .anon)
    (expected generatedWithRules : Array (GeneratedRecursor .anon))
    (methods : Methods .anon) (initial final : TcState .anon)
    (run :
      (commitGeneratedRecursorRulesAt indBlockId expected
        generatedWithRules).run methods initial = .ok () final) :
    ∃ cached,
      initial.env.recursorCache[indBlockId]? = some cached ∧
      cached.size = expected.size ∧
      cached.map GeneratedRecursor.metadata =
        expected.map GeneratedRecursor.metadata ∧
      generatedWithRules.size = expected.size ∧
      final.env.recursorCache[indBlockId]? =
        some (expected.zipWith
          (fun header generated => header.withRules generated.rules)
          generatedWithRules) ∧
      (expected.zipWith
          (fun header generated => header.withRules generated.rules)
          generatedWithRules).map GeneratedRecursor.metadata =
          expected.map GeneratedRecursor.metadata ∧
      (expected.zipWith
          (fun header generated => header.withRules generated.rules)
          generatedWithRules).map (fun recursor => recursor.ty) =
        expected.map (fun recursor => recursor.ty) := by
  unfold commitGeneratedRecursorRulesAt at run
  rw [ReaderT.run_bind] at run
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ initial =
    .ok () final at run
  unfold EStateM.bind at run
  rw [show (get : TcM .anon (TcState .anon)) initial =
    .ok initial initial from rfl] at run
  simp only at run
  cases cacheEq : initial.env.recursorCache[indBlockId]? with
  | none =>
      rw [cacheEq] at run
      contradiction
  | some cached =>
      rw [cacheEq] at run
      simp only at run
      split at run
      · contradiction
      · next sameSizeBool =>
        have sameSize : cached.size = expected.size := by
          simpa using sameSizeBool
        split at run
        · next sameMetadataBool =>
          have sameMetadata :
              cached.map GeneratedRecursor.metadata =
                expected.map GeneratedRecursor.metadata :=
            eq_of_beq sameMetadataBool
          split at run
          · contradiction
          · next generatedSizeBool =>
            have generatedSize :
                generatedWithRules.size = expected.size := by
              simpa using generatedSizeBool
            simp only [modify, ReaderT.run] at run
            cases run
            refine ⟨cached, rfl, sameSize, sameMetadata, generatedSize, ?_,
              ?_, ?_⟩
            · rw [Std.HashMap.getElem?_insert, beq_self_eq_true]
              rfl
            · exact GeneratedRecursor.map_metadata_zipWithRules expected
                generatedWithRules generatedSize.symm
            · exact GeneratedRecursor.map_ty_zipWithRules expected
                generatedWithRules generatedSize.symm
        · contradiction

/-- The best-effort co-resident rule-population pass preserves the complete
metadata array even when individual rule builders fail and are recorded as
`none`.  State changes made while attempting RHS construction are unrestricted. -/
theorem populateOptionalGeneratedRecursorRules_metadata
    (flat : Array (FlatBlockMember m)) (peers : Array (KId m))
    (nParams : Nat) (isLarge : Bool) (fuel gi : Nat)
    (generated result : Array (GeneratedRecursor m))
    (methods : Methods m) (initial final : TcState m)
    (run :
      (populateOptionalGeneratedRecursorRules flat peers nParams isLarge gi
        fuel generated).run methods initial = .ok result final) :
    result.map GeneratedRecursor.metadata =
      generated.map GeneratedRecursor.metadata := by
  induction fuel generalizing gi generated initial final with
  | zero =>
      simp only [populateOptionalGeneratedRecursorRules,
        ReaderT.run_pure] at run
      cases run
      rfl
  | succ fuel ih =>
      rw [populateOptionalGeneratedRecursorRules] at run
      simp only [ReaderT.run_bind] at run
      change EStateM.bind
        ((buildOptionalGeneratedRecursorRules gi flat[gi]! flat peers
          generated[gi]!.ty nParams isLarge).run methods) _ initial =
            .ok result final at run
      unfold EStateM.bind at run
      cases rulesRun :
          (buildOptionalGeneratedRecursorRules gi flat[gi]! flat peers
            generated[gi]!.ty nParams isLarge).run methods initial with
      | error err afterRules =>
          rw [rulesRun] at run
          contradiction
      | ok rules afterRules =>
          rw [rulesRun] at run
          simp only at run
          let updated := if rules.all (·.isSome) then
              generated.modify gi (·.withRules (rules.filterMap id))
            else generated
          change
            (populateOptionalGeneratedRecursorRules flat peers nParams isLarge
              (gi + 1) fuel updated).run methods afterRules =
                .ok result final at run
          have updatedMetadata :
              updated.map GeneratedRecursor.metadata =
                generated.map GeneratedRecursor.metadata := by
            unfold updated
            split
            · exact GeneratedRecursor.map_metadata_modify_withRules
                generated gi (rules.filterMap id)
            · rfl
          exact (ih (gi := gi + 1) (generated := updated)
            (initial := afterRules) (final := final) run).trans updatedMetadata

/-- The canonical peer-backed rule-population pass also preserves the complete
metadata array. -/
theorem populateCompleteGeneratedRecursorRules_metadata
    (flat : Array (FlatBlockMember m)) (peers : Array (KId m))
    (nParams : Nat) (isLarge : Bool) (fuel gi : Nat)
    (generated result : Array (GeneratedRecursor m))
    (methods : Methods m) (initial final : TcState m)
    (run :
      (populateCompleteGeneratedRecursorRules flat peers nParams isLarge gi
        fuel generated).run methods initial = .ok result final) :
    result.map GeneratedRecursor.metadata =
      generated.map GeneratedRecursor.metadata := by
  induction fuel generalizing gi generated initial final with
  | zero =>
      simp only [populateCompleteGeneratedRecursorRules,
        ReaderT.run_pure] at run
      cases run
      rfl
  | succ fuel ih =>
      rw [populateCompleteGeneratedRecursorRules] at run
      simp only [ReaderT.run_bind] at run
      change EStateM.bind
        ((buildCompleteGeneratedRecursorRules gi flat[gi]! flat peers
          generated[gi]!.ty nParams isLarge).run methods) _ initial =
            .ok result final at run
      unfold EStateM.bind at run
      cases rulesRun :
          (buildCompleteGeneratedRecursorRules gi flat[gi]! flat peers
            generated[gi]!.ty nParams isLarge).run methods initial with
      | error err afterRules =>
          rw [rulesRun] at run
          contradiction
      | ok rules afterRules =>
          rw [rulesRun] at run
          simp only at run
          let updated := generated.modify gi (·.withRules rules)
          change
            (populateCompleteGeneratedRecursorRules flat peers nParams isLarge
              (gi + 1) fuel updated).run methods afterRules =
                .ok result final at run
          exact (ih (gi := gi + 1) (generated := updated)
            (initial := afterRules) (final := final) run).trans
              (GeneratedRecursor.map_metadata_modify_withRules generated gi
                rules)

/-- Complete public generated-artifact boundary. An absent ingress cache is an
exact no-op. Otherwise the core's returned rule batch is exposed, target-cache
interference is checked against the immutable ingress metadata, and the final
cache is reconstructed from ingress headers/types plus exactly those returned
rules. No callback-written type or rule can cross this boundary. -/
theorem populateRecursorRulesFromBlock_artifacts
    (indBlockId recBlockId : KId .anon)
    (methods : Methods .anon) (initial final : TcState .anon)
    (run :
      (populateRecursorRulesFromBlock indBlockId recBlockId).run methods
        initial = .ok () final) :
    match initial.env.recursorCache[indBlockId]? with
    | none => final = initial
    | some ingress =>
        ∃ generatedWithRules afterCore cached,
          (populateRecursorRulesFromBlockCore indBlockId recBlockId ingress).run
              methods initial = .ok generatedWithRules afterCore ∧
          afterCore.env.recursorCache[indBlockId]? = some cached ∧
          cached.size = ingress.size ∧
          cached.map GeneratedRecursor.metadata =
            ingress.map GeneratedRecursor.metadata ∧
          generatedWithRules.size = ingress.size ∧
          final.env.recursorCache[indBlockId]? =
            some (ingress.zipWith
              (fun header generated => header.withRules generated.rules)
              generatedWithRules) ∧
          (ingress.zipWith
              (fun header generated => header.withRules generated.rules)
              generatedWithRules).map GeneratedRecursor.metadata =
            ingress.map GeneratedRecursor.metadata ∧
          (ingress.zipWith
              (fun header generated => header.withRules generated.rules)
              generatedWithRules).map (fun recursor => recursor.ty) =
            ingress.map (fun recursor => recursor.ty) := by
  unfold populateRecursorRulesFromBlock at run
  rw [ReaderT.run_bind] at run
  change EStateM.bind (get : TcM .anon (TcState .anon)) _ initial =
    .ok () final at run
  unfold EStateM.bind at run
  rw [show (get : TcM .anon (TcState .anon)) initial =
    .ok initial initial from rfl] at run
  simp only at run
  cases cacheEq : initial.env.recursorCache[indBlockId]? with
  | none =>
      rw [cacheEq] at run
      simp only [pure, ReaderT.run] at run
      cases run
      rfl
  | some ingress =>
      rw [cacheEq] at run
      simp only [ReaderT.run_bind] at run
      change EStateM.bind
        ((populateRecursorRulesFromBlockCore indBlockId recBlockId ingress).run
          methods) _ initial = .ok () final at run
      unfold EStateM.bind at run
      cases coreRun :
          (populateRecursorRulesFromBlockCore indBlockId recBlockId ingress).run
            methods initial with
      | error err afterCore =>
          rw [coreRun] at run
          contradiction
      | ok generatedWithRules afterCore =>
          rw [coreRun] at run
          simp only at run
          obtain ⟨cached, afterCache, sameSize, cachedMetadata,
              generatedSize, finalCache, finalMetadata, finalTypes⟩ :=
            commitGeneratedRecursorRulesAt_artifacts indBlockId ingress
              generatedWithRules methods afterCore final run
          exact ⟨generatedWithRules, afterCore, cached, coreRun, afterCache,
            sameSize, cachedMetadata, generatedSize, finalCache, finalMetadata,
            finalTypes⟩

/-- Concise metadata consequence of the full transactional artifact boundary. -/
theorem populateRecursorRulesFromBlock_metadata
    (indBlockId recBlockId : KId .anon)
    (methods : Methods .anon) (initial final : TcState .anon)
    (run :
      (populateRecursorRulesFromBlock indBlockId recBlockId).run methods
        initial = .ok () final) :
    match initial.env.recursorCache[indBlockId]? with
    | none => final = initial
    | some ingress =>
        ∃ cachedFinal,
          final.env.recursorCache[indBlockId]? = some cachedFinal ∧
          cachedFinal.map GeneratedRecursor.metadata =
            ingress.map GeneratedRecursor.metadata := by
  have artifacts := populateRecursorRulesFromBlock_artifacts indBlockId
    recBlockId methods initial final run
  cases cacheEq : initial.env.recursorCache[indBlockId]? with
  | none =>
      simpa [cacheEq] using artifacts
  | some ingress =>
      rw [cacheEq] at artifacts
      simp only at artifacts ⊢
      obtain ⟨generatedWithRules, afterCore, cached, _, _, _, _, _, finalCache,
          finalMetadata, _⟩ := artifacts
      exact ⟨ingress.zipWith
        (fun header generated => header.withRules generated.rules)
        generatedWithRules, finalCache, finalMetadata⟩

private theorem buildGeneratedRecursorTypes_metadata_fromPrefix
    (indInfos :
      Array (KId m × UInt64 × UInt64 × Array (KId m) × KExpr m))
    (blockInds : Array (KId m)) (flat : Array (FlatBlockMember m))
    (motiveTypes : Array (KExpr m))
    (univOffset recLvls nParams nMinors : UInt64)
    (blockIsUnsafe : Bool) (fuel di : Nat)
    (generated result : Array (GeneratedRecursor m))
    (methods : Methods m) (initial final : TcState m)
    (span : di + fuel = flat.size)
    (hprefix : GeneratedRecursorMetadata.MatchesPrefix flat recLvls nParams
      nMinors blockIsUnsafe di generated)
    (run :
      (buildGeneratedRecursorTypes indInfos blockInds flat motiveTypes
        univOffset recLvls nParams nMinors blockIsUnsafe di fuel generated).run
          methods initial = .ok result final) :
    result.map GeneratedRecursor.metadata =
      GeneratedRecursorMetadata.expectedFlat flat recLvls nParams nMinors
        blockIsUnsafe := by
  induction fuel generalizing di generated initial final with
  | zero =>
      simp only [Nat.add_zero] at span
      subst di
      simp only [buildGeneratedRecursorTypes, ReaderT.run_pure] at run
      cases run
      simpa [GeneratedRecursorMetadata.MatchesPrefix,
        GeneratedRecursorMetadata.expectedFlat] using hprefix
  | succ fuel ih =>
      have currentInBounds : di < flat.size := by omega
      rw [buildGeneratedRecursorTypes] at run
      simp only [currentInBounds, ↓reduceDIte, ReaderT.run_bind] at run
      change EStateM.bind
        ((buildRecType di indInfos blockInds flat motiveTypes univOffset).run
          methods) _ initial = .ok result final at run
      unfold EStateM.bind at run
      cases typeRun :
          (buildRecType di indInfos blockInds flat motiveTypes univOffset).run
            methods initial with
      | error err afterType =>
          rw [typeRun] at run
          contradiction
      | ok recType afterType =>
          rw [typeRun] at run
          simp only at run
          have nextPrefix :
              GeneratedRecursorMetadata.MatchesPrefix flat recLvls nParams
                nMinors blockIsUnsafe (di + 1)
                (generated.push
                  (initialGeneratedRecursor flat[di] flat recLvls nParams
                    nMinors blockIsUnsafe recType)) := by
            unfold GeneratedRecursorMetadata.MatchesPrefix
            rw [Array.map_push, initialGeneratedRecursor_metadata, hprefix]
            rw [Array.extract_succ_right (by omega) currentInBounds,
              Array.map_push]
          apply ih (di := di + 1)
            (generated := generated.push
              (initialGeneratedRecursor flat[di] flat recLvls nParams nMinors
                blockIsUnsafe recType))
            (initial := afterType) (final := final)
          · omega
          · exact nextPrefix
          · exact run

/-- Every successful execution of the production type-construction loop,
started at the exact flat-block boundary, returns precisely the metadata array
derived from that flat block.  No semantic assumption about `buildRecType` is
needed. -/
theorem buildGeneratedRecursorTypes_metadata
    (indInfos :
      Array (KId m × UInt64 × UInt64 × Array (KId m) × KExpr m))
    (blockInds : Array (KId m)) (flat : Array (FlatBlockMember m))
    (motiveTypes : Array (KExpr m))
    (univOffset recLvls nParams nMinors : UInt64)
    (blockIsUnsafe : Bool) (methods : Methods m)
    (initial final : TcState m) (result : Array (GeneratedRecursor m))
    (run :
      (buildGeneratedRecursorTypes indInfos blockInds flat motiveTypes
        univOffset recLvls nParams nMinors blockIsUnsafe 0 flat.size
          (Array.mkEmpty flat.size)).run methods initial = .ok result final) :
    result.map GeneratedRecursor.metadata =
      GeneratedRecursorMetadata.expectedFlat flat recLvls nParams nMinors
        blockIsUnsafe := by
  apply buildGeneratedRecursorTypes_metadata_fromPrefix
    indInfos blockInds flat motiveTypes univOffset recLvls nParams nMinors
      blockIsUnsafe flat.size 0 (Array.mkEmpty flat.size) result methods
      initial final
  · simp
  · simp [GeneratedRecursorMetadata.MatchesPrefix]
  · exact run

/-- The production phase that builds and inserts a generated-recursors batch
stores exactly the metadata derived from its canonical flat block.  Optional
co-resident rule synthesis may succeed, partially fail, or be absent; none of
those branches can affect the cached header array. -/
theorem buildAndCacheGeneratedRecursors_metadata
    (blockId : KId .anon)
    (flatIndInfos :
      Array (KId .anon × UInt64 × UInt64 × Array (KId .anon) ×
        KExpr .anon))
    (flatIds : Array (KId .anon))
    (flat : Array (FlatBlockMember .anon))
    (motiveTypes : Array (KExpr .anon))
    (univOffset recLvls nParams nMinors : UInt64)
    (blockIsUnsafe isLarge : Bool) (methods : Methods .anon)
    (initial final : TcState .anon)
    (run :
      (buildAndCacheGeneratedRecursors blockId flatIndInfos flatIds flat
        motiveTypes univOffset recLvls nParams nMinors blockIsUnsafe
          isLarge).run methods initial = .ok () final) :
    ∃ generated,
      final.env.recursorCache[blockId]? = some generated ∧
      generated.map GeneratedRecursor.metadata =
        GeneratedRecursorMetadata.expectedFlat flat recLvls nParams nMinors
          blockIsUnsafe := by
  unfold buildAndCacheGeneratedRecursors at run
  rw [ReaderT.run_bind] at run
  change EStateM.bind
    ((buildGeneratedRecursorTypes flatIndInfos flatIds flat motiveTypes
      univOffset recLvls nParams nMinors blockIsUnsafe 0 flat.size
        (Array.mkEmpty flat.size)).run methods) _ initial = .ok () final at run
  unfold EStateM.bind at run
  cases typeRun :
      (buildGeneratedRecursorTypes flatIndInfos flatIds flat motiveTypes
        univOffset recLvls nParams nMinors blockIsUnsafe 0 flat.size
          (Array.mkEmpty flat.size)).run methods initial with
  | error err afterTypes =>
      rw [typeRun] at run
      contradiction
  | ok generatedTypes afterTypes =>
      have typeMetadata := buildGeneratedRecursorTypes_metadata flatIndInfos
        flatIds flat motiveTypes univOffset recLvls nParams nMinors
        blockIsUnsafe methods initial afterTypes generatedTypes typeRun
      rw [typeRun] at run
      simp only at run
      rw [ReaderT.run_bind] at run
      change EStateM.bind ((findPeerRecursors blockId flat).run methods) _
        afterTypes = .ok () final at run
      unfold EStateM.bind at run
      cases peerRun : (findPeerRecursors blockId flat).run methods afterTypes with
      | error err afterPeers =>
          rw [peerRun] at run
          contradiction
      | ok peerRecs afterPeers =>
          rw [peerRun] at run
          cases peerRecs with
          | none =>
              simp only [pure_bind] at run
              simp only [modify, ReaderT.run] at run
              cases run
              refine ⟨generatedTypes, ?_, typeMetadata⟩
              rw [Std.HashMap.getElem?_insert, beq_self_eq_true]
              rfl
          | some peers =>
              simp only [ReaderT.run_bind] at run
              change EStateM.bind
                ((populateOptionalGeneratedRecursorRules flat peers
                  nParams.toNat isLarge 0 generatedTypes.size
                    generatedTypes).run methods) _ afterPeers =
                      .ok () final at run
              unfold EStateM.bind at run
              cases rulesRun :
                  (populateOptionalGeneratedRecursorRules flat peers
                    nParams.toNat isLarge 0 generatedTypes.size
                      generatedTypes).run methods afterPeers with
              | error err afterRules =>
                  rw [rulesRun] at run
                  contradiction
              | ok generatedRules afterRules =>
                  have rulesMetadata :=
                    populateOptionalGeneratedRecursorRules_metadata flat peers
                      nParams.toNat isLarge generatedTypes.size 0
                      generatedTypes generatedRules methods afterPeers
                      afterRules rulesRun
                  rw [rulesRun] at run
                  simp only [modify, ReaderT.run] at run
                  cases run
                  refine ⟨generatedRules, ?_, rulesMetadata.trans typeMetadata⟩
                  rw [Std.HashMap.getElem?_insert, beq_self_eq_true]
                  rfl

end RecM

end Ix.Tc
