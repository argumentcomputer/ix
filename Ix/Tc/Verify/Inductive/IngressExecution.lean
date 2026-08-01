import Ix.Tc.Ingress
import Ix.Tc.Verify.Inductive.SingletonIngress

/-!
# Anonymous inductive-block ingress execution

This module exposes the successful execution shape of production anonymous
block ingress.  Conversion remains an arbitrary effectful computation; the
only fact extracted from `ingressAnonBlockWithTrace` is its exact final
publication step.  Consequently the proof does not reimplement the ingress
stack machine or assume that conversion succeeded.

The flat entry array is inserted with last-write-wins hash-map semantics.
`EntryKeysUnique` is therefore an explicit premise of the theorem which turns
entry-array membership into a post-state lookup.  Concrete fixtures must
discharge it for their actual projection addresses; no Blake3 injectivity is
smuggled into the model.
-/

namespace Ix.Tc

/-! ## Flat insertion semantics -/

/-- No two converted entries use the same anonymous id. -/
def EntryKeysUnique (entries : Array Entry) : Prop :=
  (entries.toList.map (·.1)).Nodup

/-- Folding insertions at keys other than `id` preserves its lookup. -/
private theorem foldl_insert_get?_of_key_not_mem
    (entries : List Entry) (env : AnonEnv) (id : KId .anon)
    (hnot : id ∉ entries.map (·.1)) :
    (entries.foldl (fun env (entryId, concrete) =>
      env.insert entryId concrete) env).get? id = env.get? id := by
  induction entries generalizing env with
  | nil => rfl
  | cons first rest ih =>
      rcases first with ⟨firstId, firstConcrete⟩
      simp only [List.map_cons, List.mem_cons, not_or] at hnot
      rw [List.foldl_cons, ih _ hnot.2]
      simp only [KEnv.get?, KEnv.insert, Std.HashMap.getElem?_insert]
      split
      · next heq =>
        exact False.elim (hnot.1 (eq_of_beq heq).symm)
      · rfl

/-- Under key uniqueness, every pair in a left-to-right insertion fold is
the exact lookup retained by the final constant map. -/
private theorem foldl_insert_get?_of_mem
    (entries : List Entry) (env : AnonEnv)
    (hunique : (entries.map (·.1)).Nodup)
    {id : KId .anon} {concrete : KConst .anon}
    (hmem : (id, concrete) ∈ entries) :
    (entries.foldl (fun env (entryId, value) =>
      env.insert entryId value) env).get? id = some concrete := by
  induction entries generalizing env with
  | nil => simp at hmem
  | cons first rest ih =>
      rcases first with ⟨firstId, firstConcrete⟩
      have hunique' := List.nodup_cons.mp hunique
      rcases List.mem_cons.mp hmem with hfirst | hrest
      · cases hfirst
        rw [List.foldl_cons,
          foldl_insert_get?_of_key_not_mem rest _ id hunique'.1]
        simp [KEnv.get?, KEnv.insert]
      · rw [List.foldl_cons]
        exact ih _ hunique'.2 hrest

/-- Every uniquely keyed entry is loaded by the pure production insertion
transition.  Block-map insertion is irrelevant because it leaves the
constant map unchanged. -/
theorem insertMutsEntriesState_loaded
    {before : AnonEnv} {entries : Array Entry}
    (hunique : EntryKeysUnique entries)
    {id : KId .anon} {concrete : KConst .anon}
    (hmem : (id, concrete) ∈ entries) :
    (insertMutsEntriesState before entries).get? id = some concrete := by
  unfold insertMutsEntriesState insertEntriesState
  exact foldl_insert_get?_of_mem entries.toList _ hunique
    (by simpa using hmem)

/-! ## Successful publication traces -/

/-- A successful publication call consists of a successful reserved-address
guard followed by the exact pure insertion transition. -/
inductive InsertMutsEntriesSuccessTrace
    (entries : Array Entry) (before after : AnonEnv) : Prop
  | run (guarded : AnonEnv) :
      guardReserved entries before = .ok () guarded →
      after = insertMutsEntriesState guarded entries →
      InsertMutsEntriesSuccessTrace entries before after

namespace InsertMutsEntriesSuccessTrace

/-- Invert the production effectful wrapper without assuming guard success. -/
theorem of_run
    {entries : Array Entry} {before after : AnonEnv}
    (hrun : insertMutsEntries entries before = .ok () after) :
    InsertMutsEntriesSuccessTrace entries before after := by
  unfold insertMutsEntries at hrun
  change EStateM.bind (guardReserved entries) _ before = .ok () after at hrun
  unfold EStateM.bind at hrun
  cases hguard : guardReserved entries before with
  | error err failed =>
      rw [hguard] at hrun
      contradiction
  | ok value guarded =>
      rw [hguard] at hrun
      simp only at hrun
      have hresult := EStateM.Result.ok.inj hrun
      exact .run guarded hguard hresult.2.symm

/-- Uniquely keyed published entries are exact post-state lookups. -/
theorem loaded
    {entries : Array Entry} {before after : AnonEnv}
    (trace : InsertMutsEntriesSuccessTrace entries before after)
    (hunique : EntryKeysUnique entries)
    {id : KId .anon} {concrete : KConst .anon}
    (hmem : (id, concrete) ∈ entries) :
    after.get? id = some concrete := by
  cases trace with
  | run guarded hguard hafter =>
      rw [hafter]
      exact insertMutsEntriesState_loaded hunique hmem

end InsertMutsEntriesSuccessTrace

/-- Exact successful decomposition of the traced block ingress wrapper.
`prepareAnonBlock` owns all conversion and deterministic address generation;
`publication` is the sole insertion that follows it. -/
inductive AnonBlockIngressSuccessTrace
    (ixonEnv : Ixon.Env) (blockConstant : Ixon.Constant)
    (blockAddr : Address) (before after : AnonEnv)
    (result : AnonBlockIngressTrace) : Prop
  | run (converted : AnonEnv) :
      prepareAnonBlock ixonEnv blockConstant blockAddr before =
        .ok result converted →
      InsertMutsEntriesSuccessTrace result.allEntries converted after →
      AnonBlockIngressSuccessTrace ixonEnv blockConstant blockAddr before
        after result

namespace AnonBlockIngressSuccessTrace

/-- Invert one actual successful production block-ingress execution. -/
theorem of_run
    {ixonEnv : Ixon.Env} {blockConstant : Ixon.Constant}
    {blockAddr : Address} {before after : AnonEnv}
    {result : AnonBlockIngressTrace}
    (hrun : ingressAnonBlockWithTrace ixonEnv blockConstant blockAddr before =
      .ok result after) :
    AnonBlockIngressSuccessTrace ixonEnv blockConstant blockAddr before after
      result := by
  unfold ingressAnonBlockWithTrace at hrun
  change EStateM.bind
    (prepareAnonBlock ixonEnv blockConstant blockAddr) _ before =
      .ok result after at hrun
  unfold EStateM.bind at hrun
  cases hprepare : prepareAnonBlock ixonEnv blockConstant blockAddr before with
  | error err failed =>
      rw [hprepare] at hrun
      contradiction
  | ok prepared converted =>
      rw [hprepare] at hrun
      simp only at hrun
      change EStateM.bind (insertMutsEntries prepared.allEntries) _ converted =
        .ok result after at hrun
      unfold EStateM.bind at hrun
      cases hinsert : insertMutsEntries prepared.allEntries converted with
      | error err failed =>
          rw [hinsert] at hrun
          contradiction
      | ok value inserted =>
          rw [hinsert] at hrun
          have hresult := EStateM.Result.ok.inj hrun
          rcases hresult with ⟨rfl, rfl⟩
          cases value
          exact .run converted hprepare
            (InsertMutsEntriesSuccessTrace.of_run hinsert)

/-- Every uniquely keyed entry returned by successful traced ingress is
loaded in its actual production post-state. -/
theorem loaded
    {ixonEnv : Ixon.Env} {blockConstant : Ixon.Constant}
    {blockAddr : Address} {before after : AnonEnv}
    {result : AnonBlockIngressTrace}
    (trace : AnonBlockIngressSuccessTrace ixonEnv blockConstant blockAddr
      before after result)
    (hunique : EntryKeysUnique result.allEntries)
    {id : KId .anon} {concrete : KConst .anon}
    (hmem : (id, concrete) ∈ result.allEntries) :
    after.get? id = some concrete := by
  cases trace with
  | run converted hprepare publication =>
      exact publication.loaded hunique hmem

end AnonBlockIngressSuccessTrace

/-! ## Singleton source interpretations -/

open Lean4Lean (VEnv VInductDecl)

/-- Ghost interpretation of one production family-block conversion result.

Anonymous ingress cannot recover Lean names from its input, so name and raw
Theory-expression relations are intentionally explicit.  Everything about
concrete loading is instead phrased as membership in the actual converted
entry array.  `entryIds` also pins the exact flat physical block order used by
production registration. -/
structure SingletonFamilyIngressInterpretation
    (trProj : RawProjRel) (nameOf : Address → Option Lean.Name)
    (result : AnonBlockIngressTrace)
    {source : VInductDecl} {before theoryAfter : VEnv}
    (tx : CertifiedGenerationTransaction source before theoryAfter) where
  familyId : KId .anon
  constructorIds : Array (KId .anon)
  memberKids : result.memberKids = #[familyId]
  entryIds : result.allEntries.map (·.1) = #[familyId] ++ constructorIds
  entriesUnique : EntryKeysUnique result.allEntries
  constructorCount :
    constructorIds.size =
      tx.certificate.generation.block.sourceType.ctors.length
  familyConcrete : KConst .anon
  familyEntry : (familyId, familyConcrete) ∈ result.allEntries
  familyShape : familyConcrete.IsCertifiedSingletonFamily source
    tx.certificate.generation constructorIds
  familyName : nameOf familyId.addr =
    some tx.certificate.generation.block.sourceType.name
  familyType : RawExprRel theoryAfter nameOf trProj [] familyConcrete.ty
    tx.certificate.generation.block.sourceType.type
  constructor : ∀ (index : Nat) (hindex : index < constructorIds.size),
    ∃ sourceConstructor concrete,
      tx.certificate.generation.block.sourceType.ctors[index]? =
        some sourceConstructor ∧
      (constructorIds[index], concrete) ∈ result.allEntries ∧
      concrete.IsCertifiedSingletonConstructor source familyId index
        sourceConstructor ∧
      nameOf constructorIds[index].addr = some sourceConstructor.name ∧
      RawExprRel theoryAfter nameOf trProj [] concrete.ty sourceConstructor.type

namespace SingletonFamilyIngressInterpretation

/-- Actual successful ingress turns entry-array interpretation into the
loaded-state family view consumed by the catalog adapter. -/
def toIngressView
    {trProj : RawProjRel} {nameOf : Address → Option Lean.Name}
    {result : AnonBlockIngressTrace}
    {source : VInductDecl} {before theoryAfter : VEnv}
    {tx : CertifiedGenerationTransaction source before theoryAfter}
    (interpretation : SingletonFamilyIngressInterpretation trProj nameOf
      result tx)
    {ixonEnv : Ixon.Env} {blockConstant : Ixon.Constant}
    {blockAddr : Address} {ingressBefore ingressAfter : AnonEnv}
    (execution : AnonBlockIngressSuccessTrace ixonEnv blockConstant blockAddr
      ingressBefore ingressAfter result) :
    SingletonFamilyIngressView trProj ingressAfter nameOf tx where
  familyId := interpretation.familyId
  constructorIds := interpretation.constructorIds
  constructorCount := interpretation.constructorCount
  familyConcrete := interpretation.familyConcrete
  familyLoaded := execution.loaded interpretation.entriesUnique
    interpretation.familyEntry
  familyShape := interpretation.familyShape
  familyName := interpretation.familyName
  familyType := interpretation.familyType
  constructor := by
    intro index hindex
    obtain ⟨sourceConstructor, concrete, hsource, hentry, hshape,
      hname, htype⟩ := interpretation.constructor index hindex
    exact ⟨sourceConstructor, concrete, hsource,
      execution.loaded interpretation.entriesUnique hentry,
      hshape, hname, htype⟩

@[simp] theorem toIngressView_members
    {trProj : RawProjRel} {nameOf : Address → Option Lean.Name}
    {result : AnonBlockIngressTrace}
    {source : VInductDecl} {before theoryAfter : VEnv}
    {tx : CertifiedGenerationTransaction source before theoryAfter}
    (interpretation : SingletonFamilyIngressInterpretation trProj nameOf
      result tx)
    {ixonEnv : Ixon.Env} {blockConstant : Ixon.Constant}
    {blockAddr : Address} {ingressBefore ingressAfter : AnonEnv}
    (execution : AnonBlockIngressSuccessTrace ixonEnv blockConstant blockAddr
      ingressBefore ingressAfter result) :
    (interpretation.toIngressView execution).members =
      result.allEntries.map (·.1) := by
  exact interpretation.entryIds.symm

/-- Complete production-ingress-to-catalog bridge for the family block.
Catalog agreement remains an invariant of the actual ingress post-state;
semantic freshness is derived by `toCatalogLink` from the trusted log. -/
def toCatalogLink
    {trProj : RawProjRel} {world : VerifyWorld}
    {result : AnonBlockIngressTrace}
    {source : VInductDecl} {theoryAfter : VEnv}
    {tx : CertifiedGenerationTransaction source world.venv theoryAfter}
    (interpretation : SingletonFamilyIngressInterpretation trProj
      world.nameOf result tx)
    {ixonEnv : Ixon.Env} {blockConstant : Ixon.Constant}
    {blockAddr : Address} {ingressBefore ingressAfter : AnonEnv}
    (execution : AnonBlockIngressSuccessTrace ixonEnv blockConstant blockAddr
      ingressBefore ingressAfter result)
    (loaded : LoadedAgrees world.catalog ingressAfter)
    (trustedCatalog : TrustedCatalogRel trProj world) :
    SingletonFamilyCatalogLink trProj world.catalog world.nameOf world.trusted
      tx :=
  (interpretation.toIngressView execution).toCatalogLink loaded trustedCatalog

/-- A narrower catalog bridge for callers which retain exact catalog facts
for the converted entry array but do not need a global `LoadedAgrees`
invariant for the intermediate ingress state.  The successful execution index
still prevents a fabricated conversion result from being linked. -/
def toCatalogLinkOfEntries
    {trProj : RawProjRel} {world : VerifyWorld}
    {result : AnonBlockIngressTrace}
    {source : VInductDecl} {theoryAfter : VEnv}
    {tx : CertifiedGenerationTransaction source world.venv theoryAfter}
    (interpretation : SingletonFamilyIngressInterpretation trProj
      world.nameOf result tx)
    {ixonEnv : Ixon.Env} {blockConstant : Ixon.Constant}
    {blockAddr : Address} {ingressBefore ingressAfter : AnonEnv}
    (_execution : AnonBlockIngressSuccessTrace ixonEnv blockConstant blockAddr
      ingressBefore ingressAfter result)
    (catalogEntry : ∀ {id concrete},
      (id, concrete) ∈ result.allEntries →
        world.catalog id = some concrete)
    (trustedCatalog : TrustedCatalogRel trProj world) :
    SingletonFamilyCatalogLink trProj world.catalog world.nameOf world.trusted
      tx where
  familyId := interpretation.familyId
  constructorIds := interpretation.constructorIds
  constructorCount := interpretation.constructorCount
  familyConcrete := interpretation.familyConcrete
  familyCatalog := catalogEntry interpretation.familyEntry
  familyShape := interpretation.familyShape
  familyName := interpretation.familyName
  familyType := interpretation.familyType
  constructor := by
    intro index hindex
    obtain ⟨sourceConstructor, concrete, hsource, hentry, hshape,
      hname, htype⟩ := interpretation.constructor index hindex
    exact ⟨sourceConstructor, concrete, hsource, catalogEntry hentry,
      hshape, hname, htype⟩
  fresh := by
    intro id hmember
    simp only [Array.mem_append, Array.mem_singleton] at hmember
    rcases hmember with rfl | hconstructor
    · exact (interpretation.toIngressView _execution).familyFresh
        trustedCatalog
    · obtain ⟨index, hindex, hid⟩ :=
        Array.mem_iff_getElem.mp hconstructor
      subst id
      exact (interpretation.toIngressView _execution).constructorFresh
        trustedCatalog index hindex

@[simp] theorem toCatalogLink_members
    {trProj : RawProjRel} {world : VerifyWorld}
    {result : AnonBlockIngressTrace}
    {source : VInductDecl} {theoryAfter : VEnv}
    {tx : CertifiedGenerationTransaction source world.venv theoryAfter}
    (interpretation : SingletonFamilyIngressInterpretation trProj
      world.nameOf result tx)
    {ixonEnv : Ixon.Env} {blockConstant : Ixon.Constant}
    {blockAddr : Address} {ingressBefore ingressAfter : AnonEnv}
    (execution : AnonBlockIngressSuccessTrace ixonEnv blockConstant blockAddr
      ingressBefore ingressAfter result)
    (loaded : LoadedAgrees world.catalog ingressAfter)
    (trustedCatalog : TrustedCatalogRel trProj world) :
    (interpretation.toCatalogLink execution loaded trustedCatalog).members =
      result.allEntries.map (·.1) := by
  exact interpretation.entryIds.symm

end SingletonFamilyIngressInterpretation

/-- Ghost interpretation of one production recursor-block conversion result.
The preceding family link fixes the constructor and generated-rule order. -/
structure SingletonRecursorIngressInterpretation
    (trProj : RawProjRel) (nameOf : Address → Option Lean.Name)
    (result : AnonBlockIngressTrace)
    {source : VInductDecl} {before theoryAfter : VEnv}
    (tx : CertifiedGenerationTransaction source before theoryAfter)
    {trusted : KId .anon → Prop} {catalog : Catalog}
    (family : SingletonFamilyCatalogLink trProj catalog nameOf trusted tx) where
  recursorId : KId .anon
  memberKids : result.memberKids = #[recursorId]
  entryIds : result.allEntries.map (·.1) = #[recursorId]
  entriesUnique : EntryKeysUnique result.allEntries
  recursorConcrete : KConst .anon
  recursorEntry : (recursorId, recursorConcrete) ∈ result.allEntries
  recursorShape : recursorConcrete.IsCertifiedSingletonRecursor source
    tx.certificate.generation family.constructorIds
  recursorName : nameOf recursorId.addr =
    some (.str tx.certificate.generation.block.sourceType.name "rec")
  recursorType : RawExprRel theoryAfter nameOf trProj [] recursorConcrete.ty
    tx.certificate.generation.recursor.type
  rule : ∀ (index : Nat) (_hindex : index < family.constructorIds.size),
    ∃ concreteRule normalizedConstructor,
      recursorConcrete.RecursorRuleAt index concreteRule ∧
      tx.certificate.generation.block.ctorPairs[index]? =
        some normalizedConstructor ∧
      concreteRule.fields.toNat =
        (normalizedConstructor.fieldsR source.uvars source.nparams).length ∧
      RawExprRel theoryAfter nameOf trProj [] concreteRule.rhs
        (tx.certificate.generation.rule index normalizedConstructor).rhs ∧
      TrKExprS theoryAfter
        (tx.certificate.generation.rule index normalizedConstructor).uvars
        nameOf trProj [] concreteRule.rhs
        (tx.certificate.generation.rule index normalizedConstructor).rhs

namespace SingletonRecursorIngressInterpretation

/-- Successful recursor ingress supplies the exact concrete lookup missing
from the source interpretation. -/
def toIngressView
    {trProj : RawProjRel} {nameOf : Address → Option Lean.Name}
    {result : AnonBlockIngressTrace}
    {source : VInductDecl} {before theoryAfter : VEnv}
    {tx : CertifiedGenerationTransaction source before theoryAfter}
    {trusted : KId .anon → Prop} {catalog : Catalog}
    {family : SingletonFamilyCatalogLink trProj catalog nameOf trusted tx}
    (interpretation : SingletonRecursorIngressInterpretation trProj nameOf
      result tx family)
    {ixonEnv : Ixon.Env} {blockConstant : Ixon.Constant}
    {blockAddr : Address} {ingressBefore ingressAfter : AnonEnv}
    (execution : AnonBlockIngressSuccessTrace ixonEnv blockConstant blockAddr
      ingressBefore ingressAfter result) :
    SingletonRecursorIngressView trProj ingressAfter nameOf tx family where
  recursorId := interpretation.recursorId
  recursorConcrete := interpretation.recursorConcrete
  recursorLoaded := execution.loaded interpretation.entriesUnique
    interpretation.recursorEntry
  recursorShape := interpretation.recursorShape
  recursorName := interpretation.recursorName
  recursorType := interpretation.recursorType
  rule := interpretation.rule

@[simp] theorem toIngressView_members
    {trProj : RawProjRel} {nameOf : Address → Option Lean.Name}
    {result : AnonBlockIngressTrace}
    {source : VInductDecl} {before theoryAfter : VEnv}
    {tx : CertifiedGenerationTransaction source before theoryAfter}
    {trusted : KId .anon → Prop} {catalog : Catalog}
    {family : SingletonFamilyCatalogLink trProj catalog nameOf trusted tx}
    (interpretation : SingletonRecursorIngressInterpretation trProj nameOf
      result tx family)
    {ixonEnv : Ixon.Env} {blockConstant : Ixon.Constant}
    {blockAddr : Address} {ingressBefore ingressAfter : AnonEnv}
    (execution : AnonBlockIngressSuccessTrace ixonEnv blockConstant blockAddr
      ingressBefore ingressAfter result) :
    (interpretation.toIngressView execution).members =
      result.allEntries.map (·.1) := by
  exact interpretation.entryIds.symm

/-- Complete production-ingress-to-catalog bridge for the recursor block. -/
def toCatalogLink
    {trProj : RawProjRel} {world : VerifyWorld}
    {result : AnonBlockIngressTrace}
    {source : VInductDecl} {theoryAfter : VEnv}
    {tx : CertifiedGenerationTransaction source world.venv theoryAfter}
    {family : SingletonFamilyCatalogLink trProj world.catalog world.nameOf
      world.trusted tx}
    (interpretation : SingletonRecursorIngressInterpretation trProj
      world.nameOf result tx family)
    {ixonEnv : Ixon.Env} {blockConstant : Ixon.Constant}
    {blockAddr : Address} {ingressBefore ingressAfter : AnonEnv}
    (execution : AnonBlockIngressSuccessTrace ixonEnv blockConstant blockAddr
      ingressBefore ingressAfter result)
    (loaded : LoadedAgrees world.catalog ingressAfter)
    (trustedCatalog : TrustedCatalogRel trProj world) :
    SingletonRecursorCatalogLink trProj world.catalog world.nameOf
      world.trusted tx family :=
  (interpretation.toIngressView execution).toCatalogLink loaded trustedCatalog

/-- Exact-entry counterpart of `toCatalogLink`.  This is useful when the
recursor was loaded after its family and the final immutable catalog is known
at the returned recursor entry, without requiring a global agreement theorem
for every unrelated constant in the final state. -/
def toCatalogLinkOfEntry
    {trProj : RawProjRel} {world : VerifyWorld}
    {result : AnonBlockIngressTrace}
    {source : VInductDecl} {theoryAfter : VEnv}
    {tx : CertifiedGenerationTransaction source world.venv theoryAfter}
    {family : SingletonFamilyCatalogLink trProj world.catalog world.nameOf
      world.trusted tx}
    (interpretation : SingletonRecursorIngressInterpretation trProj
      world.nameOf result tx family)
    {ixonEnv : Ixon.Env} {blockConstant : Ixon.Constant}
    {blockAddr : Address} {ingressBefore ingressAfter : AnonEnv}
    (_execution : AnonBlockIngressSuccessTrace ixonEnv blockConstant blockAddr
      ingressBefore ingressAfter result)
    (catalogEntry : world.catalog interpretation.recursorId =
      some interpretation.recursorConcrete)
    (trustedCatalog : TrustedCatalogRel trProj world) :
    SingletonRecursorCatalogLink trProj world.catalog world.nameOf
      world.trusted tx family where
  recursorId := interpretation.recursorId
  recursorConcrete := interpretation.recursorConcrete
  recursorCatalog := catalogEntry
  recursorShape := interpretation.recursorShape
  recursorName := interpretation.recursorName
  recursorType := interpretation.recursorType
  rule := interpretation.rule
  fresh := (interpretation.toIngressView _execution).recursorFresh
    trustedCatalog

end SingletonRecursorIngressInterpretation

end Ix.Tc
