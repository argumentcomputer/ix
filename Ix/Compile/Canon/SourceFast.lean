module
public import Ix.Compile.Canon.Source
import all Ix.Compile.Canon.Source
import all Ix.Environment
import all IxC.Address.Core
public import Std.Data.HashSet.Lemmas
public section

namespace Ix.Compile.Canon
open Ix (Name ConstantInfo)

private theorem address_beq_iff_fast {a b : Address} : (a == b) = true ↔ a = b := by
  obtain ⟨⟨x⟩⟩ := a
  obtain ⟨⟨y⟩⟩ := b
  show (ByteArray.beq ⟨x⟩ ⟨y⟩) = true ↔ _
  simp [ByteArray.beq]

private instance : LawfulBEq Address where
  rfl := address_beq_iff_fast.2 rfl
  eq_of_beq := address_beq_iff_fast.1

/-- The source resolver's existing identity is the complete cached Address.
This is lookup congruence, not injectivity of source names or generated names. -/
theorem sourceLookup_key_eq (source : Ix.Environment) {a b : Name}
    (h : a.getHash = b.getHash) : source.get? a = source.get? b := by
  have same {α : Type} (m : Std.HashMap Name α) : m.get? a = m.get? b := by
    apply Std.HashMap.getElem?_congr
    change (a.getHash == b.getHash) = true
    rw [h]
    exact BEq.rfl
  unfold Ix.Environment.get?
  rw [same source.overlay, same source.consts]
  cases source.overlay.get? b with
  | some value => rfl
  | none =>
    cases source.consts.get? b with
    | some value => rfl
    | none =>
      cases source.fallback? with
      | none => rfl
      | some f => simp only [Ix.LazyConstants.get?, same f.index]

/-- Fetch memo for exactly the source map's existing lookup identity. A row
remembers the queried name so the invariant needs no digest-injectivity law. -/
structure SourceFetchCache (source : Ix.Environment) where
  rows : Std.HashMap Address (Name × Option ConstantInfo) := {}
  valid : ∀ address query value, rows[address]? = some (query,value) →
    query.getHash = address ∧ source.get? query = value

instance (source : Ix.Environment) : EmptyCollection (SourceFetchCache source) :=
  ⟨{ rows := {}, valid := by simp }⟩

structure SourceFetchResult (source : Ix.Environment) (query : Name) where
  value : Option ConstantInfo
  cache : SourceFetchCache source
  exactValue : value = source.get? query

/-- Fetching a missing query is memoized too. The caller still protects the
actual query spelling before this operation on every occurrence. -/
def SourceFetchCache.read (cache : SourceFetchCache source) (query : Name) :
    SourceFetchResult source query :=
  match hit : cache.rows[query.getHash]? with
  | some (old,value) =>
    { value, cache, exactValue := by
        have h := cache.valid query.getHash old value hit
        exact h.2.symm.trans (sourceLookup_key_eq source h.1) }
  | none =>
    let value := source.get? query
    { value
      cache := {
        rows := cache.rows.insert query.getHash (query,value)
        valid := by
          intro address old result found
          by_cases eq : query.getHash = address
          · subst address
            simp only [Std.HashMap.getElem?_insert_self, Option.some.injEq, Prod.mk.injEq] at found
            rcases found with ⟨rfl,rfl⟩
            exact ⟨rfl,rfl⟩
          · apply cache.valid address old result
            simpa [Std.HashMap.getElem?_insert, eq] using found }
      exactValue := rfl }

/-- A fast membership index, with the original visited list retained exactly. -/
structure SourceVisited (keys : List Address) where
  set : Std.HashSet Address := {}
  valid : ∀ address, address ∈ set ↔ address ∈ keys

def SourceVisited.empty : SourceVisited [] :=
  { set := {}, valid := by simp }

def SourceVisited.insert (index : SourceVisited keys) (address : Address) :
    SourceVisited (address :: keys) :=
  { set := index.set.insert address
    valid := by
      intro key
      rw [Std.HashSet.mem_insert, index.valid, List.mem_cons]
      constructor
      · rintro (same | member)
        · exact Or.inl (address_beq_iff_fast.mp same).symm
        · exact Or.inr member
      · rintro (same | member)
        · exact Or.inl (address_beq_iff_fast.mpr same.symm)
        · exact Or.inr member }

def SourceVisited.ofList : (keys : List Address) → SourceVisited keys
  | [] => .empty
  | key :: keys => (ofList keys).insert key

/-- Same work-list traversal as `collectSource`, with exact fetch and visited
caches. No list is deduplicated, reordered, bounded or omitted. -/
def collectSourceFast (source : Ix.Environment) (refs : ConstantInfo → List Name)
    (names : ConstantInfo → List Lean.Name) (pending : List Name) (out : SourceContext)
    (groups : Std.HashMap Name (Array (Array Name)))
    (fetch : SourceFetchCache source) (visited : SourceVisited out.visitedKeys) : SourceContext :=
  match pending with
  | [] => out
  | n :: rest =>
    let out' := { out with protectedNames := keyName n :: out.protectedNames }
    let read := fetch.read n
    match got : read.value with
    | none => collectSourceFast source refs names rest out' groups read.cache visited
    | some ci =>
      let out' := { out' with declarations := out'.declarations.insert n ci }
      if _known : n.getHash ∈ visited.set then
        collectSourceFast source refs names rest out' groups read.cache visited
      else
        let groupRefs := match ci with
          | .inductInfo _ => ((groups.get? n).getD #[]).toList.flatMap (·.toList)
          | _ => []
        collectSourceFast source refs names (refs ci ++ groupRefs ++ rest)
          { out' with protectedNames := names ci ++ out'.protectedNames
                      visitedKeys := n.getHash :: out.visitedKeys }
          groups read.cache (visited.insert n.getHash)
termination_by
  (((sourceSupport source).filter (fun n => !out.visitedKeys.contains n)).length,
    pending.length)
decreasing_by
  all_goals simp_wf
  all_goals first
    | exact Prod.Lex.right _ (Nat.lt_succ_self _)
    | apply Prod.Lex.left
      have sourceGet : source.get? n = some ci := read.exactValue.symm.trans got
      have fresh : n.getHash ∉ out.visitedKeys := fun member =>
        _known ((visited.valid _).2 member)
      simpa using filter_unseen_decreases (sourceSupport source) out.visitedKeys n.getHash
        (sourceGet_mem sourceGet) fresh

set_option maxRecDepth 10000 in
/-- Exact result equality includes declarations, every protected-name entry,
its order and multiplicity, and the complete visited-key list. -/
theorem collectSourceFast_eq (source : Ix.Environment) (refs : ConstantInfo → List Name)
    (names : ConstantInfo → List Lean.Name) (pending : List Name) (out : SourceContext)
    (groups : Std.HashMap Name (Array (Array Name)))
    (fetch : SourceFetchCache source) (visited : SourceVisited out.visitedKeys) :
    collectSourceFast source refs names pending out groups fetch visited =
      collectSource source refs names pending out groups := by
  fun_induction collectSourceFast source refs names pending out groups fetch visited
  case case1 => rw [collectSource.eq_def]
  case case2 out fetch visited n rest out1 read got ih =>
    have sourceGet := read.exactValue.symm.trans got
    rw [collectSource.eq_def]
    dsimp only
    split
    next missing => exact ih
    next value found => rw [sourceGet] at found; cases found
  case case3 out fetch visited n rest out1 read ci got out2 known ih =>
    have sourceGet := read.exactValue.symm.trans got
    have isKnown := (visited.valid _).1 known
    rw [collectSource.eq_def]
    dsimp only
    split
    next missing => rw [sourceGet] at missing; cases missing
    next value found =>
      have same : value = ci := Option.some.inj (found.symm.trans sourceGet)
      subst value
      simp only [isKnown, ↓reduceDIte]
      exact ih
  case case4 out fetch visited n rest out1 read ci got out2 fresh groupRefs ih =>
    have sourceGet := read.exactValue.symm.trans got
    have isNew : n.getHash ∉ out.visitedKeys := fun h => fresh ((visited.valid _).2 h)
    rw [collectSource.eq_def]
    dsimp only
    split
    next missing => rw [sourceGet] at missing; cases missing
    next value found =>
      have same : value = ci := Option.some.inj (found.symm.trans sourceGet)
      subst value
      simp only [isNew, ↓reduceDIte]
      cases ci <;> exact ih

/-- Runtime entry for the fast traversal. The ordinary call starts with an
empty list; arbitrary intermediate callers get an index of their actual list. -/
def collectSourceCached (source : Ix.Environment) (refs : ConstantInfo → List Name)
    (names : ConstantInfo → List Lean.Name) (pending : List Name) (out : SourceContext := {})
    (groups : Std.HashMap Name (Array (Array Name)) := {}) : SourceContext :=
  collectSourceFast source refs names pending out groups {} (SourceVisited.ofList out.visitedKeys)

@[csimp] theorem collectSource_eq_cached : @collectSource = @collectSourceCached := by
  funext source refs names pending out groups
  exact (collectSourceFast_eq source refs names pending out groups {} _).symm

/-- Public runtime entry also rewrites at consumers, including when the
original Source module was compiled before this refinement was imported. -/
def sourceContextCached (source : Ix.Environment) (members : Array Name)
    (groups : Std.HashMap Name (Array (Array Name)) := {}) : SourceContext :=
  collectSourceCached source sourceConstRefs sourceConstNames members.toList {} groups

@[csimp] theorem sourceContext_eq_cached : @sourceContext = @sourceContextCached := by
  funext source members groups
  exact (collectSourceFast_eq source sourceConstRefs sourceConstNames members.toList {} groups {} _).symm

end Ix.Compile.Canon
