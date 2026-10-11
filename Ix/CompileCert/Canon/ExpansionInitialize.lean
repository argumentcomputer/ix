import Ix.CompileCert.Canon.ExpansionReferences
import Ix.CompileCert.Canon.SourceAliasScope

namespace Ix.CompileCert.Canon
open Ix.Compile.Canon
open Ix (Name Expr)

/-- Proof-side name for the exact original-member loop body of `expandSourceSpec`. -/
def initialMember (cx : XCtx) (name : Name) (view : IndView)
    (aliases : Std.HashMap Name Name) : XMember :=
  { name, sourceOwner := name, typ := canonicalizeConstNames aliases view.type,
    ctors := view.ctors.map fun (cn,ct,nf) =>
      { name := cn, typ := canonicalizeConstNames aliases ct, nFields := nf },
    nParams := cx.nParams, nIndices := view.numIndices }

/-- The real initializer, isolated only as a proof-side expression. The bridge
below unfolds `expandSourceSpec` to identify this exact loop and its successful output. -/
def initialMembers (cx : XCtx) (ordered : Array Name) (aliases : Std.HashMap Name Name) :
    Except String XSt :=
  forIn ordered ({} : XSt) fun name st => do
    let some view := cx.ind? name | .error s!"expand: {namePretty name} is not an inductive"
    return .yield (st.push (initialMember cx name view aliases))

/-- An actually resolved source member and its constructor reads stay in the
same block reference closure after canonical alias substitution. -/
theorem initialMember_scope {cx : XCtx} (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    {name : Name} (reached : RunReach cx name) {view : IndView}
    (found : cx.ind? name = some view) (aliases : Std.HashMap Name Name)
    (range : ∀ query value, aliases.get? query = some value → RunReach cx value)
    (st : XSt) : MemberScope (RunKnown cx st) (initialMember cx name view aliases) := by
  have actual : IndView.ofConst? cx.source.get? name = some view := by simpa [lookup] using found
  obtain ⟨v,record,-,typ,-,-⟩ := IndView.sourceInfo actual
  constructor
  · have referenceScope : RefScope (RunReach cx) view.type := by
      rw [typ]
      exact reached.type_scope record
    exact (referenceScope.canonicalizeConstNames aliases range).mono (fun _ h => Or.inl h)
  · intro ctor member
    obtain ⟨sourceCtor,inView,rfl⟩ := Array.mem_map.mp member
    obtain ⟨cn,ct,nf⟩ := sourceCtor
    have referenceScope := (reached.viewCtor actual inView).2.1
    exact (referenceScope.canonicalizeConstNames aliases range).mono (fun _ h => Or.inl h)

/-- The initializer's invariant is derived from actual source reads. Its
reachability/range arguments are discharged below for canonical expansion. -/
theorem initialize_scope {cx : XCtx} (lookup : cx.ind? = IndView.ofConst? cx.source.get?)
    (ordered : Array Name) (members : ∀ n ∈ ordered, RunReach cx n)
    (aliases : Std.HashMap Name Name)
    (range : ∀ query value, aliases.get? query = some value → RunReach cx value)
    {st : XSt} (run : initialMembers cx ordered aliases = .ok st) : ExpansionScope cx st := by
  unfold initialMembers at run
  apply forIn_except_array_mem _ (fun _ state => ExpansionScope cx state) ordered
    ?_ (ExpansionScope.empty cx) run
  intro pre name before step member scopeProof result
  split at result
  · rename_i view found
    cases except_pure_ok result
    refine ⟨_,rfl,scopeProof.push _ ?_⟩
    exact initialMember_scope lookup (members name (by simpa using member)) found aliases range _
  · cases result

/-- Every successful canonical `expandSourceSpec` has the exact scoped initializer and
actual queue run below. No source-closure/freshness premise is exposed to the
caller; reference support is the finite data already supplied by the compiler. -/
theorem expand_initialization (source : Ix.Environment) (dedup : Dedup)
    (classes : Array (Array Name)) (groupOf : SourceGroups)
    (keyAddr? : Option (Name → Option Address)) {x : Expanded}
    (run : expandSourceSpec source dedup (repsOf classes) (aliasesOf classes) groupOf keyAddr? = .ok x) :
    ∃ (first : Name) (fi : IndView),
      (repsOf classes)[0]? = some first ∧ IndView.ofConst? source.get? first = some fi ∧
      let cx : XCtx := {
        source, sourceMembers := repsOf classes, ind? := IndView.ofConst? source.get?,
        groupOf, keyAddr?, dedup, all0 := fi.all[0]?.getD first,
        blockLevels := fi.levelParams.map Ix.Level.mkParam,
        levelParams := fi.levelParams.toList, nParams := fi.numParams,
        paramBinders := (peelForalls fi.numParams fi.type #[]).1 }
      ∃ initial final,
        initialMembers cx (repsOf classes) (aliasesOf classes) = .ok initial ∧
        ExpansionScope cx initial ∧
        (∀ binder ∈ cx.paramBinders, BinderScope (RunReach cx) binder) ∧
        walkQueue cx expansionBound 0 initial = .ok final ∧
        x = {
          types := final.types, auxToNested := final.auxToNested,
          auxCtorMap := final.auxCtorMap, nOriginals := initial.types.size,
          levelParams := fi.levelParams, nParams := fi.numParams,
          all0 := cx.all0, sourceNames := final.sourceNames?.getD [] } := by
  unfold expandSourceSpec at run
  dsimp only at run
  split at run
  · rename_i first firstFound
    split at run
    · rename_i fi viewFound
      refine ⟨first,fi,firstFound,viewFound,?_⟩
      dsimp only
      obtain ⟨initial,initialRun,run⟩ := except_bind_ok.1 run
      obtain ⟨final,queueRun,done⟩ := except_bind_ok.1 run
      refine ⟨initial,final,?_,?_,?_,queueRun,(except_pure_ok done).symm⟩
      · exact initialRun
      · refine initialize_scope rfl (repsOf classes) ?_ (aliasesOf classes) ?_ ?_
        · intro name member
          exact SourceReach.seed (by simpa using member)
        · intro query value found
          exact SourceReach.alias_value source groupOf.blocks classes found
        · exact initialRun
      · apply SourceReach.parameterBinders (SourceReach.seed ?_) viewFound
        exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? firstFound)
    · cases run
  · cases run

end Ix.CompileCert.Canon
