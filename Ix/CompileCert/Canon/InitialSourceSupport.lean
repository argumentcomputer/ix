import Ix.CompileCert.Canon.ReaderInitialization
import Ix.CompileCert.Canon.SourceReadBridge

/-!
Proof-only derivation of the actual initializer's source protection.

The reference list below is computed from the real initial members, after
alias replacement. It retains member/owner/constructor query names and every
constant or projection reference, in order and with repetitions. Its paired
graph is supported by the two real sourceContext lists; a separate forbidden
set is neither supplied nor existentially chosen.

This is a source-backed specialization of the unrestricted callback core.
The raw-read relation and structural functionality/injectivity still require
their original-presentation bridge. No claim that arbitrary callbacks are
finite, that MRen alone supplies raw reader observations, or that this graph
is already a NameCorrespondence is made. Existing public domains are unchanged.

Uncompiled and unaudited source checkpoint.
-/

namespace Ix.CompileCert.Canon.InitialSourceSupport

open Ix.Compile.Canon
open Ix (Name Expr)
open PairedInitializer ReaderInitialization

/-- Names used by the initial queue, including the actual constructor query
spellings. This is a proof-side list, not a replacement for sourceContext. -/
def memberReferences (member : XMember) : List Name :=
  ([member.name, member.sourceOwner] ++ sourceExprRefs member.typ) ++
    member.ctors.toList.flatMap (fun ctor => ctor.name :: sourceExprRefs ctor.typ)

def initialReferences (state : XSt) : List Name :=
  state.types.toList.flatMap memberReferences

/-- The complete ordered reference list follows the existing member relation.
No query is replaced by a stored declaration name. -/
theorem MembersRelated.references {σ : Name → Name} {S : Name → Prop}
    {left right : XMember} (members : PairedInitializer.MembersRelated σ S left right) :
    memberReferences right = (memberReferences left).map σ := by
  have constructors :
      right.ctors.toList.flatMap (fun ctor => ctor.name :: sourceExprRefs ctor.typ) =
        (left.ctors.toList.flatMap (fun ctor => ctor.name :: sourceExprRefs ctor.typ)).map σ := by
    have related := members.ctors
    induction related with
    | nil => rfl
    | cons head tail ih =>
      simp only [List.flatMap_cons, head.name, head.type.sourceExprRefs,
        List.map_append, List.map_cons, ih]
  simp only [memberReferences, members.name, members.owner, members.type.sourceExprRefs,
    constructors, List.map_append, List.map_cons, List.map_nil]

/-- The actual full initial states, not a later history alignment, determine
the two reference lists. Repeated references and insertion order are retained. -/
theorem StatesRelated.references {σ : Name → Name} {S : Name → Prop}
    {left right : XSt} (states : PairedInitializer.StatesRelated σ S left right) :
    initialReferences right = (initialReferences left).map σ := by
  have members := states.types
  unfold initialReferences
  induction members with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.flatMap_cons, MembersRelated.references head, List.map_append, ih]

/-- Each constituent is an actual reached source query, rather than a name
merely accepted by a hash set. The expression property uses declaration edges
only; metadata/binder/universe names remain protected by sourceContext itself. -/
structure MemberReached (P : Name → Prop) (member : XMember) : Prop where
  name : P member.name
  owner : P member.sourceOwner
  type : RefScope P member.typ
  constructorNames : ∀ ctor ∈ member.ctors, P ctor.name
  constructorTypes : ∀ ctor ∈ member.ctors, RefScope P ctor.typ

theorem MemberReached.references {P : Name → Prop} {member : XMember}
    (reached : MemberReached P member) : ∀ name ∈ memberReferences member, P name := by
  intro name included
  unfold memberReferences at included
  rcases List.mem_append.mp included with ownOrType | ctorReference
  · rcases List.mem_append.mp ownOrType with own | type
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at own
      rcases own with rfl | rfl
      · exact reached.name
      · exact reached.owner
    · exact reached.type name type
  · obtain ⟨ctor, inConstructors, reference⟩ := List.mem_flatMap.mp ctorReference
    have inArray : ctor ∈ member.ctors := by simpa using inConstructors
    rcases List.mem_cons.mp reference with rfl | reference
    · exact reached.constructorNames ctor inArray
    · exact reached.constructorTypes ctor inArray name reference

/-- The real member reader and the real alias builder establish reachability
of the whole initialized payload. No source completeness, constructor-prefix,
query/stored-name equality, or alias-range assumption is required. -/
theorem memberOf_reached (source : Ix.Environment)
    (groups : Std.HashMap Name (Array (Array Name))) (classes : Array (Array Name))
    (count : Nat) {name : Name} (seed : name ∈ repsOf classes) {view : IndView}
    (found : IndView.ofConst? source.get? name = some view) :
    MemberReached (SourceReach source groups (repsOf classes).toList)
      (memberOf count (aliasesOf classes) name view) := by
  have reached : SourceReach source groups (repsOf classes).toList name :=
    .seed (by simpa using seed)
  obtain ⟨value, record, _, type, _, _⟩ := IndView.sourceInfo found
  have range : ∀ query output, (aliasesOf classes).get? query = some output →
      SourceReach source groups (repsOf classes).toList output :=
    fun _ _ read => SourceReach.alias_value source groups classes read
  refine ⟨reached, reached, ?_, ?_, ?_⟩
  · change RefScope (SourceReach source groups (repsOf classes).toList)
      (canonicalizeConstNames (aliasesOf classes) view.type)
    apply RefScope.canonicalizeConstNames _ _ range
    rw [type]
    exact reached.type_scope record
  · intro ctor included
    obtain ⟨original, inView, equal⟩ := Array.mem_map.mp included
    subst ctor
    exact (reached.viewCtor found inView).1
  · intro ctor included
    obtain ⟨original, inView, equal⟩ := Array.mem_map.mp included
    subst ctor
    exact (reached.viewCtor found inView).2.1.canonicalizeConstNames _ range

/-- Source data enters through the actual wrapper's thunk and declaration
reader. Every other core field stays the supplied field; this definition does
not add a finite-support restriction to the generic context type. -/
def sourceCtx (source : Ix.Environment) (classes : Array (Array Name))
    (groups : GroupOf) (cx : ExpansionCore.Ctx) : ExpansionCore.Ctx :=
  { cx with
    protect := fun () => (sourceContext source (repsOf classes) groups.blocks).protectedNames
    ind? := IndView.ofConst? source.get?
    groupOf := groups }

/-- Exact producer specialization, including its fixed lazy protection thunk.
This equality is not a renaming or source-ingestion correctness theorem. -/
theorem sourceCtx_ofSource (cx : XCtx) (classes : Array (Array Name)) :
    sourceCtx cx.source classes cx.groupOf (ExpansionCore.Ctx.ofSource cx) =
      ExpansionCore.Ctx.ofSource
        { cx with sourceMembers := repsOf classes, ind? := IndView.ofConst? cx.source.get? } := rfl

/-- Every actual successful initial state consists only of the reached member
payloads above. A missing/wrong-kind source still returns the same error; this
lemma is later combined with the whole-Except paired initializer relation. -/
theorem initialMembers_reached (source : Ix.Environment) (classes : Array (Array Name))
    (groups : GroupOf) (cx : ExpansionCore.Ctx) {state : XSt}
    (run : ExpansionHistory.initialMembers (sourceCtx source classes groups cx)
      (repsOf classes) (aliasesOf classes) = .ok state) :
    ∀ member ∈ state.types,
      MemberReached (SourceReach source groups.blocks (repsOf classes).toList) member := by
  unfold ExpansionHistory.initialMembers at run
  apply forIn_except_array_mem _ (fun _ state => ∀ member ∈ state.types,
    MemberReached (SourceReach source groups.blocks (repsOf classes).toList) member)
      (repsOf classes) ?_ ?_ run
  · intro pre name before step included known result
    split at result
    · rename_i view found
      cases except_pure_ok result
      refine ⟨_, rfl, ?_⟩
      intro member inPush
      change member ∈ before.types.push (memberOf cx.nParams (aliasesOf classes) name view) at inPush
      rcases Array.mem_push.mp inPush with old | rfl
      · exact known member old
      · exact memberOf_reached source groups.blocks classes cx.nParams
          (by simpa using included) found
    · cases result
  · intro member included
    simp at included

/-- Initial reference support is derived from the completed real read loop and
the complete source collector. The protected list remains exactly that of the
actual source wrapper, including any additional metadata/level/binder fields. -/
theorem initialReferences_protected (source : Ix.Environment) (classes : Array (Array Name))
    (groups : GroupOf) (cx : ExpansionCore.Ctx) {state : XSt}
    (run : ExpansionHistory.initialMembers (sourceCtx source classes groups cx)
      (repsOf classes) (aliasesOf classes) = .ok state) :
    ∀ name ∈ initialReferences state,
      keyName name ∈ (sourceCtx source classes groups cx).protect () := by
  intro name included
  obtain ⟨member, inState, reference⟩ := List.mem_flatMap.mp included
  have reached := initialMembers_reached source classes groups cx run member
    (by simpa using inState)
  exact (sourceContext_reachable_done source (repsOf classes) groups.blocks
    (reached.references name reference)).1

/-- This finite graph is computed from the actual initial queue. Functionality
and injectivity are deliberately not built into this definition: deriving
those properties from the original source presentation remains necessary. -/
def InitialGraph (σ : Name → Name) (state : XSt) (left right : Lean.Name) : Prop :=
  ∃ name ∈ initialReferences state, left = keyName name ∧ right = keyName (σ name)

/-- Support of every pair follows from the actual reference-list transport and
both actual source runs. It is not an assumed event alignment or support set. -/
theorem initialGraph_protected {σ : Name → Name} {S : Name → Prop}
    (leftSource rightSource : Ix.Environment)
    (leftClasses rightClasses : Array (Array Name)) (leftGroups rightGroups : GroupOf)
    (leftCtx rightCtx : ExpansionCore.Ctx) {left right : XSt}
    (states : PairedInitializer.StatesRelated σ S left right)
    (leftRun : ExpansionHistory.initialMembers (sourceCtx leftSource leftClasses leftGroups leftCtx)
      (repsOf leftClasses) (aliasesOf leftClasses) = .ok left)
    (rightRun : ExpansionHistory.initialMembers (sourceCtx rightSource rightClasses rightGroups rightCtx)
      (repsOf rightClasses) (aliasesOf rightClasses) = .ok right) :
    ∀ a b, InitialGraph σ left a b →
      a ∈ (sourceCtx leftSource leftClasses leftGroups leftCtx).protect () ∧
      b ∈ (sourceCtx rightSource rightClasses rightGroups rightCtx).protect () := by
  intro a b related
  obtain ⟨name, included, rfl, rfl⟩ := related
  refine ⟨initialReferences_protected leftSource leftClasses leftGroups leftCtx leftRun name included, ?_⟩
  apply initialReferences_protected rightSource rightClasses rightGroups rightCtx rightRun (σ name)
  rw [StatesRelated.references states]
  exact List.mem_map_of_mem included

private theorem repsOf_mapped (σ : Name → Name) (classes : Array (Array Name)) :
    repsOf (classes.map (fun cls => cls.map σ)) = (repsOf classes).map σ := by
  simp only [repsOf, Array.filterMap_map, Array.map_filterMap, Function.comp_def,
    Array.getElem?_map]

/-- Whole actual initializer transport with the source protection invariant
derived, not assumed. The raw-reader and old Boolean-renaming hypotheses are
the internal inputs from ReaderInitialization; this theorem adds no final
caller premise. Missing queries retain their original paired error messages.

The resulting supported graph is not asserted to be functional/injective, and
actual sorter representative correspondence is not silently replaced by the
mapped-class presentation used at this induction boundary. -/
theorem initialMembers_supported {σ : Name → Name} {S : Name → Prop}
    (leftSource rightSource : Ix.Environment)
    (reads : ReadsRelated σ S leftSource.get? rightSource.get?)
    (hinj : ∀ x y, S x → S y → (σ x == σ y) = (x == y))
    (classes : Array (Array Name)) (classSupport : ∀ cls ∈ classes, ∀ name ∈ cls, S name)
    (leftGroups rightGroups : GroupOf) (leftCtx rightCtx : ExpansionCore.Ctx)
    (params : rightCtx.nParams = leftCtx.nParams) :
    let rightClasses := classes.map (fun cls => cls.map σ)
    let left := sourceCtx leftSource classes leftGroups leftCtx
    let right := sourceCtx rightSource rightClasses rightGroups rightCtx
    ResultRelated σ S (fun a b => PairedInitializer.StatesRelated σ S a b ∧
      ∀ x y, InitialGraph σ a x y → x ∈ left.protect () ∧ y ∈ right.protect ())
      (ExpansionHistory.initialMembers left (repsOf classes) (aliasesOf classes))
      (ExpansionHistory.initialMembers right (repsOf rightClasses) (aliasesOf rightClasses)) := by
  dsimp only
  have seeds : ∀ name ∈ repsOf classes, S name := by
    intro name included
    obtain ⟨cls, inClasses, first⟩ := Array.mem_filterMap.mp included
    exact classSupport cls inClasses name (Array.mem_of_getElem? first)
  have related := initialMembers_related hinj classes classSupport
    (sourceCtx leftSource classes leftGroups leftCtx)
    (sourceCtx rightSource (classes.map (fun cls => cls.map σ)) rightGroups rightCtx)
    params (repsOf classes) seeds
    (fun name included => ofConst_members_related reads (seeds name included))
  rw [← repsOf_mapped σ classes] at related
  generalize leftRun : ExpansionHistory.initialMembers
    (sourceCtx leftSource classes leftGroups leftCtx) (repsOf classes) (aliasesOf classes) = a at related ⊢
  generalize rightRun : ExpansionHistory.initialMembers
    (sourceCtx rightSource (classes.map (fun cls => cls.map σ)) rightGroups rightCtx)
    (repsOf (classes.map (fun cls => cls.map σ)))
    (aliasesOf (classes.map (fun cls => cls.map σ))) = b at related ⊢
  cases related with
  | missing name supported => exact .missing name supported
  | ok states =>
    exact .ok ⟨states, initialGraph_protected leftSource rightSource classes
      (classes.map (fun cls => cls.map σ)) leftGroups rightGroups leftCtx rightCtx
      states leftRun rightRun⟩

end Ix.CompileCert.Canon.InitialSourceSupport
