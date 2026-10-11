import Ix.CompileCert.Canon.AllocationHistory
import Ix.CompileCert.Canon.ComponentDiscovery

/-!
UNCOMPILED prospective public contracts. This separate namespace permits a
strict additive check before the explicitly documented public-root migration.
The old public roots are not renamed or replaced by this preparation.
-/

namespace Ix.CompileCert.Canon.CallbackPublic

open Ix.Compile.Canon
open Ix (Name)
open ExpansionHistory

/-- Prospective public growth invariant. The previous index-only skeleton
invariant remains an internal proof tool, not the public naming contract. -/
def Grow (cx : ExpansionCore.Ctx) (owner : Name) (before after : XSt) : Prop :=
  ∃ events, History cx before events after ∧ ∀ event ∈ events, event.owner = owner

theorem Grow.refl (cx : ExpansionCore.Ctx) (owner : Name) (st : XSt) : Grow cx owner st st :=
  ⟨[],.refl st,by simp⟩

theorem Grow.keyError (cx : ExpansionCore.Ctx) (owner : Name) (st : XSt) (err : Option String) :
    Grow cx owner st {st with keyError := err} := ⟨[],.keyError st err,by simp⟩

theorem Grow.trans {cx : ExpansionCore.Ctx} {owner : Name} {a b c : XSt}
    (left : Grow cx owner a b) (right : Grow cx owner b c) : Grow cx owner a c := by
  obtain ⟨l,hl,ol⟩ := left
  obtain ⟨r,hr,oright⟩ := right
  refine ⟨l ++ r,.trans hl hr,?_⟩
  intro event member
  rcases List.mem_append.mp member with member | member
  · exact ol event member
  · exact oright event member

/-- The single-step naming proof consumes the actual allocating call. Its
cache and lookup facts are internal event facts derived by the run proofs. -/
theorem Grow.push {cx : ExpansionCore.Ctx} {owner : Name} {initial before : XSt}
    (prefixRun : Grow cx owner initial before) (event : Event cx)
    (preState : event.before = before) (eventOwner : event.owner = owner) :
    Grow cx owner initial event.after := by
  subst before
  apply prefixRun.trans
  refine ⟨[event],.allocation event,?_⟩
  intro other member
  have same : other = event := List.mem_singleton.mp member
  subst other
  exact eventOwner

/-- The event-based invariant preserves the old skeleton, counter and common
owner conclusions. Its naming input is the actual event pre-state and fixed
protection thunk, rather than an independently existential forbidden list. -/
theorem Grow.fields {cx : ExpansionCore.Ctx} {owner : Name} {before after : XSt}
    (growth : Grow cx owner before after) :
    ∃ events : List (Event cx), History cx before events after ∧
      skel after = skel before ++ events.map (fun event => (event.name,event.owner)) ∧
      after.nextAuxIdx = before.nextAuxIdx + events.length ∧
      ∀ (k : Nat) (event : Event cx), events[k]? = some event →
        event.owner = owner ∧ event.before.nextAuxIdx = before.nextAuxIdx + k ∧
        event.name = auxNameOf cx.all0 event.sourceName (before.nextAuxIdx + k)
          (event.before.allocatedNames ++ cx.protect ()) := by
  obtain ⟨events,history,owners⟩ := growth
  refine ⟨events,history,history.fields.1,history.fields.2,?_⟩
  intro k event found
  refine ⟨owners event (List.mem_of_getElem? found),history.index k event found,?_⟩
  unfold Event.name
  rw [history.index k event found]

/-- The original member/discovery/owner contract, strengthened by an ordered
history whose events contain actual pre-allocation state and exact class calls.
Protection is unrestricted input data; there is no completeness premise. -/
def DiscoverySpec (protect : Unit → List Lean.Name) (ind? : Name → Option IndView)
    (dedup : Dedup) (ordered : Array Name) (aliases : Std.HashMap Name Name)
    (groups : ExpansionCore.GroupCallback) (keyAddr? : Option (Name → Option _root_.Address))
    (x : Expanded) : Prop :=
  ∃ (first : Name) (fi : IndView), ordered[0]? = some first ∧ ind? first = some fi ∧
    x.nOriginals = ordered.size ∧ x.nOriginals ≤ x.types.size ∧
    (∀ (i : Nat) (n : Name), ordered[i]? = some n →
      ∃ m : XMember, x.types[i]? = some m ∧ m.name = n ∧ m.sourceOwner = n) ∧
    let cx := context protect ind? dedup groups keyAddr? first fi
    ∃ (initial final : XSt) (events : List (Event cx)),
      initialMembers cx ordered aliases = .ok initial ∧
      ExpansionCore.walkQueue cx expansionBound 0 initial = .ok final ∧
      History cx initial events final ∧
      x = {
        types := final.types, auxToNested := final.auxToNested,
        auxCtorMap := final.auxCtorMap, nOriginals := initial.types.size,
        levelParams := fi.levelParams, nParams := fi.numParams,
        all0 := cx.all0, sourceNames := final.sourceNames?.getD []} ∧
      events.length = x.aux.size ∧
      ∃ D : List Nat, D.length = x.aux.size ∧ D.Pairwise (· ≤ ·) ∧
        ∀ (k : Nat) (m : XMember), x.aux[k]? = some m →
          ∃ event, events[k]? = some event ∧ event.before.nextAuxIdx = k + 1 ∧
            event.owner = m.sourceOwner ∧
            m.name = auxNameOf (fi.all[0]?.getD first) event.sourceName (k+1)
              (event.before.allocatedNames ++ protect ()) ∧
            (∀ protectedName ∈ protect (), (keyName m.name).isPrefixOf protectedName = false) ∧
            (∀ previousName ∈ event.before.allocatedNames,
              (keyName m.name).isPrefixOf previousName = false) ∧
            ∃ (d : Nat) (md : XMember), D[k]? = some d ∧ d < x.nOriginals + k ∧
              x.types[d]? = some md ∧ m.sourceOwner = md.sourceOwner

/-- Every original arbitrary callback is still quantified, independently of
the group callback, addresses and protection data. No finite-Env witness is used. -/
theorem expand_spec {protect : Unit → List Lean.Name} {ind? : Name → Option IndView}
    {dedup : Dedup} {ordered : Array Name} {aliases : Std.HashMap Name Name}
    {groups : ExpansionCore.GroupCallback} {keyAddr? : Option (Name → Option _root_.Address)}
    {x : Expanded}
    (run : ExpansionCore.expand protect ind? dedup ordered aliases groups keyAddr? = .ok x) :
    DiscoverySpec protect ind? dedup ordered aliases groups keyAddr? x := by
  obtain ⟨first,fi,firstFound,viewFound,initial,final,events,
    initialRun,queueRun,history,output,eventCount,eventAt⟩ := expand_aux_events run
  obtain ⟨oldFirst,oldFi,oldFirstFound,oldViewFound,originalCount,bound,originalAt,
    D,discoveryCount,orderedDiscovery,discoveryAt⟩ := ExpansionCoreProof.expand_spec run
  have sameFirst : oldFirst = first := Option.some.inj (oldFirstFound.symm.trans firstFound)
  subst oldFirst
  have sameView : oldFi = fi := Option.some.inj (oldViewFound.symm.trans viewFound)
  subst oldFi
  refine ⟨first,fi,firstFound,viewFound,originalCount,bound,originalAt,
    initial,final,events,initialRun,queueRun,history,output,eventCount,
    D,discoveryCount,orderedDiscovery,?_⟩
  intro k member found
  obtain ⟨event,eventFound,name,owner,index⟩ := eventAt k member found
  obtain ⟨_,discoverer,discovered,atIndex,earlier,atQueue,sameOwner⟩ := discoveryAt k member found
  refine ⟨event,eventFound,index,owner,?_,?_,?_,discoverer,discovered,atIndex,earlier,atQueue,sameOwner⟩
  · rw [← name]
    unfold Event.name
    rw [index]
    rfl
  · intro protectedName protectedMember
    rw [← name]
    exact event.sourceFree protectedName protectedMember
  · intro previousName previousMember
    rw [← name]
    exact event.previousFree previousName previousMember

/-- Every discoverer index is in range, even when presented by its index-list
entry rather than by an auxiliary-member witness. This retains the original
component conclusion; the operational naming/history remains in DiscoverySpec. -/
theorem DiscoverySpec.discoverer_bounds
    {protect : Unit → List Lean.Name} {ind? : Name → Option IndView}
    {dedup : Dedup} {ordered : Array Name} {aliases : Std.HashMap Name Name}
    {groups : ExpansionCore.GroupCallback} {keyAddr? : Option (Name → Option _root_.Address)}
    {x : Expanded} (spec : DiscoverySpec protect ind? dedup ordered aliases groups keyAddr? x) :
    ∃ D : List Nat, D.length = x.aux.size ∧ D.Pairwise (· ≤ ·) ∧
      ∀ (k d : Nat), D[k]? = some d → d < x.nOriginals + k := by
  obtain ⟨first,fi,firstFound,viewFound,originalCount,bound,originalAt,
    initial,final,events,initialRun,queueRun,history,output,eventCount,
    D,discoveryCount,orderedDiscovery,atAux⟩ := spec
  refine ⟨D,discoveryCount,orderedDiscovery,?_⟩
  intro k d found
  have inRange : k < x.aux.size := by
    rw [← discoveryCount]
    rcases Nat.lt_or_ge k D.length with inside | outside
    · exact inside
    · rw [List.getElem?_eq_none outside] at found
      cases found
  obtain ⟨member,memberFound⟩ : ∃ member, x.aux[k]? = some member :=
    ⟨x.aux[k],Array.getElem?_eq_getElem inRange⟩
  obtain ⟨event,eventFound,index,owner,name,sourceFree,previousFree,
    discoverer,discovered,atIndex,earlier,atQueue,sameOwner⟩ := atAux k member memberFound
  rw [found] at atIndex
  cases atIndex
  exact earlier

theorem expand_owner {protect : Unit → List Lean.Name} {ind? : Name → Option IndView}
    {dedup : Dedup} {ordered : Array Name} {aliases : Std.HashMap Name Name}
    {groups : ExpansionCore.GroupCallback} {keyAddr? : Option (Name → Option _root_.Address)}
    {x : Expanded}
    (run : ExpansionCore.expand protect ind? dedup ordered aliases groups keyAddr? = .ok x) :
    ∀ (i : Nat) (member : XMember), x.types[i]? = some member → member.sourceOwner ∈ ordered :=
  ExpansionCoreProof.expand_owner run

/-- The actual source wrapper obtains the protection thunk from its own source
closure. No protection data, completeness proof or cache property is supplied by
this theorem's caller. The generic contract above remains independently public. -/
theorem expand_source_spec {source : Ix.Environment} {dedup : Dedup} {ordered : Array Name}
    {aliases : Std.HashMap Name Name} {groups : SourceGroups}
    {keyAddr? : Option (Name → Option _root_.Address)} {x : Expanded}
    (run : Ix.Compile.Canon.expandSourceSpec source dedup ordered aliases groups keyAddr? = .ok x) :
    DiscoverySpec (fun () => (sourceContext source ordered groups.blocks).protectedNames)
      (IndView.ofConst? source.get?) dedup ordered aliases groups.apply keyAddr? x := by
  apply expand_spec
  rw [← CoreBridge.expand_eq_core]
  exact run

/-- Component characterization retains arbitrary raw constant callbacks and
both independent protection presentations through the actual generic facade. -/
theorem componentNested_some {rules : Rules} (discovery : rules.nested = .discovery)
    {protect : ComponentCore.Protection} {env : ComponentCore.Env}
    {all : Array Name} {classes : Array (Array Name)} {nested : NestedCanon}
    (run : ComponentCore.componentNested protect rules env all classes = .ok (some nested)) :
    ∃ x, ComponentCore.canonExpand protect rules env classes = .ok x ∧
      nested.canonClasses = x.aux.map (fun m => #[m.name]) ∧
      sigsInOrder x nested.canonClasses = .ok nested.canon ∧
      nested.addrDecided = false ∧
      (∃ source, ExpansionCore.expand (protect.source all) env.ind? rules.dedup all
        (groupOf := leanSourceGroup.apply) = .ok source ∧ nested.source = source.sigs ∧
        computePerm env.addr? nested.canon nested.source all (origToCanonOf classes) = .ok nested.perm) ∧
      nested.evaporated = Array.replicate nested.perm.size false :=
  ComponentCoreProof.componentNested_some discovery run

theorem componentNested_discovery {rules : Rules} (discovery : rules.nested = .discovery)
    {protect : ComponentCore.Protection} {env : ComponentCore.Env}
    {all : Array Name} {classes : Array (Array Name)} {nested : NestedCanon}
    (run : ComponentCore.componentNested protect rules env all classes = .ok (some nested)) :
    ∃ x, ComponentCore.canonExpand protect rules env classes = .ok x ∧
      nested.canonClasses = x.aux.map (fun m => #[m.name]) ∧
      sigsInOrder x nested.canonClasses = .ok nested.canon ∧
      DiscoverySpec (protect.canonical (repsOf classes)) env.ind? rules.dedup
        (repsOf classes) (aliasesOf classes) env.groupOf (some env.addr?) x ∧
      (∀ (i : Nat) (member : XMember), x.types[i]? = some member →
        member.sourceOwner ∈ repsOf classes) ∧
      (∃ D : List Nat, D.length = x.aux.size ∧ D.Pairwise (· ≤ ·) ∧
        ∀ (k d : Nat), D[k]? = some d → d < x.nOriginals + k) := by
  obtain ⟨x,expanded,classesEq,signatures,_,_,_⟩ := componentNested_some discovery run
  have generic := expanded
  unfold ComponentCore.canonExpand at generic
  rw [discovery] at generic
  have spec := expand_spec generic
  exact ⟨x,expanded,classesEq,signatures,spec,expand_owner generic,spec.discoverer_bounds⟩

/-- Actual production supplies the canonical protected set from its own
source/reference closure. No support list or completeness/freshness proof is
an argument. The callback-generic theorem above remains unrestricted. -/
theorem componentNested_source_spec {rules : Rules} (discovery : rules.nested = .discovery)
    {env : Ix.Compile.Canon.SourceEnv} {all : Array Name} {classes : Array (Array Name)}
    {nested : NestedCanon}
    (run : Ix.Compile.Canon.SourceBlock.componentNested rules env all classes = .ok (some nested)) :
    ∃ x, Ix.Compile.Canon.SourceBlock.canonExpand rules env classes = .ok x ∧
      nested.canonClasses = x.aux.map (fun m => #[m.name]) ∧
      sigsInOrder x nested.canonClasses = .ok nested.canon ∧
      DiscoverySpec
        (fun () => (sourceContext env.source (repsOf classes) env.groupOf.blocks).protectedNames)
        env.ind? rules.dedup (repsOf classes) (aliasesOf classes) env.groupOf.apply
        (some env.addr?) x ∧
      (∀ (i : Nat) (member : XMember), x.types[i]? = some member →
        member.sourceOwner ∈ repsOf classes) ∧
      (∃ D : List Nat, D.length = x.aux.size ∧ D.Pairwise (· ≤ ·) ∧
        ∀ (k d : Nat), D[k]? = some d → d < x.nOriginals + k) := by
  rw [SourceComponentCoreProof.componentNested_eq_core] at run
  obtain ⟨x,expanded,classesEq,signatures,spec,owners,bounds⟩ :=
    componentNested_discovery discovery run
  refine ⟨x,?_,classesEq,signatures,spec,owners,bounds⟩
  rw [SourceComponentCoreProof.canonExpand_eq_core]
  exact expanded

end Ix.CompileCert.Canon.CallbackPublic
