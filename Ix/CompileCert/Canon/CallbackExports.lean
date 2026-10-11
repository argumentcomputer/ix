import Ix.CompileCert.Canon.CallbackPublic
import Ix.CompileCert.Canon.ComponentProtection
import Ix.CompileCert.Canon.CallbackPresentations

/-!
Public callback-domain contracts and actual-source specializations. These are
real declarations at the audited names, not name-resolution-only `export`
aliases. The index-only and source-specific proof bodies remain under explicit
companion names. Discovery uses the actual event pre-state and fixed protection
thunk; no support-completeness, freshness, hash or final-alignment assumption is
added. The audited public entries are the actual production functions; finite source
companions have explicit SourceEnv/SourceGroups types.
-/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon
open Ix (Name)
open ExpansionHistory

/-! The original Grow predicate is preserved literally as a skeleton fact.
Its three-argument auxNameOf uses the default empty protection list, which
reduces to the original literal name. ProtectedGrow below is the distinct
actual-history contract; no implication to literal Grow is claimed on collisions.
-/

/-- `st'` extends `st`'s queue by auxiliaries owned by `owner`, numbered from `st.nextAuxIdx`. -/
def Grow (all0 owner : Name) (st st' : XSt) : Prop :=
  ∃ L : List (Name × Name), skel st' = skel st ++ L ∧ st'.nextAuxIdx = st.nextAuxIdx + L.length ∧
    ∀ i p, L[i]? = some p → p.2 = owner ∧ ∃ J, p.1 = auxNameOf all0 J (st.nextAuxIdx + i)

theorem Grow.refl {all0 owner : Name} (st : XSt) : Grow all0 owner st st :=
  ⟨[], by simp, by simp, fun i p h => by simp at h⟩

theorem Grow.trans {all0 owner : Name} {st₁ st₂ st₃ : XSt} (h₁ : Grow all0 owner st₁ st₂)
    (h₂ : Grow all0 owner st₂ st₃) : Grow all0 owner st₁ st₃ := by
  obtain ⟨L₁, hs₁, hn₁, hp₁⟩ := h₁
  obtain ⟨L₂, hs₂, hn₂, hp₂⟩ := h₂
  refine ⟨L₁ ++ L₂, by rw [hs₂, hs₁, List.append_assoc], by rw [hn₂, hn₁, List.length_append]; omega,
    fun i p hp => ?_⟩
  by_cases hi : i < L₁.length
  · rw [List.getElem?_append_left hi] at hp
    exact hp₁ i p hp
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hi)] at hp
    obtain ⟨ho, J, hJ⟩ := hp₂ _ p hp
    refine ⟨ho, J, ?_⟩
    rw [hJ, hn₁]
    have : st₁.nextAuxIdx + L₁.length + (i - L₁.length) = st₁.nextAuxIdx + i := by omega
    rw [this]

/-- One auxiliary appended on top of a growth. -/
theorem Grow.push {all0 owner : Name} {st₀ r T : XSt} {m : XMember} (hr : Grow all0 owner st₀ r)
    (hT : T.types = r.types) (hN : T.nextAuxIdx = r.nextAuxIdx + 1) (ho : m.sourceOwner = owner)
    (hn : ∃ J, m.name = auxNameOf all0 J r.nextAuxIdx) : Grow all0 owner st₀ (T.push m) := by
  refine hr.trans ⟨[(m.name, m.sourceOwner)], ?_, ?_, fun i p hp => ?_⟩
  · unfold skel XSt.push
    rw [Array.toList_push, List.map_append, hT]; rfl
  · show T.nextAuxIdx = _; rw [hN]; rfl
  · cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
      subst hp
      obtain ⟨J, hJ⟩ := hn
      exact ⟨ho, J, by rw [Nat.add_zero]; exact hJ⟩
    | succ i => simp at hp

/-- Recording a key failure leaves the original skeleton-only predicate unchanged. -/
theorem Grow.keyError {all0 owner : Name} (st : XSt) (err : Option String) :
    Grow all0 owner st { st with keyError := err } :=
  ⟨[], by simp [skel], by simp, fun i p h => by simp at h⟩

abbrev ProtectedGrow (cx : ExpansionCore.Ctx) (owner : Name) (before after : XSt) : Prop :=
  CallbackPublic.Grow cx owner before after

abbrev DiscoverySpec (protect : Unit → List Lean.Name) (ind? : Name → Option IndView)
    (dedup : Dedup) (ordered : Array Name) (aliases : Std.HashMap Name Name)
    (groups : ExpansionCore.GroupCallback) (keyAddr? : Option (Name → Option _root_.Address))
    (x : Expanded) : Prop :=
  CallbackPublic.DiscoverySpec protect ind? dedup ordered aliases groups keyAddr? x

theorem ProtectedGrow.refl (cx : ExpansionCore.Ctx) (owner : Name) (st : XSt) : ProtectedGrow cx owner st st :=
  CallbackPublic.Grow.refl cx owner st

theorem ProtectedGrow.keyError (cx : ExpansionCore.Ctx) (owner : Name) (st : XSt) (err : Option String) :
    ProtectedGrow cx owner st {st with keyError := err} :=
  CallbackPublic.Grow.keyError cx owner st err

theorem ProtectedGrow.trans {cx : ExpansionCore.Ctx} {owner : Name} {a b c : XSt}
    (left : ProtectedGrow cx owner a b) (right : ProtectedGrow cx owner b c) : ProtectedGrow cx owner a c :=
  CallbackPublic.Grow.trans left right

theorem ProtectedGrow.push {cx : ExpansionCore.Ctx} {owner : Name} {initial before : XSt}
    (prefixRun : ProtectedGrow cx owner initial before) (event : Event cx)
    (preState : event.before = before) (eventOwner : event.owner = owner) :
    ProtectedGrow cx owner initial event.after :=
  CallbackPublic.Grow.push prefixRun event preState eventOwner

theorem ProtectedGrow.fields {cx : ExpansionCore.Ctx} {owner : Name} {before after : XSt}
    (growth : ProtectedGrow cx owner before after) :
    ∃ events : List (Event cx), History cx before events after ∧
      skel after = skel before ++ events.map (fun event => (event.name,event.owner)) ∧
      after.nextAuxIdx = before.nextAuxIdx + events.length ∧
      ∀ (k : Nat) (event : Event cx), events[k]? = some event →
        event.owner = owner ∧ event.before.nextAuxIdx = before.nextAuxIdx + k ∧
        event.name = auxNameOf cx.all0 event.sourceName (before.nextAuxIdx + k)
          (event.before.allocatedNames ++ cx.protect ()) :=
  CallbackPublic.Grow.fields growth

/-- The operational growth contract retains the queue-skeleton, counter and
owner conclusions with fresh-family naming. The existential index view is derived
internally; it is not substituted for the public fixed-protection contract. -/
theorem ProtectedGrow.index {cx : ExpansionCore.Ctx} {owner : Name} {before after : XSt}
    (growth : ProtectedGrow cx owner before after) : IndexGrow cx.all0 owner before after := by
  obtain ⟨events,_,skeleton,counter,atEvent⟩ := CallbackPublic.Grow.fields growth
  refine ⟨events.map (fun event => (event.name,event.owner)),skeleton,?_,?_⟩
  · simpa only [List.length_map] using counter
  · intro i pair found
    rw [List.getElem?_map] at found
    cases foundEvent : events[i]? with
    | none => rw [foundEvent] at found; cases found
    | some event =>
      rw [foundEvent] at found
      cases found
      obtain ⟨ownerEq,_,nameEq⟩ := atEvent i event foundEvent
      exact ⟨ownerEq,event.sourceName,event.before.allocatedNames ++ cx.protect (),nameEq⟩

theorem expand_spec {protect : Unit → List Lean.Name} {ind? : Name → Option IndView}
    {dedup : Dedup} {ordered : Array Name} {aliases : Std.HashMap Name Name}
    {groups : GroupOf} {keyAddr? : Option (Name → Option _root_.Address)}
    {x : Expanded}
    (run : Ix.Compile.Canon.expand ind? dedup ordered aliases groups keyAddr? protect = .ok x) :
    DiscoverySpec protect ind? dedup ordered aliases groups keyAddr? x :=
  CallbackPublic.expand_spec run

theorem expand_owner {protect : Unit → List Lean.Name} {ind? : Name → Option IndView}
    {dedup : Dedup} {ordered : Array Name} {aliases : Std.HashMap Name Name}
    {groups : GroupOf} {keyAddr? : Option (Name → Option _root_.Address)}
    {x : Expanded}
    (run : Ix.Compile.Canon.expand ind? dedup ordered aliases groups keyAddr? protect = .ok x) :
    ∀ (i : Nat) (member : XMember), x.types[i]? = some member → member.sourceOwner ∈ ordered :=
  CallbackPublic.expand_owner run

theorem expand_source_spec {source : Ix.Environment} {dedup : Dedup} {ordered : Array Name}
    {aliases : Std.HashMap Name Name} {groups : SourceGroups}
    {keyAddr? : Option (Name → Option _root_.Address)} {x : Expanded}
    (run : Ix.Compile.Canon.expandSource source dedup ordered aliases groups keyAddr? = .ok x) :
    DiscoverySpec (fun () => (sourceContext source ordered groups.blocks).protectedNames)
      (IndView.ofConst? source.get?) dedup ordered aliases groups.apply keyAddr? x :=
  CallbackPublic.expand_spec run

theorem componentNested_some {rules : Rules} (discovery : rules.nested = .discovery)
    {env : Env}
    {all : Array Name} {classes : Array (Array Name)} {nested : NestedCanon}
    (run : Ix.Compile.Canon.componentNested rules env all classes = .ok (some nested)) :
    ∃ x, canonExpand rules env classes = .ok x ∧
      nested.canonClasses = x.aux.map (fun m => #[m.name]) ∧
      sigsInOrder x nested.canonClasses = .ok nested.canon ∧
      nested.addrDecided = false ∧
      (∃ source, Ix.Compile.Canon.expand env.ind? rules.dedup all
        (protect := env.protection.source all) = .ok source ∧ nested.source = source.sigs ∧
        computePerm env.addr? nested.canon nested.source all (origToCanonOf classes) = .ok nested.perm) ∧
      nested.evaporated = Array.replicate nested.perm.size false := by
  rw [ComponentCoreProof.componentNested_eq_core] at run
  exact CallbackPublic.componentNested_some discovery run

theorem componentNested_discovery {rules : Rules} (discovery : rules.nested = .discovery)
    {env : Env}
    {all : Array Name} {classes : Array (Array Name)} {nested : NestedCanon}
    (run : Ix.Compile.Canon.componentNested rules env all classes = .ok (some nested)) :
    ∃ x, canonExpand rules env classes = .ok x ∧
      nested.canonClasses = x.aux.map (fun m => #[m.name]) ∧
      sigsInOrder x nested.canonClasses = .ok nested.canon ∧
      DiscoverySpec (env.protection.canonical (repsOf classes)) env.ind? rules.dedup
        (repsOf classes) (aliasesOf classes) env.groupOf (some env.addr?) x ∧
      (∀ (i : Nat) (member : XMember), x.types[i]? = some member →
        member.sourceOwner ∈ repsOf classes) ∧
      (∃ D : List Nat, D.length = x.aux.size ∧ D.Pairwise (· ≤ ·) ∧
        ∀ (k d : Nat), D[k]? = some d → d < x.nOriginals + k) := by
  rw [ComponentCoreProof.componentNested_eq_core] at run
  exact CallbackPublic.componentNested_discovery discovery run

theorem componentNested_source_spec {rules : Rules} (discovery : rules.nested = .discovery)
    {env : SourceEnv} {all : Array Name} {classes : Array (Array Name)}
    {nested : NestedCanon}
    (run : Ix.Compile.Canon.componentNested rules (Env.ofSource env) all classes = .ok (some nested)) :
    ∃ x, Ix.CompileCert.Canon.canonExpand rules (Env.ofSource env) classes = .ok x ∧
      nested.canonClasses = x.aux.map (fun m => #[m.name]) ∧
      sigsInOrder x nested.canonClasses = .ok nested.canon ∧
      DiscoverySpec
        (fun () => (sourceContext env.source (repsOf classes) env.groupOf.blocks).protectedNames)
        env.ind? rules.dedup (repsOf classes) (aliasesOf classes) env.groupOf.apply
        (some env.addr?) x ∧
      (∀ (i : Nat) (member : XMember), x.types[i]? = some member →
        member.sourceOwner ∈ repsOf classes) ∧
      (∃ D : List Nat, D.length = x.aux.size ∧ D.Pairwise (· ≤ ·) ∧
        ∀ (k d : Nat), D[k]? = some d → d < x.nOriginals + k) :=
  componentNested_discovery discovery run

theorem canonBlock_nested_discovery {rules : Rules} (discovery : rules.nested = .discovery)
    {env : Env}
    {all : Array Name} {b : BlockCanon}
    (run : Ix.Compile.Canon.canonBlock rules env all = .ok b)
    {component : ComponentCanon} (member : component ∈ b.components)
    {nested : NestedCanon} (hasNested : component.nested = some nested) :
    ∃ x, canonExpand rules env component.classes = .ok x ∧
      nested.canonClasses = x.aux.map (fun m => #[m.name]) ∧
      sigsInOrder x nested.canonClasses = .ok nested.canon ∧ nested.addrDecided = false ∧
      CallbackPublic.DiscoverySpec (env.protection.canonical (repsOf component.classes))
        env.ind? rules.dedup (repsOf component.classes) (aliasesOf component.classes)
        env.groupOf (some env.addr?) x ∧
      (∀ (i : Nat) (entry : XMember), x.types[i]? = some entry →
        entry.sourceOwner ∈ repsOf component.classes) ∧
      (∃ D : List Nat, D.length = x.aux.size ∧ D.Pairwise (· ≤ ·) ∧
        ∀ (k d : Nat), D[k]? = some d → d < x.nOriginals + k) := by
  rw [ComponentCoreProof.canonBlock_eq_core] at run
  exact CallbackBlock.canonBlock_nested_history discovery run member hasNested

theorem canonBlock_member_order {rules : Rules} (hseed : rules.seed = .byNameHash) {env : Env}
    {all all' : Array Name} (hp : all.toList.Perm all'.toList) (hnd : NodupB (nodesOf env all))
    (hwf : EnvWF env all) {b b' : BlockCanon} (h : Ix.Compile.Canon.canonBlock rules env all = .ok b)
    (h' : Ix.Compile.Canon.canonBlock rules env all' = .ok b') :
    ∀ c ∈ b.components, ∃ c' ∈ b'.components, c.members.toList.Perm c'.members.toList ∧
      c'.classes = c.classes ∧ c'.blindClasses = c.blindClasses ∧ c'.stats = c.stats :=
  canonBlock_source_member_order hseed hp hnd hwf h h'

theorem canonBlock_separate {rules : Rules} {env : Env} {all : Array Name} {b : BlockCanon}
    (hnd : NodupB (nodesOf env all)) (hwf : EnvWF env all) (h : Ix.Compile.Canon.canonBlock rules env all = .ok b)
    {c : ComponentCanon} (hc : c ∈ b.components) {b' : BlockCanon}
    (h' : Ix.Compile.Canon.canonBlock rules env c.members = .ok b') :
    ∃ c', b'.components = #[c'] ∧ c'.members = c.members ∧ c'.classes = c.classes ∧
      c'.blindClasses = c.blindClasses ∧ c'.stats = c.stats :=
  canonBlock_source_separate hnd hwf h hc h'

theorem canonBlock_member_order_nested {rules : Rules} (hseed : rules.seed = .byNameHash)
    (hr : rules.nested = .discovery) {env : Env} {all all' : Array Name}
    (hp : all.toList.Perm all'.toList) (hnd : NodupB (nodesOf env all)) (hwf : EnvWF env all)
    {b b' : BlockCanon} (h : Ix.Compile.Canon.canonBlock rules env all = .ok b) (h' : Ix.Compile.Canon.canonBlock rules env all' = .ok b') :
    ∀ c ∈ b.components, ∃ c' ∈ b'.components, c.members.toList.Perm c'.members.toList ∧
      c'.classes = c.classes ∧ c'.blindClasses = c.blindClasses ∧ c'.stats = c.stats ∧
      canonAux c'.nested = canonAux c.nested :=
  canonBlock_source_member_order_nested hseed hr hp hnd hwf h h'

theorem canonBlock_separate_nested {rules : Rules} (hr : rules.nested = .discovery) {env : Env}
    {all : Array Name} {b : BlockCanon} (hnd : NodupB (nodesOf env all)) (hwf : EnvWF env all)
    (h : Ix.Compile.Canon.canonBlock rules env all = .ok b) {c : ComponentCanon} (hc : c ∈ b.components)
    {b' : BlockCanon} (h' : Ix.Compile.Canon.canonBlock rules env c.members = .ok b') :
    ∃ c', b'.components = #[c'] ∧ c'.members = c.members ∧ c'.classes = c.classes ∧
      c'.blindClasses = c.blindClasses ∧ c'.stats = c.stats ∧ canonAux c'.nested = canonAux c.nested :=
  canonBlock_source_separate_nested hr hnd hwf h hc h'

end Ix.CompileCert.Canon
