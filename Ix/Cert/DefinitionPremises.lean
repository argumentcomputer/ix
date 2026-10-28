import Ix.Cert.DefinitionBlockReads
import Ix.Cert.Statement
import Ix.CompileCert.Canon.QSort

/-! # A definition group's member names are distinct

`DefinitionBlockReads.definition_block_reads` asks that a definition group's members have
distinct names. Quotient Source's definition groups are its condensation components' constants
(`groupsOf_definitions`): a component's members are a set of names, which hold no two names of
one stored hash, and a constant the closure stores carries its key's name up to that hash
(`sub_named`, from the compile's input-name check and the closure's lookups), so the group's
names have no two of one stored hash (`componentGroup_distinct`), and they are distinct
(`distinct_of_groupsOf`). -/

namespace Ix.Cert.DefinitionPremises

open Ix.LeanIngress
open Ix.CompileCert.Loop (idBind idPure)

/-- An invariant of an `Id` loop's states holds of its result. -/
theorem forIn_id_prop {α σ : Type} (I : σ → Prop) {Q : σ → Prop} {f : α → σ → Id (ForInStep σ)} :
    ∀ (l : List α), (∀ x ∈ l, ∀ s, I s → I (f x s).value) → (∀ t, I t → Q t) →
      ∀ s, I s → Q (Id.run (forIn l s f))
  | [], _, concl, s, hs => concl s hs
  | x :: l, step, concl, s, hs => by
    rw [List.forIn_cons]
    have hx := step x List.mem_cons_self s hs
    generalize f x s = v at hx ⊢
    cases v with
    | done b => exact concl b hx
    | yield b =>
      exact forIn_id_prop I l (fun y hy => step y (List.mem_cons_of_mem _ hy)) concl b hx

/-- Names of two stored hashes, related to two names of two stored hashes. -/
theorem name_beq_false {a b x y : Ix.Name} (ha : (a == x) = true) (hb : (b == y) = true)
    (hxy : (x == y) = false) : (a == b) = false := by
  cases hab : (a == b)
  · rfl
  · have : (x == y) = true := BEq.trans (BEq.trans (BEq.symm ha) hab) hb
    rw [this] at hxy
    cases hxy

/-- **A constant the closure stores carries its key's name**, up to the stored hash: the
closure's lookups are the input's, and the compile's input-name check makes every input
constant's own name the key it is stored under (`inputsNamed`). -/
theorem sub_named {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} (closure : IsClosure env roots sub)
    (compiled : compileReport env = .ok (ixe, failures)) :
    ∀ k ci, sub.consts.get? k = some ci → (ci.getCnst.name == k) = true := by
  intro k ci h
  have henv := closure.mem_env h
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList] at henv
  obtain ⟨k', hk', hmem⟩ := henv
  rw [inputsNamed compiled k' ci hmem]
  exact BEq.symm hk'

/-- **A component group's definitions have no two names of one stored hash.** -/
theorem componentGroup_distinct {env : Ix.Environment} {members : Ix.Set Ix.Name}
    {ms : Array Ix.ConstantInfo} (named : ∀ k ci, env.consts.get? k = some ci → (ci.getCnst.name == k) = true)
    (h : componentGroup env members = some (.definitions ms)) :
    (ms.toList.map (·.getCnst.name)).Pairwise (fun a b => (a == b) = false) := by
  unfold componentGroup componentGroupUsing at h
  generalize hcis : (Array.filterMapM (m := Id) (fun x => env.consts.get? x) members.toArray :
    Array Ix.ConstantInfo) = cis at h
  dsimp only [Id.run, bind, pure] at h
  have hcisL : (Id.run cis).toList = members.toList.filterMap (fun x => env.consts.get? x) := by
    rw [← hcis]
    show (members.toArray.filterMap (fun x => env.consts.get? x)).toList = _
    rw [Array.toList_filterMap, Std.HashSet.toList_toArray]
  have pw : ((Id.run cis).toList.map (·.getCnst.name)).Pairwise (fun a b => (a == b) = false) := by
    rw [hcisL, List.map_filterMap]
    refine List.Pairwise.filterMap _ ?_ Std.HashSet.distinct_toList
    intro x y hxy a ha b hb
    simp only [Option.map_eq_some_iff] at ha hb
    obtain ⟨ci, hci, rfl⟩ := ha
    obtain ⟨cj, hcj, rfl⟩ := hb
    exact name_beq_false (named x ci hci) (named y cj hcj) hxy
  generalize hothers : (cis.filter (fun x => !isFamily x)).qsort
    (fun a b => Ix.sourceOrderLt (a.blockPosition, a.getCnst.name)
      (b.blockPosition, b.getCnst.name)) = others at h
  have pwo : (others.toList.map (·.getCnst.name)).Pairwise (fun a b => (a == b) = false) := by
    rw [← hothers]
    have perm := Array.perm_iff_toList_perm.mp (Ix.CompileCert.Canon.qsort_perm
      (cis.filter (fun x => !isFamily x))
      (fun a b => Ix.sourceOrderLt (a.blockPosition, a.getCnst.name) (b.blockPosition, b.getCnst.name)))
    have base : ((cis.filter (fun x => !isFamily x)).toList.map (·.getCnst.name)).Pairwise
        (fun a b => (a == b) = false) := by
      rw [Array.toList_filter]
      exact pw.sublist (List.filter_sublist.map _)
    exact base.perm (perm.map _).symm (fun h => by rw [BEq.comm]; exact h)
  have hms : ms = others := by
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
          rfl
        · exfalso
          obtain ⟨l⟩ := others
          rcases l with _ | ⟨c, _ | ⟨c₂, rest⟩⟩
          · cases h
          · cases c <;> cases h
          · cases h
  subst hms
  exact pwo

/-- **A definition group of quotient Source's groups is a component's group.** -/
theorem groupsOf_definitions (env : Ix.Environment) (blocks : Ix.CondensedBlocks) :
    ∀ ms, Group.definitions ms ∈ groupsOf env blocks →
      ∃ members, componentGroup env members = some (.definitions ms) := by
  unfold groupsOf
  simp only [Id.run, Std.HashMap.forIn_eq_forIn_toList, idBind, idPure]
  refine forIn_id_prop (I := fun acc : Array Group => ∀ ms, Group.definitions ms ∈ acc →
      ∃ members, componentGroup env members = some (.definitions ms)) _ ?_ (fun _ h => h) _ ?_
  · intro x _ s hs
    split
    · exact hs
    · intro ms hms
      rcases Array.mem_push.mp hms with hms | heq
      · exact hs ms hms
      · unfold unplaced at heq
        split at heq <;> cases heq
  · refine forIn_id_prop (I := fun acc : Array Group => ∀ ms, Group.definitions ms ∈ acc →
        ∃ members, componentGroup env members = some (.definitions ms)) _ ?_ (fun _ h => h) _ ?_
    · intro x _ s hs
      split
      · rename_i g' hg'
        intro ms hms
        rcases Array.mem_push.mp hms with hms | heq
        · exact hs ms hms
        · exact ⟨_, heq ▸ hg'⟩
      · exact hs
    · refine forIn_id_prop (I := fun acc : Array Group => ∀ ms, Group.definitions ms ∈ acc →
          ∃ members, componentGroup env members = some (.definitions ms)) _ ?_ (fun _ h => h) _ ?_
      · intro x _ s hs
        split
        · split
          · intro ms hms
            rcases Array.mem_push.mp hms with hms | heq
            · exact hs ms hms
            · exfalso
              rcases Ix.CompileCert.SourceConstructorPositions.inductiveGroup_cases env _ _ with
                ⟨names, e, hi⟩ | ⟨types, ctors, recs, hi⟩
              · rw [hi] at heq; cases heq
              · rw [hi] at heq; cases heq
          · exact hs
        · exact hs
      · intro ms hms
        exact absurd hms (Array.not_mem_empty _)

theorem names_of_views : ∀ {members : List Ix.ConstantInfo} {defs : List Ix.Def},
    List.Forall₂ (fun ci d => Ix.CompileCert.EmissionDispatch.sourceData ci = some d) members defs →
      defs.map (·.name) = members.map (·.getCnst.name)
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h rest => by
    simp only [List.map_cons, names_of_views rest, (RecordReadings.sourceData_facts h).1]

/-- **A definition group of an accepted closure has distinct member names**: the premise
`distinct` of `DefinitionBlockReads.definition_block_reads`, for the compiler's views `defs`
of a definition group of quotient Source's groups of the closure. -/
theorem distinct_of_groupsOf {env : Ix.Environment} {roots : List Ix.Name} {sub : Ix.Environment}
    {ixe : Ixon.Env} {failures : Failures} (closure : IsClosure env roots sub)
    (compiled : compileReport env = .ok (ixe, failures)) {blocks : Ix.CondensedBlocks}
    {members : Array Ix.ConstantInfo} (hg : Group.definitions members ∈ groupsOf sub blocks)
    {defs : List Ix.Def}
    (views : List.Forall₂ (fun ci d => Ix.CompileCert.EmissionDispatch.sourceData ci = some d)
      members.toList defs) :
    Ix.CompileCert.Canon.KeysDistinct (defs.map MutConst.defn) := by
  obtain ⟨set, hset⟩ := groupsOf_definitions sub blocks members hg
  apply DefinitionBlockReads.keysDistinct_of_pairwise
  rw [names_of_views views]
  exact componentGroup_distinct (sub_named closure compiled) hset

/--
info: 'Ix.Cert.DefinitionPremises.distinct_of_groupsOf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms distinct_of_groupsOf

end Ix.Cert.DefinitionPremises
