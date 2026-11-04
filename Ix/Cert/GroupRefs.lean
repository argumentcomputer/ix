import Ix.Cert.ScheduleOrder
import Ix.Cert.Condense

/-! # A group's references lie in it or in the groups it references

Quotient Source's graph (`Ix.LeanIngress.graphOf`) gives each group the groups it references
(`Graph.hard`): for each of its names, the references outside the name's strongly connected
component (`CondensedBlocks.blockRefs` at the name's representative), by the group that holds
each. A group whose every name has a representative and every reference a group is placed
(`Graph.unplaced`), and the schedule lets through only placed groups. So a reference of a name
of a group the schedule lets through, outside the name's component, is a name of the group or
of a group it references (`refs_in_hard`).

* `graphOf_hard`, `graphOf_unplaced`: `graphOf`'s two loops, named (`groupIndex`, `scanGroup`,
  `scanGroups`);
* `groupIndex_get`: a name's group holds a name that hashes like it;
* `scanGroup_covers`: a group scanned without a refusal has every name's representative's
  references in its own group or its references;
* `condense_lowLinks`, `condense_blockRefs_complete`: a name's representative's block holds
  the name, and the block's references hold every reference of a member outside the block. -/

namespace Ix.Cert.GroupRefs

open Ix.LeanIngress
open Ix.Kernel.Reader (CName ReadError)

/-! ## Loops that always continue -/

/-- A loop in `Id` whose body always continues is a left fold. -/
theorem forIn_yield_foldl {α σ : Type} (f : α → σ → Id (ForInStep σ)) (hy : ∀ x s, ∃ s', f x s = .yield s') :
    ∀ (l : List α) (init : σ), forIn l init f = l.foldl (fun s x => (f x s).value) init
  | [], _ => rfl
  | x :: l, init => by
    obtain ⟨s', h⟩ := hy x init
    rw [List.forIn_cons, List.foldl_cons, h]
    exact forIn_yield_foldl f hy l s'

/-- A fold pushing one entry per element onto two arrays appends their maps. -/
theorem foldl_push {α β γ : Type} (A : α → β) (B : α → γ) :
    ∀ (l : List α) (h : Array β) (u : Array γ),
      l.foldl (fun s x => (s.1.push (A x), s.2.push (B x))) (h, u) = (h ++ (l.map A).toArray, u ++ (l.map B).toArray)
  | [], h, u => by simp
  | x :: l, h, u => by
    rw [List.foldl_cons, foldl_push A B l]
    simp

/-! ## `graphOf`'s loops -/

/-- `graphOf`'s first loop: the group of each name, and of each literal support name. -/
def groupIndex (groups : Array Group) : Ix.Map TableName Nat × Std.HashMap (CName .source) Nat := Id.run do
  let supportNames := Ix.Kernel.Reader.strLitSupportNames
  let mut groupOf : Ix.Map TableName Nat := {}
  let mut supportOf : Std.HashMap (CName .source) Nat := {}
  for (g, i) in groups.zipIdx do
    for n in g.names do
      groupOf := groupOf.insert n i
      if let some k := supportNames.find? (nameIs n) then supportOf := supportOf.insert k i
  return (groupOf, supportOf)

/-- `graphOf`'s scan of one group: the representatives seen, the groups referenced, and the
first refusal. -/
def scanGroup (blocks : Ix.CondensedBlocks) (groupOf : Ix.Map TableName Nat) (g : Group) (i : Nat) :
    Ix.Set TableName × Std.HashSet Nat × Option ReadError := Id.run do
  let mut seenLo : Ix.Set TableName := {}
  let mut ds : Std.HashSet Nat := {}
  let mut bad : Option ReadError := none
  for n in g.names do
    let some lo := blocks.lowLinks.get? n
      | if bad.isNone then
          bad := some (.malformed s!"constant {ingressName n} is not in the condensation")
    if seenLo.contains lo then continue
    seenLo := seenLo.insert lo
    for r in (blocks.blockRefs.get? lo).getD {} do
      match groupOf.get? r with
      | some j => if j != i then ds := ds.insert j
      | none =>
        if bad.isNone then
          bad := some (.malformed s!"references {ingressName r}, which is not in the environment")
  return (seenLo, ds, bad)

/-- `graphOf`'s second loop: every group scanned. -/
def scanGroups (blocks : Ix.CondensedBlocks) (groups : Array Group) (groupOf : Ix.Map TableName Nat) :
    Array (Array Nat) × Array (Option ReadError) := Id.run do
  let mut hard : Array (Array Nat) := #[]
  let mut unplaced : Array (Option ReadError) := #[]
  for (g, i) in groups.zipIdx do
    let s := scanGroup blocks groupOf g i
    hard := hard.push (s.2.1.toArray.qsort (· < ·))
    unplaced := unplaced.push s.2.2
  return (hard, unplaced)

theorem graphOf_hard (blocks : Ix.CondensedBlocks) (groups : Array Group)
    (converted : Array (Except ReadError Converted)) :
    (graphOf blocks groups converted).hard = (scanGroups blocks groups (groupIndex groups).1).1 := rfl

theorem graphOf_unplaced (blocks : Ix.CondensedBlocks) (groups : Array Group)
    (converted : Array (Except ReadError Converted)) :
    (graphOf blocks groups converted).unplaced = (scanGroups blocks groups (groupIndex groups).1).2 := rfl

/-- **The scan of every group, by index.** -/
theorem scanGroups_get (blocks : Ix.CondensedBlocks) (groups : Array Group) (groupOf : Ix.Map TableName Nat)
    {i : Nat} {gr : Group} (hgr : groups[i]? = some gr) :
    (scanGroups blocks groups groupOf).1[i]? =
        some ((scanGroup blocks groupOf gr i).2.1.toArray.qsort (· < ·)) ∧
      (scanGroups blocks groups groupOf).2[i]? = some (scanGroup blocks groupOf gr i).2.2 := by
  unfold scanGroups
  simp only [Id.run]
  rw [← Array.forIn_toList, forIn_yield_foldl]
  · have e := foldl_push (fun x : Group × Nat => (scanGroup blocks groupOf x.1 x.2).2.1.toArray.qsort (· < ·))
      (fun x : Group × Nat => (scanGroup blocks groupOf x.1 x.2).2.2) groups.zipIdx.toList #[] #[]
    have hz : groups.zipIdx.toList[i]? = some (gr, i) := by
      rw [Array.toList_zipIdx, List.getElem?_zipIdx, Array.getElem?_toList, hgr]
      simp
    refine ⟨?_, ?_⟩
    · refine (congrArg (fun p : Array (Array Nat) × Array (Option ReadError) => p.1[i]?) e).trans ?_
      simp only [hz, List.getElem?_map, Option.map_some, List.getElem?_toArray, Array.empty_append]
    · refine (congrArg (fun p : Array (Array Nat) × Array (Option ReadError) => p.2[i]?) e).trans ?_
      simp only [hz, List.getElem?_map, Option.map_some, List.getElem?_toArray, Array.empty_append]
  · intro _ _; exact ⟨_, rfl⟩

/-- **A name's group holds it**: the ingress's own tables compare names exactly. -/
theorem groupIndex_get {groups : Array Group} {r : TableName} {j : Nat}
    (h : (groupIndex groups).1.get? r = some j) :
    ∃ gr, groups[j]? = some gr ∧ (r : Ix.Name) ∈ gr.names := by
  let I : Ix.Map TableName Nat × Std.HashMap (CName .source) Nat → Prop := fun s =>
    ∀ (r : TableName) j, s.1.get? r = some j → ∃ gr, groups[j]? = some gr ∧ (r : Ix.Name) ∈ gr.names
  suffices hI : I (groupIndex groups) from hI r j h
  unfold groupIndex
  simp only [Id.run]
  rw [← Array.forIn_toList, forIn_yield_foldl]
  · refine Condense.foldl_inv I _ _ _ (fun r j h => by
      change (∅ : Ix.Map TableName Nat).get? r = some j at h
      rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty] at h; cases h) fun s x hx hs => ?_
    obtain ⟨g, i⟩ := x
    have hgi : groups[i]? = some g := by
      rw [Array.toList_zipIdx] at hx
      have := List.mem_zipIdx_iff_getElem?.mp hx
      simpa using this
    simp only []
    rw [← Array.forIn_toList, forIn_yield_foldl]
    · refine Condense.foldl_inv I _ _ _ hs fun s' n hn hs' r' j' h' => ?_
      split at h' <;>
      · change (Std.HashMap.insert s'.fst (n : TableName) i).get? r' = some j' at h'
        rw [Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert (m := s'.fst) (k := (n : TableName)) (a := r') (v := i)] at h'
        split at h'
        · rename_i same
          cases h'
          have e : (n : TableName) = r' := (beq_iff_eq (α := TableName)).mp same
          exact ⟨g, hgi, e ▸ Array.mem_toList_iff.mp hn⟩
        · rw [← Std.HashMap.get?_eq_getElem?] at h'
          exact hs' r' j' h'
    · intro n s
      split <;> exact ⟨_, rfl⟩
  · intro _ _; exact ⟨_, rfl⟩

/-! ## A group scanned without a refusal -/

/-- The scan's state: the representatives seen, the groups referenced, the first refusal. -/
abbrev ScanState := Ix.Set TableName × Std.HashSet Nat × Option ReadError

/-- **What a scan state covers**: without a refusal, every reference of a representative seen
has a group, the scanned group or one recorded. -/
def Covered (blocks : Ix.CondensedBlocks) (groupOf : Ix.Map TableName Nat) (i : Nat) (s : ScanState) : Prop :=
  s.2.2 = none → ∀ lo : Ix.Name, s.1.contains lo = true →
    ∀ r ∈ ((blocks.blockRefs.get? lo).getD {}).toList,
      ∃ j, groupOf.get? r = some j ∧ (j = i ∨ s.2.1.contains j = true)

/-- The scan of one representative's references, as a fold. -/
theorem refs_fold {groupOf : Ix.Map TableName Nat} {i : Nat}
    (step : Std.HashSet Nat × Option ReadError → Ix.Name → Std.HashSet Nat × Option ReadError)
    (h1 : ∀ t r, (step t r).2 = none → t.2 = none)
    (h2 : ∀ t r j, t.1.contains j = true → (step t r).1.contains j = true)
    (h3 : ∀ t r, (step t r).2 = none → ∃ j, groupOf.get? r = some j ∧ (j = i ∨ (step t r).1.contains j = true)) :
    ∀ (l : List Ix.Name) t, ((l.foldl step t).2 = none → t.2 = none) ∧
      (∀ j, t.1.contains j = true → (l.foldl step t).1.contains j = true) ∧
      ((l.foldl step t).2 = none → ∀ r ∈ l, ∃ j, groupOf.get? r = some j ∧
        (j = i ∨ (l.foldl step t).1.contains j = true))
  | [], t => ⟨id, fun _ h => h, fun _ r hr => nomatch hr⟩
  | r :: l, t => by
    obtain ⟨b, m, c⟩ := refs_fold step h1 h2 h3 l (step t r)
    refine ⟨fun h => h1 t r (b h), fun j hj => m j (h2 t r j hj), fun h r' hr' => ?_⟩
    rcases List.mem_cons.mp hr' with rfl | hr'
    · obtain ⟨j, hj, hji⟩ := h3 t r' (b h)
      exact ⟨j, hj, hji.imp id (m j)⟩
    · exact c h r' hr'

/-- The scan of a group's names, as a fold. -/
theorem names_fold {blocks : Ix.CondensedBlocks} {groupOf : Ix.Map TableName Nat} {i : Nat}
    (step : ScanState → Ix.Name → ScanState)
    (p1 : ∀ s n, (step s n).2.2 = none → s.2.2 = none)
    (p3 : ∀ s n (lo : Ix.Name), s.1.contains lo = true → (step s n).1.contains lo = true)
    (p4 : ∀ s n, (step s n).2.2 = none →
      ∃ lo, blocks.lowLinks.get? n = some lo ∧ (step s n).1.contains lo = true)
    (p5 : ∀ s n, Covered blocks groupOf i s → Covered blocks groupOf i (step s n)) :
    ∀ (l : List Ix.Name) s, Covered blocks groupOf i s → Covered blocks groupOf i (l.foldl step s) ∧
      ((l.foldl step s).2.2 = none → ∀ n ∈ l,
        ∃ lo, blocks.lowLinks.get? n = some lo ∧ (l.foldl step s).1.contains lo = true)
  | [], s, hs => ⟨hs, fun _ n hn => nomatch hn⟩
  | n :: l, s, hs => by
    have seen : ∀ (l : List Ix.Name) s (lo : Ix.Name), s.1.contains lo = true →
        (l.foldl step s).1.contains lo = true := by
      intro l
      induction l with
      | nil => intro s lo h; exact h
      | cons x l ih => intro s lo h; exact ih _ lo (p3 s x lo h)
    have bad : ∀ (l : List Ix.Name) s, (l.foldl step s).2.2 = none → s.2.2 = none := by
      intro l
      induction l with
      | nil => intro s h; exact h
      | cons x l ih => intro s h; exact p1 s x (ih _ h)
    obtain ⟨cov, rest⟩ := names_fold step p1 p3 p4 p5 l (step s n) (p5 s n hs)
    refine ⟨cov, fun h n' hn' => ?_⟩
    rcases List.mem_cons.mp hn' with rfl | hn'
    · obtain ⟨lo, hlo, hc⟩ := p4 s n' (bad l _ h)
      exact ⟨lo, hlo, seen l _ lo hc⟩
    · exact rest h n' hn'

/-- What one step of the scan, on the name `n`, keeps from `s` to `s'`: a refusal stays, the
representatives seen stay, a step without a refusal sees the name's representative, and the
coverage stays. -/
def StepOK (blocks : Ix.CondensedBlocks) (groupOf : Ix.Map TableName Nat) (i : Nat) (n : Ix.Name)
    (s s' : ScanState) : Prop :=
  (s'.2.2 = none → s.2.2 = none) ∧ (∀ lo : Ix.Name, s.1.contains lo = true → s'.1.contains lo = true) ∧
    (s'.2.2 = none → ∃ lo, blocks.lowLinks.get? n = some lo ∧ s'.1.contains lo = true) ∧
    (Covered blocks groupOf i s → Covered blocks groupOf i s')

/-- `refs_fold`, as a property of the fold's result. -/
theorem refs_fold_on {groupOf : Ix.Map TableName Nat} {i : Nat}
    (step : Std.HashSet Nat × Option ReadError → Ix.Name → Std.HashSet Nat × Option ReadError)
    (h1 : ∀ t r, (step t r).2 = none → t.2 = none)
    (h2 : ∀ t r j, t.1.contains j = true → (step t r).1.contains j = true)
    (h3 : ∀ t r, (step t r).2 = none → ∃ j, groupOf.get? r = some j ∧ (j = i ∨ (step t r).1.contains j = true))
    (l : List Ix.Name) (t : Std.HashSet Nat × Option ReadError) (P : Std.HashSet Nat × Option ReadError → Prop)
    (k : ∀ t', (t'.2 = none → t.2 = none) → (∀ j, t.1.contains j = true → t'.1.contains j = true) →
      (t'.2 = none → ∀ r ∈ l, ∃ j, groupOf.get? r = some j ∧ (j = i ∨ t'.1.contains j = true)) → P t') :
    P (l.foldl step t) :=
  let h := refs_fold step h1 h2 h3 l t
  k _ h.1 h.2.1 h.2.2

theorem contains_empty_set (lo : Ix.Name) : (∅ : Ix.Set TableName).contains lo = false :=
  Std.HashSet.contains_empty (α := TableName)

theorem contains_insert_set {s : Ix.Set TableName} {lo lo' : Ix.Name} :
    (s.insert lo).contains lo' = true ↔ (lo : TableName) = lo' ∨ s.contains lo' = true := by
  rw [Std.HashSet.contains_insert (α := TableName) (k := (lo : TableName)) (a := (lo' : TableName)),
    Bool.or_eq_true]
  exact or_congr_left (beq_iff_eq (α := TableName))

/-- **A group scanned without a refusal covers its names**: every name has a representative,
and every reference of it has a group, the scanned one or one recorded. -/
theorem scanGroup_covers (blocks : Ix.CondensedBlocks) (groupOf : Ix.Map TableName Nat) (g : Group) (i : Nat)
    (hbad : (scanGroup blocks groupOf g i).2.2 = none) :
    ∀ n ∈ g.names, ∃ lo, blocks.lowLinks.get? n = some lo ∧
      ∀ r ∈ ((blocks.blockRefs.get? lo).getD {}).toList,
        ∃ j, groupOf.get? r = some j ∧ (j = i ∨ (scanGroup blocks groupOf g i).2.1.contains j = true) := by
  obtain ⟨step, heq, hstep⟩ : ∃ step : ScanState → Ix.Name → ScanState,
      scanGroup blocks groupOf g i = g.names.toList.foldl step (∅, ∅, none) ∧
      ∀ s n, StepOK blocks groupOf i n s (step s n) := by
    refine ⟨?step, ?eq, ?ok⟩
    case eq =>
      unfold scanGroup
      simp only [Id.run]
      rw [← Array.forIn_toList, forIn_yield_foldl]
      · rfl
      · intro n s
        split
        · split
          · exact ⟨_, rfl⟩
          · exact ⟨_, rfl⟩
        · split <;> exact ⟨_, rfl⟩
    case ok =>
      intro s n
      split
      · rename_i lo hlo
        split
        · rename_i hseen
          exact ⟨id, fun _ h => h, fun _ => ⟨lo, hlo, hseen⟩, id⟩
        · rename_i hseen
          rw [Std.HashSet.forIn_eq_forIn_toList, forIn_yield_foldl]
          · refine refs_fold_on (groupOf := groupOf) (i := i) _ ?h1 ?h2 ?h3 _ _
              (fun res => StepOK blocks groupOf i n s (s.1.insert lo, res.1, res.2)) ?k
            case k =>
              intro t' b m c
              refine ⟨b, fun lo' h => contains_insert_set.mpr (.inr h),
                fun _ => ⟨lo, hlo, contains_insert_set.mpr (.inl rfl)⟩, fun cov hnone lo' hlo' r hr => ?_⟩
              rcases contains_insert_set.mp hlo' with e | hlo'
              · have e' : lo = lo' := e
                subst e'
                exact c hnone r hr
              · obtain ⟨j, hj, hji⟩ := cov (b hnone) lo' hlo' r hr
                exact ⟨j, hj, hji.imp id (m j)⟩
            case h1 =>
              intro t r
              split
              · split
                · exact fun h => h
                · exact fun h => h
              · split
                · exact fun h => by cases h
                · exact fun h => h
            case h2 =>
              intro t r j hj
              split
              · split
                · show (t.1.insert _).contains j = true
                  rw [Std.HashSet.contains_insert, hj, Bool.or_true]
                · exact hj
              · split
                · exact hj
                · exact hj
            case h3 =>
              intro t r
              split
              · rename_i j hj
                split
                · exact fun _ => ⟨j, hj, .inr (by
                    show (t.1.insert j).contains j = true
                    rw [Std.HashSet.contains_insert, beq_self_eq_true, Bool.true_or])⟩
                · rename_i hji
                  exact fun _ => ⟨j, hj, .inl (by simpa using hji)⟩
              · split
                · exact fun h => by cases h
                · rename_i hb
                  intro h
                  have h' : t.2 = none := h
                  rw [h'] at hb
                  exact absurd rfl hb
          · intro r t
            split
            · split <;> exact ⟨_, rfl⟩
            · split <;> exact ⟨_, rfl⟩
      · split
        · exact ⟨(fun h => by cases h), fun _ h => h, (fun h => by cases h), fun _ h => by cases h⟩
        · rename_i hb
          refine ⟨id, fun _ h => h, fun h => ?_, id⟩
          have h' : s.2.2 = none := h
          rw [h'] at hb
          exact absurd rfl hb
  have cov0 : Covered blocks groupOf i (∅, ∅, none) := fun _ lo h => by
    rw [contains_empty_set] at h; cases h
  have fold : ∀ (l : List Ix.Name) s, Covered blocks groupOf i s → Covered blocks groupOf i (l.foldl step s) ∧
      ((l.foldl step s).2.2 = none → ∀ n ∈ l,
        ∃ lo, blocks.lowLinks.get? n = some lo ∧ (l.foldl step s).1.contains lo = true) :=
    names_fold step (fun s n => (hstep s n).1) (fun s n => (hstep s n).2.1) (fun s n => (hstep s n).2.2.1)
      (fun s n => (hstep s n).2.2.2)
  rw [heq] at hbad ⊢
  obtain ⟨cov, names⟩ := fold g.names.toList _ cov0
  intro n hn
  obtain ⟨lo, hlo, hc⟩ := names hbad n (Array.mem_toList_iff.mpr hn)
  exact ⟨lo, hlo, cov hbad lo hc⟩

/-! ## The condensation: a name's block and the block's references -/

/-- `CondenseM.run`'s loop that files each name under its representative. -/
def discMaps (byDiscovery : Std.HashMap UInt64 (Ix.Name × Ix.Name)) :
    Ix.Map Ix.Name (Ix.Set Ix.Name) × Ix.Map Ix.Name Ix.Name := Id.run do
  let mut blocks : Ix.Map Ix.Name (Ix.Set Ix.Name) := {}
  let mut lowLinks : Ix.Map Ix.Name Ix.Name := {}
  for (_, (name, lowName)) in byDiscovery do
    lowLinks := lowLinks.insert name lowName
    blocks := blocks.alter lowName fun x => match x with
      | .some s => .some (s.insert name)
      | .none => .some {name}
  return (blocks, lowLinks)

/-- **`CondenseM.run`'s representatives and blocks, from one loop.** -/
theorem condense_maps (refs : Ix.Map Ix.Name (Ix.Set Ix.Name)) :
    ∃ bd, (CondenseM.run refs).blocks = (discMaps bd).1 ∧ (CondenseM.run refs).lowLinks = (discMaps bd).2 := by
  obtain ⟨hr, hv, -⟩ := Condense.blocks_eq refs
  exact ⟨Condense.discOf (Condense.namesOf refs) (Condense.compsOf refs)
    (Condense.rootNames (Condense.namesOf refs) (Condense.compsOf refs) hr) hv, rfl, rfl⟩

theorem discMaps_lowLinks (bd : Std.HashMap UInt64 (Ix.Name × Ix.Name)) {n lo : Ix.Name}
    (h : (discMaps bd).2.get? n = some lo) :
    ∃ all, (discMaps bd).1.get? lo = some all ∧ all.contains n = true := by
  let I : Ix.Map Ix.Name (Ix.Set Ix.Name) × Ix.Map Ix.Name Ix.Name → Prop := fun s =>
    ∀ n lo, s.2.get? n = some lo → ∃ all, s.1.get? lo = some all ∧ all.contains n = true
  suffices hI : I (discMaps bd) from hI n lo h
  unfold discMaps
  simp only [Id.run, Std.HashMap.forIn_eq_forIn_toList, List.forIn_pure_yield_eq_foldl]
  refine Condense.foldl_inv I _ _ _ (fun n lo h => by
    rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty] at h; cases h) fun s x _ hs n lo h => ?_
  obtain ⟨d, name, lowName⟩ := x
  change (s.2.insert name lowName).get? n = some lo at h
  change ∃ all, (s.1.alter lowName fun x => match x with
      | .some s => .some (s.insert name)
      | .none => .some {name}).get? lo = some all ∧ all.contains n = true
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] at h
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_alter]
  split at h
  · rename_i same
    have e := Option.some.inj h
    subst e
    simp only [BEq.rfl, ↓reduceIte]
    cases s.1[lowName]? with
    | some s0 => exact ⟨_, rfl, by rw [Std.HashSet.contains_insert, same, Bool.true_or]⟩
    | none =>
      refine ⟨_, rfl, ?_⟩
      show (({} : Ix.Set Ix.Name).insert name).contains n = true
      rw [Std.HashSet.contains_insert, same, Bool.true_or]
  · rw [← Std.HashMap.get?_eq_getElem?] at h
    obtain ⟨all, hall, hn⟩ := hs n lo h
    split
    · rename_i same
      rw [Std.HashMap.getElem?_congr same, ← Std.HashMap.get?_eq_getElem?, hall]
      exact ⟨_, rfl, by rw [Std.HashSet.contains_insert, hn, Bool.or_true]⟩
    · rw [← Std.HashMap.get?_eq_getElem?]
      exact ⟨all, hall, hn⟩

/-- **A name's representative's block holds the name.** -/
theorem condense_lowLinks {refs : Ix.Map Ix.Name (Ix.Set Ix.Name)} {n lo : Ix.Name}
    (h : (CondenseM.run refs).lowLinks.get? n = some lo) :
    ∃ all, (CondenseM.run refs).blocks.get? lo = some all ∧ all.contains n = true := by
  obtain ⟨bd, hb, hl⟩ := condense_maps refs
  rw [hl] at h
  rw [hb]
  exact discMaps_lowLinks bd h

/-- A fold of unions holds every element of a listed member's set. -/
theorem foldl_union_contains (refs : Ix.Map Ix.Name (Ix.Set Ix.Name)) {a r : Ix.Name}
    (hr : (refs.getD a {}).contains r = true) :
    ∀ (l : List Ix.Name) (acc : Ix.Set Ix.Name), (a ∈ l ∨ acc.contains r = true) →
      (l.foldl (fun (s : Ix.Set Ix.Name) a => s.union (refs.getD a {})) acc).contains r = true
  | [], _, h => by
    rcases h with h | h
    · cases h
    · exact h
  | x :: l, acc, h => by
    rw [List.foldl_cons]
    refine foldl_union_contains refs hr l _ ?_
    rcases h with h | h
    · rcases List.mem_cons.mp h with rfl | h
      · exact .inr (by change (acc ∪ refs.getD a {}).contains r = true
                       rw [Std.HashSet.contains_union, hr, Bool.or_true])
      · exact .inl h
    · exact .inr (by change (acc ∪ refs.getD x {}).contains r = true
                     rw [Std.HashSet.contains_union, h, Bool.true_or])

/-- The block's filtered union holds a member's reference outside the block. -/
theorem filter_union_contains (all : Ix.Set Ix.Name) (refs : Ix.Map Ix.Name (Ix.Set Ix.Name)) {n r : Ix.Name}
    (hn : n ∈ all.toList) (hr : (refs.getD n {}).contains r = true) (hout : all.contains r = false) :
    (Std.HashSet.filter (fun y => !all.contains y)
      (List.foldl (fun (b : Ix.Set Ix.Name) a => Std.HashSet.union b (refs.getD a ∅)) ∅ all.toList)).contains r =
      true := by
  have hu := foldl_union_contains refs hr all.toList ∅ (.inl hn)
  rw [← Std.HashSet.mem_iff_contains, Std.HashSet.mem_filter]
  have hmem : r ∈ (List.foldl (fun (b : Ix.Set Ix.Name) a => Std.HashSet.union b (refs.getD a ∅)) ∅
      all.toList) := Std.HashSet.mem_iff_contains.mpr hu
  refine ⟨hmem, ?_⟩
  rw [Std.HashSet.contains_congr (Std.HashSet.get_beq hmem), hout]
  rfl

/-- **A block's references hold every reference of a member outside the block.** -/
theorem blockRefs_complete {refs blocks : Ix.Map Ix.Name (Ix.Set Ix.Name)} {lo : Ix.Name}
    {all : Ix.Set Ix.Name} (hb : blocks.get? lo = some all) {n r : Ix.Name} (hn : all.contains n = true)
    (hr : (refs.getD n {}).contains r = true) (hout : all.contains r = false) :
    (((Condense.blockRefsOf refs blocks).get? lo).getD {}).contains r = true := by
  have hb' := hb
  rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList] at hb'
  obtain ⟨k, rk, hk⟩ := hb'
  -- the member, as listed in the block
  obtain ⟨n', hn', e⟩ := List.contains_iff_exists_mem_beq.mp
    (by rw [Std.HashSet.contains_toList]; exact hn : all.toList.contains n = true)
  have hr' : (refs.getD n' {}).contains r = true := by
    rw [Std.HashMap.getD_congr (BEq.symm e)]; exact hr
  unfold Condense.blockRefsOf
  simp only [Id.run, Std.HashMap.forIn_eq_forIn_toList, Std.HashSet.forIn_eq_forIn_toList,
    List.forIn_pure_yield_eq_foldl, pure_bind]
  let F : Ix.Name × Ix.Set Ix.Name → Ix.Set Ix.Name := fun a =>
    Std.HashSet.filter (fun x => !a.snd.contains x)
      (List.foldl (fun (b : Ix.Set Ix.Name) a => Std.HashSet.union b (refs.getD a ∅)) ∅ a.snd.toList)
  change (((List.foldl (fun (m : Ix.Map Ix.Name (Ix.Set Ix.Name)) x => m.insert x.1 (F x)) ∅
    blocks.toList).get? lo).getD {}).contains r = true
  have hc := Condense.foldl_insert_contains_of (fun x : Ix.Name × Ix.Set Ix.Name => x.1) F blocks.toList ∅ hk
    (BEq.symm rk)
  obtain ⟨rs, hrs⟩ : ∃ rs, (List.foldl (fun (m : Ix.Map Ix.Name (Ix.Set Ix.Name)) x => m.insert x.1 (F x)) ∅
      blocks.toList).get? lo = some rs :=
    Option.isSome_iff_exists.mp (by
      rw [Std.HashMap.get?_eq_getElem?, ← Std.HashMap.contains_eq_isSome_getElem?]; exact hc)
  rw [hrs, Option.getD_some]
  refine Condense.foldl_insert_get_of (P := fun key v => (key == lo) = true → v.contains r = true)
    (fun x => x.1) F blocks.toList ∅
    (fun n v h => by rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_empty] at h; cases h)
    (fun x hx key hkey hkl => ?_) lo rs hrs (BEq.refl lo)
  have hx2 : blocks.get? lo = some x.2 := Condense.get_of_mem_toList hx (BEq.trans hkey hkl)
  rw [hb] at hx2
  have e : x.2 = all := (Option.some.inj hx2).symm
  show (Std.HashSet.filter (fun y => !x.2.contains y)
    (List.foldl (fun (b : Ix.Set Ix.Name) a => Std.HashSet.union b (refs.getD a ∅)) ∅ x.2.toList)).contains r = true
  rw [e]
  exact filter_union_contains all refs hn' hr' hout

/-! ## A scheduled group's references -/

/-- **`graphOf` places a group's references**: a placed group's names have representatives, and
every reference of a representative is a name of a group, the group itself or one it
references. -/
theorem graphOf_covers (blocks : Ix.CondensedBlocks) (groups : Array Group)
    (converted : Array (Except ReadError Converted)) {i : Nat} {gr : Group} (hgr : groups[i]? = some gr)
    (placed : (graphOf blocks groups converted).unplaced[i]! = none) {n : Ix.Name} (hn : n ∈ gr.names) :
    ∃ lo, blocks.lowLinks.get? n = some lo ∧ ∀ r ∈ ((blocks.blockRefs.get? lo).getD {}).toList,
      ∃ j gr', groups[j]? = some gr' ∧ (r : Ix.Name) ∈ gr'.names ∧
        (j = i ∨ j ∈ (graphOf blocks groups converted).hard[i]!) := by
  obtain ⟨hh, hu⟩ := scanGroups_get blocks groups (groupIndex groups).1 hgr
  have hbad : (scanGroup blocks (groupIndex groups).1 gr i).2.2 = none := by
    rw [graphOf_unplaced, getElem!_def, hu] at placed
    exact placed
  obtain ⟨lo, hlo, cov⟩ := scanGroup_covers blocks (groupIndex groups).1 gr i hbad n hn
  refine ⟨lo, hlo, fun r hr => ?_⟩
  obtain ⟨j, hj, hji⟩ := cov r hr
  obtain ⟨gr', hgr', hr'⟩ := groupIndex_get hj
  refine ⟨j, gr', hgr', hr', hji.imp id fun hd => ?_⟩
  rw [graphOf_hard, getElem!_def, hh]
  exact Ix.CompileCert.Canon.mem_qsort.mpr (Std.HashSet.mem_toArray.mpr (Std.HashSet.mem_iff_contains.mpr hd))

/-- **The schedule lets through placed groups only.** -/
theorem scheduled_placed {g : Graph} {x : Nat × Except ReadError Converted} {conv : Converted}
    (hx : x ∈ scheduleOf g) (hc : x.2 = .ok conv) : g.unplaced[x.1]! = none := by
  rw [ScheduleOrder.scheduleOf_eq] at hx
  obtain ⟨i, -, rfl⟩ := Array.mem_map.mp hx
  simp only at hc ⊢
  unfold ScheduleOrder.admit at hc
  cases hcv : g.converted[i]! with
  | error e => rw [hcv] at hc; cases hc
  | ok c =>
    simp only [hcv, bind, Except.bind] at hc
    cases hu : g.unplaced[i]! with
    | none => rfl
    | some e => rw [hu] at hc; cases hc

/-- **A reference of a scheduled group's name, outside the name's strongly connected component,
is (up to the names' hash) a name of the group or of a group it references** (`Graph.hard`). -/
theorem refs_in_hard {ρ : FiberMap} {hints : CName .source → Option Ix.Kernel.ReducibilityHint}
    {env : Ix.Environment} {x : Nat × Except ReadError Converted} {conv : Converted}
    (hx : x ∈ scheduleOf (graphCollapsed ρ hints env (blocksOf env))) (hc : x.2 = .ok conv) {gr : Group}
    (hgr : (graphCollapsed ρ hints env (blocksOf env)).groups[x.1]? = some gr) {n m : Ix.Name}
    (hn : n ∈ gr.names) (hm : ((groundedRefs env).getD n {}).contains m = true)
    (hout : ∀ lo all, (blocksOf env).lowLinks.get? n = some lo → (blocksOf env).blocks.get? lo = some all →
      all.contains m = false) :
    ∃ k, (k == m) = true ∧ (k ∈ gr.names ∨ ∃ j ∈ (graphCollapsed ρ hints env (blocksOf env)).hard[x.1]!,
      ∃ gr', (graphCollapsed ρ hints env (blocksOf env)).groups[j]? = some gr' ∧ k ∈ gr'.names) := by
  have placed := scheduled_placed hx hc
  obtain ⟨lo, hlo, cov⟩ := graphOf_covers (blocksOf env) (groupsOf env (blocksOf env))
    ((groupsOf env (blocksOf env)).map convert) hgr placed hn
  obtain ⟨all, hall, hnall⟩ := condense_lowLinks hlo
  have hin : (((blocksOf env).blockRefs.get? lo).getD {}).contains m = true :=
    blockRefs_complete hall hnall hm (hout lo all hlo hall)
  obtain ⟨k, hk, hmk⟩ := List.contains_iff_exists_mem_beq.mp
    (by rw [Std.HashSet.contains_toList]; exact hin : (((blocksOf env).blockRefs.get? lo).getD {}).toList.contains m = true)
  obtain ⟨j, gr', hgr', hk', hji⟩ := cov k hk
  refine ⟨k, BEq.symm hmk, ?_⟩
  rcases hji with rfl | hj
  · have e : gr = gr' := Option.some.inj (hgr.symm.trans hgr')
    subst e
    exact .inl hk'
  · exact .inr ⟨j, hj, gr', hgr', hk'⟩

/--
info: 'Ix.Cert.GroupRefs.refs_in_hard' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms refs_in_hard

end Ix.Cert.GroupRefs
