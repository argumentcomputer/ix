import Ix.Cert.SelectedRoots

/-! # The Source reverse index and its bounded worklist

This unwired layer indexes exactly the materialized logical Source edges.
Adjacency updates consume their old array inside `alter`; the walk retains
missing seeds and counts duplicate edges in its derived fuel budget. The
bound is in extracted adjacency volume. Selection is proved literally equal
to the frozen reference. Source-expression extraction costs, the streaming
graph bridge, admission and runtime wiring remain separate.
-/

namespace Ix.Cert.SourceReverse

open Ix (Name)
open SelectedRoots (logicalInput)

abbrev Index := Std.HashMap Name (Array Name)

/-- Consume the old array inside the updater, without retaining it via the map. -/
def appendAt (m : Std.HashMap Name (Array α)) (key : Name) (item : α) :
    Std.HashMap Name (Array α) :=
  m.alter key fun old => some ((old.getD #[]).push item)

theorem appendAt_lookup (m : Std.HashMap Name (Array α)) (key query : Name) (item : α) :
    (appendAt m key item).getD query #[] =
      if key == query then (m.getD key #[]).push item else m.getD query #[] := by
  simp only [appendAt, Std.HashMap.getD_eq_getD_getElem?, Std.HashMap.getElem?_alter]
  split <;> rfl

private def recStep (m : Ix.Map Name (Array (Name × Name))) (p : Name × Ix.ConstantInfo) :=
  match p.2 with
  | .recInfo rv => match rv.all[0]? with
    | some first => appendAt m first (first, p.1)
    | none => m
  | _ => m

/-- The original recursor index's arrays, built with owned updates. -/
def recursors (env : Ix.Environment) : Ix.Map Name (Array (Name × Name)) :=
  env.consts.fold (init := {}) fun m n ci => recStep m (n, ci)

private theorem recStep_lookup {m old : Ix.Map Name (Array (Name × Name))}
    (same : ∀ n, m.getD n #[] = old.getD n #[]) (p : Name × Ix.ConstantInfo) (n : Name) :
    (recStep m p).getD n #[] = (Closure.recStep old p).getD n #[] := by
  obtain ⟨k, ci⟩ := p
  cases ci with
  | recInfo rv =>
    cases h : rv.all[0]? <;>
      simp only [recStep, Closure.recStep, h, appendAt_lookup, Std.HashMap.getD_insert, same]
  | _ => exact same n

/-- Pointwise equality avoids equating hash-equivalent stored key representatives. -/
theorem recursors_lookup (env : Ix.Environment) (first : Name) :
    (recursors env).getD first #[] = (recursorsByBlock (logicalInput env)).getD first #[] := by
  have fold : ∀ (L : List (Name × Ix.ConstantInfo)) (m old : Ix.Map Name (Array (Name × Name))),
      (∀ n, m.getD n #[] = old.getD n #[]) →
      ∀ n, (L.foldl recStep m).getD n #[] = (L.foldl Closure.recStep old).getD n #[] := by
    intro L
    induction L with
    | nil => intro m old h n; exact h n
    | cons p L ih => intro m old h n; exact ih _ _ (recStep_lookup h p) n
  unfold recursors
  rw [Std.HashMap.fold_eq_foldl_toList, Closure.recursorsByBlock_eq]
  exact fold env.consts.toList {} {} (fun _ => rfl) first

theorem dependencies_eq (env : Ix.Environment) (ci : Ix.ConstantInfo) :
    dependencies (recursors env) ci = dependencies (recursorsByBlock (logicalInput env)) ci := by
  cases ci <;> simp only [dependencies]
  split <;> simp only [recursors_lookup]

private def addCaller (rs : Ix.Map Name (Array (Name × Name))) (m : Index)
    (p : Name × Ix.ConstantInfo) : Index :=
  (dependencies rs p.2).foldl (fun m d => appendAt m d p.1) m

/-- Every stored Source caller contributes its full dependency array, including
literals and grouping edges. A missing dependency still gets a reverse bucket. -/
def build (env : Ix.Environment) : Index :=
  let rs := recursors env
  env.consts.fold (init := {}) fun m n ci => addCaller rs m (n, ci)

private theorem appendAt_contains (m : Index) (key caller dependency query : Name) :
    ((appendAt m key caller).getD dependency #[]).contains query = true ↔
      (m.getD dependency #[]).contains query = true ∨
      (key == dependency) = true ∧ (query == caller) = true := by
  rw [appendAt_lookup]
  by_cases h : (key == dependency) = true
  · simp only [h, ite_true, Std.HashMap.getD_congr h, Array.contains_push, Bool.or_eq_true]
    simp
  · simp [h]

private theorem appendList_contains (ds : List Name) (m : Index) (caller dependency query : Name) :
    ((ds.foldl (fun m d => appendAt m d caller) m).getD dependency #[]).contains query = true ↔
      (m.getD dependency #[]).contains query = true ∨
      ∃ d ∈ ds, (d == dependency) = true ∧ (query == caller) = true := by
  induction ds generalizing m with
  | nil => simp
  | cons d ds ih =>
    rw [List.foldl_cons, ih, appendAt_contains]
    simp only [List.mem_cons]
    constructor
    · rintro ((old | edge) | ⟨x, hx, same⟩)
      · exact .inl old
      · exact .inr ⟨d, .inl rfl, edge⟩
      · exact .inr ⟨x, .inr hx, same⟩
    · rintro (old | ⟨x, hx, same⟩)
      · exact .inl (.inl old)
      · rcases hx with rfl | hx
        · exact .inl (.inr same)
        · exact .inr ⟨x, hx, same⟩

private theorem addCaller_contains (rs : Ix.Map Name (Array (Name × Name)))
    (m : Index) (p : Name × Ix.ConstantInfo) (dependency query : Name) :
    ((addCaller rs m p).getD dependency #[]).contains query = true ↔
      (m.getD dependency #[]).contains query = true ∨
      ∃ d ∈ dependencies rs p.2, (d == dependency) = true ∧ (query == p.1) = true := by
  unfold addCaller
  rw [← Array.foldl_toList, appendList_contains]
  simp only [Array.mem_toList_iff]

private theorem buildList_contains (rs : Ix.Map Name (Array (Name × Name)))
    (L : List (Name × Ix.ConstantInfo)) (m : Index) (dependency query : Name) :
    ((L.foldl (addCaller rs) m).getD dependency #[]).contains query = true ↔
      (m.getD dependency #[]).contains query = true ∨
      ∃ p ∈ L, ∃ d ∈ dependencies rs p.2,
        (d == dependency) = true ∧ (query == p.1) = true := by
  induction L generalizing m with
  | nil => simp
  | cons p L ih =>
    rw [List.foldl_cons, ih, addCaller_contains]
    simp only [List.mem_cons]
    constructor
    · rintro ((old | edge) | ⟨x, hx, edge⟩)
      · exact .inl old
      · exact .inr ⟨p, .inl rfl, edge⟩
      · exact .inr ⟨x, .inr hx, edge⟩
    · rintro (old | ⟨x, hx, edge⟩)
      · exact .inl (.inl old)
      · rcases hx with rfl | hx
        · exact .inl (.inr edge)
        · exact .inr ⟨x, hx, edge⟩

/-- Exact Source reverse edges; neither endpoint is assumed grounded. -/
theorem build_contains_iff (env : Ix.Environment) (dependency caller : Name) :
    ((build env).getD dependency #[]).contains caller = true ↔
      DependsOn (logicalInput env) caller dependency := by
  unfold build
  rw [Std.HashMap.fold_eq_foldl_toList]
  change ((env.consts.toList.foldl (addCaller (recursors env)) {}).getD dependency #[]).contains caller = true ↔ _
  rw [buildList_contains]
  simp only [Std.HashMap.getD_empty, Array.contains_empty, Bool.false_eq_true, false_or]
  constructor
  · rintro ⟨⟨n, ci⟩, stored, d, hd, sameD, sameN⟩
    have got : (logicalInput env).consts.get? caller = some ci := by
      rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_congr sameN]
      exact Closure.get?_of_mem_toList stored
    rw [dependencies_eq] at hd
    exact Closure.dependsOn_congr (Closure.dependencies_sound got hd) sameD
  · intro edge
    obtain ⟨ci, got, rest⟩ := edge
    obtain ⟨n, sameN, stored⟩ := Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList.mp got
    obtain ⟨d, hd, sameD⟩ := Closure.dependencies_complete got ⟨ci, got, rest⟩
    refine ⟨(n, ci), stored, d, ?_, BEq.symm sameD, sameN⟩
    rw [dependencies_eq]
    exact hd

structure State where
  seen : Std.HashSet Name
  pending : List Name

/-- Mark on pop: even an absent index key is marked, with no predecessors. -/
def step (index : Index) (s : State) : State :=
  match s.pending with
  | [] => s
  | n :: todo =>
    if s.seen.contains n then ⟨s.seen, todo⟩
    else ⟨s.seen.insert n, (index.getD n #[]).toList ++ todo⟩

def walkFuel (index : Index) : Nat → State → State
  | 0, s => s
  | fuel + 1, s => match s.pending with
    | [] => s
    | _ :: _ => walkFuel index fuel (step index s)

/-- All extracted adjacency entries count, including repeated edges. -/
def edgeCount (index : Index) : Nat := (index.toList.map (·.2.size)).sum

def budget (index : Index) (seeds : Std.HashSet Name) : Nat :=
  edgeCount index + seeds.toList.length

def walk (index : Index) (seeds : Std.HashSet Name) : State :=
  walkFuel index (budget index seeds) ⟨{}, seeds.toList⟩

private def weight (seen : Std.HashSet Name) (p : Name × Array Name) : Nat :=
  if seen.contains p.1 then 0 else p.2.size

private def mass (seen : Std.HashSet Name) (entries : List (Name × Array Name)) : Nat :=
  (entries.map (weight seen)).sum

private def potential (index : Index) (s : State) : Nat :=
  s.pending.length + mass s.seen index.toList

private theorem weight_insert_le (seen : Std.HashSet Name) (n : Name) (p : Name × Array Name) :
    weight (seen.insert n) p ≤ weight seen p := by
  simp only [weight, Std.HashSet.contains_insert]
  cases seen.contains p.1 <;> cases n == p.1 <;> simp

private theorem mass_insert_le (seen : Std.HashSet Name) (n : Name)
    (entries : List (Name × Array Name)) : mass (seen.insert n) entries ≤ mass seen entries := by
  induction entries with
  | nil => simp [mass]
  | cons p entries ih =>
    have := weight_insert_le seen n p
    simp only [mass, List.map_cons, List.sum_cons] at *
    omega

/-- A queried bucket's whole weight is removed, also when its stored name is
only hash-equivalent. Other removed weight can only improve the bound. -/
private theorem mass_insert_drop (seen : Std.HashSet Name) (n k : Name) (ds : Array Name)
    (entries : List (Name × Array Name)) (stored : (k, ds) ∈ entries)
    (same : (n == k) = true) (fresh : seen.contains n = false) :
    mass (seen.insert n) entries + ds.size ≤ mass seen entries := by
  induction entries with
  | nil => cases stored
  | cons p entries ih =>
    rcases List.mem_cons.mp stored with rfl | stored
    · have hk : seen.contains k = false := by
        rw [← Std.HashSet.contains_congr same]; exact fresh
      have tail := mass_insert_le seen n entries
      simp only [mass, List.map_cons, List.sum_cons] at *
      simp only [weight, Std.HashSet.contains_insert, same, Bool.true_or, ite_true,
        hk, Bool.false_eq_true, ite_false]
      omega
    · have tail := ih stored
      have head := weight_insert_le seen n p
      simp only [mass, List.map_cons, List.sum_cons] at *
      omega

private theorem step_decreases (index : Index) (s : State) (nonempty : s.pending ≠ []) :
    potential index (step index s) < potential index s := by
  obtain ⟨seen, pending⟩ := s
  cases pending with
  | nil => exact False.elim (nonempty rfl)
  | cons n todo =>
    cases hseen : seen.contains n with
    | true => simp [step, hseen, potential]
    | false =>
      cases hlookup : index[n]? with
      | none =>
        have smaller := mass_insert_le seen n index.toList
        simp only [step, hseen, Bool.false_eq_true, ite_false,
          Std.HashMap.getD_eq_getD_getElem?, hlookup, Option.getD_none,
          Array.toList_empty, List.nil_append, potential, List.length_cons]
        omega
      | some ds =>
        obtain ⟨k, same, stored⟩ := Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList.mp hlookup
        have smaller := mass_insert_drop seen n k ds index.toList stored same hseen
        simp only [step, hseen, Bool.false_eq_true, ite_false,
          Std.HashMap.getD_eq_getD_getElem?, hlookup, Option.getD_some,
          potential, List.length_append, Array.length_toList, List.length_cons]
        omega

private theorem walkFuel_complete (index : Index) (fuel : Nat) (s : State)
    (enough : potential index s ≤ fuel) : (walkFuel index fuel s).pending = [] := by
  induction fuel generalizing s with
  | zero =>
    simp only [walkFuel]
    apply List.eq_nil_of_length_eq_zero
    unfold potential at enough
    omega
  | succ fuel ih =>
    cases hp : s.pending with
    | nil => simp [walkFuel, hp]
    | cons n todo =>
      have smaller := step_decreases index s (by simp [hp])
      have next : potential index (step index s) ≤ fuel := by omega
      simpa only [walkFuel, hp] using ih (step index s) next

/-- The derived budget always consumes the pending tail. No fuel sufficiency,
grounding, acyclicity, edge uniqueness or hash injectivity is an input premise. -/
theorem walk_pending_empty (index : Index) (seeds : Std.HashSet Name) :
    (walk index seeds).pending = [] := by
  apply walkFuel_complete
  have emptyWeight : weight ({} : Std.HashSet Name) = (fun p : Name × Array Name => p.2.size) := by
    funext p
    simp [weight]
  simp [potential, mass, emptyWeight, budget, edgeCount, Nat.add_comm]

/-- Reverse reachability includes every seed, even one absent from the index. -/
inductive BackReach (index : Index) (seeds : Std.HashSet Name) : Name → Prop
  | seed {n} : seeds.contains n = true → BackReach index seeds n
  | step {dependency caller} : BackReach index seeds dependency →
      (index.getD dependency #[]).contains caller = true → BackReach index seeds caller

theorem backReach_congr {index seeds n n'} (reached : BackReach index seeds n)
    (same : (n == n') = true) : BackReach index seeds n' := by
  cases reached with
  | seed h => exact .seed (by rw [← Std.HashSet.contains_congr same]; exact h)
  | step h edge => exact .step h (Closure.array_contains_of_beq same edge)

private def Pending (s : State) (n : Name) : Prop :=
  s.seen.contains n = true ∨ s.pending.contains n = true

private theorem pending_step (index : Index) (s : State) (n : Name)
    (h : Pending s n) : Pending (step index s) n := by
  obtain ⟨seen, pending⟩ := s
  cases pending with
  | nil => exact h
  | cons top todo =>
    rcases h with marked | queued
    · cases hs : seen.contains top <;> simp [Pending, step, hs, Std.HashSet.contains_insert, marked]
    · simp only [List.contains_cons, Bool.or_eq_true] at queued
      rcases queued with same | queued
      · cases hs : seen.contains top with
        | false => simp [Pending, step, hs, Std.HashSet.contains_insert, BEq.symm same]
        | true =>
          have hn := (Std.HashSet.contains_congr (m := seen) (BEq.symm same)).symm.trans hs
          exact .inl (by simpa [step, hs] using hn)
      · cases hs : seen.contains top <;> simp [Pending, step, hs, List.contains_append, queued]

private structure Inv (index : Index) (seeds : Std.HashSet Name) (s : State) : Prop where
  sound : ∀ n, Pending s n → BackReach index seeds n
  roots : ∀ n, seeds.contains n = true → Pending s n
  closed : ∀ d, s.seen.contains d = true → ∀ n,
    (index.getD d #[]).contains n = true → Pending s n

private theorem inv_step {index seeds s} (inv : Inv index seeds s) :
    Inv index seeds (step index s) := by
  obtain ⟨seen, pending⟩ := s
  cases pending with
  | nil => exact inv
  | cons top todo =>
    have reached : BackReach index seeds top := inv.sound top (.inr (by simp))
    refine ⟨?_, fun n h => pending_step index _ n (inv.roots n h), ?_⟩
    · intro n hn
      cases hs : seen.contains top with
      | true =>
        rcases hn with marked | queued
        · exact inv.sound n (.inl (by simpa [step, hs] using marked))
        · have tail : todo.contains n = true := by simpa [step, hs] using queued
          exact inv.sound n (.inr (by simp [tail]))
      | false =>
        rcases hn with marked | queued
        · simp only [step, hs, Bool.false_eq_true, ite_false, Std.HashSet.contains_insert,
            Bool.or_eq_true] at marked
          rcases marked with same | old
          · exact backReach_congr reached same
          · exact inv.sound n (.inl old)
        · simp only [step, hs, Bool.false_eq_true, ite_false, List.contains_append,
            Array.contains_toList, Bool.or_eq_true] at queued
          rcases queued with edge | old
          · exact .step reached edge
          · exact inv.sound n (.inr (by simp [old]))
    · intro d marked n edge
      cases hs : seen.contains top with
      | true =>
        exact pending_step index _ n (inv.closed d (by simpa [step, hs] using marked) n edge)
      | false =>
        simp only [step, hs, Bool.false_eq_true, ite_false, Std.HashSet.contains_insert,
          Bool.or_eq_true] at marked
        rcases marked with same | old
        · have edgeTop : (index.getD top #[]).contains n = true := by
            rw [Std.HashMap.getD_congr same]; exact edge
          exact .inr (by simp [step, hs, List.contains_append, Array.contains_toList, edgeTop])
        · exact pending_step index _ n (inv.closed d old n edge)

private theorem inv_walkFuel {index seeds} (fuel : Nat) (s : State) (inv : Inv index seeds s) :
    Inv index seeds (walkFuel index fuel s) := by
  induction fuel generalizing s with
  | zero => exact inv
  | succ fuel ih =>
    cases hp : s.pending with
    | nil => simpa only [walkFuel, hp] using inv
    | cons n todo => simpa only [walkFuel, hp] using ih (step index s) (inv_step inv)

theorem walk_contains_iff (index : Index) (seeds : Std.HashSet Name) (n : Name) :
    (walk index seeds).seen.contains n = true ↔ BackReach index seeds n := by
  have initial : Inv index seeds ⟨{}, seeds.toList⟩ := by
    constructor
    · intro n h
      exact .seed (by simpa [Pending, Std.HashSet.contains_toList] using h)
    · intro n h; exact .inr (by simpa using h)
    · intro d h; simp at h
  have inv := inv_walkFuel (budget index seeds) _ initial
  change Inv index seeds (walk index seeds) at inv
  have done : ∀ n, Pending (walk index seeds) n → (walk index seeds).seen.contains n = true := by
    intro n h
    simpa [Pending, walk_pending_empty] using h
  constructor
  · intro h; exact inv.sound n (.inl h)
  · intro reached
    induction reached with
    | seed h => exact done _ (inv.roots _ h)
    | step _ edge ih => exact done _ (inv.closed _ ih _ edge)

private theorem reaches_from {env roots a b} (start : Reaches env roots a)
    (path : Reaches env [a] b) : Reaches env roots b := by
  induction path with
  | root h => exact Closure.reaches_congr start (BEq.symm (by simpa using h))
  | step _ edge ih => exact .step ih edge

private theorem back_of_reaches (env : Ix.Environment) (cs : Ix.Compile.ChangedSet.ChangedSet)
    {a b : Name} (path : Reaches (logicalInput env) [a] b) :
    BackReach (build env) cs.names b → BackReach (build env) cs.names a := by
  induction path with
  | root h => intro back; exact backReach_congr back (by simpa using h)
  | step _ edge ih => intro back; exact ih (.step back ((build_contains_iff ..).mpr edge))

theorem backReach_iff_affected (env : Ix.Environment) (cs : Ix.Compile.ChangedSet.ChangedSet) (n : Name) :
    BackReach (build env) cs.names n ↔ SelectedRoots.AffectedName env cs n := by
  constructor
  · intro reached
    induction reached with
    | @seed n changed => exact ⟨n, .root (by simp), changed⟩
    | @step d n _ edge ih =>
      obtain ⟨m, path, changed⟩ := ih
      exact ⟨m, reaches_from (.step (.root (by simp)) ((build_contains_iff ..).mp edge)) path, changed⟩
  · rintro ⟨m, path, changed⟩
    exact back_of_reaches env cs path (.seed changed)

def affectedNames (env : Ix.Environment) (cs : Ix.Compile.ChangedSet.ChangedSet) : Std.HashSet Name :=
  (walk (build env) cs.names).seen

theorem affectedNames_iff (env : Ix.Environment) (cs : Ix.Compile.ChangedSet.ChangedSet) (n : Name) :
    (affectedNames env cs).contains n = true ↔ SelectedRoots.AffectedName env cs n := by
  exact (walk_contains_iff ..).trans (backReach_iff_affected ..)

theorem affectedNames_contains_eq (env : Ix.Environment) (cs : Ix.Compile.ChangedSet.ChangedSet) (n : Name) :
    (affectedNames env cs).contains n = SelectedRoots.affected env cs n := by
  apply Bool.eq_iff_iff.mpr
  rw [affectedNames_iff, SelectedRoots.affected_iff]

/-- Unwired selection computes the reverse cone once. Direct and observed-row
enumeration, publication order and reason multiplicity are the reference's. -/
def select (env : Ix.Environment) (cs : Ix.Compile.ChangedSet.ChangedSet) (sub : Ix.Environment)
    (ixe : Ixon.Env) : List SelectedRoots.Root :=
  let affected := affectedNames env cs
  SelectedRoots.directRoots cs sub ixe ++
    (sub.consts.toList.filterMap fun (n, _) =>
      if cs.contains n = false ∧ affected.contains n = true then
        (SelectedRoots.published? sub ixe n).map fun a => ⟨n, a, .cascade⟩
      else none) ++ SelectedRoots.rowRoots cs sub ixe

/-- Literal list equality, stronger than address coverage or permutation. -/
theorem select_eq (env : Ix.Environment) (cs : Ix.Compile.ChangedSet.ChangedSet)
    (sub : Ix.Environment) (ixe : Ixon.Env) :
    select env cs sub ixe = SelectedRoots.select env cs sub ixe := by
  simp only [select, SelectedRoots.select, SelectedRoots.cascadeRoots, affectedNames_contains_eq]

theorem select_sound {env cs sub ixe r} (h : r ∈ select env cs sub ixe) :
    SelectedRoots.ClassifiedRoot env cs sub ixe r :=
  SelectedRoots.select_sound (by simpa only [select_eq] using h)

theorem select_complete {env cs sub ixe a reason}
    (h : ∃ n, SelectedRoots.ClassifiedRoot env cs sub ixe ⟨n, a, reason⟩) :
    ∃ r ∈ select env cs sub ixe, r.address = a ∧ r.reason = reason := by
  simpa only [select_eq] using SelectedRoots.select_complete h

/-- Coverage uses the actual classifier's proved names/entries correspondence. -/
theorem required_covered_ofCompile {env condensed table sub ixe a}
    (h : SelectedRoots.RequiredRoot env
      (Ix.Compile.ChangedSet.ofCompile (logicalInput env) condensed table ixe) sub ixe a) :
    ∃ r ∈ select env (Ix.Compile.ChangedSet.ofCompile (logicalInput env) condensed table ixe) sub ixe,
      r.address = a := by
  simpa only [select_eq] using SelectedRoots.required_covered_ofCompile h

theorem selected_input_required_ofCompile {env condensed table sub ixe r}
    (h : r ∈ select env (Ix.Compile.ChangedSet.ofCompile (logicalInput env) condensed table ixe) sub ixe)
    (input : r.reason ≠ .row) :
    SelectedRoots.RequiredRoot env
      (Ix.Compile.ChangedSet.ofCompile (logicalInput env) condensed table ixe) sub ixe r.address :=
  SelectedRoots.selected_input_required_ofCompile
    (by simpa only [SelectedRoots.selectCompile, select_eq] using h) input

end Ix.Cert.SourceReverse
