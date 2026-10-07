import Ix.CompileCert.Canon.Loop
import Ix.CompileCert.Canon.Coarsest
import Ix.CompileCert.Canon.Seed
import Ix.CompileCert.Canon.SeedFree
import Ix.CompileCert.Canon.Terminate
import Ix.CompileCert.Canon.BlockComp
import Ix.Compile.Canon.Clique

/-!
# M7 L1, the clique classes and the statement order

`Ix.Compile.Canon.cliqueClasses rules addr? c` is `sortClasses` over the clique's
specifications (`CliqueMember.toMutConst`: each member as a definition whose value is its
specification's value, applied to the literal `recArgPos` when that position is pinned) followed by
`classNames` (`cliqueClasses_eq`). A specification is a definition, so its keys are its name
alone (`keysOf_toMutConst`), and the hypothesis every refinement theorem needs (`KeysDistinct`)
is that the members' names are pairwise distinct under `==` (`cliqueKeys`). Clique order is
then (Theorem 4.2, "clique order as defined"; design document §2.7, M.3):

* the coarsest consistent partition of the specifications (`cliqueClasses_coarsest`);
* returned whenever no comparison of two distinct specifications fails (`cliqueClasses_ok`);
* the same for every order of the members under the compiler's name-hash seed, classes, order and
  representatives (`cliqueClasses_perm`), and, for any seed, the same classes in the same order
  (`cliqueClasses_setEq`).

`Ix.Compile.Canon.statementOrder` (Q6, the order of a theorem clique by its statements): when it
returns `some σ`, `σ` is a permutation of the positions `0, …, n-1` (`statementOrder_perm`), the
canonical position of Lean's `i`-th member at index `i` (`statementOrder_spec`).
-/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon
open Ix (Name MutConst)

/-- The specifications the clique comparator sorts, in Lean's order. -/
def cliqueSpecs (c : Clique) : List MutConst := c.members.toList.map (·.toMutConst)

/-- The members' names are pairwise distinct under `==`. -/
def CliqueNamesDistinct (c : Clique) : Prop :=
  (c.members.toList.map (·.name)).Pairwise (fun a b => (a == b) = false)

/-- `cliqueClasses` is `sortClasses` over the specifications, then the class names. -/
theorem cliqueClasses_eq (rules : Rules) (addr? : Name → Option Address) (c : Clique) :
    cliqueClasses rules addr? c =
      (fun r => (classNames r.1, r.2)) <$> sortClasses rules addr? (cliqueSpecs c) := by
  unfold cliqueClasses cliqueSpecs
  cases sortClasses rules addr? (c.members.toList.map (·.toMutConst)) with
  | error e => rfl
  | ok r => obtain ⟨a, b⟩ := r; rfl

theorem cliqueClasses_ok_iff {rules : Rules} {addr? : Name → Option Address} {c : Clique}
    {cls : Array (Array Name)} {st : SortStats} :
    cliqueClasses rules addr? c = .ok (cls, st) ↔
      ∃ F, sortClasses rules addr? (cliqueSpecs c) = .ok (F, st) ∧ cls = classNames F := by
  rw [cliqueClasses_eq]
  constructor
  · intro h
    obtain ⟨⟨F, st'⟩, hF, e⟩ := except_map_ok h
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact ⟨F, hF, rfl⟩
  · rintro ⟨F, hF, rfl⟩
    rw [hF]; rfl

/-- A specification is a definition: its only key is its name. -/
theorem keysOf_toMutConst (m : CliqueMember) : keysOf m.toMutConst = [m.name] := by
  unfold CliqueMember.toMutConst keysOf
  rfl

theorem cliqueSpecs_keys (c : Clique) :
    (cliqueSpecs c).flatMap keysOf = c.members.toList.map (·.name) := by
  unfold cliqueSpecs
  induction c.members.toList with
  | nil => rfl
  | cons m l ih => rw [List.map_cons, List.flatMap_cons, keysOf_toMutConst, ih]; rfl

/-- Distinct names give distinct keys. -/
theorem cliqueKeys {c : Clique} (h : CliqueNamesDistinct c) : KeysDistinct (cliqueSpecs c) := by
  unfold KeysDistinct
  rw [cliqueSpecs_keys]
  exact h

/-- **Clique order is the coarsest consistent partition of the specifications** (design document
§2.7, M.3: §2.2–§2.3 applied to specifications). -/
theorem cliqueClasses_coarsest {rules : Rules} (hpf : rules.portFixes = true)
    {addr? : Name → Option Address} (hA : AddrCongr addr?) {c : Clique} (hn : CliqueNamesDistinct c)
    {cls : Array (Array Name)} {st : SortStats} (h : cliqueClasses rules addr? c = .ok (cls, st)) :
    ∃ F, sortClasses rules addr? (cliqueSpecs c) = .ok (F, st) ∧ cls = classNames F ∧
      Partition F (cliqueSpecs c) ∧ Consistent rules addr? F ∧ Coarsest rules addr? (cliqueSpecs c) F := by
  obtain ⟨F, hF, rfl⟩ := cliqueClasses_ok_iff.1 h
  exact ⟨F, hF, rfl, sortClasses_coarsest hpf hA (cliqueKeys hn) hF⟩

/-- **The clique classes are computed** when no comparison of two distinct specifications fails. -/
theorem cliqueClasses_ok {rules : Rules} (hpf : rules.portFixes = true)
    {addr? : Name → Option Address} (hA : AddrCongr addr?) {c : Clique} (hn : CliqueNamesDistinct c)
    (hok : ∀ (ctx : Ix.MutCtx), ∀ a ∈ cliqueSpecs c, ∀ b ∈ cliqueSpecs c, a ≠ b →
      ∃ o, constOrd rules addr? ctx a b = .ok o) :
    ∃ cls st, cliqueClasses rules addr? c = .ok (cls, st) := by
  obtain ⟨F, st, hF⟩ := sortClasses_ok hA hok hpf (cliqueKeys hn)
  exact ⟨classNames F, st, cliqueClasses_ok_iff.2 ⟨F, hF, rfl⟩⟩

/-- **Clique order does not depend on Lean's member order** (Def 4.3 for cliques, permutation):
under the compiler's name-hash seed, a clique with the same members in another order has the same
classes, order, representatives and statistics. -/
theorem cliqueClasses_perm {rules : Rules} (hseed : rules.seed = .byNameHash)
    (addr? : Name → Option Address) {c c' : Clique} (hp : c.members.toList.Perm c'.members.toList)
    (hn : CliqueNamesDistinct c) :
    cliqueClasses rules addr? c = cliqueClasses rules addr? c' := by
  have hp' : (cliqueSpecs c).Perm (cliqueSpecs c') := hp.map _
  rw [cliqueClasses_eq, cliqueClasses_eq, sortClasses_perm hseed addr? hp' (cliqueKeys hn)]

/-- **For any seed, the clique's classes and their order do not depend on the seed or Lean's
member order**: only the order inside a class (the representative) can change. -/
theorem cliqueClasses_setEq {r₁ r₂ : Rules} (hpf₁ : r₁.portFixes = true) (hpf₂ : r₂.portFixes = true)
    (hl : r₁.levels = r₂.levels) (ht : r₁.tieBreak = r₂.tieBreak) {addr? : Name → Option Address}
    (hA : AddrCongr addr?) {c c' : Clique} (hp : c.members.toList.Perm c'.members.toList)
    (hn : CliqueNamesDistinct c) {cls : Array (Array Name)} {st : SortStats}
    (h : cliqueClasses r₁ addr? c = .ok (cls, st)) :
    ∃ F F' cls' st', sortClasses r₁ addr? (cliqueSpecs c) = .ok (F, st) ∧ cls = classNames F ∧
      cliqueClasses r₂ addr? c' = .ok (cls', st') ∧
      sortClasses r₂ addr? (cliqueSpecs c') = .ok (F', st') ∧ cls' = classNames F' ∧ SetEq F F' := by
  obtain ⟨F, hF, rfl⟩ := cliqueClasses_ok_iff.1 h
  have hp' : (cliqueSpecs c).Perm (cliqueSpecs c') := hp.map _
  obtain ⟨F', st', hF', hs⟩ := sortClasses_setEq hpf₁ hpf₂ hl ht hA hp' (cliqueKeys hn) hF
  exact ⟨F, F', classNames F', st', hF, rfl, cliqueClasses_ok_iff.2 ⟨F', hF', rfl⟩, hF', rfl, hs⟩

/-! ## The statement order of a theorem clique (Q6) -/

/-- The clique `statementOrder` sorts: each statement as its own value, no pinned position. -/
def statementClique (members : Array CliqueMember) : Clique :=
  { kind := .noSpec, members := members.map fun m => { m with value := m.type, recArgPos := none } }

theorem flatten_singletons {α : Type} :
    ∀ (F : List (List α)), (∀ C ∈ F, C.length = 1) → F = F.flatten.map (fun r => [r])
  | [], _ => rfl
  | C :: F, h => by
    have ih := flatten_singletons F (fun C hC => h C (List.mem_cons_of_mem _ hC))
    match C, h C (List.mem_cons_self ..) with
    | [r], _ => rw [List.flatten_cons, List.map_append, ← ih]; rfl

theorem classNames_singletons : ∀ (F : List (List MutConst)), (∀ C ∈ F, C.length = 1) →
    (classNames F).toList = (F.flatten.map MutConst.name).map (fun n => #[n])
  | [], _ => by simp [classNames]
  | C :: F, h => by
    have ih := classNames_singletons F (fun C hC => h C (List.mem_cons_of_mem _ hC))
    match C, h C (List.mem_cons_self ..) with
    | [r], _ =>
      unfold classNames at ih ⊢
      simp only [Array.toList_map] at ih ⊢
      rw [List.map_cons, ih]
      simp [List.flatten_cons]

/-- Two positions of a list of pairwise distinct names holding `==` names are one position. -/
theorem pairwise_nbeq_index {L : List Name} (h : L.Pairwise (fun a b => (a == b) = false))
    {i j : Nat} {a b : Name} (ha : L[i]? = some a) (hb : L[j]? = some b) (hab : (a == b) = true) :
    i = j := by
  have hi : i < L.length := by
    rcases Nat.lt_or_ge i L.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at ha; cases ha
  have hj : j < L.length := by
    rcases Nat.lt_or_ge j L.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hb; cases hb
  rw [List.getElem?_eq_getElem hi, Option.some.injEq] at ha
  rw [List.getElem?_eq_getElem hj, Option.some.injEq] at hb
  subst ha hb
  rcases Nat.lt_trichotomy i j with hl | rfl | hl
  · have := List.pairwise_iff_getElem.1 h i j hi hj hl
    rw [hab] at this; cases this
  · rfl
  · have := List.pairwise_iff_getElem.1 h j i hj hi hl
    rw [name_beq_symm hab] at this; cases this

theorem findIdx_singletons {names : List Name} (hd : names.Pairwise (fun a b => (a == b) = false))
    {x : Name} {k : Nat} (hk : names[k]? = some x) :
    ((names.map (fun n => #[n])).toArray.findIdx? (fun c => c.contains x)) = some k := by
  have hkl : k < names.length := by
    rcases Nat.lt_or_ge k names.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hk; cases hk
  rw [Array.findIdx?_eq_some_iff_getElem]
  refine ⟨by simp [hkl], ?_, ?_⟩
  · simp only [List.getElem_toArray, List.getElem_map]
    rw [List.getElem?_eq_getElem hkl, Option.some.injEq] at hk
    simp [Array.contains, hk]
  · intro j hjk hp
    simp only [List.getElem_toArray, List.getElem_map] at hp
    have hjl : j < names.length := by omega
    have hp' : (x == names[j]) = true := by simpa [Array.contains] using hp
    have := pairwise_nbeq_index hd hk (List.getElem?_eq_getElem hjl) hp'
    omega

/-- **The statement order is a permutation** (Q6): when `statementOrder` returns `σ`, every class
of the statement clique is one member, `σ[i]` is the position of the class of Lean's `i`-th
member, and `σ` maps the positions `0, …, n-1` one to one onto themselves. -/
theorem statementOrder_spec {rules : Rules} (hpf : rules.portFixes = true)
    {addr? : Name → Option Address} (hA : AddrCongr addr?) {members : Array CliqueMember}
    (hn : (members.toList.map (·.name)).Pairwise (fun a b => (a == b) = false))
    {σ : Array Nat} (h : statementOrder rules addr? members = .ok (some σ)) :
    ∃ F st, cliqueClasses rules addr? (statementClique members) = .ok (classNames F, st) ∧
      Partition F (cliqueSpecs (statementClique members)) ∧ (∀ C ∈ F, C.length = 1) ∧
      σ.size = members.size ∧
      (∀ (i : Nat) (m : CliqueMember) (j : Nat), members[i]? = some m → σ[i]? = some j →
        ∃ r, F[j]? = some [r] ∧ r.name = m.name) ∧
      (∀ (i i' j : Nat), σ[i]? = some j → σ[i']? = some j → i = i') ∧
      (∀ j, j < members.size → ∃ i : Nat, σ[i]? = some j) := by
  have hnames : CliqueNamesDistinct (statementClique members) := by
    unfold CliqueNamesDistinct statementClique
    simp only [Array.toList_map, List.map_map]
    exact hn
  unfold statementOrder at h
  dsimp only at h
  obtain ⟨⟨cls, st⟩, hc, h⟩ := except_bind_ok.1 h
  dsimp only at h
  split at h
  · cases except_pure_ok h
  · rename_i hany
    have hσ := except_pure_ok h
    simp only [Option.some.injEq] at hσ
    obtain ⟨F, hF, rfl, hpart, -, -⟩ := cliqueClasses_coarsest hpf hA hnames hc
    -- every class is one member
    have hsing : ∀ C ∈ F, C.length = 1 := by
      intro C hC
      have hne : C ≠ [] := hpart.2 C hC
      have hlt : ¬ C.length ≥ 2 := by
        intro hge
        apply hany
        rw [← Array.any_toList]
        unfold classNames
        rw [List.any_eq_true]
        refine ⟨C.toArray.map (·.name), ?_, by simpa using hge⟩
        simp only [Array.toList_map]
        exact List.mem_map_of_mem hC
      cases C with
      | nil => exact absurd rfl hne
      | cons a l => cases l with
        | nil => rfl
        | cons b l => exact absurd (by simp) hlt
    have hF1 := flatten_singletons F hsing
    -- the names of the classes, in order
    let R := F.flatten
    have hRp : R.Perm (cliqueSpecs (statementClique members)) := hpart.1
    have hspecs : (cliqueSpecs (statementClique members)).map MutConst.name = members.toList.map (·.name) := by
      unfold cliqueSpecs statementClique
      simp only [Array.toList_map, List.map_map]
      apply List.map_congr_left
      intro m _
      rfl
    have hNp : (R.map MutConst.name).Perm (members.toList.map (·.name)) := by
      rw [← hspecs]; exact hRp.map _
    have hNd : (R.map MutConst.name).Pairwise (fun a b => (a == b) = false) :=
      pairwise_nbeq_perm hNp.symm hn
    have hcls : classNames F = ((R.map MutConst.name).map (fun n => #[n])).toArray := by
      apply Array.ext'
      rw [classNames_singletons F hsing, List.toList_toArray]
    have hRlen : R.length = members.size := by
      have := hNp.length_eq; simpa using this
    -- σ, position by position
    have hσi : ∀ (i : Nat) (m : CliqueMember), members[i]? = some m → ∃ k, σ[i]? = some k ∧ (R.map MutConst.name)[k]? = some m.name := by
      intro i m hm
      have hmem : m.name ∈ R.map MutConst.name := by
        apply hNp.symm.subset
        exact List.mem_map_of_mem (List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hm))
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hmem
      refine ⟨k, ?_, hk⟩
      rw [← hσ, Array.getElem?_map, Array.getElem?_map, hm]
      simp only [Option.map_some]
      rw [hcls, findIdx_singletons hNd hk]
      rfl
    have hFk : ∀ (k : Nat) (x : Name), (R.map MutConst.name)[k]? = some x →
        ∃ r : MutConst, F[k]? = some [r] ∧ r.name = x := by
      intro k x hk
      rw [List.getElem?_map, Option.map_eq_some_iff] at hk
      obtain ⟨r, hr, rfl⟩ := hk
      refine ⟨r, ?_, rfl⟩
      rw [hF1, List.getElem?_map, hr]; rfl
    have hσnone : ∀ i : Nat, members[i]? = none → σ[i]? = none := by
      intro i hq
      rw [← hσ, Array.getElem?_map, Array.getElem?_map, hq]; rfl
    refine ⟨F, st, hc, hpart, hsing, by rw [← hσ]; simp, ?_, ?_, ?_⟩
    · intro i m j hm hj
      obtain ⟨k, hk, hkn⟩ := hσi i m hm
      rw [hk, Option.some.injEq] at hj
      subst hj
      exact hFk _ _ hkn
    · intro i i' j hi hi'
      have hm : ∃ m : CliqueMember, members[i]? = some m := by
        cases hq : members[i]? with
        | none => rw [hσnone i hq] at hi; cases hi
        | some m => exact ⟨m, rfl⟩
      have hm' : ∃ m : CliqueMember, members[i']? = some m := by
        cases hq : members[i']? with
        | none => rw [hσnone i' hq] at hi'; cases hi'
        | some m => exact ⟨m, rfl⟩
      obtain ⟨m, hm⟩ := hm
      obtain ⟨m', hm'⟩ := hm'
      obtain ⟨k, hk, hkn⟩ := hσi i m hm
      obtain ⟨k', hk', hkn'⟩ := hσi i' m' hm'
      rw [hk] at hi; cases hi
      rw [hk'] at hi'; cases hi'
      rw [hkn] at hkn'
      simp only [Option.some.injEq] at hkn'
      have h1 : (members.toList.map (·.name))[i]? = some m.name := by
        rw [List.getElem?_map, Array.getElem?_toList, hm]; rfl
      have h2 : (members.toList.map (·.name))[i']? = some m'.name := by
        rw [List.getElem?_map, Array.getElem?_toList, hm']; rfl
      exact pairwise_nbeq_index hn h1 h2 (by rw [hkn']; exact name_beq_refl _)
    · intro j hj
      have hjl : j < (R.map MutConst.name).length := by simp [hRlen, hj]
      have hy := List.getElem?_eq_getElem hjl
      have hmem : (R.map MutConst.name)[j] ∈ members.toList.map (·.name) :=
        hNp.subset (List.getElem_mem hjl)
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hmem
      rw [List.getElem?_map, Option.map_eq_some_iff] at hi
      obtain ⟨m, hm, hmn⟩ := hi
      rw [Array.getElem?_toList] at hm
      obtain ⟨k, hk, hkn⟩ := hσi i m hm
      refine ⟨i, ?_⟩
      rw [hk]
      congr 1
      rw [hmn] at hkn
      exact pairwise_nbeq_index hNd hkn hy (name_beq_refl _)

end Ix.CompileCert.Canon
