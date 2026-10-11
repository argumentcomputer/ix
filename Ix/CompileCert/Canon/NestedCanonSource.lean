import Ix.CompileCert.Canon.CanonBlockSource

/-!
# M7 L1, a component's nested auxiliaries over the canonical block

`Ix.Compile.Canon.componentNested rules env all classes` expands the component's canonical block
(`canonExpand`: the class representatives in canonical order, every other member of a class
renamed to its representative, external groups as `env.groupOf` opens them, occurrences
deduplicated up to compiled addresses under the discovery rule), orders the auxiliaries
(`canonicalAuxOrder`), takes their signatures (`sigsInOrder`), expands Lean's source block `all`
and maps each of Lean's positions to a canonical one (`computePerm`). Under the compiler's rules
(`Rules.compiler = Rules.phaseA`, `nested := .discovery`):

* `canonicalAuxOrder` is the identity on the expansion (`canonicalAuxOrder_discovery`), so the
  canonical auxiliaries are **those of the canonical expansion, in its discovery order**, one per
  class, and the signatures are theirs, in that order (`componentNested_source_some`,
  `sigsInOrder_discovery`; design document §2.5, "discovery order over the canonical block");
* no component's order needs addresses (`addrDecided = false`);
* the canonical part of the nested data, its classes and signatures (`canonAux`), is a function of
  the component's classes alone: it does not depend on the presentation `all`
  (`componentNested_canonAux`). With `CanonBlock.lean`'s theorems, the canonical nested
  auxiliaries are the same under member reorder (`canonBlock_source_member_order_nested`) and separate
  declaration (`canonBlock_source_separate_nested`) of Def 4.3. Lean's own numbering (`source`, `perm`)
  is the presentation's, by design.

`evaporate` changes only the evaporation flags (`evaporate_fields`).
-/

namespace Ix.CompileCert.Canon

open Ix.Compile.Canon
open Ix (Name ConstantInfo MutConst)

/-- The class representatives, in canonical order. -/
def repsOf (classes : Array (Array Name)) : Array Name := classes.filterMap (·[0]?)

/-- The canonical expansion of a component with these classes (Def 2.5 over the canonical
block). -/
def canonExpand (rules : Rules) (env : Env) (classes : Array (Array Name)) : Except String Expanded :=
  expand env.ind? rules.dedup (repsOf classes) (aliasesOf classes) env.groupOf
    (if rules.nested == .discovery then some env.addr? else none)
    (env.protection.canonical (repsOf classes))

/-- The canonical part of a component's nested data: the auxiliary classes and signatures (none
when the component has no nested data). -/
def canonAux : Option NestedCanon → Array (Array Name) × Array Sig
  | some n => (n.canonClasses, n.canon)
  | none => (#[], #[])

/-- Under the discovery rule, the canonical auxiliary order is the expansion's own. -/
theorem canonicalAuxOrder_discovery {rules : Rules} (hr : rules.nested = .discovery)
    (addr? : Name → Option Address) (x : Expanded) :
    canonicalAuxOrder rules addr? x = .ok (x.aux.map fun m => #[m.name], false) := by
  unfold canonicalAuxOrder
  rw [hr]; rfl

theorem aux_eq_empty {x : Expanded} (h : ¬ x.types.size > x.nOriginals) : x.aux = #[] := by
  apply Array.eq_empty_of_size_eq_zero
  unfold Expanded.aux
  rw [Array.size_extract]; omega

/-- **The nested data of a component, under the discovery rule**: the canonical auxiliary classes
are the auxiliaries of the canonical expansion, one per class, in discovery order; the canonical
signatures are theirs in that order; no order needs addresses; Lean's positions are those of the
expansion of `all` and are mapped by `computePerm`; nothing is evaporated yet. -/
theorem componentNested_source_some {rules : Rules} (hr : rules.nested = .discovery) {env : Env}
    {all : Array Name} {classes : Array (Array Name)} {n : NestedCanon}
    (h : componentNested rules env all classes = .ok (some n)) :
    ∃ x, canonExpand rules env classes = .ok x ∧
      n.canonClasses = x.aux.map (fun m => #[m.name]) ∧ sigsInOrder x n.canonClasses = .ok n.canon ∧
      n.addrDecided = false ∧
      (∃ src, expand env.ind? rules.dedup all (protect := env.protection.source all) = .ok src ∧ n.source = src.sigs ∧
        computePerm env.addr? n.canon n.source all (origToCanonOf classes) = .ok n.perm) ∧
      n.evaporated = Array.replicate n.perm.size false := by
  unfold componentNested at h
  dsimp only at h
  split at h
  · cases h
  · obtain ⟨x, hx, h⟩ := except_bind_ok.1 h
    refine ⟨x, hx, ?_⟩
    split at h
    · cases h
    · split at h
      · obtain ⟨oa, hoa, h⟩ := except_bind_ok.1 h
        rw [canonicalAuxOrder_discovery hr] at hoa
        cases hoa
        obtain ⟨canon, hc, h⟩ := except_bind_ok.1 h
        obtain ⟨src, hsrc, h⟩ := except_bind_ok.1 h
        obtain ⟨perm, hp, h⟩ := except_bind_ok.1 h
        have := except_pure_ok h
        simp only [Option.some.injEq] at this
        subst this
        exact ⟨rfl, hc, rfl, ⟨src, hsrc, rfl, hp⟩, rfl⟩
      · obtain ⟨oa, hoa, h⟩ := except_bind_ok.1 h
        cases except_pure_ok hoa
        obtain ⟨canon, hc, h⟩ := except_bind_ok.1 h
        obtain ⟨src, hsrc, h⟩ := except_bind_ok.1 h
        obtain ⟨perm, hp, h⟩ := except_bind_ok.1 h
        have := except_pure_ok h
        simp only [Option.some.injEq] at this
        subst this
        exact ⟨rfl, hc, rfl, ⟨src, hsrc, rfl, hp⟩, rfl⟩

/-- When a component has no nested data, its classes are empty or the canonical expansion has no
auxiliary. -/
theorem componentNested_none {rules : Rules} {env : Env} {all : Array Name}
    {classes : Array (Array Name)} (h : componentNested rules env all classes = .ok none) :
    repsOf classes = #[] ∨ ∃ x, canonExpand rules env classes = .ok x ∧ x.aux = #[] := by
  unfold componentNested at h
  dsimp only at h
  split at h
  · rename_i he; left
    unfold repsOf
    exact Array.isEmpty_iff.1 he
  · right
    obtain ⟨x, hx, h⟩ := except_bind_ok.1 h
    refine ⟨x, hx, ?_⟩
    split at h
    · rename_i hns
      apply aux_eq_empty
      intro hgt
      simp only [hgt, decide_true, Bool.not_true, Bool.and_false] at hns
      cases hns
    · exfalso
      split at h
      · obtain ⟨oa, -, h⟩ := except_bind_ok.1 h
        obtain ⟨_, _⟩ := oa
        obtain ⟨_, -, h⟩ := except_bind_ok.1 h
        obtain ⟨_, -, h⟩ := except_bind_ok.1 h
        obtain ⟨_, -, h⟩ := except_bind_ok.1 h
        cases except_pure_ok h
      · obtain ⟨oa, -, h⟩ := except_bind_ok.1 h
        obtain ⟨_, _⟩ := oa
        obtain ⟨_, -, h⟩ := except_bind_ok.1 h
        obtain ⟨_, -, h⟩ := except_bind_ok.1 h
        obtain ⟨_, -, h⟩ := except_bind_ok.1 h
        cases except_pure_ok h

theorem sigsInOrder_empty (x : Expanded) : sigsInOrder x #[] = .ok #[] := by
  unfold sigsInOrder; rw [Array.mapM_eq_mapM_toList]; rfl

/-- **The canonical nested auxiliaries depend on the component's classes only** (under the
discovery rule): two runs of `componentNested` with the same classes and any two presentations
`all`, `all'` give the same canonical auxiliary classes and signatures. -/
theorem componentNested_reps_empty {rules : Rules} {env : Env} {all : Array Name}
    {classes : Array (Array Name)} (he : repsOf classes = #[]) :
    componentNested rules env all classes = .ok none := by
  unfold componentNested; dsimp only
  have he' : (Array.filterMap (fun x => x[0]?) classes).isEmpty = true := by
    unfold repsOf at he; rw [he]; rfl
  simp only [he', ↓reduceIte]; rfl

/-- The canonical part an expansion determines: its auxiliaries one per class, in discovery
order, and their signatures. -/
def auxOf (x : Expanded) : Except String (Array (Array Name) × Array Sig) :=
  (fun s => (x.aux.map (fun m => #[m.name]), s)) <$> sigsInOrder x (x.aux.map (fun m => #[m.name]))

theorem componentNested_auxOf {rules : Rules} (hr : rules.nested = .discovery) {env : Env}
    {all : Array Name} {classes : Array (Array Name)} {n : Option NestedCanon}
    (hne : repsOf classes ≠ #[]) (h : componentNested rules env all classes = .ok n) :
    ∃ x, canonExpand rules env classes = .ok x ∧ auxOf x = .ok (canonAux n) := by
  cases n with
  | none =>
    rcases componentNested_none h with he | ⟨x, hx, hax⟩
    · exact absurd he hne
    · refine ⟨x, hx, ?_⟩
      unfold auxOf; rw [hax, show (#[] : Array XMember).map (fun m => #[m.name]) = #[] by simp,
        sigsInOrder_empty]; rfl
  | some m =>
    obtain ⟨x, hx, hcc, hsig, -⟩ := componentNested_source_some hr h
    refine ⟨x, hx, ?_⟩
    unfold auxOf; rw [← hcc, hsig]; rfl

/-- **The canonical nested auxiliaries depend on the component's classes only** (under the
discovery rule): two runs of `componentNested` with the same classes and any two presentations
`all`, `all'` give the same canonical auxiliary classes and signatures. -/
theorem componentNested_canonAux {rules : Rules} (hr : rules.nested = .discovery) {env : Env}
    {all all' : Array Name} {classes : Array (Array Name)} {n₁ n₂ : Option NestedCanon}
    (h₁ : componentNested rules env all classes = .ok n₁)
    (h₂ : componentNested rules env all' classes = .ok n₂) : canonAux n₁ = canonAux n₂ := by
  by_cases he : repsOf classes = #[]
  · rw [componentNested_reps_empty he] at h₁ h₂; cases h₁; cases h₂; rfl
  · obtain ⟨x, hx, ha⟩ := componentNested_auxOf hr he h₁
    obtain ⟨x', hx', ha'⟩ := componentNested_auxOf hr he h₂
    rw [hx] at hx'; cases hx'
    exact Except.ok.inj (ha.symm.trans ha')

/-- `evaporate` changes only the evaporation flags. -/
theorem evaporate_fields {env : Env} {rules : Rules} {all : Array Name}
    {comps : Array (Array (Array Name))} {here : Nat} {n n' : NestedCanon}
    (h : evaporate env rules all comps here n = .ok n') :
    n'.source = n.source ∧ n'.canonClasses = n.canonClasses ∧ n'.canon = n.canon ∧
      n'.perm = n.perm ∧ n'.addrDecided = n.addrDecided := by
  unfold evaporate at h
  split at h
  · cases except_pure_ok h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · split at h
    · split at h
      · obtain ⟨flags, -, h⟩ := except_bind_ok.1 h
        cases except_pure_ok h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      · cases h
    · cases except_pure_ok h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem canonAux_evaporate {env : Env} {rules : Rules} {all : Array Name}
    {comps : Array (Array (Array Name))} {here : Nat} {n0 n : Option NestedCanon}
    (h : n0.mapM (evaporate env rules all comps here) = .ok n) : canonAux n = canonAux n0 := by
  cases n0 with
  | none => cases except_pure_ok h; rfl
  | some m =>
    obtain ⟨m', hm', h⟩ := except_bind_ok.1 h
    cases except_pure_ok h
    obtain ⟨-, h1, h2, -, -⟩ := evaporate_fields hm'
    show (m'.canonClasses, m'.canon) = (m.canonClasses, m.canon)
    rw [h1, h2]

/-- **The nested data of `canonBlock`'s components, under the discovery rule**: a component with
nested data holds the auxiliaries of its canonical expansion, in discovery order, with their
signatures in that order. -/
theorem canonBlock_source_nested_discovery {rules : Rules} (hr : rules.nested = .discovery) {env : Env}
    {all : Array Name} {b : BlockCanon} (h : canonBlock rules env all = .ok b)
    {c : ComponentCanon} (hc : c ∈ b.components) {n : NestedCanon} (hn : c.nested = some n) :
    ∃ x, canonExpand rules env c.classes = .ok x ∧
      n.canonClasses = x.aux.map (fun m => #[m.name]) ∧ sigsInOrder x n.canonClasses = .ok n.canon ∧
      n.addrDecided = false := by
  obtain ⟨i, hs⟩ := canonBlock_mem_spec h hc
  obtain ⟨n0, hn0, hev⟩ := hs.hnest
  rw [hn] at hev
  cases n0 with
  | none => cases except_pure_ok hev
  | some m =>
    obtain ⟨m', hm', hev⟩ := except_bind_ok.1 hev
    have := except_pure_ok hev
    simp only [Option.some.injEq] at this
    subst this
    obtain ⟨-, h1, h2, -, h3⟩ := evaporate_fields hm'
    obtain ⟨x, hx, hcc, hsig, had, -⟩ := componentNested_source_some hr hn0
    exact ⟨x, hx, h1 ▸ hcc, by rw [h1, h2]; exact hsig, h3 ▸ had⟩

theorem canonBlock_canonAux {rules : Rules} {env : Env} {all : Array Name} {b : BlockCanon}
    (h : canonBlock rules env all = .ok b) {c : ComponentCanon} (hc : c ∈ b.components) :
    ∃ n0, componentNested rules env all c.classes = .ok n0 ∧ canonAux c.nested = canonAux n0 := by
  obtain ⟨i, hs⟩ := canonBlock_mem_spec h hc
  obtain ⟨n0, hn0, hev⟩ := hs.hnest
  exact ⟨n0, hn0, canonAux_evaporate hev⟩

/-- **Member order, nested part** (Def 4.3): under the compiler's rules (name-hash seed, discovery
order), every component of a block has a component of the permuted block with the same members up
to order, the same classes, and the same canonical nested auxiliaries and signatures. -/
theorem canonBlock_source_member_order_nested {rules : Rules} (hseed : rules.seed = .byNameHash)
    (hr : rules.nested = .discovery) {env : Env} {all all' : Array Name}
    (hp : all.toList.Perm all'.toList) (hnd : NodupB (nodesOf env all)) (hwf : EnvWF env all)
    {b b' : BlockCanon} (h : canonBlock rules env all = .ok b) (h' : canonBlock rules env all' = .ok b') :
    ∀ c ∈ b.components, ∃ c' ∈ b'.components, c.members.toList.Perm c'.members.toList ∧
      c'.classes = c.classes ∧ c'.blindClasses = c.blindClasses ∧ c'.stats = c.stats ∧
      canonAux c'.nested = canonAux c.nested := by
  intro c hc
  obtain ⟨c', hc', pm, hcl, hbl, hst⟩ := canonBlock_source_member_order hseed hp hnd hwf h h' c hc
  refine ⟨c', hc', pm, hcl, hbl, hst, ?_⟩
  obtain ⟨n0, hn0, e0⟩ := canonBlock_canonAux h hc
  obtain ⟨n0', hn0', e0'⟩ := canonBlock_canonAux h' hc'
  rw [e0, e0']
  rw [hcl] at hn0'
  exact componentNested_canonAux hr hn0' hn0

/-- **Separate declaration, nested part** (Def 4.3): a component declared on its own has the same
canonical nested auxiliaries and signatures as within its block. -/
theorem canonBlock_source_separate_nested {rules : Rules} (hr : rules.nested = .discovery) {env : Env}
    {all : Array Name} {b : BlockCanon} (hnd : NodupB (nodesOf env all)) (hwf : EnvWF env all)
    (h : canonBlock rules env all = .ok b) {c : ComponentCanon} (hc : c ∈ b.components)
    {b' : BlockCanon} (h' : canonBlock rules env c.members = .ok b') :
    ∃ c', b'.components = #[c'] ∧ c'.members = c.members ∧ c'.classes = c.classes ∧
      c'.blindClasses = c.blindClasses ∧ c'.stats = c.stats ∧ canonAux c'.nested = canonAux c.nested := by
  obtain ⟨c', hb', hmem, hcl, hbl, hst⟩ := canonBlock_source_separate hnd hwf h hc h'
  refine ⟨c', hb', hmem, hcl, hbl, hst, ?_⟩
  have hc' : c' ∈ b'.components := by rw [hb']; simp
  obtain ⟨n0, hn0, e0⟩ := canonBlock_canonAux h hc
  obtain ⟨n0', hn0', e0'⟩ := canonBlock_canonAux h' hc'
  rw [e0, e0']
  rw [hcl] at hn0'
  exact componentNested_canonAux hr hn0' hn0

end Ix.CompileCert.Canon
