import IxCCGrounding.Direct.Check

/-!
# The checked facts the theorems consume (`IxCCGrounding.Facts`)

The recursor clause `RecFacts` and the two structures that carry it, `Faith` (the faithfulness
clauses over `RecFacts`) and `GroundFacts` (every decidable fact the root theorem consumes), with
the lemmas that the facts as earlier parts landed them imply today's. Everything they are built
from (`RecClass`, `recClassB`, `RecStored`, the bases, `FaithWith`, `GroundFactsWith`, `NatBasis`,
`CaseFacts`) is in `IxCCGrounding.Syntax`; this module comes after the decided direct route
(`IxCCGrounding.Direct.Check`), so a recursor fact may read it. Denotes-free, like both.
-/

namespace IxCC.Grounding

open Ix.Kernel
open IxCC.Src (Value Slot Term CId Program Levels)

/-- **The recursors of `S`, checked** (replacing `NoRecr`): each is in an admitted class, has the
checked shape, and where it is `Eq.rec` the bases of `Eq.refl`, `Eq` and `Eq.rec` hold. Vacuous
when `S` has no recursor (`recFacts_of_noRecr`). -/
structure RecFacts (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (S : CId → Prop) : Prop where
  cls : ∀ r, S r → ∀ sf kk lvls np nmot nmin ni ind rules ty,
    p.decl? r = some (.recr sf kk lvls np nmot nmin ni ind rules ty) →
    ∃ k, recClassB p env κ r = some k ∧ k ∈ admittedClasses
  stored : ∀ r, S r → ∀ sf kk lvls np nmot nmin ni ind rules ty,
    p.decl? r = some (.recr sf kk lvls np nmot nmin ni ind rules ty) → RecStored p env κ lpsOf r
  eqRefl : ∀ r, S r → recClassB p env κ r = some .eqRec → EqReflBasis env
  /-- where it is `Eq.rec`, `Eq` and `Eq.rec` are stored as F3 there reads them (G3, part C) -/
  eqRec : ∀ r, S r → recClassB p env κ r = some .eqRec → EqBasis env ∧ EqRecBasis env
  /-- where it is flat, its rules' telescopes, the program side and its rules' constructors as ι
  reads them (G3, part D) -/
  flat : ∀ r, S r → recClassB p env κ r = some .flat →
    RecTele env (κ r) ∧ RecProg p κ S r ∧ RecCtorsRaw p env κ r

/-- **The landed clause implies the new one**: with no recursor in `S`, `RecFacts` holds. -/
theorem recFacts_of_noRecr {p : Program} {env : KEnv} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {S : CId → Prop} (h : NoRecr p S) : RecFacts p env κ lpsOf S where
  cls r hr sf kk lvls np nmot nmin ni ind rules ty hd :=
    absurd hd (h r hr sf kk lvls np nmot nmin ni ind rules ty)
  stored r hr sf kk lvls np nmot nmin ni ind rules ty hd :=
    absurd hd (h r hr sf kk lvls np nmot nmin ni ind rules ty)
  eqRefl r hr hk := by
    obtain ⟨sf, kk, lvls, np, nmot, nmin, ni, ind, rules, ty, hd⟩ := recClassB_recr hk
    exact absurd hd (h r hr sf kk lvls np nmot nmin ni ind rules ty)
  eqRec r hr hk := by
    obtain ⟨sf, kk, lvls, np, nmot, nmin, ni, ind, rules, ty, hd⟩ := recClassB_recr hk
    exact absurd hd (h r hr sf kk lvls np nmot nmin ni ind rules ty)
  flat r hr hk := by
    obtain ⟨sf, kk, lvls, np, nmot, nmin, ni, ind, rules, ty, hd⟩ := recClassB_recr hk
    exact absurd hd (h r hr sf kk lvls np nmot nmin ni ind rules ty)

/-- **The recursor facts as parts A and B landed them imply today's** (G3, part C): there every
recursor of `S` was of class `empty`, the one class then admitted, with the checked shape, so no
recursor of `S` is `Eq.rec` and the `Eq.rec` clauses hold vacuously. So each theorem taking
`RecFacts` (through `Faith` or `GroundFacts`) implies its statement as parts A and B landed it. -/
theorem recFacts_of_emptyOnly {p : Program} {env : KEnv} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {S : CId → Prop}
    (hcls : ∀ r, S r → ∀ sf kk lvls np nmot nmin ni ind rules ty,
      p.decl? r = some (.recr sf kk lvls np nmot nmin ni ind rules ty) →
      ∃ k, recClassB p env κ r = some k ∧ k ∈ [RecClass.empty])
    (hst : ∀ r, S r → ∀ sf kk lvls np nmot nmin ni ind rules ty,
      p.decl? r = some (.recr sf kk lvls np nmot nmin ni ind rules ty) → RecStored p env κ lpsOf r) :
    RecFacts p env κ lpsOf S where
  cls r hr sf kk lvls np nmot nmin ni ind rules ty hd := by
    obtain ⟨k, hk, hm⟩ := hcls r hr sf kk lvls np nmot nmin ni ind rules ty hd
    exact ⟨k, hk, by simp only [List.mem_singleton] at hm; subst hm; simp [admittedClasses]⟩
  stored := hst
  eqRefl r hr hk := by
    obtain ⟨sf, kk, lvls, np, nmot, nmin, ni, ind, rules, ty, hd⟩ := recClassB_recr hk
    obtain ⟨k, hk', hm⟩ := hcls r hr sf kk lvls np nmot nmin ni ind rules ty hd
    simp only [List.mem_singleton] at hm
    subst hm
    rw [hk] at hk'
    cases hk'
  eqRec r hr hk := by
    obtain ⟨sf, kk, lvls, np, nmot, nmin, ni, ind, rules, ty, hd⟩ := recClassB_recr hk
    obtain ⟨k, hk', hm⟩ := hcls r hr sf kk lvls np nmot nmin ni ind rules ty hd
    simp only [List.mem_singleton] at hm
    subst hm
    rw [hk] at hk'
    cases hk'
  flat r hr hk := by
    obtain ⟨sf, kk, lvls, np, nmot, nmin, ni, ind, rules, ty, hd⟩ := recClassB_recr hk
    obtain ⟨k, hk', hm⟩ := hcls r hr sf kk lvls np nmot nmin ni ind rules ty hd
    simp only [List.mem_singleton] at hm
    subst hm
    rw [hk] at hk'
    cases hk'

/-- **The recursor facts as part C landed them imply today's** (G3, part D): there every recursor
of `S` was of class `empty` or `eqRec`, the classes then admitted, with the checked shape and, at
`Eq.rec`, the `Eq`, `Eq.refl` and `Eq.rec` bases; so no recursor of `S` is flat and the clause
part D adds holds vacuously. So each theorem taking `RecFacts` (through `Faith` or `GroundFacts`)
implies its statement as part C landed it. -/
theorem recFacts_of_eqRecOnly {p : Program} {env : KEnv} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {S : CId → Prop}
    (hcls : ∀ r, S r → ∀ sf kk lvls np nmot nmin ni ind rules ty,
      p.decl? r = some (.recr sf kk lvls np nmot nmin ni ind rules ty) →
      ∃ k, recClassB p env κ r = some k ∧ k ∈ [RecClass.empty, RecClass.eqRec])
    (hst : ∀ r, S r → ∀ sf kk lvls np nmot nmin ni ind rules ty,
      p.decl? r = some (.recr sf kk lvls np nmot nmin ni ind rules ty) → RecStored p env κ lpsOf r)
    (hR : ∀ r, S r → recClassB p env κ r = some .eqRec → EqReflBasis env)
    (hB : ∀ r, S r → recClassB p env κ r = some .eqRec → EqBasis env ∧ EqRecBasis env) :
    RecFacts p env κ lpsOf S where
  cls r hr sf kk lvls np nmot nmin ni ind rules ty hd := by
    obtain ⟨k, hk, hm⟩ := hcls r hr sf kk lvls np nmot nmin ni ind rules ty hd
    refine ⟨k, hk, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl <;> simp [admittedClasses]
  stored := hst
  eqRefl := hR
  eqRec := hB
  flat r hr hk := by
    obtain ⟨sf, kk, lvls, np, nmot, nmin, ni, ind, rules, ty, hd⟩ := recClassB_recr hk
    obtain ⟨k, hk', hm⟩ := hcls r hr sf kk lvls np nmot nmin ni ind rules ty hd
    rw [hk] at hk'
    cases hk'
    simp at hm

/-- **The faithfulness clauses**, with the recursors of `S` checked (`RecFacts`). -/
abbrev Faith (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (S : CId → Prop) : Prop :=
  FaithWith (RecFacts p env κ lpsOf S) p env κ lpsOf S

/-- **The checked facts**, the recursors of `S` checked (`RecFacts`). -/
abbrev GroundFacts (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (ann : IxCC.Src.Relevance.Ann) (S : CId → Prop) : Prop :=
  GroundFactsWith (RecFacts p env κ lpsOf S) p env κ lpsOf ann S

/-- **Every landed `GroundFacts` is a `GroundFacts`**: so each theorem taking `GroundFacts`
implies its landed form (`rootSound_noRecr` and the others in `IxCCGrounding.Root`). -/
theorem groundFacts_of_noRecr {p : Program} {env : KEnv} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {S : CId → Prop}
    (hG : GroundFactsNoRecr p env κ lpsOf ann S) : GroundFacts p env κ lpsOf ann S :=
  hG.mono recFacts_of_noRecr

end IxCC.Grounding
