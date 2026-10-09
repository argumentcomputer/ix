import Ix.CompileCert.Canon.ComponentBridge
import Ix.CompileCert.Canon.CoreDiscovery

/-!
UNCOMPILED proposal. This module lifts the existing component proof bodies
through the unrestricted callback facade. Both protection functions and all
callbacks are arbitrary; there is no finite-environment representation premise.
The discovery name equation inherited from CoreDiscovery still has an
existential forbidden list. It is not presented here as the complete fresh-name
correspondence; SourceProtection supplies concrete actual-source separation.
-/

namespace Ix.CompileCert.Canon.ComponentCoreProof
open Ix.Compile.Canon
open Ix (Name)

theorem componentNested_some {rules : Rules} (hr : rules.nested = .discovery) {protect : ComponentCore.Protection} {env : ComponentCore.Env}
    {all : Array Name} {classes : Array (Array Name)} {n : NestedCanon}
    (h : ComponentCore.componentNested protect rules env all classes = .ok (some n)) :
    ∃ x, ComponentCore.canonExpand protect rules env classes = .ok x ∧
      n.canonClasses = x.aux.map (fun m => #[m.name]) ∧ sigsInOrder x n.canonClasses = .ok n.canon ∧
      n.addrDecided = false ∧
      (∃ src, ExpansionCore.expand (protect.source all) env.ind? rules.dedup all
        (groupOf := leanSourceGroup.apply) = .ok src ∧ n.source = src.sigs ∧
        computePerm env.addr? n.canon n.source all (origToCanonOf classes) = .ok n.perm) ∧
      n.evaporated = Array.replicate n.perm.size false := by
  unfold ComponentCore.componentNested at h
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

theorem componentNested_none {rules : Rules} {protect : ComponentCore.Protection} {env : ComponentCore.Env} {all : Array Name}
    {classes : Array (Array Name)} (h : ComponentCore.componentNested protect rules env all classes = .ok none) :
    repsOf classes = #[] ∨ ∃ x, ComponentCore.canonExpand protect rules env classes = .ok x ∧ x.aux = #[] := by
  unfold ComponentCore.componentNested at h
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

theorem componentNested_reps_empty {rules : Rules} {protect : ComponentCore.Protection} {env : ComponentCore.Env} {all : Array Name}
    {classes : Array (Array Name)} (he : repsOf classes = #[]) :
    ComponentCore.componentNested protect rules env all classes = .ok none := by
  unfold ComponentCore.componentNested; dsimp only
  have he' : (Array.filterMap (fun x => x[0]?) classes).isEmpty = true := by
    unfold repsOf at he; rw [he]; rfl
  simp only [he', ↓reduceIte]; rfl

theorem componentNested_auxOf {rules : Rules} (hr : rules.nested = .discovery) {protect : ComponentCore.Protection} {env : ComponentCore.Env}
    {all : Array Name} {classes : Array (Array Name)} {n : Option NestedCanon}
    (hne : repsOf classes ≠ #[]) (h : ComponentCore.componentNested protect rules env all classes = .ok n) :
    ∃ x, ComponentCore.canonExpand protect rules env classes = .ok x ∧ auxOf x = .ok (canonAux n) := by
  cases n with
  | none =>
    rcases componentNested_none h with he | ⟨x, hx, hax⟩
    · exact absurd he hne
    · refine ⟨x, hx, ?_⟩
      unfold auxOf; rw [hax, show (#[] : Array XMember).map (fun m => #[m.name]) = #[] by simp,
        sigsInOrder_empty]; rfl
  | some m =>
    obtain ⟨x, hx, hcc, hsig, -⟩ := componentNested_some hr h
    refine ⟨x, hx, ?_⟩
    unfold auxOf; rw [← hcc, hsig]; rfl

theorem componentNested_canonAux {rules : Rules} (hr : rules.nested = .discovery) {protect : ComponentCore.Protection} {env : ComponentCore.Env}
    {all all' : Array Name} {classes : Array (Array Name)} {n₁ n₂ : Option NestedCanon}
    (h₁ : ComponentCore.componentNested protect rules env all classes = .ok n₁)
    (h₂ : ComponentCore.componentNested protect rules env all' classes = .ok n₂) : canonAux n₁ = canonAux n₂ := by
  by_cases he : repsOf classes = #[]
  · rw [componentNested_reps_empty he] at h₁ h₂; cases h₁; cases h₂; rfl
  · obtain ⟨x, hx, ha⟩ := componentNested_auxOf hr he h₁
    obtain ⟨x', hx', ha'⟩ := componentNested_auxOf hr he h₂
    rw [hx] at hx'; cases hx'
    exact Except.ok.inj (ha.symm.trans ha')

theorem evaporate_fields {protect : ComponentCore.Protection} {env : ComponentCore.Env} {rules : Rules} {all : Array Name}
    {comps : Array (Array (Array Name))} {here : Nat} {n n' : NestedCanon}
    (h : ComponentCore.evaporate protect env rules all comps here n = .ok n') :
    n'.source = n.source ∧ n'.canonClasses = n.canonClasses ∧ n'.canon = n.canon ∧
      n'.perm = n.perm ∧ n'.addrDecided = n.addrDecided := by
  unfold ComponentCore.evaporate at h
  split at h
  · cases except_pure_ok h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · split at h
    · split at h
      · obtain ⟨flags, -, h⟩ := except_bind_ok.1 h
        cases except_pure_ok h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      · cases h
    · cases except_pure_ok h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem canonAux_evaporate {protect : ComponentCore.Protection} {env : ComponentCore.Env} {rules : Rules} {all : Array Name}
    {comps : Array (Array (Array Name))} {here : Nat} {n0 n : Option NestedCanon}
    (h : n0.mapM (ComponentCore.evaporate protect env rules all comps here) = .ok n) : canonAux n = canonAux n0 := by
  cases n0 with
  | none => cases except_pure_ok h; rfl
  | some m =>
    obtain ⟨m', hm', h⟩ := except_bind_ok.1 h
    cases except_pure_ok h
    obtain ⟨-, h1, h2, -, -⟩ := evaporate_fields hm'
    show (m'.canonClasses, m'.canon) = (m.canonClasses, m.canon)
    rw [h1, h2]

theorem componentNested_discovery {rules : Rules} (hr : rules.nested = .discovery) {protect : ComponentCore.Protection} {env : ComponentCore.Env}
    {all : Array Name} {classes : Array (Array Name)} {n : NestedCanon}
    (h : ComponentCore.componentNested protect rules env all classes = .ok (some n)) :
    ∃ (x : Expanded) (first : Name) (fi : IndView), ComponentCore.canonExpand protect rules env classes = .ok x ∧
      n.canonClasses = x.aux.map (fun m => #[m.name]) ∧ sigsInOrder x n.canonClasses = .ok n.canon ∧
      (repsOf classes)[0]? = some first ∧ env.ind? first = some fi ∧
      x.nOriginals = (repsOf classes).size ∧
      (∀ (k : Nat) (m : XMember), x.aux[k]? = some m →
        (∃ J forbidden, m.name = auxNameOf (fi.all[0]?.getD first) J (k + 1) forbidden) ∧ m.sourceOwner ∈ repsOf classes) ∧
      ∃ D : List Nat, D.length = x.aux.size ∧ D.Pairwise (· ≤ ·) ∧
        ∀ (k d : Nat), D[k]? = some d → d < x.nOriginals + k := by
  obtain ⟨x, hx, hcc, hsig, -, -, -⟩ := componentNested_some hr h
  have hx' := hx
  unfold ComponentCore.canonExpand at hx'
  obtain ⟨first, fi, hfirst, hfi, hn0, hle, -, D, hD, hDs, hk⟩ := ExpansionCoreProof.expand_spec hx'
  refine ⟨x, first, fi, hx, hcc, hsig, hfirst, hfi, hn0, fun k m hm => ?_, D, hD, hDs, fun k d hd => ?_⟩
  · obtain ⟨hJ, -⟩ := hk k m hm
    refine ⟨hJ, ExpansionCoreProof.expand_owner hx' (x.nOriginals + k) m ?_⟩
    rw [← aux_getElem?_eq x k hle]; exact hm
  · have hkl : k < x.aux.size := by
      rw [← hD]
      rcases Nat.lt_or_ge k D.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hd; cases hd
    obtain ⟨m, hm⟩ : ∃ m, x.aux[k]? = some m := ⟨x.aux[k], Array.getElem?_eq_getElem hkl⟩
    obtain ⟨-, d', md, hd', hlt, -⟩ := hk k m hm
    rw [hd] at hd'; cases hd'
    exact hlt

end Ix.CompileCert.Canon.ComponentCoreProof
