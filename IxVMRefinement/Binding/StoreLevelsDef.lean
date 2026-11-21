import IxVMRefinement.Binding.FamilyFlatLocal

/-! # Level-parameter well-scopedness and inductive parameter coherence definitions

Leaf definitions for store-level level-parameter scoping (`FamilyRecon.StoreLevelsOk`),
inductive parameter coherence (`FamilyRecon.StoreIndParamsOk`), unit-level bundle
(`FamilyRecon.UnitLevelsAndParamsOk`), and the blob-independent store invariant
`Binding.StoreLevelsParams` carried on `StoredFamilies` and `FamilyAdmits`. -/

namespace IxVM.Refinement.Binding.FamilyRecon

open IxVM.Consistency
open IxVM.Refinement.Binding.FamilyFlat

set_option linter.unusedVariables false

/-- **Every expression of every record at an address in `S` has its level parameters within the
record's declared level count (below `2^32`)**, so `RawConvExpr` lifts directly to `TmOExact` and
`loadedAt`. -/
structure StoreLevelsOk (t : Ix.Kernel.RoleTable) (E : Ixon.Env)
    (S : _root_.Address → Prop) : Prop where
  defnVal : ∀ a c d, S a → recordOf E a = some c → c.info = .defn d → d.kind = .defn →
    d.lvls.toNat < 4294967296 ∧
    ∀ E_rd, (exprReader t (fun x => E.blobs.get? x) c id (soloSelf t a)).read d.value = .ok E_rd →
      E_rd.allLevelParamsDefined (List.range d.lvls.toNat) = true
  dPrjVal : ∀ a c p cb ms d, S a → recordOf E a = some c → c.info = .dPrj p →
    recordOf E p.block = some cb → cb.info = .muts ms → ms[p.idx.toNat]? = some (.defn d) →
    d.kind = .defn →
    d.lvls.toNat < 4294967296 ∧
    ∀ E_rd, (exprReader t (fun x => E.blobs.get? x) cb id
        (blockSelf t p.block ms)).read d.value = .ok E_rd →
      E_rd.allLevelParamsDefined (List.range d.lvls.toNat) = true
  indTy : ∀ a c p cb ms ind, S a → recordOf E a = some c → c.info = .iPrj p →
    recordOf E p.block = some cb → cb.info = .muts ms → ms[p.idx.toNat]? = some (.indc ind) →
    ind.lvls.toNat < 4294967296 ∧
    ∀ E_rd, (exprReader t (fun x => E.blobs.get? x) cb id
        (blockSelf t p.block ms)).read ind.typ = .ok E_rd →
      E_rd.allLevelParamsDefined (List.range ind.lvls.toNat) = true
  ctorTy : ∀ (b : _root_.Address) (cb : Ixon.Constant) (ms : Array Ixon.MutConst)
      (i : Nat) (ind : Ixon.Inductive) (j : Nat) (ct : Ixon.Constructor),
    S b → recordOf E b = some cb → cb.info = .muts ms →
    ms[i]? = some (.indc ind) → ind.ctors[j]? = some ct →
    ct.lvls.toNat < 4294967296 ∧
    ∀ E_rd, (exprReader t (fun x => E.blobs.get? x) cb id
        (blockSelf t b ms)).read ct.typ = .ok E_rd →
      E_rd.allLevelParamsDefined (List.range ct.lvls.toNat) = true
  recr : ∀ (rb : _root_.Address) (crb : Ixon.Constant) (rs : Array Ixon.MutConst)
      (k : Nat) (r : Ixon.Recursor),
    S rb → recordOf E rb = some crb → crb.info = .muts rs →
    rs[k]? = some (.recr r) →
    r.lvls.toNat < 4294967296 ∧
    (∀ E_rd, (exprReader t (fun x => E.blobs.get? x) crb id
        (blockSelf t rb rs)).read r.typ = .ok E_rd →
      E_rd.allLevelParamsDefined (List.range r.lvls.toNat) = true) ∧
    (∀ (j : Nat) (ru : Ixon.RecursorRule) E_rd, r.rules[j]? = some ru →
      (exprReader t (fun x => E.blobs.get? x) crb id
        (blockSelf t rb rs)).read ru.rhs = .ok E_rd →
      E_rd.allLevelParamsDefined (List.range r.lvls.toNat) = true)

/-- **Inductive parameter coherence over a store subset `S`**: every constructor of an inductive
block in `S` has the same parameter count as its parent inductive, and any two inductive members
of the same block in `S` share their parameter count. -/
structure StoreIndParamsOk (E : Ixon.Env) (S : _root_.Address → Prop) : Prop where
  ctorParams : ∀ (b : _root_.Address) (cb : Ixon.Constant) (ms : Array Ixon.MutConst)
      (i : Nat) (ind : Ixon.Inductive) (j : Nat) (ct : Ixon.Constructor),
    S b → recordOf E b = some cb → cb.info = .muts ms →
    ms[i]? = some (.indc ind) → ind.ctors[j]? = some ct → ct.params = ind.params
  blockParams : ∀ (b : _root_.Address) (cb : Ixon.Constant) (ms : Array Ixon.MutConst)
      (i₁ i₂ : Nat) (ind₁ ind₂ : Ixon.Inductive),
    S b → recordOf E b = some cb → cb.info = .muts ms →
    ms[i₁]? = some (.indc ind₁) → ms[i₂]? = some (.indc ind₂) → ind₁.params = ind₂.params

/-- Unit-level bundle capturing all level-parameter and inductive-parameter invariants of a
single record `c` at address `a`. -/
structure UnitLevelsAndParamsOk (t : Ix.Kernel.RoleTable) (E₀ : Ixon.Env)
    (a : _root_.Address) (c : Ixon.Constant) : Prop where
  defnVal : ∀ (d : Ixon.Definition), c.info = .defn d → d.kind = .defn →
    d.lvls.toNat < 4294967296 ∧
    ∀ E_rd, (exprReader t (fun x => E₀.blobs.get? x) c id (soloSelf t a)).read d.value = .ok E_rd →
      E_rd.allLevelParamsDefined (List.range d.lvls.toNat) = true
  mutDefn : ∀ (ms : Array Ixon.MutConst) (i : Nat) (d : Ixon.Definition),
    c.info = .muts ms → ms[i]? = some (.defn d) → d.kind = .defn →
    d.lvls.toNat < 4294967296 ∧
    ∀ E_rd, (exprReader t (fun x => E₀.blobs.get? x) c id (blockSelf t a ms)).read d.value = .ok E_rd →
      E_rd.allLevelParamsDefined (List.range d.lvls.toNat) = true
  mutInd : ∀ (ms : Array Ixon.MutConst) (i : Nat) (ind : Ixon.Inductive),
    c.info = .muts ms → ms[i]? = some (.indc ind) →
    (ind.lvls.toNat < 4294967296 ∧
      ∀ E_rd, (exprReader t (fun x => E₀.blobs.get? x) c id (blockSelf t a ms)).read ind.typ = .ok E_rd →
        E_rd.allLevelParamsDefined (List.range ind.lvls.toNat) = true) ∧
    (∀ (j : Nat) (ct : Ixon.Constructor), ind.ctors[j]? = some ct →
      ct.lvls.toNat < 4294967296 ∧
      (∀ E_rd, (exprReader t (fun x => E₀.blobs.get? x) c id (blockSelf t a ms)).read ct.typ = .ok E_rd →
        E_rd.allLevelParamsDefined (List.range ct.lvls.toNat) = true) ∧
      ct.params = ind.params) ∧
    (∀ (i₂ : Nat) (ind₂ : Ixon.Inductive), ms[i₂]? = some (.indc ind₂) → ind.params = ind₂.params)
  mutRecr : ∀ (ms : Array Ixon.MutConst) (k : Nat) (r : Ixon.Recursor),
    c.info = .muts ms → ms[k]? = some (.recr r) →
    r.lvls.toNat < 4294967296 ∧
    (∀ E_rd, (exprReader t (fun x => E₀.blobs.get? x) c id (blockSelf t a ms)).read r.typ = .ok E_rd →
      E_rd.allLevelParamsDefined (List.range r.lvls.toNat) = true) ∧
    (∀ (j : Nat) (ru : Ixon.RecursorRule) E_rd, r.rules[j]? = some ru →
      (exprReader t (fun x => E₀.blobs.get? x) c id (blockSelf t a ms)).read ru.rhs = .ok E_rd →
      E_rd.allLevelParamsDefined (List.range r.lvls.toNat) = true)

/-- **Any `UsedClosed` sub-store `R` of `E₀` whose records satisfy `UnitLevelsAndParamsOk`**
satisfies both `StoreLevelsOk t E₀ (Held R)` and `StoreIndParamsOk E₀ (Held R)`. -/
theorem storeLevelsOk_and_indParamsOk_of_units {t : Ix.Kernel.RoleTable} {E₀ R : Ixon.Env}
    (hRsub : ∀ y c, recordOf R y = some c → recordOf E₀ y = some c)
    (hcl : UsedClosed R)
    (hunits : ∀ a c, recordOf R a = some c → UnitLevelsAndParamsOk t E₀ a c) :
    StoreLevelsOk t E₀ (Held R) ∧ StoreIndParamsOk E₀ (Held R) := by
  have held_rec : ∀ a c, Held R a → recordOf E₀ a = some c → recordOf R a = some c := by
    intro a c ha hcE
    obtain ⟨cR, hcR⟩ := Option.isSome_iff_exists.mp ha
    have heq := Option.some.inj ((hRsub a cR hcR).symm.trans hcE)
    exact heq ▸ hcR
  have owner_held : ∀ a c, Held R a → recordOf E₀ a = some c → Held R (Ix.Cert.ownerOf a c) :=
    fun a c ha hcE => (hcl.1 a c (held_rec a c ha hcE)).1
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro a c d ha hcE hci hdk
    exact (hunits a c (held_rec a c ha hcE)).defnVal d hci hdk
  · intro a c p cb ms d ha hcE hci hcbE hms hi hdk
    have hpb : Held R p.block := by simpa [Ix.Cert.ownerOf, hci] using owner_held a c ha hcE
    exact (hunits p.block cb (held_rec p.block cb hpb hcbE)).mutDefn ms p.idx.toNat d hms hi hdk
  · intro a c p cb ms ind ha hcE hci hcbE hms hi
    have hpb : Held R p.block := by simpa [Ix.Cert.ownerOf, hci] using owner_held a c ha hcE
    exact ((hunits p.block cb (held_rec p.block cb hpb hcbE)).mutInd ms p.idx.toNat ind hms hi).1
  · intro b cb ms i ind j ct hb hcbE hms hi hj
    have hct := ((hunits b cb (held_rec b cb hb hcbE)).mutInd ms i ind hms hi).2.1 j ct hj
    exact ⟨hct.1, hct.2.1⟩
  · intro rb crb rs k r hrb hcrbE hrs hk
    exact (hunits rb crb (held_rec rb crb hrb hcrbE)).mutRecr rs k r hrs hk
  · intro b cb ms i ind j ct hb hcbE hms hi hj
    exact (((hunits b cb (held_rec b cb hb hcbE)).mutInd ms i ind hms hi).2.1 j ct hj).2.2
  · intro b cb ms i₁ i₂ ind₁ ind₂ hb hcbE hms hi₁ hi₂
    exact ((hunits b cb (held_rec b cb hb hcbE)).mutInd ms i₁ ind₁ hms hi₁).2.2 i₂ ind₂ hi₂

end IxVM.Refinement.Binding.FamilyRecon

namespace IxVM.Refinement.Binding

open IxVM.Consistency

/-- **Blob-independent level-parameter well-scopedness and inductive parameter coherence on a
store `R`**: for every store `E` that holds every record of `R`, `StoreLevelsOk` and
`StoreIndParamsOk` hold over `Held R` in `E`. -/
def StoreLevelsParams (t : Ix.Kernel.RoleTable) (R : Ixon.Env) : Prop :=
  ∀ E : Ixon.Env, (∀ y c, recordOf R y = some c → recordOf E y = some c) →
    FamilyRecon.StoreLevelsOk t E (FamilyFlat.Held R) ∧
    FamilyRecon.StoreIndParamsOk E (FamilyFlat.Held R)

/-- **`StoreLevelsParams` from unit-level facts over arbitrary blob stores.** -/
theorem storeLevelsParams_of_units {t : Ix.Kernel.RoleTable} {R : Ixon.Env}
    (hcl : UsedClosed R)
    (hunits : ∀ E a c, recordOf R a = some c → FamilyRecon.UnitLevelsAndParamsOk t E a c) :
    StoreLevelsParams t R :=
  fun E hRE => FamilyRecon.storeLevelsOk_and_indParamsOk_of_units hRE hcl (hunits E)

/-- **`StoreLevelsParams` restricts to any `UsedClosed` sub-store.** -/
theorem StoreLevelsParams.of_usedClosed_sub {t : Ix.Kernel.RoleTable} {R₁ R₂ : Ixon.Env}
    (hcl : UsedClosed R₁)
    (hsub : ∀ y c, recordOf R₁ y = some c → recordOf R₂ y = some c)
    (h₂ : StoreLevelsParams t R₂) : StoreLevelsParams t R₁ := by
  intro E hRE
  let E' : Ixon.Env := { consts := R₂.consts, blobs := E.blobs }
  obtain ⟨hlv₂, hpar₂⟩ := h₂ E' (fun _ _ h => h)
  have hheld : ∀ a, FamilyFlat.Held R₁ a → FamilyFlat.Held R₂ a := by
    intro a ha
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp ha
    exact Option.isSome_iff_exists.mpr ⟨c, hsub a c hc⟩
  have hrec_eq : ∀ a c, FamilyFlat.Held R₁ a → recordOf E a = some c → recordOf E' a = some c := by
    intro a c ha hcE
    obtain ⟨c₁, hc₁⟩ := Option.isSome_iff_exists.mp ha
    have ec : c₁ = c := Option.some.inj ((hRE a c₁ hc₁).symm.trans hcE)
    subst ec
    exact hsub a c₁ hc₁
  have howner : ∀ a c, FamilyFlat.Held R₁ a → recordOf E a = some c →
      FamilyFlat.Held R₁ (Ix.Cert.ownerOf a c) := by
    intro a c ha hcE
    obtain ⟨c₁, hc₁⟩ := Option.isSome_iff_exists.mp ha
    have ec : c₁ = c := Option.some.inj ((hRE a c₁ hc₁).symm.trans hcE)
    subst ec
    exact (hcl.1 a c₁ hc₁).1
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro a c d ha hc hci hdk
    exact hlv₂.defnVal a c d (hheld a ha) (hrec_eq a c ha hc) hci hdk
  · intro a c p cb ms d ha hc hci hcb hms hi hdk
    have hpb : FamilyFlat.Held R₁ p.block := by simpa [Ix.Cert.ownerOf, hci] using howner a c ha hc
    exact hlv₂.dPrjVal a c p cb ms d (hheld a ha) (hrec_eq a c ha hc) hci
      (hrec_eq p.block cb hpb hcb) hms hi hdk
  · intro a c p cb ms ind ha hc hci hcb hms hi
    have hpb : FamilyFlat.Held R₁ p.block := by simpa [Ix.Cert.ownerOf, hci] using howner a c ha hc
    exact hlv₂.indTy a c p cb ms ind (hheld a ha) (hrec_eq a c ha hc) hci
      (hrec_eq p.block cb hpb hcb) hms hi
  · intro b cb ms i ind j ct hb hcb hms hi hj
    exact hlv₂.ctorTy b cb ms i ind j ct (hheld b hb) (hrec_eq b cb hb hcb) hms hi hj
  · intro rb crb rs k r hrb hcrb hrs hk
    exact hlv₂.recr rb crb rs k r (hheld rb hrb) (hrec_eq rb crb hrb hcrb) hrs hk
  · intro b cb ms i ind j ct hb hcb hms hi hj
    exact hpar₂.ctorParams b cb ms i ind j ct (hheld b hb) (hrec_eq b cb hb hcb) hms hi hj
  · intro b cb ms i₁ i₂ ind₁ ind₂ hb hcb hms hi₁ hi₂
    exact hpar₂.blockParams b cb ms i₁ i₂ ind₁ ind₂ (hheld b hb) (hrec_eq b cb hb hcb) hms hi₁ hi₂

/-- **`StoreLevelsParams` depends on a store only through its constant map.** -/
theorem StoreLevelsParams.of_storeCongr {t : Ix.Kernel.RoleTable} {R R' : Ixon.Env}
    (hc : ∀ a, R.consts.get? a = R'.consts.get? a)
    (h : StoreLevelsParams t R) : StoreLevelsParams t R' := by
  have hrec : ∀ y, recordOf R y = recordOf R' y := fun y => by
    unfold recordOf; rw [hc y]
  have hheld : FamilyFlat.Held R = FamilyFlat.Held R' := by
    funext y; unfold FamilyFlat.Held; rw [hrec y]
  intro E hE
  rw [← hheld]
  exact h E (fun y c hy => hE y c (by rwa [← hrec y]))

end IxVM.Refinement.Binding
