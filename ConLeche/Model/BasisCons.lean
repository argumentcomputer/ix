module

public import ConLeche.Model.RecRulesCons

public section

/-!
# The basis-cons preservation kit (task #161, ENDGAME B, task 2)

`BasisStepPB` conses *inductive-kind* heads — `indInfo`, `ctorInfo`,
`recInfo` — and the existing preservation lemmas are all keyed on the
value kinds:

| field | value-kind lemma | at a basis cons |
| --- | --- | --- |
| `nat_ops` | `natOps_cons_fresh` | **reusable** (`Or.inl`: not a `defnInfo`) |
| `div_mod` | `divMod_cons_fresh` | **reusable**, same disjunct |
| `eq_law` | `eqLaw_cons_fresh` | **reusable** (the `Eq` disequality, off freshness) |
| `nat_heads` | `natHeads_cons_fresh` | **REFUTED** — its `hknd` premise is the cons's own kind |
| `caps_ok` | `capsOk_cons_fresh` | **REFUTED** — same three kind premises |
| `rec_rules` | `recRules_cons_fresh` | **REFUTED** — `hnotctor`/`hnotrec` |

This file supplies the two replacements that go through, and records
the one that does not.

## The replacement is `reservedBasisNames`, and it was designed in

`EtaFamilyStored`'s **name-only conjunct**
(`Verify/EnvGuards.lean:49`) says the capability constructor is
never a reserved name, and its docstring says why it is there: "which
keeps the basis installs' head obligations vacuous by computation".
`CapsOk`'s two halves both carry `reservedBasisNames.contains T =
false`, and `projFnName_ne_reserved` closes the projection slot.  So
at a cons whose name *is* reserved, all four disequalities
`capsOk_cons_fresh` derives from the cons's kind come instead from
the name, and the body transposes unchanged — `capsOk_cons_basis`.

`nat_heads` is easier still: the guard reads exactly three names, so a
cons that is none of them moves neither the guard nor the three leaves
(`natHeads_cons_offNat`).  The `Nat` block supplies its own
`nat_heads` bespoke — that is the block where the guard *becomes*
true, and no back-transfer exists or should.

## THE GAP THAT WAS NOT ONE: `rec_rules` at a basis cons (CLOSED)

Recorded here as a wall, and **the record was wrong** — corrected at
ENDGAME D, mechanized rather than argued.

The wall read: `recRules_cons_fresh` needs `RecRule.ctor rl ≠ c₀.name`
for every rule of every *stored* recursor and derives it from the
cons's kind; at a basis cons the kind is exactly a `ctorInfo`; and
`EnvWF`'s `recInfo` clause (`Verify/EnvWF.lean:45-70`) records the
rhs's `constsResolve`, its level parameters, its bound-variable bound
and the nested pins' shape — never that `RecRule.ctor` resolves.  All
of that is accurate.  What it missed is that the fact does not have to
come from `EnvWF` at all: **`EnvS.rec_ctors`** (`RecCtorsStored`,
`Verify/EnvPreds.lean:64`, reachable as `mp.base2.rec_ctors`)
already says every stored recursor rule's constructor is itself
stored.  With the cons fresh, the disequality is immediate.

So `recRules_cons_fresh` **lost its `hnotctor` premise** rather than
gaining a hypothesis, and the row is reusable at every basis cons whose
kind is not a recursor.  A basis *recursor* cons still establishes its
own rules bespoke from `Interp/Value.lean`'s firing laws — that was
never a transport.

The general lesson, worth carrying: before recording an invariant gap,
check the *semantic* invariant bundle and not only the syntactic one.
`EnvS` carries five V-free fields (`basis_pinned`, `proj_ok`,
`rec_ctors`, and the pinned/reserved shape facts) that exist precisely
to supply facts `EnvWF` does not.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  IndCaps projFnName RecRule)


universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

/-! ## The P basis leaves are pinned FOR FREE

The obvious reading of the basis bill is that the P tier needs its own
"basis constants are valued by their direct pins" field, mirroring
`EnvS.basis_pinned`.  **It does not**, and the reason is one line of
`AnnotTerm.erase`'s definition: the erasure is structural and maps
`.const` to `.const` and *nothing else* to `.const`.  So
`EnvModel.acval_erase` turns v1's equation `cval n ψ = .const c us`
into the `AnnotTerm` equation `acval n ψ = .const c us` outright.

Every downstream basis obligation reads the leaf through this — the
type readings are `BConst.typeAV` towers over the *pinned* leaves, and
`BasisOk.lean`'s `bval2_mem_*` memberships are stated at exactly those
towers.  Recording it here because the missing bridge between the
checker's pinned `ConstantInfo` blocks and the TT `BConst` alphabet is
the basis tier's structural crux, and this is its P half. -/

/-- **A stored reserved-basis constant's annotated leaf is its direct
pin.**  From `EnvS.basis_pinned` and `acval_erase`, by injectivity of
`erase` at a constant head. -/
theorem acval_basis_pinned {m : EnvModel V env}
    {n : Name} {ci : ConstantInfo} (hf : env.find? n = some ci)
    (hres : ConLeche.reservedBasisNames.contains n = true)
    {c : ConLeche.Term.BConst} {us : List Nat} {ψ : Name → Nat}
    (hd : ConLeche.Verify.pinnedStructT n ψ
      = some (Term.const c us)) :
    m.acval n ψ = .const c us := by
  have h1 := (m.basis_pinned n ci hf hres).2 _ ψ hd
  have h2 := m.acval_erase n ψ
  rw [h1] at h2
  cases hh : m.acval n ψ with
  | const c' us' =>
    rw [hh] at h2
    simp only [ConLeche.Semantics.AnnotTerm.erase, Term.const.injEq] at h2
    rw [h2.1, h2.2]
  | _ => rw [hh] at h2; exact nomatch h2

/-- **Every pinned basis constant carries a reserved name, except the
pair's two projections.**  So the side condition `capsOk_cons_basis`
takes is free at every cons of `BasisStepPB` — by computation, which
is the point of `reservedBasisNames` being a closed list.

The exception is not a gap: `pairFstA`/`pairSndA` are `.projInfo`
heads (`Kernel/Basis/PSigma.lean:326`), a kind that is neither
`indInfo`, `ctorInfo` nor `recInfo`, so those two conses discharge
`caps_ok` through the *existing* `capsOk_cons_fresh` and never reach
the reserved-name route.  Between the two lemmas every basis cons is
covered. -/
theorem basis_declsA_reserved (kind : ConLeche.BasisKind) :
    ∀ ci ∈ kind.declsA,
      (match ci with
       | .projInfo _ => true
       | _ => ConLeche.reservedBasisNames.contains ci.name) = true := by
  cases kind <;> decide

/-- **`nat_heads` at a cons that is none of the three literal
heads.**  The guard reads `natName`, `natZeroName` and `natSuccName`
and nothing else, so a cons named otherwise moves neither the guard
nor the three leaves — the basis blocks other than `Nat` discharge
their obligation here, and so would any inductive-kind cons.  (The
`Nat` block itself is where the guard *becomes* true; it supplies
`nat_heads` bespoke, and no back-transfer exists.) -/
theorem natHeads_cons_offNat (mp : EnvModelM V μ env)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    (hnN : c₀.name ≠ natName) (hnZ : c₀.name ≠ natZeroName)
    (hnS : c₀.name ≠ natSuccName)
    (m2 : EnvModel V ⟨c₀ :: env.consts⟩)
    (hacval : m2.acval = acvalWith mp.base2.acval c₀.name A)
    (φ : Name → Nat) : NatHeads m2 φ := by
  intro hg ρ
  rw [hacval]
  -- the three lookups are the prefix's, so the guard reflects
  have hfind : ∀ p : Name, c₀.name ≠ p →
      (⟨c₀ :: env.consts⟩ : Env).find? p = env.find? p := by
    intro p hp
    show List.find? _ (c₀ :: env.consts) = _
    rw [List.find?_cons_of_neg (by simpa using hp)]
    rfl
  have hgold : ConLeche.natLitSupported env = true := by
    simp only [ConLeche.natLitSupported, Bool.and_eq_true] at hg ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hg
    rw [hfind _ hnN] at h1
    rw [hfind _ hnZ] at h2
    rw [hfind _ hnS] at h3
    exact ⟨⟨h1, h2⟩, h3⟩
  have e1 : acvalWith mp.base2.acval c₀.name A natZeroName
      = mp.base2.acval natZeroName :=
    acvalWith_ne (fun h => hnZ h.symm)
  have e2 : acvalWith mp.base2.acval c₀.name A natSuccName
      = mp.base2.acval natSuccName :=
    acvalWith_ne (fun h => hnS h.symm)
  have e3 : acvalWith mp.base2.acval c₀.name A natName
      = mp.base2.acval natName :=
    acvalWith_ne (fun h => hnN h.symm)
  have := mp.nat_heads φ hgold ρ
  simpa only [e1, e2, e3] using this

/-- **The stored family descends past a *reserved-named* cons.**
`etaFamilyStored_descend`'s twin, with all four disequalities taken
from the name rather than from the kind: the law's own
`reservedBasisNames.contains T = false` premise separates the former,
`EtaFamilyStored`'s name-only conjunct separates the capability
constructor, and `projFnName_ne_reserved` separates every projection
slot. -/
theorem etaFamilyStored_descend_reserved {c₀ : ConstantInfo} {T : Name}
    {cvT : ConstantVal} {caps : IndCaps}
    (hres₀ : ConLeche.reservedBasisNames.contains c₀.name = true)
    (hresT : ConLeche.reservedBasisNames.contains T = false)
    (hf : (⟨c₀ :: env.consts⟩ : Env).find? T = some (.indInfo cvT caps))
    (hfam : ConLeche.EtaFamilyStored ⟨c₀ :: env.consts⟩ T caps) :
    env.find? T = some (.indInfo cvT caps) ∧
      ConLeche.EtaFamilyStored env T caps ∧
      T ≠ c₀.name ∧ caps.etaCtor ≠ c₀.name ∧
      ∀ j, j < caps.etaFields → projFnName T j ≠ c₀.name := by
  obtain ⟨hCres, ⟨cvC, hfC⟩, hfP⟩ := hfam
  have hnT : T ≠ c₀.name := fun hh => by rw [hh, hres₀] at hresT
                                         exact nomatch hresT
  have hnC : caps.etaCtor ≠ c₀.name := fun hh => by
    rw [hh, hres₀] at hCres; exact nomatch hCres
  have hnP : ∀ j, j < caps.etaFields → projFnName T j ≠ c₀.name :=
    fun _ _ => projFnName_ne_reserved hres₀
  have hdown : ∀ n : Name, n ≠ c₀.name →
      (⟨c₀ :: env.consts⟩ : Env).find? n = env.find? n := by
    intro n hn
    rw [ConLeche.Env.find?_cons, if_neg (fun hh => hn hh.symm)]
  refine ⟨by rwa [hdown _ hnT] at hf, ⟨hCres, ⟨cvC, ?_⟩, ?_⟩,
    hnT, hnC, hnP⟩
  · rwa [hdown _ hnC] at hfC
  · intro j hj
    obtain ⟨cv2, mI2, rP2, rules2, hf2⟩ := hfP j hj
    rw [hdown _ (hnP j hj)] at hf2
    exact ⟨cv2, mI2, rP2, rules2, hf2⟩

/-- **`CapsOk` at a fresh cons whose name is reserved** —
`capsOk_cons_fresh`'s basis twin.  Every basis block's constant is a
reserved name (`BasisKind.declsA` ⊆ `reservedBasisNames`), and both
`CapsOk` halves are premised on a *non*-reserved family, so no
stored family can be completed here and the law's leaves are all
prefix leaves. -/
theorem capsOk_cons_basis (mp : EnvModelM V μ env)
    (hprev : CapsOk mp.base2)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none)
    (hntc : ConsCrossEnv env c₀)
    (hres₀ : ConLeche.reservedBasisNames.contains c₀.name = true)
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith mp.base2.acval c₀.name A) :
    CapsOk m₂ := by
  constructor
  · -- the η half
    intro T cvT caps hf hcape hres hfam φ' us hlen
    obtain ⟨hfE, hfam₀, hnT, hnC, hnP⟩ :=
      etaFamilyStored_descend_reserved hres₀ hres hf hfam
    obtain ⟨TVa, hTVa, hokTVa, hlaw⟩ :=
      hprev.1 T cvT caps hfE hcape hres hfam₀ φ' us hlen
    refine ⟨TVa, ?_, hokTVa, ?_⟩
    · rw [hac]
      exact denoteMeta_cons_mono hfresh
        ((hntc.typeOf hfE).instantiateLevelParams _ _) _ 0
        (constsBound_instType mp.base2.wf
          (ConLeche.Semantics.Env.find?_mem hfE) us) hTVa
    · intro ρ ts rest x hlents hfit hmem
      rw [hac, acvalWith_ne hnT] at hmem
      have hfab : etaFabArgsV
            (fun n => interp V ρ
              (m₂.acval n (Level.substFn φ' cvT.levelParams us)))
            T ts x caps.etaFields
          = etaFabArgsV
            (fun n => interp V ρ
              (mp.base2.acval n (Level.substFn φ' cvT.levelParams us)))
            T ts x caps.etaFields := by
        unfold etaFabArgsV projSpines
        refine congrArg _ (List.map_congr_left fun j hj => ?_)
        dsimp only
        rw [hac, acvalWith_ne (hnP j (List.mem_range.mp hj))]
      rw [hfab, hac, acvalWith_ne hnC]
      exact hlaw ρ ts rest x hlents hfit hmem
  · -- the unit-like half: one leaf to move, the disequality off the
    -- law's own non-reserved premise
    intro T cvT caps hf hcapu hres φ' us hlen
    have hnT : T ≠ c₀.name := fun hh => by
      rw [hh, hres₀] at hres; exact nomatch hres
    have hfE : env.find? T = some (.indInfo cvT caps) := by
      rw [ConLeche.Env.find?_cons, if_neg (fun hh => hnT hh.symm)] at hf
      exact hf
    obtain ⟨TVa, hTVa, hokTVa, hlaw⟩ :=
      hprev.2 T cvT caps hfE hcapu hres φ' us hlen
    refine ⟨TVa, ?_, hokTVa, ?_⟩
    · rw [hac]
      exact denoteMeta_cons_mono hfresh
        ((hntc.typeOf hfE).instantiateLevelParams _ _) _ 0
        (constsBound_instType mp.base2.wf
          (ConLeche.Semantics.Env.find?_mem hfE) us) hTVa
    · intro ρ ts rest x y hlents hfit hx hy
      rw [hac, acvalWith_ne hnT] at hx hy
      exact hlaw ρ ts rest x y hlents hfit hx hy

end ConLeche.Model
