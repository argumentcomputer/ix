module

public import ConLeche.Model.IndMember
import ConLeche.Verify.Extend.Iota
import ConLeche.Verify.Extend.Ind
public section

/-!
# `caps_ok` at a member cons: the split, and the two live rows (task #161, IND TIER)

v1's `memberEtaS` (`Install/IndMembersS.lean`) records the finding
this file transposes:

> the eta head **is** live — an `etaFields = 0` structure completes
> inside the member fold — and the three rows that are not live die on
> facts the fold can carry, which is what `EtaFamiliesClosedO`,
> `BlockEtaPinned` and `BlockProjFresh` are.

That argument is entirely about *what is stored*, so it is V-free and
`memberEtaSplit` below states it as such: at a member cons, every
η-capable stored family either **descends untouched** (in which case
the four disequalities the transport needs come with it) or **is a
block former at `etaFields = 0`** carrying the fold's η pins.  One
disjunction, proved once, consumed at both tiers.

`capsOk_cons_member` is then the P row: the descending case is
`capsOk_cons_fresh`'s transport verbatim (the same
`denoteMeta_cons_fresh_mono` forward crossing and the same three
`acvalWith_ne` leaf moves), and what is left as premises is exactly
two laws —

* `EtaLaw` for a block former at `etaFields = 0`, and
* `UnitLaw` for the cons's own former,

which are `etaLawKeyS`/`unitLawKeyS`'s conclusions one currency over.
**No other `caps_ok` obligation survives a member cons**, and the
unit half needs no family premise at all (the ratified repair), so
its split is two-way where the eta half's is four-way.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics ConLeche.SetModel
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  IndCaps ReducibilityHint)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

/-- **The member cons's η split** (v1's `memberEtaS`, first half,
V-free).  Either the family descends untouched, or `T` is a block
former with no projection fields. -/
theorem memberEtaSplit {blockNames : List Name}
    {c₀ : ConstantInfo} {cvA : ConstantVal}
    (hfresh : env.find? c₀.name = none)
    (hc₀cv : c₀.toConstantVal = cvA) (hc₀name : c₀.name = cvA.name)
    (hpshape0 : c₀.name.isProjFnShape = false)
    (hbn : blockNames.contains cvA.name = true)
    (hpins : ∀ caps, c₀ = .indInfo cvA caps →
      ConLeche.EtaPins μ env cvA.name cvA.levelParams caps ∧
        (caps.eta = true → blockNames.contains caps.etaCtor = true) ∧
        (caps.eta = true → 0 < caps.etaFields →
          env.find? (ConLeche.projFnName cvA.name 0) = none))
    (hEC : ConLeche.EtaFamiliesClosedO blockNames env)
    (hBP : ConLeche.BlockEtaPinned μ blockNames env)
    {T : Name} {cvT : ConstantVal} {caps : IndCaps}
    (hfT : (⟨c₀ :: env.consts⟩ : Env).find? T
      = some (.indInfo cvT caps))
    (hcape : caps.eta = true)
    (hnresT : ConLeche.reservedBasisNames.contains T = false)
    (hfam : ConLeche.EtaFamilyStored ⟨c₀ :: env.consts⟩ T caps) :
    (env.find? T = some (.indInfo cvT caps) ∧
        ConLeche.EtaFamilyStored env T caps ∧
        T ≠ c₀.name ∧ caps.etaCtor ≠ c₀.name ∧
        ∀ j, j < caps.etaFields → ConLeche.projFnName T j ≠ c₀.name) ∨
      (ConLeche.EtaPins μ env T cvT.levelParams caps ∧
        caps.etaFields = 0 ∧ blockNames.contains T = true ∧
        blockNames.contains caps.etaCtor = true) := by
  have hdown : ∀ n : Name, n ≠ c₀.name →
      (⟨c₀ :: env.consts⟩ : Env).find? n = env.find? n := by
    intro n hn
    rw [ConLeche.Env.find?_cons, if_neg (fun hh => hn hh.symm)]
  -- no projection slot is a member's name
  have hnP : ∀ j, j < caps.etaFields →
      ConLeche.projFnName T j ≠ c₀.name :=
    fun _ _ => ConLeche.projFnName_ne_of_shape hpshape0
  -- `etaFields = 0` whenever the projection fold has not run
  have hzero : ∀ hprojF : 0 < caps.etaFields →
        env.find? (ConLeche.projFnName T 0) = none,
      caps.etaFields = 0 := by
    intro hprojF
    rcases Nat.eq_zero_or_pos caps.etaFields with h | h
    · exact h
    · exfalso
      obtain ⟨cvp, mI, rP, rules, hfp⟩ := hfam.2.2 0 h
      rw [hdown _ (hnP 0 h), hprojF h] at hfp
      exact nomatch hfp
  by_cases hT0 : T = c₀.name
  · -- the cons is the former itself
    right
    have hc₀ : c₀ = .indInfo cvT caps := by
      rw [hT0, ConLeche.Env.find?_cons_self] at hfT
      exact Option.some.inj hfT
    have hcvT : cvT = cvA := by rw [hc₀] at hc₀cv; exact hc₀cv
    subst hcvT
    obtain ⟨hp, hbc, hj⟩ := hpins caps (by rw [hc₀])
    have hTn : T = cvT.name := by rw [hT0, hc₀name]
    refine ⟨?_, hzero ?_, ?_, hbc hcape⟩
    · rw [hTn]; exact hp
    · rw [hTn]; exact hj hcape
    · rw [hT0, hc₀name]; exact hbn
  · have hfE : env.find? T = some (.indInfo cvT caps) := by
      rwa [hdown _ hT0] at hfT
    by_cases hC0 : caps.etaCtor = c₀.name
    · -- the cons is the family's capability constructor
      right
      by_cases hTb : blockNames.contains T = true
      · obtain ⟨hp, hbc, hj⟩ := hBP T cvT caps hTb hfE hcape
        exact ⟨hp, hzero hj, hTb, hbc⟩
      · exfalso
        obtain ⟨cvC, hfC⟩ :=
          hEC T cvT caps hfE hcape hnresT (by simpa using hTb)
        rw [hC0, hfresh] at hfC
        exact nomatch hfC
    · -- the family descends untouched
      left
      obtain ⟨hCres, ⟨cvC, hfC⟩, hfP⟩ := hfam
      refine ⟨hfE, ⟨hCres, ⟨cvC, by rwa [hdown _ hC0] at hfC⟩, ?_⟩,
        hT0, hC0, hnP⟩
      intro j hj
      obtain ⟨cv2, mI2, rP2, rules2, hf2⟩ := hfP j hj
      rw [hdown _ (hnP j hj)] at hf2
      exact ⟨cv2, mI2, rP2, rules2, hf2⟩

/-- **`caps_ok` at a member cons.**  The descending case transports;
what remains as premises is exactly the two live laws. -/
theorem capsOk_cons_member (mp : EnvModelM V μ env)
    {blockNames : List Name} {c₀ : ConstantInfo} {cvA : ConstantVal}
    {A : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none)
    (hntc : ∀ entry, c₀ ≠ .projInfo entry)
    (hc₀cv : c₀.toConstantVal = cvA) (hc₀name : c₀.name = cvA.name)
    (hpshape0 : c₀.name.isProjFnShape = false)
    (hbn : blockNames.contains cvA.name = true)
    (hpins : ∀ caps, c₀ = .indInfo cvA caps →
      ConLeche.EtaPins μ env cvA.name cvA.levelParams caps ∧
        (caps.eta = true → blockNames.contains caps.etaCtor = true) ∧
        (caps.eta = true → 0 < caps.etaFields →
          env.find? (ConLeche.projFnName cvA.name 0) = none))
    (hEC : ConLeche.EtaFamiliesClosedO blockNames env)
    (hBP : ConLeche.BlockEtaPinned μ blockNames env)
    -- the live η row: a block former at `etaFields = 0`
    (hetaLive : ∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
      (⟨c₀ :: env.consts⟩ : Env).find? T = some (.indInfo cvT caps) →
      caps.eta = true → ConLeche.reservedBasisNames.contains T = false →
      ConLeche.EtaPins μ env T cvT.levelParams caps →
      caps.etaFields = 0 →
      blockNames.contains T = true →
      blockNames.contains caps.etaCtor = true →
      ConLeche.EtaFamilyStored ⟨c₀ :: env.consts⟩ T caps →
      ∀ m₂ : EnvModel V ⟨c₀ :: env.consts⟩,
        m₂.acval = acvalWith mp.base2.acval c₀.name A →
        ∀ φ' : Name → Nat, EtaLaw m₂ φ' T cvT caps)
    -- the live unit row: the cons's own former (the pins travel with
    -- it — see `MemberUnitLaw`'s note; `hpins` is right here)
    (hunitLive : ∀ (cvT : ConstantVal) (caps : IndCaps),
      c₀ = .indInfo cvT caps → caps.unitlike = true →
      ConLeche.reservedBasisNames.contains c₀.name = false →
      ConLeche.EtaPins μ env cvA.name cvA.levelParams caps →
      ∀ m₂ : EnvModel V ⟨c₀ :: env.consts⟩,
        m₂.acval = acvalWith mp.base2.acval c₀.name A →
        ∀ φ' : Name → Nat, UnitLaw m₂ φ' c₀.name cvT caps)
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith mp.base2.acval c₀.name A) :
    CapsOk m₂ := by
  constructor
  · -- the η half
    intro T cvT caps hf hcape hres hfam φ'
    rcases memberEtaSplit hfresh hc₀cv hc₀name hpshape0 hbn hpins hEC
        hBP hf hcape hres hfam with
      ⟨hfE, hfam₀, hnT, hnC, hnP⟩ | ⟨hp, h0, hbT, hbC⟩
    · -- the transport (`capsOk_cons_fresh`'s η branch verbatim)
      intro us hlen
      obtain ⟨TVa, hTVa, hokTVa, hlaw⟩ :=
        mp.caps_ok.1 T cvT caps hfE hcape hres hfam₀ φ' us hlen
      refine ⟨TVa, ?_, hokTVa, ?_⟩
      · rw [hac]
        exact denoteMeta_cons_fresh_mono hfresh hntc _ 0 _
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
                (mp.base2.acval n
                  (Level.substFn φ' cvT.levelParams us)))
              T ts x caps.etaFields := by
          unfold etaFabArgsV projSpines
          refine congrArg _ (List.map_congr_left fun j hj => ?_)
          dsimp only
          rw [hac, acvalWith_ne (hnP j (List.mem_range.mp hj))]
        rw [hfab, hac, acvalWith_ne hnC]
        exact hlaw ρ ts rest x hlents hfit hmem
    · exact hetaLive T cvT caps hf hcape hres hp h0 hbT hbC hfam m₂ hac φ'
  · -- the unit half: two ways, and no family premise
    intro T cvT caps hf hcapu hres φ'
    by_cases hT0 : T = c₀.name
    · subst hT0
      have hc₀ : c₀ = .indInfo cvT caps := by
        rw [ConLeche.Env.find?_cons_self] at hf
        exact Option.some.inj hf
      have hcvT : cvT = cvA := by rw [hc₀] at hc₀cv; exact hc₀cv
      exact hunitLive cvT caps hc₀ hcapu hres
        (hpins caps (by rw [hc₀, hcvT])).1 m₂ hac φ'
    · have hfE : env.find? T = some (.indInfo cvT caps) := by
        rw [ConLeche.Env.find?_cons, if_neg (fun hh => hT0 hh.symm)] at hf
        exact hf
      intro us hlen
      obtain ⟨TVa, hTVa, hokTVa, hlaw⟩ :=
        mp.caps_ok.2 T cvT caps hfE hcapu hres φ' us hlen
      refine ⟨TVa, ?_, hokTVa, ?_⟩
      · rw [hac]
        exact denoteMeta_cons_fresh_mono hfresh hntc _ 0 _
          (constsBound_instType mp.base2.wf
            (ConLeche.Semantics.Env.find?_mem hfE) us) hTVa
      · intro ρ ts rest x y hlents hfit hmx hmy
        rw [hac, acvalWith_ne hT0] at hmx hmy
        exact hlaw ρ ts rest x y hlents hfit hmx hmy

end ConLeche.Model
