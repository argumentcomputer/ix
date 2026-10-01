module

public import ConLeche.Model.IndCaps

public section

/-!
# `caps_ok` at a projection-function cons (task #161, IND TIER part 3, step 5)

Part 1's finding 6 said this row exists and no bill had listed it:
`EtaFamilyStored` mentions **three** kinds — `indInfo` (the former),
`ctorInfo` (the capability constructor) and **`recInfo`, a projection
slot** — so installing a projection function can *complete* a family
that was not previously stored, and `capsOk_cons_fresh` (which needs
`hnotrec`) cannot descend past it.

This file is that row's split, and the headline is that it is
**cheaper than the member cons's, not dearer**.

## The disequalities are free here, by kind

`memberEtaSplit` had to work for its four disequalities: a member cons
can be a family's former *or* its capability constructor, so the split
is four-way and two of its branches are discharged only by importing
the fold's own closure facts (`EtaFamiliesClosedO`, `BlockEtaPinned`).

A projection-function cons stores a **`recInfo`**, and that single
fact kills both branches outright:

* `T ≠ c₀.name` — if they were equal the family's own lookup would
  return the cons, i.e. a `recInfo`, where `CapsOk`'s premise says
  `indInfo`;
* `caps.etaCtor ≠ c₀.name` — same argument at `EtaFamilyStored`'s
  second conjunct, which says `ctorInfo`.

So neither closure fact is needed, no `isProjFnShape` side condition
is needed, and the split is **two-way**: either every projection slot
of the family misses the cons — and the family descends untouched —
or exactly one slot hits it, and then `projFnName_inj` identifies the
family as the cons's own `T` and the slot as its own index.

This is part 1's "by kind or by non-reservedness" practice in the
third of its three positions, and it is the reason step 5 survives
the part-3 wall: nothing here reads a comparison the checker ran.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics ConLeche.SetModel
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  IndCaps)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

/-- **The projection cons's η split** (`memberEtaSplit`'s twin at a
`recInfo` head, V-free).  Either the family descends untouched — with
the three disequalities the transport needs — or the cons completes
it, at the cons's own former and field index. -/
theorem projEtaSplit {c₀ : ConstantInfo} {T₀ : Name} {i : Nat}
    (hc₀name : c₀.name = ConLeche.projFnName T₀ i)
    (hc₀rec : ∃ cv mI rP rules, c₀ = .recInfo cv mI rP rules)
    {T : Name} {cvT : ConstantVal} {caps : IndCaps}
    (hfT : (⟨c₀ :: env.consts⟩ : Env).find? T
      = some (.indInfo cvT caps))
    (hfam : ConLeche.EtaFamilyStored ⟨c₀ :: env.consts⟩ T caps) :
    (env.find? T = some (.indInfo cvT caps) ∧
        ConLeche.EtaFamilyStored env T caps ∧
        T ≠ c₀.name ∧ caps.etaCtor ≠ c₀.name ∧
        ∀ j, j < caps.etaFields → ConLeche.projFnName T j ≠ c₀.name) ∨
      (T = T₀ ∧ i < caps.etaFields) := by
  obtain ⟨cvr, mIr, rPr, rulesr, hc₀eq⟩ := hc₀rec
  have hdown : ∀ n : Name, n ≠ c₀.name →
      (⟨c₀ :: env.consts⟩ : Env).find? n = env.find? n := by
    intro n hn
    rw [ConLeche.Env.find?_cons, if_neg (fun hh => hn hh.symm)]
  -- the former is not the cons: the cons is a `recInfo`
  have hT0 : T ≠ c₀.name := by
    intro hh
    rw [hh, ConLeche.Env.find?_cons_self, hc₀eq] at hfT
    exact nomatch hfT
  -- the capability constructor is not the cons: same argument
  have hC0 : caps.etaCtor ≠ c₀.name := by
    intro hh
    obtain ⟨-, ⟨cvC, hfC⟩, -⟩ := hfam
    rw [hh, ConLeche.Env.find?_cons_self, hc₀eq] at hfC
    exact nomatch hfC
  by_cases hhit : ∃ j, j < caps.etaFields ∧
      ConLeche.projFnName T j = c₀.name
  · -- the cons completes the family: identify it
    right
    obtain ⟨j, hj, hjeq⟩ := hhit
    rw [hc₀name] at hjeq
    obtain ⟨hTT, hij⟩ := ConLeche.projFnName_inj hjeq
    exact ⟨hTT, hij ▸ hj⟩
  · -- the family descends untouched
    left
    have hnP : ∀ j, j < caps.etaFields →
        ConLeche.projFnName T j ≠ c₀.name := by
      intro j hj hh
      exact hhit ⟨j, hj, hh⟩
    obtain ⟨hCres, ⟨cvC, hfC⟩, hfP⟩ := hfam
    refine ⟨by rwa [hdown _ hT0] at hfT,
      ⟨hCres, ⟨cvC, by rwa [hdown _ hC0] at hfC⟩, ?_⟩, hT0, hC0, hnP⟩
    intro j hj
    obtain ⟨cv2, mI2, rP2, rules2, hf2⟩ := hfP j hj
    rw [hdown _ (hnP j hj)] at hf2
    exact ⟨cv2, mI2, rP2, rules2, hf2⟩

/-- **`caps_ok` at a projection-function cons.**  The descending case
is `capsOk_cons_fresh`'s transport verbatim — the same
`denoteMeta_cons_fresh_mono` forward crossing and the same three
`acvalWith_ne` leaf moves — so what is left as a premise is exactly
the one live law: `EtaLaw` for the family the cons *completes*.

The unit half needs no split at all.  A `recInfo` cons is not an
`indInfo`, so `CapsOk`'s unit premise `find? T = some (.indInfo …)`
descends by kind at once, and — post-repair — the unit half carries no
family premise to re-establish. -/
theorem capsOk_cons_proj (mp : EnvModelM V μ env)
    (hprev : CapsOk mp.base2)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm} {T₀ : Name} {i : Nat}
    (hfresh : env.find? c₀.name = none)
    (hc₀name : c₀.name = ConLeche.projFnName T₀ i)
    (hc₀rec : ∃ cv mI rP rules, c₀ = .recInfo cv mI rP rules)
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith mp.base2.acval c₀.name A)
    -- the one live row: the family this cons completes
    (hcomplete : ∀ (cvT : ConstantVal) (caps : IndCaps),
      (⟨c₀ :: env.consts⟩ : Env).find? T₀ = some (.indInfo cvT caps) →
      caps.eta = true → i < caps.etaFields →
      ConLeche.reservedBasisNames.contains T₀ = false →
      ConLeche.EtaFamilyStored ⟨c₀ :: env.consts⟩ T₀ caps →
      ∀ φ' : Name → Nat, EtaLaw m₂ φ' T₀ cvT caps) :
    CapsOk m₂ := by
  have hnotind : ∀ cv caps, c₀ ≠ .indInfo cv caps := by
    obtain ⟨cvr, mIr, rPr, rulesr, rfl⟩ := hc₀rec
    intro cv caps h
    exact nomatch h
  have hntc : ∀ entry, c₀ ≠ .projInfo entry := by
    obtain ⟨cvr, mIr, rPr, rulesr, rfl⟩ := hc₀rec
    intro entry h
    exact nomatch h
  constructor
  · -- the η half
    intro T cvT caps hf hcape hres hfam φ'
    rcases projEtaSplit hc₀name hc₀rec hf hfam with
      ⟨hfE, hfam₀, hnT, hnC, hnP⟩ | ⟨rfl, hlt⟩
    · -- descends: the transport, verbatim
      intro us hlen
      obtain ⟨TVa, hTVa, hokTVa, hlaw⟩ :=
        hprev.1 T cvT caps hfE hcape hres hfam₀ φ' us hlen
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
                (mp.base2.acval n (Level.substFn φ' cvT.levelParams us)))
              T ts x caps.etaFields := by
          unfold etaFabArgsV projSpines
          refine congrArg _ (List.map_congr_left fun j hj => ?_)
          dsimp only
          rw [hac, acvalWith_ne (hnP j (List.mem_range.mp hj))]
        rw [hfab, hac, acvalWith_ne hnC]
        exact hlaw ρ ts rest x hlents hfit hmem
    · -- completes: the live row
      exact hcomplete cvT caps hf hcape hlt hres hfam φ'
  · -- the unit-like half: the premise descends by kind
    intro T cvT caps hf hcapu hres φ'
    have hnT : T ≠ c₀.name := by
      intro hh
      rw [hh, ConLeche.Env.find?_cons_self] at hf
      exact hnotind cvT caps (Option.some.inj hf)
    have hfE : env.find? T = some (.indInfo cvT caps) := by
      rw [ConLeche.Env.find?_cons, if_neg (fun hh => hnT hh.symm)] at hf
      exact hf
    intro us hlen
    obtain ⟨TVa, hTVa, hokTVa, hlaw⟩ :=
      hprev.2 T cvT caps hfE hcapu hres φ' us hlen
    refine ⟨TVa, ?_, hokTVa, ?_⟩
    · rw [hac]
      exact denoteMeta_cons_fresh_mono hfresh hntc _ 0 _
        (constsBound_instType mp.base2.wf
          (ConLeche.Semantics.Env.find?_mem hfE) us) hTVa
    · intro ρ ts rest x y hlents hfit hmx hmy
      rw [hac, acvalWith_ne hnT] at hmx hmy
      exact hlaw ρ ts rest x y hlents hfit hmx hmy

end ConLeche.Model
