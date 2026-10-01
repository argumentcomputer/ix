module

public import ConLeche.Model.Caps

public section

/-!
# The fired modeled-iota contract across a fresh cons (task #161, iota
tier)

`recRules_cons_fresh`, the obligation every value-kind harvest
discharges for the new `EnvModelM` field `rec_rules`.  The statements
live in `Annot/EnvModelM.lean` beside `CapsOk` (the field must mention
them); this is the preservation half, `capsOk_cons_fresh`'s sibling.

## FINDING — every crossing is FORWARD; no equality-form transfer

The freeze anticipated that the law's reading *premises* (`TVa`,
`TVja`, and the `.nested` clause's `vpa`) would have to move
**backward** across the cons, through the equality-form
`denoteMeta_cons_fresh`, and flagged that as legal at value-kind conses
because the `noConfusion` pair supplies `LitGuardsAgree`.

Neither the backward transfer nor that justification is needed, and
the justification would not have held: the literal tier's seal I
already showed `LitGuardsAgree` is **refutable** at a value-kind cons
(a `def` named `String.ofList` completes string support and flips the
`str` half), which is exactly why `LitStabilityP` was deleted.  Only
the `nat` half is free from the `noConfusion` pair.

What makes the backward direction unnecessary is that the readings
sit in *premise* position, so the transfer they need is contravariant:

* `TVa`/`TVja` are ∀-bound premises, so instead of moving the given
  extension reading down, the proof produces the **prefix** reading
  from `EnvModelM.constType`, moves *that* forward
  (`denoteMeta_cons_fresh_mono`), and identifies the two by determinism —
  the `type_reads`/`type_wellDenotedV` idiom `declStep_preserves_of_cons` already uses
  three times;
* the `.nested` clause is itself a premise, so proving the prefix form
  of it *consumes* the extension form: a prefix pin reading is moved
  **forward** and fed to the hypothesis in hand.

So the whole preservation runs on `denoteMeta_cons_fresh_mono`, the only
crossing the campaign has ever shown to be honest, and no literal-tier
premise appears — matching what the literal tier's seal established
for the harvests.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  RecRule)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

/-- The reverse opening introduces no constants, so it preserves
prefix-boundedness (its opener annotations are `.sort .zero`). -/
theorem constsBound_openRev {env₀ : Env} {e : Expr}
    (h : ConstsBound env₀ e) :
    ∀ d n : Nat, ConstsBound env₀ (openRev d n e) := by
  intro d n
  induction n with
  | zero => exact h
  | succ n ih =>
    show ConstsBound env₀ ((openRev d n e).instantiate1
      (.fvar (d + n) (.sort .zero)) 0)
    exact ConstsBound.instantiate1 (by simp) _ 0 ih

/-- **The fired modeled-iota contract survives a fresh cons that is
not itself a recursor.**

The recursor disequality is the cons's kind.  The *constructor*
disequality was a second premise until ENDGAME D, and it is not
needed: `EnvS.rec_ctors` (`RecCtorsStored`, `Verify/EnvPreds.lean:64`)
says every stored recursor rule's constructor is itself **stored**, and
the cons is fresh — so `RecRule.ctor rl ≠ c₀.name` follows from the
environment invariant rather than from the cons's kind.  Dropping it is
what lets the **basis** tier use this lemma at its `indInfo`/`ctorInfo`
conses, where the kind premise is false (`Interp/BasisConsP.lean`'s
`rec_rules` row recorded that as a wall; it is not one).

A recursor cons with rules still establishes its *own* rules bespoke —
that is the firing-law work, not a transport.  A recursor cons with
**no** rules (`Empty.rec`) transports here unchanged, which is why the
premise is `rules = []` rather than "not a recursor". -/
theorem recRuleLaw_cons_prefix (mp : EnvModelM V μ env)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none)
    (hntc : ConsCrossEnv env c₀)
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith mp.base2.acval c₀.name A)
    (φ : Name → Nat) {n : Name} {cv : ConstantVal} {mI rP : Nat}
    {rules : List RecRule} (hnN : n ≠ c₀.name)
    (hfE : env.find? n = some (.recInfo cv mI rP rules))
    {rl : RecRule} (hmem : rl ∈ rules)
    (hfire : RecRule.fire rl ≠ .inert) :
    RecRuleLaw m₂ φ n cv mI rP rl := by
  obtain ⟨hrPle, hlaw0⟩ := mp.rec_rules φ n cv mI rP rules hfE rl hmem hfire
  refine ⟨hrPle, fun us hlen => ?_⟩
  obtain ⟨Ra, hRa0, hokRa, hpinsOk, hlaw⟩ := hlaw0 us hlen
  obtain ⟨-, -, -, -, -, hrec', -⟩ :=
    mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfE)
  obtain ⟨-, -, hRres, -, hnest⟩ := hrec' cv mI rP rules rfl rl hmem
  refine ⟨Ra, ?_, hokRa, ?_, ?_⟩
  · rw [hac]
    exact denoteMeta_cons_mono hfresh
      ((hntc.ruleRhs (ConLeche.Semantics.Env.find?_mem hfE) hmem).instantiateLevelParams
        _ _) _ 0
      (constsBound_of_constsResolve _ (by
        rw [ConLeche.Expr.constsResolve_instantiateLevelParams]
        exact hRres)) hRa0
  · -- the pins' carried readings, moved forward (the iota seal's
    -- ratified repair: the grading conjunct in the ∃-form crosses
    -- exactly as `Ra`'s does)
    intro lvls pins hn i hi
    obtain ⟨vpa, hvpa, hok⟩ := hpinsOk lvls pins hn i hi
    obtain ⟨-, -, hpinsWf, -⟩ := hnest lvls pins hn
    have hpinCR : ConLeche.Expr.constsResolve env (pins.getD i default)
        = true := by
      by_cases hilt : i < pins.length
      · obtain ⟨-, -, hres, -⟩ := hpinsWf _ (ConLeche.getD_mem hilt)
        exact hres
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
    refine ⟨vpa, ?_, ?_⟩
    · rw [hac]
      exact denoteMeta_cons_mono hfresh
        (((hntc.rulePinD (ConLeche.Semantics.Env.find?_mem hfE) hmem hn
          i).instantiateLevelParams _ _).openRev 0 rP) _ rP
        (constsBound_openRev (constsBound_of_constsResolve _ (by
          rw [ConLeche.Expr.constsResolve_instantiateLevelParams]
          exact hpinCR)) 0 rP) hvpa
    · -- the guarded grading (part-6 probe repair) crosses by the
      -- determinism trick on its contravariant type reading, exactly
      -- as the inner block's `TVa` does below
      intro ρ zs TVa restR hzl hzok hTVa hfit
      obtain ⟨TVa', hTVa', -, -⟩ :=
        mp.constType 0 n _ us hfE rfl (by exact hlen)
      obtain rfl : TVa' = TVa := by
        refine Option.some.inj (Eq.trans ?_ hTVa)
        rw [hac]
        exact (denoteMeta_cons_mono hfresh
          ((hntc.typeOf hfE).instantiateLevelParams _ _) _ 0
          (constsBound_instType mp.base2.wf
            (ConLeche.Semantics.Env.find?_mem hfE) us) hTVa').symm
      exact hok ρ zs TVa' restR hzl hzok hTVa' hfit
  · intro cvj cnP cnF hfcj usj ρ xs ys TVa TVja restR restC hxl hyl hujl
      hψ hplain hnested hpin hTVa hTVja hfitR hfitC
    -- **the environment invariant, not the cons's kind**: the rule's
    -- constructor is stored, and the cons is fresh
    have hnC : RecRule.ctor rl ≠ c₀.name := by
      obtain ⟨⟨cvj', cnP', cnF', hst⟩, -, -⟩ :=
        mp.base2.rec_ctors n cv mI rP rules hfE rl hmem
      intro hh
      rw [hh, hfresh] at hst
      exact nomatch hst
    have hfcjE : env.find? (RecRule.ctor rl)
        = some (.ctorInfo cvj cnP cnF) := by
      rw [ConLeche.Env.find?_cons, if_neg (fun hh => hnC hh.symm)] at hfcj
      exact hfcj
    -- the two stored types: produced at the prefix, moved forward,
    -- identified with the given extension readings by determinism
    obtain ⟨TVa', hTVa', -, -⟩ :=
      mp.constType 0 n _ us hfE rfl (by exact hlen)
    obtain rfl : TVa' = TVa := by
      refine Option.some.inj (Eq.trans ?_ hTVa)
      rw [hac]
      exact (denoteMeta_cons_mono hfresh
        ((hntc.typeOf hfE).instantiateLevelParams _ _) _ 0
        (constsBound_instType mp.base2.wf
          (ConLeche.Semantics.Env.find?_mem hfE) us) hTVa').symm
    obtain ⟨TVja', hTVja', -, -⟩ :=
      mp.constType 0 (RecRule.ctor rl) _ usj hfcjE rfl (by exact hujl)
    obtain rfl : TVja' = TVja := by
      refine Option.some.inj (Eq.trans ?_ hTVja)
      rw [hac]
      exact (denoteMeta_cons_mono hfresh
        ((hntc.typeOf hfcjE).instantiateLevelParams _ _) _ 0
        (constsBound_instType mp.base2.wf
          (ConLeche.Semantics.Env.find?_mem hfcjE) usj) hTVja').symm
    -- the `.nested` premise, contravariantly: a prefix pin reading is
    -- moved FORWARD and fed to the hypothesis in hand
    have hnested' : ∀ lvls pins, RecRule.fire rl = .nested lvls pins →
        ∀ i, i < RecRule.ctorParams rl →
        ∀ vpa : AnnotTerm,
          denoteMeta mp.base2.acval env φ rP
            (openRev 0 rP ((pins.getD i default).instantiateLevelParams
              cv.levelParams us)) = some vpa →
          interp V ρ (ys.getD i default)
            = interp V ρ (AnnotTerm.instRevChain (xs.take rP) vpa) := by
      intro lvls pins hn i hi vpa hvpa
      refine hnested lvls pins hn i hi vpa ?_
      obtain ⟨-, -, hpinsWf, -⟩ := hnest lvls pins hn
      have hpinCR : ConLeche.Expr.constsResolve env (pins.getD i default)
          = true := by
        by_cases hilt : i < pins.length
        · obtain ⟨-, -, hres, -⟩ := hpinsWf _ (ConLeche.getD_mem hilt)
          exact hres
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
          rfl
      rw [hac]
      exact denoteMeta_cons_mono hfresh
        (((hntc.rulePinD (ConLeche.Semantics.Env.find?_mem hfE) hmem hn
          i).instantiateLevelParams _ _).openRev 0 rP) _ rP
        (constsBound_openRev (constsBound_of_constsResolve _ (by
          rw [ConLeche.Expr.constsResolve_instantiateLevelParams]
          exact hpinCR)) 0 rP) hvpa
    -- the two leaves the conclusion mentions are the prefix's
    rw [hac, acvalWith_ne hnC] at hfitR
    rw [hac, acvalWith_ne hnN, acvalWith_ne hnC]
    exact hlaw cvj cnP cnF hfcjE usj ρ xs ys _ _ restR restC hxl hyl
      hujl hψ hplain hnested' hpin hTVa' hTVja' hfitR hfitC

/-- **The fired modeled-iota contract survives a fresh cons that is
not itself a recursor** — `recRuleLaw_cons_prefix` at every stored
row, the freshness supplying the disequality. -/
theorem recRules_cons_fresh (mp : EnvModelM V μ env)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none)
    (hntc : ConsCrossEnv env c₀)
    (hnotrec : ∀ cv mI rP rules, c₀ = .recInfo cv mI rP rules →
      rules = [])
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith mp.base2.acval c₀.name A)
    (φ : Name → Nat) : RecRules m₂ φ := by
  intro n cv mI rP rules hf rl hmem hfire
  -- the recursor is stored in the prefix: either the cons is not a
  -- recursor at all (the value kinds' `noConfusion`), or it is one
  -- with no rules (a basis recursor whose block installs its ι
  -- content elsewhere), and then `rl ∈ rules` is impossible
  have hnN : n ≠ c₀.name := by
    intro hh
    subst hh
    have hrl := hnotrec cv mI rP rules
      (Option.some.inj ((ConLeche.Env.find?_cons_self c₀ env).symm.trans hf))
    rw [hrl] at hmem
    exact nomatch hmem
  exact recRuleLaw_cons_prefix mp hfresh hntc m₂ hac φ hnN
    (by rw [ConLeche.Env.find?_cons, if_neg (fun hh => hnN hh.symm)] at hf
        exact hf) hmem hfire

/-- **The fired modeled-iota contract at a *recursor* cons.**  The
prefix rows are `recRuleLaw_cons_prefix` unchanged; the new
constant's own rows are the block's bespoke firing work, taken here as
a premise.  ENDGAME F's §3 established that all six basis recursors
owe theirs (`Empty.rec` alone has no rules and goes through
`recRules_cons_fresh`). -/
theorem recRules_cons_rec (mp : EnvModelM V μ env)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    {cv₀ : ConstantVal} {mI₀ rP₀ : Nat} {rules₀ : List RecRule}
    (hfresh : env.find? c₀.name = none)
    (hkind : c₀ = .recInfo cv₀ mI₀ rP₀ rules₀)
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith mp.base2.acval c₀.name A)
    (φ : Name → Nat)
    (hnew : ∀ rl ∈ rules₀, RecRule.fire rl ≠ .inert →
      RecRuleLaw m₂ φ c₀.name cv₀ mI₀ rP₀ rl) :
    RecRules m₂ φ := by
  intro n cv mI rP rules hf rl hmem hfire
  by_cases hnN : n = c₀.name
  · subst hnN
    have hself : c₀ = .recInfo cv mI rP rules :=
      Option.some.inj ((ConLeche.Env.find?_cons_self c₀ env).symm.trans hf)
    have heq : ConstantInfo.recInfo cv₀ mI₀ rP₀ rules₀
        = .recInfo cv mI rP rules := hkind.symm.trans hself
    injection heq with h1 h2 h3 h4
    subst h1; subst h2; subst h3; subst h4
    exact hnew rl hmem hfire
  · exact recRuleLaw_cons_prefix mp hfresh
      (fun _ heq => by rw [hkind] at heq; exact nomatch heq)
      m₂ hac φ hnN
      (by rw [ConLeche.Env.find?_cons, if_neg (fun hh => hnN hh.symm)] at hf
          exact hf) hmem hfire

/-! ## The tower projection law across a fresh cons (task #175 wiring, W5)

`TowerOk` (`Annot/EnvModelM.lean`) is keyed on the stored tower-backed
entries; a cons that is not itself a tower entry adds none, and every
stored row transports exactly as `recRuleLaw_cons_prefix`'s: the
lookups the law reads (the entry, the former, the constructor) are
prefix lookups, the two readings it carries (`Ta`, `TCa`) move
**forward** by `denoteMeta_cons_fresh_mono`, and the two leaves it
mentions (`acval T`, `acval entry.ctor`) are the prefix's by
`acvalWith_ne` — both names are stored, so neither is the fresh one.
The semantic clauses are then the prefix's verbatim. -/

/-- **A prefix tower entry's law crosses a cons**: the entry, its
former and its constructor are prefix lookups, their type readings
cross (the head's slot mentions none of them), and the two leaves the
laws read are the prefix's. -/
theorem towerEntryLaw_cons_prefix (mp : EnvModelM V μ env)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none)
    (hcross : ConsCrossEnv env c₀)
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith mp.base2.acval c₀.name A)
    (φ : Name → Nat) {T : Name} {i : Nat} {entry : ProjEntry}
    (hfP : env.findProj? T i = some entry) :
    TowerEntryLaw m₂ φ T i entry := by
  obtain ⟨tbl, hfP0, hi, hentry⟩ := ConLeche.Env.findProj?_some hfP
  obtain ⟨hsn, hidx, hlt, ⟨cvT, capsT, hfT, hlpsT⟩, hO5, cvC, hfC, hlpsC,
    hlaw, hetaL⟩ := mp.tower_ok φ T i entry hfP
  -- the two stored names are not the fresh one
  have hne : ∀ {n : Name} {ci : ConstantInfo}, env.find? n = some ci →
      n ≠ c₀.name := by
    intro n ci hn hh
    rw [hh, hfresh] at hn
    exact nomatch hn
  have hnT : T ≠ c₀.name := hne hfT
  have hnC : entry.ctor ≠ c₀.name := hne hfC
  refine ⟨hsn, hidx, hlt, ⟨cvT, capsT, ?_, hlpsT⟩, hO5, cvC, ?_, hlpsC,
    fun us hus => ?_, ?_⟩
  · rw [ConLeche.Env.find?_cons_of_isSome hfresh (by rw [hfT]; rfl)]; exact hfT
  · rw [ConLeche.Env.find?_cons_of_isSome hfresh (by rw [hfC]; rfl)]; exact hfC
  · obtain ⟨⟨Ta, hTa, hA⟩, ⟨TCa, hTCa, hB⟩⟩ := hlaw us hus
    refine ⟨⟨Ta, ?_, ?_⟩, ⟨TCa, ?_, ?_⟩⟩
    · -- the body telescope's reading crosses (task #175 S1): the
      -- table is a prefix lookup, its bodies resolve (`EnvWF`) and
      -- mention none of the head's slots
      rw [hac]
      refine denoteMeta_cons_mono hfresh ?_ _ 0 ?_ hTa
      · intro tbl' heq' j
        subst hentry
        exact Expr.NoProjAt.projTele _ _ _ _
          (Expr.NoProjAt.instantiateLevelParams _ _ _
            ((hcross.body hfP0 hi) tbl' heq' j))
      · refine constsBound_of_constsResolve _ ?_
        rw [ConLeche.projTele_constsResolve, ConLeche.Expr.constsResolve_instantiateLevelParams]
        exact (ConLeche.projEntry_body_wf mp.base2.wf hfP).2.2.1
    · intro hg ρ vs x rest hlen hokT hokx hmem hpeel
      rw [hac, acvalWith_ne hnT] at hokT hmem
      exact hA hg ρ vs x rest hlen hokT hokx hmem hpeel
    · -- the constructor type's reading crosses (task #175 W6): a
      -- prefix lookup's closed type
      rw [hac]
      exact denoteMeta_cons_mono hfresh
        ((hcross.typeOf hfC).instantiateLevelParams _ _) _ 0
        (constsBound_instType mp.base2.wf
          (ConLeche.Semantics.Env.find?_mem hfC) us) hTCa
    · intro hg ρ ys rest hlen hok hfit
      rw [hac, acvalWith_ne hnC] at hok ⊢
      exact hB hg ρ ys rest hlen hok hfit
  · -- (C) the η law crosses (task #175 W4c): the former's lookup is a
    -- prefix lookup, its type reading is closed, the leaves are prefix
    -- leaves
    intro cvT' capsT' hfT' us hus
    have hfT'' : env.find? T = some (.indInfo cvT' capsT') := by
      rw [ConLeche.Env.find?_cons_of_isSome hfresh (by rw [hfT]; rfl)] at hfT'
      exact hfT'
    obtain ⟨TVa, hTVa, hok, hlaw'⟩ := hetaL cvT' capsT' hfT'' us hus
    refine ⟨TVa, ?_, hok, ?_⟩
    · rw [hac]
      exact denoteMeta_cons_mono hfresh
        ((hcross.typeOf hfT'').instantiateLevelParams _ _) _ 0
        (constsBound_instType mp.base2.wf
          (ConLeche.Semantics.Env.find?_mem hfT'') us) hTVa
    · intro ρ ts rest x hlen hfit hmem
      rw [hac, acvalWith_ne hnT] at hmem
      rw [hac, acvalWith_ne hnC]
      exact hlaw' ρ ts rest x hlen hfit hmem

/-- **`TowerOk` at a fresh non-table cons**: every stored entry is a
prefix entry, and its law crosses. -/
theorem towerOk_cons_fresh (mp : EnvModelM V μ env)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none)
    (hcross : ConsCrossEnv env c₀)
    (hntc : ∀ tbl, c₀ ≠ .projInfo tbl)
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith mp.base2.acval c₀.name A)
    (φ : Name → Nat) : TowerOk m₂ φ := by
  intro T i entry hf
  -- the entry is a prefix entry: the head is not a table
  have hfP : env.findProj? T i = some entry := by
    obtain ⟨tbl, hf3, hi, rfl⟩ := ConLeche.Env.findProj?_some hf
    rw [ConLeche.Env.find?_cons] at hf3
    split at hf3
    · exact absurd (Option.some.inj hf3) (hntc tbl)
    · exact ConLeche.Env.findProj?_of_table hf3 hi
  exact towerEntryLaw_cons_prefix mp hfresh hcross m₂ hac φ hfP

/-- **`TowerOk` at a table cons** (task #175 W4c, module 4;
S1: one table per structure): the prefix entries' laws cross, and the
head's laws — one per field — are the install's own. -/
theorem towerOk_cons_tower (mp : EnvModelM V μ env)
    {tbl₀ : ProjTable} {A : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? (ConstantInfo.projInfo tbl₀).name = none)
    (hcross : ConsCrossEnv env (.projInfo tbl₀))
    (m₂ : EnvModel V ⟨.projInfo tbl₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith mp.base2.acval
      (ConstantInfo.projInfo tbl₀).name A)
    (hlaw : ∀ (φ : Name → Nat) (i : Nat), i < tbl₀.numFields →
      TowerEntryLaw m₂ φ tbl₀.structName i (tbl₀.entry i))
    (φ : Name → Nat) : TowerOk m₂ φ := by
  intro T i entry hf
  obtain ⟨tbl, hf3, hi, rfl⟩ := ConLeche.Env.findProj?_some hf
  rw [ConLeche.Env.find?_cons] at hf3
  split at hf3
  · next hn =>
    obtain rfl : tbl₀ = tbl :=
      ConstantInfo.projInfo.inj (Option.some.inj hf3)
    have hn' : ConLeche.projTableName tbl₀.structName = ConLeche.projTableName T := hn
    obtain rfl := ConLeche.projTableName_inj hn'
    exact hlaw φ i hi
  · exact towerEntryLaw_cons_prefix mp hfresh hcross m₂ hac φ
      (ConLeche.Env.findProj?_of_table hf3 hi)

end ConLeche.Model
