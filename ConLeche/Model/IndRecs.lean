module

import ConLeche.Semantics.IndBlockRun
public import ConLeche.Semantics.IndRecsCore
public import ConLeche.Model.Swap
import ConLeche.Model.IndMembers
import ConLeche.Model.Capstone
public section

/-!
# The recursor-group phase, P tier (task #161, IND TIER part 10)

`Install/IndRecsS.lean`'s **environment layer** at the reading.  The
law layer landed in part 9 (`iotaRule`/`iotaRules`); what remains,
and what this file is, is the `EnvModelM` construction that carries those
laws to the group's output environment:

* **provision** — `provisionRecsPM` (part 2) already installs the
  group rule-less *at both tiers*, so the self environment carries an
  `EnvModelM`, which is what the rule certificates' run route needs;
* **fire** — `iotaRules` at each provisioned recursor;
* **swap** — `EnvModelM.swapP`, with the group's `rec_rules` row assembled
  here.

**The fold is much smaller than v1's.**  `indRecsFoldS` threads seven
invariants because it must produce the swap data (`SwapShList`,
`SwapNResS`) and the `EnvWF`/`RecCtorsStored` inputs of `EnvS.swap`.
None of that is V-tier content: the P fold needs only the *rows*, so it
threads exactly one invariant — the per-recursor law at the fold's
accumulator — and takes the swap data from the v1 fold, which the
install runs anyway (`indRecsFoldS`, called here for `hswR` alone).

The `iotaRules` call's environment argument is the **base**
environment throughout (`IndRecsFoldR`'s own choice, task #148 T6), so
`FoldUpS envBase envSelf` and the `Eq` lookup are fixed across the
whole induction — the only per-step data are the block membership and
the provisioned entry's lookup.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics ConLeche.SetModel
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  RecRule IndCaps)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

/-- **One recursor's fired rows, at a fixed carrier** — the single
invariant the P fold threads.  `RuleFactsS`'s P residue: its syntactic
clauses are V-free and the v1 fold establishes them, so only the law
is here. -/
def RecLawsAt {env : Env} (m : EnvModel V env) (cv : ConstantVal)
    (mI rP : Nat) (rules : List RecRule) : Prop :=
  ∀ rl ∈ rules, RecRule.fire rl ≠ .inert →
    ∀ φ : Name → Nat, RecRuleLaw m φ cv.name cv mI rP rl

set_option maxHeartbeats 1600000 in
/-- **The provisioning and the install fold, run together at the
reading** (`indRecsFoldS`'s P half).  The conclusion is the single row
`EnvModelM.swapP` consumes: every recursor stored at the fold's output
either sits unchanged in the self environment — where `rec_rules`
already covers it — or carries the rules `iotaRules` fired. -/
theorem indRecsFold (hμ : μ.verifiedChecks = true) {F : Nat}
    {blockNames : List Name} {envSelf envBase : Env}
    (mp : EnvModelM V μ envSelf)
    (hIS : BlockInstalledTT blockNames envSelf mp.base2.cvalE)
    (hroT : RenameOk mp.base2.acval envSelf (fun n =>
      if blockNames.contains n then n.str "_model" else n))
    (hupB : FoldUpS envBase envSelf)
    (heqfB : envBase.find? eqName = some eqA) :
    ∀ (recs : List ConstantInfo) {envP envF env₃ : Env}
      {checked : List (ConstantVal × Nat × Nat × List RecRule)},
      (∀ (n : Name) (cv : ConstantVal) (mI rP : Nat)
        (rules : List RecRule),
        envF.find? n = some (.recInfo cv mI rP rules) →
        envSelf.find? n = some (.recInfo cv mI rP rules) ∨
        RecLawsAt mp.base2 cv mI rP rules) →
      (∀ ci ∈ recs, blockNames.contains ci.name = true) →
      ProvisionRecsRun μ F blockNames envP recs envSelf checked →
      IndRecsRun.IndRecsFoldRun μ F blockNames envBase envSelf
        envF checked env₃ →
      ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat)
        (rules : List RecRule),
        env₃.find? n = some (.recInfo cv mI rP rules) →
        envSelf.find? n = some (.recInfo cv mI rP rules) ∨
        RecLawsAt mp.base2 cv mI rP rules := by
  -- the four claims and the reads, at every assignment (`hμ` + `mp`)
  have hclaims := fun ψ =>
    checkSoundAt (V := V) hμ (Rules.RulesInputs.ofSem mp ψ) F
  have hdeq : ∀ ψ : Name → Nat, DefEqClaim μ mp.base2 ψ F :=
    fun ψ => (hclaims ψ).2.2.1
  have hinf : ∀ ψ : Name → Nat, InferClaim μ mp.base2 ψ F :=
    fun ψ => (hclaims ψ).2.2.2
  have hreadsP : ∀ ψ : Name → Nat, InferReads mp.base2 μ ψ F :=
    fun ψ => inferReads_of hμ (Rules.RulesInputs.ofSem mp ψ)
  intro recs
  induction recs with
  | nil =>
    intro envP envF env₃ checked hentF hbn hprov hfold
    obtain ⟨rfl, rfl⟩ := hprov
    subst hfold
    exact hentF
  | cons ci₀ rest ih =>
    intro envP envF env₃ checked hentF hbn hprov hfold
    obtain ⟨cvA, mI, rP, rules, rest', hciE, hmv, hprov', rfl⟩ := hprov
    obtain ⟨rules', hiot, hfold'⟩ := hfold
    obtain ⟨type', hcv, hcvAdef, -⟩ := id hmv
    have hnameA : cvA.name = ci₀.toConstantVal.name := by rw [hcvAdef]
    have hselfA : envSelf.find? cvA.name
        = some (.recInfo cvA mI rP []) :=
      provisionRecsRunS_mono rest hprov' _ _
        (Env.find?_cons_self (.recInfo cvA mI rP []) envP)
    have hbnA : blockNames.contains cvA.name = true := by
      rw [hnameA]; exact hbn ci₀ List.mem_cons_self
    -- this recursor's rules, fired
    have hfacts : RecLawsAt mp.base2 cvA mI rP rules' :=
      fun rl hrl hfire φ =>
        iotaRules mp hdeq hinf hreadsP rfl hroT hIS hupB hbnA hselfA
          heqfB 0 rules rules' hiot rl hrl hfire φ
    refine ih ?_ (fun ci hci => hbn ci (List.mem_cons_of_mem _ hci))
      hprov' hfold'
    intro n cv mI₀ rP₀ rules₀ hfx
    rw [Env.find?_cons] at hfx
    split at hfx
    · obtain ⟨rfl, rfl, rfl, rfl⟩ :=
        ConstantInfo.recInfo.inj (Option.some.inj hfx)
      exact Or.inr hfacts
    · exact hentF n cv mI₀ rP₀ rules₀ hfx

/-- `BlockAcvalInstalled` crosses the swap: the predicate reads the
environment only through "this name is stored", and a swap changes no
stored name. -/
theorem blockAcvalInstalled_swap {blockNames : List Name}
    {env₀ env₃ : Env} {acval : Name → (Name → Nat) → AnnotTerm}
    (hcg : ConLeche.SwapCongr env₀ env₃)
    (h : BlockAcvalInstalled blockNames env₀ acval) :
    BlockAcvalInstalled blockNames env₃ acval := by
  intro n hbn ci hf ψ
  have hs := hcg.isSomeEq n
  rw [hf] at hs
  rcases hf₀ : env₀.find? n with _ | ci₀
  · rw [hf₀] at hs; exact nomatch hs.symm
  · exact h n hbn ci₀ hf₀ ψ

set_option maxHeartbeats 1600000 in
/-- **The recursor-group phase, P tier**: provision, fire, swap.
The v1 carrier at the group's output is a premise — the install runs
`indRecsS` for it anyway, and taking it here keeps `EnvWF`,
`RecCtorsStored` and `RecRulesV` out of the P lane entirely. -/
theorem indRecs (hμ : μ.verifiedChecks = true)
    (hetaP : MemberEtaLaw V) (hunitP : MemberUnitLaw V) {F : Nat}
    {blockNames : List Name} {env₂ env₃ : Env}
    {recs : List ConstantInfo}
    (mp : EnvModelM V μ env₂)
    (hI : BlockInstalledTT blockNames env₂ mp.base2.cvalE)
    (hIA : BlockAcvalInstalled blockNames env₂ mp.base2.acval)
    (hbn : ∀ ci ∈ recs, blockNames.contains ci.name = true)
    (hall : ∀ n, blockNames.contains n = true →
      (env₂.find? n).isSome = true ∨ ∃ ci ∈ recs, ci.name = n)
    (hEC : ConLeche.EtaFamiliesClosedO blockNames env₂)
    (hBP : ConLeche.BlockEtaPinned μ blockNames env₂)
    (h : IndRecsRun μ F blockNames env₂ recs env₃) :
    ∃ mp₃ : EnvModelM V μ env₃,
      BlockInstalledTT blockNames env₃ mp₃.base2.cvalE ∧
      BlockAcvalInstalled blockNames env₃ mp₃.base2.acval := by
  rcases h with ⟨rfl, rfl⟩ | ⟨-, heqf, envSelf, checked,
    hprov, hfold⟩
  · exact ⟨mp, hI, hIA⟩
  -- the provisioning, at both tiers
  obtain ⟨mS, hIS, hIAS, hECS, hBPS⟩ :=
    provisionRecsPM hetaP hunitP recs mp hbn hprov hI hIA hEC hBP
  -- every block member is stored in the provisional environment
  have hnames : ∀ n, blockNames.contains n = true →
      (envSelf.find? n).isSome = true := by
    intro n hn
    rcases hall n hn with hfound | ⟨ci, hci, rfl⟩
    · rcases hf : env₂.find? n with _ | ci
      · rw [hf] at hfound; exact nomatch hfound
      · rw [provisionRecsRunS_mono recs hprov n ci hf]; rfl
    · exact provisionRecsRunS_stored recs hprov ci hci
  -- the block renaming, at both tiers
  have hro := blockRenameOkT hIS hnames
  have hroP := blockRenameOk hIS hIAS hnames
  -- the fold's swap data, model-free (task #161 S6): this call used
  -- to be `indRecsFoldS mS.base` — the v1 install, run for two of its
  -- five conclusions.  `indRecsFoldFacts` (`SetBase/IndBlockR.lean`)
  -- is the same induction with the per-rule conclusion as a
  -- parameter, and `iotaRulesFactsR` supplies the model-free one, so
  -- the P lane no longer round-trips through the collapsed install
  -- here at all.
  -- **the rule rhs's reading, from the RUN** (task #161 S11b): the
  -- one row `RuleFacts` wants that the run record does not carry is
  -- the fired rhs's denotation, and `acceptedReads_of` supplies it at
  -- the P carrier — the S10 residual-A route, threaded as
  -- `iotaRulesFactsRun`'s `hden` premise.
  have hdenS : ∀ e : Expr, e.hasFvar = false →
      e.looseBVarsBounded 0 = true →
      (∃ t', inferTypeCore μ envSelf F 0 e = .ok t') →
      ∀ φ : Name → Nat,
        ∃ Rv, denoteClosed mS.base2.cvalE envSelf φ e = some Rv := by
    intro e hef heb hrun φ
    obtain ⟨t', hrun'⟩ := hrun
    obtain ⟨ea, hea⟩ :=
      acceptedReads_of mS.base2 φ hrun'
        (Expr.WScoped.of_not_hasFvar hef) heb
        (fun l hl => absurd hl (fun h' => by
          rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hef] at h'
          exact nomatch h'))
    exact ⟨ea.erase,
      denoteMeta_erase mS.base2.acval_erase 0 e hea⟩
  obtain ⟨hswR, hnresR, hentR, hentFR⟩ :=
    indRecsFoldFactsRun (RuleFacts envSelf mS.base2.cvalE)
      (fun _cvA _mI _rP rules rules' _hbnA _hselfA hiot =>
        iotaRulesFactsRun
          (fun n ci hf =>
            Or.inl (provisionRecsRunS_mono recs hprov n ci hf))
          hdenS 0 rules rules' hiot)
      recs (SwapShList.of_eq env₂.consts)
      (SwapNResS.of_eq env₂)
      (fun n ci hf =>
        Or.inl (provisionRecsRunS_mono recs hprov n ci hf))
      (provisionRecsRunS_mono recs hprov) heqf
      (fun c hc => Or.inl (provisionRecsRunS_mem recs hprov c hc))
      (fun n cv mI rP rules hf =>
        Or.inl (provisionRecsRunS_mono recs hprov n _ hf))
      hbn hprov hfold
  have hcg : ConLeche.SwapCongr envSelf env₃ := SwapShList.congr hswR
  -- the P rows at the group's output
  have hentF := indRecsFold (V := V) hμ mS hIS hroP
    (fun n ci hf => Or.inl (provisionRecsRunS_mono recs hprov n ci hf))
    heqf recs
    (fun n cv mI rP rules hf =>
      Or.inl (provisionRecsRunS_mono recs hprov n _ hf))
    hbn hprov hfold
  -- `rec_rules` at the swapped carrier
  have hrecP : ∀ m₃ : EnvModel V env₃, m₃.acval = mS.base2.acval →
      ∀ φ : Name → Nat, RecRules m₃ φ := by
    intro m₃ hac φ n cv mI rP rules hf rl hrl hfire
    rcases hentF n cv mI rP rules hf with hfS | hlaws
    · exact RecRuleLaw.swapP hcg hac
        (mS.rec_rules φ n cv mI rP rules hfS rl hrl hfire)
    · rw [← Env.find?_name hf]
      exact RecRuleLaw.swapP hcg hac (hlaws rl hrl hfire φ)
  -- the swap
  obtain ⟨hwf₃, hctors₃, hbp₃, hproj₃⟩ :=
    swapEnvFacts mS.base2.wf mS.base2.rec_ctors mS.base2.basis_pinned
      mS.base2.proj_ok hswR hnresR hentR hentFR
  obtain ⟨mp₃, hacc, hcval₃⟩ :=
    EnvModelM.swapP mS hswR hwf₃ hctors₃ hbp₃ hproj₃ hrecP
  refine ⟨mp₃, ?_, by rw [hacc]; exact blockAcvalInstalled_swap hcg hIAS⟩
  -- the block invariant survives the swap (`indRecsCoreR`'s own
  -- argument, at the P carrier's valuation)
  rw [hcval₃]
  intro n hn ci₃ hf₃
  rcases swapSh_find?_corr hswR n with heq |
    ⟨cv, mI, rP, rules, h₀, h₃, -⟩
  · rw [heq] at hf₃
    obtain ⟨cvm, mval, hm, hfm, hlps, hren, hv⟩ := hIS n hn ci₃ hf₃
    exact ⟨cvm, mval, hm,
      hcg.findUp _ _ hfm
        (fun _ _ _ _ hcon => ConstantInfo.noConfusion hcon),
      hlps, hren, hv⟩
  · rw [h₃] at hf₃
    obtain rfl := Option.some.inj hf₃
    obtain ⟨cvm, mval, hm, hfm, hlps, hren, hv⟩ := hIS n hn _ h₀
    exact ⟨cvm, mval, hm,
      hcg.findUp _ _ hfm
        (fun _ _ _ _ hcon => ConstantInfo.noConfusion hcon),
      hlps, hren, hv⟩

end ConLeche.Model
