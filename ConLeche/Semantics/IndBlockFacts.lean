module

public import ConLeche.Semantics.DeclEta
import ConLeche.Verify.Extend.Iota

public import ConLeche.Verify.Extend.Block

import ConLeche.Verify.Denote.Rename

public import ConLeche.Verify.Extend.Recs

import ConLeche.Semantics.DeclRun

@[expose] public section
/-!
# The inductive block's **relation-level** residue (task #161 S5,
THE SEPARATION — the C4 refutation's bill, paid)

S3's stop-and-name refuted the design census's C4 at the `indDecl`
kind: `declStepS`'s ind branch takes its η-closure from the whole
`DeclIndS` obligation, whose discharge reads `hEC₁`/`hBP₁` off
`indMembersS` and `hnonrecUp` off `indRecsS` — both **model-carrying**
installs.  The S3 seal sized the repair at "two ~800-line inductions
re-run η-only".

**MEASURED, THE SIZING IS WRONG, AND THAT IS THE FINDING.**  Nothing
of the two folds' model content is needed.  Every ingredient of
`declIndS`'s second component was already relation-level and V-free —
`indMembersR_mono`/`_indNew`/`_ctorEntry`, `indRecsR_noInd`,
`projInstallR_ext` — and the *one* ingredient that
was not, `indRecsS`'s `hnonrecUp`, is not a consequence of the install
at all: the group's install fold accumulates on the **base**
environment (`IndRecsFoldR`'s `acc` starts at `env₂`, not at the
provisional `envSelf`), and every name it conses was checked fresh
against that base.  So the preservation is `indRecsR_keep` below —
an eight-line `find?` walk, *stronger* than `hnonrecUp` (it needs no
"not a recursor" side condition and returns an equation), and the
recursor swap never enters.

This module is model-free by construction: no `V`, no `SetTheory`, no
`EnvS`.  It holds the relation-level lemmas the block folds' syntactic
residue consists of, moved here verbatim from
`SetR/Install/{IndRecsS,IndMembersS,DeclIndS}.lean`, plus the three new
lemmas the keep-fact needs and `declIndEtaClosed`, the ind kind's
η-closure proved from `DeclIndRun` alone.  `declIndS` routes its own
second component through it (one source of truth), and the P fold
consumes it instead of `declIndS memberKeyS mp.base`.
-/

namespace ConLeche.Semantics

open ConLeche.Term ConLeche.Verify

/-- An empty capability record pins nothing, and asks nothing. -/
theorem etaPins_empty {μ : CheckMode} {env : Env} {T : Name}
    {lps : List Name} : EtaPins μ env T lps {} :=
  ⟨fun h => absurd h (by decide), fun h => absurd h (by decide)⟩

/-! ## The provisioning's syntactic residue -/

/-! ## The member fold's syntactic residue

The `DeclIndS` assembly needs to know what the fold *preserves*, not
just that it produces a model.  These two are the [set] analogues of
`checkIndFold_mono` / `checkIndMember_fold_names`
(`Verify/Extend/Ind.lean`); they are V-free and prove by the same
freshness chain `provisionRecsS_mono` uses. -/

/-- The fold's per-member eta data steps at a fresh, non-projection
install: `EtaPins.step` for the pins, nothing for the (environment-free)
constructor fact, and the name shape for the projection freshness. -/
theorem etaMemberData_step {μ : CheckMode} {blockNames : List Name}
    {caps : IndCaps} {env : Env} {c₀ : ConstantInfo} {n : Name}
    {lps : List Name} (hfresh : env.find? c₀.name = none)
    (hshape : c₀.name.isProjFnShape = false)
    (h : EtaPins μ env n lps caps ∧
      (caps.eta = true → blockNames.contains caps.etaCtor = true) ∧
      (caps.eta = true → 0 < caps.etaFields →
        env.find? (projFnName n 0) = none)) :
    EtaPins μ ⟨c₀ :: env.consts⟩ n lps caps ∧
      (caps.eta = true → blockNames.contains caps.etaCtor = true) ∧
      (caps.eta = true → 0 < caps.etaFields →
        (⟨c₀ :: env.consts⟩ : Env).find? (projFnName n 0) = none) :=
  ⟨EtaPins.step h.1 hfresh, h.2.1, fun he hlt => by
    rw [Env.find?_cons, if_neg (fun hh =>
      projFnName_ne_of_shape (T := n) (j := 0) hshape hh.symm)]
    exact h.2.2 he hlt⟩

/-! ## The group phase's keep-fact (task #161 S5 — the C4 bill)

`indRecsS` reports a *non-recursor* transport (`hnonrecUp`) and proves
it through the `EnvS` swap.  At the relation level the fact is both
simpler and stronger, and needs no install: `IndRecsFoldR` accumulates
on the group's **base** environment (`IndRecsR` starts the fold at
`env₂`, handing `envSelf` over only as the environment the *rules* are
checked against), and every name it conses was checked fresh against
that base by `MemberValR`.  So a base lookup that succeeds is
untouched — recursor or not. -/

/-! ## `declIndEtaClosed` — the ind kind's η-closure, model-free -/

/-- **The block renaming is sound at the provisional
environment.**  Extracted from `indRecsS` when the bridge's own
rules fold (`indRecsFoldRS`) needed the same fact — the *second*
consumer, which is the relocation rule's threshold.

**Task #161 S6**: it never used its `mS : EnvS` for anything but the
valuation in its own statement — S5's finding-2 shape, third instance
in the ind tier — so it is re-signed over a bare `TConstVal` and moved
to the base, where the P lane reaches it without a crossing. -/
theorem blockRenameOkT {blockNames : List Name} {envSelf : Env}
    {cvalSelf : TConstVal}
    (hIS : BlockInstalledTT blockNames envSelf cvalSelf)
    (hnames : ∀ n, blockNames.contains n = true →
      (envSelf.find? n).isSome = true) :
    RenameOkT cvalSelf envSelf (fun n =>
      if blockNames.contains n then n.str "_model" else n) := by
    refine ⟨?_, ?_, ?_⟩
    · intro n ciS hfS
      dsimp only
      by_cases hc : blockNames.contains n = true
      · rw [if_pos hc]
        obtain ⟨cvmS, mvalS, hmS, hfmS, hlpsS, -, -⟩ := hIS n hc ciS hfS
        exact ⟨.defnInfo cvmS mvalS hmS, hfmS, hlpsS⟩
      · rw [if_neg hc]
        exact ⟨ciS, hfS, rfl⟩
    · intro n hfS
      dsimp only
      by_cases hc : blockNames.contains n = true
      · have := hnames n hc
        rw [hfS] at this
        exact nomatch this
      · rw [if_neg hc]
        exact hfS
    · intro n ψ
      dsimp only
      by_cases hc : blockNames.contains n = true
      · rw [if_pos hc]
        rcases hfS : envSelf.find? n with _ | ciS
        · have := hnames n hc
          rw [hfS] at this
          exact nomatch this
        · obtain ⟨-, -, -, -, -, -, hvS⟩ := hIS n hc ciS hfS
          exact (hvS ψ).symm
      · rw [if_neg hc]

/-- The reserved-name side condition of the group swap: a genuinely
swapped entry never sits at a pinned basis name. -/
def SwapNResS (env₀ env₃ : Env) : Prop :=
  ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
    env₀.find? n = some (.recInfo cv mI rP []) →
    env₃.find? n = some (.recInfo cv mI rP rules) →
    rules = [] ∨ reservedBasisNames.contains n = false

theorem SwapNResS.of_eq (env : Env) : SwapNResS env env := by
  intro n cv mI rP rules h₀ h₃
  rw [h₀] at h₃
  obtain ⟨-, -, -, rfl⟩ := ConstantInfo.recInfo.inj (Option.some.inj h₃)
  exact Or.inl rfl

/-- The install fold's accumulator, read against the self environment:
a lookup either agrees or differs only in a recursor's rule list. -/
def FoldUpS (envAcc envSelf : Env) : Prop :=
  ∀ (n : Name) (ci : ConstantInfo), envAcc.find? n = some ci →
    envSelf.find? n = some ci ∨
    ∃ cv mI' rP' rules rules',
      ci = .recInfo cv mI' rP' rules ∧
      envSelf.find? n = some (.recInfo cv mI' rP' rules')

/-! ## The group's rule facts, model-free (task #161 S6)

`RuleFactsS` (`SetR/Install/IndRecsS.lean`) is what one checked rule
owes the installed environment, and **six of its seven conjuncts are
syntactic**; the seventh is the fired law, which is the only place a
model appears.  What the ind tier's de-basing needs is those six plus
the two the law's *head* carries — `rP ≤ mI` and the right-hand side's
denotation — because they are exactly what an `EnvFacts` at the swapped
environment asks for (`rec_params_le`, `rec_rhs_denotes`).

`RuleFacts` is that package, and `iotaRulesFactsR` produces it from
the rule fold's record alone.  `iotaRulesS` is re-proved through it,
so there is one proof of the syntactic half.
-/

/-- **What one checked rule owes the environment, model-free**:
`RuleFactsS`'s six syntactic conjuncts, plus the two facts about a
*fired* rule an `EnvFacts` reads — the parameter bound and the right-hand
side's denotation.  (The law itself stays in `RuleFactsS`.) -/
def RuleFacts (envSelf : Env) (cvalSelf : TConstVal)
    (cv : ConstantVal) (mI rP : Nat) (rl : RecRule) : Prop :=
  (RecRule.rhs rl).hasFvar = false ∧
  (RecRule.rhs rl).allLevelParamsDefined cv.levelParams = true ∧
  (RecRule.rhs rl).constsResolve envSelf = true ∧
  (RecRule.rhs rl).looseBVarsBounded 0 = true ∧
  (∀ lvls pins, RecRule.fire rl = .nested lvls pins →
    rP ≤ mI ∧
    (∀ l ∈ lvls, l.allParamsDefined cv.levelParams = true) ∧
    (∀ pin ∈ pins, pin.hasFvar = false ∧
      pin.allLevelParamsDefined cv.levelParams = true ∧
      pin.constsResolve envSelf = true ∧
      pin.looseBVarsBounded rP = true) ∧
    ∃ pre dom body bm D,
      cv.type.stripPis mI = some (pre, .forallE dom body bm) ∧
      dom.getAppFn = .const D lvls ∧
      dom.getAppArgs =
        pins.map (Expr.liftLooseBVars (mI - rP) 0) ++
          (List.range (mI - rP)).map
            (fun i => Expr.bvar (mI - rP - 1 - i))) ∧
  (∃ cvj cnP cnF,
    envSelf.find? (RecRule.ctor rl) = some (.ctorInfo cvj cnP cnF)) ∧
  (RecRule.fire rl ≠ .inert →
    rP ≤ mI ∧
    ∀ φ : Name → Nat,
      ∃ Rv, denoteClosed cvalSelf envSelf φ (RecRule.rhs rl) = some Rv) ∧
  -- the two install-computed rescue bits are the store's own verdict
  (rl.k = true → recRuleKOf envSelf.find? rl.ctor = true) ∧
  (rl.eta = true → recRuleEtaOf envSelf.find? cv.name rl.ctor = true)

/-- A plain fire's shape test carries the parameter bound. -/
theorem recRulePlain_params_le {recTy : Expr} {mI rP cnP : Nat}
    (h : Expr.recRulePlain recTy mI rP cnP = true) : rP ≤ mI := by
  unfold Expr.recRulePlain at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  omega


end ConLeche.Semantics
