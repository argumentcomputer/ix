module

public import ConLeche.Semantics.IndBlockRun
public import ConLeche.Model.IndCons
import ConLeche.Model.Annot.BitRename
import ConLeche.Verify.Extend.Block

public section

/-!
# The block member's key, P tier (task #161, IND TIER)

`memberKeyS` (`Install/IndMembersS.lean`) is v1's; this is its
transpose, and it is the same short argument for the same reason:

> the member's leaf is *given* — it takes its model artifact's — so
> the invariant's own `mem_type`/`type_wellDenotedV` at the stored `_model`
> constant supply the membership and the grading outright.  All that
> is left is that the member's type and the model's type **read the
> same**.

The two blindnesses that close that gap are `Annot/BitRename.lean`'s
(`denoteMeta_renameConsts_resolve` and `denoteMeta_erasedEq`), transposed
there for this consumer.

**What is V-free is reused, not re-proved** (ENDGAME D's §3 lesson).
The block renaming's `hup` clause — every stored constant's model is
stored with the same level parameters — is `BlockInstalledTT`'s, a
predicate about the environment and the *v1* valuation, already
carried by the v1 fold that rides beside this one.  Only its last
conjunct is about a valuation leaf, and `acval_erase` fixes leaves
only up to numerals (H's §1 finding, in the same shape once more), so
exactly that conjunct gets a P twin: `BlockAcvalInstalled`.  It is one
line, it is what the member cons establishes by construction (the
leaf it stores *is* `acval (n ++ "_model")`), and it is the only new
predicate the member fold needs.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics ConLeche.SetModel
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  ReducibilityHint)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {F : Nat}

/-- **The annotated half of `BlockInstalledTT`**: an installed block
member's *leaf* is its model's.  The other three conjuncts of
`BlockInstalledTT` are V-free environment facts and are consumed from
the v1 predicate directly. -/
@[expose] def BlockAcvalInstalled (blockNames : List Name) (env : Env)
    (acval : Name → (Name → Nat) → AnnotTerm) : Prop :=
  ∀ n, blockNames.contains n = true → ∀ ci : ConstantInfo,
    env.find? n = some ci →
    ∀ ψ : Name → Nat, acval (n.str "_model") ψ = acval n ψ

/-- The P invariant's three type facts at a *stored* constant, keyed
by `find?` rather than by membership (`EnvS.cval_memType`'s
transpose). -/
theorem EnvModelM.acval_memType (mp : EnvModelM V μ env) {n : Name}
    {ci : ConstantInfo} (hf : env.find? n = some ci)
    (ψ : Name → Nat) :
    ∃ ta, denoteMeta mp.base2.acval env ψ 0 ci.toConstantVal.type
        = some ta ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧
      ∀ ρ : Nat → V,
        interp V ρ (mp.base2.acval n ψ) ∈ˢ interp V ρ ta := by
  obtain ⟨ta, hta⟩ := mp.type_reads ci (Env.find?_mem hf) ψ
  refine ⟨ta, hta, mp.type_wellDenotedV ci (Env.find?_mem hf) ψ ta hta, ?_⟩
  intro ρ
  have := mp.mem_type ci (Env.find?_mem hf) ψ ta hta ρ
  rwa [Env.find?_name hf] at this

/-- **The block member's key, P tier.**  The model artifact's leaf
inhabits the checked member's type's reading, graded, at every
assignment. -/
theorem memberKey (mp : EnvModelM V μ env) {blockNames : List Name}
    {cv cvA : ConstantVal}
    (hmv : MemberValRun μ F env blockNames cv cvA)
    (hIB : BlockInstalledTT blockNames env mp.base2.cvalE)
    (hIA : BlockAcvalInstalled blockNames env mp.base2.acval)
    (ψ : Name → Nat) :
    ∃ ta, denoteMeta mp.base2.acval env ψ 0 cvA.type = some ta ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧
      ∀ ρ : Nat → V,
        interp V ρ (mp.base2.acval (cvA.name.str "_model") ψ)
          ∈ˢ interp V ρ ta := by
  obtain ⟨type', hcv, rfl, -, cvm, mval, hint, hfm, hlpm, hren⟩ := hmv
  obtain ⟨-, -, -, -, -, -, -, -, htr, -⟩ := hcv
  -- the renaming's two `RenameOkT` clauses, at a member environment
  have hup : ∀ n ci, env.find? n = some ci →
      ∃ ci', env.find? ((fun n =>
          if blockNames.contains n then n.str "_model" else n) n)
        = some ci' ∧
        ci'.toConstantVal.levelParams
          = ci.toConstantVal.levelParams := by
    intro n ci hfn
    dsimp only
    by_cases hb : blockNames.contains n = true
    · obtain ⟨cvm', mval', hint', hfm', hlp', -, -⟩ := hIB n hb ci hfn
      exact ⟨.defnInfo cvm' mval' hint', by rw [if_pos hb]; exact hfm',
        hlp'⟩
    · exact ⟨ci, by rw [if_neg hb]; exact hfn, rfl⟩
  have hval : ∀ (n : Name) (ci : ConstantInfo),
      env.find? n = some ci → ∀ ψ' : Name → Nat,
      mp.base2.acval ((fun n =>
        if blockNames.contains n then n.str "_model" else n) n) ψ'
        = mp.base2.acval n ψ' := by
    intro n ci hfn ψ'
    dsimp only
    by_cases hb : blockNames.contains n = true
    · rw [if_pos hb]; exact hIA n hb ci hfn ψ'
    · rw [if_neg hb]
  -- the model constant's own facts, and the two types read the same
  obtain ⟨ta, hta, hokta, hmem⟩ :=
    mp.acval_memType (n := cv.name.str "_model") hfm ψ
  refine ⟨ta, ?_, hokta, hmem⟩
  show denoteMeta mp.base2.acval env ψ 0 type' = some ta
  rw [← hta]
  show denoteMeta mp.base2.acval env ψ 0 type'
    = denoteMeta mp.base2.acval env ψ 0 cvm.type
  rw [← denoteMeta_erasedEq (Expr.ErasedEq.of_eq (eq_of_beq hren)) 0]
  exact (denoteMeta_renameConsts_resolve hup hval type' 0 htr).symm

/-! ## The member install -/

/-- **One block member, installed at the model's leaf** —
`indMemberS`'s transpose, covering the same three kinds (the two
non-recursor members and provisioning's *rule-less* recursor).

The leaf is `acval (n ++ "_model")`, exactly as v1's valuation is
`cval (n ++ "_model")`: the tower's five laws are then the invariant's
own leaf laws at the model's name, and no tower is built by hand
anywhere in the inductive tier.  The type's reading is `memberKey`,
crossed forward to the extension.

`caps_ok` stays a **parameter**, as v1's two capability head
obligations do and for v1's reason: at a single member's install the
family's constructor and projections need not be stored yet, so the
caller — the block fold, which knows the whole block is in — is the
only place it can be discharged. -/
theorem indMember (mp : EnvModelM V μ env) {c₀ : ConstantInfo}
    {cvA : ConstantVal}
    (hkind : (∃ caps, c₀ = .indInfo cvA caps) ∨
      (∃ nP nF, c₀ = .ctorInfo cvA nP nF) ∨
      (∃ mI rP, c₀ = .recInfo cvA mI rP []))
    (hfresh : env.find? cvA.name = none)
    (hnres : ConLeche.reservedBasisNames.contains cvA.name = false)
    -- the model artifact whose leaf the member takes
    {cvm : ConstantVal} {mval : Expr} {hint : ReducibilityHint}
    (hmE : env.find? (cvA.name.str "_model")
      = some (.defnInfo cvm mval hint))
    (hmlps : cvm.levelParams = cvA.levelParams)
    -- the member's type resolves in the prefix (`ConstantValR`)
    (hres : cvA.type.constsResolve env = true)
    -- the extended store's well-formedness (`memberInstallInv`'s
    -- first conclusion; task #161 S7 — this is all the v1 install
    -- ever supplied here)
    (hwf : EnvWF ⟨c₀ :: env.consts⟩)
    -- the member's key at the prefix (`memberKey`)
    (hkeyP : ∀ ψ : Name → Nat, ∃ ta,
      denoteMeta mp.base2.acval env ψ 0 cvA.type = some ta ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧
      ∀ ρ : Nat → V,
        interp V ρ (mp.base2.acval (cvA.name.str "_model") ψ)
          ∈ˢ interp V ρ ta)
    -- the block fold's row
    (hcaps : ∀ m₂ : EnvModel V ⟨c₀ :: env.consts⟩,
      m₂.acval = acvalWith mp.base2.acval cvA.name
        (fun ψ => mp.base2.acval (cvA.name.str "_model") ψ) →
      CapsOk m₂) :
    ∃ mp' : EnvModelM V μ ⟨c₀ :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval cvA.name
        (fun ψ => mp.base2.acval (cvA.name.str "_model") ψ) := by
  -- the three kinds share a constant value and a name
  have hcvA : c₀.toConstantVal = cvA := by
    rcases hkind with ⟨caps, rfl⟩ | ⟨nP, nF, rfl⟩ | ⟨mI, rP, rfl⟩ <;> rfl
  have hname : c₀.name = cvA.name := congrArg ConstantVal.name hcvA
  have hfresh' : env.find? c₀.name = none := by rw [hname]; exact hfresh
  have hnres' : ConLeche.reservedBasisNames.contains c₀.name = false := by
    rw [hname]; exact hnres
  -- provisioning's recursor is rule-less, so `rec_rules` transports
  have hnorules : ∀ cv2 mI2 rP2 rules2,
      c₀ = .recInfo cv2 mI2 rP2 rules2 → rules2 = [] := by
    rcases hkind with ⟨caps, rfl⟩ | ⟨nP, nF, rfl⟩ | ⟨mI, rP, rfl⟩ <;>
      intro cv2 mI2 rP2 rules2 heq
    · exact nomatch heq
    · exact nomatch heq
    · injection heq with _ _ _ h4
      exact h4.symm
  have hcb : ConstsBound env cvA.type :=
    constsBound_of_constsResolve _ hres
  -- the crossing, forward
  have hcross : ∀ (ψ : Name → Nat) {ta : AnnotTerm},
      denoteMeta mp.base2.acval env ψ 0 cvA.type = some ta →
      denoteMeta (acvalWith mp.base2.acval c₀.name
          (fun ψ => mp.base2.acval (cvA.name.str "_model") ψ))
        ⟨c₀ :: env.consts⟩ ψ 0 c₀.toConstantVal.type = some ta := by
    intro ψ ta h
    rw [hcvA]
    exact denoteMeta_cons_fresh_mono hfresh'
      (by rcases hkind with ⟨caps, rfl⟩ | ⟨nP, nF, rfl⟩ | ⟨mI, rP, rfl⟩ <;>
        intro _ h <;> exact nomatch h)
      ψ 0 cvA.type hcb h
  have hgoal := declStep_preserves_of_ind_cons mp (c₀ := c₀)
    (A := fun ψ => mp.base2.acval (cvA.name.str "_model") ψ)
    hfresh' hnres'
    (by rcases hkind with ⟨caps, rfl⟩ | ⟨nP, nF, rfl⟩ | ⟨mI, rP, rfl⟩ <;>
          intro _ _ _ h <;> exact nomatch h)
    (by rcases hkind with ⟨caps, rfl⟩ | ⟨nP, nF, rfl⟩ | ⟨mI, rP, rfl⟩ <;>
          intro _ h <;> exact nomatch h)
    (ConsHead.ofFresh hwf
      (fun ψ => mp.base2.cval_closedL _ ψ) hnres'
      (by rcases hkind with ⟨caps, rfl⟩ | ⟨nP, nF, rfl⟩ | ⟨mI, rP, rfl⟩ <;>
            intro _ h <;> exact nomatch h)
      (fun cv2 mI2 rP2 rules2 heq r hr => by
        rw [hnorules cv2 mI2 rP2 rules2 heq] at hr
        exact nomatch hr))
    -- the tower: the invariant's own leaf laws, at the model's name
    (fun ψ k => mp.base2.acval_closed _ ψ k)
    (fun ψ₁ ψ₂ hps =>
      mp.base2.acval_params _ _ hmE ψ₁ ψ₂ (by
        intro p hp
        have hp' : p ∈ cvm.levelParams := hp
        rw [hmlps] at hp'
        exact hps p (by rw [hcvA]; exact hp')))
    (fun ψ ρ => mp.base2.acval_wellDenoted _ ψ ρ)
    (fun ψ ρ => mp.acval_validV _ ψ ρ)
    -- the type's reading, crossed
    (fun ψ => by
      obtain ⟨ta, hta, -, -⟩ := hkeyP ψ
      exact ⟨ta, hcross ψ hta⟩)
    (fun ψ ta hta ρ => by
      obtain ⟨ta₀, hta₀, hok, -⟩ := hkeyP ψ
      obtain rfl : ta₀ = ta := Option.some.inj ((hcross ψ hta₀).symm.trans hta)
      exact hok ρ)
    (fun ψ ta hta ρ => by
      obtain ⟨ta₀, hta₀, -, hmem⟩ := hkeyP ψ
      obtain rfl : ta₀ = ta := Option.some.inj ((hcross ψ hta₀).symm.trans hta)
      exact hmem ρ)
    (fun m₂ hac => hcaps m₂ (by rw [hac, hname]))
    (fun m₂ hac φ => recRules_cons_fresh mp hfresh'
      (by rcases hkind with ⟨caps, rfl⟩ | ⟨nP, nF, rfl⟩ | ⟨mI, rP, rfl⟩ <;>
        intro _ h <;> exact nomatch h)
      hnorules m₂ hac φ)
    (by rcases hkind with ⟨caps, rfl⟩ | ⟨nP, nF, rfl⟩ | ⟨mI, rP, rfl⟩ <;>
      intro _ h <;> exact nomatch h)
  rw [hname] at hgoal
  exact hgoal

end ConLeche.Model
