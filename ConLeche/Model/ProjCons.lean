module

public import ConLeche.Model.ProjRename
import ConLeche.Model.IndProjEta
public import ConLeche.Semantics.ProjFnFacts
public section

/-!
# The projection-function cons, P tier (task #161, IND TIER part 10)

`projConsS`'s twin.  Everything the v1 cons has to *check* is either a
name-distinctness fact or vacuous at a `.recInfo` head, and the P tier
inherits all of it through `declStep_preserves_of_ind_rec_cons`; what is left
is exactly three things:

* **the stored type's three rows**, read through the *pruned*
  projection renaming.  `pty.renameConsts (projFwd …) = mcv.type` is
  the checker's roundtrip pin, `denoteMeta_renameConsts` turns it into an
  equality of readings, and `EnvModelM.acval_memType` at the model
  definition supplies the reading, its grading and the leaf's
  membership in one call — the same three-field read every P cons
  makes;
* **`caps_ok`**, through `capsOk_cons_proj` (part 9's row) —
  called directly rather than through `capsOk_cons_proj_of` because
  the `hvP` clause needs the *completed family's* own storedness of
  the earlier projection slots, which only `EtaFamilyStored` carries;
* **`rec_rules`**, a premise here exactly as v1's `hheadRec` is: the
  projection bottom fires **below** this cons (`projFn`), and
  `acvalWith_self` makes its head the installed constant's leaf.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics ConLeche.SetModel
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  RecRule IndCaps projFnName projModelName projFwd ReducibilityHint)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

/-- `BlockAcvalInstalled` crosses a fresh cons whose name is not a
block name (`BlockInstalledTT.fresh_cons`'s annotated half).  The
`_model` side is free: the head's name is `projFnName T i`, a `Name.num`,
and `n.str "_model"` never is. -/
theorem blockAcvalInstalled_fresh_cons {blockNames : List Name}
    {env : Env} {acval : Name → (Name → Nat) → AnnotTerm}
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    (hIA : BlockAcvalInstalled blockNames env acval)
    (hnotb : blockNames.contains c₀.name = false)
    (hstrNe : ∀ n : Name, c₀.name ≠ n.str "_model") :
    BlockAcvalInstalled blockNames ⟨c₀ :: env.consts⟩
      (acvalWith acval c₀.name A) := by
  intro n hbn ci hf ψ
  have hnN : n ≠ c₀.name := by
    intro hh
    rw [hh, hnotb] at hbn
    exact nomatch hbn
  rw [acvalWith_ne (fun hh => hstrNe n hh.symm), acvalWith_ne hnN]
  refine hIA n hbn ci ?_ ψ
  rw [Env.find?_cons, if_neg (fun hh => hnN hh.symm)] at hf
  exact hf

set_option maxHeartbeats 1600000 in
/-- **The projection entry installs, P tier** (`projConsS`). -/
theorem projCons {env' : Env} (mp : EnvModelM V μ env')
    {T ctorName : Name} {lps : List Name} {nP nF i : Nat}
    {rules : List RecRule} {blockNames : List Name}
    {mcv : ConstantVal} {mval : Expr} {mhint : ReducibilityHint}
    {pty : Expr}
    {c₀ : ConstantInfo} (hc₀ : c₀ = projEntry T lps pty nP i rules)
    (hfm : env'.find? (projModelName T i)
      = some (.defnInfo mcv mval mhint))
    (hmlps : mcv.levelParams = lps)
    (hpnone : (env'.find? (projFnName T i)).isNone = true)
    (hround : (pty.renameConsts (projFwd T ctorName nF) == mcv.type)
      = true)
    (hptyres : pty.constsResolve env' = true)
    (hinv : ProjPhaseInvS T ctorName nF env' mp.base2.cvalE)
    (hinvA : ProjPhaseAcval T ctorName nF env' mp.base2.acval)
    (hilt : i < nF)
    (hTf : (env'.find? T).isSome = true)
    (hCf : (env'.find? ctorName).isSome = true)
    (hIB : BlockInstalledTT blockNames env' mp.base2.cvalE)
    (hIA : BlockAcvalInstalled blockNames env' mp.base2.acval)
    (hTblock : blockNames.contains T = true)
    (hnotb : blockNames.contains (projFnName T i) = false)
    (hpinsT : ∀ cvT capsT, env'.find? T = some (.indInfo cvT capsT) →
      ConLeche.EtaPins μ env' T cvT.levelParams capsT)
    (hCblock : ∀ cvT capsT, env'.find? T = some (.indInfo cvT capsT) →
      capsT.eta = true → blockNames.contains capsT.etaCtor = true)
    (hFields : ∀ cvT capsT, env'.find? T = some (.indInfo cvT capsT) →
      capsT.eta = true → capsT.etaFields = nF)
    -- the head's own obligations (task #161 S7: `projFn_head`
    -- supplies both from `ProjFnR` alone)
    (hwf : EnvWF ⟨c₀ :: env'.consts⟩)
    (hctorsHead : ∀ (cvR : ConstantVal) (mI rP : Nat)
      (rules₀ : List RecRule), c₀ = .recInfo cvR mI rP rules₀ →
      ∀ r ∈ rules₀,
        (∃ cvj cnP cnF,
          env'.find? (ConLeche.RecRule.ctor r)
            = some (.ctorInfo cvj cnP cnF)) ∧
        (r.k = true → ConLeche.recRuleKOf env'.find? r.ctor = true) ∧
        (r.eta = true →
          ConLeche.recRuleEtaOf env'.find? c₀.name r.ctor = true))
    -- the fired rules: the bottom fires BELOW this cons
    (hnew : ∀ m₂ : EnvModel V ⟨c₀ :: env'.consts⟩,
      m₂.acval = acvalWith mp.base2.acval (projFnName T i)
        (fun ψ => mp.base2.acval (projModelName T i) ψ) →
      ∀ (φ : Name → Nat), ∀ rl ∈ rules, RecRule.fire rl ≠ .inert →
        RecRuleLaw m₂ φ (projFnName T i) ⟨projFnName T i, lps, pty⟩
          nP nP rl) :
    ∃ mp' : EnvModelM V μ ⟨c₀ :: env'.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval (projFnName T i)
        (fun ψ => mp.base2.acval (projModelName T i) ψ) ∧
      ProjPhaseAcval T ctorName nF ⟨c₀ :: env'.consts⟩
        mp'.base2.acval ∧
      BlockAcvalInstalled blockNames ⟨c₀ :: env'.consts⟩
        mp'.base2.acval := by
  have hname : c₀.name = projFnName T i := by rw [hc₀]; rfl
  have hcvA : c₀.toConstantVal = ⟨projFnName T i, lps, pty⟩ := by
    rw [hc₀]; rfl
  have hfreshP : env'.find? (projFnName T i) = none :=
    Option.isNone_iff_eq_none.mp hpnone
  have hfresh : env'.find? c₀.name = none := by
    rw [hname]; exact hfreshP
  have hnotb₀ : blockNames.contains c₀.name = false := by
    rw [hname]; exact hnotb
  have hstrNe₀ : ∀ n : Name, c₀.name ≠ n.str "_model" := by
    rw [hname]; exact fun n => ConLeche.Name.num_ne_str _ _ _ _
  have hnres : ConLeche.reservedBasisNames.contains c₀.name = false := by
    rw [hname]; exact ConLeche.reservedBasisNames_not_num _ _
  -- the installed leaf
  obtain ⟨A, hA⟩ : ∃ A : (Name → Nat) → AnnotTerm,
      A = fun ψ => mp.base2.acval (projModelName T i) ψ := ⟨_, rfl⟩
  have hAdef : ∀ ψ, A ψ = mp.base2.acval (projModelName T i) ψ :=
    fun ψ => by rw [hA]
  -- the pruned renaming, and the type's reading at the prefix
  have hroP := projFwd_renameOk hinv hinvA
  have hrenP : pty.renameConsts (fun n =>
      if (env'.find? n).isSome = true then
        projFwd T ctorName nF n else n) = mcv.type := by
    rw [ConLeche.Expr.renameConsts_congr_resolve
      (g := projFwd T ctorName nF)
      (fun n hn => by simp only [hn, if_true]) _ hptyres]
    exact eq_of_beq hround
  have htyPre : ∀ ψ : Name → Nat, ∃ ta : AnnotTerm,
      denoteMeta mp.base2.acval env' ψ 0 pty = some ta ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧
      ∀ ρ : Nat → V, interp V ρ (A ψ) ∈ˢ interp V ρ ta := by
    intro ψ
    obtain ⟨ta, hta, hok, hmem⟩ := mp.acval_memType hfm ψ
    refine ⟨ta, ?_, hok, ?_⟩
    · rw [← denoteMeta_renameConsts hroP pty 0, hrenP]
      exact hta
    · intro ρ; rw [hAdef]; exact hmem ρ
  have hcbPty : ConstsBound env' pty :=
    constsBound_of_constsResolve _ hptyres
  have htyExt : ∀ ψ : Name → Nat, ∃ ta : AnnotTerm,
      denoteMeta (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env'.consts⟩ ψ 0 c₀.toConstantVal.type = some ta ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧
      ∀ ρ : Nat → V, interp V ρ (A ψ) ∈ˢ interp V ρ ta := by
    intro ψ
    obtain ⟨ta, hta, hok, hmem⟩ := htyPre ψ
    refine ⟨ta, ?_, hok, hmem⟩
    rw [hcvA]
    exact denoteMeta_cons_fresh_mono hfresh
      (fun _ h => by rw [hc₀] at h; exact nomatch h)
      ψ 0 pty hcbPty hta
  -- the eight mechanical rows
  have hAclosedH : ∀ (ψ : Name → Nat) (k : Nat),
      (A ψ).liftN 1 k = A ψ := by
    intro ψ k
    rw [hAdef]
    exact mp.base2.acval_closed _ _ _
  have hAparamsH : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ c₀.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
      A ψ₁ = A ψ₂ := by
    intro ψ₁ ψ₂ hp
    rw [hAdef, hAdef]
    refine mp.base2.acval_params _ _ hfm ψ₁ ψ₂ ?_
    intro p hp'
    exact hp p (by rw [hcvA, ← hmlps]; exact hp')
  have htyOkH : ∀ (ψ : Name → Nat) (ta : AnnotTerm),
      denoteMeta (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env'.consts⟩ ψ 0 c₀.toConstantVal.type = some ta →
      ∀ ρ : Nat → V, WellDenotedV V ρ ta := by
    intro ψ ta hta ρ
    obtain ⟨ta', hta', hok, -⟩ := htyExt ψ
    obtain rfl : ta' = ta := Option.some.inj (hta'.symm.trans hta)
    exact hok ρ
  have hmemNewH : ∀ (ψ : Name → Nat) (ta : AnnotTerm),
      denoteMeta (acvalWith mp.base2.acval c₀.name A)
          ⟨c₀ :: env'.consts⟩ ψ 0 c₀.toConstantVal.type = some ta →
      ∀ ρ : Nat → V, interp V ρ (A ψ) ∈ˢ interp V ρ ta := by
    intro ψ ta hta ρ
    obtain ⟨ta', hta', -, hmem⟩ := htyExt ψ
    obtain rfl : ta' = ta := Option.some.inj (hta'.symm.trans hta)
    exact hmem ρ
  -- `caps_ok`: the row `capsOk_cons_proj` leaves open is the family
  -- this cons completes
  have hcapsH : ∀ m₂ : EnvModel V ⟨c₀ :: env'.consts⟩,
      m₂.acval = acvalWith mp.base2.acval c₀.name A → CapsOk m₂ := by
    intro m₂ hac
    refine capsOk_cons_proj mp mp.caps_ok hfresh hname
      ⟨⟨projFnName T i, lps, pty⟩, nP, nP, rules, hc₀⟩ m₂ hac ?_
    intro cvT caps hfT hcape hlt hresT hfam φ'
    -- the family, below the head
    have hfT₀ : env'.find? T = some (.indInfo cvT caps) := by
      rw [Env.find?_cons] at hfT
      split at hfT
      · rw [hc₀] at hfT; exact nomatch (Option.some.inj hfT)
      · exact hfT
    -- v1's `hvP`, from the completed family's own storedness
    have hvP : ∀ j, j < caps.etaFields → ∀ ψ : Name → Nat,
        m₂.acval (projFnName T j) ψ
          = mp.base2.acval (projModelName T j) ψ := by
      intro j hj ψ
      have hjnF : j < nF := by
        rw [← hFields cvT caps hfT₀ hcape]; exact hj
      by_cases hji : j = i
      · subst hji
        rw [hac, ← hname, acvalWith_self, hAdef]
      · have hjneP : projFnName T j ≠ projFnName T i := by
          intro hh
          have hh2 : ConLeche.Name.num (T.str "proj") j
            = ConLeche.Name.num (T.str "proj") i := hh
          injection hh2 with _hp hij
          exact hji hij
        obtain ⟨cv2, mI2, rP2, rules2, hf2⟩ := hfam.2.2 j hj
        rw [Env.find?_cons,
          if_neg (fun hh => hjneP (hname.symm.trans hh).symm)] at hf2
        rw [hac, acvalWith_ne (fun hh => hjneP (hh.trans hname))]
        exact hinvA.2.2 j hjnF (by rw [hf2]; rfl) ψ
    exact projEtaLaw mp hname
      ⟨⟨projFnName T i, lps, pty⟩, nP, nP, rules, hc₀⟩ hfresh hIB hIA
      cvT caps hfT hcape hresT (hpinsT cvT caps hfT₀) hTblock
      (hCblock cvT caps hfT₀ hcape) hfam m₂ hac hvP φ'
  -- `rec_rules`: the bottom fires below this cons
  have hrecH : ∀ m₂ : EnvModel V ⟨c₀ :: env'.consts⟩,
      m₂.acval = acvalWith mp.base2.acval c₀.name A →
      ∀ φ : Name → Nat, RecRules m₂ φ := by
    intro m₂ hac φ
    refine recRules_cons_rec mp hfresh hc₀ m₂ hac φ ?_
    intro rl hrl hfire
    rw [hname]
    exact hnew m₂ (by rw [hac, hname, hA]) φ rl hrl hfire
  -- the P cons
  obtain ⟨mp', hmp'⟩ :=
    declStep_preserves_of_ind_rec_cons mp (c₀ := c₀) (A := A) hfresh hnres
      ⟨⟨projFnName T i, lps, pty⟩, nP, nP, rules, hc₀⟩
      (ConsHead.ofFresh hwf
        (fun ψ => by rw [hAdef]; exact mp.base2.cval_closedL _ ψ)
        hnres (fun _ heq => by rw [hc₀] at heq; exact nomatch heq)
        hctorsHead)
      hAclosedH hAparamsH
      (fun ψ ρ => by rw [hAdef]; exact mp.base2.acval_wellDenoted _ _ _)
      (fun ψ ρ => by rw [hAdef]; exact mp.acval_validV _ _ _)
      (fun ψ => (htyExt ψ).imp (fun _ h => h.1))
      htyOkH hmemNewH hcapsH hrecH
  refine ⟨mp', by rw [hmp', hname, hA], ?_, ?_⟩
  · rw [hmp']
    exact projPhaseAcval_cons hname hinvA hfreshP hTf hCf hilt A hAdef
  · rw [hmp']
    exact blockAcvalInstalled_fresh_cons hIA hnotb₀ hstrNe₀

end ConLeche.Model
