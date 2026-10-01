module

public import ConLeche.Semantics.EnvFactsCons
import ConLeche.Semantics.DeclIndRun
import ConLeche.Verify.Denote.Levels

@[expose] public section

/-!
# The projection walk's front door, model-free (task #161 S7, Wall B)

The last of finding 8's three walks.  S6 landed its *bookkeeping* half
(`projFnInv`, `SetBase/EnvRCons.lean`: the phase invariant and the
block invariant at the installed environment are `projPhaseInvS_cons`
and `BlockInstalledTT.fresh_cons`, and every ingredient is a conjunct
of `ProjFnR`).  What was owed is the **carrier** at the projection
cons, and this module is it.

**The one hard field is `ty_denotes` at the head.**  A block member's
cons reads its head type's denotation straight off `ConstantValR`
(`EnvFacts.consBlockMember`'s `hty`); a projection entry cannot, because
the entry's *stored* type is `pty = mcv.type.renameConsts (projBack T
ctorName nF)` — the model projection's type read backwards.  Its
denotation therefore has to come from the model projection's, through
the phase invariant's renaming:

```
denote cval env ψ 0 pty
  = denote cval env ψ 0 (pty.renameConsts gPruned)   -- denote_renameConsts (projFwd_renameOkT hinv)
  = denote cval env ψ 0 (pty.renameConsts projFwd)   -- renameConsts_congr_resolve, at `hptyres`
  = denote cval env ψ 0 mcv.type                     -- ProjFnR's roundtrip `hround`
```

and the last one denotes because `mcv` is *stored* (`EnvFacts.ty_denotes`).
`projFwd_renameOkT` is already the base's (`SetBase/ProjPhase.lean`),
so nothing semantic enters.

The head's other two rule fields are cheap: `rec_params_le` is
`nP ≤ nP`, and `rec_rhs_denotes` is `ProjFnR`'s own rule front door
(`hrhsKey`) moved across the level instantiation by
`denote_instLevels` — the same join `SetBase/IndRecsCoreR.lean` makes
for the group's swapped rules.

Model-free by construction: no `V`, no `SetTheory`, no `EnvS`.
-/

namespace ConLeche.Semantics

open ConLeche.Term ConLeche.Verify

/-- The stored projection entry: a degenerate recursor, at whatever
rule list the caller installs.  (Moved to the base at task #161 S7 —
`SetR/Install/ProjInstallS.lean` was its only home and both lanes'
conses now name it.) -/
abbrev projEntry (T : Name) (lps : List Name) (pty : Expr)
    (nP i : Nat) (rules : List RecRule) : ConstantInfo :=
  .recInfo ⟨projFnName T i, lps, pty⟩ nP nP rules

/-- **The `EnvFacts` cons at a projection-function entry** — Wall B's
front door.  Parameterised by the rule list exactly as `projConsS` is,
because the projection bottom fires *below* the cons. -/
theorem EnvFacts.consProjFn {env' : Env} (m : EnvFacts env')
    {T ctorName : Name} {lps : List Name} {nP nF i : Nat}
    {rules : List RecRule}
    {mcv : ConstantVal} {mval : Expr} {mhint : ReducibilityHint}
    {pty : Expr}
    (hfm : env'.find? (projModelName T i)
      = some (.defnInfo mcv mval mhint))
    (hmlps : mcv.levelParams = lps)
    (hpnone : (env'.find? (projFnName T i)).isNone = true)
    (hround : (pty.renameConsts (projFwd T ctorName nF) == mcv.type)
      = true)
    (hptyres : pty.constsResolve env' = true)
    (hptyb : pty.looseBVarsBounded 0 = true)
    (hptyf : pty.hasFvar = false)
    (hptylp : pty.allLevelParamsDefined lps = true)
    (hinv : ProjPhaseInvS T ctorName nF env' m.cval)
    (hrulesWF : ∀ r ∈ rules,
      (RecRule.rhs r).hasFvar = false ∧
      (RecRule.rhs r).allLevelParamsDefined lps = true ∧
      (RecRule.rhs r).constsResolve env' = true ∧
      (RecRule.rhs r).looseBVarsBounded 0 = true ∧
      ∀ lvls pins, RecRule.fire r ≠ .nested lvls pins)
    (hrhsDen : ∀ r ∈ rules, RecRule.fire r ≠ .inert →
      ∀ ψ : Name → Nat,
        ∃ Rv, denoteClosed m.cval env' ψ (RecRule.rhs r) = some Rv) :
    ∃ m₁ : EnvFacts ⟨projEntry T lps pty nP i rules :: env'.consts⟩,
      m₁.cval = cvalWith m.cval (projFnName T i)
        (fun ψ => m.cval (projModelName T i) ψ) := by
  have hfresh : env'.find? (projFnName T i) = none :=
    Option.isNone_iff_eq_none.mp hpnone
  have hfresh0 : env'.find? (projEntry T lps pty nP i rules).name
      = none := hfresh
  obtain ⟨cval₀, hcval₀⟩ : ∃ c, c = cvalWith m.cval (projFnName T i)
      (fun ψ => m.cval (projModelName T i) ψ) := ⟨_, rfl⟩
  have hag : ∀ n, n ≠ projFnName T i → m.cval n = cval₀ n := by
    intro n hn
    rw [hcval₀, cvalWith_ne hn]
  have hi : Installs env' m.cval cval₀ (projEntry T lps pty nP i rules) :=
    Installs.of_fresh hfresh0
      (fun _ heq => ConstantInfo.noConfusion heq) hag
  have hselfA : ∀ ψ : Name → Nat,
      cval₀ (projFnName T i) ψ = m.cval (projModelName T i) ψ := by
    intro ψ
    rw [hcval₀]
    exact congrFun cvalWith_self ψ
  -- the head's type denotes: the model projection's, read backwards
  have htyHead : ∀ ψ : Name → Nat,
      ∃ t, denoteClosed m.cval env' ψ pty = some t := by
    intro ψ
    have hro := projFwd_renameOkT hinv
    have hcong : pty.renameConsts (fun n =>
        if (env'.find? n).isSome = true then
          projFwd T ctorName nF n else n)
        = pty.renameConsts (projFwd T ctorName nF) :=
      Expr.renameConsts_congr_resolve
        (fun n hn => by simp only [hn, if_true]) _ hptyres
    obtain ⟨t, ht⟩ :=
      m.ty_denotes (.defnInfo mcv mval mhint) (find?_mem hfm) ψ
    refine ⟨t, ?_⟩
    show denote m.cval env' ψ 0 pty = some t
    rw [← denote_renameConsts (φ := ψ) hro pty 0, hcong,
      eq_of_beq hround]
    exact ht
  -- the two lookup shapes in the extended store
  have hdown : ∀ (n : Name) (ci : ConstantInfo),
      (⟨projEntry T lps pty nP i rules :: env'.consts⟩ : Env).find? n
        = some ci →
      (n = projFnName T i ∧ ci = projEntry T lps pty nP i rules) ∨
        (n ≠ projFnName T i ∧ env'.find? n = some ci) := by
    intro n ci hf
    by_cases hn : (projEntry T lps pty nP i rules).name = n
    · rw [Env.find?_cons, if_pos hn] at hf
      exact Or.inl ⟨hn.symm, (Option.some.inj hf).symm⟩
    · rw [Env.find?_cons, if_neg hn] at hf
      exact Or.inr ⟨fun hh => hn hh.symm, hf⟩
  have hne : ∀ c ∈ env'.consts, c.name ≠ projFnName T i :=
    name_ne_of_mem_of_fresh hfresh0
  refine ⟨{
    cval := cval₀
    cval_closed := ?_
    wf := ?_
    val_params := ?_
    ty_denotes := ?_
    defn_eq := ?_
    rec_rhs_denotes := ?_
    rec_params_le := ?_
    proj_ok := ?_
    nat_op_guard := ?_ }, hcval₀⟩
  · -- closedness: the new leaf is the model projection's
    intro n ψ
    by_cases hn : n = projFnName T i
    · subst hn
      rw [hselfA]
      exact m.cval_closed _ _
    · rw [← hag n hn]
      exact m.cval_closed _ _
  · -- `EnvWF` at the extension
    refine EnvWF.cons m.wf ⟨hptyf, hptylp,
      Expr.constsResolve_mono hptyres, hptyb,
      (fun cv2 v2 h2 heq => ConstantInfo.noConfusion heq), ?_,
      (fun tbl heq => ConstantInfo.noConfusion heq),
      (fun cv2 caps heq => ConstantInfo.noConfusion heq)⟩
    intro cv2 mI2 rP2 rules2 heq r hr
    injection heq with h1 _ _ h4
    rw [← h4] at hr
    obtain ⟨w1, w2, w3, w4, w5⟩ := hrulesWF r hr
    refine ⟨w1, by rw [← h1]; exact w2,
      Expr.constsResolve_mono w3, w4, ?_⟩
    intro lvls pins hfr
    exact absurd hfr (w5 lvls pins)
  · -- level insensitivity
    intro n ci hf φ₁ φ₂ hp
    rcases hdown n ci hf with ⟨rfl, rfl⟩ | ⟨hn, hf'⟩
    · rw [hselfA, hselfA]
      refine m.val_params _ _ hfm φ₁ φ₂ ?_
      intro p hpm
      refine hp p ?_
      show p ∈ lps
      rw [← hmlps]
      exact hpm
    · rw [← hag n hn]
      exact m.val_params n ci hf' φ₁ φ₂ hp
  · -- the stored types denote
    intro c hc ψ
    rcases List.mem_cons.mp hc with rfl | h
    · obtain ⟨t, ht⟩ := htyHead ψ
      exact ⟨t, hi.denoteUp ht⟩
    · obtain ⟨t, ht⟩ := m.ty_denotes c h ψ
      exact ⟨t, hi.denoteUp ht⟩
  · -- definitional unfoldings: vacuous at a `.recInfo` head
    intro cv value hint hmem ψ
    rcases List.mem_cons.mp hmem with h | h
    · exact nomatch h
    · rw [← hag cv.name (hne _ h)]
      exact hi.denoteUp (m.defn_eq cv value hint h ψ)
  · -- the fired rules' right-hand sides denote
    intro n cv mI rP rules₂ hf r hr hfire us ψ hlen
    rcases hdown n _ hf with ⟨rfl, hci⟩ | ⟨hn, hf'⟩
    · obtain ⟨-, -, -, rfl⟩ := ConstantInfo.recInfo.inj hci
      obtain ⟨Rv, hRv⟩ :=
        hrhsDen r hr hfire (Level.substFn ψ cv.levelParams us)
      have hRv' : denote m.cval env' ψ 0
          ((RecRule.rhs r).instantiateLevelParams cv.levelParams us)
          = some Rv := by
        rw [denote_instLevels m.val_params ψ 0 (RecRule.rhs r)]
        exact hRv
      exact ⟨Rv, hi.denoteUp hRv'⟩
    · obtain ⟨R, hR⟩ := m.rec_rhs_denotes n cv mI rP rules₂ hf' r hr
        hfire us ψ hlen
      exact ⟨R, hi.denoteUp hR⟩
  · -- the parameter bound: `nP ≤ nP` at the head
    intro n cv mI rP rules₂ hf r hr hfire
    rcases hdown n _ hf with ⟨rfl, hci⟩ | ⟨hn, hf'⟩
    · obtain ⟨-, rfl, rfl, -⟩ := ConstantInfo.recInfo.inj hci
      exact Nat.le_refl _
    · exact m.rec_params_le n cv mI rP rules₂ hf' r hr hfire
  · -- the projection table: the head is a recursor, not an entry
    exact ProjOkT.cons m.proj_ok hfresh0
      (fun entry heq => ConstantInfo.noConfusion heq)
  · -- the `Nat`-op guard: the head is not a definition
    intro c hmem hst
    obtain ⟨cv, v, hh, hf⟩ := natOpStored_inv hst
    rcases hdown c _ hf with ⟨rfl, hci⟩ | ⟨hn, hf'⟩
    · exact nomatch hci
    · refine natOpGuard_cons hfresh0 (m.nat_op_guard c hmem ?_)
      simp [natOpStored, hf']

/-- **The projection entry's own syntactic obligations**, off
`ProjFnR` alone (task #161 S7): the extended store's `EnvWF` and the
stored rule's constructor.  Both lanes' conses need them — the R lane
inside `projConsS`, the P lane at `projCons` — and neither is
semantic. -/
theorem projFn_head {μ : CheckMode} {F : Nat} {env' env₁ : Env}
    {T ctorName : Name} {lps : List Name}
    {nP nF i : Nat}
    (hwfE : EnvWF env')
    (hR : ProjFnRun μ F env' T ctorName lps nP nF i env₁) :
    EnvWF env₁ ∧
      ∀ (cvR : ConstantVal) (mI rP : Nat) (rules : List RecRule),
        (env₁.consts.headD default) = .recInfo cvR mI rP rules →
        ∀ r ∈ rules, ∃ cvj cnP cnF,
          env'.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF) := by
  obtain ⟨cvj, mcv, mval, mhint, pty, rhsA, hctor, hfm, hmlps, hpnone,
    hTf, heqf, hptyB, hround, hptyres, hptyb, hptyf, hptylp, hstrip1,
    hilt, hstripP, hbig, henv⟩ := hR
  obtain ⟨cbinders, cbody, hCstrip, hcbodyArity, hcbodyHead, hrhsw,
    hrhsb, hrlp, hrres, hrstrip, hrhsKey, -, -⟩ := hbig
  subst henv
  have hrulesWF : ∀ r ∈ [projFnRule env'.find? T ctorName pty nP nF i rhsA],
      (RecRule.rhs r).hasFvar = false ∧
      (RecRule.rhs r).allLevelParamsDefined lps = true ∧
      (RecRule.rhs r).constsResolve env' = true ∧
      (RecRule.rhs r).looseBVarsBounded 0 = true ∧
      ∀ lvls pins, RecRule.fire r ≠ .nested lvls pins := by
    intro r hr
    rcases List.mem_cons.mp hr with rfl | h
    · refine ⟨hrhsw, hrlp, hrres, hrhsb, ?_⟩
      intro lvls pins
      by_cases hc : Expr.recRulePlain pty nP nP nP = true
      · simp only [projFnRule, recRuleBits, hc, if_true]
        exact fun hh => nomatch hh
      · simp only [projFnRule, recRuleBits, eq_false_of_ne_true hc]
        exact fun hh => nomatch hh
    · exact nomatch h
  refine ⟨?_, ?_⟩
  · refine EnvWF.cons hwfE ⟨hptyf, hptylp,
      Expr.constsResolve_mono hptyres, hptyb,
      (fun cv2 v2 h2 heq => ConstantInfo.noConfusion heq), ?_,
      (fun tbl heq => ConstantInfo.noConfusion heq),
      (fun cv2 caps heq => ConstantInfo.noConfusion heq)⟩
    intro cv2 mI2 rP2 rules2 heq r hr
    injection heq with h1 _ _ h4
    rw [← h4] at hr
    obtain ⟨w1, w2, w3, w4, w5⟩ := hrulesWF r hr
    refine ⟨w1, by rw [← h1]; exact w2,
      Expr.constsResolve_mono w3, w4, ?_⟩
    intro lvls pins hfr
    exact absurd hfr (w5 lvls pins)
  · intro cvR mI rP rules heq r hr
    injection heq with _ _ _ h4
    rw [← h4] at hr
    rcases List.mem_cons.mp hr with rfl | h
    · exact ⟨cvj, nP, nF, hctor⟩
    · exact nomatch h

/-! ## Two shared projection-phase constants (task #161 S7)

Relocated verbatim from `SetR/Install/ProjInstallS.lean`: both lanes'
projection conses read them and neither reading is semantic. -/

/-- The model projection's own name is a `projFwd` fixed point: it is
not the family, not the constructor (their stored *kinds* differ), and
not shaped like a public projection. -/
theorem projFwd_model_self {T ctorName : Name} {nF i : Nat}
    (hC : projModelName T i ≠ ctorName) :
    projFwd T ctorName nF (projModelName T i) = projModelName T i := by
  unfold projFwd
  rw [if_neg (show ¬projModelName T i = T from Name.str_str_ne T _ _),
    if_neg hC]
  rw [show (List.range nF).find?
      (fun j => projModelName T i == projFnName T j) = none from by
    rw [List.find?_eq_none]
    intro j _
    intro hh
    exact Name.num_ne_str _ _ _ _ (eq_of_beq hh).symm]

end ConLeche.Semantics
