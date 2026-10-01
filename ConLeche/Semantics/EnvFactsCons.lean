module

public import ConLeche.Semantics.EnvFacts
public import ConLeche.Semantics.DeclIndRun
public import ConLeche.Semantics.IndBlockFacts
import ConLeche.Verify.Extend.Block

import ConLeche.Verify.Extend.Ind

public import ConLeche.Semantics.ProjPhase

@[expose] public section
/-!
# The `EnvFacts`-level cons for the block folds (task #161 S6, the opener)

`ConLeche/SetR/Bridge/DeclInd.lean`'s **finding 8** is the last place the
bridge needs a model: `IndMembersR` carries a `ConstantValR` at *each
intermediate environment* of the member fold, and — as landed at S5 —
nothing built an `EnvFacts` there except by projection from the `EnvS` the
install fold was producing.  Bridge and install therefore had to walk
together, and that is what kept `checkDeclR_sound`'s `m`, hence
`FoldP`'s `mp.base`, hence `EnvModelM.base`, alive.

**The one lemma that was missing** is stated here: a `denote`
transport across a fresh cons **with a changed valuation**
(`denote_mono` fixes `cval`; `denote_cval_congr` fixes the
environment).  The two are already one bundle — `Installs`
(`Verify/Denote/Install.lean`) — so the transport itself is
`Installs.denoteUp`, and what this module contributes is the field-by-
field `EnvFacts` cons that consumes it (`EnvFacts.consBlockMember`), plus the
`EnvFacts` twin of `memberInstallS`'s *invariant* half
(`memberInstallR`).

**Why every field goes through** (the S5 seal's table, checked):

| `EnvFacts` field | at a block-member cons |
|---|---|
| `cval` | `cvalModeled m.cval cvA.name` — the model artifact's leaf |
| `cval_closed` | inherited: `cvalModeled` only ever re-points a name at *another old leaf* |
| `wf` | a premise; the install proves it model-free (`EnvWF.cons` off `ConstantValR`'s guards) |
| `val_params` | the head from `m.val_params` at the *model artifact's* entry, the rest inherited |
| `ty_denotes` | the head from `ConstantValR`'s own `denoteClosed` conjunct, the old ones by `Installs.denoteUp` |
| `defn_eq`, `thm_ok`, `rec_rhs_denotes`, `rec_params_le` | vacuous at the head (a member is `.indInfo`/`.ctorInfo`/rule-less `.recInfo`), transported below |
| `proj_ok` | `ProjOkT.cons`, head vacuous |
| `nat_op_guard` | `natOpGuard_cons`; the head is not a `defnInfo`, so `natOpStored` cannot name it |

Everything here is model-free by construction: no `V`, no `SetTheory`,
no `EnvS`.  Both lanes consume it — the R lane through
`Bridge/DeclInd.lean`, the P lane through its own ind tier.
-/

namespace ConLeche.Semantics

open ConLeche.Term ConLeche.Verify

/-- A block member's kind: an `.indInfo`, a `.ctorInfo`, or a
*rule-less* `.recInfo` (the provisioning's shape).  Named because six
of the cons's field proofs case on exactly this. -/
def BlockMemberKind (c₀ : ConstantInfo) (cvA : ConstantVal) : Prop :=
  (∃ caps, c₀ = .indInfo cvA caps) ∨
    (∃ nP nF, c₀ = .ctorInfo cvA nP nF) ∨
    (∃ mI rP, c₀ = .recInfo cvA mI rP [])

/-- A stored constant is not the fresh one.  (`declStep_preserves_of_cons`'s
`hne`, which every cons re-derives.) -/
theorem name_ne_of_mem_of_fresh {env : Env} {c₀ : ConstantInfo}
    (hfresh : env.find? c₀.name = none) :
    ∀ c ∈ env.consts, c.name ≠ c₀.name := by
  have h0 := hfresh
  rw [ConLeche.Env.find?, List.find?_eq_none] at h0
  intro c hc h
  exact h0 c hc (by simp [h])

/-- **The `EnvFacts` cons at a block member** — finding 8's missing lemma.

The member takes the model artifact's leaf (`cvalModeled`), so the new
valuation re-points one name at another *old* name's value: no new
denotation is created, and every old field transports through the
`Installs` bundle.  The type's denotation at the head is
`ConstantValR`'s own `denoteClosed` conjunct, passed in as `hty` — the
bridge has it from `memberValR_of`, the install from the front door. -/
theorem EnvFacts.consBlockMember {env : Env} (m : EnvFacts env)
    {c₀ : ConstantInfo} {cvA : ConstantVal}
    (hc₀cv : c₀.toConstantVal = cvA) (hc₀name : c₀.name = cvA.name)
    (hkind : BlockMemberKind c₀ cvA)
    (hfresh : env.find? cvA.name = none)
    (hwf : EnvWF ⟨c₀ :: env.consts⟩)
    {cvm : ConstantVal} {mval : Expr} {hint : ReducibilityHint}
    (hmE : env.find? (cvA.name.str "_model")
      = some (.defnInfo cvm mval hint))
    (hmlps : cvm.levelParams = cvA.levelParams)
    (hty : ∀ ψ : Name → Nat,
      ∃ t, denoteClosed m.cval env ψ cvA.type = some t) :
    ∃ m₁ : EnvFacts ⟨c₀ :: env.consts⟩,
      m₁.cval = cvalModeled m.cval cvA.name := by
  have hfresh' : env.find? c₀.name = none := by rw [hc₀name]; exact hfresh
  have hne := name_ne_of_mem_of_fresh hfresh'
  -- the install context: the valuation moves only at the new name
  have hi : Installs env m.cval (cvalModeled m.cval cvA.name) c₀ :=
    Installs.of_fresh hfresh'
      (by rcases hkind with ⟨caps, rfl⟩ | ⟨nP, nF, rfl⟩ | ⟨mI, rP, rfl⟩ <;>
            intro _ h <;> exact nomatch h)
      (fun n hn => by
      rw [hc₀name] at hn
      exact (cvalWith_ne hn).symm)
  -- the head is none of the value kinds, and its rules (if any) are []
  have hndefn : ∀ cv2 v2 h2, c₀ ≠ .defnInfo cv2 v2 h2 := by
    rcases hkind with ⟨caps, rfl⟩ | ⟨nP, nF, rfl⟩ | ⟨mI, rP, rfl⟩ <;>
      intro cv2 v2 h2 heq <;> exact nomatch heq
  have hnproj : ∀ entry, c₀ ≠ .projInfo entry := by
    rcases hkind with ⟨caps, rfl⟩ | ⟨nP, nF, rfl⟩ | ⟨mI, rP, rfl⟩ <;>
      intro entry heq <;> exact nomatch heq
  have hnorules : ∀ cv2 mI2 rP2 rules2,
      c₀ = .recInfo cv2 mI2 rP2 rules2 → rules2 = [] := by
    rcases hkind with ⟨caps, rfl⟩ | ⟨nP, nF, rfl⟩ | ⟨mI, rP, rfl⟩ <;>
      intro cv2 mI2 rP2 rules2 heq
    · exact nomatch heq
    · exact nomatch heq
    · injection heq with _ _ _ h4
      exact h4.symm
  -- the head's stored level parameters are the member's
  have hlpsA : c₀.toConstantVal.levelParams = cvA.levelParams := by
    rw [hc₀cv]
  -- the two shapes of a lookup in the extended store
  have hdown : ∀ (n : Name) (ci : ConstantInfo),
      (⟨c₀ :: env.consts⟩ : Env).find? n = some ci →
      (n = c₀.name ∧ ci = c₀) ∨
        (n ≠ c₀.name ∧ env.find? n = some ci) := by
    intro n ci hf
    by_cases hn : c₀.name = n
    · subst hn
      rw [Env.find?_cons, if_pos rfl] at hf
      exact Or.inl ⟨rfl, (Option.some.inj hf).symm⟩
    · rw [Env.find?_cons, if_neg hn] at hf
      exact Or.inr ⟨fun hh => hn hh.symm, hf⟩
  refine ⟨{
    cval := cvalModeled m.cval cvA.name
    cval_closed := ?_
    wf := hwf
    val_params := ?_
    ty_denotes := ?_
    defn_eq := ?_
    rec_rhs_denotes := ?_
    rec_params_le := ?_
    proj_ok := ?_
    nat_op_guard := ?_ }, rfl⟩
  · -- closedness: the new leaf is an old leaf
    intro n ψ
    by_cases hn : n = cvA.name
    · subst hn
      rw [show cvalModeled m.cval cvA.name cvA.name
          = fun ψ => m.cval (cvA.name.str "_model") ψ from cvalWith_self]
      exact m.cval_closed _ _
    · rw [show cvalModeled m.cval cvA.name n = m.cval n from cvalWith_ne hn]
      exact m.cval_closed _ _
  · -- level insensitivity
    intro n ci hf φ₁ φ₂ hp
    rcases hdown n ci hf with ⟨rfl, rfl⟩ | ⟨hn, hf'⟩
    · rw [hc₀name,
        show cvalModeled m.cval cvA.name cvA.name
          = fun ψ => m.cval (cvA.name.str "_model") ψ from cvalWith_self]
      refine m.val_params _ _ hmE φ₁ φ₂ ?_
      intro p hpm
      exact hp p (by rw [hlpsA, ← hmlps]; exact hpm)
    · rw [show cvalModeled m.cval cvA.name n = m.cval n from
        cvalWith_ne (by rw [hc₀name] at hn; exact hn)]
      exact m.val_params n ci hf' φ₁ φ₂ hp
  · -- the stored types denote
    intro c hc ψ
    rcases List.mem_cons.mp hc with rfl | h
    · obtain ⟨t, ht⟩ := hty ψ
      exact ⟨t, hi.denoteUp (by rw [hc₀cv]; exact ht)⟩
    · obtain ⟨t, ht⟩ := m.ty_denotes c h ψ
      exact ⟨t, hi.denoteUp ht⟩
  · -- the definitional unfoldings: vacuous at the head
    intro cv value hint' hmem ψ
    rcases List.mem_cons.mp hmem with h | h
    · exact absurd h.symm (hndefn cv value hint')
    · rw [show cvalModeled m.cval cvA.name cv.name = m.cval cv.name from
        cvalWith_ne (by rw [← hc₀name]; exact hne _ h)]
      exact hi.denoteUp (m.defn_eq cv value hint' h ψ)
  · -- the fired rules' right-hand sides denote: vacuous at the head
    intro n cv mI rP rules hf r hr hfire us ψ hlen
    rcases hdown n _ hf with ⟨rfl, hci⟩ | ⟨hn, hf'⟩
    · rw [hnorules cv mI rP rules hci.symm] at hr
      exact nomatch hr
    · obtain ⟨R, hR⟩ := m.rec_rhs_denotes n cv mI rP rules hf' r hr hfire
        us ψ hlen
      exact ⟨R, hi.denoteUp hR⟩
  · -- the parameter bound: vacuous at the head
    intro n cv mI rP rules hf r hr hfire
    rcases hdown n _ hf with ⟨rfl, hci⟩ | ⟨hn, hf'⟩
    · rw [hnorules cv mI rP rules hci.symm] at hr
      exact nomatch hr
    · exact m.rec_params_le n cv mI rP rules hf' r hr hfire
  · -- the projection table: the head is no entry
    exact ProjOkT.cons m.proj_ok hfresh'
      (fun entry heq => absurd heq (hnproj entry))
  · -- the `Nat`-op guard: the head is not a definition
    intro c hmem hst
    obtain ⟨cv, v, hh, hf⟩ := natOpStored_inv hst
    rcases hdown c _ hf with ⟨rfl, hci⟩ | ⟨hn, hf'⟩
    · exact absurd hci.symm (hndefn cv v hh)
    · refine natOpGuard_cons hfresh' (m.nat_op_guard c hmem ?_)
      simp [natOpStored, hf']

/-! ## The member install's invariant half, model-free

`memberInstallS`'s conclusion is four facts, and **three of them never
needed a model**: the extended store's `EnvWF`, the block-installed
invariant, and the two η side invariants are proved by
`EnvWF.cons`/`BlockInstalledTT.step`/`EtaFamiliesClosedO.cons`/
`BlockEtaPinned.cons`, all `V`-free, off `MemberValR`'s own conjuncts.
Only the `EnvS` itself needed `indMemberS`.

They are extracted here so that `memberInstallS` (the R install) and
`memberInstallR` (the bridge/P side) are the *same* proof of the same
three facts — the S5 finding's discipline: when an install and a
relation both prove a preservation fact, prove it at the relation. -/

/-- **The three model-free conclusions of a block-member install.** -/
theorem memberInstallInv {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {env : Env} {cval : TConstVal}
    (hwfE : EnvWF env)
    {cv cvA : ConstantVal} {c₀ : ConstantInfo}
    (hmv : MemberValRun μ F env blockNames cv cvA)
    (hI : BlockInstalledTT blockNames env cval)
    (hbn : blockNames.contains cvA.name = true)
    (hpins : ∀ caps, c₀ = .indInfo cvA caps →
      EtaPins μ env cv.name cv.levelParams caps ∧
        (caps.eta = true → blockNames.contains caps.etaCtor = true) ∧
        (caps.eta = true → 0 < caps.etaFields →
          env.find? (projFnName cv.name 0) = none))
    (hEC : EtaFamiliesClosedO blockNames env)
    (hBP : BlockEtaPinned μ blockNames env)
    (hc₀cv : c₀.toConstantVal = cvA) (hc₀name : c₀.name = cvA.name)
    (hkind : BlockMemberKind c₀ cvA)
    -- the capability arities of an inductive member
    (hicw : IndCapsWF c₀) :
    EnvWF ⟨c₀ :: env.consts⟩ ∧
      BlockInstalledTT blockNames ⟨c₀ :: env.consts⟩
        (cvalModeled cval cvA.name) ∧
      EtaFamiliesClosedO blockNames ⟨c₀ :: env.consts⟩ ∧
      BlockEtaPinned μ blockNames ⟨c₀ :: env.consts⟩ := by
  obtain ⟨type', hcv, hcvA, hms, cvm, mval, hint, hmE, hmlps, hren⟩ :=
    id hmv
  obtain ⟨hfind, hnres, hpshape, hnd, hlbt, hitf, hann, htp, htr, -⟩ :=
    hcv
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann hitf hlbt
  have hnameA : cvA.name = cv.name := by rw [hcvA]
  have hlpsA : cvA.levelParams = cv.levelParams := by rw [hcvA]
  have htypeA : cvA.type = type' := by rw [hcvA]
  have hfreshA : env.find? cvA.name = none := by
    rw [hnameA]
    exact Option.isNone_iff_eq_none.mp hfind
  have hwf : EnvWF ⟨c₀ :: env.consts⟩ := by
    refine EnvWF.cons hwfE ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hicw⟩
    · rw [hc₀cv, htypeA]; exact htf'
    · rw [hc₀cv, htypeA, hlpsA]; exact htp
    · rw [hc₀cv, htypeA]; exact Expr.constsResolve_mono htr
    · rw [hc₀cv, htypeA]; exact hbt'
    · rcases hkind with ⟨caps', rfl⟩ | ⟨nP, nF, rfl⟩ | ⟨mI, rP, rfl⟩ <;>
        intro cv2 v2 h2 heq <;> exact nomatch heq
    · rcases hkind with ⟨caps', rfl⟩ | ⟨nP, nF, rfl⟩ | ⟨mI, rP, rfl⟩ <;>
        intro cv2 mI2 rP2 rules2 heq
      · exact nomatch heq
      · exact nomatch heq
      · injection heq with _ _ _ h4
        intro r hr
        rw [← h4] at hr
        exact nomatch hr
    · rcases hkind with ⟨caps', rfl⟩ | ⟨nP, nF, rfl⟩ | ⟨mI, rP, rfl⟩ <;>
        intro tbl heq <;> exact nomatch heq
  have hpinsA : ∀ caps, c₀ = .indInfo cvA caps →
      EtaPins μ env cvA.name cvA.levelParams caps ∧
        (caps.eta = true → blockNames.contains caps.etaCtor = true) ∧
        (caps.eta = true → 0 < caps.etaFields →
          env.find? (projFnName cvA.name 0) = none) := by
    intro caps2 hceq
    exact ⟨by rw [hnameA, hlpsA]; exact (hpins caps2 hceq).1,
      (hpins caps2 hceq).2.1,
      by rw [hnameA]; exact (hpins caps2 hceq).2.2⟩
  have hfresh0 : env.find? c₀.name = none := by
    rw [hc₀name]; exact hfreshA
  have hbn0 : blockNames.contains c₀.name = true := by
    rw [hc₀name]; exact hbn
  have hshape0 : c₀.name.isProjFnShape = false := by
    rw [hc₀name, hnameA]; exact hpshape
  refine ⟨hwf, ?_, EtaFamiliesClosedO.cons hEC hfresh0 hbn0,
    BlockEtaPinned.cons hBP hfresh0 hshape0
      (fun cvS capsS heq hcape => by
        have hcvS : cvS = cvA := by rw [← hc₀cv, heq]; rfl
        subst hcvS
        exact ⟨by rw [hc₀name]; exact (hpinsA capsS heq).1,
          (hpinsA capsS heq).2.1 hcape,
          by rw [hc₀name]; exact (hpinsA capsS heq).2.2 hcape⟩)⟩
  refine BlockInstalledTT.step hI (by rw [hc₀name]; exact hms)
    (by rw [hc₀name]; exact hmE)
    (by rw [hc₀cv]; exact hmlps)
    (by rw [hc₀cv]; exact hren)
    (fun ψ => by
      rw [hc₀name]
      exact congrFun cvalWith_self ψ)
    (fun n ψ hn => by
      rw [hc₀name] at hn
      exact congrFun (cvalWith_ne hn) ψ)

/-! ## The projection install's invariant half, model-free

The same extraction one fold over: of `projFnS`'s four conclusions,
the `EnvS` needs `projConsS` (the front door is semantic — the field
selector's value must inhabit its type), but the **phase invariant**
and the **block invariant** at the installed environment are
`projPhaseInvS_cons` and `BlockInstalledTT.fresh_cons`, and every
ingredient they take is a conjunct of `ProjFnR` itself.

So the projection walk's *bookkeeping* is model-free even though its
front door is not — which is the honest statement of how much of
finding 8's third walk is left (see the S6 seal). -/

/-- **The phase invariant crosses a projection cons.**  Parameterised
by the head entry, because both the provisioned (rule-less) and the
ruled entry need it — they differ only in a rule list, which the
invariant never reads.  (Moved to the base at task #161 S6, unchanged:
`projFnInv` below is the second consumer and the P lane must reach
it.) -/
theorem projPhaseInvS_cons {T ctorName : Name} {nF : Nat} {env' : Env}
    {cval cval₀ : TConstVal} {c₀ : ConstantInfo} {lps : List Name}
    {pty : Expr} {i : Nat} {mcv : ConstantVal} {mval : Expr}
    {mhint : ReducibilityHint}
    (hcvA : c₀.toConstantVal = ⟨projFnName T i, lps, pty⟩)
    (hinv : ProjPhaseInvS T ctorName nF env' cval)
    (hfresh : env'.find? (projFnName T i) = none)
    (hTf : (env'.find? T).isSome = true)
    (hCf : (env'.find? ctorName).isSome = true)
    (hfm : env'.find? (projModelName T i)
      = some (.defnInfo mcv mval mhint))
    (hmlps : mcv.levelParams = lps)
    (hilt : i < nF)
    (hself : ∀ ψ : Name → Nat,
      cval₀ (projFnName T i) ψ = cval (projModelName T i) ψ)
    (hag : ∀ n, n ≠ projFnName T i → cval n = cval₀ n) :
    ProjPhaseInvS T ctorName nF ⟨c₀ :: env'.consts⟩ cval₀ := by
  have hname : c₀.name = projFnName T i := by
    rw [show c₀.name = c₀.toConstantVal.name from rfl, hcvA]
  -- the head's name differs from every name the invariant reads
  have hneP : ∀ n : Name, (env'.find? n).isSome = true →
      n ≠ projFnName T i := by
    intro n hn hh
    rw [hh, hfresh] at hn
    exact nomatch hn
  have hne : ∀ n : Name, (env'.find? n).isSome = true →
      ¬c₀.name = n :=
    fun n hn hh => hneP n hn (by rw [← hh, hname])
  have hmodelNeP : ∀ j : Nat, projModelName T j ≠ projFnName T i :=
    fun j hh => Name.num_ne_str _ _ _ _ hh.symm
  have hmodelNe : ∀ (j : Nat), ¬c₀.name = projModelName T j :=
    fun j hh => hmodelNeP j (by rw [← hh, hname])
  have hdown : ∀ (n : Name) (ci : ConstantInfo),
      Env.find? ⟨c₀ :: env'.consts⟩ n = some ci → ¬c₀.name = n →
      env'.find? n = some ci := by
    intro n ci hf hn
    rw [Env.find?_cons, if_neg hn] at hf
    exact hf
  have hup : ∀ (n : Name) (ci : ConstantInfo),
      env'.find? n = some ci → ¬c₀.name = n →
      Env.find? ⟨c₀ :: env'.consts⟩ n = some ci := by
    intro n ci hf hn
    rw [Env.find?_cons, if_neg hn]
    exact hf
  have hstrNeP : ∀ n : Name, n.str "_model" ≠ projFnName T i :=
    fun n hh => Name.num_ne_str _ _ _ _ hh.symm
  have hstrNe : ∀ n : Name, ¬c₀.name = n.str "_model" :=
    fun n hh => hstrNeP n (by rw [← hh, hname])
  refine ⟨?_, ?_, ?_⟩
  · intro ci hf
    obtain ⟨cvm, mv, hm, hfm', hlps', hv'⟩ :=
      hinv.1 ci (hdown T ci hf (hne T hTf))
    refine ⟨cvm, mv, hm, hup _ _ hfm' (hstrNe T), hlps', ?_⟩
    intro ψ
    rw [← hag T (hneP T hTf), ← hag _ (hstrNeP T)]
    exact hv' ψ
  · intro ci hf
    obtain ⟨cvm, mv, hm, hfm', hlps', hv'⟩ :=
      hinv.2.1 ci (hdown ctorName ci hf (hne ctorName hCf))
    refine ⟨cvm, mv, hm, hup _ _ hfm' (hstrNe ctorName), hlps', ?_⟩
    intro ψ
    rw [← hag ctorName (hneP ctorName hCf), ← hag _ (hstrNeP ctorName)]
    exact hv' ψ
  · intro j hj ci hf
    by_cases hji : j = i
    · subst hji
      rw [Env.find?_cons, if_pos hname] at hf
      obtain rfl := Option.some.inj hf
      refine ⟨mcv, mval, mhint, hup _ _ hfm (hmodelNe j), ?_, ?_⟩
      · rw [hcvA, hmlps]
      · intro ψ
        rw [hself, ← hag _ (hmodelNeP j)]
    · have hjneP : projFnName T j ≠ projFnName T i := by
        intro hh
        have hh2 : Name.num (T.str "proj") j
          = Name.num (T.str "proj") i := hh
        injection hh2 with _hp hij
        exact hji hij
      have hjne : ¬c₀.name = projFnName T j :=
        fun hh => hjneP (by rw [← hh, hname])
      obtain ⟨cvm, mv, hm, hfm', hlps', hv'⟩ :=
        hinv.2.2 j hj ci (hdown _ ci hf hjne)
      refine ⟨cvm, mv, hm, hup _ _ hfm' (hmodelNe j), hlps', ?_⟩
      intro ψ
      rw [← hag _ hjneP, ← hag _ (hmodelNeP j)]
      exact hv' ψ

/-- **The two model-free conclusions of a projection-function
install** — `projFnS`'s invariant half, off the record alone. -/
theorem projFnInv {μ : CheckMode} {F : Nat} {env' env₁ : Env}
    {cval : TConstVal} {T ctorName : Name} {lps : List Name}
    {nP nF i : Nat} {blockNames : List Name}
    (hR : ProjFnRun μ F env' T ctorName lps nP nF i env₁)
    (hinv : ProjPhaseInvS T ctorName nF env' cval)
    (hIB : BlockInstalledTT blockNames env' cval)
    (hbshape : ∀ n, blockNames.contains n = true →
      n.isProjFnShape = false) :
    ProjPhaseInvS T ctorName nF env₁
        (cvalWith cval (projFnName T i)
          (fun ψ => cval (projModelName T i) ψ)) ∧
      BlockInstalledTT blockNames env₁
        (cvalWith cval (projFnName T i)
          (fun ψ => cval (projModelName T i) ψ)) := by
  obtain ⟨cvj, mcv, mval, mhint, pty, rhsA, hctor, hfm, hmlps, hpnone,
    hTf, heqf, hptyB, hround, hptyres, hptyb, hptyf, hptylp, hstrip1,
    hilt, hstripP, hbig, henv⟩ := hR
  subst henv
  have hfresh : env'.find? (projFnName T i) = none :=
    Option.isNone_iff_eq_none.mp hpnone
  have hCf : (env'.find? ctorName).isSome = true := by rw [hctor]; rfl
  have hnotb : blockNames.contains (projFnName T i) = false := by
    cases hc : blockNames.contains (projFnName T i) with
    | false => rfl
    | true =>
      exact absurd (hbshape _ hc)
        (by rw [show (projFnName T i).isProjFnShape = true from rfl]
            exact fun hh => nomatch hh)
  exact ⟨projPhaseInvS_cons rfl hinv hfresh hTf hCf hfm hmlps hilt
      (fun ψ => congrFun cvalWith_self ψ)
      (fun n hn => (cvalWith_ne hn).symm),
    BlockInstalledTT.fresh_cons hIB hnotb hfresh
      (fun n ψ hn => congrFun (cvalWith_ne hn) ψ)⟩

end ConLeche.Semantics
