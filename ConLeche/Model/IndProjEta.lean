module

public import ConLeche.Model.IndProjCaps
public import ConLeche.Model.IndEtaLaw
import ConLeche.Model.Annot.BitLevels
public section

/-!
# The η key at the projection cons (task #161, IND TIER part 3, step 5b)

`capsOk_cons_proj` leaves exactly one law open — `EtaLaw` for the
family the projection-function cons *completes* — and this file is it.
It is `etaLawKeyS`'s transpose with the half `memberEtaLaw` was
allowed to drop put back.

## What changes against the member key, and what does not

Part 2's §4 recorded that `etaFields = 0` "deletes half of
`etaLawKeyS`", and that the deletion does **not** transfer to the
projection cons.  That prediction held exactly, and the returning half
is smaller than the phrase suggests: `memberEtaLaw`'s skeleton is
reused move for move, and the projection spine enters at exactly three
points —

* the fabricated spine is `ts ++ projSpines …` instead of `ts`;
* the pinned body `hsbody` carries `etaFields` further arguments, so
  `hCs`'s right-hand side is the model constructor applied to the
  parameter spine **and** to one model-projection application per
  field;
* each of those applications is evaluated by the *same*
  `interp_bvarSpine` the parameter spine uses.

That last point is the reason this file is short.  The projection
argument's pinned spine is
`((range nP).map fun k => bvar (nP - k)) ++ [bvar 0]`, and that list
**is** `(range (nP+1)).map fun k => bvar (nP - k)` — the member slot is
the `k = nP` entry of the same descending family.  So one
`instSeq_openSpine` at `nP+1` reads it, and one `interp_bvarSpine` at
the spine `ts ++ [x]` evaluates it, with the side condition
`σ (nP - q) = consN (ts ++ [x]) ρ (nP - q)` — which is *reflexivity*,
because `consN (ts ++ [x]) ρ` is `σ` itself.  The parameter spine's
own side condition needed an `omega`; the projection spine's needs
nothing.

## Three premises the member key did not need, and one it did

* **`hvP`** — the projection valuation identifications, v1's third
  install-supplied identification (`etaLawKeyS` takes `hvT`/`hvC`/`hvP`
  and part 2 derived the first two from `BlockAcvalInstalled`).  There
  is no invariant to derive this one from: the family's *earlier*
  projection slots were installed by earlier `ProjInstallR` steps, so
  the identification is the install fold's to carry, exactly as in v1.
  Taking it as a premise is part 2's own lesson applied before it
  could bite — the conclusion transposes, the premise set is
  re-derived from `etaLawKeyS`'s premises.
* **`hprojE`** is *not* a new premise: `EtaPins` already carries the
  model projections' lookups (`Verify/Extend/Iota.lean:1067-1069`), and
  the member key destructured them away unused.

Against that, two of the member key's own obligations **disappear**
here, for `projEtaSplit`'s reason: a `recInfo` cons can be neither the
family's former nor its capability constructor, so `hvT` and `hvC` are
one `acvalWith_ne` each with no case split, where the member key had
to branch on "is the cons the former?" four times over.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics ConLeche.SetModel
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  IndCaps ReducibilityHint BinderMeta)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {F : Nat}

/-! ## The pinned projection argument, read and evaluated

The one genuinely new move.  Everything else in this file is
`memberEtaLaw`'s. -/

/-- The pinned projection argument's spine is the parameter spine's
own descending family, one entry longer: the member slot is its
`k = nP` entry. -/
theorem projArgSpine_eq (nP : Nat) :
    (((List.range nP).map fun k => Expr.bvar (nP - k)) ++ [Expr.bvar 0])
      = (List.range (nP + 1)).map fun k => Expr.bvar (nP - k) := by
  rw [List.range_succ, List.map_append, List.map_cons, List.map_nil,
    Nat.sub_self]

/-- `instSeq_openSpine` at the *list* level.  The member key only ever
needed the `mkAppN`-wrapped form, because its constructor argument was
one flat parameter spine; here the constructor's spine is
`params ++ projections` and the two halves must be opened separately,
so the wrapper has to come off. -/
theorem instSeq_openSpine_list (nP L t : Nat) (hnL : nP ≤ L)
    (hnP : nP ≤ t + 1) :
    ((List.range nP).map fun k => Expr.bvar (t - k)).map
        (Expr.instSeq (openFvars 0 L) t)
      = openFvars 0 nP := by
  rw [List.map_map]
  refine List.ext_getElem (by simp) fun q h1 h2 => ?_
  have hq : q < nP := by simpa using h1
  rw [List.getElem_map, List.getElem_range]
  show Expr.instSeq (openFvars 0 L) t (Expr.bvar (t - q))
    = (openFvars 0 nP)[q]
  have hbnd := openFvars_getElem? (d := 0) (k := nP) (i := q) hq
  rw [List.getElem?_eq_getElem h2] at hbnd
  rw [Option.some.inj hbnd]
  have hhit := Expr.instSeq_bvar (openFvars 0 L) t (t - q)
    (openFvars_bounded 0 L) (by omega)
    (by rw [openFvars_length]; omega)
  rw [show t - (t - q) = q from by omega,
    openFvars_getElem? (d := 0) (k := L) (i := q) (by omega)] at hhit
  exact (Option.some.inj hhit).symm

/-- `interp` of an application spine, as a `map`-then-`foldl`.  The
member key inlined this; the mixed spine needs it as a rewrite so the
two halves can be split with `List.map_append`. -/
theorem interp_mkAppN_map (σ : Nat → V) (K : AnnotTerm) :
    ∀ as : List AnnotTerm,
      interp V σ (AnnotTerm.mkAppN K as)
        = (as.map (interp V σ)).foldl SetTheory.app (interp V σ K) := by
  intro as
  rw [interp_mkAppN]
  generalize interp V σ K = b
  induction as generalizing b with
  | nil => rfl
  | cons a asr ih => simpa using ih (SetTheory.app b (interp V σ a))

/-! ## The key -/

/-- **The projection cons's live η law**: the family a projection
function completes carries `EtaLaw`.  `capsOk_cons_proj`'s
`hcomplete`.

The projection valuation identifications `hvP` are a **premise**, as
in v1 (`etaLawKeyS` takes `hvT`/`hvC`/`hvP` and calls all three
install-supplied).  Part 2 derived `hvT`/`hvC` from
`BlockAcvalInstalled`; there is no invariant to derive `hvP` from,
because the family's earlier projection slots were installed by
earlier `ProjInstallR` steps and that fold is where the
identification lives. -/
@[expose] def ProjEtaLaw (V : Type w) [SetTheory V] : Prop :=
  ∀ {μ : CheckMode} {blockNames : List Name} {env : Env}
    (mp : EnvModelM V μ env) {c₀ : ConstantInfo}
    {A : (Name → Nat) → AnnotTerm} {T : Name} {i : Nat},
    c₀.name = ConLeche.projFnName T i →
    (∃ cv mI rP rules, c₀ = .recInfo cv mI rP rules) →
    env.find? c₀.name = none →
    BlockInstalledTT blockNames env mp.base2.cvalE →
    BlockAcvalInstalled blockNames env mp.base2.acval →
    ∀ (cvT : ConstantVal) (caps : IndCaps),
      (⟨c₀ :: env.consts⟩ : Env).find? T = some (.indInfo cvT caps) →
      caps.eta = true →
      ConLeche.reservedBasisNames.contains T = false →
      ConLeche.EtaPins μ env T cvT.levelParams caps →
      blockNames.contains T = true →
      blockNames.contains caps.etaCtor = true →
      ConLeche.EtaFamilyStored ⟨c₀ :: env.consts⟩ T caps →
      ∀ m₂ : EnvModel V ⟨c₀ :: env.consts⟩,
        m₂.acval = acvalWith mp.base2.acval c₀.name A →
        -- v1's `hvP`, install-supplied
        (∀ j, j < caps.etaFields → ∀ ψ : Name → Nat,
          m₂.acval (ConLeche.projFnName T j) ψ
            = mp.base2.acval (ConLeche.projModelName T j) ψ) →
        ∀ φ' : Name → Nat, EtaLaw m₂ φ' T cvT caps

set_option maxHeartbeats 3200000 in
theorem projEtaLaw : ProjEtaLaw V := by
  intro μ blockNames env mp c₀ A T i hc₀name hc₀rec hfresh0 hIB hIA
    cvT caps hfT hcape hnresT hp hbT hbC hfam m₂ hac hvP φ'
  -- the cons is a `recInfo`: neither the former nor the constructor
  obtain ⟨cvr, mIr, rPr, rulesr, hc₀eq⟩ := hc₀rec
  have hT0 : T ≠ c₀.name := by
    intro hh
    rw [hh, ConLeche.Env.find?_cons_self, hc₀eq] at hfT
    exact nomatch hfT
  have hfE : env.find? T = some (.indInfo cvT caps) := by
    rw [ConLeche.Env.find?_cons, if_neg (fun hh => hT0 hh.symm)] at hfT
    exact hfT
  have hC0 : caps.etaCtor ≠ c₀.name := by
    intro hh
    obtain ⟨-, ⟨cvC, _, _, hfC⟩, -⟩ := hfam
    rw [hh, ConLeche.Env.find?_cons_self, hc₀eq] at hfC
    exact nomatch hfC
  obtain ⟨-, ⟨cvCst, cnPst, cnFst, hfCst⟩, -⟩ := id hfam
  have hfCe : env.find? caps.etaCtor
      = some (.ctorInfo cvCst cnPst cnFst) := by
    rw [ConLeche.Env.find?_cons, if_neg (fun hh => hC0 hh.symm)] at hfCst
    exact hfCst
  -- the kernel's η-capability pins
  obtain ⟨tcv, tval, cvmT, mvalT, hmT, sbinders, tbindersM, sbody,
    tbodyM, tySlot, ℓA, hthmE, htlps, hTmE, hTmlps, hCmE, hprojE,
    heqfE, hSstrip, hTstrip, hsdoms, hxdom, hsbody, htySlot, -⟩ :=
    hp.1 hcape
  obtain ⟨cvmC, mvalC, hmC, hCmE', hCmlps⟩ := hCmE
  -- ===== the two valuation identifications (v1's `hvT`/`hvC`) =====
  -- one `acvalWith_ne` each: no case split, because a `recInfo` cons
  -- is neither the former nor the capability constructor
  have hvT : ∀ ψ : Name → Nat,
      m₂.acval T ψ = mp.base2.acval (T.str "_model") ψ := fun ψ => by
    rw [hac, acvalWith_ne hT0]
    exact (hIA T hbT _ hfE ψ).symm
  have hvC : ∀ ψ : Name → Nat,
      m₂.acval caps.etaCtor ψ
        = mp.base2.acval (caps.etaCtor.str "_model") ψ := fun ψ => by
    rw [hac, acvalWith_ne hC0]
    exact (hIA caps.etaCtor hbC _ hfCe ψ).symm
  -- ===== the former's type reads as its model's =====
  have hEqTy : ∀ ψ : Name → Nat,
      denoteMeta mp.base2.acval env ψ 0 cvT.type
        = denoteMeta mp.base2.acval env ψ 0 cvmT.type := by
    intro ψ
    obtain ⟨cvm, mval, hm, hfm, hlps, hren, hval⟩ := hIB T hbT _ hfE
    obtain rfl : cvm = cvmT := by
      have h := hTmE; rw [hfm] at h
      exact (ConLeche.ConstantInfo.defnInfo.inj (Option.some.inj h)).1
    obtain ⟨-, -, hty, -⟩ :=
      mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfE)
    exact blockTypeReadEq mp hIB hIA hty hren ψ
  have hcbT : ConstsBound env cvT.type := by
    obtain ⟨-, -, hty, -⟩ :=
      mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfE)
    exact constsBound_of_constsResolve _ hty
  intro us hus
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Name → Nat,
      ψ = Level.substFn φ' cvT.levelParams us := ⟨_, rfl⟩
  obtain ⟨ta, htaM, hokta, -⟩ := mp.acval_memType hTmE ψ
  have htaM' : denoteMeta mp.base2.acval env ψ 0 cvmT.type = some ta := htaM
  have hta : denoteMeta mp.base2.acval env ψ 0 cvT.type = some ta := by
    rw [hEqTy]; exact htaM'
  refine ⟨ta, ?_, hokta, ?_⟩
  · rw [denotePInstLevels m₂ φ' cvT.levelParams us 0 cvT.type, ← hψ, hac]
    exact denoteMeta_cons_fresh_mono hfresh0
      (fun _ h => by rw [hc₀eq] at h; exact nomatch h)
      ψ 0 cvT.type hcbT hta
  intro ρ ts rest x hlents hfit hmx
  rw [← hψ, hvT] at hmx
  rw [← hψ, hvC]
  -- the fabricated spine, with `hvP` moving every projection leaf to
  -- its model
  rw [show etaFabArgsV (fun n => interp V ρ (m₂.acval n ψ)) T ts x
        caps.etaFields
      = ts ++ (List.range caps.etaFields).map (fun j =>
          (ts ++ [x]).foldl SetTheory.app
            (interp V ρ (mp.base2.acval (ConLeche.projModelName T j) ψ)))
      from by
    unfold etaFabArgsV projSpines
    refine congrArg _ (List.map_congr_left fun j hj => ?_)
    dsimp only
    rw [hvP j (List.mem_range.mp hj) ψ]]
  -- ===== the two telescopes =====
  obtain ⟨Γm, Cm, hteleM, hΓmlen, hbodyM, hdomsM⟩ :=
    stripPis_denotePTele caps.etaParams hTstrip htaM'
  obtain ⟨ua, hua, hokua, hmemua⟩ := mp.acval_memType hthmE ψ
  have hua' : denoteMeta mp.base2.acval env ψ 0 tcv.type = some ua := hua
  obtain ⟨Γs, Cs, hteleS, hΓslen, hbodyS, hdomsS⟩ :=
    stripPis_denotePTele (caps.etaParams + 1) hSstrip hua'
  obtain ⟨Γ₁, Γ₂, M, hΓsplit, hΓ₂len, hΓ₁len, hteleS2, hteleS1⟩ :=
    PiTeleAV.split caps.etaParams 1 hteleS
  obtain ⟨ux, vx, Ax, Bx, Γ₁', rfl, hΓ₁eq, hS0⟩ := hteleS1.succ_inv
  cases hS0
  have hsblen : sbinders.length = caps.etaParams + 1 :=
    ConLeche.Expr.stripPis_length _ hSstrip
  have htblen : tbindersM.length = caps.etaParams :=
    ConLeche.Expr.stripPis_length _ hTstrip
  have hΓ₁ : Γ₁ = [Ax] := by rw [hΓ₁eq]; rfl
  -- ===== the parameter domains agree =====
  have hdomEq : ∀ i0, i0 < ts.length →
      Γm.getD i0 default = Γ₂.getD i0 default := by
    intro i0 hi0'
    rw [hlents] at hi0'
    have hi0 : caps.etaParams - 1 - i0 < caps.etaParams := by omega
    have hb : sbinders[caps.etaParams - 1 - i0]?
        = some (sbinders[caps.etaParams - 1 - i0]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    have hb' : tbindersM[caps.etaParams - 1 - i0]?
        = some (tbindersM[caps.etaParams - 1 - i0]'(by omega)) :=
      List.getElem?_eq_getElem (by omega)
    have hEq := hsdoms (caps.etaParams - 1 - i0) _ _ hi0 hb hb'
    have h1 := hdomsS (caps.etaParams - 1 - i0) _ hb
    have h2 := hdomsM (caps.etaParams - 1 - i0) _ hb'
    rw [hEq, h2] at h1
    rw [show caps.etaParams - 1 - (caps.etaParams - 1 - i0) = i0 from by
      omega] at h1
    rw [hΓsplit, List.getD, List.getD,
      List.getElem?_append_right (by rw [hΓ₁len]; omega), hΓ₁len,
      show caps.etaParams + 1 - 1 - (caps.etaParams - 1 - i0) - 1 = i0
        from by omega] at h1
    exact Option.some.inj h1
  -- ===== the opened slot, read and evaluated =====
  have hKle : ∀ (K : Name) (ci : ConstantInfo),
      env.find? K = some ci →
      ci.toConstantVal.levelParams = cvT.levelParams →
      ∀ d : Nat, caps.etaParams ≤ d →
      denoteMeta mp.base2.acval env ψ d
        (Expr.mkAppN (.const K (cvT.levelParams.map .param))
          (openFvars 0 caps.etaParams))
      = some (AnnotTerm.mkAppN (mp.base2.acval K ψ)
          ((List.range caps.etaParams).map fun q =>
            AnnotTerm.bvar (d - 1 - (0 + q)))) :=
    fun K ci hf hlps d hd => denoteMeta_openSpine hf hlps _ d hd
  have hspineVal : ∀ (K : Name) (d : Nat) (σ : Nat → V),
      (∀ q, q < ts.length →
        σ (d - 1 - (0 + q)) = consN ts ρ (ts.length - 1 - q)) →
      interp V σ (AnnotTerm.mkAppN (mp.base2.acval K ψ)
          ((List.range caps.etaParams).map fun q =>
            AnnotTerm.bvar (d - 1 - (0 + q))))
        = ts.foldl SetTheory.app (interp V ρ (mp.base2.acval K ψ)) := by
    intro K d σ hσ
    rw [← hlents]
    exact interp_bvarSpine (V := V) ts (ρ := ρ) (σ := σ)
      (K := mp.base2.acval K ψ) (fun q => d - 1 - (0 + q)) hσ
      (acval_interp_closedC mp.base2 _ ψ σ ρ)
  -- the major's slot
  obtain ⟨mx, hxb⟩ := hxdom
  have hAx : Ax = AnnotTerm.mkAppN (mp.base2.acval (T.str "_model") ψ)
      ((List.range caps.etaParams).map fun q =>
        AnnotTerm.bvar (caps.etaParams - 1 - (0 + q))) := by
    have h := hdomsS caps.etaParams _ hxb
    rw [instSeq_openSpine _ _ caps.etaParams caps.etaParams
        (caps.etaParams - 1) (Nat.le_refl _) (by omega),
      Nat.zero_add,
      hKle _ _ hTmE hTmlps caps.etaParams (Nat.le_refl _)] at h
    rw [hΓsplit, hΓ₁, List.getD,
      List.getElem?_append_left (by simp),
      show caps.etaParams + 1 - 1 - caps.etaParams = 0 from by omega]
      at h
    exact (Option.some.inj h).symm
  have hx' : x ∈ˢ interp V (consN ts ρ) Ax := by
    rw [hAx, hspineVal _ caps.etaParams (consN ts ρ)
      (fun q hq => congrArg (consN ts ρ) (by omega))]
    exact hmx
  -- ===== the fit, moved and continued =====
  have hteleM' : PiTeleAV ts.length ta Γm Cm := by rw [hlents]; exact hteleM
  have hteleS2' : PiTeleAV ts.length ua Γ₂ (.pi ux vx Ax Cs) := by
    rw [hlents]; exact hteleS2
  have hfitFull : TeleFit V ρ ua (ts ++ [x])
      (interp V (cons x (consN ts ρ)) Cs) :=
    teleFit_congr_ext ts hteleM' hteleS2' hdomEq hfit
      (TeleFit.cons hx' TeleFit.nil)
  have hteleFull : PiTeleAV (ts ++ [x]).length ua Γs Cs := by
    rw [List.length_append, hlents]; exact hteleS
  have hconsApp : consN (ts ++ [x]) ρ = cons x (consN ts ρ) := by
    rw [consN_append]; rfl
  -- ===== the opened body is the pinned `Eq` spine, projections and all
  have hprojRead : ∀ j ∈ List.range caps.etaFields,
      denoteMeta mp.base2.acval env ψ (caps.etaParams + 1)
        ((fun j => Expr.mkAppN
          (.const (ConLeche.projModelName T j)
            (cvT.levelParams.map .param))
          (openFvars 0 (caps.etaParams + 1))) j)
        = some ((fun j => AnnotTerm.mkAppN
            (mp.base2.acval (ConLeche.projModelName T j) ψ)
            ((List.range (caps.etaParams + 1)).map fun q =>
              AnnotTerm.bvar (caps.etaParams + 1 - 1 - (0 + q)))) j) := by
    intro j hj
    obtain ⟨cvmj, mvalj, hmj, hfj, hlpj⟩ :=
      hprojE j (List.mem_range.mp hj)
    exact denoteMeta_openSpine hfj hlpj (caps.etaParams + 1)
      (caps.etaParams + 1) (Nat.le_refl _)
  have hctorHead : denoteMeta mp.base2.acval env ψ (caps.etaParams + 1)
      (.const (caps.etaCtor.str "_model") (cvT.levelParams.map .param))
      = some (mp.base2.acval (caps.etaCtor.str "_model") ψ) := by
    rw [denoteMeta_const hCmE'
      (by show (cvT.levelParams.map Level.param).length
              = cvmC.levelParams.length
          rw [hCmlps, List.length_map])]
    show some (mp.base2.acval (caps.etaCtor.str "_model")
        (Level.substFn ψ cvmC.levelParams
          (cvT.levelParams.map .param))) = _
    rw [hCmlps, show Level.substFn ψ cvT.levelParams
        (cvT.levelParams.map .param) = ψ from
      funext fun _ => Level.substFn_map_param]
  have hprojList : ((List.range caps.etaFields).map (fun j =>
        Expr.mkAppN (.const (ConLeche.projModelName T j)
          (cvT.levelParams.map .param))
        (((List.range caps.etaParams).map fun k =>
            Expr.bvar (caps.etaParams - k)) ++ [Expr.bvar 0]))).map
        (fun y => Expr.instSeq (openFvars 0 (caps.etaParams + 1))
          caps.etaParams y)
      = (List.range caps.etaFields).map (fun j =>
          Expr.mkAppN (.const (ConLeche.projModelName T j)
            (cvT.levelParams.map .param))
            (openFvars 0 (caps.etaParams + 1))) := by
    rw [List.map_map]
    refine List.map_congr_left fun j _ => ?_
    show Expr.instSeq (openFvars 0 (caps.etaParams + 1)) caps.etaParams
        (Expr.mkAppN (.const (ConLeche.projModelName T j)
            (cvT.levelParams.map .param))
          (((List.range caps.etaParams).map fun k =>
              Expr.bvar (caps.etaParams - k)) ++ [Expr.bvar 0])) = _
    rw [projArgSpine_eq,
      instSeq_openSpine _ _ (caps.etaParams + 1) (caps.etaParams + 1)
        caps.etaParams (Nat.le_refl _) (by omega)]
  have hCs : Cs = .app (.app (.app
      (mp.base2.acval eqName
        (Level.substFn ψ eqA.toConstantVal.levelParams [ℓA]))
      (AnnotTerm.mkAppN (mp.base2.acval (T.str "_model") ψ)
        ((List.range caps.etaParams).map fun q =>
          AnnotTerm.bvar (caps.etaParams + 1 - 1 - (0 + q)))))
      (.bvar 0))
      (AnnotTerm.mkAppN (mp.base2.acval (caps.etaCtor.str "_model") ψ)
        (((List.range caps.etaParams).map fun q =>
            AnnotTerm.bvar (caps.etaParams + 1 - 1 - (0 + q)))
          ++ (List.range caps.etaFields).map fun j =>
              AnnotTerm.mkAppN
                (mp.base2.acval (ConLeche.projModelName T j) ψ)
                ((List.range (caps.etaParams + 1)).map fun q =>
                  AnnotTerm.bvar (caps.etaParams + 1 - 1 - (0 + q))))) := by
    have h := hbodyS
    rw [show caps.etaParams + 1 - 1 = caps.etaParams from by omega,
      hsbody, Expr.instSeq_mkAppN, Expr.instSeq_eq_self _ _ rfl,
      Nat.zero_add] at h
    simp only [List.map_cons, List.map_nil] at h
    rw [htySlot, instSeq_openSpine _ _ caps.etaParams
        (caps.etaParams + 1) caps.etaParams (by omega) (by omega)] at h
    -- the third argument: distribute over its own spine, then open
    -- the two halves separately
    rw [Expr.instSeq_mkAppN,
      Expr.instSeq_eq_self _ _
        (e := .const (caps.etaCtor.str "_model")
          (cvT.levelParams.map .param)) rfl,
      List.map_append,
      instSeq_openSpine_list caps.etaParams (caps.etaParams + 1)
        caps.etaParams (by omega) (by omega),
      hprojList] at h
    have hb0 : Expr.instSeq (openFvars 0 (caps.etaParams + 1))
        caps.etaParams (Expr.bvar 0)
        = Expr.fvar caps.etaParams (.sort .zero) := by
      have hhit := Expr.instSeq_bvar (openFvars 0 (caps.etaParams + 1))
        caps.etaParams 0 (openFvars_bounded 0 (caps.etaParams + 1))
        (by omega) (by rw [openFvars_length]; omega)
      rw [openFvars_getElem? (d := 0) (k := caps.etaParams + 1)
          (i := caps.etaParams - 0) (by omega),
        show (0 : Nat) + (caps.etaParams - 0) = caps.etaParams from by
          omega] at hhit
      exact (Option.some.inj hhit).symm
    rw [hb0] at h
    rw [denoteMeta_mkAppN
      (DenoteMetaSpine.cons
        (hKle _ _ hTmE hTmlps (caps.etaParams + 1) (by omega))
        (DenoteMetaSpine.cons
          (denoteMeta_fvar mp.base2.acval (caps.etaParams + 1)
            caps.etaParams (.sort .zero))
          (DenoteMetaSpine.cons
            (denoteMeta_mkAppN
              (DenoteMetaSpine.append
                (denoteMetaSpine_openFvars caps.etaParams 0
                  (caps.etaParams + 1) (by omega))
                (DenoteMetaSpine.map_list (List.range caps.etaFields)
                  hprojRead))
              hctorHead)
            DenoteMetaSpine.nil)))
      (denoteMeta_const heqfE rfl)] at h
    rw [show caps.etaParams + 1 - 1 - caps.etaParams = 0 from by omega]
      at h
    exact (Option.some.inj h).symm
  -- ===== fire =====
  have hokCs : WellDenotedV V (cons x (consN ts ρ)) Cs := by
    have h := teleFit_wellDenotedV_residual (ts ++ [x]) hteleFull (hokua ρ)
      hfitFull
    rwa [hconsApp] at h
  have hSval : ∀ K : Name, interp V (cons x (consN ts ρ))
      (AnnotTerm.mkAppN (mp.base2.acval K ψ)
        ((List.range caps.etaParams).map fun q =>
          AnnotTerm.bvar (caps.etaParams + 1 - 1 - (0 + q))))
      = ts.foldl SetTheory.app (interp V ρ (mp.base2.acval K ψ)) :=
    fun K => hspineVal K (caps.etaParams + 1) (cons x (consN ts ρ))
      (fun q hq => by
        rw [show caps.etaParams + 1 - 1 - (0 + q)
          = (ts.length - 1 - q) + 1 from by omega]
        rfl)
  -- the projection arguments, evaluated: the side condition is
  -- reflexivity, because `consN (ts ++ [x]) ρ` IS the environment
  have hPval : ∀ K : Name, interp V (cons x (consN ts ρ))
      (AnnotTerm.mkAppN (mp.base2.acval K ψ)
        ((List.range (caps.etaParams + 1)).map fun q =>
          AnnotTerm.bvar (caps.etaParams + 1 - 1 - (0 + q))))
      = (ts ++ [x]).foldl SetTheory.app
          (interp V ρ (mp.base2.acval K ψ)) := by
    intro K
    have hlen1 : (ts ++ [x]).length = caps.etaParams + 1 := by
      rw [List.length_append, hlents]; rfl
    have h := interp_bvarSpine (V := V) (ts ++ [x]) (ρ := ρ)
      (σ := cons x (consN ts ρ)) (K := mp.base2.acval K ψ)
      (fun q => caps.etaParams + 1 - 1 - (0 + q))
      (fun q hq => by
        rw [← hconsApp, hlen1]
        congr 1
        omega)
      (acval_interp_closedC mp.base2 _ ψ _ ρ)
    rwa [hlen1] at h
  have hSuniv := eqSlot_univ mp heqfE _ (hCs ▸ hokCs)
  rw [hSval] at hSuniv
  have hxS : x ∈ˢ ts.foldl SetTheory.app
      (interp V ρ (mp.base2.acval (T.str "_model") ψ)) := hmx
  have hRS := eqThird_mem mp heqfE _ (hCs ▸ hokCs)
    (by rw [hSval]; exact hSuniv)
    (by rw [hSval]; exact hxS)
  rw [hSval] at hRS
  rw [interp_mkAppN_map, List.map_append, List.map_map, List.map_map]
    at hRS
  have hmapS : ((List.range caps.etaParams).map fun q =>
        AnnotTerm.bvar (caps.etaParams + 1 - 1 - (0 + q))).map
        (interp V (cons x (consN ts ρ))) = ts := by
    refine List.ext_getElem (by simp [hlents]) fun q h1 h2 => ?_
    have hq : q < caps.etaParams := by simpa using h1
    rw [List.getElem_map, List.getElem_map, List.getElem_range,
      interp_bvar,
      show caps.etaParams + 1 - 1 - (0 + q) = (ts.length - 1 - q) + 1
        from by omega]
    show consN ts ρ (ts.length - 1 - q) = _
    have := consN_getElem? ts ρ (ts.length - 1 - q) (by omega)
    rw [show ts.length - 1 - (ts.length - 1 - q) = q from by omega,
      List.getElem?_eq_getElem (by omega)] at this
    exact (Option.some.inj this).symm
  have hmapP : ((List.range caps.etaFields).map fun j =>
        AnnotTerm.mkAppN (mp.base2.acval (ConLeche.projModelName T j) ψ)
          ((List.range (caps.etaParams + 1)).map fun q =>
            AnnotTerm.bvar (caps.etaParams + 1 - 1 - (0 + q)))).map
        (interp V (cons x (consN ts ρ)))
      = (List.range caps.etaFields).map fun j =>
          (ts ++ [x]).foldl SetTheory.app
            (interp V ρ (mp.base2.acval (ConLeche.projModelName T j) ψ)) := by
    rw [List.map_map]
    exact List.map_congr_left fun j _ => hPval _
  rw [List.map_map] at hmapS hmapP
  rw [hmapS, hmapP,
    acval_interp_closedC mp.base2 (caps.etaCtor.str "_model") ψ
      (cons x (consN ts ρ)) ρ] at hRS
  have hlanded := memFoldl_of_teleFit (ts ++ [x]) (hokua ρ)
    (hmemua ρ) hfitFull
  rw [hCs] at hlanded
  have hc0 : (cons x (consN ts ρ)) 0 = x := rfl
  simp only [interp_app, interp_bvar, hSval, hc0] at hlanded
  rw [interp_mkAppN_map, List.map_append, List.map_map, List.map_map]
    at hlanded
  rw [hmapS, hmapP,
    acval_interp_closedC mp.base2 (caps.etaCtor.str "_model") ψ
      (cons x (consN ts ρ)) ρ] at hlanded
  rw [(mp.eq_law heqfE _).1 (cons x (consN ts ρ)) _ x _
    hSuniv hxS hRS] at hlanded
  exact eq_of_mem_eqv hlanded

/-! ## The row, closed

`capsOk_cons_proj` and `projEtaLaw` compose with **no residue**: the
projection cons's `caps_ok` obligation is discharged outright from the
install-supplied bundle, exactly as `memberInstallPM`'s two rows were
once part 2 proved the member keys.  The bundle is quantified over the
family's own data because `hvP` mentions `caps.etaFields`, which is not
in scope until the family is found. -/
theorem capsOk_cons_proj_of (mp : EnvModelM V μ env)
    (hprev : CapsOk mp.base2)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm} {T₀ : Name} {i : Nat}
    {blockNames : List Name}
    (hfresh : env.find? c₀.name = none)
    (hc₀name : c₀.name = ConLeche.projFnName T₀ i)
    (hc₀rec : ∃ cv mI rP rules, c₀ = .recInfo cv mI rP rules)
    (hIB : BlockInstalledTT blockNames env mp.base2.cvalE)
    (hIA : BlockAcvalInstalled blockNames env mp.base2.acval)
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith mp.base2.acval c₀.name A)
    -- the install-supplied bundle at the completed family
    (hinst : ∀ (cvT : ConstantVal) (caps : IndCaps),
      (⟨c₀ :: env.consts⟩ : Env).find? T₀ = some (.indInfo cvT caps) →
      caps.eta = true →
      ConLeche.EtaPins μ env T₀ cvT.levelParams caps ∧
        blockNames.contains T₀ = true ∧
        blockNames.contains caps.etaCtor = true ∧
        ∀ j, j < caps.etaFields → ∀ ψ : Name → Nat,
          m₂.acval (ConLeche.projFnName T₀ j) ψ
            = mp.base2.acval (ConLeche.projModelName T₀ j) ψ) :
    CapsOk m₂ :=
  capsOk_cons_proj mp hprev hfresh hc₀name hc₀rec m₂ hac
    (fun cvT caps hf hcape _ hres hfamS φ' =>
      match hinst cvT caps hf hcape with
      | ⟨hp, hbT, hbC, hvP⟩ =>
        projEtaLaw mp hc₀name hc₀rec hfresh hIB hIA cvT caps hf hcape
          hres hp hbT hbC hfamS m₂ hac hvP φ')

end ConLeche.Model
