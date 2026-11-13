import IxCCGrounding.CaseFire
import IxCCGrounding.CaseCheck
import IxCCGrounding.Direct.Eq

/-!
# The generic `case` lemma without canonicity (`IxCCGrounding.CaseBlind`)

F5's meaning (`CaseFires`) at a `case` entry whose recursor's stored rules do not compare
parameters (`CaseRulesBlind`, decided) and whose constructors have no level parameters
(`sh.indLevels = []`), from **δ (`DefnValue`), ι in #678's guarded form (`IotaLawG`) and
level-parameter irrelevance (`CvalParams`) alone**: no `Laws.ctor_canon`, which #678's model does
not provide. The landed lemma (`caseFires_of_shape`, over `Laws` whole, canonicity included) is
unchanged and covers every other checked shape.

**Why canonicity was needed, and what replaces it.** A constructor value related by provenance
(`RelV.con`) is the constructor's image at the assignment and the parameters it was built at, its
fields fitting the constructor's type there. `caseIota` reads the image at the `case`'s own
parameters (ι's parameter premise) and the fields in the field domains at the `case`'s parameters
(β through the rule's field λs and through `casesOn`'s wrapper, the induction hypotheses, and the
graph-regime chain of the minor premise at the fields); canonicity moved both. Here:

* **Parameters**: at a rule that does not compare parameters the guarded law fires at the
  constructor's own parameters (`caseIotaG`), and its `SpineOk` conclusion (the right-hand side's
  value applies along the prefix and the fields on its domains) puts each field in its λ's domain:
  the rule's field λs are in the graph regime (their binder datum is the last binder's,
  `CaseWF.regime`, nonzero since the last site was in the graph regime), a graph regime λ's value
  is a graph, never the proof point (`lamR_ne_pt`), so the product it is a member of is in the graph
  regime too and has its domain (`lamR_dom_of_mem`, from the set theory's own definitions:
  `mem_piSet`, `mem_graph`, `mem_sigmaPairs`, `kpair_inj`, extensionality). The domains, read under
  the `case`'s parameters alone (`fieldsCorr_rev`), are the constructor's field telescope there,
  which is what `caseIota`'s remaining steps read.
* **Levels**: a constructor without level parameters has one image at every assignment
  (`CvalParams`) and its closed, level-free type moves its fit from the assignment and environment
  it was built at to the `case`'s (`fits_agree`, `fits_inst_cv`).
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open IxCC.Src (Value Slot Term CId Program Levels)

universe w

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv}

/-! ## A graph that is a member of a product -/

/-- **A graph-regime abstraction that is a member of a product has the product's domain**: the
product is in the graph regime (a member of a regime-`0` product is the proof point, which a
graph-regime abstraction never is), and a function graph in `piSet A' B` is total on `A'` and has
its pairs over `A'`, while the graph of `F` over `A` has exactly the pairs over `A`. From the set
theory's definitions only; no law. -/
theorem lamR_dom_of_mem {v r : Nat} {A A' : V} {F B : V → V} (hv : v ≠ 0)
    (h : lamR v A F ∈ˢ piR r A' B) : A' = A := by
  have hr : r ≠ 0 := by
    rintro rfl
    exact lamR_ne_pt hv (eq_pt_of_mem_piR_zero h)
  rw [lamR_pos hv, piR_pos hr] at h
  obtain ⟨hsub, htot⟩ := mem_piSet.mp h
  refine Ix.Kernel.SetTheory.ext fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨y, hy, -⟩ := htot x hx
    obtain ⟨x2, hx2, hp⟩ := mem_graph.mp hy
    obtain ⟨rfl, -⟩ := kpair_inj hp
    exact hx2
  · have hp : kpair x (F x) ∈ˢ graph F A := mem_graph.mpr ⟨x, hx, rfl⟩
    obtain ⟨x2, hx2, y2, -, hp2⟩ := mem_sigmaPairs.mp (hsub _ hp)
    obtain ⟨rfl, -⟩ := kpair_inj hp2
    exact hx2

/-- `SpineOk` along an appended list continues from the applied prefix. -/
theorem spineOk_append : ∀ {F : V} {xs ys : List V}, SpineOk F (xs ++ ys) →
    SpineOk (xs.foldl app F) ys
  | _, [], _, h => h
  | F, x :: xs, ys, h => by
    have h2 : SpineOk (app F x) (xs ++ ys) := h.2
    exact spineOk_append (F := app F x) (xs := xs) (ys := ys) h2

/-- **Values `SpineOk` along a graph-regime λ-telescope fit its domains**: each value lies in its
λ's domain (`lamR_dom_of_mem`), and β (`app_lamR_pos`) moves to the next λ. No law. -/
theorem fits_of_spineOk {cval : KKey → (LevelParam → Nat) → V} {φ : LevelParam → Nat} :
    ∀ (bs : List (KExpr × BinderMeta)) (b C : KExpr) {ρ : BVarIdx → V} {L : V} {xs : List V},
      Denotes cval env φ ρ (lamTele bs b) L → SpineOk L xs → xs.length = bs.length →
      (∀ bm ∈ bs, regime φ bm.2.pw ≠ 0) →
      Fits cval env φ ρ (piTele bs C) xs (pushAll xs ρ) C
  | [], _, C, ρ, _, [], _, _, _, _ => by rw [pushAll_nil]; exact .nil
  | [], _, _, _, _, _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, _, _, _, _, [], _, _, hl, _ => by simp at hl
  | (A, m) :: bs, b, C, ρ, L, x :: xs, hL, hsp, hl, hreg => by
    have hL' : Denotes cval env φ ρ (.lam A (lamTele bs b) m) L := hL
    obtain ⟨Ad, F, hAd, hF, -, rfl⟩ := den_lam.mp hL'
    have hv : regime φ m.pw ≠ 0 := hreg (A, m) (List.mem_cons_self ..)
    obtain ⟨⟨r', A', B', hmem, hx⟩, hrest⟩ : (∃ (r : Nat) (A : V) (B : V → V),
        lamR (regime φ m.pw) Ad F ∈ˢ piR r A B ∧ x ∈ˢ A) ∧
        SpineOk (app (lamR (regime φ m.pw) Ad F) x) xs := hsp
    have hxA : x ∈ˢ Ad := by rw [← lamR_dom_of_mem hv hmem]; exact hx
    rw [app_lamR_pos hv hxA] at hrest
    have ih := fits_of_spineOk bs b C (hF x hxA) hrest (by simpa using hl)
      (fun bm hbm => hreg bm (List.mem_cons_of_mem _ hbm))
    rw [pushAll_cons]
    exact .cons hAd hxA ih

/-- **The fields fit the constructor's field telescope at the `case`'s parameters**, from
`SpineOk` along the rule's field λs (graph regime) and `fieldsCorr_rev`: the step of `caseIotaG`
that replaces canonicity at parameters. No law. -/
theorem fields_fit_of_spineOk {M : Model V env} {φ : LevelParam → Nat} {sh : CaseShape}
    {j : Nat} {cs : CtorShape} {fbs : List (KExpr × BinderMeta)} {ps Ws Fs : List V} {mo : V}
    {ρ : BVarIdx → V} {b D : KExpr} {Y1 : V}
    (hf : (liftTele (j + 1) 0 fbs).map (·.1) = cs.fields.map (·.1))
    (hY1 : Denotes M.cval env φ (pushAll (ps ++ [mo] ++ Ws) ρ)
      (lamTele (liftTele (sh.nM - j) j cs.fields) b) Y1)
    (hsp : SpineOk Y1 Fs) (hWl : Ws.length = sh.nM) (hj : j < sh.nM)
    (hreg : ∀ bm ∈ cs.fields, regime φ bm.2.pw ≠ 0) (hFl : Fs.length = cs.fields.length)
    (hfbl : fbs.length = Fs.length) :
    Fits M.cval env φ (pushAll ps ρ) (piTele fbs D) Fs (pushAll Fs (pushAll ps ρ)) D := by
  have hregR : ∀ bm ∈ liftTele (sh.nM - j) j cs.fields, regime φ bm.2.pw ≠ 0 := by
    intro bm hb
    have hb2 : bm.2 ∈ (liftTele (sh.nM - j) j cs.fields).map (·.2) := List.mem_map_of_mem hb
    rw [liftTele_metas] at hb2
    obtain ⟨b', hb', e⟩ := List.mem_map.mp hb2
    rw [← e]
    exact hreg b' hb'
  have hFR0 := fits_of_spineOk (cval := M.cval) (env := env) (φ := φ)
    (liftTele (sh.nM - j) j cs.fields) _ D hY1 hsp (by rw [liftTele_length]; omega) hregR
  have hcRr : TeleCorr M.cval env φ (pushAll ps ρ) (pushAll (ps ++ [mo] ++ Ws) ρ) fbs
      (liftTele (sh.nM - j) j cs.fields) := by
    have := fieldsCorr_rev (M := M) (φ := φ) (ps := ps) (ρ := ρ) (fbs := fbs) (cs := cs) (j := j)
      (k' := sh.nM - j) (junk := [mo] ++ Ws) hf (by simp; omega)
    rwa [← List.append_assoc] at this
  have hFCf := fits_transport fbs (liftTele (sh.nM - j) j cs.fields) D _
    (by rw [liftTele_length]; omega) hcRr hFR0 (by rw [liftTele_length]; omega)
  rwa [List.drop_eq_nil_of_le (show fbs.length ≤ Fs.length by omega)] at hFCf

/-! ## The model side -/

-- Over the default budget (200000), within 400000. `caseIota`, whose proof this copies, elaborates
-- within 150000 (measured), and the `SpineOk` step is a lemma of its own
-- (`fields_fit_of_spineOk`); the excess is in the steps added here around the guarded ι law
-- (its application at the constructor's own parameters, the rule's blindness, the moved regime
-- step), not localized further.
set_option maxHeartbeats 400000 in
/-- **The generic `case` lemma, model side, without canonicity** (as `caseIota`, whose proof this
follows): at a checked shape whose recursor's rules do not compare parameters, `casesOn` applied to
arguments that fit its type, the last at a graph-regime site, with the major the image of
constructor `j` at the `case`'s levels applied to **its own** parameters `Ps` and to fields `Fs`
that fit its type there, is minor `j` applied to the fields, along a graph-regime chain. Laws:
`DefnValue` (δ on `casesOn`), `IotaLawG` (ι at rule `j`, guarded, with `SpineOk`), `CvalParams`
(the recursor's type read at the levels `casesOn` calls it at); `Model.mem`.
Over any sort clause (step Pc: it reads none). -/
theorem caseIotaGWith (M : Model V env) (hδ : DefnValue M) (hι : IotaLawG M.cval env)
    (hcv : CvalParams M) {kc kr : KKey} {sh : CaseShape} {Srt : KEnv → KKey → Prop}
    (hS : CaseStoredWith Srt env kc kr sh) (hB : CaseRulesBlind env kr) (cvc : ConstantVal .anon)
    (val : KExpr)
    (hint : ReducibilityHint) (hfc : env.find? kc = some (.defnInfo cvc val hint))
    (φ : LevelParam → Nat) (ρ σ : BVarIdx → V) (R : KExpr) (As : List V)
    (hfit : Fits M.cval env φ ρ cvc.type As σ R) (hlen : As.length = sh.nP + 2 + sh.nM)
    (hlast : LastSiteOk (M.cval kc φ) As)
    (j : Nat) (cs : CtorShape) (cvC : ConstantVal .anon) (K : V) (Ps Fs : List V)
    (σC : BVarIdx → V) (RC : KExpr) (hj : sh.ctors[j]? = some cs)
    (hcC : env.find? cs.key = some (.ctorInfo cvC sh.nP cs.nF))
    (hK : Denotes M.cval env φ ρ (.const cs.key sh.indLevels) K)
    (hFC : Fits M.cval env φ ρ (cvC.type.instantiateLevelParams cvC.levelParams sh.indLevels)
      (Ps ++ Fs) σC RC)
    (hPl : Ps.length = sh.nP) (hFl : Fs.length = cs.nF)
    (hmaj : As[sh.nP + 1]? = some ((Ps ++ Fs).foldl app K)) :
    ∃ Mn, As[sh.nP + 2 + j]? = some Mn ∧ As.foldl app (M.cval kc φ) = Fs.foldl app Mn ∧
      AppChain Mn Fs := by
  obtain ⟨⟨hblen, _⟩, ⟨cvc', hint', hfc', _, hty⟩, hminors, ⟨mmaj, hbmaj⟩,
    ⟨cvr, rules, hfr, hlr, htr, hrl, hrules⟩, hctors, hwf⟩ := hS
  have hfc2 := hfc.symm.trans hfc'
  simp only [Option.some.injEq, ConstantInfo.defnInfo.injEq] at hfc2
  obtain ⟨rfl, rfl, rfl⟩ := hfc2
  -- `casesOn`'s arguments and binders
  obtain ⟨ps, mo, t, mins, rfl, hps, hmins⟩ := split_ctx As sh.nP sh.nM hlen
  obtain ⟨bP, bMo, bMaj, bMin, hbs, hbP, hbMin⟩ := split_ctx sh.binders sh.nP sh.nM hblen
  have hjM : j < sh.ctors.length := (List.getElem?_eq_some_iff.mp hj).1
  have hnM : sh.nM = sh.ctors.length := rfl
  have hjm : j < mins.length := by omega
  rw [← hps] at hmaj
  rw [get_ctx1] at hmaj
  have ht : t = (Ps ++ Fs).foldl app K := Option.some.inj hmaj
  refine ⟨mins[j], by rw [← hps, get_ctx2, List.getElem?_eq_getElem hjm], ?_⟩
  have hbm : bMaj = (Expr.mkAppN (.const sh.ind sh.indLevels) (bvarsFrom 1 sh.nP), mmaj) := by
    have := get_ctx1 bP bMin bMo bMaj
    rw [hbP, ← hbs, hbmaj] at this
    exact (Option.some.inj this).symm
  have hbmin : ∀ j' cs', sh.ctors[j']? = some cs' →
      bMin[j']?.map (·.1) = some (CaseShape.casesMinor j' cs') := fun j' cs' h => by
    have := (hminors j' cs' h).1
    rwa [hbs, ← hbP, get_ctx2] at this
  obtain ⟨Alast, mLast, hgl, hreg⟩ := hwf.regime
  -- `casesOn`'s type, and its arguments' domains
  rw [hty] at hfit
  have hfit0 := hfit
  rw [hbs] at hfit
  obtain ⟨hfitP, ⟨XMo, hMoD, hmo⟩, ⟨Xmaj, hMajD, htm⟩, hrest⟩ := fits_ctx (by omega) hfit
  have hminD : ∀ j' (hj' : j' < mins.length), ∃ XM, Denotes M.cval env φ
      (pushAll (ps ++ mo :: t :: mins.take j') ρ) (bMin[j']'(by omega)).1 XM ∧ mins[j'] ∈ˢ XM := by
    intro j' hj'
    obtain ⟨X, hX, hm⟩ := fits_get bMin (.app (.bvar (sh.nM + 1)) (.bvar sh.nM)) hrest j' hj' (by omega)
    refine ⟨X, ?_, hm⟩
    rwa [← pushAll_append, show ps ++ [mo, t] ++ mins.take j' = ps ++ mo :: t :: mins.take j' by
      simp] at hX
  -- δ on `casesOn`, β through its λs
  have hval := hδ cvc (lamTele sh.binders (sh.body kr)) hint (find_mem hfc) φ ρ
  rw [show cvc.name = kc from find_name hfc] at hval
  obtain ⟨Y, hY, hYe⟩ := lamTele_app sh.binders (sh.body kr) (.app (.bvar (sh.nM + 1)) (.bvar sh.nM)) hval hfit0 (by simp; omega)
  rw [hYe]
  -- `casesOn`'s body: the recursor at the parameters, the motive, the wrappers and the major
  simp only [CaseShape.body] at hY
  obtain ⟨R0, Ys, hR0, hYs, rfl⟩ := (den_mkAppN _).mp hY
  obtain ⟨Y123, Y4, rfl, h123, h4⟩ := denotesList_append_inv hYs
  obtain ⟨Y12, Ws, rfl, h12, hWs⟩ := denotesList_append_inv h123
  obtain ⟨Y1, Y2, rfl, h1, h2⟩ := denotesList_append_inv h12
  have eY1 : Y1 = ps := by
    have := den_bvarsFrom (cval := M.cval) (env := env) (φ := φ) ρ (mo :: t :: mins) ps []
    rw [List.nil_append, show (mo :: t :: mins).length = sh.nM + 2 by simp; omega, hps] at this
    exact denotesList_functional h1 this
  have eY2 : Y2 = [mo] := by
    have := DenotesList.cons (cval := M.cval) (env := env) (φ := φ) (den_bvar_at (a := ps)
      (y := mo) (c := t :: mins) (ρ := ρ)) .nil
    rw [show (t :: mins).length = sh.nM + 1 by simp; omega] at this
    exact denotesList_functional h2 this
  have eY4 : Y4 = [t] := by
    have := DenotesList.cons (cval := M.cval) (env := env) (φ := φ) (den_bvar_at (a := ps ++ [mo])
      (y := t) (c := mins) (ρ := ρ)) .nil
    rw [hmins, show ps ++ [mo] ++ t :: mins = ps ++ mo :: t :: mins by simp] at this
    exact denotesList_functional h4 this
  subst Y1 Y2 Y4
  obtain ⟨hwl, hwg⟩ := filterMap_range sh.ctors (fun j cs => sh.wrapper j cs) sh.nM (Nat.le_refl _)
  have hWl : Ws.length = sh.nM := by rw [denotesList_length hWs, hwl]
  have hWd : ∀ j' cs' (hj' : j' < Ws.length), sh.ctors[j']? = some cs' →
      Denotes M.cval env φ (pushAll (ps ++ mo :: t :: mins) ρ) (sh.wrapper j' cs') Ws[j'] := by
    intro j' cs' hj' hc'
    have hget : ((List.range sh.nM).filterMap fun j => (sh.ctors[j]?).map (sh.wrapper j))[j']? =
        some (sh.wrapper j' cs') := by
      rw [hwg j' (by omega), hc']; rfl
    obtain ⟨v, hv, hd⟩ := denotesList_get hWs hget
    rw [List.getElem?_eq_getElem hj'] at hv
    rwa [Option.some.inj hv]
  -- the recursor
  have hR0ρ : Denotes M.cval env φ ρ (.const kr sh.recLevels) R0 := den_const_env hR0
  have hR0e : R0 = M.cval kr (Level.substFn φ cvr.levelParams sh.recLevels) := by
    cases hR0 with
    | const hf' _ =>
      rw [hfr] at hf'; cases hf'
      simp only [ConstantInfo.toConstantVal]
  -- the recursor lies in its stored type, read at the levels `casesOn`'s body calls it at
  have hTRm : ∀ ρ' : BVarIdx → V, ∃ TR, Denotes M.cval env φ ρ'
      (cvr.type.instantiateLevelParams cvr.levelParams sh.recLevels) TR ∧ R0 ∈ˢ TR := by
    intro ρ'
    obtain ⟨TR, hTR, hrm⟩ := mem_key M hfr (Level.substFn φ cvr.levelParams sh.recLevels) ρ'
    simp only [ConstantInfo.toConstantVal] at hTR
    exact ⟨TR, den_inst_exact_cv M hcv hTR, hR0e ▸ hrm⟩
  subst hbm
  have e1 : sh.binders.take (sh.nP + 1) = bP ++ [bMo] := by rw [hbs, ← hbP, take_ctx1]
  have e2 : sh.binders[sh.nP + 1]? = some (Expr.mkAppN (.const sh.ind sh.indLevels)
      (bvarsFrom 1 sh.nP), mmaj) := hbmaj
  have hrt : cvr.type.instantiateLevelParams cvr.levelParams sh.recLevels = piTele (bP ++ [bMo]) (piTele ((sh.ctors.map fun c => (c.recMinor, c.minorMeta))
      ++ [((Expr.mkAppN (.const sh.ind sh.indLevels) (bvarsFrom 1 sh.nP)).liftLooseBVars sh.nM 0,
        sh.majorMeta)]) (.app (.bvar (sh.nM + 1)) (.bvar 0))) := by
    rw [htr, ← piTele_append]
    simp only [CaseShape.recType, e1, e2, Option.toList_some, List.map_cons, List.map_nil,
      List.append_assoc]
  have hQ : ∀ j', j' ≤ sh.nM → Fits M.cval env φ ρ
      (cvr.type.instantiateLevelParams cvr.levelParams sh.recLevels) (ps ++ [mo] ++ Ws.take j')
      (pushAll (ps ++ [mo] ++ Ws.take j') ρ)
      (piTele ((sh.ctors.map fun c => (c.recMinor, c.minorMeta)).drop j' ++
        [((Expr.mkAppN (.const sh.ind sh.indLevels) (bvarsFrom 1 sh.nP)).liftLooseBVars sh.nM 0,
          sh.majorMeta)]) (.app (.bvar (sh.nM + 1)) (.bvar 0))) := by
    intro j' hj'
    induction j' with
    | zero =>
      rw [hrt, List.take_zero, List.append_nil, List.drop_zero, piTele_append, pushAll_snoc]
      exact fits_trans (hfitP _) (.cons hMoD hmo .nil)
    | succ j' ih =>
      have ih' := ih (by omega)
      have hj'c : j' < sh.ctors.length := by omega
      obtain ⟨cs', hc'⟩ : ∃ cs', sh.ctors[j']? = some cs' := ⟨_, List.getElem?_eq_getElem hj'c⟩
      have hcs' : sh.ctors[j'] = cs' := Option.some.inj ((List.getElem?_eq_getElem hj'c).symm.trans hc')
      have hdrop : (sh.ctors.map fun c => (c.recMinor, c.minorMeta)).drop j' =
          (cs'.recMinor, cs'.minorMeta) :: (sh.ctors.map fun c => (c.recMinor, c.minorMeta)).drop (j' + 1) := by
        rw [List.drop_eq_getElem_cons (by simp; omega)]
        simp [hcs']
      rw [hdrop] at ih'
      obtain ⟨TR, hTR, hrm⟩ := hTRm ρ
      obtain ⟨RR, hRR, _⟩ := fits_app_mem ih' hTR hrm
      obtain ⟨PP, _, hPP, _, _, _⟩ := den_pi.mp hRR
      obtain ⟨_, hih', hfl'⟩ := hminors j' cs' hc'
      obtain ⟨_, _, fbs', _, _, _, hf'⟩ := hctors j' cs' hc'
      have hWj' := hWd j' cs' (by omega) hc'
      rw [wrapper_eq _ _ _ hfl', ← hmins] at hWj'
      obtain ⟨XM, hXM, hmXM⟩ := hminD j' (by omega)
      have hbj : (bMin[j']'(by omega)).1 = CaseShape.casesMinor j' cs' := by
        have := hbmin j' cs' hc'
        rw [List.getElem?_eq_getElem (by omega)] at this
        exact Option.some.inj this
      rw [hbj] at hXM
      have hmem := wrapper_mem (M := M) (φ := φ) (ps := ps) (mo := mo) (t := t) (ρ := ρ)
        (Ws := Ws) hf' hfl' hih' (hwf.ihs j' cs' hc')
        (fun rf h => (hwf.recFields j' cs' hc' rf h).1) (hwf.codom j' cs' hc') (by omega)
        (by omega) hWj' hPP hXM hmXM
      have hsn := fits_snoc ih' rfl hPP hmem
      rw [← pushAll_snoc] at hsn
      rw [List.take_add_one, List.getElem?_eq_getElem (show j' < Ws.length by omega),
        Option.toList_some, ← List.append_assoc]
      exact hsn
  have hQM := hQ sh.nM (Nat.le_refl _)
  rw [List.take_of_length_le (show Ws.length ≤ sh.nM by omega),
    List.drop_eq_nil_of_le (show (sh.ctors.map fun c => (c.recMinor, c.minorMeta)).length ≤ sh.nM by
      simp [hnM]), List.nil_append] at hQM
  -- the major's domain, read in the recursor's type
  have hXmajR : Denotes M.cval env φ (pushAll (ps ++ [mo] ++ Ws) ρ)
      ((Expr.mkAppN (.const sh.ind sh.indLevels) (bvarsFrom 1 sh.nP)).liftLooseBVars sh.nM 0) Xmaj := by
    have := (den_lift_block (cval := M.cval) (env := env) (φ := φ) (a := ps ++ [mo]) (b := Ws)
      (c := []) (ρ := ρ)).mpr (by rwa [List.append_nil])
    rwa [List.append_nil, hWl] at this
  -- the constructor's type at the `case`'s levels
  obtain ⟨cvC', pbs, fbs, hcC', -, -, hf⟩ := hctors j cs hj
  rw [hcC] at hcC'
  cases hcC'
  obtain ⟨_, hih, hfl⟩ := hminors j cs hj
  have hfbl : fbs.length = Fs.length := by
    have := congrArg List.length hf; simp [liftTele_length] at this; omega
  have hFC0 := hFC
  -- ι
  obtain ⟨rl, hrl'⟩ : ∃ rl, rules[j]? = some rl :=
    ⟨_, List.getElem?_eq_getElem (by omega : j < rules.length)⟩
  obtain ⟨hrlc, hrlr⟩ := hrules j cs rl hj hrl'
  -- the rule does not compare parameters (`CaseRulesBlind`): the guarded law fires at the
  -- constructor's own parameters `Ps`, and the index premise is vacuous (`mI = rP`)
  have hblind : rl.compareParams = false := by
    obtain ⟨cvr', mI', rP', rules', hfr', hall⟩ := hB
    rw [hfr] at hfr'
    simp only [Option.some.injEq, ConstantInfo.recInfo.injEq] at hfr'
    obtain ⟨-, -, -, rfl⟩ := hfr'
    exact hall rl (List.mem_of_getElem? hrl')
  obtain ⟨H, hH, hsp, heq⟩ := hι kr cvr _ _ rules rl hfr (List.mem_of_getElem? hrl') cvC
    sh.nP cs.nF (by rw [hrlc]; exact hcC) sh.recLevels φ ρ (pushAll (ps ++ [mo] ++ Ws) ρ)
    σC (ps ++ [mo] ++ Ws) (Ps ++ Fs)
    ((Expr.mkAppN (.const sh.ind sh.indLevels) (bvarsFrom 1 sh.nP)).liftLooseBVars sh.nM 0)
    (.app (.bvar (sh.nM + 1)) (.bvar 0)) RC sh.majorMeta sh.ind sh.indLevels R0 K Xmaj
    hlr.symm (by simp; omega) (by simp; omega) hR0ρ
    hQM
    (by simp only [lift_mkAppN, getAppFn_mkAppN, Expr.liftLooseBVars, Expr.getAppFn])
    hXmajR (by rw [hrlc]; exact hK) hFC0 (by rw [← ht]; exact htm)
    (fun h => by rw [hblind] at h; cases h) (fun h => absurd rfl h)
  rw [hrlr] at hH
  -- β through the rule: the wrapper at the fields and the induction hypotheses
  have hH2 : Denotes M.cval env φ ρ (lamTele ((bP ++ [bMo]) ++ (sh.ctors.map fun c => (c.recMinor, c.minorMeta)))
      (lamTele (liftTele (sh.nM - j) j cs.fields)
        (Expr.mkAppN (.bvar (cs.nF + sh.nM - 1 - j)) (bvarsFrom 0 cs.nF ++ cs.recFields.map fun r =>
          Expr.mkAppN (.const kr sh.recLevels) (bvarsFrom (cs.nF + sh.nM + 1) sh.nP ++
            [.bvar (cs.nF + sh.nM)] ++ bvarsFrom cs.nF sh.nM ++ [.bvar (cs.nF - 1 - r)]))))) H := by
    rw [← lamTele_append, ← e1]; exact hH
  have hQM' : Fits M.cval env φ ρ (piTele ((bP ++ [bMo]) ++ (sh.ctors.map fun c => (c.recMinor, c.minorMeta)))
      (piTele [((Expr.mkAppN (.const sh.ind sh.indLevels) (bvarsFrom 1 sh.nP)).liftLooseBVars sh.nM 0,
        sh.majorMeta)] (.app (.bvar (sh.nM + 1)) (.bvar 0)))) (ps ++ [mo] ++ Ws)
      (pushAll (ps ++ [mo] ++ Ws) ρ)
      (piTele [((Expr.mkAppN (.const sh.ind sh.indLevels) (bvarsFrom 1 sh.nP)).liftLooseBVars sh.nM 0,
        sh.majorMeta)] (.app (.bvar (sh.nM + 1)) (.bvar 0))) := by
    rw [piTele_append, ← piTele_append (sh.ctors.map fun c => (c.recMinor, c.minorMeta)), ← hrt]
    exact hQM
  obtain ⟨Y1, hY1, eY1⟩ := lamTele_app _ _ _ hH2 hQM' (by simp; omega)
  -- the last binder is read in the graph regime
  have hlastReg : regime φ mLast.pw ≠ 0 := by
    have hne : (ps ++ mo :: t :: mins) ≠ [] := by simp
    have hsplit := (List.dropLast_concat_getLast hne).symm
    obtain ⟨v, A, B, hv, hX, _⟩ := hlast _ _ hsplit
    have hpre' := fits_prefix (bs := sh.binders) (xs := (ps ++ mo :: t :: mins).dropLast)
      (ys := [(ps ++ mo :: t :: mins).getLast hne]) (by rw [← hsplit]; exact hfit0) (by simp; omega)
    rw [show ((ps ++ mo :: t :: mins).dropLast).length = sh.binders.length - 1 by simp; omega,
      drop_pred_of_getLast? hgl] at hpre'
    obtain ⟨TT, hTT, hHm⟩ := mem_key M hfc φ ρ
    have hTT' : Denotes M.cval env φ ρ (piTele sh.binders (.app (.bvar (sh.nM + 1)) (.bvar sh.nM))) TT := by
      rw [← hty]; exact hTT
    exact last_regime hpre' hTT' hHm hv hX
  -- the fields lie in the rule's field domains at the `case`'s parameters, with no canonicity:
  -- `SpineOk` along the fields, whose λs are in the graph regime (their datum is the last
  -- binder's), puts each in its λ's domain; read back under the parameters alone
  have hsp1 : SpineOk Y1 Fs := by
    have e5 : (ps ++ [mo] ++ Ws).take (sh.nP + 1 + sh.nM) ++ (Ps ++ Fs).drop sh.nP =
        (ps ++ [mo] ++ Ws) ++ Fs := by
      rw [List.take_of_length_le (show (ps ++ [mo] ++ Ws).length ≤ sh.nP + 1 + sh.nM by
        simp; omega), show (Ps ++ Fs).drop sh.nP = Fs by rw [← hPl]; simp]
    rw [e5] at hsp
    have := spineOk_append hsp
    rwa [eY1] at this
  have hFCf := fields_fit_of_spineOk (M := M) (sh := sh) (D := Expr.mkAppN (.const sh.ind
    sh.indLevels) (bvarsFrom cs.nF sh.nP)) hf hY1 hsp1 (by omega) (by omega)
    (fun b hb => by rw [hreg j cs hj b hb]; exact hlastReg) (by omega) (by omega)
  have hcR : TeleCorr M.cval env φ (pushAll (ps ++ [mo] ++ Ws) ρ) (pushAll ps ρ)
      (liftTele (sh.nM - j) j cs.fields) fbs := by
    have := fieldsCorr (M := M) (φ := φ) (ps := ps) (ρ := ρ) (fbs := fbs) (cs := cs) (j := j)
      (k' := sh.nM - j) (junk := [mo] ++ Ws) hf (by simp; omega)
    rwa [← List.append_assoc] at this
  have hFR := fits_transport (liftTele (sh.nM - j) j cs.fields) fbs
    (cs.codom.liftLooseBVars 0 0) _ (by rw [liftTele_length, hfbl, hFl, hfl]) hcR hFCf (by omega)
  rw [List.drop_eq_nil_of_le (show (liftTele (sh.nM - j) j cs.fields).length ≤ Fs.length by
    rw [liftTele_length]; omega)] at hFR
  obtain ⟨Y2, hY2, eY2⟩ := lamTele_app _ _ _ hY1 hFR (by rw [liftTele_length]; omega)
  -- the induction hypotheses
  have hfv : ∀ rf (hrf : rf < cs.nF), pushAll Fs ρ (cs.nF - 1 - rf) = Fs[rf]'(by omega) := by
    intro rf hrf; rw [← hFl]; exact pushAll_rev Fs ρ rf (by omega)
  have hpre : (Ws.take j).length = j := by simp; omega
  have hcE : TeleCorr M.cval env φ (pushAll (ps ++ [mo] ++ Ws.take j) ρ) (pushAll ps ρ)
      cs.fields fbs := by
    have := fieldsCorr (M := M) (φ := φ) (ps := ps) (ρ := ρ) (fbs := fbs) (cs := cs) (j := j)
      (k' := 0) (junk := [mo] ++ Ws.take j) hf (by simp; omega)
    rwa [liftTele_zero, ← List.append_assoc] at this
  have hF1 := fits_transport cs.fields fbs (piTele cs.ihs (cs.codom.liftLooseBVars cs.ihs.length 0))
    _ (by omega) hcE hFCf (by omega)
  rw [List.drop_eq_nil_of_le (show cs.fields.length ≤ Fs.length by omega)] at hF1
  have hIHmem : ∀ rf ∈ cs.recFields, (ps ++ [mo] ++ Ws ++ [pushAll Fs ρ (cs.nF - 1 - rf)]).foldl app R0
      ∈ˢ app mo (pushAll Fs ρ (cs.nF - 1 - rf)) := by
    intro rf hrfm
    obtain ⟨hrf, hrd⟩ := hwf.recFields j cs hj rf hrfm
    rw [hfv rf hrf]
    -- the recursive field lies in the major's domain
    obtain ⟨X', hX', hm'⟩ := fits_get cs.fields _ hF1 rf (by omega) (by omega)
    rw [List.getElem?_eq_getElem (show rf < cs.fields.length by omega)] at hrd
    simp only [Option.map_some, Option.some.injEq] at hrd
    rw [hrd, CaseShape.recFieldDom] at hX'
    obtain ⟨IND, Ps1, hIND, hPs1, rfl⟩ := (den_mkAppN _).mp hX'
    obtain ⟨IND', Ps2, hIND', hPs2, rfl⟩ := (den_mkAppN _).mp hMajD
    have e3 : Ps1 = ps := by
      have := den_bvarsFrom (cval := M.cval) (env := env) (φ := φ) ρ
        ([mo] ++ Ws.take j ++ Fs.take rf) ps []
      rw [List.nil_append, show ([mo] ++ Ws.take j ++ Fs.take rf).length = rf + j + 1 by simp; omega,
        hps, show ps ++ ([mo] ++ Ws.take j ++ Fs.take rf) =
          ps ++ [mo] ++ Ws.take j ++ Fs.take rf by simp, pushAll_append (ps ++ [mo] ++ Ws.take j)] at this
      exact denotesList_functional hPs1 this
    have e4 : Ps2 = ps := by
      have := den_bvarsFrom (cval := M.cval) (env := env) (φ := φ) ρ [mo] ps []
      rw [List.nil_append, hps] at this
      exact denotesList_functional hPs2 this
    subst Ps1 Ps2
    obtain rfl := Denotes_functional (den_const_env hIND) hIND'
    have hfX : Fs[rf] ∈ˢ ps.foldl app IND := hm'
    have hsn := fits_snoc hQM rfl hXmajR hfX
    obtain ⟨TR, hTR, hrm⟩ := hTRm ρ
    obtain ⟨RR, hRR, hmRR⟩ := fits_app_mem hsn hTR hrm
    have hRR' : Denotes M.cval env φ (push Fs[rf] (pushAll (ps ++ [mo] ++ Ws) ρ))
        (.app (.bvar (sh.nM + 1)) (.bvar 0)) RR := hRR
    rw [den_app_bvars] at hRR'
    have hmo : push Fs[rf] (pushAll (ps ++ [mo] ++ Ws) ρ) (sh.nM + 1) = mo := by
      show pushAll (ps ++ [mo] ++ Ws) ρ sh.nM = mo
      rw [← hWl, show ps ++ [mo] ++ Ws = ps ++ mo :: Ws by simp, pushAll_at]
    rw [hmo] at hRR'
    rw [show app mo Fs[rf] = RR from hRR'.symm]
    exact hmRR
  -- the recursor's rule body: the wrapper at the fields and the induction hypotheses
  obtain ⟨IHs, hIHs⟩ : ∃ IHs : List V, IHs = cs.recFields.map fun rf =>
      (ps ++ [mo] ++ Ws ++ [pushAll Fs ρ (cs.nF - 1 - rf)]).foldl app R0 := ⟨_, rfl⟩
  have hIHl : IHs.length = cs.ihs.length := by rw [hIHs, List.length_map, hih]
  have hE : pushAll Fs (pushAll (ps ++ [mo] ++ Ws) ρ) = pushAll (ps ++ [mo] ++ Ws ++ Fs) ρ :=
    (pushAll_append _ _ _).symm
  have hIHterm : ∀ rf, rf < cs.nF → Denotes M.cval env φ (pushAll (ps ++ [mo] ++ Ws ++ Fs) ρ)
      (Expr.mkAppN (.const kr sh.recLevels) (bvarsFrom (cs.nF + sh.nM + 1) sh.nP ++
        [.bvar (cs.nF + sh.nM)] ++ bvarsFrom cs.nF sh.nM ++ [.bvar (cs.nF - 1 - rf)]))
      ((ps ++ [mo] ++ Ws ++ [pushAll Fs ρ (cs.nF - 1 - rf)]).foldl app R0) := by
    intro rf hrf
    refine (den_mkAppN _).mpr ⟨R0, _, den_const_env hR0, ?_, rfl⟩
    refine denotesList_append (denotesList_append (denotesList_append ?_ ?_) ?_) ?_
    · have := den_bvarsFrom (cval := M.cval) (env := env) (φ := φ) ρ ([mo] ++ Ws ++ Fs) ps []
      rwa [List.nil_append, show ([mo] ++ Ws ++ Fs).length = cs.nF + sh.nM + 1 by simp; omega,
        hps, show ps ++ ([mo] ++ Ws ++ Fs) = ps ++ [mo] ++ Ws ++ Fs by simp] at this
    · have := den_bvar_at (cval := M.cval) (env := env) (φ := φ) (a := ps) (y := mo) (c := Ws ++ Fs)
        (ρ := ρ)
      rw [show (Ws ++ Fs).length = cs.nF + sh.nM by simp; omega,
        show ps ++ mo :: (Ws ++ Fs) = ps ++ [mo] ++ Ws ++ Fs by simp] at this
      exact .cons this .nil
    · have := den_bvarsFrom (cval := M.cval) (env := env) (φ := φ) ρ Fs Ws (ps ++ [mo])
      rwa [hFl, hWl] at this
    · refine .cons ?_ .nil
      have hv : pushAll (ps ++ [mo] ++ Ws ++ Fs) ρ (cs.nF - 1 - rf) = pushAll Fs ρ (cs.nF - 1 - rf) := by
        rw [pushAll_append (ps ++ [mo] ++ Ws)]
        exact pushAll_lt (show cs.nF - 1 - rf < Fs.length by omega)
      rw [← hv]
      exact .bvar
  have hbodyR : Denotes M.cval env φ (pushAll Fs (pushAll (ps ++ [mo] ++ Ws) ρ))
      (Expr.mkAppN (.bvar (cs.nF + sh.nM - 1 - j)) (bvarsFrom 0 cs.nF ++ cs.recFields.map fun r =>
        Expr.mkAppN (.const kr sh.recLevels) (bvarsFrom (cs.nF + sh.nM + 1) sh.nP ++
          [.bvar (cs.nF + sh.nM)] ++ bvarsFrom cs.nF sh.nM ++ [.bvar (cs.nF - 1 - r)])))
      ((Fs ++ IHs).foldl app (Ws[j]'(by omega))) := by
    rw [hE]
    refine (den_mkAppN _).mpr ⟨_, Fs ++ IHs, ?_, ?_, rfl⟩
    · have hlt : ps.length + 1 + j < (ps ++ [mo] ++ Ws).length := by simp; omega
      have h2 := pushAll_rev (ps ++ [mo] ++ Ws) ρ (ps.length + 1 + j) hlt
      rw [show (ps ++ [mo] ++ Ws).length - 1 - (ps.length + 1 + j) = sh.nM - 1 - j by simp; omega]
        at h2
      have h4 : (ps ++ [mo] ++ Ws)[ps.length + 1 + j] = Ws[j]'(by omega) := by
        rw [List.getElem_append_right (show (ps ++ [mo]).length ≤ ps.length + 1 + j by simp)]
        simp
      have hv : pushAll (ps ++ [mo] ++ Ws ++ Fs) ρ (cs.nF + sh.nM - 1 - j) = Ws[j]'(by omega) := by
        rw [pushAll_append (ps ++ [mo] ++ Ws),
          show cs.nF + sh.nM - 1 - j = (sh.nM - 1 - j) + Fs.length by omega, pushAll_offset, h2, h4]
      rw [← hv]
      exact .bvar
    · refine denotesList_append ?_ ?_
      · have := den_bvarsFrom (cval := M.cval) (env := env) (φ := φ) ρ [] Fs (ps ++ [mo] ++ Ws)
        rwa [List.append_nil, List.length_nil, hFl] at this
      · rw [hIHs]
        have hall : ∀ l : List Nat, (∀ rf ∈ l, rf < cs.nF) →
            DenotesList M.cval env φ (pushAll (ps ++ [mo] ++ Ws ++ Fs) ρ)
              (l.map fun r => Expr.mkAppN (.const kr sh.recLevels)
                (bvarsFrom (cs.nF + sh.nM + 1) sh.nP ++ [.bvar (cs.nF + sh.nM)] ++
                  bvarsFrom cs.nF sh.nM ++ [.bvar (cs.nF - 1 - r)]))
              (l.map fun rf => (ps ++ [mo] ++ Ws ++ [pushAll Fs ρ (cs.nF - 1 - rf)]).foldl app R0) := by
          intro l hl
          induction l with
          | nil => exact .nil
          | cons rf l ih =>
            exact .cons (hIHterm rf (hl rf (by simp))) (ih fun r h => hl r (by simp [h]))
        exact hall cs.recFields fun rf h => (hwf.recFields j cs hj rf h).1
  have eY2' : Y2 = (Fs ++ IHs).foldl app (Ws[j]'(by omega)) := Denotes_functional hY2 hbodyR
  -- β through the wrapper
  have hF2 : Fits M.cval env φ (pushAll Fs (pushAll (ps ++ [mo] ++ Ws.take j) ρ))
      (piTele cs.ihs (cs.codom.liftLooseBVars cs.ihs.length 0)) IHs
      (pushAll IHs (pushAll Fs (pushAll (ps ++ [mo] ++ Ws.take j) ρ)))
      (cs.codom.liftLooseBVars cs.ihs.length 0) := by
    refine fits_of_forall cs.ihs _ hIHl fun r h1 h2 => ?_
    obtain ⟨rf, hrf'⟩ : ∃ rf, cs.recFields[r]? = some rf :=
      ⟨_, List.getElem?_eq_getElem (show r < cs.recFields.length by omega)⟩
    have hrfm : rf ∈ cs.recFields := List.mem_of_getElem? hrf'
    have hrfl := (hwf.recFields j cs hj rf hrfm).1
    have hd := hwf.ihs j cs hj r rf hrf'
    rw [List.getElem?_eq_getElem h2] at hd
    simp only [Option.map_some, Option.some.injEq] at hd
    refine ⟨app mo (pushAll Fs ρ (cs.nF - 1 - rf)), ?_, ?_⟩
    · rw [hd, ← pushAll_append]
      refine (ihDom_den hpre (by simp; omega) hrfl).mpr ?_
      rw [pushAll_append, show r + cs.nF - 1 - rf = (cs.nF - 1 - rf) + (IHs.take r).length by
        simp; omega, pushAll_offset]
    · have hr : cs.recFields[r]'(by omega) = rf :=
        Option.some.inj ((List.getElem?_eq_getElem (by omega)).symm.trans hrf')
      simp only [hIHs, List.getElem_map, hr]
      exact hIHmem rf hrfm
  have hF12 := fits_trans hF1 hF2
  rw [← piTele_append] at hF12
  have hcW := wrapper_corr (M := M) (φ := φ) (ps := ps) (mo := mo) (t := t) (ρ := ρ) hf hfl hih
    (hwf.ihs j cs hj) (fun rf h => (hwf.recFields j cs hj rf h).1) hjm hpre
  have hFW := fits_transport _ _ (cs.codom.liftLooseBVars 0 0) _ (liftTele_length _ _ _) hcW hF12
    (by simp; omega)
  rw [List.drop_eq_nil_of_le (show (liftTele (mins.length + 1 - j) j (cs.fields ++ cs.ihs)).length ≤
    (Fs ++ IHs).length by rw [liftTele_length]; simp; omega)] at hFW
  have hWj := hWd j cs (by omega) hj
  rw [wrapper_eq _ _ _ hfl, ← hmins] at hWj
  obtain ⟨Y3, hY3, eY3⟩ := lamTele_app _ _ _ hWj hFW (by rw [liftTele_length]; simp; omega)
  have hwb := wrapper_body (M := M) (φ := φ) (ps := ps) (mo := mo) (t := t) (ρ := ρ) hjm
    (Fs' := Fs) (hs := IHs)
  rw [show (cs.fields ++ cs.ihs).length = Fs.length + IHs.length by simp; omega,
    show cs.ihs.length = IHs.length by omega, show cs.nF = Fs.length by omega] at hY3
  have eY3' := Denotes_functional hY3 hwb
  -- the chain: minor `j` applies to the fields in the graph regime
  obtain ⟨XM, hXM, hmXM⟩ := hminD j hjm
  have hbj : (bMin[j]'(by omega)).1 = CaseShape.casesMinor j cs := by
    have := hbmin j cs hj
    rw [List.getElem?_eq_getElem (by omega)] at this
    exact Option.some.inj this
  rw [hbj, CaseShape.casesMinor, lift_piTele] at hXM
  have hcC1 : TeleCorr M.cval env φ (pushAll (ps ++ mo :: t :: mins.take j) ρ) (pushAll ps ρ)
      (liftTele 1 j cs.fields) fbs :=
    fieldsCorr (M := M) (φ := φ) (ps := ps) (ρ := ρ) (fbs := fbs) (cs := cs) (j := j) (k' := 1)
      (junk := mo :: t :: mins.take j) hf (by simp; omega)
  have hFE := fits_transport (liftTele 1 j cs.fields) fbs
    (cs.codom.liftLooseBVars 1 (j + cs.fields.length)) _ (by rw [liftTele_length]; omega) hcC1 hFCf
    (by omega)
  have hreg' : ∀ b ∈ liftTele 1 j cs.fields, regime φ b.2.pw ≠ 0 := by
    intro b hb
    have hb2 : b.2 ∈ (liftTele 1 j cs.fields).map (·.2) := List.mem_map_of_mem hb
    rw [liftTele_metas] at hb2
    obtain ⟨b', hb', e⟩ := List.mem_map.mp hb2
    rw [← e, hreg j cs hj b' hb']
    exact hlastReg
  refine ⟨?_, appChain_of_fits _ _ hXM hmXM hFE (by rw [liftTele_length]; omega) hreg'⟩
  rw [ht, heq, List.take_of_length_le (show (ps ++ [mo] ++ Ws).length ≤ sh.nP + 1 + sh.nM by
    simp; omega), show (Ps ++ Fs).drop sh.nP = Fs by rw [← hPl]; simp, List.foldl_append, eY1, eY2,
    eY2', eY3, eY3']

/-- **The generic `case` lemma, model side, without canonicity** (`caseIotaGWith` at the sort clause
`NeverProp`). -/
theorem caseIotaG (M : Model V env) (hδ : DefnValue M) (hι : IotaLawG M.cval env)
    (hcv : CvalParams M) {kc kr : KKey} {sh : CaseShape}
    (hS : CaseStored env kc kr sh) (hB : CaseRulesBlind env kr) (cvc : ConstantVal .anon) (val : KExpr)
    (hint : ReducibilityHint) (hfc : env.find? kc = some (.defnInfo cvc val hint))
    (φ : LevelParam → Nat) (ρ σ : BVarIdx → V) (R : KExpr) (As : List V)
    (hfit : Fits M.cval env φ ρ cvc.type As σ R) (hlen : As.length = sh.nP + 2 + sh.nM)
    (hlast : LastSiteOk (M.cval kc φ) As)
    (j : Nat) (cs : CtorShape) (cvC : ConstantVal .anon) (K : V) (Ps Fs : List V)
    (σC : BVarIdx → V) (RC : KExpr) (hj : sh.ctors[j]? = some cs)
    (hcC : env.find? cs.key = some (.ctorInfo cvC sh.nP cs.nF))
    (hK : Denotes M.cval env φ ρ (.const cs.key sh.indLevels) K)
    (hFC : Fits M.cval env φ ρ (cvC.type.instantiateLevelParams cvC.levelParams sh.indLevels)
      (Ps ++ Fs) σC RC)
    (hPl : Ps.length = sh.nP) (hFl : Fs.length = cs.nF)
    (hmaj : As[sh.nP + 1]? = some ((Ps ++ Fs).foldl app K)) :
    ∃ Mn, As[sh.nP + 2 + j]? = some Mn ∧ As.foldl app (M.cval kc φ) = Fs.foldl app Mn ∧
      AppChain Mn Fs :=
  caseIotaGWith M hδ hι hcv hS hB cvc val hint hfc φ ρ σ R As hfit hlen hlast j cs cvC K Ps Fs σC RC
    hj hcC hK hFC hPl hFl hmaj

/-! ## The SrcEval side -/

variable {M : Model V env} {κ : CId → KKey} {lpsOf : CId → List Nat} {S : CId → Prop}
  {Ok : CId → Levels → Prop}

/-- **The generic `case` lemma, SrcEval side, without canonicity**: `CaseFires` at every `case`
constant whose shape is checked (`CaseStored`, `CaseProg`), whose recursor's rules do not compare
parameters (`CaseRulesBlind`) and whose constructors have no level parameters (`sh.indLevels = []`;
`CaseWF.ctorRaw` gives each constructor as many). A literal major as `caseFires_of_shape`; a
constructor value at the parameters and the assignment it was built at, through `caseIotaG`. Laws:
`DefnValue`, `IotaLawG`, `CvalParams` (and `Model.mem`); not `ctor_canon`. -/
theorem caseFires_of_blind (hδ : DefnValue M) (hι : IotaLawG M.cval env) (hcv : CvalParams M)
    {p : Program} {c r : CId} {sh : CaseShape}
    (hF : Faith p env κ lpsOf S) (hN : NatBasis env) (_hSc : S c)
    (hres : p.table.resolveOf c = some (.case r)) (hst : CaseStored env (κ c) (κ r) sh)
    (hpr : CaseProg p κ S r sh) (hB : CaseRulesBlind env (κ r)) (hlv : sh.indLevels = []) :
    CaseFires M p κ lpsOf S Ok c := by
  intro r' sf kk lvls np nmot nmin ni ind rules ty hres' hd ls φ T ρ σ R As hh hfit hAsl hlast
    Tm mv j fields hTm hrelM hsel
  have hrr : r' = r := by rw [hres] at hres'; cases hres'; rfl
  subst hrr
  obtain ⟨sf0, kk0, lvls0, ind0, rules0, ty0, hd0, hctP, hnat⟩ := hpr.recr
  rw [hd0] at hd
  simp only [Option.some.injEq, IxCC.Src.Decl.recr.injEq] at hd
  obtain ⟨-, -, -, rfl, rfl, rfl, rfl, rfl, -, -⟩ := hd
  obtain ⟨cvc, hint, hfc, _, hty⟩ := hst.casesOnStored
  cases hh with
  | cases _ _ hfind =>
  rw [hfc] at hfind
  cases hfind
  have hfit' : Fits M.cval env φ ρ cvc.type As σ R := hfit
  have hlen : As.length = sh.nP + 2 + sh.nM := by omega
  have hTm' : As[sh.nP + 1]? = some Tm := by simpa using hTm
  have hidx : ∀ j', sh.nP + 1 + 0 + 1 + j' = sh.nP + 2 + j' := fun j' => by omega
  simp only [hidx]
  unfold Program.selectRule at hsel
  cases mv with
  | lit n =>
    simp only at hsel
    split at hsel
    · rename_i hnatc
      obtain ⟨hnP0, hkeys⟩ := hnat (by simpa using hnatc)
      have hTe := relV_lit_eq_cv hcv hN φ hrelM
      obtain ⟨cvZ, hfZ, _, htZ, hlZ⟩ := hN.zero
      obtain ⟨cvS, hfS, _, htS, hlS⟩ := hN.succ
      have hF0 := natFacts M hN φ
      obtain ⟨cs0, hcs0, hk0, hn0⟩ := get_of_map_pair (l := sh.ctors) (i := 0)
        (by rw [hkeys]; rfl)
      obtain ⟨cs1, hcs1, hk1, hn1⟩ := get_of_map_pair (l := sh.ctors) (i := 1)
        (by rw [hkeys]; rfl)
      obtain ⟨cvC0, hfC0, hlC0, -⟩ := hst.wf.ctorRaw 0 cs0 hcs0
      rw [hk0, hfZ, hnP0, hn0] at hfC0
      cases hfC0
      have hil : sh.indLevels = [] := by
        rw [hlZ] at hlC0; exact List.eq_nil_of_length_eq_zero hlC0.symm
      cases n with
      | zero =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsel
        obtain ⟨rfl, rfl⟩ := hsel
        have hK : Denotes M.cval env φ ρ (.const cs0.key sh.indLevels) (M.cval natZeroName φ) := by
          rw [hk0, hil]; exact (den_const0 hfZ hlZ).mpr rfl
        have hcC : env.find? cs0.key = some (.ctorInfo cvZ sh.nP cs0.nF) := by
          rw [hk0, hnP0, hn0]; exact hfZ
        have hFC : Fits M.cval env φ ρ (cvZ.type.instantiateLevelParams cvZ.levelParams sh.indLevels)
            (As.take sh.nP ++ []) ρ (cvZ.type.instantiateLevelParams cvZ.levelParams sh.indLevels) := by
          rw [hnP0, List.take_zero]; exact .nil
        have hmaj : As[sh.nP + 1]? = some ((As.take sh.nP ++ []).foldl app (M.cval natZeroName φ)) := by
          rw [hTm', hTe, hnP0, List.take_zero]; rfl
        obtain ⟨Mn, hMn, heq, hch⟩ := caseIotaG M hδ hι hcv hst hB cvc _ hint hfc φ ρ σ R As hfit' hlen
          hlast 0 cs0 cvZ _ (As.take sh.nP) [] ρ _ hcs0 hcC hK hFC (by simp; omega)
          (by rw [hn0]; rfl) hmaj
        exact ⟨Mn, [], hMn, .nil, heq, hch⟩
      | succ n =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsel
        obtain ⟨rfl, rfl⟩ := hsel
        obtain ⟨cvC1, hfC1, -, -⟩ := hst.wf.ctorRaw 1 cs1 hcs1
        rw [hk1, hfS, hnP0, hn1] at hfC1
        cases hfC1
        have hK : Denotes M.cval env φ ρ (.const cs1.key sh.indLevels) (M.cval natSuccName φ) := by
          rw [hk1, hil]; exact (den_const0 hfS hlS).mpr rfl
        have hcC : env.find? cs1.key = some (.ctorInfo cvS sh.nP cs1.nF) := by
          rw [hk1, hnP0, hn1]; exact hfS
        have hi0 := inst_self ([] : List LevelParam) cvS.type
        simp only [List.map_nil] at hi0
        have hFC : Fits M.cval env φ ρ (cvS.type.instantiateLevelParams cvS.levelParams sh.indLevels)
            (As.take sh.nP ++ [litSet M φ n]) (push (litSet M φ n) ρ) natK := by
          rw [hnP0, List.take_zero, List.nil_append, hil, hlS, hi0, htS]
          exact .cons ((hF0.natD _ _).mpr rfl) (lit_mem M hF0 n) .nil
        have hmaj : As[sh.nP + 1]? =
            some ((As.take sh.nP ++ [litSet M φ n]).foldl app (M.cval natSuccName φ)) := by
          rw [hTm', hTe, hnP0, List.take_zero]; rfl
        obtain ⟨Mn, hMn, heq, hch⟩ := caseIotaG M hδ hι hcv hst hB cvc _ hint hfc φ ρ σ R As hfit' hlen
          hlast 1 cs1 cvS _ (As.take sh.nP) [litSet M φ n] _ _ hcs1 hcC hK hFC (by simp; omega)
          (by rw [hn1]; rfl) hmaj
        exact ⟨Mn, [litSet M φ n], hMn, .cons (.val (relV_lit_intro hN φ n)) .nil, heq, hch⟩
    · simp at hsel
  | con c' ls' ps fs =>
    simp only at hsel
    cases hd' : p.decl? c' with
    | none => simp [hd'] at hsel
    | some d' =>
      cases d' with
      | ctor sf' lvls' ind' cidx np' nf' ty' =>
        simp only [hd'] at hsel
        split at hsel
        · rename_i hcond
          simp only [Option.some.injEq, Prod.mk.injEq] at hsel
          obtain ⟨rfl, rfl⟩ := hsel
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond
          obtain ⟨rfl, -⟩ := hcond
          cases hrelM with
          | @con _ _ _ _ ψ cvC' np'' nf'' Ps Fs ρc σc Rc hSc' _ hfc' hPl hFl _ hfs' hfitc =>
          obtain ⟨hnp, cs, hcs, hkey, hnF⟩ := hctP c' hSc' sf' lvls' cidx np' nf' ty' hd'
          obtain ⟨cv, hfcv, _⟩ := hF.ctor c' hSc' sf' lvls' _ cidx np' nf' ty' hd'
          rw [hfcv] at hfc'
          simp only [Option.some.injEq, ConstantInfo.ctorInfo.injEq] at hfc'
          obtain ⟨rfl, rfl, rfl⟩ := hfc'
          subst hnp hnF
          obtain ⟨cvC, hfC, hlenC, hcl, hdef, -⟩ := hst.wf.ctorRaw cidx cs hcs
          have hfCk := hfC
          rw [hkey, hfcv] at hfC
          simp only [Option.some.injEq, ConstantInfo.ctorInfo.injEq] at hfC
          obtain ⟨rfl, -, -⟩ := hfC
          -- no level parameter (`sh.indLevels = []`): the constructor's image is one set at every
          -- assignment, and its fit moves to the `case`'s environment and assignment
          have hlp : cv.levelParams = [] := by
            rw [hlv] at hlenC; exact List.eq_nil_of_length_eq_zero hlenC
          have hK : Denotes M.cval env φ ρ (.const cs.key sh.indLevels) (M.cval (κ c') ψ) := by
            have h1 : Denotes M.cval env φ ρ (.const cs.key sh.indLevels)
                (M.cval cs.key (Level.substFn φ cv.levelParams sh.indLevels)) :=
              Denotes.const hfCk (by rw [← hlenC]; rfl)
            have e1 : M.cval cs.key (Level.substFn φ cv.levelParams sh.indLevels) =
                M.cval (κ c') ψ := by
              rw [hkey]
              exact hcv _ _ hfcv _ _ (by simp [ConstantInfo.toConstantVal, hlp])
            rwa [e1] at h1
          obtain ⟨σ2, hfit2⟩ := fits_agree hfitc (ρ' := ρ) fun i hi =>
            absurd (lt_of_bvarsLt hcl hi) (Nat.not_lt_zero i)
          have hFC := fits_inst_cv M hcv (ks := []) (us := []) (φ := φ) (ψ := ψ)
            (fun _ hp => by simp at hp) hfit2 (by rw [← hlp]; exact hdef)
          rw [← hlv, ← hlp] at hFC
          -- the guarded ι law at the constructor's own parameters `Ps` (`caseIotaG`)
          obtain ⟨Mn, hMn, heq, hch⟩ := caseIotaG M hδ hι hcv hst hB cvc _ hint hfc φ ρ σ R As
            hfit' hlen hlast cidx cs cv _ Ps Fs σ2 _ hcs hfCk hK hFC hPl hFl hTm'
          exact ⟨Mn, Fs, hMn, relSlots_of_relVs hfs', heq, hch⟩
        · simp at hsel
      | _ => simp [hd'] at hsel
  | _ => simp at hsel

/-! ## The decided fact of the canonicity-free family -/

/-- **`noCanonB` is sound** (the indexed reading answers as `Env.find?`, `KTab.get_of`). -/
theorem noCanon_of_check {p : Program} {κ : CId → KKey} {Sl : List CId}
    (h : noCanonB p env κ Sl = true) : NoCanon p env κ (· ∈ Sl) := by
  have hn : ∀ (rules : List (RecRule .anon)), ctorsNoLevelsB (KTab.of env) rules = true →
      ∀ rl ∈ rules, ∃ (cvC : ConstantVal .anon) (nP nF : Nat),
        env.find? rl.ctor = some (.ctorInfo cvC nP nF) ∧ cvC.levelParams = [] := by
    intro rules hr rl hrl
    have h1 := List.all_eq_true.mp hr rl hrl
    rw [KTab.get_of] at h1
    split at h1
    · rename_i cvC nP nF hc
      exact ⟨cvC, nP, nF, hc, List.isEmpty_iff.mp h1⟩
    · cases h1
  have hall := List.all_eq_true.mp h
  refine ⟨fun c r hc hr => ?_, fun r hr hk => ?_⟩
  · have h1 := hall c hc
    simp only [hr, Bool.and_eq_true] at h1
    have h2 := h1.1
    rw [KTab.get_of] at h2
    split at h2
    · rename_i cvr mI rP rules hf
      simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h2
      exact ⟨cvr, mI, rP, rules, hf, fun rl hrl => ⟨h2.1 rl hrl, hn rules h2.2 rl hrl⟩⟩
    · cases h2
  · have h1 := (Bool.and_eq_true _ _).mp (hall r hr)
    have h2 := h1.2
    have hk' : (match recClassB p env κ r with
        | some .flat | some .noParams =>
          match (KTab.of env)[κ r]? with
          | some (.recInfo _ _ _ rules) => ctorsNoLevelsB (KTab.of env) rules
          | _ => false
        | _ => true) = true := h2
    rcases hk with hk | hk <;> rw [hk] at hk' <;> simp only at hk' <;> rw [KTab.get_of] at hk' <;>
      split at hk' <;>
      first
        | (rename_i cvr mI rP rules hf; exact ⟨cvr, mI, rP, rules, hf, hn rules hk'⟩)
        | cases hk'

/-- **A `case` recursor that needs no canonicity, at a checked shape**: its rules do not compare
parameters, and the inductive has no level (each constructor has as many level parameters as
`sh.indLevels`, `CaseWF.ctorRaw`, and there is one, `CaseStored.arity`). -/
theorem caseBlind_of_noCanon {kc kr : KKey} {sh : CaseShape} (h : CaseNoCanon env kr)
    (hst : CaseStored env kc kr sh) : CaseRulesBlind env kr ∧ sh.indLevels = [] := by
  obtain ⟨cvr, mI, rP, rules, hf, hall⟩ := h
  refine ⟨⟨cvr, mI, rP, rules, hf, fun rl hrl => (hall rl hrl).1⟩, ?_⟩
  obtain ⟨cvr', rules', hf', -, -, hlen, hrules⟩ := hst.recursor
  rw [hf] at hf'
  simp only [Option.some.injEq, ConstantInfo.recInfo.injEq] at hf'
  obtain ⟨-, -, -, rfl⟩ := hf'
  have hpos : 0 < sh.ctors.length := hst.arity.2
  obtain ⟨cs, hcs⟩ : ∃ cs, sh.ctors[0]? = some cs := ⟨_, List.getElem?_eq_getElem hpos⟩
  obtain ⟨rl, hrl⟩ : ∃ rl, rules[0]? = some rl :=
    ⟨_, List.getElem?_eq_getElem (show 0 < rules.length by rw [hlen]; exact hpos)⟩
  obtain ⟨hkey, -⟩ := hrules 0 cs rl hcs hrl
  obtain ⟨-, cvC, nP, nF, hc, hlp⟩ := hall rl (List.mem_of_getElem? hrl)
  obtain ⟨cvC', hfC, hlenC, -⟩ := hst.wf.ctorRaw 0 cs hcs
  rw [← hkey, hc] at hfC
  simp only [Option.some.injEq, ConstantInfo.ctorInfo.injEq] at hfC
  obtain ⟨rfl, -, -⟩ := hfC
  rw [hlp] at hlenC
  exact List.eq_nil_of_length_eq_zero hlenC.symm

/-- **F5 at every `case` entry of `S`, with no canonicity**: `CaseFacts` gives each a checked
shape, `NoCanon` makes it blind and level-free (`caseBlind_of_noCanon`), and `caseFires_of_blind`
does the rest. Laws: `DefnValue`, `IotaLawG`, `CvalParams`. -/
theorem caseFires_of_noCanon (hδ : DefnValue M) (hι : IotaLawG M.cval env) (hcv : CvalParams M)
    {p : Program} (hF : Faith p env κ lpsOf S) (hN : NatBasis env) (hC : CaseFacts p env κ S)
    (hNC : NoCanon p env κ S) :
    ∀ c r, S c → p.table.resolveOf c = some (.case r) → p.table.recKindOf r = some .ordinary →
      CaseFires M p κ lpsOf S Ok c := by
  intro c r hc hr hk
  obtain ⟨sh, hst, hpr⟩ := hC c r hc hr hk
  obtain ⟨hB, hlv⟩ := caseBlind_of_noCanon (hNC.cases c r hc hr) hst
  exact caseFires_of_blind hδ hι hcv hF hN hc hr hst hpr hB hlv

end IxCC.Grounding
