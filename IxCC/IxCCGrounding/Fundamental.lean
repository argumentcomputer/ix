import IxCCGrounding.Hyps
import IxCCGrounding.Heads
import IxCCGrounding.EqRec
import IxCCGrounding.RecFlat
import IxCCGrounding.RecRun

/-!
# The fundamental lemma (`IxCCGrounding.Fundamental`), step (f)

**Statement.** Under `FundHyps` (the laws, the `Nat` basis, the faithfulness clauses, F5's meaning
at each `case` constant, the `eqn` lemma, and the typing hypotheses), at every clock `k`, each of
SrcEval's eight mutual functions returns values related to what their kernel counterparts denote
(`AllP k`):

| SrcEval | Statement | Proved from |
| --- | --- | --- |
| `force` | a forced slot's value relates to the slot's set | `RelSlot.name` and `eval` at `k - 1` |
| `forceAll` | likewise, pointwise | `force` |
| `fire` | a saturated head's value relates to the head applied to the arguments | F1 by `Fits` and the pins; F5 by `CaseFires`; F6 by `nat_accel`; at a recursor, its class admitted (`RecFacts`): F4 traps, so returns no value; F3 at `Eq.rec` returns the minor premise's slot, forced, by `eqRec_iota` |
| `headValue` | a head's value relates to the head | `fire` on no arguments, or `RelV.pap` |
| `apply` | at a graph-regime site, the result relates to the application | `apply_clo` and `eval` at `k - 1`; `apply_pap` and `fire` |
| `applyAll` | along a graph-regime chain, likewise | `apply` |
| `evalConst` | an unfolded constant's value relates to the constant | δ (`defn_value`), `eqn`, heads |
| `eval` | a running term's value relates to its kernel term's denotation | induction on `Runs` |

**The induction.** Strong induction on the clock; inside one clock the eight statements are proved
in the order `force`, `forceAll`, `fire`, `headValue`, `apply`, `applyAll`, `evalConst`, `eval`,
each using the earlier ones at the same clock and all of them at smaller clocks. SrcEval's own
termination measure is `(k, size, ·)`: every call at the same clock is to a function earlier in
that order or (for `eval`, `forceAll`, `applyAll`) on a smaller term or list, which is the inner
induction. The clock is only the measure: the relation has no index.
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open IxCC.Src (Value Slot Term CId Program Levels)
open IxCC.Sem (Result later later_succ later_zero)

universe w

section Fund

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv} (M : Model V env) (p : Program)
  (κ : CId → KKey) (lpsOf : CId → List Nat) (S : CId → Prop) (Ok : CId → Levels → Prop)

/-- `force` at clock `k`. -/
def ForceP (k : Nat) : Prop :=
  ∀ (s : Slot) (v : Value) (X : V), IxCC.Src.force p k s = .ok v →
    RelSlot M p κ lpsOf S Ok s X → RelV M p κ lpsOf S Ok v X

/-- `forceAll` at clock `k`. -/
def ForceAllP (k : Nat) : Prop :=
  ∀ (ss : List Slot) (vs : List Value) (Xs : List V), IxCC.Src.forceAll p k ss = .ok vs →
    RelSlots M p κ lpsOf S Ok ss Xs → RelVs M p κ lpsOf S Ok vs Xs

/-- `fire` at clock `k`: a saturated head whose arguments fit its stored type, the last applied
at a graph-regime site. -/
def FireP (k : Nat) : Prop :=
  ∀ (h : IxCC.Src.Head) (ls : Levels) (args : List Slot) (v : Value) (φ : LevelParam → Nat)
    (kk : KKey) (T : KExpr) (ρ σ : BVarIdx → V) (R : KExpr) (As : List V),
    IxCC.Src.fire p k h ls args = .ok v → RelSlots M p κ lpsOf S Ok args As →
    HeadAt M p κ lpsOf S Ok h ls φ kk T → Fits M.cval env φ ρ T As σ R →
    args.length = p.headArity h → LastSiteOk (M.cval kk φ) As →
    RelV M p κ lpsOf S Ok v (As.foldl app (M.cval kk φ))

/-- `headValue` at clock `k`. -/
def HeadValueP (k : Nat) : Prop :=
  ∀ (h : IxCC.Src.Head) (ls : Levels) (v : Value) (φ : LevelParam → Nat) (kk : KKey) (T : KExpr),
    IxCC.Src.headValue p k ls h = .ok v → HeadAt M p κ lpsOf S Ok h ls φ kk T →
    RelV M p κ lpsOf S Ok v (M.cval kk φ)

/-- `apply` at clock `k`, at a graph-regime site. -/
def ApplyP (k : Nat) : Prop :=
  ∀ (f : Value) (s : Slot) (w : Value) (X Y : V) (v : Nat) (A : V) (B : V → V),
    IxCC.Src.apply p k f s = .ok w → RelV M p κ lpsOf S Ok f X → RelSlot M p κ lpsOf S Ok s Y →
    v ≠ 0 → X ∈ˢ piR v A B → Y ∈ˢ A → RelV M p κ lpsOf S Ok w (app X Y)

/-- `applyAll` at clock `k`, along a graph-regime chain. -/
def ApplyAllP (k : Nat) : Prop :=
  ∀ (f : Value) (ss : List Slot) (w : Value) (X : V) (Ys : List V),
    IxCC.Src.applyAll p k f ss = .ok w → RelV M p κ lpsOf S Ok f X →
    RelSlots M p κ lpsOf S Ok ss Ys → AppChain X Ys → RelV M p κ lpsOf S Ok w (Ys.foldl app X)

/-- `evalConst` at clock `k`, at an instance `Ok` admits. -/
def EvalConstP (k : Nat) : Prop :=
  ∀ (ls : Levels) (c : CId) (v : Value) (φ : LevelParam → Nat),
    IxCC.Src.evalConst p k ls c = .ok v → S c → Ok c ls → LvAt φ (lpsOf c) ls →
    RelV M p κ lpsOf S Ok v (M.cval (κ c) φ)

/-- `eval` at clock `k`, on a term that runs. -/
def EvalP (k : Nat) : Prop :=
  ∀ (lps : List Nat) (ls : Levels) (φ : LevelParam → Nat) (σ : Sig) (Γ : List KExpr) (t : Term)
    (e : KExpr), Runs M κ Ok lps ls φ σ Γ t e →
    ∀ (ρ : IxCC.Src.Env) (ρk : BVarIdx → V) (v : Value),
    ConstsIn S t → LvAt φ lps ls → RelEnv M p κ lpsOf S Ok φ ρ σ ρk → CtxSat M φ Γ ρk →
    IxCC.Src.eval p k ls ρ t = .ok v →
    ∃ X, Denotes M.cval env φ ρk e X ∧ RelV M p κ lpsOf S Ok v X

/-- **All eight statements at clock `k`.** -/
structure AllP (k : Nat) : Prop where
  force : ForceP M p κ lpsOf S Ok k
  forceAll : ForceAllP M p κ lpsOf S Ok k
  fire : FireP M p κ lpsOf S Ok k
  headValue : HeadValueP M p κ lpsOf S Ok k
  apply : ApplyP M p κ lpsOf S Ok k
  applyAll : ApplyAllP M p κ lpsOf S Ok k
  evalConst : EvalConstP M p κ lpsOf S Ok k
  eval : EvalP M p κ lpsOf S Ok k

variable {M p κ lpsOf S Ok}

theorem atLevels_ordinary (ls : Levels) : IxCC.Src.RecKind.atLevels ls .ordinary = .ordinary := rfl

/-- A head's arity is no longer than its stored telescope. -/
theorem head_tele (H : FundHyps M p κ lpsOf S Ok) {h : IxCC.Src.Head} {ls : Levels}
    {φ : LevelParam → Nat} {kk : KKey} {T : KExpr} (hh : HeadAt M p κ lpsOf S Ok h ls φ kk T) :
    p.headArity h ≤ kPis T := by
  cases hh with
  | @ctor c _ _ ci hSc _ hfind =>
    cases hd : p.decl? c with
    | none => simp [Program.headArity, hd]
    | some d =>
      cases d with
      | ctor sf lvls ind cidx np nf ty =>
        obtain ⟨cv, hcv, hle⟩ := H.faith.ctor c hSc sf lvls ind cidx np nf ty hd
        rw [hfind] at hcv
        cases hcv
        show p.headArity (.ctor c) ≤ kPis cv.type
        simpa [Program.headArity, hd] using hle
      | _ => simp [Program.headArity, hd]
  | @cases c _ _ ci hSc _ hfind =>
    cases hres : p.table.resolveOf c with
    | none => simp [Program.headArity, hres]
    | some res =>
      cases res with
      | case r =>
        obtain ⟨_, ci', hf', hle⟩ := H.faith.caseRec c r hSc hres
        rw [hfind] at hf'
        cases hf'
        exact hle
      | _ => simp [Program.headArity, hres]
  | @recr r _ _ ci hSr _ hfind =>
    -- the arity fact of the checked shape (`RecStored`)
    cases hd : p.decl? r with
    | none => simp [Program.headArity, hd]
    | some d =>
      cases d with
      | recr sf kk lvls np nmot nmin ni ind rules ty =>
        obtain ⟨⟨sf', kk', lvls', np', nmot', nmin', ni', ind', rules', ty', cvr, krules, hd', hf',
          _, har, _⟩⟩ := H.faith.recs.stored r hSr sf kk lvls np nmot nmin ni ind rules ty hd
        rw [hd] at hd'
        cases hd'
        rw [hfind] at hf'
        cases hf'
        show p.headArity (.recr r) ≤ kPis cvr.type
        simpa [Program.headArity, hd, IxCC.Src.Decl.recArity] using har
      | _ => simp [Program.headArity, hd, IxCC.Src.Decl.recArity]
  | prim _ _ har => exact har

/-- `As` related to literal values are the literals' sets. -/
theorem relVs_lits (hL : LawsCore M) (hS : NatBasis env) (φ : LevelParam → Nat) :
    ∀ {ns : List Nat} {Xs : List V}, RelVs M p κ lpsOf S Ok (ns.map .lit) Xs →
      Xs = ns.map (litSet M φ)
  | [], _, h => by rw [List.map_nil] at h; cases h; rfl
  | n :: ns, _, h => by
    rw [List.map_cons] at h
    cases h with
    | cons hv h' => rw [relV_lit_eq hL hS φ hv, relVs_lits hL hS φ h']; rfl

/-! ## The steps -/

theorem force_step {k : Nat} (ih : ∀ k' < k, AllP M p κ lpsOf S Ok k') :
    ForceP M p κ lpsOf S Ok k := by
  intro s v X hrun hs
  cases hs with
  | val hv =>
    rw [IxCC.Src.force_val] at hrun
    rw [← ok_inj hrun]
    exact hv
  | name hlv henv hctx hruns hcs hden =>
    rw [IxCC.Src.force_name] at hrun
    cases k with
    | zero => exact absurd hrun (by simp)
    | succ k' =>
      rw [later_succ] at hrun
      obtain ⟨X', hX', hv⟩ :=
        (ih k' (Nat.lt_succ_self k')).eval _ _ _ _ _ _ _ hruns _ _ _ hcs hlv henv hctx hrun
      rw [Denotes_functional hden hX']
      exact hv

theorem forceAll_step {k : Nat} (hf : ForceP M p κ lpsOf S Ok k) :
    ForceAllP M p κ lpsOf S Ok k := by
  intro ss
  induction ss with
  | nil =>
    intro vs Xs hrun hss
    rw [IxCC.Src.forceAll_nil] at hrun
    rw [← ok_inj hrun]
    cases hss
    exact .nil
  | cons s ss ih =>
    intro vs Xs hrun hss
    cases hss with
    | cons hs hss' =>
      rw [IxCC.Src.forceAll_cons] at hrun
      obtain ⟨v, hv, hrest⟩ := Result.bind_eq_ok_iff.mp hrun
      obtain ⟨vs', hvs', hfin⟩ := Result.bind_eq_ok_iff.mp hrest
      rw [← ok_inj hfin]
      exact .cons (hf _ _ _ hv hs) (ih _ _ hvs' hss')

/-- **F2 at a recursor of class `noParams`** (G3, part E): the major forced, a literal (at the
pinned `Nat`) or a constructor value of the recursor's inductive; the rule of its constructor; its
body (peeled of the prefix's and the fields' λs) evaluated by SrcEval in the slots of the arguments
before the major and the fields. `eval`'s induction hypothesis (at the smaller clock) relates that
value to what the body denotes there: the body runs (`runs_of_corr`, `runs_peel`) because it
corresponds to the stored one, the stored rule is closed and denotes (by ι), it names no constant
(`RecBodies`), and its sites are typed (`ruleSites_ok`) at the levels SrcEval runs it at, since the
major premise was applied at a graph-regime site (`LastSiteOk`, `last_regime`). ι and β
(`noParamsIota`) make the body's set the recursor applied to the arguments; the constructor value's
image and fields are moved to the recursor's assignment without a law beyond `cval_params` where
the constructor has no level parameters (`ctorFields_noLevels`), by the restricted canonicity where
it has some (`ctorFields_canon`). Laws: through the direct route's soundness, `Laws` whole. -/
theorem fire_noParams (H : FundHyps M p κ lpsOf S Ok) {k' : Nat}
    (ih : AllP M p κ lpsOf S Ok k') {r : CId} (hcl : recClassB p env κ r = some .noParams)
    {ls : Levels} {args : List Slot} {v : Value} {φ : LevelParam → Nat} {T : KExpr}
    {ρ σ : BVarIdx → V} {R : KExpr} {As : List V}
    (hrun : IxCC.Src.fire p (k' + 1) (.recr r) ls args = .ok v)
    (hargs : RelSlots M p κ lpsOf S Ok args As) (hh : HeadAt M p κ lpsOf S Ok (.recr r) ls φ (κ r) T)
    (hfit : Fits M.cval env φ ρ T As σ R) (hlen : args.length = p.headArity (.recr r))
    (hlast : LastSiteOk (M.cval (κ r) φ) As) :
    RelV M p κ lpsOf S Ok v (As.foldl app (M.cval (κ r) φ)) := by
  have hN := H.natBasis
  cases hh with
  | @recr _ _ _ ci hSr hlv hfind =>
  rw [IxCC.Src.fire_recr, later_succ] at hrun
  obtain ⟨hkind, sf, kk', lvls, nmot, nmin, ind, rules, ty, hd, hnp⟩ := recClassB_noParams hcl
  obtain ⟨hTele, hProg, hCtors, hFields, hBodies, hSites⟩ := H.faith.recs.noParams r hSr hcl
  -- the checked shape (`RecStored`)
  obtain ⟨⟨_, _, _, np', nmot', nmin', ni', _, rules', _, cvr, krules, hdS, hfS, _, _, hlenS,
    hruleS⟩⟩ := H.faith.recs.stored r hSr _ _ _ _ _ _ _ _ _ _ hd
  rw [hd] at hdS
  simp only [Option.some.injEq, IxCC.Src.Decl.recr.injEq] at hdS
  obtain ⟨-, -, -, rfl, rfl, rfl, rfl, -, rfl, -⟩ := hdS
  have hmI : 0 + nmot + nmin + 0 = nmot + nmin := by omega
  have hrP : 0 + nmot + nmin = nmot + nmin := by omega
  rw [hmI, hrP] at hfS
  rw [hfS] at hfind
  cases hfind
  have hfit : Fits M.cval env φ ρ cvr.type As σ R := hfit
  -- the rules' telescopes (`RecTele`)
  obtain ⟨cvr1, mI1, rP1, krules1, tbs, C, hf1, hty, htbs, hruleT⟩ := hTele
  rw [hfS] at hf1
  injection hf1 with hf1
  injection hf1 with e1 e2 e3 e4
  subst e1 e2 e3 e4
  -- the rules' constructors (`RecCtorsRaw`)
  obtain ⟨_, _, _, np2, _, _, _, ind2, _, _, cvr2, mI2, rP2, krules2, dom, body, mb, ls0, hd2, hf2,
    hpb, hdom, hctors⟩ := hCtors
  rw [hd] at hd2
  simp only [Option.some.injEq, IxCC.Src.Decl.recr.injEq] at hd2
  obtain ⟨-, -, -, rfl, -, -, -, rfl, -, -⟩ := hd2
  rw [hfS] at hf2
  injection hf2 with hf2
  injection hf2 with e1 e2 e3 e4
  subst e1 e2 e3 e4
  have hdomE : dom.getAppFn = .const (κ ind) ls0 := by rw [hdom, getAppFn_mkAppN]; rfl
  -- the rules' fields (`RecFields`)
  obtain ⟨cvr3, mI3, rP3, krules3, dom3, body3, m3, D3, ls3, hf3, hpb3, hdom3, hflds⟩ := hFields
  rw [hfS] at hf3
  injection hf3 with hf3
  injection hf3 with e1 e2 e3 e4
  subst e1 e2 e3 e4
  rw [hpb] at hpb3
  injection hpb3 with e5 e6 e7
  subst e5 e6 e7
  rw [hdomE] at hdom3
  injection hdom3 with e8 e9
  subst e8 e9
  -- the rule bodies (`RecBodies`)
  obtain ⟨_, _, _, np4, nmot4, nmin4, _, _, rules4, _, cvr4, mI4, rP4, krules4, hd4, hf4, hbodies,
    hclosed⟩ := hBodies
  rw [hd] at hd4
  simp only [Option.some.injEq, IxCC.Src.Decl.recr.injEq] at hd4
  obtain ⟨-, -, -, rfl, rfl, rfl, -, -, rfl, -⟩ := hd4
  rw [hfS] at hf4
  injection hf4 with hf4
  injection hf4 with e1 e2 e3 e4
  subst e1 e2 e3 e4
  -- the rule bodies' sites (`RecSites`)
  obtain ⟨_, _, _, _, _, _, _, _, rules5, _, cvr5, mI5, rP5, krules5, dom5, body5, m5, hd5, hf5,
    hpb5, hpwd, hrefs⟩ := hSites
  rw [hd] at hd5
  simp only [Option.some.injEq, IxCC.Src.Decl.recr.injEq] at hd5
  obtain ⟨-, -, -, -, -, -, -, -, rfl, -⟩ := hd5
  rw [hfS] at hf5
  injection hf5 with hf5
  injection hf5 with e1 e2 e3 e4
  subst e1 e2 e3 e4
  rw [hpb] at hpb5
  injection hpb5 with e5 e6 e7
  subst e5 e6 e7
  -- the program side (`RecProg`)
  obtain ⟨_, _, _, np3, _, _, _, ind3, rules3, _, hd3, hctP, hnat⟩ := hProg
  rw [hd] at hd3
  simp only [Option.some.injEq, IxCC.Src.Decl.recr.injEq] at hd3
  obtain ⟨-, -, -, rfl, -, -, -, rfl, rfl, -⟩ := hd3
  -- SrcEval's F2: the major, forced; the rule of its constructor
  have harity : args.length = nmot + nmin + 1 := by
    rw [hlen]; simp [Program.headArity, hd, IxCC.Src.Decl.recArity]
  have hAsl : As.length = nmot + nmin + 1 := by rw [relSlots_length hargs, harity]
  simp only [hd, hkind, Option.map_some, atLevels_ordinary, IxCC.Src.recChosen] at hrun
  obtain ⟨⟨j, fields⟩, hsel, hrest⟩ := Result.bind_eq_ok_iff.mp hrun
  obtain ⟨major, hmaj, hsel'⟩ := Result.bind_eq_ok_iff.mp hsel
  obtain ⟨sM, hsM⟩ : ∃ s, args[nmot + nmin]? = some s :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨Tm, hTm, hrelM⟩ := relSlots_get hargs hsM
  rw [List.getD_eq_getElem?_getD, hmI, hsM, Option.getD_some] at hmaj
  have hmajR := ih.force _ _ _ hmaj hrelM
  have hsel2 := ofOption_eq_ok.mp hsel'
  unfold Program.selectRule at hsel2
  -- the arguments before the major, and the major's domain
  have hxl : (As.take (nmot + nmin)).length = nmot + nmin := by simp; omega
  have hsplitA : As = As.take (nmot + nmin) ++ [Tm] := by
    have hdrop : As.drop (nmot + nmin) = [Tm] := by
      rw [List.getElem?_eq_getElem (by omega)] at hTm
      rw [List.drop_eq_getElem_cons (by omega), Option.some.inj hTm,
        List.drop_eq_nil_of_le (by omega)]
    rw [← hdrop, List.take_append_drop]
  have hfitA := hfit
  rw [hsplitA] at hfitA
  obtain ⟨σ1, R1, hfp, hfm⟩ := fits_append hfitA
  have hR1 : R1 = .forallE dom body mb := by rw [fits_piBody hfp, hxl, hpb]
  subst hR1
  obtain ⟨X, hX, hTmX⟩ : ∃ X, Denotes M.cval env φ σ1 dom X ∧ Tm ∈ˢ X := by
    cases hfm with
    | cons hA hx _ => exact ⟨_, hA, hx⟩
  -- the regime at the major premise's binder, from the graph-regime site that saturated the head
  obtain ⟨vv, AA, BB, hvv, hXm, -⟩ := hlast (As.take (nmot + nmin)) Tm hsplitA
  obtain ⟨TT, hTT, hHT⟩ := mem_key M hfS φ ρ
  have hTT' : Denotes M.cval env φ ρ cvr.type TT := hTT
  have hreg : regime φ mb.pw ≠ 0 := last_regime hfp hTT' hHT hvv hXm
  -- the common part: ι and β, the body runs, SrcEval's value related
  have tail : ∀ (j : Nat) (fields : List Slot) (rl : IxCC.Src.Rule) (krl : RecRule .anon)
      (cvC : ConstantVal .anon) (K : V) (Fs : List V) (σC : BVarIdx → V) (RC : KExpr),
      rules[j]? = some rl → krules[j]? = some krl →
      env.find? krl.ctor = some (.ctorInfo cvC 0 krl.nfields) →
      Denotes M.cval env φ ρ (.const krl.ctor ls0) K →
      Fits M.cval env φ ρ (cvC.type.instantiateLevelParams cvC.levelParams ls0) Fs σC RC →
      Fs.length = krl.nfields → Tm = Fs.foldl app K → RelSlots M p κ lpsOf S Ok fields Fs →
      (∀ t', IxCC.Src.peelLams (args.take (nmot + nmin) ++ fields).length rl.rhs = some t' →
        IxCC.Src.eval p k' ls (args.take (nmot + nmin) ++ fields).reverse t' = .ok v) →
      RelV M p κ lpsOf S Ok v (As.foldl app (M.cval (κ r) φ)) := by
    intro j fields rl krl cvC K Fs σC RC hrl hkrl hcC hK hFs hFl hTmK hrelF hev
    have hkm := List.mem_of_getElem? hkrl
    have hrm := List.mem_of_getElem? hrl
    -- the stored rule: its telescope, its fields, the constructor's codomain
    obtain ⟨hkc, hknf, hcorr⟩ := hruleS j rl krl hrl hkrl
    obtain ⟨bs, b, hrhs, hbsl, hbsd⟩ := hruleT krl hkm
    obtain ⟨cvC', fbs, bs', Cc, b', hcC', hcl, hdef, hcty, hfbl, hrhs', hbsl', hflds'⟩ :=
      hflds krl hkm
    rw [hcC] at hcC'
    simp only [Option.some.injEq, ConstantInfo.ctorInfo.injEq] at hcC'
    obtain ⟨rfl, -, -⟩ := hcC'
    obtain ⟨rfl, rfl⟩ := lamTele_inj bs bs' b b' (by omega) (hrhs.symm.trans hrhs')
    obtain ⟨cvC'', nF'', hfC'', -, -, hargs0⟩ := hctors krl hkm
    rw [hcC] at hfC''
    simp only [Option.some.injEq, ConstantInfo.ctorInfo.injEq] at hfC''
    obtain ⟨rfl, -, rfl⟩ := hfC''
    have hpbC : (piBody krl.nfields cvC.type).instantiateLevelParams cvC.levelParams ls0 = Cc := by
      rw [← piBody_inst, hcty, ← hfbl, piBody_piTele]
    have hcod : Cc.getAppArgs = [] := by
      rw [← hpbC, getAppArgs_inst]
      apply List.eq_nil_of_length_eq_zero
      rw [List.length_map]
      simp only [Nat.zero_add] at hargs0
      omega
    -- ι and β
    have hTm' : As[nmot + nmin]? = some (Fs.foldl app K) := by rw [hTm, hTmK]
    rw [hcty] at hFs
    obtain ⟨Hs, Y, hH, hY, heqY, hctx⟩ := noParamsIota M H.laws.iota_rule hfS hty htbs hkm hcC
      hrhs (by omega) hbsd hcty hfbl hcod hflds' hfit hAsl hpb hdomE hK hFs hFl hTm'
    -- the body runs
    obtain ⟨⟨t', ht', hnoc⟩, hrels⟩ := hbodies rl hrm
    have hden : DenotesIn M φ [] krl.rhs := fun ρ' _ => ⟨Hs, den_closed (hclosed krl hkm) hH⟩
    have hsites := ruleSites_ok H.laws hN hlv hrels hpwd hreg hden (hrefs j rl krl hrl hkrl)
    have hruns : Runs M κ Ok (lpsOf r) ls φ (idσ 0) [] rl.rhs krl.rhs :=
      runs_of_corr (termCorrS_of_termCorr hcorr (hclosed krl hkm)) hden hsites (fun d us hdu => by
        rw [evalConsts_peel ls _ rl.rhs t' ht'] at hdu
        have hm := evalConsts_mentions ls t' hdu
        rw [hnoc d] at hm
        cases hm) (fun A h => by rw [witDoms_of_termCorr hcorr] at h; cases h)
    rw [hrhs] at hruns
    have hpeel : IxCC.Src.peelLams bs.length rl.rhs = some t' := by
      rw [show bs.length = 0 + nmot + nmin + rl.fields by omega]; exact ht'
    have hrunsB := runs_peel bs hruns hpeel
    -- SrcEval: the body, in the slots of the arguments before the major and the fields
    have hslen : (args.take (nmot + nmin) ++ fields).length = bs.length := by
      rw [List.length_append, ← relSlots_length hrelF, hFl]; simp; omega
    have hev' := hev t' (by rw [hslen]; exact hpeel)
    have henv : RelEnv M p κ lpsOf S Ok φ (args.take (nmot + nmin) ++ fields).reverse
        (idσ (0 + bs.length)) (pushAll (As.take (nmot + nmin) ++ Fs) ρ) := by
      rw [Nat.zero_add, ← hslen]
      exact relEnv_pushAll (relSlots_append (relSlots_take (nmot + nmin) hargs) hrelF)
    have hcs : ConstsIn S t' := fun c hc => by rw [hnoc c] at hc; cases hc
    obtain ⟨X', hX', hrelX⟩ := ih.eval (lpsOf r) ls φ _ _ t' b hrunsB _ _ v hcs hlv henv
      (by simpa using hctx) hev'
    rw [heqY]
    rwa [Denotes_functional hX' hY] at hrelX
  cases major with
  | lit n =>
    -- a literal major only at the pinned `Nat`: rule `Nat.zero` or `Nat.succ`
    simp only at hsel2
    split at hsel2
    · rename_i hnatc
      obtain ⟨-, hrow⟩ := hnat (by simpa using hnatc)
      have hlenR : rules.length = 2 := by
        have := congrArg List.length hrow
        simpa using this
      have hrowAt : ∀ (i : Nat) (rl : IxCC.Src.Rule), rules[i]? = some rl →
          ([((natZeroName : KKey), 0), ((natSuccName : KKey), 1)])[i]? =
            some (κ rl.ctor, rl.fields) := by
        intro i rl hi
        rw [← hrow, List.getElem?_map, hi]
        rfl
      have hkrAt : ∀ (i : Nat) (rl : IxCC.Src.Rule), rules[i]? = some rl →
          ∃ krl, krules[i]? = some krl ∧ krl.ctor = κ rl.ctor ∧ krl.nfields = rl.fields := by
        intro i rl hi
        obtain ⟨krl, hk⟩ : ∃ krl, krules[i]? = some krl :=
          ⟨_, List.getElem?_eq_getElem (by rw [← hlenS]; exact (List.getElem?_eq_some_iff.mp hi).1)⟩
        obtain ⟨h1, h2, -⟩ := hruleS i rl krl hi hk
        exact ⟨krl, hk, h1.symm, h2.symm⟩
      have hF0 := natFacts M hN φ
      have hTe := relV_lit_eq H.laws hN φ hmajR
      obtain ⟨cvZ, hfZ, -, -, hlZ⟩ := hN.zero
      obtain ⟨cvS, hfSu, -, htS, hlS⟩ := hN.succ
      -- the major domain's levels: none (`Nat.zero` has no level parameter)
      obtain ⟨rl0, hrl0⟩ : ∃ rl, rules[0]? = some rl := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have h0 := hrowAt 0 rl0 hrl0
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h0
      obtain ⟨krl0, hkrl0, hk0c, hk0f⟩ := hkrAt 0 rl0 hrl0
      rw [← h0.1] at hk0c
      rw [← h0.2] at hk0f
      have hls0 : ls0 = [] := by
        obtain ⟨cvC'', nF'', hfC'', hlsC, -, -⟩ := hctors krl0 (List.mem_of_getElem? hkrl0)
        rw [hk0c, hfZ] at hfC''
        simp only [Option.some.injEq, ConstantInfo.ctorInfo.injEq] at hfC''
        obtain ⟨rfl, -, -⟩ := hfC''
        rw [hlZ] at hlsC
        exact List.eq_nil_of_length_eq_zero hlsC.symm
      cases n with
      | zero =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsel2
        obtain ⟨rfl, rfl⟩ := hsel2
        rw [hrl0] at hrest
        simp only [hrP] at hrest
        exact tail 0 [] rl0 krl0 cvZ (M.cval natZeroName φ) [] ρ
          (cvZ.type.instantiateLevelParams cvZ.levelParams ls0) hrl0 hkrl0
          (by rw [hk0c, hk0f]; exact hfZ)
          (by rw [hk0c, hls0]; exact (den_const0 hfZ hlZ).mpr rfl) .nil (by rw [hk0f]; rfl)
          (by rw [hTe]; rfl) .nil (fun t' ht => by rw [ht] at hrest; exact hrest)
      | succ n =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hsel2
        obtain ⟨rfl, rfl⟩ := hsel2
        obtain ⟨rl1, hrl1⟩ : ∃ rl, rules[1]? = some rl :=
          ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have h1 := hrowAt 1 rl1 hrl1
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          Prod.mk.injEq] at h1
        obtain ⟨krl1, hkrl1, hk1c, hk1f⟩ := hkrAt 1 rl1 hrl1
        rw [← h1.1] at hk1c
        rw [← h1.2] at hk1f
        rw [hrl1] at hrest
        simp only [hrP] at hrest
        have hi0 := inst_self ([] : List LevelParam) cvS.type
        simp only [List.map_nil] at hi0
        exact tail 1 [.val (.lit n)] rl1 krl1 cvS (M.cval natSuccName φ) [litSet M φ n]
          (push (litSet M φ n) ρ) natK hrl1 hkrl1
          (by rw [hk1c, hk1f]; exact hfSu)
          (by rw [hk1c, hls0]; exact (den_const0 hfSu hlS).mpr rfl)
          (by rw [hls0, hlS, hi0, htS]; exact .cons ((hF0.natD _ _).mpr rfl) (lit_mem M hF0 n) .nil)
          (by rw [hk1f]; rfl) (by rw [hTe]; rfl) (.cons (.val (relV_lit_intro hN φ n)) .nil)
          (fun t' ht => by rw [ht] at hrest; exact hrest)
    · simp at hsel2
  | con c lsc ps fs =>
    simp only at hsel2
    cases hdc : p.decl? c with
    | none => simp [hdc] at hsel2
    | some dc =>
      cases dc with
      | ctor sfc lvc indc cidx npc nfc tyc =>
        simp only [hdc] at hsel2
        split at hsel2
        · rename_i hcond
          simp only [Option.some.injEq, Prod.mk.injEq] at hsel2
          obtain ⟨rfl, rfl⟩ := hsel2
          simp only [Bool.and_eq_true, beq_iff_eq] at hcond
          obtain ⟨rfl, -⟩ := hcond
          cases hmajR with
          | @con _ _ _ _ ψ cvC' np'' nf'' Ps Fs ρc σc Rc hSc' _ hfc' hPl hFl _ hfs' hfitc =>
          obtain ⟨hnp0, rl, hrl, hkey, hnF⟩ := hctP c hSc' sfc lvc cidx npc nfc tyc hdc
          obtain ⟨cv, hfcv, _⟩ := H.faith.ctor c hSc' sfc lvc _ cidx npc nfc tyc hdc
          rw [hfcv] at hfc'
          simp only [Option.some.injEq, ConstantInfo.ctorInfo.injEq] at hfc'
          obtain ⟨rfl, rfl, rfl⟩ := hfc'
          subst hnp0
          obtain rfl : Ps = [] := List.eq_nil_of_length_eq_zero hPl
          -- the stored rule at the constructor's index
          obtain ⟨krl, hkrl⟩ : ∃ krl, krules[cidx]? = some krl := by
            have hlt : cidx < krules.length := by
              rw [← hlenS]; exact (List.getElem?_eq_some_iff.mp hrl).1
            exact ⟨_, List.getElem?_eq_getElem hlt⟩
          obtain ⟨hkc, hknf, -⟩ := hruleS cidx rl krl hrl hkrl
          have hkc' : krl.ctor = κ c := hkc.symm.trans hkey
          have hkm := List.mem_of_getElem? hkrl
          -- the constructor: closed and covered (`RecFields`), its codomain's head, its levels
          obtain ⟨cvF, -, -, -, -, hcF, hcl, hdef, -, -, -, -, -⟩ := hflds krl hkm
          rw [hkc', hfcv] at hcF
          simp only [Option.some.injEq, ConstantInfo.ctorInfo.injEq] at hcF
          obtain ⟨rfl, -, hnfk⟩ := hcF
          have hcC : env.find? krl.ctor = some (.ctorInfo cv 0 krl.nfields) := by
            rw [hkc', hfcv, hnfk]
          obtain ⟨cvH, nFH, hfH, hlsC, hhead, -⟩ := hctors krl hkm
          rw [hcC] at hfH
          simp only [Option.some.injEq, ConstantInfo.ctorInfo.injEq] at hfH
          obtain ⟨rfl, -, rfl⟩ := hfH
          have hfitc' : Fits M.cval env ψ ρc cv.type Fs σc Rc := by simpa using hfitc
          have hFlk : Fs.length = krl.nfields := by rw [hFl, hnfk]
          rw [hrl] at hrest
          simp only [hrP] at hrest
          by_cases hlp : cv.levelParams = []
          · -- no level parameter: the image is one set at every assignment
            have hls0 : ls0 = [] := by
              rw [hlp] at hlsC; exact List.eq_nil_of_length_eq_zero hlsC.symm
            obtain ⟨hK, σ', R', hFfit⟩ :=
              ctorFields_noLevels M H.laws hfcv hlp hcl (by rw [← hlp]; exact hdef) hfitc'
            have hi0 := inst_self ([] : List LevelParam) cv.type
            simp only [List.map_nil] at hi0
            exact tail cidx (fs.map .val) rl krl cv (M.cval (κ c) ψ) Fs σ' R' hrl hkrl hcC
              (by rw [hkc', hls0]; exact hK) (by rw [hlp, hls0, hi0]; exact hFfit) hFlk
              (by simp) (relSlots_of_relVs hfs') (fun t' ht => by rw [ht] at hrest; exact hrest)
          · -- level parameters: canonicity at the inductive, never a proposition
            have hnd : cv.levelParams.Nodup := by
              obtain ⟨ci, hci, hlps⟩ := H.faith.stored c hSc'
              rw [hfcv] at hci
              cases hci
              have := H.faith.nodup c hSc'
              rwa [← hlps] at this
            -- (the law; or no constructor with level parameters, `FundHyps.canon`)
            have hcc : CtorCanon M := H.canon.resolve_right fun hno =>
              hlp (recNoLevels_ctor (hno r hSr (.inr (by assumption))) hfS hkm hcC)
            obtain ⟨K, hK, heqK, σ', R', hFfit⟩ := ctorFields_canon M H.laws hcc hfcv hnd hcl hdef
              (by simpa [hnfk] using hhead) (neverProp_of_check hnp) hlsC hfitc' hFl hdomE hX
              (by simpa using hTmX)
            exact tail cidx (fs.map .val) rl krl cv K Fs σ' R' hrl hkrl hcC
              (by rw [hkc']; exact hK) hFfit hFlk (by simpa using heqK) (relSlots_of_relVs hfs')
              (fun t' ht => by rw [ht] at hrest; exact hrest)
        · simp at hsel2
      | _ => simp [hdc] at hsel2
  | _ => simp at hsel2

/-- F1, F3 at `Eq.rec`, F4, F5 and F6. -/
theorem fire_step (H : FundHyps M p κ lpsOf S Ok) {k : Nat}
    (ih : ∀ k' < k, AllP M p κ lpsOf S Ok k') (hfa : ForceAllP M p κ lpsOf S Ok k) :
    FireP M p κ lpsOf S Ok k := by
  intro h ls args v φ kk T ρ σ R As hrun hargs hh hfit hlen hlast
  have hN := H.natBasis
  cases hh with
  | @ctor c _ _ ci hSc hlv hfind hOkc =>
    -- F1
    rw [IxCC.Src.fire_ctor] at hrun
    cases hd : p.decl? c with
    | none => rw [hd] at hrun; exact absurd hrun (by simp)
    | some d =>
      rw [hd] at hrun
      cases d with
      | ctor sf lvls ind cidx np nf ty =>
        obtain ⟨cv, hcv, _⟩ := H.faith.ctor c hSc sf lvls ind cidx np nf ty hd
        rw [hfind] at hcv
        cases hcv
        have harity : args.length = np + nf := by rw [hlen]; simp [Program.headArity, hd]
        have hAsl : As.length = np + nf := by rw [relSlots_length hargs, harity]
        obtain ⟨fields, hfields, hres⟩ := Result.bind_eq_ok_iff.mp hrun
        have hrelF := hfa _ _ _ hfields (relSlots_drop np hargs)
        unfold IxCC.Src.ctorResult at hres
        split at hres
        · -- `Nat.zero` gives a literal
          rename_i hz
          have hk : κ c = natZeroName := H.faith.natZero c (beq_iff_eq.mp hz).symm
          obtain ⟨cvZ, hfZ, _, _, _⟩ := hN.zero
          have h0 := hfind
          rw [hk, hfZ] at h0
          cases h0
          rw [← ok_inj hres, List.eq_nil_of_length_eq_zero (by omega : As.length = 0), hk]
          exact relV_lit_intro hN φ 0
        · split at hres
          · -- `Nat.succ` on a literal gives a literal
            rename_i _ hs
            have hk : κ c = natSuccName := H.faith.natSucc c (beq_iff_eq.mp hs).symm
            obtain ⟨cvS, hfS, _, _, _⟩ := hN.succ
            have h1 := hfind
            rw [hk, hfS] at h1
            cases h1
            obtain ⟨A, rfl⟩ := List.length_eq_one_iff.mp (by omega : As.length = 1)
            obtain ⟨f1, rfl, hf1⟩ := relVs_single_right (by simpa using hrelF)
            cases f1 with
            | lit n =>
              simp only [Result.ok.injEq] at hres
              subst hres
              rw [relV_lit_eq H.laws hN φ hf1, hk]
              exact relV_lit_intro hN φ (n + 1)
            | _ => exact absurd hres (by simp)
          · -- any other constructor
            rw [← ok_inj hres]
            have hcon := RelV.con (M := M) (p := p) (κ := κ) (lpsOf := lpsOf) (S := S) (Ok := Ok)
              (ls := ls) (ps := args.take np) (fs := fields) (Ps := As.take np) (Fs := As.drop np)
              hSc hlv hfind (by rw [List.length_take, hAsl]; omega)
              (by rw [List.length_drop, hAsl]; omega) (relSlots_take np hargs) hrelF
              (by rw [List.take_append_drop]; exact hfit) (.inr hOkc)
            rwa [List.take_append_drop] at hcon
      | _ => exact absurd hrun (by simp)
  | @cases c _ _ ci hSc hlv hfind hOkc =>
    -- F5
    cases k with
    | zero => rw [IxCC.Src.fire_cases, later_zero] at hrun; exact absurd hrun (by simp)
    | succ k' =>
      rw [IxCC.Src.fire_cases, later_succ] at hrun
      cases hres : p.table.resolveOf c with
      | none => rw [hres] at hrun; exact absurd hrun (by simp)
      | some res =>
        cases res with
        | case r =>
          rw [hres] at hrun
          obtain ⟨hkind', -⟩ := H.faith.caseRec c r hSc hres
          cases hd : p.decl? r with
          | none => simp [hd] at hrun
          | some d =>
            cases d with
            | recr sf kk lvls np nmot nmin ni ind rules ty =>
              -- E0: at kind `empty` SrcEval traps, so the run returns no value
              have hkind : p.table.recKindOf r = some .ordinary := by
                rcases hkind' with hkind | hkind
                · exact hkind
                · simp [hd, hkind, IxCC.Src.RecKind.atLevels, IxCC.Src.recChosen, Result.bind]
                    at hrun
              simp only [hd, hkind, Option.map_some, atLevels_ordinary, IxCC.Src.recChosen] at hrun
              obtain ⟨⟨j, fields⟩, hsel, hrest⟩ := Result.bind_eq_ok_iff.mp hrun
              obtain ⟨major, hmaj, hsel'⟩ := Result.bind_eq_ok_iff.mp hsel
              obtain ⟨minor, hmin, happ⟩ := Result.bind_eq_ok_iff.mp hrest
              have harity : args.length = np + 1 + ni + 1 + nmin := by
                rw [hlen]; simp [Program.headArity, hres, hd]
              have hAsl : As.length = np + 1 + ni + 1 + nmin := by
                rw [relSlots_length hargs, harity]
              -- the major
              obtain ⟨sM, hsM⟩ : ∃ s, args[np + 1 + ni]? = some s :=
                ⟨_, List.getElem?_eq_getElem (by omega)⟩
              obtain ⟨Tm, hTm, hrelM⟩ := relSlots_get hargs hsM
              rw [List.getD_eq_getElem?_getD, hsM, Option.getD_some] at hmaj
              have hmajR := (ih k' (Nat.lt_succ_self k')).force _ _ _ hmaj hrelM
              -- F5's meaning
              obtain ⟨Mn, Ys, hMn, hYs, heq, hchain⟩ :=
                H.cases c r hSc hres hkind r sf kk lvls np nmot nmin ni ind rules ty hres hd ls φ _
                  ρ σ R As (.cases hSc hlv hfind hOkc) hfit hAsl hlast Tm major j fields hTm hmajR
                  (ofOption_eq_ok.mp hsel')
              -- the minor
              obtain ⟨sm, hsm, hrelm⟩ := relSlots_get' hargs hMn
              rw [List.getD_eq_getElem?_getD, hsm, Option.getD_some] at hmin
              have hminR := (ih k' (Nat.lt_succ_self k')).force _ _ _ hmin hrelm
              rw [heq]
              exact (ih k' (Nat.lt_succ_self k')).applyAll _ _ _ _ _ happ hminR hYs hchain
            | _ => simp [hd] at hrun
        | _ => rw [hres] at hrun; exact absurd hrun (by simp)
  | @recr r _ _ ci hSr hlv hfind =>
    -- F2–F4: the recursor's class is admitted (`RecFacts`); at `empty`, F4 traps
    cases k with
    | zero => rw [IxCC.Src.fire_recr, later_zero] at hrun; exact absurd hrun (by simp)
    | succ k' =>
      have hrun0 := hrun
      rw [IxCC.Src.fire_recr, later_succ] at hrun
      cases hd : p.decl? r with
      | none => simp [hd] at hrun
      | some d =>
        cases d with
        | recr sf kk' lvls np nmot nmin ni ind rules ty =>
          obtain ⟨cl, hcl, hadm⟩ :=
            H.faith.recs.cls r hSr sf kk' lvls np nmot nmin ni ind rules ty hd
          simp only [admittedClasses, List.mem_cons, List.not_mem_nil, or_false] at hadm
          rcases hadm with rfl | rfl | rfl | rfl
          · -- `empty`: the table's kind is `empty`, at every level, and F4 traps
            have hkind := recClassB_empty hcl
            simp [hd, hkind, IxCC.Src.RecKind.atLevels, IxCC.Src.recChosen, Result.bind] at hrun
          · -- `eqRec`: F3 at every level; the rule's body is the minor premise's slot
            obtain ⟨hκ, hkind, sf', kk'', lvls', ind', rl, ty', hd'⟩ := recClassB_eqRec hcl
            rw [hd] at hd'
            simp only [Option.some.injEq, IxCC.Src.Decl.recr.injEq] at hd'
            obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hd'
            obtain ⟨hEb, hB⟩ := H.faith.recs.eqRec r hSr hcl
            have hRb := H.faith.recs.eqRefl r hSr hcl
            obtain ⟨⟨_, _, _, np', nmot', nmin', ni', _, rules', _, cvr, krules, hdS, hfS, _, _, _,
              hruleS⟩⟩ := H.faith.recs.stored r hSr _ _ _ _ _ _ _ _ _ _ hd
            rw [hd] at hdS
            simp only [Option.some.injEq, IxCC.Src.Decl.recr.injEq] at hdS
            obtain ⟨-, -, -, rfl, rfl, rfl, rfl, -, rfl, -⟩ := hdS
            have hB' := hB
            obtain ⟨cvr0, krl0, hfr0, hty0, _, hrhs0⟩ := hB'
            rw [hκ, hfr0] at hfS
            injection hfS with hfS
            injection hfS with e1 _ _ e4
            subst e1 e4
            rw [hκ, hfr0] at hfind
            cases hfind
            obtain ⟨-, -, hcorr⟩ := hruleS 0 rl krl0 rfl rfl
            rw [hrhs0] at hcorr
            have hpeel := peelLams_eqRecRhs hcorr
            -- the six arguments, and SrcEval's F3: the minor premise's slot, forced
            have harity : args.length = 6 := by
              rw [hlen]; simp [Program.headArity, hd, IxCC.Src.Decl.recArity]
            have hAsl : As.length = 6 := by rw [relSlots_length hargs, harity]
            obtain ⟨s0, s1, s2, s3, s4, s5, rfl⟩ :
                ∃ s0 s1 s2 s3 s4 s5, args = [s0, s1, s2, s3, s4, s5] := by
              match args, harity with
              | [s0, s1, s2, s3, s4, s5], _ => exact ⟨s0, s1, s2, s3, s4, s5, rfl⟩
              | [], hl | [_], hl | [_, _], hl | [_, _, _], hl | [_, _, _, _], hl
              | [_, _, _, _, _], hl => simp only [List.length_cons, List.length_nil] at hl <;> omega
              | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, hl =>
                simp only [List.length_cons] at hl <;> omega
            have hrun' : IxCC.Src.force p k' s3 = .ok v := by
              simpa [hd, hkind, IxCC.Src.RecKind.atLevels, IxCC.Src.PropWhen.holds,
                IxCC.Src.recChosen, Result.bind, hpeel, IxCC.Src.eval_var] using hrun
            obtain ⟨X3, hX3, hrel3⟩ := relSlots_get (i := 3) hargs rfl
            have hv := (ih k' (Nat.lt_succ_self k')).force _ _ _ hrun' hrel3
            obtain ⟨Mn, hMn, heq⟩ := eqRec_iota M H.laws hEb hRb hB (by rwa [← hty0]) hAsl
            rw [hX3] at hMn
            cases hMn
            show RelV M p κ lpsOf S Ok v (As.foldl app (M.cval (κ r) φ))
            rw [hκ, heq]
            exact hv
          · -- `flat`: F2; the major is a field-less constructor of the recursor's inductive (the
            -- program side), and its rule's body is a variable, the slot of an argument before the
            -- major: `flatIota` (ι and β), the constructor's image moved to the major domain's
            -- levels without a law (no level parameter) or by canonicity
            obtain ⟨hkind, sf', kk'', lvls', nmot', nmin', ind', rules', ty', hd', hnp, hrules⟩ :=
              recClassB_flat hcl
            rw [hd] at hd'
            simp only [Option.some.injEq, IxCC.Src.Decl.recr.injEq] at hd'
            obtain ⟨-, -, -, rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := hd'
            obtain ⟨hTele, hProg, hCtors⟩ := H.faith.recs.flat r hSr hcl
            obtain ⟨⟨_, _, _, np', nmot'', nmin'', ni', _, rules'', _, cvr, krules, hdS, hfS, _, _,
              hlenS, hruleS⟩⟩ := H.faith.recs.stored r hSr _ _ _ _ _ _ _ _ _ _ hd
            rw [hd] at hdS
            simp only [Option.some.injEq, IxCC.Src.Decl.recr.injEq] at hdS
            obtain ⟨-, -, -, rfl, rfl, rfl, rfl, -, rfl, -⟩ := hdS
            have hmI : 0 + nmot + nmin + 0 = nmot + nmin := by omega
            have hrP : 0 + nmot + nmin = nmot + nmin := by omega
            rw [hmI, hrP] at hfS
            rw [hfS] at hfind
            cases hfind
            -- the rules' telescopes
            obtain ⟨cvr1, mI1, rP1, krules1, tbs, C, hf1, hty, htbs, hruleT⟩ := hTele
            rw [hfS] at hf1
            injection hf1 with hf1
            injection hf1 with e1 e2 e3 e4
            subst e1 e2 e3 e4
            -- the rules' constructors
            obtain ⟨_, _, _, np2, _, _, _, ind2, _, _, cvr2, mI2, rP2, krules2, dom, body, mb, ls,
              hd2, hf2, hpb, hdom, hctors⟩ := hCtors
            rw [hd] at hd2
            simp only [Option.some.injEq, IxCC.Src.Decl.recr.injEq] at hd2
            obtain ⟨-, -, -, rfl, -, -, -, rfl, -, -⟩ := hd2
            rw [hfS] at hf2
            injection hf2 with hf2
            injection hf2 with e1 e2 e3 e4
            subst e1 e2 e3 e4
            have hdomE : dom.getAppFn = .const (κ ind) ls := by rw [hdom, getAppFn_mkAppN]; rfl
            -- the program side
            obtain ⟨_, _, _, np3, _, _, _, ind3, rules3, _, hd3, hctP, hnat⟩ := hProg
            rw [hd] at hd3
            simp only [Option.some.injEq, IxCC.Src.Decl.recr.injEq] at hd3
            obtain ⟨-, -, -, rfl, -, -, -, rfl, rfl, -⟩ := hd3
            -- SrcEval's F2: the major, forced; the rule of its constructor
            have harity : args.length = nmot + nmin + 1 := by
              rw [hlen]; simp [Program.headArity, hd, IxCC.Src.Decl.recArity]
            have hAsl : As.length = nmot + nmin + 1 := by rw [relSlots_length hargs, harity]
            simp only [hd, hkind, Option.map_some, atLevels_ordinary, IxCC.Src.recChosen] at hrun
            obtain ⟨⟨j, fields⟩, hsel, hrest⟩ := Result.bind_eq_ok_iff.mp hrun
            obtain ⟨major, hmaj, hsel'⟩ := Result.bind_eq_ok_iff.mp hsel
            obtain ⟨sM, hsM⟩ : ∃ s, args[nmot + nmin]? = some s :=
              ⟨_, List.getElem?_eq_getElem (by omega)⟩
            obtain ⟨Tm, hTm, hrelM⟩ := relSlots_get hargs hsM
            rw [List.getD_eq_getElem?_getD, hmI, hsM, Option.getD_some] at hmaj
            have hmajR := (ih k' (Nat.lt_succ_self k')).force _ _ _ hmaj hrelM
            have hsel2 := ofOption_eq_ok.mp hsel'
            unfold Program.selectRule at hsel2
            cases major with
            | lit n =>
              -- a literal major only at the pinned `Nat`, whose recursor has a rule with a field
              simp only at hsel2
              split at hsel2
              · rename_i hnatc
                obtain ⟨-, hrow⟩ := hnat (by simpa using hnatc)
                have hfl : rules.map (·.fields) = [0, 1] := by
                  have h2 := congrArg (List.map Prod.snd) hrow
                  simp only [List.map_map, List.map_cons, List.map_nil] at h2
                  rw [← h2]
                  rfl
                have hmem : (1 : Nat) ∈ rules.map (·.fields) := by rw [hfl]; simp
                obtain ⟨rl, hrl, h1⟩ := List.mem_map.mp hmem
                have := (hrules rl hrl).1
                omega
              · simp at hsel2
            | con c lsc ps fs =>
              simp only at hsel2
              cases hdc : p.decl? c with
              | none => simp [hdc] at hsel2
              | some dc =>
                cases dc with
                | ctor sfc lvc indc cidx npc nfc tyc =>
                  simp only [hdc] at hsel2
                  split at hsel2
                  · rename_i hcond
                    simp only [Option.some.injEq, Prod.mk.injEq] at hsel2
                    obtain ⟨rfl, rfl⟩ := hsel2
                    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
                    obtain ⟨rfl, -⟩ := hcond
                    cases hmajR with
                    | @con _ _ _ _ ψ cvC' np'' nf'' Ps Fs ρc σc Rc hSc' _ hfc' hPl hFl _ hfs' _ =>
                    obtain ⟨hnp0, rl, hrl, hkey, hnF⟩ := hctP c hSc' sfc lvc cidx npc nfc tyc hdc
                    obtain ⟨cv, hfcv, _⟩ := H.faith.ctor c hSc' sfc lvc _ cidx npc nfc tyc hdc
                    rw [hfcv] at hfc'
                    simp only [Option.some.injEq, ConstantInfo.ctorInfo.injEq] at hfc'
                    obtain ⟨rfl, rfl, rfl⟩ := hfc'
                    obtain ⟨hf0, i, hpeel, hi⟩ := hrules rl (List.mem_of_getElem? hrl)
                    -- no parameter, no field
                    subst hnp0
                    have hnf0 : nfc = 0 := by rw [← hnF, hf0]
                    subst hnf0
                    obtain rfl : Ps = [] := List.eq_nil_of_length_eq_zero hPl
                    obtain rfl : Fs = [] := List.eq_nil_of_length_eq_zero hFl
                    obtain rfl : fs = [] := relVs_nil_right hfs'
                    -- the stored rule at the constructor's index, and its body, `.bvar i`
                    obtain ⟨krl, hkrl⟩ : ∃ krl, krules[cidx]? = some krl := by
                      have hlt : cidx < krules.length := by
                        rw [← hlenS]; exact (List.getElem?_eq_some_iff.mp hrl).1
                      exact ⟨_, List.getElem?_eq_getElem hlt⟩
                    obtain ⟨hkc, hknf, hcorr⟩ := hruleS cidx rl krl hrl hkrl
                    obtain ⟨bs, b, hrhs, hbsl, hbsd⟩ := hruleT krl (List.mem_of_getElem? hkrl)
                    rw [← hknf, hf0, Nat.add_zero] at hbsl
                    rw [List.take_of_length_le (by omega)] at hbsd
                    rw [hrhs] at hcorr
                    obtain ⟨t', hpt, hct⟩ := peelLams_corr bs hcorr
                    rw [hbsl, hpeel] at hpt
                    cases hpt
                    cases hct
                    -- the constructor, as ι reads it
                    have hkc' : krl.ctor = κ c := hkc.symm.trans hkey
                    obtain ⟨cvC, nF, hfC, hlsC, hhead, hargs0⟩ :=
                      hctors krl (List.mem_of_getElem? hkrl)
                    rw [hkc', hfcv] at hfC
                    simp only [Option.some.injEq, ConstantInfo.ctorInfo.injEq] at hfC
                    obtain ⟨rfl, -, rfl⟩ := hfC
                    have e00 : piBody (0 + 0) cv.type = cv.type := by simp [piBody]
                    rw [e00] at hhead hargs0
                    have hcod : cv.type.getAppArgs = [] := List.eq_nil_of_length_eq_zero (by omega)
                    -- ι and β; the major's set is the constructor's image at the major domain's
                    -- levels: without canonicity where the constructor has no level parameter
                    -- (`flatIota_noLevels`: ι and level-parameter irrelevance alone), by
                    -- canonicity at the inductive, never a proposition, where it has some
                    have hcC : env.find? krl.ctor = some (.ctorInfo cv 0 0) := by
                      rw [hkc']; exact hfcv
                    have hmaj' : As[nmot + nmin]? = some (M.cval krl.ctor ψ) := by
                      rw [hkc']; simpa using hTm
                    obtain ⟨X, hX, heq⟩ : ∃ X, (As.take (nmot + nmin)).reverse[i]? = some X ∧
                        As.foldl app (M.cval (κ r) φ) = X := by
                      by_cases hlp : cv.levelParams = []
                      · exact flatIota_noLevels M H.laws.iota_rule H.laws.cval_params hfS hty htbs
                          (List.mem_of_getElem? hkrl) hcC hlp hcod hrhs hbsd hi hfit
                          (by rw [hAsl]) hpb hdomE hlsC hmaj'
                      · have hnd : cv.levelParams.Nodup := by
                          obtain ⟨ci, hci, hlps⟩ := H.faith.stored c hSc'
                          rw [hfcv] at hci
                          cases hci
                          have := H.faith.nodup c hSc'
                          rwa [← hlps] at this
                        have hcc : CtorCanon M := H.canon.resolve_right fun hno =>
                          hlp (recNoLevels_ctor (hno r hSr (.inl hcl)) hfS
                            (List.mem_of_getElem? hkrl) hcC)
                        exact flatIota M H.laws.iota_rule hfS hty htbs (List.mem_of_getElem? hkrl)
                          hcC hcod hrhs hbsd hi hfit (by rw [hAsl]) hpb hdomE
                          (fun _ _ hX hm => by
                            rw [hkc'] at hm ⊢
                            exact ctorImage_canon M H.laws hcc hfcv hnd hhead
                              (neverProp_of_check hnp) hlsC hdomE hX hm)
                          hmaj'
                    -- SrcEval: the body, `.var i`, in the slots of the first arguments reversed
                    have hslots : args.take (0 + nmot + nmin) ++ ([] : List Value).map Slot.val =
                        args.take (nmot + nmin) := by simp
                    rw [hrl] at hrest
                    simp only [hslots] at hrest
                    have hlenT : (args.take (nmot + nmin)).length = nmot + nmin := by simp; omega
                    rw [hlenT, hpeel] at hrest
                    simp only [IxCC.Src.eval_var] at hrest
                    cases hsi : (args.take (nmot + nmin)).reverse[i]? with
                    | none => rw [hsi] at hrest; simp at hrest
                    | some s =>
                      rw [hsi] at hrest
                      simp only at hrest
                      obtain ⟨X', hX', hrelS⟩ :=
                        relSlots_get (relSlots_reverse (relSlots_take (nmot + nmin) hargs)) hsi
                      rw [hX] at hX'
                      cases hX'
                      have hv := (ih k' (Nat.lt_succ_self k')).force _ _ _ hrest hrelS
                      show RelV M p κ lpsOf S Ok v (As.foldl app (M.cval (κ r) φ))
                      rw [heq]
                      exact hv
                  · simp at hsel2
                | _ => simp [hdc] at hsel2
            | _ => simp at hsel2
          · -- `noParams` (part E): F2, the rule body evaluated; `fire_noParams`
            exact fire_noParams H (ih k' (Nat.lt_succ_self k')) hcl hrun0 hargs
              (.recr hSr hlv hfind) hfit hlen hlast
        | _ => simp [hd] at hrun
  | @prim op _ _ ci hfind hlp _ =>
    -- F6
    rw [IxCC.Src.fire_prim] at hrun
    obtain ⟨vs, hvs, hpv⟩ := Result.bind_eq_ok_iff.mp hrun
    have hrelV := hfa _ _ _ hvs hargs
    unfold IxCC.Src.primValue at hpv
    cases hla : IxCC.Src.litArgs vs with
    | none => rw [hla] at hpv; exact absurd hpv (by simp)
    | some ns =>
      rw [hla] at hpv
      simp only at hpv
      obtain rfl := litArgs_some hla
      have hAs := relVs_lits H.laws hN φ hrelV
      have hF := natFacts M hN φ
      cases hev : op.evalLits ns with
      | none => rw [hev] at hpv; exact absurd hpv (by simp)
      | some res =>
        rw [hev] at hpv
        -- the application's denotation, read through `nat_accel`
        have hacc : ∀ ρ0 : BVarIdx → V,
            Denotes M.cval env φ ρ0 (primResultE res) (As.foldl app (M.cval (primKey op) φ)) := by
          intro ρ0
          rcases evalLits_some hev with ⟨a, rfl, h1, rfl⟩ | ⟨a, b, rfl, h2, rfl⟩
          · have hd : Denotes M.cval env φ ρ0 (primApp op a 0)
                (As.foldl app (M.cval (primKey op) φ)) := by
              rw [hAs]
              have e1 : primApp (md := .anon) op a 0 = .app (.const (primKey op) []) (litE a) := by
                simp [primApp, h1]
              rw [e1]
              exact .app ((den_const0 hfind hlp).mpr rfl) ((lit_den M hF ρ0 a _).mpr rfl)
            exact H.laws.nat_accel op a 0 φ ρ0 _ (fun _ => rfl) hd
          · have hd : Denotes M.cval env φ ρ0 (primApp op a b)
                (As.foldl app (M.cval (primKey op) φ)) := by
              rw [hAs]
              have e2 : primApp (md := .anon) op a b =
                  .app (.app (.const (primKey op) []) (litE a)) (litE b) := by
                simp [primApp, h2]
              rw [e2]
              exact .app (.app ((den_const0 hfind hlp).mpr rfl) ((lit_den M hF ρ0 a _).mpr rfl))
                ((lit_den M hF ρ0 b _).mpr rfl)
            exact H.laws.nat_accel op a b φ ρ0 _ (fun h => by omega) hd
        cases res with
        | nat n =>
          simp only [Result.ok.injEq] at hpv
          subst hpv
          exact .lit (hacc (fun _ => empty))
        | bool b =>
          simp only [Program.boolValue] at hpv
          cases hbc : (if b then p.known.boolTrue else p.known.boolFalse) with
          | none => rw [hbc] at hpv; exact absurd hpv (by simp)
          | some c =>
            rw [hbc] at hpv
            simp only [Result.ok.injEq] at hpv
            subst hpv
            obtain ⟨hSc, hkc, cv, hfc, hlc⟩ := H.faith.bool b c hbc
            obtain ⟨ci', hfc', hlps⟩ := H.faith.stored c hSc
            rw [hfc] at hfc'
            cases hfc'
            have hres : primResultE (md := .anon) (.bool b) = .const (κ c) [] := by
              rw [hkc]; cases b <;> rfl
            have hX := hacc (fun _ => empty)
            rw [hres] at hX
            rw [(den_const0 hfc hlc).mp hX]
            have hl0 : lpsOf c = [] := hlps.symm.trans hlc
            have hlv0 : LvAt φ (lpsOf c) [] := by rw [hl0]; intro i q h; simp at h
            exact RelV.con (M := M) (p := p) (κ := κ) (lpsOf := lpsOf) (S := S) (Ok := Ok) (ls := [])
              (ps := []) (fs := []) (Ps := []) (Fs := []) (ρ := ρ) hSc hlv0 hfc rfl rfl .nil .nil
              .nil (.inl hl0)

theorem headValue_step {k : Nat} (hfire : FireP M p κ lpsOf S Ok k) :
    HeadValueP M p κ lpsOf S Ok k := by
  intro h ls v φ kk T hrun hh
  rw [IxCC.Src.headValue_eq] at hrun
  split at hrun
  · rename_i h0
    exact hfire h ls [] v φ kk T (fun _ => empty) (fun _ => empty) T [] hrun .nil hh .nil
      (by simp only [List.length_nil]; exact (beq_iff_eq.mp h0).symm) (lastSiteOk_nil _)
  · rw [← ok_inj hrun]
    exact .pap (ρ := fun _ => empty) hh .nil .nil

/-- A1 and A2. -/
theorem apply_step (H : FundHyps M p κ lpsOf S Ok) {k : Nat}
    (ih : ∀ k' < k, AllP M p κ lpsOf S Ok k') (hfire : FireP M p κ lpsOf S Ok k) :
    ApplyP M p κ lpsOf S Ok k := by
  intro f s w X Y v A B hrun hf hs hv hX hY
  cases f with
  | clo b d body ρ' ls' =>
    rw [IxCC.Src.apply_clo] at hrun
    split at hrun
    · cases k with
      | zero => exact absurd hrun (by simp)
      | succ k' =>
        rw [later_succ] at hrun
        obtain ⟨φ, lps, Γ, σ, ρk, Ak, Bk, Z, hlv, henv, hctx, hruns, hcs, hZ, hXY⟩ :=
          apply_clo hf hs hv hX hY
        obtain ⟨Z', hZ', hrel⟩ :=
          (ih k' (Nat.lt_succ_self k')).eval _ _ _ _ _ _ _ hruns _ _ _ hcs hlv henv hctx hrun
        rw [hXY, Denotes_functional hZ hZ']
        exact hrel
    · exact absurd hrun (by simp)
  | pap h ls' args =>
    rw [IxCC.Src.apply_pap] at hrun
    have htele : args.length < p.headArity h → ∀ (φ : LevelParam → Nat) (kk : KKey) (T : KExpr)
        (ρ σ : BVarIdx → V) (R : KExpr) (As : List V), HeadAt M p κ lpsOf S Ok h ls' φ kk T →
        Fits M.cval env φ ρ T As σ R → As.length = args.length → ∃ D Bk m, R = .forallE D Bk m := by
      intro hlt φ kk T ρ σ R As hh hfit hl
      exact fits_pi_of_lt hfit (by have := head_tele H hh; omega)
    split at hrun
    · rename_i heq
      have hl1 : args.length + 1 = p.headArity h := by simpa using heq
      obtain ⟨φ, kk, T, As, ρ, σ, R, hh, hrel, hfit, hXe, hXY⟩ :=
        apply_pap hf hs hv hX hY (htele (by omega))
      rw [hXY]
      exact hfire h ls' (args ++ [s]) w φ kk T ρ σ R (As ++ [Y]) hrun hrel hh hfit
        (by simpa using hl1) (lastSiteOk_snoc hv (by rw [← hXe]; exact hX) hY)
    · split at hrun
      · rename_i _ hlt'
        have hl1 : args.length + 1 < p.headArity h := by simpa using hlt'
        obtain ⟨φ, kk, T, As, ρ, σ, R, hh, hrel, hfit, _, hXY⟩ :=
          apply_pap hf hs hv hX hY (htele (by omega))
        rw [← ok_inj hrun, hXY]
        exact .pap hh hrel hfit
      · exact absurd hrun (by simp)
  | _ =>
    rw [IxCC.Src.apply_other p k _ s (by intros; simp) (by intros; simp)] at hrun
    exact absurd hrun (by simp)

theorem applyAll_step {k : Nat} (ha : ApplyP M p κ lpsOf S Ok k) :
    ApplyAllP M p κ lpsOf S Ok k := by
  intro f ss
  induction ss generalizing f with
  | nil =>
    intro w X Ys hrun hf hss _
    rw [IxCC.Src.applyAll_nil] at hrun
    cases hss
    rw [← ok_inj hrun]
    exact hf
  | cons s ss ih =>
    intro w X Ys hrun hf hss hch
    cases hss with
    | @cons _ _ X1 Xs hs hss' =>
      cases hch with
      | cons hv hX hy hch' =>
        rw [IxCC.Src.applyAll_cons] at hrun
        obtain ⟨f', hf', hrest⟩ := Result.bind_eq_ok_iff.mp hrun
        exact ih f' w (app X X1) Xs hrest (ha _ _ _ _ _ _ _ _ hf' hf hs hv hX hy) hss' hch'

/-- E8: δ, `eqn`, and the special heads. -/
theorem evalConst_step (H : FundHyps M p κ lpsOf S Ok) {k : Nat}
    (ih : ∀ k' < k, AllP M p κ lpsOf S Ok k') (hhv : HeadValueP M p κ lpsOf S Ok k) :
    EvalConstP M p κ lpsOf S Ok k := by
  intro ls c v φ hrun hSc hOk hlv
  obtain ⟨ci, hfind, _⟩ := H.faith.stored c hSc
  rw [IxCC.Src.evalConst_eq] at hrun
  cases hres : p.table.resolveOf c with
  | some res =>
    rw [hres] at hrun
    cases res with
    | prim op =>
      obtain ⟨hk, ci', hf', hlp', har'⟩ := H.faith.prim c op hSc hres
      rw [hk]
      exact hhv _ _ _ φ _ _ hrun (.prim hf' hlp' har')
    | csimp g us thm => exact absurd hres (H.faith.noCsimp c g us thm hSc)
    | word w op thm => exact absurd hres (H.faith.noWord c w op thm hSc)
    | eqn thm body =>
      obtain ⟨e, hcomp, hrunsE⟩ := H.eqn c thm body hSc hres
      cases k with
      | zero => exact absurd hrun (by simp)
      | succ k' =>
        simp only [later_succ] at hrun
        obtain ⟨X, hX, hrel⟩ := (ih k' (Nat.lt_succ_self k')).eval _ _ _ _ _ _ _
          (hrunsE ls φ hOk hlv) [] (fun _ => empty) v (H.faith.eqnClosed c thm body hSc hres) hlv
          .nil .nil hrun
        rw [hcomp φ _ X hX]
        exact hrel
    | case r => exact hhv _ _ _ φ _ _ hrun (.cases hSc hlv hfind hOk)
  | none =>
    rw [hres] at hrun
    cases hd : p.decl? c with
    | none => rw [hd] at hrun; exact absurd hrun (by simp)
    | some d =>
      rw [hd] at hrun
      cases d with
      | ctor sf lvls ind cidx np nf ty => exact hhv _ _ _ φ _ _ hrun (.ctor hSc hlv hfind hOk)
      | recr sf kk lvls np nmot nmin ni ind rules ty =>
        exact hhv _ _ _ φ _ _ hrun (.recr hSc hlv hfind)
      | quot qk lvls ty => exact absurd hd (H.faith.noQuot c hSc qk lvls ty)
      | defn kind safety lvls ty v' =>
        cases kind with
        | defn =>
          cases safety with
          | safe =>
            obtain ⟨⟨cv, val, hint, hfv⟩, hcs⟩ := H.faith.defn c hSc hres lvls ty v' hd
            cases k with
            | zero => exact absurd hrun (by simp)
            | succ k' =>
              simp only [later_succ] at hrun
              have hruns := H.value c ls lvls ty v' cv val hint hSc hOk hres hd hfv φ hlv
              obtain ⟨X, hX, hrel⟩ := (ih k' (Nat.lt_succ_self k')).eval _ _ _ _ _ _ _ hruns []
                (fun _ => empty) v hcs hlv .nil .nil hrun
              have hδ := H.laws.defn_value cv val hint (find_mem hfv) φ (fun _ => empty)
              have hn : cv.name = κ c := find_name hfv
              rw [hn] at hδ
              rw [Denotes_functional hδ hX]
              exact hrel
          | _ => exact absurd hrun (by simp)
        | opaq =>
          cases safety with
          | safe => simp [H.faith.noOpaque c hSc] at hrun
          | _ => exact absurd hrun (by simp)
        | thm => exact absurd hrun (by simp)
      | _ => exact absurd hrun (by simp)

/-- E1–E8 by induction on `Runs`. -/
theorem eval_step (H : FundHyps M p κ lpsOf S Ok) {k : Nat}
    (hforce : ForceP M p κ lpsOf S Ok k) (happly : ApplyP M p κ lpsOf S Ok k)
    (hec : EvalConstP M p κ lpsOf S Ok k) : EvalP M p κ lpsOf S Ok k := by
  intro lps ls φ σ Γ t e hruns
  induction hruns with
  | @var σ Γ i e hσ =>
    intro ρ ρk v _ _ henv _ hrun
    rw [IxCC.Src.eval_var] at hrun
    obtain ⟨s, X, hs, hX, hrel⟩ := relEnv_get henv hσ
    rw [hs] at hrun
    exact ⟨X, hX, hforce s v X hrun hrel⟩
  | @letRel σ Γ c r ty v b e v' hr _ _ _ ihv ihb =>
    intro ρ ρk w hcs hlv henv hctx hrun
    rw [IxCC.Src.eval_letE] at hrun
    simp only [hr, Bool.false_eq_true, ↓reduceIte] at hrun
    obtain ⟨x, hx, hb⟩ := Result.bind_eq_ok_iff.mp hrun
    obtain ⟨Y, hY, hrelY⟩ := ihv ρ ρk x (mentions_let_val hcs) hlv henv hctx hx
    exact ihb (.val x :: ρ) ρk w (mentions_let_body hcs) hlv (.some (.val hrelY) hY henv) hctx hb
  | @letIrr σ Γ c r ty v b e v' hr _ htc hdv _ ihb =>
    intro ρ ρk w hcs hlv henv hctx hrun
    rw [IxCC.Src.eval_letE] at hrun
    simp only [hr, ↓reduceIte] at hrun
    obtain ⟨Y, hY⟩ := hdv ρk hctx
    exact ihb _ ρk w (mentions_let_body hcs) hlv (.some (.val (.irr hlv henv htc hY)) hY henv)
      hctx hrun
  | @letDead σ Γ c r ty v b e _ _ ihb =>
    -- the value's evaluation, if any, is discarded: the slot is related to nothing
    intro ρ ρk w hcs hlv henv hctx hrun
    rw [IxCC.Src.eval_letE] at hrun
    split at hrun
    · exact ihb _ ρk w (mentions_let_body hcs) hlv (.none henv) hctx hrun
    · obtain ⟨x, _, hb⟩ := Result.bind_eq_ok_iff.mp hrun
      exact ihb _ ρk w (mentions_let_body hcs) hlv (.none henv) hctx hb
  | @letClo σ Γ c r ty v bz d body A b' v' mb hsub _ hiv hlam ihv _ =>
    -- step C, the closure-capture shape: SrcEval evaluates the value, then returns the closure;
    -- its environment is related at every member of the λ's domain, where the value's run is
    -- related against the lifted copy (in the λ's context) and the copy denotes
    intro ρ ρk w hcs hlv henv hctx hrun
    rw [IxCC.Src.eval_letE] at hrun
    have hden : DenotesIn M φ Γ (.lam A b' mb) := by
      cases hlam with
      | lam _ _ hd => exact hd
    obtain ⟨X, hX⟩ := hden ρk hctx
    have hctx' : ∀ (XA x : V), Denotes M.cval env φ ρk A XA → x ∈ˢ XA →
        CtxSat M φ (A :: Γ) (push x ρk) := fun XA x hA hx =>
      .cons (by rw [push_tail]; exact hctx) (by rw [push_tail]; exact hA) hx
    have hdown : ∀ (x Y : V), Denotes M.cval env φ (push x ρk) (v'.liftLooseBVars 1 0) Y →
        Denotes M.cval env φ ρk v' Y := fun x Y h => by
      rw [den_lift 1 v' 0 (push x ρk) Y, skipEnv_push_one] at h
      exact h
    have hcs' : ConstsIn S (.lam bz d body) := mentions_let_body hcs
    cases hr : r.irrAt ls with
    | false =>
      simp only [hr, Bool.false_eq_true, ↓reduceIte] at hrun
      obtain ⟨y, hy, hb⟩ := Result.bind_eq_ok_iff.mp hrun
      rw [IxCC.Src.eval_lam] at hb
      rw [← ok_inj hb]
      refine ⟨X, hX, .clo hlv (fun XA x hA hx => ?_) hctx hlam hcs' hX⟩
      obtain ⟨Y, hY, hrelY⟩ := ihv hr ρ (push x ρk) y (mentions_let_val hcs) hlv
        (relEnv_liftAll x henv) (hctx' XA x hA hx) hy
      exact .some (.val hrelY) (hdown x Y hY) henv
    | true =>
      simp only [hr, ↓reduceIte] at hrun
      rw [IxCC.Src.eval_lam] at hrun
      rw [← ok_inj hrun]
      refine ⟨X, hX, .clo hlv (fun XA x hA hx => ?_) hctx hlam hcs' hX⟩
      obtain ⟨Y, hY⟩ := denotesIn_of_subAt0 hsub (denotesIn_lam_body hden) _ (hctx' XA x hA hx)
      exact .some (.val (.irr hlv (relEnv_liftAll x henv) (hiv hr) hY)) (hdown x Y hY) henv
  | @letWit σ Γ c r ty v b e v' Δ _ hext _ hiv _ ihv ihb =>
    -- the witness shape: the environment extended past the path's λs (their domains inhabited);
    -- there the value's run is related against the lifted copy, whose denotation is the copy's
    intro ρ ρk w hcs hlv henv hctx hrun
    rw [IxCC.Src.eval_letE] at hrun
    obtain ⟨ρ', hctx', hk⟩ := hext ρk hctx
    have henv' := relEnv_liftN hk henv
    have hdown : ∀ Y, Denotes M.cval env φ ρ' (v'.liftLooseBVars Δ.length 0) Y →
        Denotes M.cval env φ ρk v' Y := fun Y h => by
      have hsk : skipEnv ρ' Δ.length 0 = ρk := funext fun i => by simp [skipEnv, hk]
      rw [den_lift Δ.length v' 0 ρ' Y, hsk] at h
      exact h
    cases hr : r.irrAt ls with
    | false =>
      simp only [hr, Bool.false_eq_true, ↓reduceIte] at hrun
      obtain ⟨x, hx, hb⟩ := Result.bind_eq_ok_iff.mp hrun
      obtain ⟨Y, hY, hrelY⟩ := ihv hr ρ ρ' x (mentions_let_val hcs) hlv henv' hctx' hx
      exact ihb (.val x :: ρ) ρk w (mentions_let_body hcs) hlv
        (.some (.val hrelY) (hdown Y hY) henv) hctx hb
    | true =>
      simp only [hr, ↓reduceIte] at hrun
      obtain ⟨htc, hdv⟩ := hiv hr
      obtain ⟨Y, hY⟩ := hdv ρ' hctx'
      exact ihb _ ρk w (mentions_let_body hcs) hlv
        (.some (.val (.irr hlv henv' htc hY)) (hdown Y hY) henv) hctx hrun
  | @sort σ Γ u l hu =>
    intro ρ ρk v _ hlv henv _ hrun
    rw [IxCC.Src.eval_sort] at hrun
    rw [← ok_inj hrun]
    exact ⟨_, .sort, .irr hlv henv (.sort hu) .sort⟩
  | @const σ Γ c us ls' htc hok hden =>
    intro ρ ρk v hcs hlv _ hctx hrun
    rw [IxCC.Src.eval_const] at hrun
    have hSc := mentions_const hcs
    obtain ⟨ci, hfind, hlps⟩ := H.faith.stored c hSc
    obtain ⟨X, hX⟩ := hden ρk hctx
    cases hX with
    | const hf hlen =>
      rw [hfind] at hf
      cases hf
      cases htc with
      | const hlen' hcorr =>
        have hlv' : LvAt (Level.substFn φ (lpsOf c) ls') (lpsOf c) (us.map (IxCC.Src.evalUniv ls)) :=
          lvAt_inst hlv (H.faith.nodup c hSc) hlen' (hlen.trans (congrArg List.length hlps)) hcorr
        refine ⟨_, .const hfind hlen, ?_⟩
        rw [hlps]
        exact hec _ c v _ hrun hSc hok hlv'
  | @natLit σ Γ n hden =>
    intro ρ ρk v _ _ _ hctx hrun
    rw [IxCC.Src.eval_natLit] at hrun
    rw [← ok_inj hrun]
    obtain ⟨X, hX⟩ := hden ρk hctx
    exact ⟨X, hX, .lit hX⟩
  | @app σ Γ f a m r f' a' _ ha hirr hsite ihf iha =>
    intro ρ ρk v hcs hlv henv hctx hrun
    rw [IxCC.Src.eval_app] at hrun
    obtain ⟨fv, hfv, hrest⟩ := Result.bind_eq_ok_iff.mp hrun
    obtain ⟨F, hF, hrelF⟩ := ihf ρ ρk fv (mentions_app_left hcs) hlv henv hctx hfv
    obtain ⟨F', Xa, vv, A, B, hF', hXa, hvv, hFm, hXaA⟩ := hsite ρk hctx
    rw [Denotes_functional hF' hF] at hFm
    refine ⟨app F Xa, .app hF hXa, ?_⟩
    split at hrest
    · rename_i hi
      exact happly fv _ v F Xa vv A B hrest hrelF (.val (.irr hlv henv (hirr hi).1 hXa)) hvv hFm
        hXaA
    · rename_i hi
      have hi' : r.irrAt ls = false := by simpa using hi
      cases m with
      | strict =>
        obtain ⟨x, hx, hap⟩ := Result.bind_eq_ok_iff.mp hrest
        obtain ⟨Xa', hXa', hrelx⟩ := iha hi' ρ ρk x (mentions_app_right hcs) hlv henv hctx hx
        obtain rfl := Denotes_functional hXa hXa'
        exact happly fv _ v F Xa vv A B hap hrelF (.val hrelx) hvv hFm hXaA
      | byName =>
        exact happly fv _ v F Xa vv A B hrest hrelF
          (.name hlv henv hctx (ha hi') (mentions_app_right hcs) hXa) hvv hFm hXaA
  | @lam σ Γ b d body d' body' mb htc hbody hden _ =>
    intro ρ ρk v hcs hlv henv hctx hrun
    rw [IxCC.Src.eval_lam] at hrun
    rw [← ok_inj hrun]
    obtain ⟨X, hX⟩ := hden ρk hctx
    exact ⟨X, hX, .clo hlv (fun _ _ _ _ => henv) hctx (.lam htc hbody hden) hcs hX⟩
  | @pi σ Γ b r d c d' c' mb htc hden =>
    intro ρ ρk v _ hlv henv hctx hrun
    rw [IxCC.Src.eval_pi] at hrun
    rw [← ok_inj hrun]
    obtain ⟨X, hX⟩ := hden ρk hctx
    exact ⟨X, hX, .irr hlv henv htc hX⟩
  | @proj σ Γ s i e e' _ _ ihe =>
    intro ρ ρk v hcs hlv henv hctx hrun
    rw [IxCC.Src.eval_proj] at hrun
    obtain ⟨v', hv', hpf⟩ := Result.bind_eq_ok_iff.mp hrun
    obtain ⟨hSs, hcse⟩ := mentions_proj hcs
    obtain ⟨P, hP, hrel⟩ := ihe ρ ρk v' hcse hlv henv hctx hv'
    cases v' with
    | con c ls' ps fs =>
      simp only [Program.projectField] at hpf
      cases hds : p.decl? s with
      | none => rw [hds] at hpf; exact absurd hpf (by simp)
      | some d =>
        rw [hds] at hpf
        cases d with
        | induct sf lvls np ni ty ctors =>
          simp only at hpf
          split at hpf
          · rename_i hct
            have hctors := single_ctor hct
            subst hctors
            cases hrel with
            | @con _ _ _ _ φc cvC np' nf Ps Fs ρc σc Rc hSc _ hfc hPl hFl _ hfs hfit =>
              have hfi : fs[i]? = some v := ofOption_eq_ok.mp hpf
              obtain ⟨Y, hY, hrelY⟩ := relVs_get hfs hfi
              have hi : i < nf := by
                have := (List.getElem?_eq_some_iff.mp hY).1
                rw [← hFl]
                exact this
              obtain ⟨entry, hent, hctor⟩ :=
                H.faith.proj s hSs sf lvls np ni ty c hds cvC np' nf hfc i hi
              refine ⟨Y, ?_, hrelY⟩
              exact proj_con M H.laws hent (by rw [hctor]; exact hfc)
                (H.faith.projSort s hSs sf lvls np ni ty c hds hSc cvC np' nf hfc (by omega))
                hPl hFl hfit hY
                (by rw [hctor]; exact hP)
          · exact absurd hpf (by simp)
        | _ => exact absurd hpf (by simp)
    | _ => simp [Program.projectField] at hpf

/-- **The fundamental lemma**: all eight statements, at every clock. -/
theorem allP (H : FundHyps M p κ lpsOf S Ok) : ∀ k, AllP M p κ lpsOf S Ok k := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    have hforce := force_step ih
    have hforceAll := forceAll_step hforce
    have hfire := fire_step H ih hforceAll
    have hhv := headValue_step hfire
    have happly := apply_step H ih hfire
    have happlyAll := applyAll_step happly
    have hec := evalConst_step H ih hhv
    have heval := eval_step H hforce happly hec
    exact ⟨hforce, hforceAll, hfire, hhv, happly, happlyAll, hec, heval⟩

/-- The fundamental lemma's clause for constants: a constant of `S` that SrcEval unfolds at an
instance `Ok` admits returns a value related to the constant's denotation. -/
theorem fundamental_const (H : FundHyps M p κ lpsOf S Ok) {k : Nat} {ls : Levels} {c : CId}
    {v : Value} {φ : LevelParam → Nat} (hrun : IxCC.Src.evalConst p k ls c = .ok v) (hSc : S c)
    (hOk : Ok c ls) (hlv : LvAt φ (lpsOf c) ls) : RelV M p κ lpsOf S Ok v (M.cval (κ c) φ) :=
  (allP H k).evalConst ls c v φ hrun hSc hOk hlv

/-- The fundamental lemma's clause for terms. -/
theorem fundamental_term (H : FundHyps M p κ lpsOf S Ok) {k : Nat} {lps : List Nat} {ls : Levels}
    {φ : LevelParam → Nat} {σ : Sig} {Γ : List KExpr} {t : Term} {e : KExpr} {ρ : IxCC.Src.Env}
    {ρk : BVarIdx → V} {v : Value} (hruns : Runs M κ Ok lps ls φ σ Γ t e) (hcs : ConstsIn S t)
    (hlv : LvAt φ lps ls) (henv : RelEnv M p κ lpsOf S Ok φ ρ σ ρk) (hctx : CtxSat M φ Γ ρk)
    (hrun : IxCC.Src.eval p k ls ρ t = .ok v) :
    ∃ X, Denotes M.cval env φ ρk e X ∧ RelV M p κ lpsOf S Ok v X :=
  (allP H k).eval _ _ _ _ _ _ _ hruns ρ ρk v hcs hlv henv hctx hrun

end Fund

end IxCC.Grounding
