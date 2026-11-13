import IxCCGrounding.Case
import IxCCGrounding.Hyps

/-!
# The generic `case` lemma, SrcEval side (`IxCCGrounding.CaseFire`)

**`caseFires_of_shape`**: F5's meaning (`CaseFires`) at every `case` constant whose shape is checked
(`CaseStored`, `CaseProg`), from the model-side lemma (`caseIota`), the relation and canonicity
(`Laws.ctor_canon`).

SrcEval's F5 selects the rule by the major value, the model reads the major's set:

* **a literal major** (at the pinned `Nat`, `CaseProg`'s last clause): `0` is `Nat.zero` and
  `n + 1` is `Nat.succ` applied to `n`'s set, by the literal reading (`NatBasis`);
* **a constructor value** related by provenance (`RelV.con`): its set is the constructor's image
  at the assignment and environment it was built in, applied to sets that fit the constructor's
  stored type there. The stored type is closed and its level parameters cover it
  (`CaseWF.ctorRaw`), so the fit moves to the `case`'s environment and, instantiated at closed
  levels evaluating to that assignment, to the `case`'s assignment (`fits_agree`, `fits_inst`);
  canonicity then makes the image the constructor's at the `case`'s parameters and levels, the
  major lying in `casesOn`'s major domain. `caseIota` gives the rest.
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open IxCC.Src (Value Slot Term CId Program Levels)

universe w

/-- The level that evaluates to `n` at every assignment. -/
def lvlOf : Nat → Level
  | 0 => .zero
  | n + 1 => .succ (lvlOf n)

theorem eval_lvlOf (φ : LevelParam → Nat) : ∀ n, Level.eval φ (lvlOf n) = n
  | 0 => rfl
  | n + 1 => by simp [lvlOf, Level.eval, eval_lvlOf φ n]

theorem getAppFn_inst (ks : List LevelParam) (us : List Level) : ∀ e : KExpr,
    (e.instantiateLevelParams ks us).getAppFn = e.getAppFn.instantiateLevelParams ks us
  | .app f _ => by
    simp only [Expr.instantiateLevelParams, Expr.getAppFn]; exact getAppFn_inst ks us f
  | .bvar _ | .fvar .. | .sort _ | .const .. | .lam .. | .forallE .. | .letE .. | .lit _
  | .proj .. => rfl

theorem subst_go_params : ∀ (ks : List LevelParam) (us : List Level), ks.Nodup →
    ks.length = us.length → ks.map (Level.subst.go ks us) = us
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | k :: ks, u :: us, hnd, hl => by
    have hk : k ∉ ks := (List.nodup_cons.mp hnd).1
    rw [List.map_cons]
    have h1 : Level.subst.go (k :: ks) (u :: us) k = u := by simp [Level.subst.go]
    have h2 : ks.map (Level.subst.go (k :: ks) (u :: us)) = ks.map (Level.subst.go ks us) :=
      List.map_congr_left fun k' hk' => by
        have : k ≠ k' := fun e => hk (e ▸ hk')
        simp [Level.subst.go, this]
    rw [h1, h2, subst_go_params ks us (List.nodup_cons.mp hnd).2 (by simpa using hl)]

theorem subst_params {ks : List LevelParam} {us : List Level} (hnd : ks.Nodup)
    (hl : ks.length = us.length) : (ks.map Level.param).map (Level.subst ks us) = us := by
  rw [List.map_map]
  exact (List.map_congr_left fun k _ => rfl).trans (subst_go_params ks us hnd hl)

theorem get_of_map_pair {l : List CtorShape} {i : Nat} {k : KKey} {n : Nat}
    (h : (l.map fun cs => (cs.key, cs.nF))[i]? = some (k, n)) :
    ∃ cs, l[i]? = some cs ∧ cs.key = k ∧ cs.nF = n := by
  rw [List.getElem?_map] at h
  cases hl : l[i]? with
  | none => rw [hl] at h; cases h
  | some cs =>
    rw [hl] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨cs, rfl, h.1, h.2⟩

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv} {φ : LevelParam → Nat}

theorem fits_piBody {cval : KKey → (LevelParam → Nat) → V} {ρ σ : BVarIdx → V} {T R : KExpr}
    {xs : List V} (h : Fits cval env φ ρ T xs σ R) : R = piBody xs.length T := by
  induction h with
  | @nil _ T => cases T <;> rfl
  | cons _ _ _ ih => simpa [piBody] using ih

/-- **`casesOn`'s major domain**, read after the parameters and the motive, holds the major, and
its arguments denote the parameters. -/
theorem major_dom {cval : KKey → (LevelParam → Nat) → V} {kc kr : KKey} {sh : CaseShape}
    (hst : CaseStored env kc kr sh) {cvc : ConstantVal .anon}
    (hty : cvc.type = piTele sh.binders (.app (.bvar (sh.nM + 1)) (.bvar sh.nM)))
    {ρ σ : BVarIdx → V} {R : KExpr} {As : List V} (hfit : Fits cval env φ ρ cvc.type As σ R)
    (hlen : As.length = sh.nP + 2 + sh.nM) {Tm : V} (hTm : As[sh.nP + 1]? = some Tm) :
    ∃ τ X, Denotes cval env φ τ (Expr.mkAppN (.const sh.ind sh.indLevels) (bvarsFrom 1 sh.nP)) X ∧
      Tm ∈ˢ X ∧ DenotesList cval env φ τ (bvarsFrom 1 sh.nP) (As.take sh.nP) := by
  obtain ⟨ps, mo, t, mins, rfl, hps, _⟩ := split_ctx As sh.nP sh.nM hlen
  obtain ⟨bP, bMo, bMaj, bMin, hbs, hbP, _⟩ := split_ctx sh.binders sh.nP sh.nM hst.arity.1
  obtain ⟨mmaj, hbmaj⟩ := hst.major
  have hbm : bMaj = (Expr.mkAppN (.const sh.ind sh.indLevels) (bvarsFrom 1 sh.nP), mmaj) := by
    have := get_ctx1 bP bMin bMo bMaj
    rw [hbP, ← hbs, hbmaj] at this
    exact (Option.some.inj this).symm
  subst hbm
  rw [hty, hbs] at hfit
  obtain ⟨_, _, ⟨X, hX, htX⟩, _⟩ := fits_ctx (by omega) hfit
  rw [← hps, get_ctx1] at hTm
  obtain rfl := Option.some.inj hTm
  refine ⟨_, X, hX, htX, ?_⟩
  rw [← hps, take_left_ctx]
  have := den_bvarsFrom (cval := cval) (env := env) (φ := φ) ρ [mo] ps []
  simpa using this

variable {M : Model V env} {p : Program} {κ : CId → KKey} {lpsOf : CId → List Nat} {S : CId → Prop}
  {Ok : CId → Levels → Prop}

theorem relSlots_of_relVs : ∀ {fs : List Value} {Fs : List V},
    RelVs M p κ lpsOf S Ok fs Fs → RelSlots M p κ lpsOf S Ok (fs.map .val) Fs
  | [], _, h => by cases h; exact .nil
  | _ :: _, _, h => by
    cases h with
    | cons hv h' => exact .cons (.val hv) (relSlots_of_relVs h')

/-- **The generic `case` lemma, SrcEval side**: `CaseFires` at every `case` constant whose shape is
checked, from `caseIota`, the relation and canonicity. -/
theorem caseFires_of_shape (hL : Laws M) {p : Program} {c r : CId} {sh : CaseShape}
    (hF : Faith p env κ lpsOf S) (hN : NatBasis env) (_hSc : S c)
    (hres : p.table.resolveOf c = some (.case r)) (hst : CaseStored env (κ c) (κ r) sh)
    (hpr : CaseProg p κ S r sh) : CaseFires M p κ lpsOf S Ok c := by
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
      have hTe := relV_lit_eq (lawsCore_of_laws hL) hN φ hrelM
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
        obtain ⟨Mn, hMn, heq, hch⟩ := caseIota M (lawsCore_of_laws hL) hst cvc _ hint hfc φ ρ σ R As hfit' hlen hlast
          0 cs0 cvZ _ [] ρ _ hcs0 hcC hK hFC (by rw [hn0]; rfl) hmaj
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
        obtain ⟨Mn, hMn, heq, hch⟩ := caseIota M (lawsCore_of_laws hL) hst cvc _ hint hfc φ ρ σ R As hfit' hlen hlast
          1 cs1 cvS _ [litSet M φ n] _ _ hcs1 hcC hK hFC (by rw [hn1]; rfl) hmaj
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
          obtain ⟨cvC, hfC, hlenC, hcl, hdef, hhead⟩ := hst.wf.ctorRaw cidx cs hcs
          have hfCk := hfC
          rw [hkey, hfcv] at hfC
          simp only [Option.some.injEq, ConstantInfo.ctorInfo.injEq] at hfC
          obtain ⟨rfl, -, -⟩ := hfC
          -- the constructor's level parameters
          obtain ⟨ci, hci, hlps⟩ := hF.stored c' hSc'
          rw [hfcv] at hci
          cases hci
          have hnd : cv.levelParams.Nodup := by
            have := hF.nodup c' hSc'; rwa [← hlps] at this
          obtain ⟨ls'', hls''⟩ : ∃ ls'' : List Level,
              ls'' = cv.levelParams.map fun q => lvlOf (ψ q) := ⟨_, rfl⟩
          have hψ : ∀ q ∈ cv.levelParams, Level.substFn φ cv.levelParams ls'' q = ψ q := by
            intro q hq
            obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hq
            rw [substFn_at φ cv.levelParams ls'' i q (lvlOf (ψ q)) hnd hi
              (by rw [hls'', List.getElem?_map, hi]; rfl), eval_lvlOf]
          have hK' : Denotes M.cval env φ ρ (.const (κ c') ls'') (M.cval (κ c') ψ) := by
            have h1 : Denotes M.cval env φ ρ (.const (κ c') ls'')
                (M.cval (κ c') (Level.substFn φ cv.levelParams ls'')) :=
              Denotes.const hfcv (by rw [hls'', List.length_map]; rfl)
            rwa [hL.cval_params _ _ hfcv (Level.substFn φ cv.levelParams ls'') ψ
              fun q hq => hψ q hq] at h1
          -- the constructor's fit, moved to the `case`'s environment and assignment
          obtain ⟨σ2, hfit2⟩ := fits_agree hfitc (ρ' := ρ) fun i hi =>
            absurd (lt_of_bvarsLt hcl hi) (Nat.not_lt_zero i)
          have hfit3 := fits_inst M (lawsCore_of_laws hL) hψ hfit2 hdef
          have hR'head : (Rc.instantiateLevelParams cv.levelParams ls'').getAppFn =
              .const sh.ind ls'' := by
            rw [getAppFn_inst, fits_piBody hfit2, show (Ps ++ Fs).length = sh.nP + cs.nF by
              simp; omega, hhead]
            simp only [Expr.instantiateLevelParams]
            rw [subst_params hnd (by rw [hls'', List.length_map])]
          -- the major domain, and canonicity
          obtain ⟨τ, X, hdom, hTmX, hDL⟩ := major_dom hst hty hfit' hlen hTm'
          have hK : Denotes M.cval env φ ρ (.const cs.key sh.indLevels)
              (M.cval cs.key (Level.substFn φ cv.levelParams sh.indLevels)) :=
            Denotes.const hfCk (by rw [← hlenC]; rfl)
          -- canonicity (`ctor_canon`) at the `case`'s inductive, which is never a proposition
          -- (`CaseWF.indSort`): in a proof-irrelevant set model its constructors are read in the
          -- graph regime, an image is the tagged tuple of its fields, and such a tuple lies in the
          -- family at other parameters only if its fields lie in their types there (at a
          -- proposition every image is `pt`, and the law is not assumed)
          obtain ⟨cvD, capsD, sD, hfD, hsD, hnvD⟩ := hst.wf.indSort
          obtain ⟨heqK, σ3, R3, hFC⟩ := hL.ctor_canon (κ c') cv sh.nP cs.nF hfcv sh.ind cvD capsD sD
            sh.indLevels ls'' φ ρ τ σ2 _ _ (As.take sh.nP) Ps Fs _ _ X hfD hsD
            (eval_ne_zero_of_never hnvD _) (eval_ne_zero_of_never hnvD _) (by simp; omega) hPl hFl
            (by rw [← hkey]; exact hK) hK' hfit3 hR'head (by rw [getAppFn_mkAppN]; rfl) hdom
            (by
              rw [getAppArgs_mkAppN]
              simp only [Expr.getAppArgs, List.nil_append]
              rw [List.take_of_length_le (show (bvarsFrom 1 sh.nP).length ≤ sh.nP by
                simp [bvarsFrom_length])]
              exact hDL)
            hTmX
          obtain ⟨Mn, hMn, heq, hch⟩ := caseIota M (lawsCore_of_laws hL) hst cvc _ hint hfc φ ρ σ R As hfit' hlen hlast
            cidx cs cv _ Fs σ3 R3 hcs hfCk hK hFC hFl (by rw [hTm', heqK])
          exact ⟨Mn, Fs, hMn, relSlots_of_relVs hfs', heq, hch⟩
        · simp at hsel
      | _ => simp [hd'] at hsel
  | _ => simp at hsel

end IxCC.Grounding
