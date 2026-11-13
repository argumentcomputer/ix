import IxCCGrounding.CaseBlind
import IxCCGrounding.Check

/-!
# `case` entries over level-polymorphic families (`IxCCGrounding.CaseLevels`)

The canonicity-free `case` lemma (`caseFires_of_blind`) needs the inductive to have no level
parameter: a constructor value related by provenance (`RelV.con`) is the constructor's image at the
assignment `ψ` it was built at, while ι (`IotaLawG`) reads the constructor at the `case`'s levels
`sh.indLevels` (at `φ`) applied to arguments that fit its type there. With level parameters the two
readings are one exactly when the value was built at the levels the `case` reads it at: **level
agreement**. This module states the one interface both evaluators need (`MajorAt`: the major is the
constructor at the site's levels applied to its own arguments, which fit there), derives it from
agreement with `cval_params` alone (`majorAt_of_agree`), and proves F5 under agreement
(`caseFires_of_agree`, `caseFires_of_blind` without `sh.indLevels = []`).

**Agreement is not a law.** It is a fact about the run, which SrcEval does not check (`selectRule`
reads the constructor and the parameter count only). None of #678's five fields the family uses
gives it: `iota_rule` reads only the image at the major domain's levels, `cval_params` relates only
assignments that agree on a constant's own parameters. A law doing without agreement would have to
move the parameters as well (the value's own parameters need not fit at other levels), i.e. it
would be canonicity (`CtorCanon`), which the canonicity-free family exists to avoid.

**It is decided on a verified instance set.** `Inst`, a finite list of (constant, concrete levels),
computed by an untrusted walk and checked by `instCheckB`: it holds the root at no level, it is
closed under every constant SrcEval may evaluate in a run term or a rule body of one of its
instances (`evalConsts`, at the levels it computes), and at every instance of a `case` entry every
instance of a constructor of the entry's family is at the entry's `indLevels` (`InstUniform`). The
fundamental lemma takes it through its abstract `Ok`, at `OkIn p ann Inst` (`Ok` and membership):
`HeadAt.ctor`/`.cases` carry `Ok c ls` and `RelV.con` carries `lpsOf c = [] ∨ Ok c ls`, so F5 sees
both instances (`caseLevelAgree_of_inst`).

**Why the instance set is complete where it is used.** `InstClosed` is stated over `evalConsts`,
which contains everything `Runs.const` asks `Ok` of: `evalConsts` reads a `let`'s value wherever the
`let` is relevant (a dead `let`'s value too, which `Runs` asks nothing of, since SrcEval evaluates it)
and its body, so the walk, `InstClosed` and `instCheckB` read `let`s together. A dead value at a
non-uniform instance makes `instCheckB` refuse a program whose result cannot depend on it: the
restriction stays fail-closed. String literals are read by neither `evalConsts` nor the check's
correspondence (`valueCorr`, `eqnCorr`), which refuses them.
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open IxCC.Src (Value Slot Term CId Program Levels)

universe w

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv}

/-! ## The interface, model side -/

/-- **The major at the site's levels** (the interface both evaluators need): a constructor image
built at the assignment `ψ`, at arguments `Ps ++ Fs`, is the constructor read at the site's levels
`ls` (at `φ`) applied to the same arguments, and they fit its type there. What `caseIotaG` takes. -/
def MajorAt (M : Model V env) (key : KKey) (cvC : ConstantVal .anon) (ls : List Level)
    (φ ψ : LevelParam → Nat) (ρ : BVarIdx → V) (Ps Fs : List V) : Prop :=
  (∃ K, Denotes M.cval env φ ρ (.const key ls) K ∧
      (Ps ++ Fs).foldl app (M.cval key ψ) = (Ps ++ Fs).foldl app K) ∧
  ∃ (σC : BVarIdx → V) (RC : KExpr),
    Fits M.cval env φ ρ (cvC.type.instantiateLevelParams cvC.levelParams ls) (Ps ++ Fs) σC RC

/-- **Level agreement**: `ψ` gives each of the constructor's level parameters the value its level
at the site has at `φ`. -/
def LevelsAgree (lps : List LevelParam) (ls : List Level) (φ ψ : LevelParam → Nat) : Prop :=
  ls.length = lps.length ∧ ∀ (k : Nat) q l, lps[k]? = some q → ls[k]? = some l → ψ q = Level.eval φ l

/-- Agreement in the form `cval_params` and `fits_inst_cv` read. -/
theorem substFn_of_agree {lps : List LevelParam} {ls : List Level} {φ ψ : LevelParam → Nat}
    (hnd : lps.Nodup) (hag : LevelsAgree lps ls φ ψ) :
    ∀ q ∈ lps, Level.substFn φ lps ls q = ψ q := by
  intro q hq
  obtain ⟨k, hk, hkq⟩ := List.getElem_of_mem hq
  have hq' : lps[k]? = some q := by rw [List.getElem?_eq_getElem hk, hkq]
  have hk' : k < ls.length := by rw [hag.1]; exact hk
  have hl : ls[k]? = some ls[k] := List.getElem?_eq_getElem hk'
  rw [substFn_at φ _ _ k q _ hnd hq' hl, hag.2 k q _ hq' hl]

/-- **Agreement gives the interface, from `cval_params` alone**: the image at `ψ` is the image at
the site's levels (the two assignments agree on the constructor's parameters), and the fit at `ψ` of
the closed, level-covered type moves to its instance at the site's levels (`fits_inst_cv`). -/
theorem majorAt_of_agree (M : Model V env) (hcv : CvalParams M) {key : KKey}
    {cvC : ConstantVal .anon} {nP nF : Nat} (hC : env.find? key = some (.ctorInfo cvC nP nF))
    (hcl : bvarsLt 0 cvC.type = true)
    (hdef : cvC.type.allLevelParamsDefined cvC.levelParams = true)
    (hnd : cvC.levelParams.Nodup) {ls : List Level} {φ ψ : LevelParam → Nat}
    (hag : LevelsAgree cvC.levelParams ls φ ψ)
    {ρc σc : BVarIdx → V} {Rc : KExpr} {Ps Fs : List V}
    (hfit : Fits M.cval env ψ ρc cvC.type (Ps ++ Fs) σc Rc) (ρ : BVarIdx → V) :
    MajorAt M key cvC ls φ ψ ρ Ps Fs := by
  have hψ := substFn_of_agree hnd hag
  refine ⟨⟨_, Denotes.const hC hag.1, ?_⟩, ?_⟩
  · show (Ps ++ Fs).foldl app (M.cval key ψ) =
        (Ps ++ Fs).foldl app (M.cval key (Level.substFn φ cvC.levelParams ls))
    rw [hcv key _ hC ψ (Level.substFn φ cvC.levelParams ls) (fun q hq => (hψ q hq).symm)]
  · obtain ⟨σ2, hfit2⟩ := fits_agree hfit (ρ' := ρ) fun i hi =>
      absurd (lt_of_bvarsLt hcl hi) (Nat.not_lt_zero i)
    exact ⟨_, _, fits_inst_cv M hcv hψ hfit2 hdef⟩

/-! ## F5 under agreement, SrcEval side -/

variable {M : Model V env} {κ : CId → KKey} {lpsOf : CId → List Nat} {S : CId → Prop}
  {Ok : CId → Levels → Prop}

/-- **Level agreement at a `case` entry**, over the abstract `Ok`: at every `Ok` instance of the
entry (its levels `ls`, read at any `φ` that gives the entry's parameters those values) and every
`Ok` instance of a constructor of the entry's family, the constructor's levels are the shape's
`indLevels` read at `φ`. -/
def CaseLevelAgree (p : Program) (lpsOf : CId → List Nat) (Ok : CId → Levels → Prop) (c : CId)
    (sh : CaseShape) (ind : CId) : Prop :=
  ∀ (ls : Levels) (φ : LevelParam → Nat), Ok c ls → LvAt φ (lpsOf c) ls →
    ∀ (c' : CId) (ls' : Levels) (sf : Bool) (lv cidx np nf : Nat) (ty : Term),
      p.decl? c' = some (.ctor sf lv ind cidx np nf ty) → Ok c' ls' →
      ls'.length = sh.indLevels.length ∧
        ∀ (k : Nat) l, sh.indLevels[k]? = some l → ls'[k]? = some (Level.eval φ l)

/-- **The canonicity-free `case` lemma with level parameters**: `caseFires_of_blind` without
`sh.indLevels = []`, under level agreement. A literal major as there; a constructor value through
agreement (its `ψ` gives the constructor's level parameters what `indLevels` gives them at the
`case`'s `φ`: `RelV.con`'s `LvAt` and its `Ok`, the `case` head's `Ok`, `CaseLevelAgree`) and then
`caseIotaG` at the constructor's own parameters. Laws: `DefnValue`, `IotaLawG`, `CvalParams` (and
`Model.mem`); not `ctor_canon`. -/
theorem caseFires_of_agree (hδ : DefnValue M) (hι : IotaLawG M.cval env) (hcv : CvalParams M)
    {p : Program} {c r : CId} {sh : CaseShape}
    (hF : Faith p env κ lpsOf S) (hN : NatBasis env) (_hSc : S c)
    (hres : p.table.resolveOf c = some (.case r)) (hst : CaseStored env (κ c) (κ r) sh)
    (hpr : CaseProg p κ S r sh) (hB : CaseRulesBlind env (κ r))
    (hag : ∀ (sf kk : Bool) (lvls np nmot nmin ni : Nat) (ind : CId) (rules : List IxCC.Src.Rule)
      (ty : Term), p.decl? r = some (.recr sf kk lvls np nmot nmin ni ind rules ty) →
      CaseLevelAgree p lpsOf Ok c sh ind) :
    CaseFires M p κ lpsOf S Ok c := by
  intro r' sf kk lvls np nmot nmin ni ind rules ty hres' hd ls φ T ρ σ R As hh hfit hAsl hlast
    Tm mv j fields hTm hrelM hsel
  have hrr : r' = r := by rw [hres] at hres'; cases hres'; rfl
  subst hrr
  obtain ⟨sf0, kk0, lvls0, ind0, rules0, ty0, hd0, hctP, hnat⟩ := hpr.recr
  have hagr := hag sf0 kk0 lvls0 _ _ _ _ ind0 rules0 ty0 hd0
  rw [hd0] at hd
  simp only [Option.some.injEq, IxCC.Src.Decl.recr.injEq] at hd
  obtain ⟨-, -, -, rfl, rfl, rfl, rfl, rfl, -, -⟩ := hd
  obtain ⟨cvc, hint, hfc, _, hty⟩ := hst.casesOnStored
  cases hh with
  | cases _ hlvc hfind hOkc =>
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
          | @con _ _ _ _ ψ cvC' np'' nf'' Ps Fs ρc σc Rc hSc' hlvψ hfc' hPl hFl _ hfs' hfitc hOkv =>
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
          -- level agreement (`CaseLevelAgree`, at the `case` head's `Ok` instance and the value's):
          -- `ψ` gives each of the constructor's level parameters what `indLevels` gives it at `φ`
          obtain ⟨ciS, hciS, hlpsS⟩ := hF.stored c' hSc'
          rw [hfcv] at hciS
          cases hciS
          simp only [ConstantInfo.toConstantVal] at hlpsS
          have hnd : cv.levelParams.Nodup := by rw [hlpsS]; exact hF.nodup c' hSc'
          have hψ : ∀ q ∈ cv.levelParams, Level.substFn φ cv.levelParams sh.indLevels q = ψ q := by
            intro q hq
            obtain ⟨k, hk, hkq⟩ := List.getElem_of_mem hq
            have hq' : cv.levelParams[k]? = some q := by rw [List.getElem?_eq_getElem hk, hkq]
            have hk' : k < sh.indLevels.length := by omega
            have hl : sh.indLevels[k]? = some sh.indLevels[k] := List.getElem?_eq_getElem hk'
            rw [substFn_at φ _ _ k q _ hnd hq' hl]
            rcases hOkv with hnil | hOk'
            · rw [← hlpsS, List.eq_nil_iff_forall_not_mem] at hnil
              exact absurd hq (hnil q)
            · obtain ⟨-, hval⟩ := hagr ls φ hOkc hlvc c' ls' _ _ _ _ _ _ hd' hOk'
              have h1 := hval k _ hl
              have h2 := hlvψ k q (by rw [← hlpsS]; exact hq')
              rw [h2, List.getD_eq_getElem?_getD, h1, Option.getD_some]
          have hK : Denotes M.cval env φ ρ (.const cs.key sh.indLevels) (M.cval (κ c') ψ) := by
            have h1 : Denotes M.cval env φ ρ (.const cs.key sh.indLevels)
                (M.cval cs.key (Level.substFn φ cv.levelParams sh.indLevels)) :=
              Denotes.const hfCk (by rw [← hlenC]; rfl)
            have e1 : M.cval cs.key (Level.substFn φ cv.levelParams sh.indLevels) =
                M.cval (κ c') ψ := by
              rw [hkey]
              exact hcv _ _ hfcv _ _ hψ
            rwa [e1] at h1
          obtain ⟨σ2, hfit2⟩ := fits_agree hfitc (ρ' := ρ) fun i hi =>
            absurd (lt_of_bvarsLt hcl hi) (Nat.not_lt_zero i)
          have hFC := fits_inst_cv M hcv (ks := cv.levelParams) (us := sh.indLevels) (φ := φ)
            (ψ := ψ) hψ hfit2 hdef
          -- the guarded ι law at the constructor's own parameters `Ps` (`caseIotaG`)
          obtain ⟨Mn, hMn, heq, hch⟩ := caseIotaG M hδ hι hcv hst hB cvc _ hint hfc φ ρ σ R As
            hfit' hlen hlast cidx cs cv _ Ps Fs σ2 _ hcs hfCk hK hFC hPl hFl hTm'
          exact ⟨Mn, Fs, hMn, relSlots_of_relVs hfs', heq, hch⟩
        · simp at hsel
      | _ => simp [hd'] at hsel
  | _ => simp at hsel

/-! ## The verified instance set -/

/-- The rule bodies of a recursor (the instance walk enters them: F2 runs them at the recursor's
levels). -/
def ruleBodies (p : Program) (c : CId) : List Term :=
  match p.decl? c with
  | some (.recr _ _ _ _ _ _ _ _ rules _) => rules.map (·.rhs)
  | _ => []

/-- **`Ok`, restricted to an instance set.** -/
def OkIn (p : Program) (ann : IxCC.Src.Relevance.Ann) (Inst : List (CId × Levels)) (c : CId)
    (ls : Levels) : Prop :=
  IxCC.Grounding.Ok p ann c ls ∧ (c, ls) ∈ Inst

/-- **The instance set is closed**: every constant SrcEval may evaluate in a run term or a rule
body of an instance of `Inst` (`evalConsts`, exactly what `Runs.const` asks `Ok` of), at the levels
it computes there, is an instance of `Inst`. -/
def InstClosed (p : Program) (Inst : List (CId × Levels)) : Prop :=
  ∀ c ls, (c, ls) ∈ Inst → ∀ t ∈ runTerms p c ++ ruleBodies p c,
    ∀ d us, (d, us) ∈ evalConsts ls t → (d, us.map (IxCC.Src.evalUniv ls)) ∈ Inst

/-- **Level uniformity on `Inst`**: at every instance of a `case` entry whose shape the check
reads, every instance of a constructor of the entry's family is at the shape's `indLevels` read at
the entry's levels. -/
def InstUniform (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (Inst : List (CId × Levels)) : Prop :=
  ∀ c r ls, (c, ls) ∈ Inst → p.table.resolveOf c = some (.case r) →
    ∀ sh, caseShape? env (κ c) (κ r) = some sh →
    ∀ (sf kk : Bool) (lvls np nmot nmin ni : Nat) (ind : CId) (rules : List IxCC.Src.Rule)
      (ty : Term), p.decl? r = some (.recr sf kk lvls np nmot nmin ni ind rules ty) →
    ∀ (φ : LevelParam → Nat), LvAt φ (lpsOf c) ls →
    ∀ (c' : CId) (ls' : Levels) (sf' : Bool) (lv cidx np' nf : Nat) (ty' : Term),
      p.decl? c' = some (.ctor sf' lv ind cidx np' nf ty') → (c', ls') ∈ Inst →
      ls'.length = sh.indLevels.length ∧
        ∀ (k : Nat) l, sh.indLevels[k]? = some l → ls'[k]? = some (Level.eval φ l)

/-- The position of `q` in `l`. -/
def posIn (q : Nat) : List Nat → Option Nat
  | [] => none
  | x :: xs => if x == q then some 0 else (posIn q xs).map (· + 1)

theorem posIn_spec (q : Nat) : ∀ {l : List Nat}, q ∈ l → ∃ k, posIn q l = some k ∧ l[k]? = some q
  | x :: xs, h => by
    by_cases hx : x = q
    · exact ⟨0, by simp [posIn, hx], by simp [hx]⟩
    · have hq : q ∈ xs := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hx
        · exact h
      obtain ⟨k, hk, hkq⟩ := posIn_spec q hq
      exact ⟨k + 1, by simp [posIn, hx, hk], by simpa using hkq⟩

/-- The assignment concrete levels `ls` give the parameters `lps` (others `0`). -/
def φAt (lps : List Nat) (ls : Levels) : LevelParam → Nat := fun q =>
  match posIn q lps with
  | some k => ls.getD k 0
  | none => 0

/-- At a level over `lps`, `φAt` reads as any assignment that gives `lps` the values `ls`. -/
theorem eval_φAt {φ : LevelParam → Nat} {lps : List Nat} {ls : Levels} (hlv : LvAt φ lps ls)
    {l : Level} (hl : l.allParamsDefined lps = true) : Level.eval φ l = Level.eval (φAt lps ls) l :=
  Level.eval_ext hl fun q hq => by
    obtain ⟨k, hk, hkq⟩ := posIn_spec q hq
    simp only [φAt, hk]
    exact hlv k q hkq

/-- **The restriction, decided on a given `Inst`** (computed by the instance walk; the check
verifies, so the walk is not trusted): the seeds at no level in `Inst`; `Inst` closed; and uniform
at every `case` entry whose shape is read, each `indLevels` over the entry's level parameters. Its
cost is quadratic in `|Inst|` (list membership, and every constructor instance against every
`case` instance): 170 ms interpreted on `phase1-decline/strings` (138 instances); an index is open
(`docs/roadmap.md`). -/
def instCheckB (p : Program) (env : KEnv) (κ : CId → KKey) (lpsOf : CId → List Nat)
    (seeds : List CId) (Inst : List (CId × Levels)) : Bool :=
  seeds.all (fun c => decide ((c, ([] : Levels)) ∈ Inst)) &&
  Inst.all (fun x => (runTerms p x.1 ++ ruleBodies p x.1).all fun t =>
    (evalConsts x.2 t).all fun y => decide ((y.1, y.2.map (IxCC.Src.evalUniv x.2)) ∈ Inst)) &&
  Inst.all fun x =>
    match p.table.resolveOf x.1 with
    | some (.case r) =>
      match caseShape? env (κ x.1) (κ r), p.decl? r with
      | some sh, some (.recr _ _ _ _ _ _ _ ind _ _) =>
        sh.indLevels.all (·.allParamsDefined (lpsOf x.1)) &&
        Inst.all fun y =>
          match p.decl? y.1 with
          | some (.ctor _ _ ind' _ _ _ _) =>
            ind' != ind || y.2 == sh.indLevels.map (Level.eval (φAt (lpsOf x.1) x.2))
          | _ => true
      | _, _ => true
    | _ => true


/-- **The instance walk** (a producer, not trusted: `instCheckB` verifies what it returns): from
the seeds at no level, every constant `evalConsts` reaches in a run term or a rule body of a
reached instance, at the levels it computes there; at most `fuel` steps (`none` beyond). Like
`evalConsts` it reads a `let`'s value where the `let` is relevant (dead or not) and its body. -/
def instWalk (p : Program) (seeds : List CId) (fuel : Nat) : Option (List (CId × Levels)) :=
  go fuel (seeds.map fun c => (c, [])) []
where
  go : Nat → List (CId × Levels) → List (CId × Levels) → Option (List (CId × Levels))
    | _, [], acc => some acc.reverse
    | 0, _ :: _, _ => none
    | n + 1, x :: todo, acc =>
      if acc.contains x then go n todo acc
      else
        go n (todo ++ (runTerms p x.1 ++ ruleBodies p x.1).flatMap fun t =>
          (evalConsts x.2 t).map fun y => (y.1, y.2.map (IxCC.Src.evalUniv x.2))) (x :: acc)

/-- **`instCheckB` is sound.** -/
theorem instFacts_of_check {p : Program} {env : KEnv} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {seeds : List CId} {Inst : List (CId × Levels)}
    (h : instCheckB p env κ lpsOf seeds Inst = true) :
    (∀ c ∈ seeds, (c, ([] : Levels)) ∈ Inst) ∧ InstClosed p Inst ∧
      InstUniform p env κ lpsOf Inst := by
  simp only [instCheckB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, fun c ls hm t ht d us hd => h2 (c, ls) hm t ht (d, us) hd, ?_⟩
  intro c r ls hm hres sh hsh sf kk lvls np nmot nmin ni ind rules ty hd φ hlv c' ls' sf' lv cidx
    np' nf ty' hd' hm'
  have h4 := h3 (c, ls) hm
  simp only [hres, hsh, hd, Bool.and_eq_true, List.all_eq_true] at h4
  obtain ⟨hdef, hall⟩ := h4
  have h5 := hall (c', ls') hm'
  simp only [hd', bne_self_eq_false, Bool.false_or, beq_iff_eq] at h5
  subst h5
  refine ⟨by simp, fun k l hl => ?_⟩
  simp only [List.getElem?_map, hl, Option.map_some,
    eval_φAt hlv (hdef l (List.mem_of_getElem? hl))]

/-- **Uniformity gives agreement at `OkIn`**, at the shape the check reads. -/
theorem caseLevelAgree_of_inst {p : Program} {env : KEnv} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Inst : List (CId × Levels)}
    (hU : InstUniform p env κ lpsOf Inst) {c r : CId} {sh : CaseShape}
    (hres : p.table.resolveOf c = some (.case r)) (hsh : caseShape? env (κ c) (κ r) = some sh)
    {sf kk : Bool} {lvls np nmot nmin ni : Nat} {ind : CId} {rules : List IxCC.Src.Rule} {ty : Term}
    (hd : p.decl? r = some (.recr sf kk lvls np nmot nmin ni ind rules ty)) :
    CaseLevelAgree p lpsOf (OkIn p ann Inst) c sh ind :=
  fun ls φ hOk hlv c' ls' sf' lv cidx np' nf ty' hd' hOk' =>
    hU c r ls hOk.2 hres sh hsh sf kk lvls np nmot nmin ni ind rules ty hd φ hlv c' ls' sf' lv cidx
      np' nf ty' hd' hOk'.2

/-! ## The family's decided facts -/

/-- **`CaseFacts` at the shape the check reads** (`caseShape?`), which uniformity is stated at. -/
def CaseFactsRead (p : Program) (env : KEnv) (κ : CId → KKey) (S : CId → Prop) : Prop :=
  ∀ c r, S c → p.table.resolveOf c = some (.case r) →
    ∃ sh, caseShape? env (κ c) (κ r) = some sh ∧ CaseStored env (κ c) (κ r) sh ∧ CaseProg p κ S r sh

theorem CaseFactsRead.facts {p : Program} {env : KEnv} {κ : CId → KKey} {S : CId → Prop}
    (h : CaseFactsRead p env κ S) : CaseFacts p env κ S := fun c r hc hr => by
  obtain ⟨sh, -, hst, hpr⟩ := h c r hc hr
  exact ⟨sh, hst, hpr⟩

theorem caseFactsRead_of_check {p : Program} {env : KEnv} {κ : CId → KKey}
    {lpsOf : CId → List Nat} {ann : IxCC.Src.Relevance.Ann} {Sl : List CId}
    (h : groundCheck p env κ lpsOf ann Sl = true) : CaseFactsRead p env κ (· ∈ Sl) := by
  intro c r hc hr
  have h1 := List.all_eq_true.mp (part_of (name := "caseShape") (b := Sl.all (caseShapeB p env κ)) h (by simp [checkParts, checkPartsWith])) c hc
  have h2 := List.all_eq_true.mp (part_of (name := "caseProg") (b := Sl.all (caseProgOkB p env κ Sl)) h (by simp [checkParts, checkPartsWith])) c hc
  simp only [caseShapeB, caseProgOkB, hr] at h1 h2
  split at h1
  · rename_i sh hsh
    rw [hsh] at h2
    exact ⟨sh, hsh, caseStored_of_check h1, caseProg_of_check h2⟩
  · exact absurd h1 (by simp)

/-- **`NoCanon` without the level condition at `case` entries**: their stored rules do not compare
parameters (`CaseRulesBlind`); `flat`/`noParams` recursors as in `NoCanon`. -/
structure NoCanonA (p : Program) (env : KEnv) (κ : CId → KKey) (S : CId → Prop) : Prop where
  cases : ∀ c r, S c → p.table.resolveOf c = some (.case r) → CaseRulesBlind env (κ r)
  recs : ∀ r, S r → (recClassB p env κ r = some .flat ∨ recClassB p env κ r = some .noParams) →
    RecNoLevels env (κ r)

/-- `NoCanonA`, decided (`noCanonB` less `ctorsNoLevelsB` at `case` entries). -/
def noCanonAB (p : Program) (env : KEnv) (κ : CId → KKey) (Sl : List CId) : Bool :=
  let tab := KTab.of env
  Sl.all fun c =>
    (match p.table.resolveOf c with
      | some (.case r) =>
        match tab[κ r]? with
        | some (.recInfo _ _ _ rules) => rules.all fun rl => !rl.compareParams
        | _ => false
      | _ => true) &&
    (match recClassB p env κ c with
      | some .flat | some .noParams =>
        match tab[κ c]? with
        | some (.recInfo _ _ _ rules) => ctorsNoLevelsB tab rules
        | _ => false
      | _ => true)

/-- The landed fact implies the new one. -/
theorem noCanonA_of_noCanon {p : Program} {env : KEnv} {κ : CId → KKey} {S : CId → Prop}
    (h : NoCanon p env κ S) : NoCanonA p env κ S :=
  ⟨fun c r hc hr => by
    obtain ⟨cvr, mI, rP, rules, hf, hall⟩ := h.cases c r hc hr
    exact ⟨cvr, mI, rP, rules, hf, fun rl hrl => (hall rl hrl).1⟩, h.recs⟩

/-- **`noCanonAB` is sound** (as `noCanon_of_check`). -/
theorem noCanonA_of_check {p : Program} {env : KEnv} {κ : CId → KKey} {Sl : List CId}
    (h : noCanonAB p env κ Sl = true) : NoCanonA p env κ (· ∈ Sl) := by
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
      simp only [List.all_eq_true, Bool.not_eq_true'] at h2
      exact ⟨cvr, mI, rP, rules, hf, h2⟩
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

/-- **F5 at every `case` entry of `Sl` at `OkIn`**: from the shapes the check reads, `NoCanonA`
and uniformity. -/
theorem caseFires_of_inst (hδ : DefnValue M) (hι : IotaLawG M.cval env) (hcv : CvalParams M)
    {p : Program} {ann : IxCC.Src.Relevance.Ann} {Inst : List (CId × Levels)}
    (hF : Faith p env κ lpsOf S) (hN : NatBasis env) (hC : CaseFactsRead p env κ S)
    (hNC : NoCanonA p env κ S) (hU : InstUniform p env κ lpsOf Inst) :
    ∀ c r, S c → p.table.resolveOf c = some (.case r) →
      CaseFires M p κ lpsOf S (OkIn p ann Inst) c := by
  intro c r hc hr
  obtain ⟨sh, hsh, hst, hpr⟩ := hC c r hc hr
  exact caseFires_of_agree hδ hι hcv hF hN hc hr hst hpr (hNC.cases c r hc hr)
    (fun _ _ _ _ _ _ _ _ _ _ hd => caseLevelAgree_of_inst hU hr hsh hd)

end IxCC.Grounding
