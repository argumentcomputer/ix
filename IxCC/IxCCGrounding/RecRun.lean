import IxCCGrounding.RecFlat
import IxCCGrounding.Direct.Sites

/-!
# F2 at a recursor whose rule bodies run (`IxCCGrounding.RecRun`; G3, part E)

The class `noParams`: kind `ordinary`, no parameter, no index, the inductive never a proposition,
not flat (a rule with fields, or a body that is not a variable). SrcEval's F2 forces the major,
selects the rule by its constructor and **evaluates the rule's body** (peeled of the prefix's and the
fields' λs) in the slots of the arguments before the major and the fields. The fundamental lemma
relates that evaluation to the body's denotation through `eval`'s induction hypothesis, which needs
the body to *run* (`Runs`); ι and β make the body's denotation the recursor applied to the arguments.

**Model side** (`noParamsIota`, over `IotaLaw` alone): given the major premise's set as rule `j`'s
constructor image `K` at the levels the major domain names applied to fields `Fs` that fit the
constructor's type there, ι at rule `j` and β through the rule's λs (the prefix's domains are the
type's, `RecTele`; the fields' are the constructor's field types lifted past the prefix,
`RecFields`) give the recursor applied to the arguments as the body's set, with the prefix and the
fields bound, in an environment satisfying the λs' domains. The constructor image and its fields'
fit are moved from the assignment and environment the constructor value was built at to the
recursor's: without canonicity where the constructor has no level parameters
(`ctorFields_noLevels`: level-parameter irrelevance only), by the restricted canonicity where it has
some (`ctorFields_canon`; no measured closure has one).

**SrcEval side**: the body runs (`Runs`, by `runs_of_corr` on the whole right-hand side, then
`runs_peel`): it corresponds to the stored body (`RecStored`), the stored rule is closed and
denotes (by ι), it names no constant (`RecBodies`), and its sites are typed (`ruleSites_ok`):

1. **Where.** A recursor whose motive lands in `Sort u` stores "a proposition where `u = 0`" on
   every binder (a binder datum says when the *function* is a proof), its minor premises' field
   binders included; so at `u = 0` a rule body's site `mⱼ f` is in regime `0` and not typed.
   `fire` has no `Ok` for the recursor, but it has `LastSiteOk`: the major premise was applied at a
   graph-regime site, which `last_regime` turns into "the major premise's binder datum does not
   hold at `φ`". The check walks each rule at exactly the profiles where that datum does not hold
   (`RecSites`, `recProfiles`), and `φ`'s profile is one of them.
2. **At which levels.** `fire` knows no length for the levels `ls` SrcEval carries (`HeadAt.recr`
   gives `LvAt` only), so `profileOf ls` need not be a profile of the recursor's level count. The
   proof reads the body at `ls` cut or padded to that count (`ls'`, which `φ` agrees with); this
   changes nothing SrcEval decides in the body, because its relevance annotations name only level
   variables below the count (`RecBodies`, `relsBelow`; its universes are below it already, by
   `TermCorr`), so `evalSites ls = evalSites ls'` (`evalSites_congr`).

`termRefused_sound` (the direct route's soundness) then types every site. It takes the laws whole
(`Laws`, `NatBasis`): the walk may use δ, ι, the projection law and the `Nat` accelerations in its
conversion; on the measured rule bodies (`mⱼ f…`, variables applied to variables) it reduces
nothing.
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel
open IxCC.Src (Value Slot Term CId Program Levels)

universe w

/-! ## A rule body read at the levels SrcEval carries, cut or padded to the recursor's count -/

/-- A zero-ness condition naming only level variables below `n` reads two level lists alike when
they agree below `n`. -/
theorem holds_below {n : Nat} {ls ls' : Levels} (hag : ∀ i < n, ls.getD i 0 = ls'.getD i 0)
    {w : IxCC.Src.PropWhen} (hw : ∀ q ∈ w.params, q < n) : w.holds ls = w.holds ls' := by
  cases w with
  | never => rfl
  | allZero ps =>
    simp only [IxCC.Src.PropWhen.params] at hw
    simp only [IxCC.Src.PropWhen.holds]
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    constructor
    · intro H q hq
      rw [← hag q (hw q hq)]
      exact H q hq
    · intro H q hq
      rw [hag q (hw q hq)]
      exact H q hq

/-- **The sites SrcEval may evaluate are the same at two level lists** that agree below `n`, when
the term's relevance annotations name only level variables below `n`. -/
theorem evalSites_congr {n : Nat} {ls ls' : Levels} (hag : ∀ i < n, ls.getD i 0 = ls'.getD i 0) :
    ∀ (t : Term) (Γ : List KExpr) (e : KExpr), relsBelow n t = true →
      evalSites ls Γ t e = evalSites ls' Γ t e
  | .app f a m r, Γ, e, h => by
    simp only [relsBelow, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hr, hf⟩, ha⟩ := h
    cases e with
    | app f' a' =>
      have hirr : r.irrAt ls = r.irrAt ls' := holds_below hag hr
      simp only [evalSites, hirr, evalSites_congr hag f Γ f' hf, evalSites_congr hag a Γ a' ha]
    | _ => first | rfl | simp [evalSites]
  | .lam b d body, Γ, e, h => by
    simp only [relsBelow, Bool.and_eq_true] at h
    cases e with
    | lam d' body' m => simp only [evalSites, evalSites_congr hag body (d' :: Γ) body' h.2]
    | _ => first | rfl | simp [evalSites]
  | .proj s i t, Γ, e, h => by
    simp only [relsBelow] at h
    cases e with
    | proj s' i' e' => simp only [evalSites, evalSites_congr hag t Γ e' h]
    | _ => first | rfl | simp [evalSites]
  | .var _, _, _, _ => rfl
  | .sort _, _, _, _ => rfl
  | .const _ _, _, _, _ => rfl
  | .pi .., _, _, _ => rfl
  | .letE .., _, _, _ => rfl
  | .natLit _, _, _, _ => rfl
  | .strLit _, _, _, _ => rfl

/-- A constant SrcEval may evaluate is one the term names. -/
theorem evalConsts_mentions (ls : Levels) :
    ∀ (t : Term) {d : CId} {us : List IxCC.Ixon.Univ}, (d, us) ∈ evalConsts ls t →
      t.mentions d = true
  | .const c us', d, us, h => by
    simp only [evalConsts, List.mem_singleton, Prod.mk.injEq] at h
    simp [Term.mentions, h.1]
  | .app f a _ r, d, us, h => by
    simp only [evalConsts, List.mem_append] at h
    simp only [Term.mentions, Bool.or_eq_true]
    rcases h with h | h
    · exact Or.inl (evalConsts_mentions ls f h)
    · split at h
      · simp at h
      · exact Or.inr (evalConsts_mentions ls a h)
  | .lam _ _ body, d, us, h => by
    simp only [evalConsts] at h
    simp [Term.mentions, evalConsts_mentions ls body h]
  | .proj _ _ e, d, us, h => by
    simp only [evalConsts] at h
    simp [Term.mentions, evalConsts_mentions ls e h]
  | .var _, _, _, h => by simp [evalConsts] at h
  | .sort _, _, _, h => by simp [evalConsts] at h
  | .pi .., _, _, h => by simp [evalConsts] at h
  | .letE .., _, _, h => by simp [evalConsts] at h
  | .natLit _, _, _, h => by simp [evalConsts] at h
  | .strLit _, _, _, h => by simp [evalConsts] at h

/-- Peeling λs does not change the constants SrcEval may evaluate (it never evaluates a domain). -/
theorem evalConsts_peel (ls : Levels) :
    ∀ (n : Nat) (t t' : Term), IxCC.Src.peelLams n t = some t' → evalConsts ls t = evalConsts ls t'
  | 0, t, t', h => by
    simp only [IxCC.Src.peelLams, Option.some.injEq] at h
    rw [h]
  | n + 1, t, t', h => by
    cases t with
    | lam b d body =>
      simp only [IxCC.Src.peelLams] at h
      simp only [evalConsts]
      exact evalConsts_peel ls n body t' h
    | _ => simp [IxCC.Src.peelLams] at h

/-- Two λ-telescopes of one length over the same term are the same. -/
theorem lamTele_inj : ∀ (bs bs' : List (KExpr × BinderMeta)) (b b' : KExpr),
    bs.length = bs'.length → lamTele bs b = lamTele bs' b' → bs = bs' ∧ b = b'
  | [], [], _, _, _, h => ⟨rfl, h⟩
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl
  | (A, m) :: bs, (A', m') :: bs', b, b', hl, h => by
    simp only [lamTele, Expr.lam.injEq] at h
    obtain ⟨rfl, h2, rfl⟩ := h
    obtain ⟨rfl, rfl⟩ := lamTele_inj bs bs' b b' (by simpa using hl) h2
    exact ⟨rfl, rfl⟩

theorem piBody_piTele : ∀ (bs : List (KExpr × BinderMeta)) (C : KExpr),
    piBody bs.length (piTele bs C) = C
  | [], C => by cases C <;> rfl
  | (A, m) :: bs, C => by
    simp only [List.length_cons, piTele, piBody]
    exact piBody_piTele bs C

theorem piBody_inst (ks : List LevelParam) (us : List Level) : ∀ (n : Nat) (e : KExpr),
    piBody n (e.instantiateLevelParams ks us) = (piBody n e).instantiateLevelParams ks us
  | 0, e => by cases e <;> rfl
  | n + 1, e => by
    cases e with
    | forallE d b m =>
      simp only [Expr.instantiateLevelParams, piBody]
      exact piBody_inst ks us n b
    | _ => rfl

section Sem

variable {V : Type w} [Ix.Kernel.SetTheory V] {env : KEnv}

/-! ## The rule body's sites -/

/-- **A rule body's sites are typed** at the levels SrcEval runs it at, where the major premise's
binder is in the graph regime and the right-hand side denotes: the direct route refuses none at the
profiles `RecSites` names (`termRefused_sound`), read at `ls` cut or padded to the level count
(`evalSites_congr`). Laws: those the direct route's soundness takes (`Laws`, `NatBasis`). -/
theorem ruleSites_ok {M : Model V env} (hL : LawsCore M) (hN : NatBasis env) {lps : List Nat}
    {ls : Levels} {φ : LevelParam → Nat} (hlv : LvAt φ lps ls) {t : Term} {e : KExpr}
    (hrels : relsBelow lps.length t = true) {pw : PropWhen} (hd : pw.paramsDefined lps = true)
    (hreg : regime φ pw ≠ 0) (hD : DenotesIn M φ [] e)
    (href : termRefused (KTab.of env) lps directFuel (recProfiles lps pw) [] t e [] = []) :
    ∀ s ∈ evalSites ls [] t e, SiteOk M φ s.1 s.2.1 s.2.2 := by
  intro s hs
  let ls' : Levels := (List.range lps.length).map fun i => ls.getD i 0
  have hag : ∀ i < lps.length, ls.getD i 0 = ls'.getD i 0 := by
    intro i hi
    simp [ls', List.getD_eq_getElem?_getD, hi]
  have hlen : ls'.length = lps.length := by simp [ls']
  have hlv' : LvAt φ lps ls' := fun i q hq => by
    rw [hlv i q hq]
    exact hag i (List.getElem?_eq_some_iff.mp hq).1
  have hφ : ProfAt φ lps (IxCC.Src.profileOf ls') := profAt_of_lvAt hlv' hlen
  have hfalse : pw.holds φ = false := by
    cases hh : pw.holds φ
    · rfl
    · simp [regime, hh] at hreg
  have hpw : pwAt lps (IxCC.Src.profileOf ls') pw = some false := by
    unfold pwAt
    simp only [hd, ↓reduceIte]
    rw [← holds_congr_zero hd (φOf_zero hφ), hfalse]
  have hP : IxCC.Src.profileOf ls' ∈ recProfiles lps pw := by
    simp only [recProfiles, List.mem_filter]
    exact ⟨mem_profiles _ _ (by simp [IxCC.Src.profileOf, hlen]), by rw [hpw]; rfl⟩
  rw [evalSites_congr hag t [] e hrels] at hs
  exact termRefused_sound hL hN (KTab.get_of env) hφ t (recProfiles lps pw) [] e [] hP hD s
    (Or.inl hs) (by rw [href]; exact List.not_mem_nil)

/-- **`Runs` through a λ-telescope**: the body runs in the context of the λs' domains. -/
theorem runs_peel {M : Model V env} {κ : CId → KKey} {Ok : CId → Levels → Prop} {lps : List Nat}
    {ls : Levels} {φ : LevelParam → Nat} :
    ∀ (bs : List (KExpr × BinderMeta)) {Γ : List KExpr} {t t' : Term} {b : KExpr},
      Runs M κ Ok lps ls φ Γ t (lamTele bs b) → IxCC.Src.peelLams bs.length t = some t' →
      Runs M κ Ok lps ls φ ((bs.map (·.1)).reverse ++ Γ) t' b
  | [], Γ, t, t', b, h, hp => by
    simp only [List.length_nil, IxCC.Src.peelLams, Option.some.injEq] at hp
    subst hp
    simp only [List.map_nil, List.reverse_nil, List.nil_append]
    exact h
  | (A, m) :: bs, Γ, t, t', b, h, hp => by
    have h' : Runs M κ Ok lps ls φ Γ t (.lam A (lamTele bs b) m) := h
    cases h' with
    | lam _ hbody _ =>
      have := runs_peel bs hbody (by simpa [IxCC.Src.peelLams] using hp)
      simpa [List.map_cons, List.reverse_cons, List.append_assoc] using this

/-! ## The environment and the context the body runs in -/

/-- Slots related to sets give a related environment, the last slot innermost. -/
theorem relEnv_pushAll {M : Model V env} {κ : CId → KKey} {lpsOf : CId → List Nat}
    {S : CId → Prop} {Ok : CId → Levels → Prop} :
    ∀ {ss : List Slot} {Xs : List V} {E : IxCC.Src.Env} {ρ : BVarIdx → V},
      RelSlots M κ lpsOf S Ok ss Xs → RelEnv M κ lpsOf S Ok E ρ →
        RelEnv M κ lpsOf S Ok (ss.reverse ++ E) (pushAll Xs ρ)
  | [], _, _, _, h, hE => by
    cases h
    simpa [pushAll_nil] using hE
  | s :: ss, _, E, ρ, h, hE => by
    cases h with
    | @cons _ _ X Xs hs h' =>
      have hE' : RelEnv M κ lpsOf S Ok (s :: E) (push X ρ) :=
        .cons hs (by rw [push_tail]; exact hE)
      have := relEnv_pushAll (E := s :: E) (ρ := push X ρ) h' hE'
      simpa [List.reverse_cons, List.append_assoc, pushAll_cons] using this

/-- Sets that fit a `∀`-telescope satisfy its domains as a context, the last innermost. -/
theorem ctxSat_of_fits {M : Model V env} {φ : LevelParam → Nat} :
    ∀ (bs : List (KExpr × BinderMeta)) (C : KExpr) {Γ0 : List KExpr} {ρ σ : BVarIdx → V}
      {R : KExpr} {xs : List V},
      CtxSat M φ Γ0 ρ → Fits M.cval env φ ρ (piTele bs C) xs σ R → xs.length = bs.length →
        CtxSat M φ ((bs.map (·.1)).reverse ++ Γ0) (pushAll xs ρ)
  | [], _, Γ0, ρ, σ, R, [], h0, _, _ => by simpa [pushAll_nil] using h0
  | [], _, _, _, _, _, _ :: _, _, _, hl => by simp at hl
  | _ :: _, _, _, _, _, _, [], _, _, hl => by simp at hl
  | (A, m) :: bs, C, Γ0, ρ, σ, R, x :: xs, h0, h, hl => by
    have h1 : Fits M.cval env φ ρ (.forallE A (piTele bs C) m) (x :: xs) σ R := h
    cases h1 with
    | cons hA hx h' =>
      have hc : CtxSat M φ (A :: Γ0) (push x ρ) :=
        .cons (by rw [push_tail]; exact h0) (by rw [push_tail]; exact hA) hx
      have := ctxSat_of_fits bs C hc h' (by simpa using hl)
      simpa [List.map_cons, List.reverse_cons, List.append_assoc, pushAll_cons] using this

/-! ## ι and β through a rule with fields -/

/-- **F2 at a recursor without parameters, model side** (ι, then β through the rule's λs at the
arguments before the major and the fields): given the major premise's set as rule `krl`'s
constructor image `K` at the levels the major domain names, applied to fields `Fs` that fit the
constructor's type there, the recursor applied to its arguments is what the rule's body denotes
with the prefix and the fields bound, in an environment that satisfies the rule's λ-domains; and the
right-hand side denotes. Of the laws it takes ι alone (`Laws.iota_rule`). -/
theorem noParamsIota (M : Model V env) (hι : IotaLaw M.cval env) {kr : KKey}
    {cvr : ConstantVal .anon} {mI : Nat} {krules : List (RecRule .anon)}
    (hf : env.find? kr = some (.recInfo cvr mI mI krules)) {tbs : List (KExpr × BinderMeta)}
    {C : KExpr} (hty : cvr.type = piTele tbs C) (htbs : tbs.length = mI) {krl : RecRule .anon}
    (hkrl : krl ∈ krules) {cvC : ConstantVal .anon} {nF : Nat}
    (hcC : env.find? krl.ctor = some (.ctorInfo cvC 0 nF)) {bs : List (KExpr × BinderMeta)}
    {b : KExpr} (hrhs : krl.rhs = lamTele bs b) (hbsl : bs.length = mI + nF)
    (hbs : (bs.take mI).map (·.1) = tbs.map (·.1)) {ls : List Level}
    {fbs : List (KExpr × BinderMeta)} {Cc : KExpr}
    (hcty : cvC.type.instantiateLevelParams cvC.levelParams ls = piTele fbs Cc)
    (hfbl : fbs.length = nF) (hcod : Cc.getAppArgs = [])
    (hflds : (bs.drop mI).map (·.1) = (liftTele mI 0 fbs).map (·.1))
    {φ : LevelParam → Nat} {ρ σ : BVarIdx → V} {R : KExpr} {As : List V}
    (hfit : Fits M.cval env φ ρ cvr.type As σ R) (hlen : As.length = mI + 1)
    {dom body : KExpr} {m : BinderMeta} {D : KKey}
    (hpb : piBody mI cvr.type = .forallE dom body m) (hdom : dom.getAppFn = .const D ls)
    {K : V} {Fs : List V} {σC : BVarIdx → V} {RC : KExpr}
    (hK : Denotes M.cval env φ ρ (.const krl.ctor ls) K)
    (hFs : Fits M.cval env φ ρ (piTele fbs Cc) Fs σC RC) (hFl : Fs.length = nF)
    (hmaj : As[mI]? = some (Fs.foldl app K)) :
    ∃ H Y, Denotes M.cval env φ ρ krl.rhs H ∧
      Denotes M.cval env φ (pushAll (As.take mI ++ Fs) ρ) b Y ∧
      As.foldl app (M.cval kr φ) = Y ∧
      CtxSat M φ (bs.map (·.1)).reverse (pushAll (As.take mI ++ Fs) ρ) := by
  -- the arguments: the prefix and the major
  have hdrop : As.drop mI = [Fs.foldl app K] := by
    rw [List.getElem?_eq_getElem (by omega)] at hmaj
    rw [List.drop_eq_getElem_cons (by omega), Option.some.inj hmaj,
      List.drop_eq_nil_of_le (by omega)]
  have hsplit : As = As.take mI ++ [Fs.foldl app K] := by rw [← hdrop, List.take_append_drop]
  have hxl : (As.take mI).length = mI := by simp; omega
  have hfit' := hfit
  rw [hsplit] at hfit'
  obtain ⟨σ1, R1, hf1, hf2⟩ := fits_append hfit'
  have hR1 : R1 = .forallE dom body m := by rw [fits_piBody hf1, hxl, hpb]
  subst hR1
  obtain ⟨X, hX, hKX⟩ : ∃ X, Denotes M.cval env φ σ1 dom X ∧ Fs.foldl app K ∈ˢ X := by
    cases hf2 with
    | cons hA hx _ => exact ⟨_, hA, hx⟩
  -- the fields' fit, its result the constructor's codomain (no index)
  obtain ⟨-, hRC, -⟩ := fits_piTele fbs Cc hFs (by omega)
  rw [show Fs.length = fbs.length by omega, List.drop_eq_nil_of_le (Nat.le_refl _)] at hRC
  have hRCe : RC = Cc := hRC
  -- ι at rule `krl`, at the recursor's own level parameters
  have hRden : Denotes M.cval env φ ρ (.const kr (cvr.levelParams.map .param)) (M.cval kr φ) := by
    have h1 : Denotes M.cval env φ ρ (.const kr (cvr.levelParams.map .param))
        (M.cval kr (Level.substFn φ cvr.levelParams (cvr.levelParams.map .param))) :=
      Denotes.const (ci := .recInfo cvr mI mI krules) hf (by simp [ConstantInfo.toConstantVal])
    rwa [substFn_self] at h1
  have hidx : DenotesList M.cval env φ σC (RC.getAppArgs.drop 0) ((As.take mI).drop mI) := by
    rw [hRCe, hcod, List.drop_eq_nil_of_le (as := As.take mI) (by omega)]
    exact .nil
  obtain ⟨H, hH, heq⟩ := hι kr cvr mI mI krules krl hf hkrl cvC 0 nF hcC
    (cvr.levelParams.map .param) φ ρ σ1 σC (As.take mI) Fs dom body RC m D ls (M.cval kr φ) K X
    (by simp) hxl (by omega) hRden (by rw [inst_self]; exact hf1) hdom hX hK
    (by rw [hcty]; exact hFs) hKX (by simp; exact .nil) hidx
  rw [inst_self] at hH
  -- β through the rule's right-hand side: its λ-domains are the type's prefix and the
  -- constructor's field domains lifted past it
  have hfitT : Fits M.cval env φ ρ (piTele tbs C) (As.take mI) σ1 (.forallE dom body m) := by
    rw [← hty]; exact hf1
  obtain ⟨e1, -, h3⟩ := fits_piTele tbs C hfitT (by omega)
  subst e1
  have hdropT : tbs.drop (As.take mI).length = [] := List.drop_eq_nil_of_le (by omega)
  have hcorr : TeleCorr M.cval env φ (pushAll (As.take mI) ρ) ρ (liftTele mI 0 fbs) fbs := by
    intro ys AL AP hL hP Y hY
    rw [liftTele_get, Nat.zero_add] at hL
    have h2 := hL.symm.trans (map_fst_get hP fun A => A.liftLooseBVars mI ys.length)
    obtain rfl := Option.some.inj h2
    have := (den_lift_block (cval := M.cval) (env := env) (φ := φ) (a := []) (b := As.take mI)
      (c := ys) (ρ := ρ) (e := AP) (X := Y)).mpr (by simpa using hY)
    rw [hxl] at this
    simpa [pushAll_append] using this
  have hfF := fits_transport (liftTele mI 0 fbs) fbs Cc Cc (liftTele_length _ _ _) hcorr hFs
    (by omega)
  have hfitAll : Fits M.cval env φ ρ (piTele (tbs ++ liftTele mI 0 fbs) Cc) (As.take mI ++ Fs)
      (pushAll Fs (pushAll (As.take mI) ρ))
      (piTele ((liftTele mI 0 fbs).drop Fs.length) Cc) := by
    rw [piTele_append]
    have h4 := h3 (piTele (liftTele mI 0 fbs) Cc)
    rw [hdropT] at h4
    exact fits_trans h4 hfF
  have hdoms : bs.map (·.1) = (tbs ++ liftTele mI 0 fbs).map (·.1) := by
    rw [← List.take_append_drop mI bs, List.map_append, hbs, hflds, List.map_append]
  have hall : (As.take mI ++ Fs).length = bs.length := by simp; omega
  rw [hrhs] at hH
  obtain ⟨Y, hY, hYe⟩ := lamTele_app_doms bs (tbs ++ liftTele mI 0 fbs) b Cc hdoms hH hfitAll hall
  have hctx := ctxSat_of_fits (M := M) (tbs ++ liftTele mI 0 fbs) Cc (Γ0 := []) .nil hfitAll
    (by rw [hall, ← List.length_map (f := (·.1)), hdoms, List.length_map])
  rw [List.append_nil, ← hdoms] at hctx
  refine ⟨H, Y, by rw [hrhs]; exact hH, hY, ?_, hctx⟩
  have e2 : (As.take mI).take mI ++ Fs.drop 0 = As.take mI ++ Fs := by
    rw [List.take_take, Nat.min_self, List.drop_zero]
  rw [e2] at heq
  have e3 : As.foldl app (M.cval kr φ) =
      (As.take mI ++ [Fs.foldl app K]).foldl app (M.cval kr φ) := by rw [← hsplit]
  rw [e3, heq, hYe]

/-! ## The constructor image at the recursor's levels -/

/-- **A constructor without level parameters**: built at any assignment `ψ` and environment, its
image is the constant's set at the recursor's assignment, and its fields fit its (closed) type
there. Laws: level-parameter irrelevance only (`Laws.cval_params`; `fits_inst` reads no other). -/
theorem ctorFields_noLevels (M : Model V env) (hL : LawsCore M) {c : KKey} {cvC : ConstantVal .anon}
    {nF : Nat} (hcC : env.find? c = some (.ctorInfo cvC 0 nF)) (hlp : cvC.levelParams = [])
    (hcl : bvarsLt 0 cvC.type = true) (hdef : cvC.type.allLevelParamsDefined [] = true)
    {φ ψ : LevelParam → Nat} {ρ ρc σc : BVarIdx → V} {Rc : KExpr} {Fs : List V}
    (hfit : Fits M.cval env ψ ρc cvC.type Fs σc Rc) :
    Denotes M.cval env φ ρ (.const c []) (M.cval c ψ) ∧
      ∃ σ R, Fits M.cval env φ ρ cvC.type Fs σ R := by
  refine ⟨ctorImage_noLevels M hL.cval_params hcC hlp φ ψ ρ, ?_⟩
  obtain ⟨σ2, hfit2⟩ := fits_agree hfit (ρ' := ρ) fun i hi =>
    absurd (lt_of_bvarsLt hcl hi) (Nat.not_lt_zero i)
  have h3 := fits_inst M hL (ks := []) (us := []) (φ := φ) (ψ := ψ) (fun _ hp => by simp at hp)
    hfit2 hdef
  have hi0 := inst_self ([] : List LevelParam) cvC.type
  simp only [List.map_nil] at hi0
  rw [hi0] at h3
  exact ⟨σ2, _, h3⟩

/-- **A constructor with level parameters**, by canonicity at the inductive, which the class asks
to be never a proposition: its image built at `ψ`, lying in the major domain's set, is the image at
the levels the major domain names, and its fields fit there. Laws: `Laws.ctor_canon` (restricted),
`Laws.cval_params`. No measured closure reaches it. -/
theorem ctorFields_canon (M : Model V env) (hL : LawsCore M) (hcc : CtorCanon M) {c D : KKey} {cvC : ConstantVal .anon}
    {nF : Nat} (hcC : env.find? c = some (.ctorInfo cvC 0 nF)) (hnd : cvC.levelParams.Nodup)
    (hcl : bvarsLt 0 cvC.type = true)
    (hdef : cvC.type.allLevelParamsDefined cvC.levelParams = true)
    (hhead : (piBody nF cvC.type).getAppFn = .const D (cvC.levelParams.map .param))
    (hN : NeverProp env D) {ls : List Level} (hls : cvC.levelParams.length = ls.length)
    {φ ψ : LevelParam → Nat} {ρ ρc σc τ : BVarIdx → V} {Rc dom : KExpr} {Fs : List V} {X : V}
    (hfit : Fits M.cval env ψ ρc cvC.type Fs σc Rc) (hFl : Fs.length = nF)
    (hdom : dom.getAppFn = .const D ls) (hX : Denotes M.cval env φ τ dom X)
    (hm : Fs.foldl app (M.cval c ψ) ∈ˢ X) :
    ∃ K, Denotes M.cval env φ ρ (.const c ls) K ∧ Fs.foldl app (M.cval c ψ) = Fs.foldl app K ∧
      ∃ σ R, Fits M.cval env φ ρ (cvC.type.instantiateLevelParams cvC.levelParams ls) Fs σ R := by
  obtain ⟨ls'', hls''⟩ : ∃ ls'' : List Level,
      ls'' = cvC.levelParams.map fun q => lvlOf (ψ q) := ⟨_, rfl⟩
  have hψ : ∀ q ∈ cvC.levelParams, Level.substFn φ cvC.levelParams ls'' q = ψ q := by
    intro q hq
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hq
    rw [substFn_at φ cvC.levelParams ls'' i q (lvlOf (ψ q)) hnd hi
      (by rw [hls'', List.getElem?_map, hi]; rfl), eval_lvlOf]
  have hK' : Denotes M.cval env φ ρ (.const c ls'') (M.cval c ψ) := by
    have h1 : Denotes M.cval env φ ρ (.const c ls'')
        (M.cval c (Level.substFn φ cvC.levelParams ls'')) :=
      Denotes.const (ci := .ctorInfo cvC 0 nF) hcC (by rw [hls'', List.length_map]; rfl)
    rwa [hL.cval_params _ _ hcC (Level.substFn φ cvC.levelParams ls'') ψ
      fun q hq => hψ q hq] at h1
  have hK : Denotes M.cval env φ ρ (.const c ls)
      (M.cval c (Level.substFn φ cvC.levelParams ls)) :=
    Denotes.const (ci := .ctorInfo cvC 0 nF) hcC (by rw [← hls]; rfl)
  obtain ⟨σ2, hfit2⟩ := fits_agree hfit (ρ' := ρ) fun i hi =>
    absurd (lt_of_bvarsLt hcl hi) (Nat.not_lt_zero i)
  have hfit3 := fits_inst M hL hψ hfit2 hdef
  have hR'head : (Rc.instantiateLevelParams cvC.levelParams ls'').getAppFn = .const D ls'' := by
    rw [getAppFn_inst, fits_piBody hfit2, hFl, hhead]
    simp only [Expr.instantiateLevelParams]
    rw [subst_params hnd (by rw [hls'', List.length_map])]
  -- canonicity at `D`, which is never a proposition
  obtain ⟨cvD, capsD, sD, hfD, hsD, hnvD⟩ := hN
  obtain ⟨heqK, σ3, R3, hFC⟩ := hcc c cvC 0 nF hcC D cvD capsD sD ls ls'' φ ρ τ σ2 dom
    _ [] [] Fs _ _ X hfD hsD (eval_ne_zero_of_never hnvD _) (eval_ne_zero_of_never hnvD _) rfl rfl
    hFl hK hK' (by simpa using hfit3) hR'head hdom hX (by simp; exact .nil) (by simpa using hm)
  exact ⟨_, hK, by simpa using heqK, σ3, R3, by simpa using hFC⟩

end Sem

end IxCC.Grounding
