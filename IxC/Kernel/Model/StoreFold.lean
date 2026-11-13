module

public import IxC.Kernel.Model.Open.StoredFacts
public import IxC.Kernel.Model.ClaimsJ
public import IxC.Kernel.Model.JudgeRules
public import IxC.Kernel.Model.Inductives.NativeJudge
public import IxC.Kernel.Semantics.DeclJ
public import IxC.Kernel.Semantics.Decl
public import IxC.Kernel.Semantics.DeclIndJ
public import IxC.Kernel.Semantics.EnvFacts
public import IxC.Kernel.Semantics.IndBlockFacts
public import IxC.Kernel.Semantics.IndBlockRun
public import IxC.Kernel.Semantics.Inductives.DeclNativeJ
public import IxC.Kernel.Semantics.Inductives.DeclSumEta
public import IxC.Kernel.Verify.Extend.Recs
public import IxC.Kernel.Verify.Extend.Sibs
public import IxC.Kernel.Verify.Extend.Iota
public import IxC.Kernel.Verify.Denote.Install
public import IxC.Kernel.Verify.Inductives.SumWF
public import IxC.Kernel.Verify.Inductives.SumRec
public import IxC.Kernel.Verify.Inductives.StructWF
public import IxC.Kernel.Verify.Inductives.FixParts
public import IxC.Kernel.Verify.InferLemmas
/- `Ix.Kernel.PropWhen` seals its representation; the pinned blocks' facts are decided by
evaluating terms that carry it, so `import all` gives that view HERE only. -/
import all IxC.Kernel.PropWhen

@[expose] public section

/-!
# The store invariant, kept by every declaration step with no model

`StoreInv env` (`Model/Open/StoredFacts.lean`) is the conjunction of the three syntactic
invariants of the stored constants: `EnvWF` (every stored constant is well formed),
`RecCtorsStored` (every rule of a stored recursor is recorded against its stored constructor,
its two rescue bits the store's verdict) and `ProjOkT` (every stored projection table carries
its head data). This file proves that every step of a declaration run over a judgement package
whose annotations keep scoping (`JudgeFrames`) keeps it, from the empty environment on, and that
the run over derivations does (`storeFoldRoutes`, in the shape of `foldRulesRoutes`, so both
apply to one run):

* the value kinds (`storeInv_declDefnRunJ`, `storeInv_declThmRunJ`, `storeInv_declOpaqueRunJ`,
  `storeInv_declAxiomRunJ`): a fresh checked constant, its type (and a definition's value)
  closed;
* the basis blocks and the quotient (`storeInv_basis`): the pinned declarations' well-formedness
  and recursor rules decided once per kind (`basis_decided`) against the block itself (and `Eq`
  for the quotient), then read at the installed environment;
* the three inductive routes (`storeInv_indRoutesJ`): the native route
  (`storeInv_declNativeRunJ`: the former, the constructors, the recursor with its generated rules,
  the projection table at a structure-like block), the native route without a recursor
  (`storeInv_declNativeNoRecRunJ`) and the modeled route (`storeInv_declIndRunJ`: the members, the
  provisioned recursors, the rules' syntactic facts `RuleFactsS` and the group swap).

Nothing here reads a valuation or a model: the facts are the records' own guards, the
annotations' scoping, and lookups.
-/

namespace Ix.Kernel.Model

open Ix.Kernel.Semantics
open Ix.Kernel.Open (StoreInv)
open Ix.Kernel (Env Key Expr Level LevelParam ConstantInfo ConstantVal RecRule RecRuleFire
  Declaration BasisKind IndCaps InductiveShape NativeParts RecFieldKind)

/-! ## A fresh head -/

/-- A checked type's four facts, at a package whose annotations keep scoping. -/
theorem typeFacts_of_runJ {J : Judgements md} {env : Env md} (hfr : JudgeFrames J env)
    {cv : ConstantVal md} {type' : Expr md} (h : ConstantValRunJ J env cv type') :
    type'.hasFvar = false ∧ type'.allLevelParamsDefined cv.levelParams = true ∧
      type'.constsResolve env = true ∧ type'.looseBVarsBounded 0 = true := by
  obtain ⟨-, -, -, -, hlb, hfv, hann, hlp, hcr, -⟩ := h
  obtain ⟨h1, h2⟩ := hfr.annot_syntax hann hfv hlb
  exact ⟨h1, hlp, hcr, h2⟩

/-- A checked value's four facts, at a package whose annotations keep scoping. -/
theorem valueFacts_of_runJ {J : Judgements md} {env : Env md} (hfr : JudgeFrames J env)
    {cv : ConstantVal md} {value type' value' : Expr md}
    (h : ValueFrontRunJ J env cv value type' value') :
    value'.hasFvar = false ∧ value'.allLevelParamsDefined cv.levelParams = true ∧
      value'.constsResolve env = true ∧ value'.looseBVarsBounded 0 = true := by
  obtain ⟨hlb, hfv, hann, hlp, hcr, -⟩ := h
  obtain ⟨h1, h2⟩ := hfr.annot_syntax hann hfv hlb
  exact ⟨h1, hlp, hcr, h2⟩

/-- **A fresh well-formed constant that is neither a recursor nor a projection table keeps the
store invariant.** -/
theorem storeInv_cons {env : Env md} {c : ConstantInfo md} (h : StoreInv env)
    (hfresh : env.find? c.name = none) (hwf : Ix.Kernel.ConstWF ⟨c :: env.consts⟩ c)
    (hrec : ∀ cv mI rP rules, c ≠ .recInfo cv mI rP rules)
    (hproj : ∀ tbl, c ≠ .projInfo tbl) : StoreInv ⟨c :: env.consts⟩ :=
  ⟨Ix.Kernel.EnvWF.cons h.wf hwf,
    Ix.Kernel.RecCtorsStored.cons h.rec_ctors hfresh
      (fun cv mI rP rules heq => absurd heq (hrec cv mI rP rules)),
    Ix.Kernel.Verify.ProjOkT.cons h.proj_ok hfresh (fun tbl heq => absurd heq (hproj tbl))⟩

/-- **A fresh checked constant with no rule and no table keeps the store invariant**: its type
closed at the environment (and its value, at a definition), its capability arities. -/
theorem storeInv_consTyped {env : Env md} {c : ConstantInfo md} (h : StoreInv env)
    (hfresh : env.find? c.name = none)
    (hty : c.toConstantVal.type.hasFvar = false ∧
      c.toConstantVal.type.allLevelParamsDefined c.toConstantVal.levelParams = true ∧
      c.toConstantVal.type.constsResolve env = true ∧
      c.toConstantVal.type.looseBVarsBounded 0 = true)
    (hval : ∀ cv value hint, c = .defnInfo cv value hint →
      value.hasFvar = false ∧ value.allLevelParamsDefined cv.levelParams = true ∧
      value.constsResolve env = true ∧ value.looseBVarsBounded 0 = true)
    (hrec : ∀ cv mI rP rules, c ≠ .recInfo cv mI rP rules)
    (hproj : ∀ tbl, c ≠ .projInfo tbl) (hcaps : Ix.Kernel.IndCapsWF c) :
    StoreInv ⟨c :: env.consts⟩ := by
  obtain ⟨h1, h2, h3, h4⟩ := hty
  refine storeInv_cons h hfresh
    (Ix.Kernel.structConstWF h1 h2 (Ix.Kernel.Expr.constsResolve_mono h3) h4 ?_ ?_ ?_ hcaps)
    hrec hproj
  · intro cv value hint heq
    obtain ⟨v1, v2, v3, v4⟩ := hval cv value hint heq
    exact ⟨v1, v2, Ix.Kernel.Expr.constsResolve_mono v3, v4⟩
  · intro cv mI rP rules heq
    exact absurd heq (hrec cv mI rP rules)
  · intro tbl heq
    exact absurd heq (hproj tbl)

/-- **A fresh recursor without rules keeps the store invariant** (the modeled route's
provisioning). -/
theorem storeInv_consRecNil {env : Env md} {cv : ConstantVal md} {mI rP : Nat}
    (h : StoreInv env) (hfresh : env.find? cv.name = none)
    (hty : cv.type.hasFvar = false ∧ cv.type.allLevelParamsDefined cv.levelParams = true ∧
      cv.type.constsResolve env = true ∧ cv.type.looseBVarsBounded 0 = true) :
    StoreInv ⟨.recInfo cv mI rP [] :: env.consts⟩ := by
  obtain ⟨h1, h2, h3, h4⟩ := hty
  refine ⟨Ix.Kernel.EnvWF.cons h.wf (Ix.Kernel.structConstWF (c := .recInfo cv mI rP [])
      h1 h2 (Ix.Kernel.Expr.constsResolve_mono h3) h4 (fun _ _ _ heq => nomatch heq) ?_),
    Ix.Kernel.RecCtorsStored.cons h.rec_ctors hfresh ?_,
    Ix.Kernel.Verify.ProjOkT.cons h.proj_ok hfresh (fun _ heq => nomatch heq)⟩
  · intro cv' mI' rP' rules heq r hr
    injection heq with _ _ _ e4
    subst e4
    exact nomatch hr
  · intro cv' mI' rP' rules heq r hr
    injection heq with _ _ _ e4
    subst e4
    exact nomatch hr

/-- `ConstWF` survives any extension that keeps the stored names. -/
theorem constWF_mono {env env' : Env md}
    (hf : ∀ n, (env.find? n).isSome = true → (env'.find? n).isSome = true)
    {c : ConstantInfo md} (h : Ix.Kernel.ConstWF env c) : Ix.Kernel.ConstWF env' c := by
  have hres : ∀ {e : Expr md}, e.constsResolve env = true → e.constsResolve env' = true :=
    Ix.Kernel.Expr.constsResolve_le hf
  obtain ⟨h1, h2, h3, h4, h5, h6, h8, h9⟩ := h
  refine ⟨h1, h2, hres h3, h4, fun cv value hint heq =>
    let ⟨g1, g2, g3, g4⟩ := h5 cv value hint heq
    ⟨g1, g2, hres g3, g4⟩, ?_,
    fun tbl heq =>
      let ⟨g0, g⟩ := h8 tbl heq
      ⟨g0, fun i b hb =>
        let ⟨g1, g2, g3, g4⟩ := g i b hb
        ⟨g1, g2, hres g3, g4⟩⟩, h9⟩
  intro cv mI rP rules heq r hr
  obtain ⟨g1, g2, g3, g4, g5⟩ := h6 cv mI rP rules heq r hr
  refine ⟨g1, g2, hres g3, g4, ?_⟩
  intro lvls pins hfr
  obtain ⟨n1, n2, n3, n4⟩ := g5 lvls pins hfr
  exact ⟨n1, n2, fun pin hpin =>
    let ⟨p1, p2, p3, p4⟩ := n3 pin hpin
    ⟨p1, p2, hres p3, p4⟩, n4⟩

/-! ## The value kinds -/

theorem storeInv_declDefnRunJ {J : Judgements md} {env env₂ : Env md}
    (hfr : JudgeFrames J env) (h : StoreInv env) {cv : ConstantVal md} {value : Expr md}
    {hint : Ix.Kernel.ReducibilityHint} (hrun : DeclDefnRunJ J env cv value hint env₂) :
    StoreInv env₂ := by
  obtain ⟨type', value', hcv, hvfr, rfl, -, -⟩ := hrun
  refine storeInv_consTyped h (Option.isNone_iff_eq_none.mp hcv.1)
      (typeFacts_of_runJ (cv := cv) hfr hcv)
    ?_ (fun _ _ _ _ heq => nomatch heq) (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
  intro cv' v hint' heq
  injection heq with e1 e2 _
  subst e1 e2
  exact valueFacts_of_runJ hfr hvfr

theorem storeInv_declThmRunJ {J : Judgements md} {env env₂ : Env md}
    (hfr : JudgeFrames J env) (h : StoreInv env) {cv : ConstantVal md} {value : Expr md}
    (hrun : DeclThmRunJ J env cv value env₂) : StoreInv env₂ := by
  obtain ⟨type', value', hcv, -, -, rfl⟩ := hrun
  exact storeInv_consTyped h (Option.isNone_iff_eq_none.mp hcv.1)
      (typeFacts_of_runJ (cv := cv) hfr hcv)
    (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq) (fun _ heq => nomatch heq)
    (fun _ _ heq => nomatch heq)

theorem storeInv_declOpaqueRunJ {J : Judgements md} {env env₂ : Env md}
    (hfr : JudgeFrames J env) (h : StoreInv env) {cv : ConstantVal md} {value : Expr md}
    (hrun : DeclOpaqueRunJ J env cv value env₂) : StoreInv env₂ := by
  obtain ⟨type', value', hcv, -, rfl⟩ := hrun
  exact storeInv_consTyped h (Option.isNone_iff_eq_none.mp hcv.1)
      (typeFacts_of_runJ (cv := cv) hfr hcv)
    (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq) (fun _ heq => nomatch heq)
    (fun _ _ heq => nomatch heq)

theorem storeInv_declAxiomRunJ {J : Judgements md} {env env₂ : Env md}
    (hfr : JudgeFrames J env) (h : StoreInv env) {cv : ConstantVal md}
    (hrun : DeclAxiomRunJ J env cv env₂) : StoreInv env₂ := by
  rcases hrun with ⟨-, rfl⟩ | ⟨type', hcv, ⟨-, rfl⟩ | ⟨-, -, -, -, rfl⟩⟩
  · exact h
  · exact storeInv_consTyped h (Option.isNone_iff_eq_none.mp hcv.1)
      (typeFacts_of_runJ (cv := cv) hfr hcv)
      (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
      (fun _ heq => nomatch heq) (fun _ _ heq => nomatch heq)
  · exact h

/-! ## The basis blocks

A basis block installs pinned declarations. Their well-formedness and their recursor rules are
decided once per kind against the block's own constants (`basis_decided`), then read at the
installed environment: the block's names are found there, and so is `Eq` before the quotient's
block (`DeclBasisRun`'s premise). -/

/-- The four facts of a closed term, decided against a resolution environment. -/
def closedIn (E : Env md) (lps : List LevelParam) (e : Expr md) : Bool :=
  !e.hasFvar && e.allLevelParamsDefined lps && e.constsResolve E && e.looseBVarsBounded 0

theorem closedIn_sound {E env : Env md}
    (hE : ∀ n, (E.find? n).isSome = true → (env.find? n).isSome = true)
    {lps : List LevelParam} {e : Expr md} (h : closedIn E lps e = true) :
    e.hasFvar = false ∧ e.allLevelParamsDefined lps = true ∧ e.constsResolve env = true ∧
      e.looseBVarsBounded 0 = true := by
  simp only [closedIn, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, Ix.Kernel.Expr.constsResolve_le hE h3, h4⟩

/-- A rule mode is `.plain`. -/
def firePlain : RecRuleFire md → Bool
  | .plain => true
  | _ => false

theorem eq_plain_of_firePlain : ∀ {f : RecRuleFire md}, firePlain f = true → f = .plain
  | .plain, _ => rfl
  | .inert, h => by simp [firePlain] at h
  | .nested _ _, h => by simp [firePlain] at h

/-- A pinned constant's well-formedness, decided against a resolution environment: its type
closed (and a definition's value), a recursor's rules canonical with closed right-hand sides,
no projection table, and the capability arities. -/
def basisWFb (E : Env md) : ConstantInfo md → Bool
  | .axiomInfo cv => closedIn E cv.levelParams cv.type
  | .defnInfo cv v _ => closedIn E cv.levelParams cv.type && closedIn E cv.levelParams v
  | .thmInfo cv _ => closedIn E cv.levelParams cv.type
  | .indInfo cv caps => closedIn E cv.levelParams cv.type &&
      (!caps.unitlike || (cv.type.stripPis caps.unitParams).isSome) &&
      (!caps.eta || (cv.type.stripPis caps.etaParams).isSome)
  | .ctorInfo cv _ _ => closedIn E cv.levelParams cv.type
  | .recInfo cv _ _ rules => closedIn E cv.levelParams cv.type &&
      rules.all fun r => closedIn E cv.levelParams r.rhs && firePlain r.fire
  | .projInfo _ => false

theorem constWF_of_basisWFb {E env : Env md}
    (hE : ∀ n, (E.find? n).isSome = true → (env.find? n).isSome = true) :
    ∀ {c : ConstantInfo md}, basisWFb E c = true → Ix.Kernel.ConstWF env c
  | .axiomInfo cv, h => by
    simp only [basisWFb] at h
    obtain ⟨h1, h2, h3, h4⟩ := closedIn_sound hE h
    exact Ix.Kernel.structConstWF (c := .axiomInfo cv) h1 h2 h3 h4
      (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
  | .defnInfo cv v hint, h => by
    simp only [basisWFb, Bool.and_eq_true] at h
    obtain ⟨h1, h2, h3, h4⟩ := closedIn_sound hE h.1
    obtain ⟨v1, v2, v3, v4⟩ := closedIn_sound hE h.2
    refine Ix.Kernel.structConstWF (c := .defnInfo cv v hint) h1 h2 h3 h4 ?_
      (fun _ _ _ _ heq => nomatch heq)
    intro cv' v' hint' heq
    injection heq with e1 e2 _
    subst e1 e2
    exact ⟨v1, v2, v3, v4⟩
  | .thmInfo cv v, h => by
    simp only [basisWFb] at h
    obtain ⟨h1, h2, h3, h4⟩ := closedIn_sound hE h
    exact Ix.Kernel.structConstWF (c := .thmInfo cv v) h1 h2 h3 h4
      (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
  | .indInfo cv caps, h => by
    simp only [basisWFb, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true] at h
    obtain ⟨⟨hc, hu⟩, he⟩ := h
    obtain ⟨h1, h2, h3, h4⟩ := closedIn_sound hE hc
    refine Ix.Kernel.structConstWF (c := .indInfo cv caps) h1 h2 h3 h4
      (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq) (fun _ heq => nomatch heq)
      (Ix.Kernel.IndCapsWF.of_caps ?_ ?_)
    · intro hU
      rcases hu with hu | hu
      · rw [hU] at hu; cases hu
      · exact hu
    · intro hE'
      rcases he with he | he
      · rw [hE'] at he; cases he
      · exact he
  | .ctorInfo cv nP nF, h => by
    simp only [basisWFb] at h
    obtain ⟨h1, h2, h3, h4⟩ := closedIn_sound hE h
    exact Ix.Kernel.structConstWF (c := .ctorInfo cv nP nF) h1 h2 h3 h4
      (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
  | .recInfo cv mI rP rules, h => by
    simp only [basisWFb, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨hc, hr⟩ := h
    obtain ⟨h1, h2, h3, h4⟩ := closedIn_sound hE hc
    refine Ix.Kernel.structConstWF (c := .recInfo cv mI rP rules) h1 h2 h3 h4
      (fun _ _ _ heq => nomatch heq) ?_
    intro cv' mI' rP' rules' heq r hr'
    injection heq with e1 e2 e3 e4
    subst e1 e2 e3 e4
    obtain ⟨hrc, hpl⟩ := hr r hr'
    obtain ⟨r1, r2, r3, r4⟩ := closedIn_sound hE hrc
    refine ⟨r1, r2, r3, r4, fun lvls pins hfire => ?_⟩
    rw [eq_plain_of_firePlain hpl] at hfire
    exact nomatch hfire
  | .projInfo _, h => by simp [basisWFb] at h

/-- A pinned recursor's rules against a store, decided: each canonical, at a stored constructor
with the rule's counts and the canonical major premise, its two rescue bits the store's verdict
at `n`. -/
def basisRulesb (F : Env md) (n : Key md) : ConstantInfo md → Bool
  | .recInfo cv mI rP rules => rules.all fun r =>
      firePlain r.fire &&
      (match F.find? r.ctor with
        | some (.ctorInfo cvj cnP cnF) =>
          cnP == r.ctorParams && cnF == r.nfields &&
            Ix.Kernel.Expr.recRulePlain cv.type mI rP r.ctorParams cvj.levelParams &&
            Ix.Kernel.Expr.ctorTeleOk cvj.type (r.ctorParams + r.nfields)
        | _ => false) &&
      (!r.k || Ix.Kernel.recRuleKOf F.find? r.ctor) &&
      (!r.eta || Ix.Kernel.recRuleEtaOf F.find? n r.ctor)
  | _ => true

theorem basisRulesb_sound {F : Env md} {n : Key md} {cv : ConstantVal md} {mI rP : Nat}
    {rules : List (RecRule md)} (h : basisRulesb F n (.recInfo cv mI rP rules) = true) :
    ∀ r ∈ rules, Ix.Kernel.RuleCtorOk F.find? cv mI rP r ∧
      (r.k = true → Ix.Kernel.recRuleKOf F.find? r.ctor = true) ∧
      (r.eta = true → Ix.Kernel.recRuleEtaOf F.find? n r.ctor = true) := by
  intro r hr
  simp only [basisRulesb, List.all_eq_true] at h
  have h' := h r hr
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h'
  obtain ⟨⟨⟨hpl, hct⟩, hk⟩, he⟩ := h'
  refine ⟨?_, fun hK => ?_, fun hE => ?_⟩
  · have hfire := eq_plain_of_firePlain hpl
    revert hct
    split
    · next cvj cnP cnF hf =>
      intro hct
      simp only [Bool.and_eq_true, beq_iff_eq] at hct
      obtain ⟨⟨⟨rfl, rfl⟩, hpl'⟩, htele⟩ := hct
      exact Ix.Kernel.RuleCtorOk.of_plain hf hfire hpl' htele
    · intro hct
      exact absurd hct (by simp)
  · rcases hk with hk | hk
    · rw [hK] at hk; cases hk
    · exact hk
  · rcases he with he | he
    · rw [hE] at he; cases he
    · exact he

/-- `find?` on a prefixed constant list. -/
theorem find?_prefix (l : List (ConstantInfo md)) (env : Env md) (n : Key md) :
    Env.find? ⟨l ++ env.consts⟩ n = (Env.find? ⟨l⟩ n).or (env.find? n) := by
  simp only [Env.find?, List.find?_append]

/-- `find?` on two appended constant lists. -/
theorem find?_lists (l₁ l₂ : List (ConstantInfo md)) (n : Key md) :
    Env.find? ⟨l₁ ++ l₂⟩ n = (Env.find? ⟨l₁⟩ n).or (Env.find? ⟨l₂⟩ n) := by
  simp only [Env.find?, List.find?_append]

/-- **A basis install conses its declarations in order**, each fresh before the block. -/
theorem basisInstallRun_eq :
    ∀ {ds : List (ConstantInfo md)} {env env₂ : Env md}, BasisInstallRun env ds env₂ →
      env₂ = ⟨ds.reverse ++ env.consts⟩ ∧ ∀ c ∈ ds, env.find? c.name = none
  | [], env, env₂, h => by
    have h' : env₂ = env := h
    subst h'
    exact ⟨rfl, fun _ hc => nomatch hc⟩
  | ci :: rest, env, env₂, h => by
    obtain ⟨hfresh, hrest⟩ := h
    obtain ⟨rfl, hf⟩ := basisInstallRun_eq hrest
    refine ⟨by simp, fun c hc => ?_⟩
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact Option.isNone_iff_eq_none.mp hfresh
    · have h1 := hf c hc'
      rw [Ix.Kernel.Env.find?_cons] at h1
      split at h1
      · exact nomatch h1
      · exact h1

/-- **A basis install keeps the store invariant**, given its declarations' decided facts against
the block (and the extra constants the block's terms name, stored before it). -/
theorem storeInv_basisInstall {env env₂ : Env md} {ds extra : List (ConstantInfo md)}
    (h : StoreInv env) (hrun : BasisInstallRun env ds env₂)
    (hdec : ∀ c ∈ ds, basisWFb ⟨ds.reverse ++ extra⟩ c = true ∧
      basisRulesb ⟨ds.reverse⟩ c.name c = true)
    (hextra : ∀ c ∈ extra, (env.find? c.name).isSome = true) : StoreInv env₂ := by
  obtain ⟨rfl, hfresh⟩ := basisInstallRun_eq hrun
  have hblock : ∀ n ci, Env.find? ⟨ds.reverse⟩ n = some ci →
      Env.find? ⟨ds.reverse ++ env.consts⟩ n = some ci := by
    intro n ci hf
    rw [find?_prefix, hf]
    rfl
  have hold : ∀ n ci, env.find? n = some ci →
      Env.find? ⟨ds.reverse ++ env.consts⟩ n = some ci := by
    intro n ci hf
    rw [find?_prefix]
    cases hb : Env.find? ⟨ds.reverse⟩ n with
    | none => simpa using hf
    | some ci' =>
      exfalso
      have hmem : ci' ∈ ds := List.mem_reverse.mp (Ix.Kernel.Semantics.Env.find?_mem hb)
      have hname : ci'.name = n := Ix.Kernel.Semantics.Env.find?_name hb
      rw [← hname, hfresh ci' hmem] at hf
      exact nomatch hf
  have hgrow : ∀ n, (env.find? n).isSome = true →
      (Env.find? ⟨ds.reverse ++ env.consts⟩ n).isSome = true := by
    intro n hn
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn
    rw [hold n ci hci]
    rfl
  have hE : ∀ n, (Env.find? ⟨ds.reverse ++ extra⟩ n).isSome = true →
      (Env.find? ⟨ds.reverse ++ env.consts⟩ n).isSome = true := by
    intro n hn
    rw [find?_lists] at hn
    cases hb : Env.find? ⟨ds.reverse⟩ n with
    | some ci =>
      rw [hblock n ci hb]
      rfl
    | none =>
      rw [hb, Option.none_or] at hn
      obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn
      have hmem : ci ∈ extra := Ix.Kernel.Semantics.Env.find?_mem hci
      have hname : ci.name = n := Ix.Kernel.Semantics.Env.find?_name hci
      exact hgrow n (hname ▸ hextra ci hmem)
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact constWF_of_basisWFb hE (hdec c (List.mem_reverse.mp hc)).1
    · exact constWF_mono hgrow (h.wf c hc)
  · intro n cv mI rP rules hf r hr
    rw [find?_prefix] at hf
    cases hb : Env.find? ⟨ds.reverse⟩ n with
    | some ci =>
      rw [hb, Option.some_or] at hf
      obtain rfl := Option.some.inj hf
      have hmem := List.mem_reverse.mp (Ix.Kernel.Semantics.Env.find?_mem hb)
      have hname := Ix.Kernel.Semantics.Env.find?_name hb
      obtain ⟨hco, hk, he⟩ := basisRulesb_sound (hdec _ hmem).2 r hr
      have hkeep : ∀ (m : Key md) (ci' : ConstantInfo md),
          (∀ cv mI rP rules, ci' ≠ .recInfo cv mI rP rules) →
          Env.find? ⟨ds.reverse⟩ m = some ci' →
          Env.find? ⟨ds.reverse ++ env.consts⟩ m = some ci' :=
        fun m ci' _ hf' => hblock m ci' hf'
      refine ⟨hco.mono hkeep, fun hK => Ix.Kernel.recRuleKOf_mono hkeep (hk hK), fun hE' => ?_⟩
      rw [← hname]
      exact Ix.Kernel.recRuleEtaOf_mono hkeep (he hE')
    | none =>
      rw [hb, Option.none_or] at hf
      obtain ⟨hco, hk, he⟩ := h.rec_ctors n cv mI rP rules hf r hr
      have hkeep : ∀ (m : Key md) (ci' : ConstantInfo md),
          (∀ cv mI rP rules, ci' ≠ .recInfo cv mI rP rules) →
          env.find? m = some ci' → Env.find? ⟨ds.reverse ++ env.consts⟩ m = some ci' :=
        fun m ci' _ hf' => hold m ci' hf'
      exact ⟨hco.mono hkeep, fun hK => Ix.Kernel.recRuleKOf_mono hkeep (hk hK),
        fun hE' => Ix.Kernel.recRuleEtaOf_mono hkeep (he hE')⟩
  · intro n tbl hf i hi
    rw [find?_prefix] at hf
    cases hb : Env.find? ⟨ds.reverse⟩ n with
    | some ci =>
      rw [hb, Option.some_or] at hf
      obtain rfl := Option.some.inj hf
      have hmem := List.mem_reverse.mp (Ix.Kernel.Semantics.Env.find?_mem hb)
      have hwfb := (hdec _ hmem).1
      simp [basisWFb] at hwfb
    | none =>
      rw [hb, Option.none_or] at hf
      exact Ix.Kernel.TowerHead.mono (fun m ci' _ hf' => hold m ci' hf') (h.proj_ok n tbl hf i hi)

/-- The constants a basis block's terms name beyond the block: `Eq`, for the quotient's. -/
def basisExtra : BasisKind → List (ConstantInfo md)
  | .quotK => [Ix.Kernel.eqA]
  | _ => []

/-- **The pinned blocks' facts, decided**: every pinned declaration is well formed against its
block (and `Eq`, for the quotient), and every pinned recursor's rules are canonical, at a
constructor of the block, with their rescue bits the block's verdict. -/
theorem basis_decided (kind : BasisKind) :
    ∀ c ∈ kind.declsA (md := md),
      basisWFb ⟨kind.declsA.reverse ++ basisExtra kind⟩ c = true ∧
        basisRulesb ⟨kind.declsA.reverse⟩ c.name c = true := by
  cases kind <;> (cases md <;> decide +kernel)

/-- **A basis block keeps the store invariant.** -/
theorem storeInv_basis {env env₂ : Env md} {kind : BasisKind} (h : StoreInv env)
    (hrun : DeclBasisRun env kind env₂) : StoreInv env₂ := by
  obtain ⟨hEq, hinst⟩ := hrun
  refine storeInv_basisInstall h hinst (basis_decided kind) ?_
  intro c hc
  cases kind <;> simp only [basisExtra, List.mem_singleton, List.not_mem_nil] at hc
  subst hc
  show (env.find? Ix.Kernel.eqName).isSome = true
  rw [hEq rfl]
  rfl

/-! ## The modeled route -/

/-- **The syntactic facts of an installed rule**: `RuleFacts` without its reading of the
right-hand side, which the store invariant does not need. -/
def RuleFactsS (envSelf : Env md) (cv : ConstantVal md) (mI rP : Nat) (rl : RecRule md) :
    Prop :=
  (RecRule.rhs rl).hasFvar = false ∧
  (RecRule.rhs rl).allLevelParamsDefined cv.levelParams = true ∧
  (RecRule.rhs rl).constsResolve envSelf = true ∧
  (RecRule.rhs rl).looseBVarsBounded 0 = true ∧
  (∀ lvls pins, RecRule.fire rl = .nested lvls pins →
    rP ≤ mI ∧
    (∀ l ∈ lvls, l.allParamsDefined cv.levelParams = true) ∧
    (∀ pin ∈ pins, pin.hasFvar = false ∧
      pin.allLevelParamsDefined cv.levelParams = true ∧
      pin.constsResolve envSelf = true ∧
      pin.looseBVarsBounded rP = true) ∧
    ∃ pre dom body bm D,
      cv.type.stripPis mI = some (pre, .forallE dom body bm) ∧
      dom.getAppFn = .const D lvls ∧
      dom.getAppArgs =
        pins.map (Expr.liftLooseBVars (mI - rP) 0) ++
          (List.range (mI - rP)).map
            (fun i => Expr.bvar (mI - rP - 1 - i))) ∧
  Ix.Kernel.RuleCtorOk envSelf.find? cv mI rP rl ∧
  (rl.k = true → Ix.Kernel.recRuleKOf envSelf.find? rl.ctor = true) ∧
  (rl.eta = true → Ix.Kernel.recRuleEtaOf envSelf.find? cv.name rl.ctor = true)

/-- **Every rule the per-recursor fold returns carries its syntactic facts** — the model-free
half of `iotaRulesFactsRun`, with no reading premise. -/
theorem iotaRulesFactsSRun {J : Judgements md}
    {env₂ envSelf : Env md} {f : Key md → Key md}
    (hup : FoldUpS env₂ envSelf)
    (hsyn : ∀ {e e' : Expr md}, J.annot envSelf 0 e e' → e.hasFvar = false →
      e.looseBVarsBounded 0 = true → e'.hasFvar = false ∧ e'.looseBVarsBounded 0 = true)
    {cvA : ConstantVal md} {mI rP : Nat} :
    ∀ (j : Nat) (rules rules' : List (RecRule md)),
      IotaRulesRunJ J env₂ envSelf f cvA.name cvA.levelParams
        cvA.type mI rP j rules rules' →
      ∀ rl ∈ rules', RuleFactsS envSelf cvA mI rP rl := by
  intro j rules
  induction rules generalizing j with
  | nil =>
    intro rules' h rl hrl
    rw [h] at hrl
    exact nomatch hrl
  | cons r rest ih =>
    intro rules' h rl hrl
    obtain ⟨r', rest', hkit, hrec, rfl⟩ := h
    rcases List.mem_cons.mp hrl with heqrl | hrl'
    · rw [heqrl]
      obtain ⟨cvjK, cnPK, cnFK, rhsA, hfcK, hnfK, hrb, hrf, hann, hrlp,
        hrres, -, -, fire, hr'eq, hbranch⟩ := hkit
      have hr'rhs : RecRule.rhs r' = rhsA := by rw [hr'eq]; rfl
      have hr'ctor : RecRule.ctor r' = RecRule.ctor r := by rw [hr'eq]; rfl
      have hr'fire : RecRule.fire r' = fire := by rw [hr'eq]; rfl
      obtain ⟨hrhsAw, hrhsAb⟩ := hsyn hann hrf hrb
      have hfcS : envSelf.find? (RecRule.ctor r')
          = some (.ctorInfo cvjK cnPK cnFK) := by
        rw [hr'ctor]
        rcases hup _ _ hfcK with h' |
          ⟨cv, mI', rP', rules₀, rules₁, heq, -⟩
        · exact h'
        · exact nomatch heq
      have hkeep : ∀ (n : Key md) (ci : ConstantInfo md),
          (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
          env₂.find? n = some ci → envSelf.find? n = some ci := by
        intro n ci hnr hf
        rcases hup _ _ hf with h' | ⟨cv, mI', rP', rules₀, rules₁, heq, -⟩
        · exact h'
        · exact absurd heq (hnr _ _ _ _)
      refine ⟨by rw [hr'rhs]; exact hrhsAw, by rw [hr'rhs]; exact hrlp,
        by rw [hr'rhs]; exact hrres, by rw [hr'rhs]; exact hrhsAb, ?_,
        ?_, ?_, ?_⟩
      · -- the nested shape facts, from `nestedRuleShape`
        intro lvls pins hfireN
        rw [hr'fire] at hfireN
        rcases hbranch with ⟨-, hfireP, -⟩ | ⟨-, hrest⟩
        · rw [hfireP] at hfireN; exact nomatch hfireN
        obtain ⟨lvls₀, pins₀, hfireN₀, hthmN⟩ := hrest
        rw [hfireN₀] at hfireN
        obtain ⟨rfl, rfl⟩ := RecRuleFire.nested.inj hfireN
        obtain ⟨hshape, -⟩ := hthmN
        obtain ⟨hrPmI, hlvls, hpins, pre, dom, body, bm, D, hstrip,
          hfn, hargs, -⟩ := Ix.Kernel.nestedRuleShape_inv hshape
        exact ⟨hrPmI, hlvls, hpins, pre, dom, body, bm, D, hstrip,
          hfn, hargs⟩
      · -- the constructor's record: its counts, and the shape of the mode
        have hr'cp : RecRule.ctorParams r' = cnPK := by rw [hr'eq]; rfl
        have hr'nf : RecRule.nfields r' = cnFK := by rw [hr'eq]; exact hnfK
        refine ⟨cvjK, by rw [hr'cp, hr'nf]; exact hfcS, fun hp => ?_,
          fun lvls pins hfireN => ?_, ?_, ?_⟩
        · rw [hr'cp]
          rw [hr'fire] at hp
          rcases hbranch with ⟨hplain, -, -⟩ | ⟨-, hrest⟩
          · exact hplain
          obtain ⟨lvls₀, pins₀, hfireN₀, -⟩ := hrest
          rw [hfireN₀] at hp; exact nomatch hp
        · rw [hr'cp]
          rw [hr'fire] at hfireN
          rcases hbranch with ⟨-, hfireP, -⟩ | ⟨-, hrest⟩
          · rw [hfireP] at hfireN; exact nomatch hfireN
          obtain ⟨lvls₀, pins₀, hfireN₀, hthmN⟩ := hrest
          rw [hfireN₀] at hfireN
          obtain ⟨rfl, rfl⟩ := RecRuleFire.nested.inj hfireN
          obtain ⟨-, -, -, _, _, _, _, _, -, -, -, hlen⟩ :=
            Ix.Kernel.nestedRuleShape_inv hthmN.1
          exact hlen
        · rw [hr'fire]
          rcases hbranch with ⟨-, hfireP, -⟩ | ⟨-, lvls₀, pins₀, hfireN₀, -⟩
          · rw [hfireP]; exact fun h => nomatch h
          · rw [hfireN₀]; exact fun h => nomatch h
        · -- the constructor's telescope, which the rule's `iota` theorem opened
          rw [hr'cp, hr'nf]
          rcases hbranch with ⟨-, -, hthm⟩ | ⟨-, lvls₀, pins₀, -, hthmN⟩
          · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hsC, -⟩ := hthm
            exact hsC
          · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, ⟨cb, cb0, hsC, hmatch⟩, -⟩ :=
              hthmN
            split at hmatch
            · next c us hh => exact Ix.Kernel.Expr.ctorTeleOk_of hsC hh
            · exact nomatch hmatch
      · -- the K bit is the install's own lookup, moved to `envSelf`
        intro hb
        refine Ix.Kernel.recRuleKOf_mono hkeep ?_
        rw [hr'eq] at hb ⊢
        exact hb
      · -- the η-rescue bit, likewise
        intro hb
        refine Ix.Kernel.recRuleEtaOf_mono hkeep ?_
        rw [hr'eq] at hb ⊢
        exact hb
    · exact ih (j + 1) rest' hrec rl hrl'

/-- **The store invariant survives the group swap** — `swapEnvFacts`'s three syntactic
conclusions, from the rules' syntactic facts. -/
theorem swapStoreInv {envSelf env₃ : Env md} (hS : StoreInv envSelf)
    (hswR : Ix.Kernel.SwapShList envSelf.consts env₃.consts)
    (hentR : ∀ c ∈ env₃.consts, c ∈ envSelf.consts ∨
      ∃ (cv : ConstantVal md) (mI rP : Nat) (rules : List (RecRule md)),
        c = .recInfo cv mI rP rules ∧
        ∀ rl ∈ rules, RuleFactsS envSelf cv mI rP rl)
    (hentF : ∀ (n : Key md) (cv : ConstantVal md) (mI rP : Nat)
      (rules : List (RecRule md)),
      env₃.find? n = some (.recInfo cv mI rP rules) →
      envSelf.find? n = some (.recInfo cv mI rP rules) ∨
      ∀ rl ∈ rules, RuleFactsS envSelf cv mI rP rl) :
    StoreInv env₃ := by
  have hcg : Ix.Kernel.SwapCongr envSelf env₃ := Ix.Kernel.SwapShList.congr hswR
  have hcorr : ∀ n : Key md,
      env₃.find? n = envSelf.find? n ∨
      ∃ cv mI rP rules,
        envSelf.find? n = some (.recInfo cv mI rP []) ∧
        env₃.find? n = some (.recInfo cv mI rP rules) ∧
        cv.name = n := Ix.Kernel.swapSh_find?_corr hswR
  have hsame : ∀ (n : Key md) (ci : ConstantInfo md),
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      (env₃.find? n = some ci ↔ envSelf.find? n = some ci) :=
    fun n ci hnr =>
      ⟨fun h => hcg.findDown n ci h hnr, fun h => hcg.findUp n ci h hnr⟩
  have hres₃ : ∀ e : Expr md, e.constsResolve envSelf = true →
      e.constsResolve env₃ = true := by
    intro e he
    rw [← Ix.Kernel.Expr.constsResolve_congr hcg.isSomeEq]
    exact he
  refine ⟨?_, ?_, ?_⟩
  · -- `EnvWF`
    intro c hc
    rcases hentR c hc with hcS | ⟨cv, mI, rP, rules, rfl, hfacts⟩
    · obtain ⟨hSw, hSlp, hSres, hSb, hSdef, hSrec, hStbl, hScaps⟩ := hS.wf c hcS
      refine ⟨hSw, hSlp, hres₃ _ hSres, hSb, ?_, ?_, ?_, hScaps⟩
      · intro cv v hint heq
        obtain ⟨d1, d2, d3, d4⟩ := hSdef cv v hint heq
        exact ⟨d1, d2, hres₃ _ d3, d4⟩
      · intro cv mI rP rules heq r hr
        obtain ⟨r1, r2, r3, r4, r5⟩ := hSrec cv mI rP rules heq r hr
        refine ⟨r1, r2, hres₃ _ r3, r4, ?_⟩
        intro lvls pins hfr
        obtain ⟨n1, n2, n3, n4⟩ := r5 lvls pins hfr
        refine ⟨n1, n2, ?_, n4⟩
        intro pin hpin
        obtain ⟨p1, p2, p3, p4⟩ := n3 pin hpin
        exact ⟨p1, p2, hres₃ _ p3, p4⟩
      · intro tbl heq
        obtain ⟨g0, g⟩ := hStbl tbl heq
        refine ⟨g0, fun i b hb => ?_⟩
        obtain ⟨t1, t2, t3, t4⟩ := g i b hb
        exact ⟨t1, t2, hres₃ _ t3, t4⟩
    · obtain ⟨c₀, hc₀, hpair⟩ := Ix.Kernel.swapSh_mem_corr hswR _ hc
      obtain ⟨hSw, hSlp, hSres, hSb, -, -, -, -⟩ := hS.wf c₀ hc₀
      have hcvt : c₀.toConstantVal = cv := by
        rcases hpair with rfl | ⟨cv', mI', rP', rules', rfl, heq⟩
        · rfl
        · obtain ⟨rfl, -, -, -⟩ := ConstantInfo.recInfo.inj heq
          rfl
      rw [hcvt] at hSw hSlp hSres hSb
      refine ⟨hSw, hSlp, hres₃ _ hSres, hSb,
        fun _ _ _ hcon => ConstantInfo.noConfusion rfl (heq_of_eq hcon), ?_,
        fun _ hcon => ConstantInfo.noConfusion rfl (heq_of_eq hcon),
        fun _ _ hcon => ConstantInfo.noConfusion rfl (heq_of_eq hcon)⟩
      intro cv' mI' rP' rules' heq r hr
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ConstantInfo.recInfo.inj heq
      obtain ⟨w1, w2, w3, w4, w5, -, -⟩ := hfacts r hr
      refine ⟨w1, w2, hres₃ _ w3, w4, ?_⟩
      intro lvls pins hfr
      obtain ⟨n1, n2, n3, n4⟩ := w5 lvls pins hfr
      refine ⟨n1, n2, ?_, n4⟩
      intro pin hpin
      obtain ⟨p1, p2, p3, p4⟩ := n3 pin hpin
      exact ⟨p1, p2, hres₃ _ p3, p4⟩
  · -- `RecCtorsStored`
    intro n cv mI rP rules hf r hr
    have hkeep : ∀ (m : Key md) (ci : ConstantInfo md),
        (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
        envSelf.find? m = some ci → env₃.find? m = some ci :=
      fun m ci hnr hfc => hcg.findUp m ci hfc hnr
    rcases hentF n cv mI rP rules hf with hfS | hfacts
    · obtain ⟨hco, hk, he⟩ := hS.rec_ctors n cv mI rP rules hfS r hr
      exact ⟨hco.mono hkeep,
        fun hb => Ix.Kernel.recRuleKOf_mono hkeep (hk hb),
        fun hb => Ix.Kernel.recRuleEtaOf_mono hkeep (he hb)⟩
    · obtain ⟨-, -, -, -, -, hco, hk, he⟩ := hfacts r hr
      -- the swapped recursor is stored under its own constant's name
      have hnR : cv.name = n := by
        rcases hcorr n with heq | ⟨cv', mI', rP', rules', h₀, h₃, hn'⟩
        · rw [heq] at hf
          exact Ix.Kernel.Semantics.Env.find?_name hf
        · rw [h₃] at hf
          obtain ⟨rfl, -, -, -⟩ := ConstantInfo.recInfo.inj (Option.some.inj hf)
          exact hn'
      exact ⟨hco.mono hkeep,
        fun hb => Ix.Kernel.recRuleKOf_mono hkeep (hk hb),
        fun hb => Ix.Kernel.recRuleEtaOf_mono hkeep (hnR ▸ he hb)⟩
  · -- `ProjOkT`: projection tables are untouched
    intro n tbl hf i hi
    exact Ix.Kernel.TowerHead.mono (fun n ci hnr hf' => (hsame n ci hnr).mpr hf')
      (hS.proj_ok n tbl ((hsame _ _
        (fun _ _ _ _ h => ConstantInfo.noConfusion rfl (heq_of_eq h))).mp hf) i hi)

/-- **The block members keep the store invariant**, at a capability record with no flag. -/
theorem storeInv_indMembersRunJ {J : Judgements md} (hfr : ∀ e : Env md, JudgeFrames J e)
    {blockNames : List (Key md)} {caps : IndCaps md}
    (hcaps : caps.unitlike = false ∧ caps.eta = false) :
    ∀ (members : List (ConstantInfo md)) {env env₂ : Env md},
      IndMembersRunJ J blockNames caps env members env₂ → StoreInv env → StoreInv env₂
  | [], env, env₂, hrun, h => by
    have h' : env₂ = env := hrun
    subst h'
    exact h
  | ci :: rest, env, env₂, hrun, h => by
    obtain ⟨cvA, hmv, hrest⟩ := hrun
    obtain ⟨type', hcv, rfl, -⟩ := hmv
    have hty := typeFacts_of_runJ (hfr env) hcv
    have hfresh : env.find? ci.toConstantVal.name = none := Option.isNone_iff_eq_none.mp hcv.1
    cases ci with
    | indInfo cv caps' =>
      exact storeInv_indMembersRunJ hfr hcaps rest hrest
        (storeInv_consTyped h hfresh hty (fun _ _ _ heq => nomatch heq)
          (fun _ _ _ _ heq => nomatch heq) (fun _ heq => nomatch heq)
          (Ix.Kernel.IndCapsWF.of_caps (fun hu => absurd hu (by rw [hcaps.1]; decide))
            (fun he => absurd he (by rw [hcaps.2]; decide))))
    | ctorInfo cv nP nF =>
      exact storeInv_indMembersRunJ hfr hcaps rest hrest
        (storeInv_consTyped h hfresh hty (fun _ _ _ heq => nomatch heq)
          (fun _ _ _ _ heq => nomatch heq) (fun _ heq => nomatch heq)
          (fun _ _ heq => nomatch heq))
    | _ => exact (hrest : False).elim

/-- **The provisioning keeps the store invariant.** -/
theorem storeInv_provisionRecsRunJ {J : Judgements md} (hfr : ∀ e : Env md, JudgeFrames J e)
    {blockNames : List (Key md)} :
    ∀ (recs : List (ConstantInfo md)) {envAcc envSelf : Env md}
      {checked : List (ConstantVal md × Nat × Nat × List (RecRule md))},
      ProvisionRecsRunJ J blockNames envAcc recs envSelf checked →
      StoreInv envAcc → StoreInv envSelf
  | [], envAcc, envSelf, checked, hrun, h => by
    obtain ⟨rfl, -⟩ := hrun
    exact h
  | ci :: rest, envAcc, envSelf, checked, hrun, h => by
    obtain ⟨cvA, mI, rP, rules, rest', -, hmv, hrec, -⟩ := hrun
    obtain ⟨type', hcv, rfl, -⟩ := hmv
    exact storeInv_provisionRecsRunJ hfr rest hrec
      (storeInv_consRecNil h (Option.isNone_iff_eq_none.mp hcv.1)
        (typeFacts_of_runJ (cv := ci.toConstantVal) (hfr envAcc) hcv))

/-- **The recursor group keeps the store invariant**: the provisioning, the rules' syntactic
facts (`iotaRulesFactsSRun`), the group swap (`swapStoreInv`). -/
theorem storeInv_indRecsRunJ {J : Judgements md} (hfr : ∀ e : Env md, JudgeFrames J e)
    {blockNames : List (Key md)} {env₂ env₃ : Env md} {recs : List (ConstantInfo md)}
    (hbn : ∀ ci ∈ recs, blockNames.contains ci.name = true)
    (h : StoreInv env₂) (hrun : IndRecsRunJ J blockNames env₂ recs env₃) :
    StoreInv env₃ := by
  rcases hrun with ⟨-, rfl⟩ | ⟨-, heqf, envSelf, checked, hprov, hfold⟩
  · exact h
  have hS := storeInv_provisionRecsRunJ hfr recs hprov h
  obtain ⟨hswR, -, hentR, hentFR⟩ :=
    indRecsFoldFactsRun (RuleFactsS envSelf)
      (fun _cvA _mI _rP rules rules' _hbnA _hselfA hiot =>
        iotaRulesFactsSRun
          (fun n ci hf => Or.inl (provisionRecsRunS_mono recs hprov n ci hf))
          (hfr envSelf).annot_syntax 0 rules rules' hiot)
      recs (Ix.Kernel.SwapShList.of_eq env₂.consts)
      (SwapNResS.of_eq env₂)
      (fun n ci hf => Or.inl (provisionRecsRunS_mono recs hprov n ci hf))
      (provisionRecsRunS_mono recs hprov) heqf
      (fun c hc => Or.inl (provisionRecsRunS_mem recs hprov c hc))
      (fun n cv mI rP rules hf => Or.inl (provisionRecsRunS_mono recs hprov n _ hf))
      hbn hprov hfold
  exact swapStoreInv hS hswR hentR hentFR

/-- **The modeled route keeps the store invariant.** -/
theorem storeInv_declIndRunJ {J : Judgements md} (hfr : ∀ e : Env md, JudgeFrames J e)
    {env env₂ : Env md} {block : List (ConstantInfo md)} (h : StoreInv env)
    (hrun : DeclIndRunJ J env block env₂) : StoreInv env₂ := by
  obtain ⟨-, envM, hmem, hrecs⟩ := hrun
  have hbnRec : ∀ ci ∈ block.filter (fun ci => match ci with
      | .recInfo _ _ _ _ => true | _ => false),
      (block.map (·.name)).contains ci.name = true := by
    intro ci hci
    have hmm : ci.name ∈ block.map (·.name) := List.mem_map_of_mem (List.mem_filter.mp hci).1
    simpa using hmm
  exact storeInv_indRecsRunJ hfr hbnRec
    (storeInv_indMembersRunJ hfr ⟨rfl, rfl⟩ _ hmem h) hrecs

/-! ## The native routes -/

/-- The recogniser's facts the projection table's head data reads: the constructors are at the
family's level parameters, and neither the family nor a constructor is a reserved name. -/
def NativeRecog (p₀ : NativeParts md) : Prop :=
  (∀ c ∈ p₀.ctors, c.1.levelParams = p₀.cvT.levelParams ∧
    Ix.Kernel.reservedBasisNames.contains c.1.name = false) ∧
  Ix.Kernel.reservedBasisNames.contains p₀.cvT.name = false

theorem nativeRecog_of {nPd : Nat} {block : List (ConstantInfo md)} {p₀ : NativeParts md}
    (hdp : Ix.Kernel.nativeParts? nPd block = some p₀) : NativeRecog p₀ := by
  obtain ⟨hshape, -⟩ := Ix.Kernel.nativeParts?_inv hdp
  obtain ⟨-, hC, hT, -⟩ := Ix.Kernel.nativeShape?_inv hshape
  exact ⟨hC, hT⟩

theorem nativeRecog_noRec {nPd : Nat} {block : List (ConstantInfo md)} {p₀ : NativeParts md}
    (hdp : nativePartsNoRec? nPd block = some p₀) : NativeRecog p₀ := by
  unfold nativePartsNoRec? at hdp
  split at hdp
  · split at hdp
    · exact nativeRecog_of hdp
    · exact nomatch hdp
  · exact nomatch hdp

/-- The capability record's arities are the parameter count. -/
theorem nativeCapsAt_params (q : InductiveShape md) (isRec : Bool) :
    ((Ix.Kernel.nativeCapsAt q isRec).unitlike = true →
      (Ix.Kernel.nativeCapsAt q isRec).unitParams = q.nP) ∧
    ((Ix.Kernel.nativeCapsAt q isRec).eta = true →
      (Ix.Kernel.nativeCapsAt q isRec).etaParams = q.nP) := by
  unfold Ix.Kernel.nativeCapsAt
  split <;> simp

/-- **The constructors' conses keep the store invariant**, each fresh and closed. -/
theorem storeInv_consSumCtors {nP : Nat} :
    ∀ {ctorsA : List (ConstantVal md × Nat)} {env : Env md}, StoreInv env →
      (ctorsA.map (·.1.name)).Nodup →
      (∀ c ∈ ctorsA, env.find? c.1.name = none) →
      (∀ c ∈ ctorsA, c.1.type.hasFvar = false ∧
        c.1.type.allLevelParamsDefined c.1.levelParams = true ∧
        c.1.type.constsResolve env = true ∧ c.1.type.looseBVarsBounded 0 = true) →
      StoreInv (Ix.Kernel.consSumCtors nP ctorsA env)
  | [], _, h, _, _, _ => h
  | c :: cs, env, h, hnd, hfresh, hty => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [Ix.Kernel.consSumCtors]
    refine storeInv_consSumCtors
      (storeInv_consTyped (c := .ctorInfo c.1 nP c.2) h (hfresh c List.mem_cons_self)
        (hty c List.mem_cons_self) (fun _ _ _ heq => nomatch heq)
        (fun _ _ _ _ heq => nomatch heq) (fun _ heq => nomatch heq)
        (fun _ _ heq => nomatch heq))
      hnd.2 (fun c' hc' => ?_) (fun c' hc' => ?_)
    · rw [Ix.Kernel.Env.find?_cons, if_neg]
      · exact hfresh c' (List.mem_cons_of_mem _ hc')
      · intro he
        exact hnd.1 (List.mem_map.mpr ⟨c', hc', he.symm⟩)
    · obtain ⟨h1, h2, h3, h4⟩ := hty c' (List.mem_cons_of_mem _ hc')
      exact ⟨h1, h2, Ix.Kernel.Expr.constsResolve_mono h3, h4⟩

/-- A consed constructor is found at its own record. -/
theorem consSumCtors_find?_ctor {nP : Nat} :
    ∀ {ctorsA : List (ConstantVal md × Nat)} {env : Env md}, (ctorsA.map (·.1.name)).Nodup →
      ∀ cA ∈ ctorsA, (Ix.Kernel.consSumCtors nP ctorsA env).find? cA.1.name
        = some (.ctorInfo cA.1 nP cA.2)
  | [], _, _, _, h => nomatch h
  | c :: cs, env, hnd, cA, hcA => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [Ix.Kernel.consSumCtors]
    rcases List.mem_cons.mp hcA with rfl | hcA'
    · rw [consSumCtors_find?_of_not_mem hnd.1]
      exact Ix.Kernel.Env.find?_cons_self _ _
    · exact consSumCtors_find?_ctor hnd.2 cA hcA'

/-- What the former's and the constructors' stages leave at the constructors' environment. -/
structure NativeFront (p : NativeParts md) (cvTa : ConstantVal md)
    (ctorsA : List (ConstantVal md × Nat)) (envC : Env md) : Prop where
  store : StoreInv envC
  former : ∃ caps, envC.find? p.cvT.name = some (.indInfo cvTa caps)
  formerLps : cvTa.levelParams = p.cvT.levelParams
  formerStrip : ∃ bs, cvTa.type.stripPis (p.nP + p.nIdx) = some (bs, .sort p.resSort)
  resT : Ix.Kernel.reservedBasisNames.contains p.cvT.name = false
  ctor : ∀ (j : Nat) (cA : ConstantVal md × Nat), ctorsA[j]? = some cA →
    envC.find? cA.1.name = some (.ctorInfo cA.1 p.nP cA.2) ∧
    cA.1.levelParams = p.cvT.levelParams ∧
    Ix.Kernel.reservedBasisNames.contains cA.1.name = false ∧
    ∃ cbs es, cA.1.type.stripPis (p.nP + cA.2) = some (cbs,
      Expr.mkAppN (.const p.cvT.name (p.cvT.levelParams.map .param))
        (Ix.Kernel.structPsAt cA.2 p.nP ++ es)) ∧
      es.length = p.nIdx

/-- **The former's and the constructors' stages keep the store invariant**, and leave the
lookups and shapes the recursor and the table read. -/
theorem nativeFront {J : Judgements md} (hfr : ∀ e : Env md, JudgeFrames J e)
    {env env₁ : Env md} (h : StoreInv env) {p₀ : NativeParts md} (hrc : NativeRecog p₀)
    {isRec : Bool} {cvTa : ConstantVal md} {p₁ : InductiveShape md}
    {kinds : List (List RecFieldKind)} {p : NativeParts md}
    {ctorsA : List (ConstantVal md × Nat)} {sortss : List (List Level)}
    (hnd : (p₀.ctors.map (·.1.name)).Nodup)
    (hInd : SumIndRunJ J env p₀.toInductiveShape (fun p₁ => Ix.Kernel.nativeCapsAt p₁ isRec)
      env₁ cvTa p₁)
    (hp : p = (p₀.complete p₁).withKinds kinds)
    (hCtors : SumCtorsRunJ J env₁ env₁ p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort
      p.isProp p.large cvTa p.ctors ctorsA sortss) :
    NativeFront p cvTa ctorsA (Ix.Kernel.consSumCtors p.nP ctorsA env₁) := by
  obtain ⟨hClps₀, hresT₀⟩ := hrc
  obtain ⟨cvT, s, hTname₀, hTlps₀, hccvT, rfl, henv₁, bsT, hstripT₀⟩ := hInd.shape
  subst hp
  have hpT : ((p₀.complete (p₀.toInductiveShape.withSort s)).withKinds kinds).cvT = p₀.cvT := by
    simp [NativeParts.withKinds]
  have hpC : ((p₀.complete (p₀.toInductiveShape.withSort s)).withKinds kinds).ctors
      = p₀.ctors := by simp [NativeParts.withKinds]
  have hpP : ((p₀.complete (p₀.toInductiveShape.withSort s)).withKinds kinds).nP = p₀.nP := by
    simp [NativeParts.withKinds]
  have hpI : ((p₀.complete (p₀.toInductiveShape.withSort s)).withKinds kinds).nIdx
      = p₀.nIdx := by simp [NativeParts.withKinds]
  have hpS : ((p₀.complete (p₀.toInductiveShape.withSort s)).withKinds kinds).resSort = s := by
    simp [NativeParts.withKinds]
  generalize ((p₀.complete (p₀.toInductiveShape.withSort s)).withKinds kinds) = p
    at hCtors hpT hpC hpP hpI hpS ⊢
  -- the former
  have hTname : cvTa.name = p.cvT.name := by
    rw [hccvT.name_eq, hTname₀, hpT]
  have hlpsT : cvTa.levelParams = p.cvT.levelParams := by
    rw [hccvT.levelParams_eq, hTlps₀, hpT]
  have hfreshT : env.find? cvTa.name = none := by
    rw [hccvT.name_eq]; exact hccvT.fresh
  have hstripT : cvTa.type.stripPis (p.nP + p.nIdx) = some (bsT, .sort p.resSort) := by
    rw [hpP, hpI, hpS]; exact hstripT₀
  have hsome : (cvTa.type.stripPis (p₀.nP + p₀.nIdx)).isSome = true := by
    rw [hstripT₀]; rfl
  have hS₁ : StoreInv env₁ := by
    rw [henv₁]
    show StoreInv ⟨.indInfo cvTa (Ix.Kernel.nativeCapsAt (p₀.toInductiveShape.withSort s) isRec)
      :: env.consts⟩
    refine storeInv_consTyped h hfreshT (ConstantValCheckJ.typeWF (hfr env) hccvT)
      (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
      (fun _ heq => nomatch heq) (Ix.Kernel.IndCapsWF.of_caps ?_ ?_)
    · intro hu
      rw [(nativeCapsAt_params _ isRec).1 hu, InductiveShape.withSort_nP]
      exact Ix.Kernel.stripPis_isSome_of_le (Nat.le_add_right _ _) hsome
    · intro he
      rw [(nativeCapsAt_params _ isRec).2 he, InductiveShape.withSort_nP]
      exact Ix.Kernel.stripPis_isSome_of_le (Nat.le_add_right _ _) hsome
  have hfT₁ : ∃ caps, env₁.find? p.cvT.name = some (.indInfo cvTa caps) := by
    rw [henv₁, ← hTname]
    exact ⟨_, Ix.Kernel.Env.find?_cons_self _ _⟩
  -- the constructors
  obtain ⟨hlen, -, hall⟩ := hCtors
  have hcf : ∀ (j : Nat) (cA : ConstantVal md × Nat), ctorsA[j]? = some cA →
      env₁.find? cA.1.name = none ∧
      (cA.1.type.hasFvar = false ∧ cA.1.type.allLevelParamsDefined cA.1.levelParams = true ∧
        cA.1.type.constsResolve env₁ = true ∧ cA.1.type.looseBVarsBounded 0 = true) ∧
      cA.1.levelParams = p.cvT.levelParams ∧
      Ix.Kernel.reservedBasisNames.contains cA.1.name = false ∧
      ∃ cbs es, cA.1.type.stripPis (p.nP + cA.2) = some (cbs,
        Expr.mkAppN (.const p.cvT.name (p.cvT.levelParams.map .param))
          (Ix.Kernel.structPsAt cA.2 p.nP ++ es)) ∧
        es.length = p.nIdx := by
    intro j cA hj
    have hj' : j < p.ctors.length := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      omega
    obtain ⟨hnF, sorts, -, hrun⟩ := hall j (p.ctors[j]) cA (List.getElem?_eq_getElem hj') hj
    obtain ⟨hCn, hClp, hfC, -⟩ := hrun.names
    obtain ⟨ty', hcc⟩ := hrun.check
    obtain ⟨-, ⟨cbs, es, hstrip, hes⟩, -⟩ := hrun
    have hmemC : p.ctors[j] ∈ p₀.ctors := by
      rw [← hpC]; exact List.getElem_mem hj'
    obtain ⟨hlp₀, hres₀⟩ := hClps₀ _ hmemC
    refine ⟨by rw [hCn]; exact hfC, ConstantValCheckJ.typeWF (hfr env₁) hcc, ?_,
      by rw [hCn]; exact hres₀, cbs, es, by rw [hnF]; exact hstrip, hes⟩
    rw [hClp, hlp₀, hpT]
  have hnames : ctorsA.map (·.1.name) = p.ctors.map (·.1.name) := by
    apply List.ext_getElem
    · simp [hlen]
    · intro j h1 h2
      simp only [List.getElem_map]
      have hj : j < p.ctors.length := by simpa using h2
      obtain ⟨-, _, -, hrun⟩ := hall j (p.ctors[j]) (ctorsA[j])
        (List.getElem?_eq_getElem hj) (List.getElem?_eq_getElem (by omega))
      exact hrun.names.1
  have hndA : (ctorsA.map (·.1.name)).Nodup := by rw [hnames, hpC]; exact hnd
  have hcfm : ∀ c ∈ ctorsA, env₁.find? c.1.name = none ∧
      (c.1.type.hasFvar = false ∧ c.1.type.allLevelParamsDefined c.1.levelParams = true ∧
        c.1.type.constsResolve env₁ = true ∧ c.1.type.looseBVarsBounded 0 = true) := by
    intro c hc
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
    obtain ⟨h1, h2, -⟩ := hcf j c hj
    exact ⟨h1, h2⟩
  have hTnot : p.cvT.name ∉ ctorsA.map (·.1.name) := by
    intro hm
    obtain ⟨c, hc, he⟩ := List.mem_map.mp hm
    obtain ⟨caps, hf⟩ := hfT₁
    have h1 := (hcfm c hc).1
    rw [he, hf] at h1
    exact nomatch h1
  refine ⟨storeInv_consSumCtors hS₁ hndA (fun c hc => (hcfm c hc).1) (fun c hc => (hcfm c hc).2),
    ?_, hlpsT, ⟨bsT, hstripT⟩, by rw [hpT]; exact hresT₀, ?_⟩
  · obtain ⟨caps, hf⟩ := hfT₁
    exact ⟨caps, by rw [consSumCtors_find?_of_not_mem hTnot]; exact hf⟩
  · intro j cA hj
    obtain ⟨-, -, hlp, hres, hstrip⟩ := hcf j cA hj
    exact ⟨consSumCtors_find?_ctor hndA cA (List.mem_of_getElem? hj), hlp, hres, hstrip⟩

/-- **Every rule the block stores fires** (`NativeRecJ.plain`, at the front's lookups). -/
theorem NativeFront.plain {p : NativeParts md} {cvTa : ConstantVal md}
    {ctorsA : List (ConstantVal md × Nat)} {envC : Env md} (hF : NativeFront p cvTa ctorsA envC)
    {J : Judgements md} {cvRa : ConstantVal md} {rhss : List (Expr md)}
    (hRec : NativeRecJ J envC p cvTa ctorsA cvRa rhss) (hk : ctorsA.length = p.kinds.length)
    (hlenA : ctorsA.length = p.ctors.length) :
    ctorsA.all (fun c => Expr.recRulePlain cvRa.type p.majorIdx p.rulePrefix p.nP
      c.1.levelParams) = true :=
  let ⟨caps, hfT⟩ := hF.former
  hRec.plain ⟨cvTa, caps, hfT⟩ hk hlenA fun c hc =>
    let ⟨j, hj⟩ := List.mem_iff_getElem?.mp hc
    (hF.ctor j c hj).2.1

/-- **The projection table's stage keeps the store invariant**: at a structure-like block the
table is consed with its head data, which the former's and the constructor's lookups give;
otherwise nothing is installed. -/
theorem storeInv_nativeTable {p : NativeParts md} {ctorsA : List (ConstantVal md × Nat)}
    {sortss : List (List Level)} {envX env₂ : Env md} (h : StoreInv envX)
    (hTbl : Ix.Kernel.checkNativeTable (m := Ix.Kernel.CheckM md) p ctorsA sortss envX
      = .ok env₂)
    (hhead : ∀ cA, ctorsA = [cA] → p.nIdx = 0 →
      Ix.Kernel.reservedBasisNames.contains p.cvT.name = false ∧
      Ix.Kernel.reservedBasisNames.contains cA.1.name = false ∧
      (∃ (cvT : ConstantVal md) (caps : IndCaps md),
        envX.find? p.cvT.name = some (.indInfo cvT caps) ∧
        cvT.levelParams = p.cvT.levelParams ∧
        ∃ bs, cvT.type.stripPis p.nP = some (bs, .sort p.resSort)) ∧
      envX.find? cA.1.name = some (.ctorInfo cA.1 p.nP cA.2) ∧
      cA.1.levelParams = p.cvT.levelParams ∧
      ∃ bs, cA.1.type.stripPis (p.nP + cA.2) = some (bs,
        Expr.mkAppN (.const p.cvT.name (p.cvT.levelParams.map .param))
          ((List.range p.nP).map fun k => .bvar (cA.2 + p.nP - 1 - k)))) :
    StoreInv env₂ := by
  unfold Ix.Kernel.checkNativeTable at hTbl
  split at hTbl
  · next cA sorts =>
    split at hTbl
    · next hnIdx =>
      have hnIdx' : p.nIdx = 0 := beq_iff_eq.mp hnIdx
      obtain ⟨hrT, hrC, ⟨cvT, caps, hfT, hlT, hsT⟩, hfC, hlC, hsC⟩ := hhead cA rfl hnIdx'
      have hwf := Ix.Kernel.direct_table_wf h.wf hTbl
      obtain ⟨bodies, -, -, -, hfresh, rfl⟩ := Ix.Kernel.checkStructProjTable_inv hTbl
      refine ⟨hwf, Ix.Kernel.RecCtorsStored.cons h.rec_ctors hfresh
        (fun _ _ _ _ heq => nomatch heq), Ix.Kernel.Verify.ProjOkT.cons h.proj_ok hfresh ?_⟩
      intro tbl heq i hi
      obtain rfl := ConstantInfo.projInfo.inj heq
      exact ⟨hrT, hrC, hi, ⟨cvT, caps, Ix.Kernel.Env.find?_cons_of_fresh hfresh hfT, hlT, hsT⟩,
        ⟨cA.1, Ix.Kernel.Env.find?_cons_of_fresh hfresh hfC, hlC, hsC⟩⟩
    · obtain rfl := Except.ok.inj hTbl
      exact h
  · obtain rfl := Except.ok.inj hTbl
    exact h

/-- **The native route keeps the store invariant**: the former and the constructors
(`nativeFront`), the recursor with its generated rules (each canonical, at a stored constructor,
its two rescue bits the install's lookups), then the projection table. -/
theorem storeInv_declNativeRunJ {J : Judgements md} (hfr : ∀ e : Env md, JudgeFrames J e)
    {env env₂ : Env md} {p₀ : NativeParts md} (hrc : NativeRecog p₀) (h : StoreInv env)
    (hrun : DeclNativeRunJ J env p₀ env₂) : StoreInv env₂ := by
  obtain ⟨hnd, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, cvRa, rhss, -, -, -, hInd, hp,
    hCtors, -, -, -, -, -, hFOk, -, hRec, hTbl⟩ := hrun
  have hF := nativeFront hfr h hrc hnd hInd hp hCtors
  have hplAll := hF.plain hRec (nativeFieldsOk_length hFOk) hCtors.1
  -- the recursor
  obtain ⟨hnR, -, hfR, -⟩ := hRec.recursor
  have hfreshR : (Ix.Kernel.consSumCtors p.nP ctorsA env₁).find? cvRa.name = none := by
    rw [hnR]; exact hfR
  have hSR : StoreInv ⟨.recInfo cvRa p.majorIdx p.rulePrefix
      (sumRules (Ix.Kernel.consSumCtors p.nP ctorsA env₁).find? cvRa.name p.nP p.majorIdx
        p.rulePrefix cvRa.type ctorsA rhss) ::
      (Ix.Kernel.consSumCtors p.nP ctorsA env₁).consts⟩ := by
    refine ⟨hRec.recWF hF.store.wf (hfr _).annot_syntax,
      Ix.Kernel.RecCtorsStored.cons hF.store.rec_ctors hfreshR ?_,
      Ix.Kernel.Verify.ProjOkT.cons hF.store.proj_ok hfreshR (fun _ heq => nomatch heq)⟩
    intro cvR' mI' rP' rules heq r hr
    injection heq with h1 h2 h3 hrules
    subst h1 h2 h3 hrules
    obtain ⟨j, cA, rhs, hj, -, rfl⟩ := Ix.Kernel.sumRules_getElem? hr
    obtain ⟨hfC, -, -, cbs, es, hres, -⟩ := hF.ctor j cA hj
    have hpl : Expr.recRulePlain cvRa.type p.majorIdx p.rulePrefix p.nP cA.1.levelParams = true :=
      List.all_eq_true.mp hplAll cA (List.mem_of_getElem? hj)
    exact ⟨Ix.Kernel.RuleCtorOk.of_plain hfC (by simp [Ix.Kernel.recRuleBits, hpl]) hpl
        (Ix.Kernel.Expr.ctorTeleOk_of hres (by rw [Ix.Kernel.Expr.getAppFn_mkAppN]; rfl)),
      fun hb => hb, fun hb => hb⟩
  -- the table
  refine storeInv_nativeTable hSR hTbl ?_
  intro cA hA hI
  obtain ⟨hfC, hlpC, hresC, cbs, es, hres, hes⟩ := hF.ctor 0 cA (by simp [hA])
  obtain ⟨caps, hfT⟩ := hF.former
  obtain ⟨bs, hsT⟩ := hF.formerStrip
  have hes0 : es = [] := List.eq_nil_of_length_eq_zero (by rw [hes, hI])
  rw [hI, Nat.add_zero] at hsT
  refine ⟨hF.resT, hresC, ⟨cvTa, caps, Ix.Kernel.Env.find?_cons_of_fresh hfreshR hfT,
    hF.formerLps, bs, hsT⟩, Ix.Kernel.Env.find?_cons_of_fresh hfreshR hfC, hlpC, cbs, ?_⟩
  rw [hres, hes0, List.append_nil]
  rfl

/-- **The native route without a recursor record keeps the store invariant**: the former and
the constructors (`nativeFront`), then the projection table. -/
theorem storeInv_declNativeNoRecRunJ {J : Judgements md} (hfr : ∀ e : Env md, JudgeFrames J e)
    {env env₂ : Env md} {p₀ : NativeParts md} (hrc : NativeRecog p₀) (h : StoreInv env)
    (hrun : DeclNativeNoRecRunJ J env p₀ env₂) : StoreInv env₂ := by
  obtain ⟨hnd, isRec, env₁, cvTa, p₁, p, ctorsA, sortss, kinds, -, -, -, hInd, hp,
    hCtors, -, -, -, -, -, hTbl⟩ := hrun
  have hF := nativeFront hfr h hrc hnd hInd hp hCtors
  refine storeInv_nativeTable hF.store hTbl ?_
  intro cA hA hI
  obtain ⟨hfC, hlpC, hresC, cbs, es, hres, hes⟩ := hF.ctor 0 cA (by simp [hA])
  obtain ⟨caps, hfT⟩ := hF.former
  obtain ⟨bs, hsT⟩ := hF.formerStrip
  have hes0 : es = [] := List.eq_nil_of_length_eq_zero (by rw [hes, hI])
  rw [hI, Nat.add_zero] at hsT
  refine ⟨hF.resT, hresC, ⟨cvTa, caps, hfT, hF.formerLps, bs, hsT⟩, hfC, hlpC, cbs, ?_⟩
  rw [hres, hes0, List.append_nil]
  rfl

/-- **Every inductive route keeps the store invariant.** -/
theorem storeInv_indRoutesJ {J : Judgements md} (hfr : ∀ e : Env md, JudgeFrames J e)
    {env env₂ : Env md} {block : List (ConstantInfo md)} {nP : Nat} (h : StoreInv env)
    (hr : IndRoutesJ J env block nP env₂) : StoreInv env₂ := by
  rcases hr with ⟨p₀, hdp, hN⟩ | hM | ⟨p₀, hdp, hN⟩
  · exact storeInv_declNativeRunJ hfr (nativeRecog_of hdp) h hN
  · exact storeInv_declIndRunJ hfr h hM
  · exact storeInv_declNativeNoRecRunJ hfr (nativeRecog_noRec hdp) h hN

/-! ## The fold -/

/-- **One declaration step keeps the store invariant**, at a package whose annotations keep
scoping, given the inductive kind's step. -/
theorem storeInv_declRunJ {J : Judgements md} (hfr : ∀ e : Env md, JudgeFrames J e)
    {Ind : List (ConstantInfo md) → Nat → Env md → Prop} {env env₂ : Env md}
    {d : Declaration md}
    (hind : ∀ {block : List (ConstantInfo md)} {nP : Nat} {envI : Env md},
      Ind block nP envI → StoreInv envI)
    (h : StoreInv env) (hrun : DeclRunJ J Ind env d env₂) : StoreInv env₂ := by
  cases d with
  | defnDecl cv value hint => exact storeInv_declDefnRunJ (hfr env) h hrun
  | thmDecl cv value => exact storeInv_declThmRunJ (hfr env) h hrun
  | opaqueDecl cv value => exact storeInv_declOpaqueRunJ (hfr env) h hrun
  | axiomDecl cv => exact storeInv_declAxiomRunJ (hfr env) h hrun
  | basisDecl kind => exact storeInv_basis h hrun
  | indDecl block nP =>
    simp only [DeclRunJ] at hrun
    split at hrun
    · exact storeInv_basis h hrun
    · exact hind hrun
  | quotDecl k cv =>
    simp only [DeclRunJ] at hrun
    split at hrun
    · exact storeInv_basis h hrun
    · subst hrun
      exact h

/-- **The fold keeps the store invariant over every inductive route**, at a package whose
annotations keep scoping. -/
theorem storeInv_declsRunJ {J : Judgements md} (hfr : ∀ e : Env md, JudgeFrames J e)
    {env env' : Env md} {ds : List (Declaration md)} :
    DeclsRunJ J (IndRoutesJ J) env ds env' → StoreInv env → StoreInv env' := by
  intro hds
  induction hds with
  | nil => exact id
  | cons hd _ ih =>
    intro h
    exact ih (storeInv_declRunJ hfr (fun hI => storeInv_indRoutesJ hfr h hI) h hd)

/-- **The fold over derivations keeps the store invariant** (`foldRulesRoutes`'s shape, so the
two apply to one run): every step of `DeclsRunJ rulesJ (IndRoutesJ rulesJ)` — the value kinds,
the basis blocks, the quotient, and the three inductive routes — keeps `EnvWF`,
`RecCtorsStored` and `ProjOkT`, with no model. From the empty environment (`StoreInv.empty`)
every environment such a run reaches satisfies them. -/
theorem storeFoldRoutes {env env' : Env md} {ds : List (Declaration md)} :
    DeclsRunJ rulesJ (IndRoutesJ rulesJ) env ds env' → StoreInv env → StoreInv env' :=
  storeInv_declsRunJ judgeFrames_rulesJ

/-- **Every environment a run over derivations reaches from the empty one satisfies the store
invariant.** -/
theorem storeInv_of_run {env' : Env md} {ds : List (Declaration md)}
    (h : DeclsRunJ rulesJ (IndRoutesJ rulesJ) Env.empty ds env') : StoreInv env' :=
  storeFoldRoutes h StoreInv.empty

end Ix.Kernel.Model
