import IxCCGrounding.Syntax

/-!
# The check of a `case` entry's shape (`IxCCGrounding.CaseCheck`)

Denotes-free. A reader (`caseShape?`) takes the shape off the stored `casesOn`, its recursor and
the recursor's rules: the binders of `casesOn`'s type; per rule its constructor and field count;
per minor premise of the recursor's type its fields, induction hypotheses and codomain (lowered
past the hypotheses); the recursive fields from the rule's right-hand side; the inductive and its
levels from the major premise. The reader needs no proof: the deciders below recompute every
builder and compare it with what is stored (`caseStoredB` decides `CaseStored`, `caseProgB`
decides `CaseProg`), and their soundness lemmas are what the theorems use.
-/

namespace IxCC.Grounding

open Ix.Kernel
open IxCC.Src (Value Slot Term CId Program Levels)

/-! ## The reader -/

/-- Lower the loose bound variables at or above `c` by `k`. -/
def lowerBVars (k : Nat) : Nat → KExpr → KExpr
  | c, .bvar i => if i ≥ c then .bvar (i - k) else .bvar i
  | c, .app f a => .app (lowerBVars k c f) (lowerBVars k c a)
  | c, .lam d b m => .lam (lowerBVars k c d) (lowerBVars k (c + 1) b) m
  | c, .forallE d b m => .forallE (lowerBVars k c d) (lowerBVars k (c + 1) b) m
  | c, .letE t v b l => .letE (lowerBVars k c t) (lowerBVars k c v) (lowerBVars k (c + 1) b) l
  | c, .proj s i e => .proj s i (lowerBVars k c e)
  | _, e => e

/-- A `∀`-telescope's binders, all of them, and what remains. -/
def teleSplit : KExpr → List (KExpr × BinderMeta) × KExpr
  | .forallE d b m => ((d, m) :: (teleSplit b).1, (teleSplit b).2)
  | e => ([], e)

/-- Exactly `n` leading binders of a `∀`-telescope, and what remains. -/
def piSplit : Nat → KExpr → Option (List (KExpr × BinderMeta) × KExpr)
  | 0, e => some ([], e)
  | n + 1, .forallE d b m => (piSplit n b).map fun r => ((d, m) :: r.1, r.2)
  | _ + 1, _ => none

/-- The body under `n` leading λs. -/
def lamBody : Nat → KExpr → KExpr
  | n + 1, .lam _ b _ => lamBody n b
  | _, e => e

/-- The recursive field an induction hypothesis argument of a rule's right-hand side points at
(its last argument, a variable among the `nF` fields). -/
def recFieldOf (nF : Nat) (arg : KExpr) : Nat :=
  match arg.getAppArgs.getLast? with
  | some (.bvar k) => nF - 1 - k
  | _ => 0

/-- **The shape of a `case` constant `kc` over its recursor `kr`, read off the stored terms**, the
recursor's type read at the levels `casesOn`'s body calls it at. -/
def caseShape? (env : KEnv) (kc kr : KKey) : Option CaseShape := do
  let .defnInfo cvc val _ ← env.find? kc | none
  let .recInfo cvr _ _ rules ← env.find? kr | none
  let binders := (teleSplit cvc.type).1
  let nM := rules.length
  let nP := binders.length - 2 - nM
  let .const _ recLevels := (lamBody binders.length val).getAppFn | none
  let (majDom, _) ← binders[nP + 1]?
  let .const ind indLevels := majDom.getAppFn | none
  let recBs := (teleSplit (cvr.type.instantiateLevelParams cvr.levelParams recLevels)).1
  let (_, majorMeta) ← recBs[nP + 1 + nM]?
  let ctors ← (List.range nM).mapM fun j => do
    let rl ← rules[j]?
    let (minor, minorMeta) ← recBs[nP + 1 + j]?
    let .ctorInfo _ _ nF ← env.find? rl.ctor | none
    let (fihs, body) := teleSplit minor
    let ihs := fihs.drop nF
    pure { key := rl.ctor, nF, fields := fihs.take nF, ihs,
           recFields := ((lamBody (nP + 1 + nM + nF) rl.rhs).getAppArgs.drop nF).map (recFieldOf nF),
           codom := lowerBVars ihs.length 0 body, minorMeta }
  pure { lps := cvc.levelParams, ind, indLevels, nP, binders, ctors, majorMeta, recLevels }

/-! ## The deciders -/

/-- Every constructor of the shape satisfies `P`. -/
def allCtors (sh : CaseShape) (P : Nat → CtorShape → Bool) : Bool :=
  (List.range sh.ctors.length).all fun j =>
    match sh.ctors[j]? with
    | some cs => P j cs
    | none => true

/-- Constructor `j`'s stored type at the `case`'s levels (`CaseStored.ctors`). -/
def ctorTypeB (env : KEnv) (sh : CaseShape) (j : Nat) (cs : CtorShape) : Bool :=
  match env.find? cs.key with
  | some (.ctorInfo cvC np nf) =>
    np == sh.nP && nf == cs.nF &&
    match piSplit sh.nP (cvC.type.instantiateLevelParams cvC.levelParams sh.indLevels) with
    | some (pbs, T1) =>
      match piSplit cs.nF T1 with
      | some (fbs, T2) =>
        decide (T2 = Expr.mkAppN (.const sh.ind sh.indLevels) (bvarsFrom cs.nF sh.nP)) &&
          decide (pbs.map (·.1) = (sh.binders.take sh.nP).map (·.1)) &&
          decide ((liftTele (j + 1) 0 fbs).map (·.1) = cs.fields.map (·.1))
      | none => false
    | none => false
  | _ => false

/-- A constructor's own stored type (`CaseWF.ctorRaw`). -/
def ctorRawB (env : KEnv) (sh : CaseShape) (cs : CtorShape) : Bool :=
  match env.find? cs.key with
  | some (.ctorInfo cvC np nf) =>
    np == sh.nP && nf == cs.nF && cvC.levelParams.length == sh.indLevels.length &&
      bvarsLt 0 cvC.type && cvC.type.allLevelParamsDefined cvC.levelParams &&
      decide ((piBody (sh.nP + cs.nF) cvC.type).getAppFn =
        .const sh.ind (cvC.levelParams.map .param))
  | _ => false

/-- `CaseWF`. -/
def caseWFB (env : KEnv) (sh : CaseShape) : Bool :=
  allCtors sh (fun j cs => cs.recFields.all fun rf =>
    decide (rf < cs.nF) && decide ((cs.fields[rf]?).map (·.1) = some (sh.recFieldDom j rf))) &&
  allCtors sh (fun j cs => (List.range cs.recFields.length).all fun r =>
    match cs.recFields[r]? with
    | some rf => decide ((cs.ihs[r]?).map (·.1) = some (cs.ihDom j r rf))
    | none => true) &&
  allCtors sh (fun j cs => avoids cs.nF j cs.codom) &&
  (match sh.binders.getLast? with
    | some (_, m) => allCtors sh fun _ cs => cs.fields.all fun b => decide (b.2.pw = m.pw)
    | none => false) &&
  allCtors sh (fun _ cs => ctorRawB env sh cs) &&
  neverPropB env sh.ind

/-- `CaseStored`. -/
def caseStoredB (env : KEnv) (kc kr : KKey) (sh : CaseShape) : Bool :=
  (sh.binders.length == sh.nP + 2 + sh.nM && decide (0 < sh.nM)) &&
  (match env.find? kc with
    | some (.defnInfo cvc val _) =>
      decide (val = lamTele sh.binders (sh.body kr)) && cvc.levelParams == sh.lps &&
        decide (cvc.type = piTele sh.binders (.app (.bvar (sh.nM + 1)) (.bvar sh.nM)))
    | _ => false) &&
  allCtors sh (fun j cs =>
    decide ((sh.binders[sh.nP + 2 + j]?).map (·.1) = some (CaseShape.casesMinor j cs)) &&
      cs.ihs.length == cs.recFields.length && cs.fields.length == cs.nF) &&
  (match sh.binders[sh.nP + 1]? with
    | some (A, _) => decide (A = Expr.mkAppN (.const sh.ind sh.indLevels) (bvarsFrom 1 sh.nP))
    | none => false) &&
  (match env.find? kr with
    | some (.recInfo cvr mI rP rules) =>
      mI == sh.nP + 1 + sh.nM && rP == sh.nP + 1 + sh.nM &&
        cvr.levelParams.length == sh.recLevels.length &&
        decide (cvr.type.instantiateLevelParams cvr.levelParams sh.recLevels = sh.recType) &&
        rules.length == sh.nM &&
        allCtors sh (fun j cs =>
          match rules[j]? with
          | some rl => decide (rl.ctor = cs.key) &&
              decide (rl.rhs.instantiateLevelParams cvr.levelParams sh.recLevels = sh.ruleRhs kr j cs)
          | none => true)
    | _ => false) &&
  allCtors sh (ctorTypeB env sh) &&
  caseWFB env sh

/-- `CaseProg`. -/
def caseProgB (p : Program) (κ : CId → KKey) (Sl : List CId) (r : CId) (sh : CaseShape) : Bool :=
  match p.decl? r with
  | some (.recr _ _ _ np nmot nmin ni ind _ _) =>
    np == sh.nP && nmot == 1 && nmin == sh.nM && ni == 0 &&
    Sl.all (fun c =>
      match p.decl? c with
      | some (.ctor _ _ ind' cidx np' nf' _) =>
        if ind' == ind then
          np' == sh.nP &&
            match sh.ctors[cidx]? with
            | some cs => decide (cs.key = κ c) && cs.nF == nf'
            | none => false
        else true
      | _ => true) &&
    (if some ind == p.known.nat then
      sh.nP == 0 && decide (sh.ctors.map (fun cs => (cs.key, cs.nF)) =
        [((natZeroName : KKey), 0), ((natSuccName : KKey), 1)])
    else true)
  | _ => false

/-! ## Soundness -/

theorem allCtors_spec {sh : CaseShape} {P : Nat → CtorShape → Bool} (h : allCtors sh P = true) :
    ∀ j cs, sh.ctors[j]? = some cs → P j cs = true := by
  intro j cs hj
  have hl := (List.getElem?_eq_some_iff.mp hj).1
  have := List.all_eq_true.mp h j (List.mem_range.mpr hl)
  simpa [hj] using this

theorem piSplit_spec (n : Nat) : ∀ (T : KExpr) (bs : List (KExpr × BinderMeta)) (R : KExpr),
    piSplit n T = some (bs, R) → T = piTele bs R := by
  induction n with
  | zero =>
    intro T bs R h
    simp only [piSplit, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | succ n ih =>
    intro T bs R h
    cases T with
    | forallE d b m =>
      simp only [piSplit] at h
      cases h' : piSplit n b with
      | none => rw [h'] at h; cases h
      | some r =>
        rw [h'] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [ih b r.1 r.2 (by rw [h'])]
        rfl
    | _ => simp [piSplit] at h

theorem ctorType_of_check {env : KEnv} {sh : CaseShape} {j : Nat} {cs : CtorShape}
    (h : ctorTypeB env sh j cs = true) : ∃ (cvC : ConstantVal .anon)
      (pbs fbs : List (KExpr × BinderMeta)),
      env.find? cs.key = some (.ctorInfo cvC sh.nP cs.nF) ∧
      cvC.type.instantiateLevelParams cvC.levelParams sh.indLevels =
        piTele pbs (piTele fbs (Expr.mkAppN (.const sh.ind sh.indLevels) (bvarsFrom cs.nF sh.nP))) ∧
      pbs.map (·.1) = (sh.binders.take sh.nP).map (·.1) ∧
      (liftTele (j + 1) 0 fbs).map (·.1) = cs.fields.map (·.1) := by
  unfold ctorTypeB at h
  split at h
  · rename_i cvC np nf hf
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, rfl⟩, h⟩ := h
    split at h
    · rename_i pbs T1 h1
      split at h
      · rename_i fbs T2 h2
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨hT2, hp⟩, hfb⟩ := h
        refine ⟨cvC, pbs, fbs, hf, ?_, hp, hfb⟩
        rw [piSplit_spec _ _ _ _ h1, piSplit_spec _ _ _ _ h2, hT2]
      · cases h
    · cases h
  · cases h

theorem ctorRaw_of_check {env : KEnv} {sh : CaseShape} {cs : CtorShape}
    (h : ctorRawB env sh cs = true) : ∃ cvC : ConstantVal .anon,
      env.find? cs.key = some (.ctorInfo cvC sh.nP cs.nF) ∧
      cvC.levelParams.length = sh.indLevels.length ∧ bvarsLt 0 cvC.type = true ∧
      cvC.type.allLevelParamsDefined cvC.levelParams = true ∧
      (piBody (sh.nP + cs.nF) cvC.type).getAppFn = .const sh.ind (cvC.levelParams.map .param) := by
  unfold ctorRawB at h
  split at h
  · rename_i cvC np nf hf
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨rfl, rfl⟩, h1⟩, h2⟩, h3⟩, h4⟩ := h
    exact ⟨cvC, hf, h1, h2, h3, h4⟩
  · cases h

theorem caseWF_of_check {env : KEnv} {sh : CaseShape} (h : caseWFB env sh = true) :
    CaseWF env sh := by
  unfold caseWFB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨fun j cs hj rf hrf => ?_, fun j cs hj r rf hr => ?_, fun j cs hj => allCtors_spec h3 j cs hj,
    ?_, fun j cs hj => ctorRaw_of_check (allCtors_spec h5 j cs hj), neverProp_of_check h6⟩
  · have := List.all_eq_true.mp (allCtors_spec h1 j cs hj) rf hrf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this
  · have hl := (List.getElem?_eq_some_iff.mp hr).1
    have := List.all_eq_true.mp (allCtors_spec h2 j cs hj) r (List.mem_range.mpr hl)
    simpa [hr] using this
  · split at h4
    · rename_i A m hg
      refine ⟨A, m, hg, fun j cs hj b hb => ?_⟩
      have := List.all_eq_true.mp (allCtors_spec h4 j cs hj) b hb
      simpa using this
    · cases h4

/-- **The check of a `case` shape is sound.** -/
theorem caseStored_of_check {env : KEnv} {kc kr : KKey} {sh : CaseShape}
    (h : caseStoredB env kc kr sh = true) : CaseStored env kc kr sh := by
  unfold caseStoredB at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hl, hnm⟩, hco⟩, hmin⟩, hmaj⟩, hrec⟩, hct⟩, hwf⟩ := h
  refine ⟨⟨hl, hnm⟩, ?_, fun j cs hj => ?_, ?_, ?_,
    fun j cs hj => ctorType_of_check (allCtors_spec hct j cs hj), caseWF_of_check hwf⟩
  · split at hco
    · rename_i cvc val hint hf
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hco
      obtain ⟨⟨hv, hlp⟩, hty⟩ := hco
      exact ⟨cvc, hint, by rw [hf, hv], hlp, hty⟩
    · cases hco
  · have := allCtors_spec hmin j cs hj
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  · split at hmaj
    · rename_i A m hb
      simp only [decide_eq_true_eq] at hmaj
      exact ⟨m, by rw [hb, hmaj]⟩
    · cases hmaj
  · unfold CaseRec
    split at hrec
    · rename_i cvr mI rP rules hf
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hrec
      obtain ⟨⟨⟨⟨⟨rfl, rfl⟩, hlp⟩, hty⟩, hrl⟩, hrs⟩ := hrec
      refine ⟨cvr, rules, hf, hlp, hty, hrl, fun j cs rl hj hr => ?_⟩
      have := allCtors_spec hrs j cs hj
      simp only [hr, Bool.and_eq_true, decide_eq_true_eq] at this
      exact this
    · cases hrec

/-- **The check of a `case` entry's program side is sound.** -/
theorem caseProg_of_check {p : Program} {κ : CId → KKey} {Sl : List CId} {r : CId}
    {sh : CaseShape} (h : caseProgB p κ Sl r sh = true) : CaseProg p κ (· ∈ Sl) r sh := by
  unfold caseProgB at h
  split at h
  · rename_i sf kk lvls np nmot nmin ni ind rules ty hd
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hS⟩, hN⟩ := h
    refine ⟨⟨sf, kk, lvls, ind, rules, ty, hd, fun c hc sf' lv' cidx np nf ty' hdc => ?_, fun hn => ?_⟩⟩
    · have := List.all_eq_true.mp hS c hc
      simp only [hdc, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at this
      obtain ⟨hnp, hcs⟩ := this
      refine ⟨hnp, ?_⟩
      split at hcs
      · rename_i cs hcs'
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcs
        exact ⟨cs, hcs', hcs.1, hcs.2⟩
      · cases hcs
    · simp only [hn, ↓reduceIte, Bool.and_eq_true, beq_iff_eq,
        decide_eq_true_eq] at hN
      exact hN
  · cases h

end IxCC.Grounding
