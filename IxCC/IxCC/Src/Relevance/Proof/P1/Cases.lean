import IxCC.Src.Relevance.Proof.P1.Measure

/-! # P1, relevance preservation: the core as one induction over its cases

P1's core statements, `preserve` and `pre_step` (`IxCC.Src.Relevance.Proof.P1.Defs`), are the two
projections of one well-founded induction over `Step` on SrcEval's termination measure
(`IxCC.Src.Relevance.Proof.P1.Measure`): at every call `c` a run from `top` makes, `Inv c`, that
is, if `c`'s precondition holds, its result has `Post` and every step but the shielded variable's
evaluation has its target's precondition (`StepPre`). The induction is proved here from one
statement per evaluator case (25 of them: E1–E8, δ, `headValue`, A1–A3, `applyAll`, F1–F8 with F6w,
`force`, `forceAll`), each a `Prop` over the call's components with one signature (`CaseAt`):
L1's facts (`Facts`), the structure (`ShapeOk`), the call's precondition and sort events, and the
statement at every call the evaluation makes (`Below`, the induction hypothesis, so a case may use
`Post` of a grandchild). `Cases` collects them, and `preserve_of_cases` and `pre_step_of_cases`
give P1's approved statements from it.

**P1 is not proved.** `Cases` is a hypothesis: of its 25 fields, 22 are proved, five here (E2 at
a sort and at a Π, E3 at both literals, F4), one in `IxCC.Src.Relevance.Proof.P1.Recr` (F2), four
in `IxCC.Src.Relevance.Proof.P1.Ctor` (E6, F1, F7, F8), five in `IxCC.Src.Relevance.Proof.P1.Delta`
(E8, δ, `headValue`, F6, F6w) and seven in `IxCC.Src.Relevance.Proof.P1.Plumbing` (E1, E4, E5,
A1–A3, `applyAll`, `force`, `forceAll`). The other three, E7, F3 and F5, are stated, not proved.
F3 as stated is false where a reached subsingleton recursor's rule-0 constructor has no constructor
record, reproduced by a run (a `Prop` inductive with large elimination over a non-proof field, built
below the kernel, which only the kernel refuses); it is also a wrong-value route on the recheck
path. The check that closes it (`checkCanonical`: such a constructor has a record) is approved and
lands next, before `case_F3`. -/

set_option autoImplicit false

namespace IxCC.Src.Relevance.Proof.P1

open IxCC.Src
open Check Check.Canonical

variable {p : Program} {ann : Ann} {ch : Checked}

/-! ## The statement at one call -/

/-- The one step whose target's precondition fails: E7's evaluation of an argument variable its
spine shields (`pre_step`'s exception). -/
def ShieldedStep (c c' : Call) : Prop :=
  ∃ k ls ρ f m r x, c = .eval k ls ρ (.app f (.var x) m r) ∧ c' = .eval k ls ρ (.var x) ∧
    ShieldedIn x ρ (.app f (.var x) m r)

/-- Every step of `c` but the shielded one has its target's precondition. -/
def StepPre (p : Program) (ann : Ann) (ch : Checked) (c : Call) : Prop :=
  ∀ c', Step p c c' → ¬ ShieldedStep c c' → Pre p ann ch c'

/-- The core's statement at one call. -/
def Inv (p : Program) (ann : Ann) (ch : Checked) (c : Call) : Prop :=
  Pre p ann ch c → Post p ann ch c ∧ StepPre p ann ch c

/-- The induction hypothesis at `c`: the statement at every call `c`'s evaluation makes, its
children and their descendants (E1 reads a by-name slot's value through its `eval`, E7 a
saturating application's through `apply`'s `fire`). -/
def Below (p : Program) (ann : Ann) (ch : Checked) (c : Call) : Prop :=
  ∀ c', Relation.TransGen (Step p) c c' → Inv p ann ch c'

/-- One case's signature at call `c`: from L1's facts, the structure, `c`'s precondition and sort
events and the induction hypothesis, `c`'s result and its steps' preconditions. -/
def CaseAt (p : Program) (ann : Ann) (ch : Checked) (c : Call) : Prop :=
  Facts p ann ch → ShapeOk p → Pre p ann ch c → SortCoherent p ann c → Below p ann ch c →
    Post p ann ch c ∧ StepPre p ann ch c

/-! ## The 25 cases -/

/-- E1 `var`. -/
def CaseVar (p : Program) (ann : Ann) (ch : Checked) : Prop :=
  ∀ ⦃k : Nat⦄ ⦃ls : Levels⦄ ⦃ρ : Env⦄ ⦃i : Nat⦄, CaseAt p ann ch (.eval k ls ρ (.var i))

/-- E2 at a sort. -/
def CaseSort (p : Program) (ann : Ann) (ch : Checked) : Prop :=
  ∀ ⦃k : Nat⦄ ⦃ls : Levels⦄ ⦃ρ : Env⦄ ⦃u : Ixon.Univ⦄, CaseAt p ann ch (.eval k ls ρ (.sort u))

/-- E2 at a Π. -/
def CasePi (p : Program) (ann : Ann) (ch : Checked) : Prop :=
  ∀ ⦃k : Nat⦄ ⦃ls : Levels⦄ ⦃ρ : Env⦄ ⦃b : Binder⦄ ⦃res : Ixon.V3.ValueContract⦄ ⦃d c : Term⦄,
    CaseAt p ann ch (.eval k ls ρ (.pi b res d c))

/-- E3 at a `Nat` literal. -/
def CaseNatLit (p : Program) (ann : Ann) (ch : Checked) : Prop :=
  ∀ ⦃k : Nat⦄ ⦃ls : Levels⦄ ⦃ρ : Env⦄ ⦃n : Nat⦄, CaseAt p ann ch (.eval k ls ρ (.natLit n))

/-- E3 at a string literal. -/
def CaseStrLit (p : Program) (ann : Ann) (ch : Checked) : Prop :=
  ∀ ⦃k : Nat⦄ ⦃ls : Levels⦄ ⦃ρ : Env⦄ ⦃s : String⦄, CaseAt p ann ch (.eval k ls ρ (.strLit s))

/-- E4 `lam`. -/
def CaseLam (p : Program) (ann : Ann) (ch : Checked) : Prop :=
  ∀ ⦃k : Nat⦄ ⦃ls : Levels⦄ ⦃ρ : Env⦄ ⦃b : Binder⦄ ⦃d body : Term⦄,
    CaseAt p ann ch (.eval k ls ρ (.lam b d body))

/-- E5 `letE`. -/
def CaseLetE (p : Program) (ann : Ann) (ch : Checked) : Prop :=
  ∀ ⦃k : Nat⦄ ⦃ls : Levels⦄ ⦃ρ : Env⦄ ⦃c : Ixon.V3.LetContract⦄ ⦃r : Rel⦄ ⦃ty v b : Term⦄,
    CaseAt p ann ch (.eval k ls ρ (.letE c r ty v b))

/-- E6 `proj`. -/
def CaseProj (p : Program) (ann : Ann) (ch : Checked) : Prop :=
  ∀ ⦃k : Nat⦄ ⦃ls : Levels⦄ ⦃ρ : Env⦄ ⦃s : CId⦄ ⦃i : Nat⦄ ⦃e : Term⦄,
    CaseAt p ann ch (.eval k ls ρ (.proj s i e))

/-- E7 `app`. -/
def CaseApp (p : Program) (ann : Ann) (ch : Checked) : Prop :=
  ∀ ⦃k : Nat⦄ ⦃ls : Levels⦄ ⦃ρ : Env⦄ ⦃f a : Term⦄ ⦃m : Mode⦄ ⦃r : Rel⦄,
    CaseAt p ann ch (.eval k ls ρ (.app f a m r))

/-- E8 `const`: the reference. -/
def CaseConst (p : Program) (ann : Ann) (ch : Checked) : Prop :=
  ∀ ⦃k : Nat⦄ ⦃ls : Levels⦄ ⦃ρ : Env⦄ ⦃c : CId⦄ ⦃us : List Ixon.Univ⦄,
    CaseAt p ann ch (.eval k ls ρ (.const c us))

/-- δ (`evalConst`). -/
def CaseEvalConst (p : Program) (ann : Ann) (ch : Checked) : Prop :=
  ∀ ⦃k : Nat⦄ ⦃ls : Levels⦄ ⦃c : CId⦄, CaseAt p ann ch (.evalConst k ls c)

/-- A special head as a value (`headValue`). -/
def CaseHeadValue (p : Program) (ann : Ann) (ch : Checked) : Prop :=
  ∀ ⦃k : Nat⦄ ⦃ls : Levels⦄ ⦃h : Head⦄, CaseAt p ann ch (.headValue k ls h)

/-- A1–A3 (`apply`). -/
def CaseApply (p : Program) (ann : Ann) (ch : Checked) : Prop :=
  ∀ ⦃k : Nat⦄ ⦃f : Value⦄ ⦃s : Slot⦄, CaseAt p ann ch (.apply k f s)

/-- `applyAll`. -/
def CaseApplyAll (p : Program) (ann : Ann) (ch : Checked) : Prop :=
  ∀ ⦃k : Nat⦄ ⦃f : Value⦄ ⦃ss : List Slot⦄, CaseAt p ann ch (.applyAll k f ss)

/-- F1 (constructors). -/
def CaseCtor (p : Program) (ann : Ann) (ch : Checked) : Prop :=
  ∀ ⦃k : Nat⦄ ⦃c : CId⦄ ⦃ls : Levels⦄ ⦃args : List Slot⦄, CaseAt p ann ch (.fire k (.ctor c) ls args)

/-- F7 (`Quot.mk`). -/
def CaseQuotMk (p : Program) (ann : Ann) (ch : Checked) : Prop :=
  ∀ ⦃k : Nat⦄ ⦃c : CId⦄ ⦃ls : Levels⦄ ⦃args : List Slot⦄,
    CaseAt p ann ch (.fire k (.quotMk c) ls args)

/-- F8 (`Quot.lift`). -/
def CaseQuotLift (p : Program) (ann : Ann) (ch : Checked) : Prop :=
  ∀ ⦃k : Nat⦄ ⦃c : CId⦄ ⦃ls : Levels⦄ ⦃args : List Slot⦄,
    CaseAt p ann ch (.fire k (.quotLift c) ls args)

/-- F2 (ordinary ι), at a recursor declaration of kind `ordinary` at the levels. -/
def CaseF2 (p : Program) (ann : Ann) (ch : Checked) : Prop :=
  ∀ ⦃k : Nat⦄ ⦃r : CId⦄ ⦃ls : Levels⦄ ⦃args : List Slot⦄ ⦃sf kk : Bool⦄ ⦃lv np nmot nmin ni : Nat⦄
    ⦃ind : CId⦄ ⦃rules : List Rule⦄ ⦃ty : Term⦄,
    p.decl? r = some (.recr sf kk lv np nmot nmin ni ind rules ty) →
    (p.table.recKindOf r).map (·.atLevels ls) = some .ordinary →
    CaseAt p ann ch (.fire (k + 1) (.recr r) ls args)

/-- F3 (subsingleton ι), at a recursor declaration of kind `subsingleton` at the levels. -/
def CaseF3 (p : Program) (ann : Ann) (ch : Checked) : Prop :=
  ∀ ⦃k : Nat⦄ ⦃r : CId⦄ ⦃ls : Levels⦄ ⦃args : List Slot⦄ ⦃sf kk : Bool⦄ ⦃lv np nmot nmin ni : Nat⦄
    ⦃ind : CId⦄ ⦃rules : List Rule⦄ ⦃ty : Term⦄ ⦃w : PropWhen⦄ ⦃srcs : List FieldSrc⦄,
    p.decl? r = some (.recr sf kk lv np nmot nmin ni ind rules ty) →
    (p.table.recKindOf r).map (·.atLevels ls) = some (.subsingleton w srcs) →
    CaseAt p ann ch (.fire (k + 1) (.recr r) ls args)

/-- F4 (empty recursor), at a recursor declaration of kind `empty` at the levels. -/
def CaseF4 (p : Program) (ann : Ann) (ch : Checked) : Prop :=
  ∀ ⦃k : Nat⦄ ⦃r : CId⦄ ⦃ls : Levels⦄ ⦃args : List Slot⦄ ⦃sf kk : Bool⦄ ⦃lv np nmot nmin ni : Nat⦄
    ⦃ind : CId⦄ ⦃rules : List Rule⦄ ⦃ty : Term⦄,
    p.decl? r = some (.recr sf kk lv np nmot nmin ni ind rules ty) →
    (p.table.recKindOf r).map (·.atLevels ls) = some .empty →
    CaseAt p ann ch (.fire (k + 1) (.recr r) ls args)

/-- F5 (`case`). -/
def CaseCases (p : Program) (ann : Ann) (ch : Checked) : Prop :=
  ∀ ⦃k : Nat⦄ ⦃c : CId⦄ ⦃ls : Levels⦄ ⦃args : List Slot⦄, CaseAt p ann ch (.fire k (.cases c) ls args)

/-- F6 (primitives). -/
def CasePrim (p : Program) (ann : Ann) (ch : Checked) : Prop :=
  ∀ ⦃k : Nat⦄ ⦃op : PrimOp⦄ ⦃ls : Levels⦄ ⦃args : List Slot⦄,
    CaseAt p ann ch (.fire k (.prim op) ls args)

/-- F6w (word operations). -/
def CaseWord (p : Program) (ann : Ann) (ch : Checked) : Prop :=
  ∀ ⦃k : Nat⦄ ⦃w : Width⦄ ⦃op : WordOp⦄ ⦃ls : Levels⦄ ⦃args : List Slot⦄,
    CaseAt p ann ch (.fire k (.word w op) ls args)

/-- `force`. -/
def CaseForce (p : Program) (ann : Ann) (ch : Checked) : Prop :=
  ∀ ⦃k : Nat⦄ ⦃s : Slot⦄, CaseAt p ann ch (.force k s)

/-- `forceAll`. -/
def CaseForceAll (p : Program) (ann : Ann) (ch : Checked) : Prop :=
  ∀ ⦃k : Nat⦄ ⦃ss : List Slot⦄, CaseAt p ann ch (.forceAll k ss)

/-- The 25 cases of the core. -/
structure Cases (p : Program) (ann : Ann) (ch : Checked) : Prop where
  var : CaseVar p ann ch
  sort : CaseSort p ann ch
  pi : CasePi p ann ch
  natLit : CaseNatLit p ann ch
  strLit : CaseStrLit p ann ch
  lam : CaseLam p ann ch
  letE : CaseLetE p ann ch
  proj : CaseProj p ann ch
  app : CaseApp p ann ch
  const : CaseConst p ann ch
  evalConst : CaseEvalConst p ann ch
  headValue : CaseHeadValue p ann ch
  apply : CaseApply p ann ch
  applyAll : CaseApplyAll p ann ch
  ctor : CaseCtor p ann ch
  quotMk : CaseQuotMk p ann ch
  quotLift : CaseQuotLift p ann ch
  f2 : CaseF2 p ann ch
  f3 : CaseF3 p ann ch
  f4 : CaseF4 p ann ch
  cases : CaseCases p ann ch
  prim : CasePrim p ann ch
  word : CaseWord p ann ch
  force : CaseForce p ann ch
  forceAll : CaseForceAll p ann ch

/-! ## The cases proved here -/

/-- E2 at a sort: no tier-C case (C7), so the precondition fails. -/
theorem case_sort : CaseSort p ann ch := by
  intro k ls ρ u _ _ hpre _ _
  obtain ⟨q, bs, -, -, -, -, ht | ⟨more, -, hsp, -⟩ | ⟨c, us, he, -⟩⟩ := hpre
  · cases ht
  · cases hsp with
    | head _ _ ht => cases ht
  · cases he

/-- E2 at a Π: as at a sort. -/
theorem case_pi : CasePi p ann ch := by
  intro k ls ρ b res d c _ _ hpre _ _
  obtain ⟨q, bs, -, -, -, -, ht | ⟨more, -, hsp, -⟩ | ⟨c', us, he, -⟩⟩ := hpre
  · cases ht
  · cases hsp with
    | head _ _ ht => cases ht
  · cases he

/-- E3 at a `Nat` literal: a literal, and no step. -/
theorem case_natLit : CaseNatLit p ann ch := by
  intro k ls ρ n _ _ _ _ _
  constructor
  · intro v hv
    simp only [eval, Sem.Result.ok.injEq] at hv
    subst hv
    exact ⟨.lit n, fun _ _ _ _ he => nomatch he⟩
  · intro c' hst _
    cases hst

/-- E3 at a string literal: a literal, and no step. -/
theorem case_strLit : CaseStrLit p ann ch := by
  intro k ls ρ s _ _ _ _ _
  constructor
  · intro v hv
    simp only [eval, Sem.Result.ok.injEq] at hv
    subst hv
    exact ⟨.str s, fun _ _ _ _ he => nomatch he⟩
  · intro c' hst _
    cases hst

/-- F4: an empty recursor traps, and its only steps need another kind. -/
theorem case_F4 : CaseF4 p ann ch := by
  intro k r ls args sf kk lv np nmot nmin ni ind rules ty hd hk _ _ _ _ _
  constructor
  · intro v hv
    simp [fire, hd, hk] at hv
  · intro c' hst _
    cases hst <;> simp_all [recChosen]

/-! ## The induction -/

/-- F2–F4 at a recursor head, from the three kinds: no result and no step otherwise. -/
theorem case_recr_of (h2 : CaseF2 p ann ch) (h3 : CaseF3 p ann ch) (h4 : CaseF4 p ann ch)
    {k : Nat} {r : CId} {ls : Levels} {args : List Slot} :
    CaseAt p ann ch (.fire k (.recr r) ls args) := by
  intro hf hs hpre hcoh ih
  cases k with
  | zero =>
    refine ⟨fun v hv => ?_, fun c' hst => ?_⟩
    · simp [fire] at hv
    · cases hst
  | succ k =>
    cases hd : p.decl? r with
    | none =>
      refine ⟨fun v hv => ?_, fun c' hst => ?_⟩
      · simp [fire, hd] at hv
      · cases hst <;> simp_all
    | some d =>
      cases d with
      | recr sf kk lv np nmot nmin ni ind rules ty =>
        cases hk : (p.table.recKindOf r).map (·.atLevels ls) with
        | none =>
          refine ⟨fun v hv => ?_, fun c' hst => ?_⟩
          · simp only [fire, hd, hk] at hv; cases hv
          · cases hst <;> simp_all
        | some kind =>
          cases kind with
          | ordinary => exact h2 hd hk hf hs hpre hcoh ih
          | subsingleton w srcs => exact h3 hd hk hf hs hpre hcoh ih
          | empty => exact h4 hd hk hf hs hpre hcoh ih
      | _ =>
        refine ⟨fun v hv => ?_, fun c' hst => ?_⟩
        · simp [fire, hd] at hv
        · cases hst <;> simp_all

/-- Every call, from the cases. -/
theorem case_all_of (hc : Cases p ann ch) {c : Call} : CaseAt p ann ch c := by
  intro hf hs hpre hcoh ih
  cases c with
  | eval k ls ρ t =>
    cases t with
    | var i => exact hc.var hf hs hpre hcoh ih
    | sort u => exact hc.sort hf hs hpre hcoh ih
    | const c us => exact hc.const hf hs hpre hcoh ih
    | app f a m r => exact hc.app hf hs hpre hcoh ih
    | lam b d body => exact hc.lam hf hs hpre hcoh ih
    | pi b res d c => exact hc.pi hf hs hpre hcoh ih
    | letE c r ty v b => exact hc.letE hf hs hpre hcoh ih
    | proj s i e => exact hc.proj hf hs hpre hcoh ih
    | natLit n => exact hc.natLit hf hs hpre hcoh ih
    | strLit s => exact hc.strLit hf hs hpre hcoh ih
  | evalConst k ls c => exact hc.evalConst hf hs hpre hcoh ih
  | headValue k ls h => exact hc.headValue hf hs hpre hcoh ih
  | apply k f s => exact hc.apply hf hs hpre hcoh ih
  | applyAll k f ss => exact hc.applyAll hf hs hpre hcoh ih
  | fire k h ls args =>
    cases h with
    | ctor c => exact hc.ctor hf hs hpre hcoh ih
    | quotMk c => exact hc.quotMk hf hs hpre hcoh ih
    | quotLift c => exact hc.quotLift hf hs hpre hcoh ih
    | recr r => exact case_recr_of hc.f2 hc.f3 hc.f4 hf hs hpre hcoh ih
    | cases c => exact hc.cases hf hs hpre hcoh ih
    | prim op => exact hc.prim hf hs hpre hcoh ih
    | word w op => exact hc.word hf hs hpre hcoh ih
  | force k s => exact hc.force hf hs hpre hcoh ih
  | forceAll k ss => exact hc.forceAll hf hs hpre hcoh ih

/-- The core, from the cases: at every call a run from `top` makes, `Inv`. -/
theorem core_of_cases (hc : Cases p ann ch) (hf : Facts p ann ch) (hs : ShapeOk p) {top : Call}
    (hsa : SortAgree p ann top) : ∀ c, Reach p top c → Inv p ann ch c := by
  intro c
  induction c using callLt_wf.induction with
  | _ c ih =>
    intro hr hpre
    exact case_all_of hc hf hs hpre (hsa c hr)
      (fun c' hc' => ih c' (transGen_lt hc') (reach_transGen hr hc'))

/-- **P1, relevance preservation** (`preserve`'s approved statement), from the cases. -/
theorem preserve_of_cases (hc : Cases p ann ch) (hf : Facts p ann ch) (hs : ShapeOk p) {top : Call}
    (hsa : SortAgree p ann top) : ∀ c, Reach p top c → Pre p ann ch c → Post p ann ch c :=
  fun c hr hpre => (core_of_cases hc hf hs hsa c hr hpre).1

/-- The precondition propagates along every step but the shielded variable's evaluation
(`pre_step`'s approved statement), from the cases. -/
theorem pre_step_of_cases (hc : Cases p ann ch) (hf : Facts p ann ch) (hs : ShapeOk p) {top : Call}
    (hsa : SortAgree p ann top) {c c' : Call} (hr : Reach p top c) (hc' : Pre p ann ch c)
    (hst : Step p c c')
    (hsh : ¬ ∃ k ls ρ f m r x, c = .eval k ls ρ (.app f (.var x) m r) ∧ c' = .eval k ls ρ (.var x) ∧
      ShieldedIn x ρ (.app f (.var x) m r)) :
    Pre p ann ch c' :=
  (core_of_cases hc hf hs hsa c hr hc').2 c' hst hsh

end IxCC.Src.Relevance.Proof.P1
