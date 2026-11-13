import IxCC.Src.Relevance.Proof.Canonical
import IxCC.Src.Proof.Lazify
import IxCC.Lam.Erase.Proof.Rel
import IxCC.Recheck.Proof.Soundness
import IxCC.Recheck.Proof.Parts

/-! # P1: relevance preservation (statements; engineer RN's draft 1, revised by engineer RO)

On a program the verifier's checks accept, SrcEval never yields the irrelevance marker at a
position that is read. Hypotheses, on the program SrcEval runs (`Lazify`'s image of the checked
one, `facts_modeEq`):

* `Facts`: L1's propositions, `WellAnnotatedC` (tiers S and C, C7 among them: `TermC` has no case
  for a sort or a Π) and `Canonical` (`checkCanonical`, with the structure the kernel ensures:
  `dense`, `rules`, `univs`, `ctorRecords`, `subsingletonFields`, `finProof`);
* `ShapeOk`: one constructor per inductive and index, the one structural fact no check of the
  front end decides; under `Recheck.run`'s acceptance it is `erase_progWF`'s (`shapeOk_of_run`);
* `SortAgree`: at every call SrcEval makes from the root, a marker that comes from a position
  irrelevant **by sort** (never one written erased) meets a receiver that ignores it. True of well
  typed programs, the erased-misuse ones included; discharged by kernel typing in progress (T6).

Conclusions: `preserve` (every reachable call whose precondition holds returns `Live` values),
`pre_step` (the precondition propagates along every step but one: the evaluation of a shielded
variable), `reads_live` (what a call reads is `Live`), `run_live` (the root), and the consumption:
`Front.GoesWrongLive`, `Front.goesWrong_live`, `sound_live`.

Every statement is exact; proofs are `sorry`. -/

set_option autoImplicit false

namespace IxCC.Src.Relevance.Proof.P1

open IxCC.Src
open Check Check.Canonical
open IxCC.Lam.Erase.Proof (Agree)

/-! ## Structure no check of the front end decides -/

/-- One constructor per inductive and index (`Erase.Proof.ProgWF.ctorIn`): F2 and F5 select a
rule by the major's constructor index, and `Canonical.rules` names that rule's constructor. -/
structure ShapeOk (p : Program) : Prop where
  ctorUnique : ∀ c c' sf sf' lv lv' ind j np np' nf nf' ty ty',
    p.decl? c = some (.ctor sf lv ind j np nf ty) → p.decl? c' = some (.ctor sf' lv' ind j np' nf' ty') →
    c = c'

/-! ## L1's facts on the program SrcEval runs -/

/-- L1's propositions (`check_soundC`, `checkCanonical_sound`) on `p`. -/
structure Facts (p : Program) (ann : Ann) (ch : Checked) : Prop where
  wa : WellAnnotatedC p ann ch
  canon : Canonical p ann ch
  /-- A reached instance's constant is reached (`check`'s `reached` is its instances' constants):
  `Canonical`'s per-constant clauses are over `ch.reached`, the evaluator meets `ch.instances`. -/
  reached : ∀ inst ∈ ch.instances, inst.1 ∈ ch.reached

/-- Lazify changes only application modes, which no fact of `Facts` reads. -/
theorem facts_modeEq {p₀ p : Program} {ann : Ann} {ch : Checked}
    (hc : check p₀ ann = .ok ch) (hk : checkCanonical p₀ ann ch = []) (hme : Program.ModeEq p₀ p) :
    Facts p ann ch := sorry

/-! ## Receivers that ignore an argument -/

/-- The constant of a special head (none for a primitive or word operation). -/
def headConst? : Head → Option CId
  | .ctor c | .quotMk c | .quotLift c | .recr c | .cases c => some c
  | .prim _ | .word .. => none

/-- Special head `h` at levels `ls` does not read its argument `j` relevantly: its constant's
parameter class there is irrelevant (a primitive or word operation reads every argument). -/
def HeadIgnores (ann : Ann) (h : Head) (ls : Levels) (j : Nat) : Prop :=
  ∃ c cr r, headConst? h = some c ∧ ann.constRel? c = some cr ∧ cr.params[j]? = some r ∧
    r.irrAt ls = true

/-- A special head as SrcEval met it: its constant (if any) is a reached instance at a profile
agreeing with `ls`, and a word operation comes from a reached `word` entry (where one is reached,
`Canonical.finProof` has `Fin.mk` drop the proof field F6w builds with the marker). -/
def HeadSeen (p : Program) (ch : Checked) (ls : Levels) (h : Head) : Prop :=
  (∀ c, headConst? h = some c → ∃ q, Agree ls q ∧ (c, q) ∈ ch.instances) ∧
  (∀ w op, h = .word w op → ∃ c ∈ ch.reached, ∃ thm, p.table.resolveOf c = some (.word w op thm))

/-- `v`, applied to one more slot, does not read it: a closure whose binder is irrelevant at its
levels, a partial application whose head ignores the next position, or a value that applying is
stuck on (A3). -/
def IgnoresNext (ann : Ann) : Value → Prop
  | .clo b _ _ _ ls => b.rel.irrAt ls = true
  | .pap h ls args => HeadIgnores ann h ls args.length
  | _ => True

/-- A minor premise's slot ignores its argument `i`: it is (or suspends) a λ-telescope whose
binder `i` is irrelevant at its levels, or a value applying is stuck on. Syntactic: C3 sees the
minor's leading λs (`lamRels`). -/
def IgnoresSlot : Slot → Nat → Prop
  | .val (.clo b d body _ ls), i => ∃ r, (lamRels (.lam b d body))[i]? = some r ∧ r.irrAt ls = true
  | .val (.pap ..), _ => False
  | .val _, _ => True
  | .name t _ ls, i => ∃ r, (lamRels t)[i]? = some r ∧ r.irrAt ls = true

/-- A slot holding the marker. -/
def MarkerSlot (s : Slot) : Prop := ∃ t ρ ls, s = .val (.irr t ρ ls)

/-- The per-minor fact of an eliminator's partial application: every minor present ignores each
field written erased of each constructor whose rule dispatches it (C3's `MinorC`; at a `case`
entry minor `j` meets rule `j`). Vacuous for any other head. -/
def MinorsIgnore (p : Program) (ann : Ann) (h : Head) (args : List Slot) : Prop :=
  ∀ c shape, headConst? h = some c → elimShape? p c = some shape →
    ∀ pos j kidx, (pos, j, kidx) ∈ shape.minors → ∀ s, args[pos]? = some s →
      ∀ k fields, ruleCtorFields p ann shape.recr kidx = some (k, fields) →
        ∀ i, i < fields.length → fieldWrittenErased p k i = true → IgnoresSlot s i

/-- Variable `x` is **shielded** in `t` under `ρ`: `t` is a spine headed by another variable whose
slot ignores argument `n`, and `x` occurs in `t` only as that argument (`ForwardOk`'s shape at the
top of a rule body, for a field written erased passed to the dispatched minor). -/
def ShieldedIn (x : Nat) (ρ : Env) (t : Term) : Prop :=
  ∃ h n s, t.spineL.1 = .var h ∧ h ≠ x ∧ ρ[h]? = some s ∧ IgnoresSlot s n ∧
    (∃ a, t.spineL.2[n]? = some a ∧ a.1 = .var x) ∧
    ∀ m a, t.spineL.2[m]? = some a → m ≠ n → mentionsVar x a.1 = false

/-- Field `i` of a constructor value `con c ls ..` is read: kept at its levels (`Checked.keeps`,
what readback and erasure keep), and for `Quot.mk` the element unless `Quot.mk`'s parameter class
there is irrelevant at `ls`. -/
def ReadsField (p : Program) (ann : Ann) (ch : Checked) (c : CId) (ls : Levels) (i : Nat) : Bool :=
  match p.decl? c with
  | some (.quot .ctor ..) => !((((ann.constRel? c).bind (·.params[2]?)).map (·.irrAt ls)).getD false)
  | _ => ch.keeps c ls i

/-- The relevant constant references of `t` at profile `q` are reached instances (or outside the
program): `WellAnnotated.closed` for the subterms of reached runtime terms. -/
def RefsHandled (p : Program) (ch : Checked) (q : Profile) (t : Term) : Prop :=
  ∀ r ∈ t.relevantRefs q [], Handled p ch.instances r

/-- The facts a term carries at profile `q` under binder classes `bs`: tier C, its references
reached, its universe arguments counted. -/
structure TermOk (p : Program) (ann : Ann) (ch : Checked) (q : Profile) (bs : List Rel) (t : Term) :
    Prop where
  c : TermC p ann q bs t
  refs : RefsHandled p ch q t
  univs : univsOk p t = true

/-- A value that is not a partial application of an eliminator over a field written erased.
Such a partial application exists only inside the evaluation of a saturated spine (C3's
`partialElim`/`bareHead`, `Canonical.redirects`) or at a root, so every value stored in a slot, a
field or an environment is `Whole`; only there do its minors arrive with C3's facts. -/
def Whole (p : Program) (v : Value) : Prop :=
  ∀ h ls args, v = .pap h ls args → ∀ c shape, headConst? h = some c → elimShape? p c = some shape →
    erasedMinors p shape = false

/-- A term whose value is `Whole`: its spine head is no eliminator over a field written erased
applied to fewer arguments than its arity (what `ElimC` and `TermC.const` give). -/
def WholeTerm (p : Program) (t : Term) : Prop :=
  ∀ c us shape, t.spineL.1 = .const c us → elimShape? p c = some shape → erasedMinors p shape = true →
    shape.arity ≤ t.spineL.2.length

/-! ## `Live`: no marker at a read position, by provenance -/

mutual

/-- A value with no marker at a position that is read. A closure and a suspension are `Live` by
provenance (the facts of the λ they come from, and their environment), not by behaviour, so the
definition is strictly positive. A marker is never `Live`. -/
inductive Live (p : Program) (ann : Ann) (ch : Checked) : Value → Prop
  | lit (n : Nat) : Live p ann ch (.lit n)
  | str (s : String) : Live p ann ch (.str s)
  /-- Every field is `Live` or a marker, a field that is read is `Live`, and none is a partial eliminator. -/
  | con {c : CId} {ls : Levels} {ps : List Slot} {fs : List Value} :
      (∀ i v, fs[i]? = some v → (ReadsField p ann ch c ls i = true ∨ v.isIrr = false) →
        Live p ann ch v) →
      (∀ (i : Nat) (v : Value), fs[i]? = some v → Whole p v) →
      Live p ann ch (.con c ls ps fs)
  /-- The closure of `λ b d. body` under `ρ`, from a term with the facts at a profile agreeing
  with its levels. -/
  | clo {b : Binder} {d body : Term} {ρ : Env} {ls : Levels} (q : Profile) (bs : List Rel) :
      Agree ls q → TermOk p ann ch q bs (.lam b d body) → EnvOk p ann ch ls bs ρ (.lam b d body) →
      Live p ann ch (.clo b d body ρ ls)
  /-- A partial application of a special head reached at its levels: each argument `Live`
  unless it is a marker at a position the head ignores; each minor present ignores its
  dispatching constructors' fields written erased. -/
  | pap {h : Head} {ls : Levels} {args : List Slot} :
      HeadSeen p ch ls h →
      (∀ j s, args[j]? = some s → ¬ (HeadIgnores ann h ls j ∧ MarkerSlot s) → LiveSlot p ann ch s) →
      MinorsIgnore p ann h args → args.length < p.headArity h →
      Live p ann ch (.pap h ls args)

/-- A `Live`, `Whole` value, or a suspension of a term with the facts under an environment that has them. -/
inductive LiveSlot (p : Program) (ann : Ann) (ch : Checked) : Slot → Prop
  | val {v : Value} : Live p ann ch v → Whole p v → LiveSlot p ann ch (.val v)
  | name {t : Term} {ρ : Env} {ls : Levels} (q : Profile) (bs : List Rel) :
      Agree ls q → TermOk p ann ch q bs t → EnvOk p ann ch ls bs ρ t → LiveSlot p ann ch (.name t ρ ls)

/-- The environment of an evaluation of `t`: one slot per binder class, and every slot at a binder
relevant at `ls` that `t` mentions is `LiveSlot`, unless it is shielded in `t`. -/
inductive EnvOk (p : Program) (ann : Ann) (ch : Checked) : Levels → List Rel → Env → Term → Prop
  | mk {ls : Levels} {bs : List Rel} {ρ : Env} {t : Term} :
      ρ.length = bs.length →
      (∀ x s r, ρ[x]? = some s → bs[x]? = some r → r.irrAt ls = false → mentionsVar x t = true →
        ¬ ShieldedIn x ρ t → LiveSlot p ann ch s) →
      EnvOk p ann ch ls bs ρ t

end

/-! ## SrcEval's calls and one step of each -/

/-- A call of SrcEval's mutual block, with its arguments. -/
inductive Call where
  | eval (k : Nat) (ls : Levels) (ρ : Env) (t : Term)
  | evalConst (k : Nat) (ls : Levels) (c : CId)
  | headValue (k : Nat) (ls : Levels) (h : Head)
  | apply (k : Nat) (f : Value) (s : Slot)
  | applyAll (k : Nat) (f : Value) (ss : List Slot)
  | fire (k : Nat) (h : Head) (ls : Levels) (args : List Slot)
  | force (k : Nat) (s : Slot)
  | forceAll (k : Nat) (ss : List Slot)

/-- F2/F3/F4's rule choice (`fire`'s `chosen` at `.recr`, verbatim). -/
def recChosen (p : Program) (k : Nat) (ls : Levels) (np nmot nmin ni : Nat) (ind : CId)
    (kind : RecKind) (args : List Slot) : Sem.Result (Nat × List Slot) :=
  match kind with
  | .empty => .trap
  | .ordinary =>
    match force p k (args.getD (np + nmot + nmin + ni) default) with
    | .ok major => Sem.Result.ofOption (p.selectRule ind np major)
    | .timeout => .timeout
    | .resource r => .resource r
    | .trap => .trap
    | .stuck => .stuck
  | .subsingleton _ srcs =>
    let indices := (args.drop (np + nmot + nmin)).take ni
    .ok (0, srcs.map fun
      | .index i => indices.getD i (Slot.irrNone ls)
      | .proof => Slot.irrNone ls)

/-- F5's constructor choice (`fire`'s `chosen` at `.cases`, verbatim). -/
def caseChosen (p : Program) (k : Nat) (ls : Levels) (np ni : Nat) (ind : CId) (kind : RecKind)
    (args : List Slot) : Sem.Result (Nat × List Slot) :=
  match kind with
  | .empty => .trap
  | .ordinary =>
    match force p k (args.getD (np + 1 + ni) default) with
    | .ok major => Sem.Result.ofOption (p.selectRule ind np major)
    | .timeout => .timeout
    | .resource r => .resource r
    | .trap => .trap
    | .stuck => .stuck
  | .subsingleton _ srcs =>
    .ok (0, srcs.map fun
      | .index i => args.getD (np + 1 + i) (Slot.irrNone ls)
      | .proof => Slot.irrNone ls)

/-- One step: the call `c` makes the call `c'` (one constructor per call site of
`Src/Semantics.lean`, the results of earlier sibling calls as premises). -/
inductive Step (p : Program) : Call → Call → Prop
  -- E1
  | var {k ls ρ i s} : ρ[i]? = some s → Step p (.eval k ls ρ (.var i)) (.force k s)
  -- E5
  | letIrr {k ls ρ c r ty v b} : r.irrAt ls = true →
      Step p (.eval k ls ρ (.letE c r ty v b)) (.eval k ls (.val (.irr (some v) ρ ls) :: ρ) b)
  | letVal {k ls ρ c r ty v b} : r.irrAt ls = false →
      Step p (.eval k ls ρ (.letE c r ty v b)) (.eval k ls ρ v)
  | letBody {k ls ρ c r ty v b x} : r.irrAt ls = false → eval p k ls ρ v = .ok x →
      Step p (.eval k ls ρ (.letE c r ty v b)) (.eval k ls (.val x :: ρ) b)
  -- E6
  | proj {k ls ρ s i e} : Step p (.eval k ls ρ (.proj s i e)) (.eval k ls ρ e)
  -- E7
  | appFun {k ls ρ f a m r} : Step p (.eval k ls ρ (.app f a m r)) (.eval k ls ρ f)
  | appIrr {k ls ρ f a m r fv} : eval p k ls ρ f = .ok fv → r.irrAt ls = true →
      Step p (.eval k ls ρ (.app f a m r)) (.apply k fv (.val (.irr (some a) ρ ls)))
  | appArg {k ls ρ f a r fv} : eval p k ls ρ f = .ok fv → r.irrAt ls = false →
      Step p (.eval k ls ρ (.app f a .strict r)) (.eval k ls ρ a)
  | appStrict {k ls ρ f a r fv x} : eval p k ls ρ f = .ok fv → r.irrAt ls = false →
      eval p k ls ρ a = .ok x → Step p (.eval k ls ρ (.app f a .strict r)) (.apply k fv (.val x))
  | appName {k ls ρ f a r fv} : eval p k ls ρ f = .ok fv → r.irrAt ls = false →
      Step p (.eval k ls ρ (.app f a .byName r)) (.apply k fv (.name a ρ ls))
  -- E8
  | const {k ls ρ c us} : Step p (.eval k ls ρ (.const c us)) (.evalConst k (us.map (evalUniv ls)) c)
  | prim {k ls c op} : p.table.resolveOf c = some (.prim op) →
      Step p (.evalConst k ls c) (.headValue k ls (.prim op))
  | word {k ls c w op thm} : p.table.resolveOf c = some (.word w op thm) →
      Step p (.evalConst k ls c) (.headValue k ls (.word w op))
  | csimp {k ls c g vs thm} : p.table.resolveOf c = some (.csimp g vs thm) →
      Step p (.evalConst (k + 1) ls c) (.eval k ls [] (.const g vs))
  | eqn {k ls c thm body} : p.table.resolveOf c = some (.eqn thm body) →
      Step p (.evalConst (k + 1) ls c) (.eval k ls [] body)
  | case {k ls c r} : p.table.resolveOf c = some (.case r) →
      Step p (.evalConst k ls c) (.headValue k ls (.cases c))
  | ctor {k ls c sf lv ind cidx np nf ty} : p.table.resolveOf c = none →
      p.decl? c = some (.ctor sf lv ind cidx np nf ty) → Step p (.evalConst k ls c) (.headValue k ls (.ctor c))
  | recr {k ls c sf kk lv np nmot nmin ni ind rules ty} : p.table.resolveOf c = none →
      p.decl? c = some (.recr sf kk lv np nmot nmin ni ind rules ty) →
      Step p (.evalConst k ls c) (.headValue k ls (.recr c))
  | quotMk {k ls c lv ty} : p.table.resolveOf c = none → p.decl? c = some (.quot .ctor lv ty) →
      Step p (.evalConst k ls c) (.headValue k ls (.quotMk c))
  | quotLift {k ls c lv ty} : p.table.resolveOf c = none → p.decl? c = some (.quot .lift lv ty) →
      Step p (.evalConst k ls c) (.headValue k ls (.quotLift c))
  | defn {k ls c lv ty v} : p.table.resolveOf c = none → p.decl? c = some (.defn .defn .safe lv ty v) →
      Step p (.evalConst (k + 1) ls c) (.eval k ls [] v)
  | opaq {k ls c lv ty v} : p.table.resolveOf c = none → p.decl? c = some (.defn .opaq .safe lv ty v) →
      p.table.isOpaqueByValue c = true → Step p (.evalConst (k + 1) ls c) (.eval k ls [] v)
  -- headValue
  | nullary {k ls h} : p.headArity h = 0 → Step p (.headValue k ls h) (.fire k h ls [])
  -- A1, A2
  | beta {k b d body ρ ls s} : b.propWhen.allowsBeta ls = true →
      Step p (.apply (k + 1) (.clo b d body ρ ls) s) (.eval k ls (s :: ρ) body)
  | papFire {k h ls args s} : (args ++ [s]).length = p.headArity h →
      Step p (.apply k (.pap h ls args) s) (.fire k h ls (args ++ [s]))
  -- applyAll
  | allHead {k f s ss} : Step p (.applyAll k f (s :: ss)) (.apply k f s)
  | allRest {k f s ss v} : apply p k f s = .ok v → Step p (.applyAll k f (s :: ss)) (.applyAll k v ss)
  -- F1
  | ctorArgs {k c ls args sf lv ind cidx np nf ty} : p.decl? c = some (.ctor sf lv ind cidx np nf ty) →
      Step p (.fire k (.ctor c) ls args) (.forceAll k (args.drop np))
  -- F7
  | mkArg {k c ls α r a} : Step p (.fire k (.quotMk c) ls [α, r, a]) (.force k a)
  -- F8
  | liftQuot {k c ls α r β f h q} : Step p (.fire (k + 1) (.quotLift c) ls [α, r, β, f, h, q]) (.force k q)
  | liftFun {k c ls α r β f h q c' l' ps a} : force p k q = .ok (.con c' l' ps [a]) →
      p.isQuotCtor c' = true → Step p (.fire (k + 1) (.quotLift c) ls [α, r, β, f, h, q]) (.force k f)
  | liftApply {k c ls α r β f h q c' l' ps a fv} : force p k q = .ok (.con c' l' ps [a]) →
      p.isQuotCtor c' = true → force p k f = .ok fv →
      Step p (.fire (k + 1) (.quotLift c) ls [α, r, β, f, h, q]) (.apply k fv (.val a))
  -- F2, F3
  | recMajor {k r ls args sf kk lv np nmot nmin ni ind rules ty} :
      p.decl? r = some (.recr sf kk lv np nmot nmin ni ind rules ty) →
      (p.table.recKindOf r).map (·.atLevels ls) = some .ordinary →
      Step p (.fire (k + 1) (.recr r) ls args) (.force k (args.getD (np + nmot + nmin + ni) default))
  | recRule {k r ls args sf kk lv np nmot nmin ni ind rules ty kind j fields rule body} :
      p.decl? r = some (.recr sf kk lv np nmot nmin ni ind rules ty) →
      (p.table.recKindOf r).map (·.atLevels ls) = some kind →
      recChosen p k ls np nmot nmin ni ind kind args = .ok (j, fields) → rules[j]? = some rule →
      peelLams (args.take (np + nmot + nmin) ++ fields).length rule.rhs = some body →
      Step p (.fire (k + 1) (.recr r) ls args) (.eval k ls (args.take (np + nmot + nmin) ++ fields).reverse body)
  -- F5
  | caseMajor {k c ls args r sf kk lv np nmot nmin ni ind rules ty} :
      p.table.resolveOf c = some (.case r) → p.decl? r = some (.recr sf kk lv np nmot nmin ni ind rules ty) →
      (p.table.recKindOf r).map (·.atLevels ls) = some .ordinary →
      Step p (.fire (k + 1) (.cases c) ls args) (.force k (args.getD (np + 1 + ni) default))
  | caseMinor {k c ls args r sf kk lv np nmot nmin ni ind rules ty kind j fields} :
      p.table.resolveOf c = some (.case r) → p.decl? r = some (.recr sf kk lv np nmot nmin ni ind rules ty) →
      (p.table.recKindOf r).map (·.atLevels ls) = some kind →
      caseChosen p k ls np ni ind kind args = .ok (j, fields) →
      Step p (.fire (k + 1) (.cases c) ls args) (.force k (args.getD (np + 1 + ni + 1 + j) default))
  | caseApply {k c ls args r sf kk lv np nmot nmin ni ind rules ty kind j fields mv} :
      p.table.resolveOf c = some (.case r) → p.decl? r = some (.recr sf kk lv np nmot nmin ni ind rules ty) →
      (p.table.recKindOf r).map (·.atLevels ls) = some kind →
      caseChosen p k ls np ni ind kind args = .ok (j, fields) →
      force p k (args.getD (np + 1 + ni + 1 + j) default) = .ok mv →
      Step p (.fire (k + 1) (.cases c) ls args) (.applyAll k mv fields)
  -- F6, F6w
  | primArgs {k op ls args} : Step p (.fire k (.prim op) ls args) (.forceAll k args)
  | wordArgs {k w op ls args} : Step p (.fire k (.word w op) ls args) (.forceAll k args)
  -- force, forceAll
  | forceName {k t ρ ls} : Step p (.force (k + 1) (.name t ρ ls)) (.eval k ls ρ t)
  | allForce {k s ss} : Step p (.forceAll k (s :: ss)) (.force k s)
  | allForceRest {k s ss v} : force p k s = .ok v → Step p (.forceAll k (s :: ss)) (.forceAll k ss)

/-- The calls a run starting at `top` makes. -/
inductive Reach (p : Program) (top : Call) : Call → Prop
  | refl : Reach p top top
  | step {c c' : Call} : Reach p top c → Step p c c' → Reach p top c'

/-- A marker is never `Live`. -/
theorem live_not_irr {p : Program} {ann : Ann} {ch : Checked} {v : Value} (h : Live p ann ch v) :
    v.isIrr = false := sorry

/-! ## `SortAgree`: markers from positions irrelevant by sort -/

/-- The leading binders of a λ-telescope. -/
def lamBinders : Term → List Binder
  | .lam b _ t => b :: lamBinders t
  | _ => []

/-- The last argument of the spine `t` is at a position written erased: at a constant head, a
parameter its type writes erased; at a λ head, a binder written erased. (`KernelFront.erasedAt`
acts only there; every other irrelevant tag is a sort tag, `tagOk`.) -/
def WrittenErasedArg (p : Program) (t : Term) : Prop :=
  match t.spineL with
  | (.const c _, args) => ∃ d, p.decl? c = some d ∧ args.length - 1 ∈ erasedParams d.type
  | (.lam b d body, args) =>
    ∃ bd, (lamBinders (.lam b d body))[args.length - 1]? = some bd ∧ writtenErased bd = true
  | _ => False

/-- Slot `n` of an F2/F3 activation (`npre` parameter, motive and minor slots, then the fields) comes from
a position written erased: a recursor parameter its type writes erased, a field its rule's
constructor writes erased, or (F3) an index slot the type writes erased. -/
def RecSlotErased (p : Program) (ty : Term) (npre : Nat) (kind : RecKind) (rule : Rule) (n : Nat) : Prop :=
  (n < npre ∧ n ∈ erasedParams ty) ∨
  (npre ≤ n ∧ fieldWrittenErased p rule.ctor (n - npre) = true) ∨
  (∃ w srcs i, kind = .subsingleton w srcs ∧ npre ≤ n ∧ srcs[n - npre]? = some (.index i) ∧
    npre + i ∈ erasedParams ty)

/-- Field slot `i` of an F5 activation of the `case` key `c` (recursor rules `rules`, choice `j`)
comes from a position written erased: a field the constructor writes erased, or (F3-style) an index
slot the key's type writes erased. -/
def CaseFieldErased (p : Program) (c : CId) (np : Nat) (rules : List Rule) (kind : RecKind) (j i : Nat) :
    Prop :=
  ((rules[j]?).map fun rule => fieldWrittenErased p rule.ctor i).getD false = true ∨
  (∃ w srcs i' d, kind = .subsingleton w srcs ∧ srcs[i]? = some (.index i') ∧ p.decl? c = some d ∧
    np + 1 + i' ∈ erasedParams d.type)

/-- Applying `f` to `ss` one by one at clock `k` (as `applyAll`), each marker slot whose position
`exempt` does not exempt meets a value that ignores it. -/
def MarkersIgnored (p : Program) (ann : Ann) (k : Nat) (exempt : Nat → Prop) :
    Nat → Value → List Slot → Prop
  | _, _, [] => True
  | i, f, s :: ss => (MarkerSlot s → ¬ exempt i → IgnoresNext ann f) ∧
      ∀ v, apply p k f s = .ok v → MarkersIgnored p ann k exempt (i + 1) v ss

/-- The sort events of one call. Each constrains a marker that does **not** come from a position
written erased; where L1's facts name the receiver of a marker written erased, nothing is asked. -/
def SortCoherent (p : Program) (ann : Ann) : Call → Prop
  /- (a) E7: an argument irrelevant at the run's levels, at a position not written erased: the
  function value ignores it. -/
  | .eval k ls ρ (.app f a m r) =>
      r.irrAt ls = true → ¬ WrittenErasedArg p (.app f a m r) →
      ∀ fv, eval p k ls ρ f = .ok fv → IgnoresNext ann fv
  /- (f) E6: a projection yields the marker only from a field written erased (which C3 refuses). -/
  | .eval k ls ρ (.proj _ i e) =>
      ∀ c lsv ps fs v, eval p k ls ρ e = .ok (.con c lsv ps fs) → fs[i]? = some v → v.isIrr = true →
        fieldWrittenErased p c i = true
  /- (d) F2/F3: a marker slot meets a rule λ irrelevant at the run's levels, unless it is a field
  is written erased (`RecSlotErased`; IxCC does not check rule λ classes). -/
  | .fire (k + 1) (.recr r) ls args =>
      ∀ sf kk lv np nmot nmin ni ind rules ty kind j fields rule,
        p.decl? r = some (.recr sf kk lv np nmot nmin ni ind rules ty) →
        (p.table.recKindOf r).map (·.atLevels ls) = some kind →
        recChosen p k ls np nmot nmin ni ind kind args = .ok (j, fields) → rules[j]? = some rule →
        let pre := args.take (np + nmot + nmin)
        ∀ n s, (pre ++ fields)[n]? = some s → MarkerSlot s →
          ¬ RecSlotErased p ty pre.length kind rule n →
          ∃ b, (lamRels rule.rhs)[n]? = some b ∧ b.irrAt ls = true
  /- (c) F5: a marker field, of a field its constructor does not write erased, meets an ignoring
  receiver (the minor's binder, or what the minor returns past its λs). -/
  | .fire (k + 1) (.cases c) ls args =>
      ∀ r sf kk lv np nmot nmin ni ind rules ty kind j fields mv,
        p.table.resolveOf c = some (.case r) →
        p.decl? r = some (.recr sf kk lv np nmot nmin ni ind rules ty) →
        (p.table.recKindOf r).map (·.atLevels ls) = some kind →
        caseChosen p k ls np ni ind kind args = .ok (j, fields) →
        force p k (args.getD (np + 1 + ni + 1 + j) default) = .ok mv →
        MarkersIgnored p ann k (CaseFieldErased p c np rules kind j) 0 mv fields
  /- (e) F8: a marker element, unless `Quot.mk`'s element is written erased, meets a function that
  ignores it. -/
  | .fire (k + 1) (.quotLift _) _ [_, _, _, f, _, q] =>
      ∀ c' l' ps a fv, force p k q = .ok (.con c' l' ps [a]) → p.isQuotCtor c' = true →
        force p k f = .ok fv → a.isIrr = true → (¬ ∃ d, p.decl? c' = some d ∧ 2 ∈ erasedParams d.type) →
        IgnoresNext ann fv
  | _ => True

/-- The sort events of every call a run from `top` makes are coherent. -/
def SortAgree (p : Program) (ann : Ann) (top : Call) : Prop :=
  ∀ c, Reach p top c → SortCoherent p ann c

/-- `SortAgree` for `Src.run p k root xs`: δ on the root, then `applyAll`. -/
def RunSortAgree (p : Program) (ann : Ann) (k : Nat) (root : CId) (xs : List Value) : Prop :=
  SortAgree p ann (.evalConst k [] root) ∧
    ∀ f, evalConst p k [] root = .ok f → SortAgree p ann (.applyAll k f (xs.map .val))

/-! ## Preconditions and results -/

/-- An evaluation's precondition: a profile agreeing with the levels, binder classes, the
environment invariant, the term's references and universe counts, and tier C at the term: a
whole relevant term (`TermC`), an inner prefix of a spine whose full spine has `HeadC` (C3 is
decided on the saturated spine), or a bare constant that is no eliminator over a field written
erased (a `csimp` redirect's target, `Canonical.redirects`). -/
def Frame (p : Program) (ann : Ann) (ch : Checked) (ls : Levels) (ρ : Env) (t : Term) : Prop :=
  ∃ q bs, Agree ls q ∧ EnvOk p ann ch ls bs ρ t ∧ RefsHandled p ch q t ∧ univsOk p t = true ∧
    (TermC p ann q bs t ∨
     (∃ more : List Term.Arg, more ≠ [] ∧ SpineC p ann q bs t ∧
        HeadC p ann q (Term.mkApps t more).spineL.1 (Term.mkApps t more).spineL.2) ∨
     (∃ c us, t = .const c us ∧ ∀ shape, elimShape? p c = some shape → erasedMinors p shape = false))

/-- `s` fits the next argument of `f`: `LiveSlot` where `f` reads it, and, at an eliminator's
minor position, the per-minor fact. -/
def SlotFits (p : Program) (ann : Ann) (ch : Checked) : Value → Slot → Prop
  | .clo b _ _ _ ls, s => b.rel.irrAt ls = false → LiveSlot p ann ch s
  | .pap h ls args, s =>
      (¬ (HeadIgnores ann h ls args.length ∧ MarkerSlot s) → LiveSlot p ann ch s) ∧
        MinorsIgnore p ann h (args ++ [s])
  | _, _ => True

/-- `ss` fit `f` one by one, as `applyAll` applies them at clock `k`. -/
def AllFit (p : Program) (ann : Ann) (ch : Checked) (k : Nat) : Value → List Slot → Prop
  | _, [] => True
  | f, s :: ss => SlotFits p ann ch f s ∧ ∀ v, apply p k f s = .ok v → AllFit p ann ch k v ss

/-- A saturated special head's arguments (what `Live.pap` gives, at the arity). -/
structure FireOk (p : Program) (ann : Ann) (ch : Checked) (h : Head) (ls : Levels) (args : List Slot) :
    Prop where
  arity : args.length = p.headArity h
  inst : HeadSeen p ch ls h
  live : ∀ j s, args[j]? = some s → ¬ (HeadIgnores ann h ls j ∧ MarkerSlot s) → LiveSlot p ann ch s
  minors : MinorsIgnore p ann h args

/-- Each call's precondition. -/
def Pre (p : Program) (ann : Ann) (ch : Checked) : Call → Prop
  | .eval _ ls ρ t => Frame p ann ch ls ρ t
  | .evalConst _ ls c => p.size ≤ c ∨ ∃ q, Agree ls q ∧ (c, q) ∈ ch.instances
  | .headValue _ ls h => HeadSeen p ch ls h
  | .apply _ f s => Live p ann ch f ∧ SlotFits p ann ch f s
  | .applyAll k f ss => Live p ann ch f ∧ AllFit p ann ch k f ss
  | .fire _ h ls args => FireOk p ann ch h ls args
  | .force _ s => LiveSlot p ann ch s ∨ MarkerSlot s
  | .forceAll _ ss => ∀ s ∈ ss, LiveSlot p ann ch s ∨ MarkerSlot s

/-- Each call's result, when it returns: `Live` (a forced marker excepted), and `Whole` where the call
is no inner part of a spine. -/
def Post (p : Program) (ann : Ann) (ch : Checked) : Call → Prop
  | .eval k ls ρ t => ∀ v, eval p k ls ρ t = .ok v → Live p ann ch v ∧ (WholeTerm p t → Whole p v)
  | .evalConst k ls c => ∀ v, evalConst p k ls c = .ok v → Live p ann ch v ∧
      ((∀ shape, elimShape? p c = some shape → erasedMinors p shape = false) → Whole p v)
  | .headValue k ls h => ∀ v, headValue p k ls h = .ok v → Live p ann ch v ∧
      ((∀ c shape, headConst? h = some c → elimShape? p c = some shape → erasedMinors p shape = false) →
        Whole p v)
  | .apply k f s => ∀ v, apply p k f s = .ok v → Live p ann ch v ∧ (Whole p f → Whole p v)
  | .applyAll k f ss => ∀ v, applyAll p k f ss = .ok v → Live p ann ch v ∧ (Whole p f → Whole p v)
  | .fire k h ls args => ∀ v, fire p k h ls args = .ok v → Live p ann ch v ∧ Whole p v
  | .force k s => ∀ v, force p k s = .ok v → (v.isIrr = false → Live p ann ch v) ∧ Whole p v
  | .forceAll k ss => ∀ vs, forceAll p k ss = .ok vs → ∀ v ∈ vs, (v.isIrr = false → Live p ann ch v) ∧ Whole p v

/-- What a call reads: the function an application returns from, the structure a projection
reads and the field it yields, the major F2 or F5 selects a rule by, and the quotient F8 lifts. -/
def Reads (p : Program) (ann : Ann) (ch : Checked) : Call → Prop
  | .apply k f s => (∃ v, apply p k f s = .ok v) → Live p ann ch f
  | .eval k ls ρ (.proj s i e) => ∀ v w, eval p k ls ρ e = .ok v → p.projectField s i v = .ok w →
      Live p ann ch v ∧ Live p ann ch w
  | .fire (k + 1) (.recr r) _ args =>
      ∀ sf kk lv np nmot nmin ni ind rules ty major jf,
        p.decl? r = some (.recr sf kk lv np nmot nmin ni ind rules ty) →
        force p k (args.getD (np + nmot + nmin + ni) default) = .ok major →
        p.selectRule ind np major = some jf → Live p ann ch major
  | .fire (k + 1) (.cases c) _ args =>
      ∀ r sf kk lv np nmot nmin ni ind rules ty major jf,
        p.table.resolveOf c = some (.case r) → p.decl? r = some (.recr sf kk lv np nmot nmin ni ind rules ty) →
        force p k (args.getD (np + 1 + ni) default) = .ok major →
        p.selectRule ind np major = some jf → Live p ann ch major
  | .fire (k + 1) (.quotLift _) _ [_, _, _, _, _, q] =>
      ∀ c' l' ps a, force p k q = .ok (.con c' l' ps [a]) → p.isQuotCtor c' = true →
        Live p ann ch (.con c' l' ps [a])
  | _ => True

/-! ## P1 -/

section

variable {p : Program} {ann : Ann} {ch : Checked}

/-- **P1, relevance preservation.** Under L1's facts, the structure, and coherent sort events,
every call a run makes whose precondition holds returns only `Live` values. -/
theorem preserve (hf : Facts p ann ch) (hs : ShapeOk p) {top : Call} (hsa : SortAgree p ann top) :
    ∀ c, Reach p top c → Pre p ann ch c → Post p ann ch c := sorry

/-- The precondition propagates along every step but one: the evaluation of a variable its spine
shields (a dropped field passed to the minor that ignores it), which returns the marker. -/
theorem pre_step (hf : Facts p ann ch) (hs : ShapeOk p) {top : Call} (hsa : SortAgree p ann top)
    {c c' : Call} (hr : Reach p top c) (hc : Pre p ann ch c) (hst : Step p c c')
    (hsh : ¬ ∃ k ls ρ f m r x, c = .eval k ls ρ (.app f (.var x) m r) ∧ c' = .eval k ls ρ (.var x) ∧
      ShieldedIn x ρ (.app f (.var x) m r)) :
    Pre p ann ch c' := sorry

/-- What a call with its precondition reads is `Live`. -/
theorem reads_live (hf : Facts p ann ch) (hs : ShapeOk p) {top : Call} (hsa : SortAgree p ann top) :
    ∀ c, Reach p top c → Pre p ann ch c → Reads p ann ch c := sorry

/-! ### Spine and prefix lemmas (PB) -/

/-- `Result.bind` returning `.ok`. -/
theorem bind_ok_inv {α β : Type} {r : Sem.Result α} {g : α → Sem.Result β} {v : β}
    (h : r.bind g = .ok v) : ∃ x, r = .ok x ∧ g x = .ok v := by
  cases r with
  | ok x => exact ⟨x, rfl, h⟩
  | _ => cases h

/-- `Term.spine.go` with an accumulator appends it. -/
theorem spine_go_acc : ∀ (t : Term) (acc : List Term.Arg),
    Term.spine.go t acc = ((Term.spine.go t []).1, (Term.spine.go t []).2 ++ acc)
  | .app f a m r, acc => by
    simp only [Term.spine.go]
    rw [spine_go_acc f ((a, m, r) :: acc), spine_go_acc f [(a, m, r)]]
    simp
  | .var _, _ | .sort _, _ | .const .., _ | .lam .., _ | .pi .., _ | .letE .., _ | .proj .., _
  | .natLit _, _ | .strLit _, _ => by simp [Term.spine.go]

/-- The spine of an application: its function's, with the argument appended. -/
theorem spineL_app (f a : Term) (m : Mode) (r : Rel) :
    (Term.app f a m r).spineL = (f.spineL.1, f.spineL.2 ++ [(a, m, r)]) := by
  show Term.spine.go (.app f a m r) [] = _
  simp only [Term.spine.go]
  exact spine_go_acc f [(a, m, r)]

/-- A term is the application of its spine's head to its spine's arguments. -/
theorem mkApps_spineL (t : Term) : Term.mkApps t.spineL.1 t.spineL.2 = t := Term.spine_mkApps t

/-- `lamRels` is the classes of `lamBinders`. -/
theorem lamRels_eq : ∀ t : Term, lamRels t = (lamBinders t).map (·.rel)
  | .lam b _ t => by simp only [lamRels, lamBinders, List.map_cons, lamRels_eq t]
  | .var _ | .sort _ | .const .. | .app .. | .pi .. | .letE .. | .proj .. | .natLit _
  | .strLit _ => rfl

private theorem propWhen_lawfulBEq' : LawfulBEq PropWhen where
  rfl := by
    intro a
    cases a with
    | never => rfl
    | allZero ps => show (ps == ps) = true; exact beq_self_eq_true ps
  eq_of_beq := by
    intro a b h
    cases a with
    | never => cases b with
      | never => rfl
      | allZero _ => cases h
    | allZero ps => cases b with
      | never => cases h
      | allZero qs => exact congrArg _ (beq_iff_eq.1 (show (ps == qs) = true from h))

/-- A class irrelevant at every instance is irrelevant at any levels. -/
theorem alwaysIrr_irrAt {r : Rel} (h : r.alwaysIrr = true) (ls : Levels) : r.irrAt ls = true := by
  have hl := propWhen_lawfulBEq'
  unfold Rel.alwaysIrr at h
  unfold Rel.irrAt
  rw [beq_iff_eq.1 h]
  rfl

/-- Applying the closure of a λ-telescope along arguments as many as a binder index of the
telescope whose class is irrelevant at the closure's levels gives a closure whose next binder is
that one. -/
theorem applySpine_lamChain {k : Nat} {ls : Levels} {ρ : Env} :
    ∀ (args : List Term.Arg) (b : Binder) (d body : Term) (ρ' : Env) (ls' : Levels) (r : Rel)
      (fv : Value),
      (lamRels (.lam b d body))[args.length]? = some r → r.irrAt ls' = true →
      applySpine p k ls ρ (.clo b d body ρ' ls') args = .ok fv →
      IgnoresNext ann fv ∧ ∀ h' ls'' as, fv ≠ .pap h' ls'' as
  | [], b, d, body, ρ', ls', r, fv, hr, hirr, he => by
    simp only [applySpine, Sem.Result.ok.injEq] at he
    subst he
    simp only [lamRels, List.length_nil, List.getElem?_cons_zero, Option.some.injEq] at hr
    subst hr
    exact ⟨hirr, fun _ _ _ h => by cases h⟩
  | a :: as, b, d, body, ρ', ls', r, fv, hr, hirr, he => by
    simp only [applySpine] at he
    obtain ⟨s, -, he⟩ := bind_ok_inv he
    obtain ⟨v, hv, he⟩ := bind_ok_inv he
    simp only [lamRels, List.length_cons, List.getElem?_cons_succ] at hr
    cases body with
    | lam b2 d2 body2 =>
      rw [apply_clo] at hv
      split at hv
      · cases k with
        | zero => cases hv
        | succ k' =>
          simp only [Sem.later_succ, eval_lam, Sem.Result.ok.injEq] at hv
          subst hv
          exact applySpine_lamChain as b2 d2 body2 _ ls' r fv hr hirr he
      · cases hv
    | _ => simp [lamRels] at hr

/-- Applying a value that is neither a closure nor a partial application is stuck. -/
theorem applySpine_stuck {k : Nat} {ls : Levels} {ρ : Env} {v : Value}
    (h1 : ∀ b d body ρ' ls', v ≠ .clo b d body ρ' ls') (h2 : ∀ h ls' args, v ≠ .pap h ls' args)
    {a : Term.Arg} {as : List Term.Arg} {fv : Value}
    (he : applySpine p k ls ρ v (a :: as) = .ok fv) : False := by
  simp only [applySpine] at he
  obtain ⟨s, -, he⟩ := bind_ok_inv he
  obtain ⟨w, hw, -⟩ := bind_ok_inv he
  rw [apply_other p k v s h1 h2] at hw
  cases hw

/-- A value of a λ-telescope's chain (`IgnoresSlot` at the length of the spine): what a spine
headed by a slot that ignores argument `n` evaluates to after `n` arguments. -/
theorem applySpine_ignoresSlot {k : Nat} {ls : Levels} {ρ : Env} {s : Slot} {v0 fv : Value}
    {args : List Term.Arg} (hig : IgnoresSlot s args.length) (hv0 : force p k s = .ok v0)
    (he : applySpine p k ls ρ v0 args = .ok fv) :
    IgnoresNext ann fv ∧ ∀ h' ls' as, fv ≠ .pap h' ls' as := by
  cases s with
  | val v =>
    rw [force_val] at hv0
    injection hv0 with e
    subst e
    cases v with
    | clo b d body ρ' ls' =>
      obtain ⟨r, hr, hirr⟩ := hig
      exact applySpine_lamChain args b d body ρ' ls' r fv hr hirr he
    | pap _ _ _ => exact hig.elim
    | lit n =>
      cases args with
      | nil => simp only [applySpine, Sem.Result.ok.injEq] at he; subst he; exact ⟨trivial, fun _ _ _ h => by cases h⟩
      | cons a as => exact (applySpine_stuck (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h) he).elim
    | str s =>
      cases args with
      | nil => simp only [applySpine, Sem.Result.ok.injEq] at he; subst he; exact ⟨trivial, fun _ _ _ h => by cases h⟩
      | cons a as => exact (applySpine_stuck (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h) he).elim
    | con c ls' ps fs =>
      cases args with
      | nil => simp only [applySpine, Sem.Result.ok.injEq] at he; subst he; exact ⟨trivial, fun _ _ _ h => by cases h⟩
      | cons a as => exact (applySpine_stuck (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h) he).elim
    | irr t ρ' ls' =>
      cases args with
      | nil => simp only [applySpine, Sem.Result.ok.injEq] at he; subst he; exact ⟨trivial, fun _ _ _ h => by cases h⟩
      | cons a as => exact (applySpine_stuck (fun _ _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h) he).elim
  | name t ρ' ls' =>
    rw [force_name] at hv0
    cases k with
    | zero => cases hv0
    | succ k' =>
      simp only [Sem.later_succ] at hv0
      obtain ⟨r, hr, hirr⟩ := hig
      cases t with
      | lam b d body =>
        rw [eval_lam] at hv0
        cases hv0
        exact applySpine_lamChain args b d body ρ' ls' r fv hr hirr he
      | _ => simp [lamRels] at hr

/-- A constant reference keeps the references already collected. -/
theorem relevantRefs_mono (q : Profile) {x : Inst} :
    ∀ (t : Term) (acc : List Inst), x ∈ acc → x ∈ t.relevantRefs q acc
  | .const _ _, _, h => List.mem_cons_of_mem _ h
  | .app f a _ r, acc, h => by
    simp only [Term.relevantRefs]
    have h1 := relevantRefs_mono q f acc h
    split
    · exact h1
    · exact relevantRefs_mono q a _ h1
  | .lam _ _ t, acc, h => by
    simp only [Term.relevantRefs]
    split
    · exact h
    · exact relevantRefs_mono q t acc h
  | .letE _ r _ v b, acc, h => by
    simp only [Term.relevantRefs]
    apply relevantRefs_mono q b
    split
    · exact h
    · exact relevantRefs_mono q v acc h
  | .proj _ _ e, acc, h => by simp only [Term.relevantRefs]; exact relevantRefs_mono q e acc h
  | .var _, _, h | .sort _, _, h | .pi .., _, h | .natLit _, _, h | .strLit _, _, h => by
    simp only [Term.relevantRefs]; exact h

/-- A spine's head constant is among its relevant references. -/
theorem head_mem_relevantRefs (q : Profile) {c : CId} {us : List Ixon.Univ} :
    ∀ (t : Term) (acc : List Inst), t.spineL.1 = .const c us → (c, q.inst us) ∈ t.relevantRefs q acc
  | .const c' us', acc, h => by
    simp only [Term.spineL, Term.spine, Term.spine.go, Term.const.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [Term.relevantRefs]
  | .app f a m r, acc, h => by
    rw [spineL_app] at h
    simp only [Term.relevantRefs]
    have h1 := head_mem_relevantRefs q f acc h
    split
    · exact h1
    · exact relevantRefs_mono q a _ h1
  | .var _, _, h | .sort _, _, h | .lam .., _, h | .pi .., _, h | .letE .., _, h | .proj .., _, h
  | .natLit _, _, h | .strLit _, _, h => by simp [Term.spineL, Term.spine, Term.spine.go] at h

/-- The head λ of a spine with tier C's facts has them. -/
theorem spineC_head_lam {q : Profile} {b : Binder} {d body : Term} :
    ∀ {bs : List Rel} {f : Term}, SpineC p ann q bs f → f.spineL.1 = .lam b d body →
      TermC p ann q bs (.lam b d body)
  | _, .app f a m r, h, hh => by
    rw [spineL_app] at hh
    cases h with
    | app hsf _ => exact spineC_head_lam hsf hh
    | head hne _ _ => exact absurd rfl (hne f a m r)
  | _, .lam b' d' body', h, hh => by
    simp only [Term.spineL, Term.spine, Term.spine.go, Term.lam.injEq] at hh
    obtain ⟨rfl, rfl, rfl⟩ := hh
    cases h with
    | head _ _ ht => exact ht
  | _, .var _, _, hh | _, .sort _, _, hh | _, .const .., _, hh | _, .pi .., _, hh
  | _, .letE .., _, hh | _, .proj .., _, hh | _, .natLit _, _, hh | _, .strLit _, _, hh => by
    simp [Term.spineL, Term.spine, Term.spine.go] at hh

/-- C0 along a λ-telescope: a binder written erased is irrelevant at the profile. -/
theorem termC_lamBinder_erased {q : Profile} :
    ∀ {bs : List Rel} {t : Term} {i : Nat} {bd : Binder}, TermC p ann q bs t →
      (lamBinders t)[i]? = some bd → writtenErased bd = true → bd.rel.irrP q = true
  | _, .lam b d t, 0, bd, h, hi, hw => by
    simp only [lamBinders, List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    cases h with
    | lam h0 _ => exact h0 hw
  | _, .lam b d t, i + 1, bd, h, hi, hw => by
    simp only [lamBinders, List.getElem?_cons_succ] at hi
    cases h with
    | lam _ ht => exact termC_lamBinder_erased ht hi hw
  | _, .var _, _, _, _, hi, _ | _, .sort _, _, _, _, hi, _ | _, .const .., _, _, _, hi, _
  | _, .app .., _, _, _, hi, _ | _, .pi .., _, _, _, hi, _ | _, .letE .., _, _, _, hi, _
  | _, .proj .., _, _, _, hi, _ | _, .natLit _, _, _, _, hi, _ | _, .strLit _, _, _, _, hi, _ => by
    simp [lamBinders] at hi

/-- A run body agreeing with its constant's header, evaluated and applied to as many arguments as
the index of a parameter written erased, gives a closure that ignores the next one. -/
theorem body_prefix {k k' : Nat} {ls ls' : Levels} {ρ : Env} {ty body : Term} {params : List Rel}
    {n : Nat} {rr : Rel} {v0 fv : Value} {args : List Term.Arg}
    (hb : HeaderOk ty body params) (hn : n ∈ erasedParams ty) (hrr : params[n]? = some rr)
    (hirr : rr.alwaysIrr = true) (hlen : args.length = n) (hv0 : eval p k' ls' [] body = .ok v0)
    (he : applySpine p k ls ρ v0 args = .ok fv) : IgnoresNext ann fv := by
  have hlt := hb.1 n hn
  obtain ⟨b0, hb0⟩ : ∃ b0, (lamRels body)[n]? = some b0 :=
    ⟨_, List.getElem?_eq_getElem hlt⟩
  have heq := hb.2 n b0 rr hb0 hrr
  subst heq
  cases body with
  | lam b d t =>
    rw [eval_lam] at hv0
    cases hv0
    subst hlen
    exact (applySpine_lamChain args b d t [] ls' b0 fv hb0 (alwaysIrr_irrAt hirr ls') he).1
  | _ => simp [lamRels] at hlt

/-- A shielded spine's prefix up to the shielded argument returns a value that ignores it, and no
partial application (the syntactic closure chain of `IgnoresSlot`, which is `False` on a pap slot:
the value is a closure of the λ-telescope, or one applying is stuck on; no `Live` needed). -/
theorem eval_shielded_prefix {k : Nat} {ls : Levels} {ρ : Env} {t : Term} {h n : Nat} {s : Slot}
    {fv : Value} (hsp : t.spineL.1 = .var h) (hlen : t.spineL.2.length = n) (hs : ρ[h]? = some s)
    (hig : IgnoresSlot s n) (he : eval p k ls ρ t = .ok fv) :
    IgnoresNext ann fv ∧ ∀ h' ls' args, fv ≠ .pap h' ls' args := by
  have hmk := mkApps_spineL t
  rw [hsp] at hmk
  rw [← hmk, eval_mkApps, eval_var_of p k ls ρ hs] at he
  obtain ⟨v0, hv0, he⟩ := bind_ok_inv he
  subst hlen
  exact applySpine_ignoresSlot hig hv0 he

/-- E7 at a position written erased (the events `SortCoherent` (a) exempts): the function value
ignores the argument. At a constant head through δ (a run body's λs cover the position with its
parameter's class, `Canonical.bodies`; a special head's partial application has it irrelevant,
`param_erased_irr`; a constructor value is stuck on application; no `csimp`, primitive, word or
recursor head, and no position at or past a special head's arity, is written erased,
`Canonical.csimp`, `Canonical.reads`); at a λ head through β (C0 on its binders). -/
theorem eval_erased_prefix (hf : Facts p ann ch) {k : Nat} {ls : Levels} {ρ : Env} {f a : Term}
    {m : Mode} {r : Rel} {fv : Value} (hfr : Frame p ann ch ls ρ (.app f a m r))
    (hwe : WrittenErasedArg p (.app f a m r)) (he : eval p k ls ρ f = .ok fv) :
    IgnoresNext ann fv := by
  obtain ⟨q, bs, hag, -, hrefs, -, hterm⟩ := hfr
  have hsp := spineL_app f a m r
  have hmk := mkApps_spineL f
  rw [← hmk, eval_mkApps] at he
  obtain ⟨v0, hv0, he⟩ := bind_ok_inv he
  unfold WrittenErasedArg at hwe
  rw [hsp] at hwe
  have hlen : (f.spineL.2 ++ [(a, m, r)]).length - 1 = f.spineL.2.length := by simp
  have hhead := congrArg Prod.fst hsp
  generalize hH : f.spineL.1 = H at hwe hv0 hhead
  cases H with
  | const c us =>
    obtain ⟨d, hd, hn⟩ := hwe
    rw [hlen] at hn
    -- the head constant is reached
    have hmem := head_mem_relevantRefs q (Term.app f a m r) [] hhead
    have hreach : c ∈ ch.reached := by
      rcases hrefs _ hmem with hge | hin
      · exfalso
        have hent := (hf.canon.dense c hge).1
        simp [Program.decl?, hent] at hd
      · exact hf.reached _ hin
    obtain ⟨cr, hcr⟩ := Option.isSome_iff_exists.1 (hf.canon.reachedRecord c hreach)
    obtain ⟨rr, hrr, hirr⟩ := param_erased_irr (hf.canon.consts c cr hcr) hd hn
    have hrd := hf.canon.reads c hreach
    rw [eval_const] at hv0
    generalize us.map (evalUniv ls) = ls' at hv0
    -- a special head: its partial application, the position below its arity
    have special : ∀ h, specialHead? p c = some h → headConst? h = some c →
        headValue p k ls' h = .ok v0 → IgnoresNext ann fv := by
      intro h hh hc hhv
      have hlt := erased_lt_arity hrd hh hd hn
      rw [headValue_eq] at hhv
      have hne : (p.headArity h == 0) = false := by simp; omega
      rw [hne] at hhv
      simp only [Bool.false_eq_true, ite_false, Sem.Result.ok.injEq] at hhv
      subst hhv
      rw [applySpine_pap_lt p k ls ρ h ls' [] f.spineL.2 (by simpa using hlt)] at he
      obtain ⟨ss, hss, he⟩ := bind_ok_inv he
      simp only [List.nil_append, Sem.Result.ok.injEq] at he
      subst he
      have hl := slotsOf_length p k ls ρ _ _ hss
      exact ⟨c, cr, rr, hc, hcr, by rw [hl]; exact hrr, alwaysIrr_irrAt hirr _⟩
    -- a head reading every argument writes none erased
    have reads : ∀ h, specialHead? p c = some h → readsAt p ann c h f.spineL.2.length = true → False := by
      intro h hh hr
      have := hrd h d hh hd _ hn
      rw [hr] at this
      cases this
    rw [evalConst_eq] at hv0
    cases hres : p.table.resolveOf c with
    | some e =>
      rw [hres] at hv0
      cases e with
      | prim op => exact (reads (.prim op) (by simp [specialHead?, hres]) (by simp [readsAt, headReadsWith])).elim
      | word w op thm => exact (reads (.word w op) (by simp [specialHead?, hres]) (by simp [readsAt, headReadsWith])).elim
      | csimp g vs thm =>
        have := hf.canon.csimp c hreach cr d g vs thm hcr hd hres
        rw [this] at hn
        cases hn
      | eqn thm body =>
        cases k with
        | zero => cases hv0
        | succ k' =>
          simp only [Sem.later_succ] at hv0
          have hb := hf.canon.bodies c hreach cr d hcr hd (.eqn c) body (by simp [runBodies, hres])
          exact body_prefix hb hn hrr hirr rfl hv0 he
      | case r' => exact special (.cases c) (by simp [specialHead?, hres]) rfl hv0
    | none =>
      cases d with
      | ctor sf lv ind cidx np nf ty =>
        simp only [hres, hd] at hv0
        exact special (.ctor c) (by simp [specialHead?, hres, hd]) rfl hv0
      | recr sf kk lv np nmot nmin ni ind rules ty =>
        simp only [hres, hd] at hv0
        exact special (.recr c) (by simp [specialHead?, hres, hd]) rfl hv0
      | quot kind lv ty =>
        cases kind with
        | ctor => simp only [hres, hd] at hv0; exact special (.quotMk c) (by simp [specialHead?, hres, hd]) rfl hv0
        | lift => simp only [hres, hd] at hv0; exact special (.quotLift c) (by simp [specialHead?, hres, hd]) rfl hv0
        | type => simp only [hres, hd] at hv0; cases hv0
        | ind => simp only [hres, hd] at hv0; cases hv0
      | defn kind safety lv ty v =>
        cases kind <;> cases safety <;> simp only [hres, hd] at hv0 <;> try (cases hv0; done)
        all_goals first
          | (cases k with
              | zero => cases hv0
              | succ k' =>
                simp only [Sem.later_succ] at hv0
                have hb := hf.canon.bodies c hreach cr _ hcr hd (.value c) v (by simp [runBodies, hres, hd])
                exact body_prefix hb hn hrr hirr rfl hv0 he)
          | (split at hv0
             · rename_i hop
               cases k with
               | zero => cases hv0
               | succ k' =>
                 simp only [Sem.later_succ] at hv0
                 have hb := hf.canon.bodies c hreach cr _ hcr hd (.value c) v
                   (by simp [runBodies, hres, hd, hop])
                 exact body_prefix hb hn hrr hirr rfl hv0 he
             · cases hv0)
      | induct => simp only [hres, hd] at hv0; cases hv0
      | axio => simp only [hres, hd] at hv0; cases hv0
  | lam b d0 body =>
    obtain ⟨bd, hbd, hwr⟩ := hwe
    rw [hlen] at hbd
    rw [eval_lam] at hv0
    cases hv0
    have htc : TermC p ann q bs (.lam b d0 body) := by
      rcases hterm with ht | ⟨more, -, hsc, -⟩ | ⟨c, us, hc, -⟩
      · cases ht with
        | app _ hsf _ => exact spineC_head_lam hsf hH
      · cases hsc with
        | app hsf _ => exact spineC_head_lam hsf hH
        | head hne _ _ => exact absurd rfl (hne f a m r)
      · cases hc
    have hirrP := termC_lamBinder_erased htc hbd hwr
    have hirr : bd.rel.irrAt ls = true := by
      unfold Rel.irrAt
      unfold Rel.irrP at hirrP
      rw [← hag.holds]
      exact hirrP
    refine (applySpine_lamChain f.spineL.2 b d0 body ρ ls bd.rel fv ?_ hirr he).1
    rw [lamRels_eq, List.getElem?_map, hbd]
    rfl
  | var _ => exact hwe.elim
  | sort _ => exact hwe.elim
  | app => exact hwe.elim
  | pi => exact hwe.elim
  | letE => exact hwe.elim
  | proj => exact hwe.elim
  | natLit _ => exact hwe.elim
  | strLit _ => exact hwe.elim

/-- **The root.** `Src.run` on literal inputs returns a `Live` value. -/
theorem run_live (hf : Facts p ann ch) (hs : ShapeOk p) {k : Nat} {root : CId} {ns : List Nat}
    {v : Value} (hroot : ∃ a, (a, root) ∈ p.roots) (hsa : RunSortAgree p ann k root (ns.map .lit))
    (h : Src.run p k root (ns.map .lit) = .ok v) : Live p ann ch v := sorry

end

end IxCC.Src.Relevance.Proof.P1

/-! ## Consumption: the escape of `Recheck.sound` narrowed -/

namespace IxCC.Recheck

open IxCC.Sem (Obs Lang)
open IxCC.Lam.Erase.Proof (CheckedProgram)
open IxCC.Src.Relevance.Proof.P1

/-- `Front.GoesWrong` with its value disjunct restricted to a `Live` result: the view rejects a
value with no marker at a read position. -/
def Front.GoesWrongLive (f : Front) (ann : Src.Relevance.Ann) (i : Nat × List Nat) : Prop :=
  ∃ k, (Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) i k).GoesWrong ∨
    ∃ v, Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) i k = .ok v ∧
      Live f.src ann f.checked v.2 ∧ f.view i.1 (Lang.obs v) = none

/-- `SortAgree` for the run of input `i`, at every clock. -/
def Front.RunSortAgree (f : Front) (ann : Src.Relevance.Ann) (i : Nat × List Nat) : Prop :=
  ∀ k root, (f.src.roots[i.1]?).map (·.2) = some root →
    Src.Relevance.Proof.P1.RunSortAgree f.src ann k root (i.2.map .lit)

/-- The front end's acceptance: both checks on the installed program, whose Lazify image is the
program SrcEval runs. -/
theorem front_accepted {cfg : Config} {P : Src.Program} {c : Cert} {src : Src.Program}
    {ch : Src.Relevance.Checked} (h : front cfg P c = .ok (src, ch)) :
    ∃ installed, Src.Relevance.check installed c.relevance = .ok ch ∧
      Src.Relevance.checkCanonical installed c.relevance ch = [] ∧
      src = Src.Lazify.run installed ch.keys := by
  unfold front at h
  simp only [bind, Except.bind, Except.mapError] at h
  cases hm : checkMidCert c.mid with
  | error e => simp [hm] at h
  | ok u =>
    simp only [hm] at h
    cases htab : Src.Table.ofCert cfg.table P c.table with
    | error e => simp [htab] at h
    | ok table =>
      simp only [htab] at h
      have hkeys : checkRelevanceKeys P c.relevance = .ok () := by
        cases hk : checkRelevanceKeys P c.relevance with
        | error e => simp [hk] at h
        | ok u => cases u; rfl
      simp only [hkeys] at h
      cases hann : Src.Recheck.annotation { P with table } c.relevance with
      | error err =>
        rw [hann] at h
        cases err <;> cases h
      | ok res =>
        rw [hann] at h
        cases h
        unfold Src.Recheck.annotation at hann
        cases hinst : Src.Relevance.install { P with table } c.relevance with
        | error e => simp [hinst] at hann
        | ok installed =>
          simp only [hinst] at hann
          cases hchk : Src.Relevance.check installed c.relevance with
          | error errs =>
            rw [hchk] at hann
            cases hann
          | ok chk =>
            rw [hchk] at hann
            dsimp only at hann
            split at hann
            · cases hann
            · rename_i hne
              cases hann
              refine ⟨installed, hchk, ?_, rfl⟩
              simpa using hne

variable {cfg : Config} {P : Src.Program} {c : Cert} {a : Artifact}

/-- `ShapeOk` under `Recheck.run`'s acceptance: `Recheck.run` erases the program SrcEval runs
(`runLir`, `run_parts`), and a successful erasure has `ProgWF.ctorIn` (`erase_progWF`). -/
theorem shapeOk_of_run (h : run cfg P c = .ok a) : ShapeOk a.src := by
  obtain ⟨-, ⟨st, he⟩, -⟩ := runLir_spec (run_parts h).1
  have hwf := Lam.Erase.Proof.erase_progWF he
  refine ⟨fun c c' sf sf' lv lv' ind j np np' nf nf' ty ty' hc hc' => ?_⟩
  have h1 := hwf.ctorIn (c := c) (sf := sf) (lv := lv) (ind := ind) (cidx := j) (np := np) (nf := nf)
    (ty := ty) hc
  have h2 := hwf.ctorIn (c := c') (sf := sf') (lv := lv') (ind := ind) (cidx := j) (np := np')
    (nf := nf') (ty := ty') hc'
  exact Option.some.inj (h1.symm.trans h2)

/-- **The narrowing.** Under `Recheck.run`'s acceptance and the run's sort events,
the source goes wrong only by being stuck, trapping, or returning a `Live` value the view
rejects: never because of a marker. -/
theorem Front.goesWrong_live (h : run cfg P c = .ok a) {i : Nat × List Nat}
    (hsa : a.front.RunSortAgree c.relevance i) :
    a.front.GoesWrong i → a.front.GoesWrongLive c.relevance i := by
  rintro ⟨k, hgw | ⟨v, hv, hview⟩⟩
  · exact ⟨k, .inl hgw⟩
  · refine ⟨k, .inr ⟨v, hv, ?_, hview⟩⟩
    obtain ⟨hfr, -, -⟩ := runLir_spec (run_parts h).1
    obtain ⟨installed, hchk, hcan, hsrc⟩ := front_accepted hfr
    have hf : Facts a.src c.relevance a.checked := by
      have := facts_modeEq hchk hcan (Src.Lazify.run_modeEq installed a.checked.keys)
      rw [show a.src = a.front.src from rfl, hsrc]
      exact this
    change Lam.Erase.Proof.srcRun ⟨a.src, a.checked⟩ i k = .ok v at hv
    unfold Lam.Erase.Proof.srcRun at hv
    split at hv
    · rename_i x root hr
      obtain ⟨w, hw, hwv⟩ := bind_ok_inv hv
      cases hwv
      exact run_live hf (shapeOk_of_run h) ⟨x, List.mem_of_getElem? hr⟩
        (hsa k root (by simp [Artifact.front, hr])) hw
    · cases hv

/-- **`Recheck.sound` with the narrowed escape.** -/
theorem sound_live (h : run cfg P c = .ok a) (D : X86.Driver) (hD : D.Ok a.backend.encoded.text.size)
    (i : Nat × List Nat) (hi : a.front.Covered c i)
    (hsa : a.front.RunSortAgree c.relevance i) :
    (∀ k w, Lang.run (a.linked D) i k = .ok w →
      (∃ k' v, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k' = .ok v ∧
        a.front.view i.1 (Lang.obs v) = some w) ∨ a.front.GoesWrongLive c.relevance i) ∧
    (¬ a.front.GoesWrongLive c.relevance i → ∀ k, ¬ (Lang.run (a.linked D) i k).GoesWrong) ∧
    ((∀ k, Lang.run (⟨a.src, a.checked⟩ : CheckedProgram) i k = .timeout) →
      (∀ k, Lang.run (a.linked D) i k = .timeout) ∨ ∃ k failure, Lang.run (a.linked D) i k = .resource failure) :=
  by
  obtain ⟨h1, h2, h3⟩ := sound h D hD i hi
  refine ⟨fun k w hw => (h1 k w hw).imp_right (Front.goesWrong_live h hsa), fun hn => h2 ?_, h3⟩
  exact fun hg => hn (Front.goesWrong_live h hsa hg)

end IxCC.Recheck

#print axioms IxCC.Recheck.front_accepted
#print axioms IxCC.Recheck.shapeOk_of_run
#print axioms IxCC.Src.Relevance.Proof.P1.eval_shielded_prefix
#print axioms IxCC.Src.Relevance.Proof.P1.eval_erased_prefix
