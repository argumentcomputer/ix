import IxCC.Src.Relevance.Proof.Canonical
import IxCC.Lam.Erase.Proof.Rel
import IxCC.Src.Semantics

/-! # P1, relevance preservation: the definitions

SrcEval binds the marker `irr` where an argument is erased or irrelevant by its sort, and
`Recheck.sound`'s escape "the source goes wrong" includes a marker returned. P1 says that on a
program the relevance checks accept (`Relevance.check`, `checkCanonical`), SrcEval never yields the
marker at a position that is read. **P1 is proved** in `IxCC.Src.Relevance.Proof.P1.Main`
(`preserve`, `pre_step`, `reads_live`, `run_live`), under the hypotheses below. This module holds
its definitions, as approved for the proof (`Reads` at a recursor and at a `case` key repaired
since: the major is read only at an ordinary kind); the one theorem here is `live_not_irr`.

* Hypotheses: `Facts` (L1's propositions, `WellAnnotatedC` and `Canonical`, on the program SrcEval
  runs), `ShapeOk` (one constructor per inductive and index, the structural fact no check of the
  front end decides), and `SortAgree` (at every call a run makes, `Reach` over `Step`, a marker from
  a position irrelevant **by sort**, never one written erased, meets a receiver that ignores it:
  `SortCoherent`).
* Invariants: `Live`, `LiveSlot`, `EnvOk` (by provenance, strictly positive), `Whole`,
  `MinorsIgnore`, `IgnoresSlot`, `ShieldedIn`; each call's precondition `Pre` and result `Post`;
  what a call reads, `Reads`.
* The statements (proved in `IxCC.Src.Relevance.Proof.P1.Main`): every reachable call whose `Pre`
  holds has its `Post` (`preserve`); `Pre` propagates along every `Step` but the evaluation of a
  shielded variable (`pre_step`); what a call reads is `Live` (`reads_live`); the root on literal
  inputs returns a `Live` value (`run_live`). The narrowing of `Recheck.sound`'s escape that they give is stated over
  `Recheck.Front.GoesWrongLive` (`IxCC.Recheck.Proof.LiveDefs`).

`preserve` and `pre_step` hold for any call a run may start from, with arbitrary values in its
environment and arguments that satisfy `Pre`; so the invariants say of a value what SrcEval's own
values have and an arbitrary one need not. Three clauses exist for that reason alone: a special
head is the one δ makes for its constant (`HeadSeen`), a constructor value holds a marker at a
field written erased only with its constructor's field count, and a `Quot.mk` value with a marker
element only from a `Quot.mk` that reads its element (`MarkersPlaced`). Without each, a call whose
`Pre` holds returns the marker (a recursor with a table entry fired as `.recr r`; F2 binding a
rule's field λs short; F8 applying a function to an element written erased). -/

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

/-- A special head as SrcEval met it: the head `evalConst` makes for its constant
(`specialHead?`: a `case` entry gives `.cases c`; with no table entry, a constructor, recursor or
quotient declaration gives `.ctor c`, `.recr c`, `.quotMk c` or `.quotLift c`; a primitive or word
operation has no constant), that constant a reached instance at a profile agreeing with `ls`, and
a word operation from a reached `word` entry (where one is reached, `Canonical.finProof` has
`Fin.mk` drop the proof field F6w builds with the marker, and have the two fields F6w builds).
Without the first conjunct a recursor with a table entry could fire as `.recr r`, which no run
does, with rules no check reads (`runtimeKeys` omits them; `ReadsOk` and `RulesOk` speak of the
head δ makes); a `Quot.mk` with a table entry could fire as `.quotMk c` with its element written
erased; and any reached special-head constant could fire under another head's kind (`Quot.lift`'s
own constant fired as `.quotMk` builds a constructor value whose field is read through a
constructor record it does not have). -/
def HeadSeen (p : Program) (ch : Checked) (ls : Levels) (h : Head) : Prop :=
  (∀ c, headConst? h = some c → specialHead? p c = some h ∧ ∃ q, Agree ls q ∧ (c, q) ∈ ch.instances) ∧
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

/-- Where a constructor value `con c _ _ fs` may hold a marker, beyond the fields it does not
read: what the values SrcEval builds have (F1 builds every field from its constructor's
arguments, F7 from a `Quot.mk` that reads its element, `Program.boolValue` builds no field, F6w's
tower holds its one marker at `Fin.mk`'s proof field, whose count `Canonical.finProof` fixes) and
an arbitrary value need not. -/
structure MarkersPlaced (p : Program) (c : CId) (fs : List Value) : Prop where
  /-- A marker at a field its constructor writes erased sits only in a value with the
  constructor's field count. F2 binds the rule's field λs by the value's field count (`peelLams`
  over `pre ++ fields`) and the forwarding clause (`ForwardOk`) speaks of the rule's body under the
  declared count: with fewer fields the body is still a λ, in which the marker's variable is not
  shielded. The parameter slots F2 binds are the eliminator's own arguments, never the value's,
  whose count `selectRule` only compares; F3 takes its fields from the eliminator's index slots;
  F5 applies the minor to the fields without peeling. -/
  count : ∀ i v, fs[i]? = some v → v.isIrr = true → fieldWrittenErased p c i = true →
    ∀ sf lv ind cidx np nf ty, p.decl? c = some (.ctor sf lv ind cidx np nf ty) → fs.length = nf
  /-- A `Quot.mk` value whose element is a marker is of a `Quot.mk` that does not write its element
  (parameter 2) erased: F8's sort clause (`SortCoherent` (e)) exempts an element written erased,
  which `ReadsOk` refuses only at the `Quot.mk` δ makes. -/
  quotElem : ∀ v, fs[0]? = some v → v.isIrr = true → ∀ lv ty, p.decl? c = some (.quot .ctor lv ty) →
    2 ∉ erasedParams ty

/-! ## `Live`: no marker at a read position, by provenance -/

mutual

/-- A value with no marker at a position that is read. A closure and a suspension are `Live` by
provenance (the facts of the λ they come from, and their environment), not by behaviour, so the
definition is strictly positive. A marker is never `Live`. -/
inductive Live (p : Program) (ann : Ann) (ch : Checked) : Value → Prop
  | lit (n : Nat) : Live p ann ch (.lit n)
  | str (s : String) : Live p ann ch (.str s)
  /-- Every field is `Live` or a marker, a field that is read is `Live`, none is a partial
  eliminator, and the markers are where SrcEval's own values have them (`MarkersPlaced`). -/
  | con {c : CId} {ls : Levels} {ps : List Slot} {fs : List Value} :
      (∀ i v, fs[i]? = some v → (ReadsField p ann ch c ls i = true ∨ v.isIrr = false) →
        Live p ann ch v) →
      (∀ (i : Nat) (v : Value), fs[i]? = some v → Whole p v) →
      MarkersPlaced p c fs →
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
    v.isIrr = false := by
  cases h <;> rfl

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
reads and the field it yields, the major F2 or F5 selects a rule by, and the quotient F8 lifts.
The major is read only at an ordinary kind at the levels (`Step.recMajor`, `Step.caseMajor`): a
subsingleton or empty kind forces no major, so its clause has the steps' own premise. -/
def Reads (p : Program) (ann : Ann) (ch : Checked) : Call → Prop
  | .apply k f s => (∃ v, apply p k f s = .ok v) → Live p ann ch f
  | .eval k ls ρ (.proj s i e) => ∀ v w, eval p k ls ρ e = .ok v → p.projectField s i v = .ok w →
      Live p ann ch v ∧ Live p ann ch w
  | .fire (k + 1) (.recr r) ls args =>
      ∀ sf kk lv np nmot nmin ni ind rules ty major jf,
        p.decl? r = some (.recr sf kk lv np nmot nmin ni ind rules ty) →
        (p.table.recKindOf r).map (·.atLevels ls) = some .ordinary →
        force p k (args.getD (np + nmot + nmin + ni) default) = .ok major →
        p.selectRule ind np major = some jf → Live p ann ch major
  | .fire (k + 1) (.cases c) ls args =>
      ∀ r sf kk lv np nmot nmin ni ind rules ty major jf,
        p.table.resolveOf c = some (.case r) → p.decl? r = some (.recr sf kk lv np nmot nmin ni ind rules ty) →
        (p.table.recKindOf r).map (·.atLevels ls) = some .ordinary →
        force p k (args.getD (np + 1 + ni) default) = .ok major →
        p.selectRule ind np major = some jf → Live p ann ch major
  | .fire (k + 1) (.quotLift _) _ [_, _, _, _, _, q] =>
      ∀ c' l' ps a, force p k q = .ok (.con c' l' ps [a]) → p.isQuotCtor c' = true →
        Live p ann ch (.con c' l' ps [a])
  | _ => True

end IxCC.Src.Relevance.Proof.P1
