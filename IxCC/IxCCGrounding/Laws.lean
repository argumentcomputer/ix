import IxCK.Kernel.Denotes
import IxCCGrounding.Syntax

/-!
# The kernel's model, and the laws the development assumes of it (`IxCCGrounding.Laws`)

**The one module of the development that imports the kernel's model** (`IxCK.Kernel.Denotes`,
the statement half: `Denotes`, `Model` and, through its imports, the set theory interface and
`SetModel.Ops`; not the kernel's proof tree). Every other module reaches the model through this
one, so when the certified IxVM work's laws land on `main` as fields of `Model`, this file is
what changes: the four definitions copied from theirs go, and `Laws` keeps its last three fields.

Declarations of the model used by the development: `Denotes` and its rules, `Denotes_functional`,
`Model.cval`, `Model.mem`, `Model.eq_equality`, `push`, `regime`, `field`, `Level.substFn`,
`Level.eval`, `PropWhen.holds`; from the set theory `∈ˢ`, `app`, `pt`, `univ`, `empty`, `eqv`,
`graph`, `mem_eqv`, `univ_zero`, `app_pt`, `not_mem_empty`; from `SetModel.Ops` `piR`, `lamR`
and their lemmas (`lamR_zero`, `app_lamR_pos`, `app_mem_piR`, `app_mem_piR_pos`, `lamR_mem`,
`piR_dom_unique`, `eq_pt_of_mem_piR_zero`, `not_pt_mem_piR_pos`, `eq_pt_of_mem_univZero`,
`piR_zero_mem_univZero`, `eq_of_mem_piR_app_eq`, `app_off_dom_piR_pos`, `lamR_congr`,
`piR_congr`).

## The laws

The public `Model` on this branch has `mem`, `false_empty` and `eq_equality`. The laws the
development needs beyond them are an explicit structure of hypotheses, `Laws`, named as on the
IxVM side where a law exists there:

| Field | Theirs (`jcb/ixvmc-std-model`, 2026-11-11) | Who is to supply it |
| --- | --- | --- |
| `defn_value` | `Model.defn_value`, a field, proved | the IxVM side, when it lands on `main` |
| `iota_rule` | `Model.iota_rule : IotaLaw cval env`, a field, proved | the same |
| `cval_params` | `Model.cval_params`, a field | the same |
| `proj_ctor` | the value form is ours, **restricted** to structures that are not propositions; on `jcb/ixvmc-int` at `d4c079de2` the field `Model.proj_law` (`ProjLaw`), from which `projCtor_of_projLaw` derives it | the IxVM side, by that field |
| `nat_accel` | over all literals, the fifteen roles; on `jcb/ixvmc-int` at `d4c079de2` the field `Model.lit_ops` (`NatLitLaw`), from which `natAccel_of_litOps` derives it where every stored role is a definition (`LitDefs`) | the IxVM side, by that field and the checked premise |
| `ctor_canon` | none, and not scheduled by anyone; **restricted** to families that are not propositions | to be decided: the IxVM side, or IxCC from their recursor membership law |

`DenotesList`, `Fits`, `IotaRule` and `IotaLaw` are copied verbatim from theirs
(`IxC/Kernel/Denotes.lean` at `659ca9130`; the ι law's right-hand side denotes in its
conclusion). `DenotesList`, `Fits` and `Denotes` itself are still textually #678's
(`jcb/ixvmc-int` at `d4c079de2`, compared modulo the `IxC`/`IxCK` rename).

**Beside the laws, not a field**: `IotaLawG`, ι in #678's guarded form (two guards, `SpineOk` in
the conclusion, its graded conjunct dropped), copied from `jcb/ixvmc-int` at `d4c079de2`. It
implies `IotaLaw` (`IotaLawG.toIotaLaw`), so `Laws.iota_rule` is dischargeable from #678's field;
the theorems that read the guards or `SpineOk` (the `case` lemma without canonicity,
`IxCCGrounding.CaseBlind`) take it, with `DefnValue` and `CvalParams`, as separate hypotheses.

**#678's fields themselves, copied** (`Laws678`): verbatim copies of the five fields of #678's
public `Model` the canonicity-free family uses (`defn_value`, `iota_rule` with its graded conjunct,
`proj_law`, `lit_ops`, `cval_params`) and of the definitions behind them (`GradedBy`, `IotaRule678`,
`IotaLaw678`, `ProjLaw`, `natArithOps`, `natCmpOps`, `NatLitLaw`), from `jcb/ixvmc-int` at
`d4c079de2eca6ac8ba38a0aa9f131484e4191f87`, `IxC/Kernel/Denotes.lean`, each with its line range.
`IxCCGrounding.Adapt678` derives `LawsNoCanon` from them (`lawsNoCanon_of_678`, `NatAccel` under the
decided premise `LitDefs`), and the canonicity-free root theorems are restated over `Laws678`
(`rootSound_678` and its corollaries). **At the ingest the copies must be compared again with
#678's text** and then deleted in favour of theirs, `Laws678 M` being inhabited by any model `M` of
#678's `Model` from its own fields. If a field's text has moved, what must be re-proved is exactly
the adapter that reads it: `IotaRule678.toG` (ι), `projCtor_of_projLaw` (`proj_law`),
`natAccel_of_litOps` and the premise `LitDefs` with its checker (`lit_ops`), `Laws678.defnValue` and
`Laws678.cvalParams` (δ, level-parameter irrelevance); the root theorems reach the copies only
through `lawsNoCanon_of_678`. A moved definition that the copies read (`Denotes`, `Fits`,
`DenotesList`, `SpineOk`, `ProjEntry`, `Expr.stripPis`, the role keys) is compared the same way.

## What was wrong, and what is assumed now

As first landed, `ctor_canon` was stated for every constructor and `proj_ctor` for every
structure. Both are false in a proof-irrelevant set model, where a proposition's constructor
image is the proof point `pt`:

* `ctor_canon`: `Exists.intro (fun _ => True) 1 pt` is `pt`, fits at its own parameters and lies
  in the inhabited `Exists (fun w => w = 0)`, so the law concluded that `pt` proves `1 = 0`. In
  the kernel's own set model (`IxCK/Kernel/SetTheory/Derive/Quot.lean`: `quotClass 0 _ _ _ = pt`,
  `quotSet 1 A R` the classes) `Quot.mk` built at level `0` is `pt`, which is the class of
  `ptTag` in `quotSet 1 {ptTag} R`, so the law concluded `pt ∈ {ptTag}`, which is false.
* `proj_ctor`: at a `Prop` structure with a data field (`Nonempty`, whose projection table the
  kernel installs) the image is `pt`, every component of `pt` is `pt` (`sfst_pt`, `ssnd_pt`),
  so the law concluded that every value of the field's type is `pt`.

Both grounding subjects' environments hold `Quot.mk`, so in the kernel's set model `Laws` had no
instance for them, and `fibRoot` and `decideRoot` as first landed said nothing there. The laws
are now assumed only at families that are not propositions (`finalSort`, the stored sort, with a
nonzero value at the assignments involved); the check supplies that at each use from a decided
fact (`NeverProp`: the family's stored sort is never zero).

**Not yet shown**: that `Laws`, in this restricted form, has a model for any environment. Three
fields are proved on the side that owes them (`defn_value`, `iota_rule`, `cval_params`), two are
derived from fields #678's `Model` states (`proj_ctor` from `proj_law`; `nat_accel` from `lit_ops`
under the checked premise `LitDefs`), and the restricted `ctor_canon` is not scheduled by anyone.
Until that side's theorem lands, every theorem of this library is conditional on a hypothesis
whose consistency rests on the arguments written beside each law below.
-/

namespace IxCC.Grounding

open Ix.Kernel
open Ix.Kernel.SetTheory
open Ix.Kernel.SetModel

universe w

section Laws

variable {V : Type w} [Ix.Kernel.SetTheory V] {md : Mode}

/-- (theirs, verbatim) -/
inductive DenotesList (cval : Key md → (LevelParam → Nat) → V) (env : Env md)
    (φ : LevelParam → Nat) (ρ : BVarIdx → V) : List (Expr md) → List V → Prop
  | nil : DenotesList cval env φ ρ [] []
  | cons {e : Expr md} {es : List (Expr md)} {v : V} {vs : List V} :
      Denotes cval env φ ρ e v → DenotesList cval env φ ρ es vs →
      DenotesList cval env φ ρ (e :: es) (v :: vs)

/-- (theirs, verbatim) -/
inductive Fits (cval : Key md → (LevelParam → Nat) → V) (env : Env md) (φ : LevelParam → Nat) :
    (BVarIdx → V) → Expr md → List V → (BVarIdx → V) → Expr md → Prop
  | nil {ρ : BVarIdx → V} {T : Expr md} : Fits cval env φ ρ T [] ρ T
  | cons {ρ ρ' : BVarIdx → V} {A B R : Expr md} {m : BinderMeta} {X x : V} {xs : List V} :
      Denotes cval env φ ρ A X → x ∈ˢ X → Fits cval env φ (push x ρ) B xs ρ' R →
      Fits cval env φ ρ (.forallE A B m) (x :: xs) ρ' R

/-- **ι at one stored rule** (theirs, verbatim, `6a64f2b84`). -/
def IotaRule (cval : Key md → (LevelParam → Nat) → V) (env : Env md) (r : Key md)
    (cv : ConstantVal md) (mI rP : Nat) (rl : RecRule md) : Prop :=
  ∀ (cvC : ConstantVal md) (nP nF : Nat),
    env.find? rl.ctor = some (.ctorInfo cvC nP nF) →
    ∀ (us : List Level) (φ : LevelParam → Nat) (ρ σ σC : BVarIdx → V) (xs ys : List V)
      (dom body RC : Expr md) (m : BinderMeta) (D : Key md) (ls : List Level) (R K X : V),
      us.length = cv.levelParams.length → xs.length = mI → ys.length = nP + nF →
      Denotes cval env φ ρ (.const r us) R →
      Fits cval env φ ρ (cv.type.instantiateLevelParams cv.levelParams us) xs σ
        (.forallE dom body m) →
      dom.getAppFn = .const D ls → Denotes cval env φ σ dom X →
      Denotes cval env φ ρ (.const rl.ctor ls) K →
      Fits cval env φ ρ (cvC.type.instantiateLevelParams cvC.levelParams ls) ys σC RC →
      ys.foldl app K ∈ˢ X →
      DenotesList cval env φ σ (dom.getAppArgs.take nP) (ys.take nP) →
      DenotesList cval env φ σC (RC.getAppArgs.drop nP) (xs.drop rP) →
      ∃ H, Denotes cval env φ ρ (rl.rhs.instantiateLevelParams cv.levelParams us) H ∧
        (xs ++ [ys.foldl app K]).foldl app R = (xs.take rP ++ ys.drop nP).foldl app H

/-- **ι at every stored rule** (theirs, verbatim; the field `Model.iota_rule`). -/
def IotaLaw (cval : Key md → (LevelParam → Nat) → V) (env : Env md) : Prop :=
  ∀ (r : Key md) (cv : ConstantVal md) (mI rP : Nat) (rules : List (RecRule md))
    (rl : RecRule md),
    env.find? r = some (.recInfo cv mI rP rules) → rl ∈ rules → IotaRule cval env r cv mI rP rl

/-! ### ι in #678's guarded form, beside the landed one

#678's kernel states ι with two guards and a graded conclusion (`IotaRule`,
`IxC/Kernel/Denotes.lean:330-352` on `jcb/ixvmc-int` at `d4c079de2`): the parameter premise only
at a rule that compares parameters (`RecRule.compareParams`), the index premise only at a
recursor with indices (`mI ≠ rP`), and the conclusion also says that the right-hand side's
reading is graded (`GradedBy`) and that its value applies along the prefix and the fields on its
domains (`SpineOk`). `IotaRuleG` is that law less its graded conjunct, its text otherwise copied
(and `SpineOk` verbatim, `:283-287` there). It is **not** a field of `Laws`, which keeps the
landed `IotaLaw`: `IotaRuleG.of_premises` derives the landed form from it, so `Laws.iota_rule`
is dischargeable from #678's field as well. Theorems that read the guards or `SpineOk` take
`IotaLawG` explicitly. **At the ingest these definitions must be compared again with #678's**
(and deleted in favour of theirs, `GradedBy` dropped by a one-line lemma). -/

/-- **A head applied along values applies functions on their domains** (theirs, #678, verbatim):
at each step the function so far is a member of some product, and the next value a member of
its domain. -/
def SpineOk : V → List V → Prop
  | _, [] => True
  | F, x :: xs =>
    (∃ (r : Nat) (A : V) (B : V → V), F ∈ˢ piR r A B ∧ x ∈ˢ A) ∧ SpineOk (app F x) xs

/-- **ι at one stored rule, guarded** (#678's `IotaRule` less its graded conjunct): the parameter
premise is asked only at a rule that compares parameters, the index premise only at a recursor
with indices; the conclusion keeps `SpineOk`, which at a rule that does not compare parameters is
what puts the constructor's fields in the right-hand side's field domains at the recursor's
parameters (`caseIotaG`). -/
def IotaRuleG (cval : Key md → (LevelParam → Nat) → V) (env : Env md) (r : Key md)
    (cv : ConstantVal md) (mI rP : Nat) (rl : RecRule md) : Prop :=
  ∀ (cvC : ConstantVal md) (nP nF : Nat),
    env.find? rl.ctor = some (.ctorInfo cvC nP nF) →
    ∀ (us : List Level) (φ : LevelParam → Nat) (ρ σ σC : BVarIdx → V) (xs ys : List V)
      (dom body RC : Expr md) (m : BinderMeta) (D : Key md) (ls : List Level) (R K X : V),
      us.length = cv.levelParams.length → xs.length = mI → ys.length = nP + nF →
      Denotes cval env φ ρ (.const r us) R →
      Fits cval env φ ρ (cv.type.instantiateLevelParams cv.levelParams us) xs σ
        (.forallE dom body m) →
      dom.getAppFn = .const D ls → Denotes cval env φ σ dom X →
      Denotes cval env φ ρ (.const rl.ctor ls) K →
      Fits cval env φ ρ (cvC.type.instantiateLevelParams cvC.levelParams ls) ys σC RC →
      ys.foldl app K ∈ˢ X →
      (rl.compareParams = true →
        DenotesList cval env φ σ (dom.getAppArgs.take nP) (ys.take nP)) →
      (mI ≠ rP → DenotesList cval env φ σC (RC.getAppArgs.drop nP) (xs.drop rP)) →
      ∃ H, Denotes cval env φ ρ (rl.rhs.instantiateLevelParams cv.levelParams us) H ∧
        SpineOk H (xs.take rP ++ ys.drop nP) ∧
        (xs ++ [ys.foldl app K]).foldl app R = (xs.take rP ++ ys.drop nP).foldl app H

/-- **ι at every stored rule, guarded** (#678's `Model.iota_rule`, less its graded conjunct). -/
def IotaLawG (cval : Key md → (LevelParam → Nat) → V) (env : Env md) : Prop :=
  ∀ (r : Key md) (cv : ConstantVal md) (mI rP : Nat) (rules : List (RecRule md))
    (rl : RecRule md),
    env.find? r = some (.recInfo cv mI rP rules) → rl ∈ rules → IotaRuleG cval env r cv mI rP rl

/-- **The guarded law gives the landed one** (ours, as #678's `IotaRule.of_premises`): with both
premises in hand, the guards are discharged and `SpineOk` is dropped. -/
theorem IotaRuleG.of_premises {cval : Key md → (LevelParam → Nat) → V} {env : Env md}
    {r : Key md} {cv : ConstantVal md} {mI rP : Nat} {rl : RecRule md}
    (h : IotaRuleG cval env r cv mI rP rl) : IotaRule cval env r cv mI rP rl := by
  intro cvC nP nF hC us φ ρ σ σC xs ys dom body RC m D ls R K X h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    h12
  obtain ⟨H, hH, -, heq⟩ := h cvC nP nF hC us φ ρ σ σC xs ys dom body RC m D ls R K X h1 h2 h3 h4
    h5 h6 h7 h8 h9 h10 (fun _ => h11) (fun _ => h12)
  exact ⟨H, hH, heq⟩

/-- `IotaLawG` gives `IotaLaw` (so it discharges `Laws.iota_rule`). -/
theorem IotaLawG.toIotaLaw {cval : Key md → (LevelParam → Nat) → V} {env : Env md}
    (h : IotaLawG cval env) : IotaLaw cval env :=
  fun r cv mI rP rules rl hf hm => (h r cv mI rP rules rl hf hm).of_premises

/-- **δ** (theirs: the field `Model.defn_value`, stated as here).

*In a proof-irrelevant set model*: a definition's set is its value's (the model interprets each
stored definition by its value); at a proof the value and the constant are both `pt`. -/
def DefnValue {env : Env md} (M : Model V env) : Prop :=
  ∀ (cv : ConstantVal md) (value : Expr md) (hint : ReducibilityHint),
    ConstantInfo.defnInfo cv value hint ∈ env.consts →
    ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V), Denotes M.cval env φ ρ value (M.cval cv.name φ)

/-- **Level-parameter irrelevance** (theirs: the field `Model.cval_params`, stated as here).

*In a proof-irrelevant set model*: a constant's set is computed from the values of its own level
parameters only. -/
def CvalParams {env : Env md} (M : Model V env) : Prop :=
  ∀ (n : Key md) (ci : ConstantInfo md), env.find? n = some ci →
    ∀ φ₁ φ₂ : LevelParam → Nat, (∀ p ∈ ci.toConstantVal.levelParams, φ₁ p = φ₂ p) →
      M.cval n φ₁ = M.cval n φ₂

/-- **The `Nat` operations on literals** (ours for now; the IxVM side has scheduled a public law
over all literals, with no `pow` cap, covering the fifteen roles): a stored operation applied to
literals denotes the literal of its value, by SrcEval's own table `PrimOp.eval2`. `Bool`
results are the role constructors.

*In a proof-irrelevant set model*: `Nat` and `Bool` are not propositions, the stored operations
are the role-pinned definitions, which compute these values on numerals, and `eval2` agrees with
Lean's `Nat` operations (division and remainder by zero, the shifts). -/
def NatAccel {env : Env md} (M : Model V env) : Prop :=
  ∀ (op : IxCC.Src.PrimOp) (a b : Nat) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (X : V),
    (op.arity = 1 → b = 0) →
    Denotes M.cval env φ ρ (primApp op a b) X →
    Denotes M.cval env φ ρ (primResultE (op.eval2 a b)) X

/-- **The projection of a constructor, value form, at a structure that is not a proposition**
(ours for now; the IxVM side has scheduled the projection of a constructor as a public law, and
has this form from us): at a structure `T` stored as an inductive whose sort `s` is not zero at
the constructor's assignment `φ`, and whose projection table has an entry for field `i`, the
entry's constructor applied to sets that fit its type holds the `i`-th field at the entry's
position.

*In a proof-irrelevant set model*: where the structure's sort is not zero its constructor is read
in the graph regime and its image is the tuple of its arguments after `off` tag positions, so
component `i + off` is field `i`. At a proposition the image is `pt`, every component of `pt` is
`pt` (`sfst_pt`, `ssnd_pt`), and a data field (`Nonempty`'s) cannot be read back: the law as first
landed, without the sort premise, was false there. -/
def ProjCtor {env : Env md} (M : Model V env) : Prop :=
  ∀ (T : Key md) (i : Nat) (entry : ProjEntry md) (cvC : ConstantVal md) (nP nF : Nat)
    (cvT : ConstantVal md) (caps : IndCaps md) (s : Level)
    (φ : LevelParam → Nat) (ρ σ : BVarIdx → V) (R : Expr md) (Ps Fs : List V) (Y : V),
    env.findProj? T i = some entry → env.find? entry.ctor = some (.ctorInfo cvC nP nF) →
    env.find? T = some (.indInfo cvT caps) → finalSort cvT.type = some s → Level.eval φ s ≠ 0 →
    Ps.length = nP → Fs.length = nF →
    Fits M.cval env φ ρ cvC.type (Ps ++ Fs) σ R → Fs[i]? = some Y →
    field (i + entry.off) ((Ps ++ Fs).foldl app (M.cval entry.ctor φ)) = Y

/-- **Constructor canonicity across parameters and levels, at families that are not
propositions** (ours; not scheduled by anyone). A constructor image built at levels `ls'` and
parameters `Ps'` that lies in the family `D` at levels `ls` and parameters `Ps` is the image at
`ls` and `Ps`, and its fields fit there, when `D` is stored as an inductive whose sort `s` is not
zero at either level instantiation. It is what F5 needs at a parameterised family (`Decidable`),
where the major's parameters come from a different term than the `case`'s.

*In a proof-irrelevant set model*: where the family's sort is not zero its constructors are read
in the graph regime and a constructor image is the tagged tuple of its fields; such a tuple lies
in the family at other parameters only if each field lies in its type there, and at parameters
off the family's domain its graph gives the empty set. At a proposition every image is `pt`,
which lies in every inhabited instance: as first landed, without the sort premises, the law was
false there (`Exists.intro`; `Quot.mk` built at level `0` and read at level `1` in the kernel's set
model). -/
def CtorCanon {env : Env md} (M : Model V env) : Prop :=
  ∀ (c : Key md) (cvC : ConstantVal md) (nP nF : Nat),
    env.find? c = some (.ctorInfo cvC nP nF) →
    ∀ (D : Key md) (cvD : ConstantVal md) (caps : IndCaps md) (s : Level)
      (ls ls' : List Level) (φ : LevelParam → Nat) (ρ τ σ' : BVarIdx → V)
      (dom R' : Expr md) (Ps Ps' Fs : List V) (K K' X : V),
      env.find? D = some (.indInfo cvD caps) → finalSort cvD.type = some s →
      Level.eval (Level.substFn φ cvD.levelParams ls) s ≠ 0 →
      Level.eval (Level.substFn φ cvD.levelParams ls') s ≠ 0 →
      Ps.length = nP → Ps'.length = nP → Fs.length = nF →
      Denotes M.cval env φ ρ (.const c ls) K → Denotes M.cval env φ ρ (.const c ls') K' →
      Fits M.cval env φ ρ (cvC.type.instantiateLevelParams cvC.levelParams ls') (Ps' ++ Fs) σ' R' →
      R'.getAppFn = .const D ls' →
      dom.getAppFn = .const D ls → Denotes M.cval env φ τ dom X →
      DenotesList M.cval env φ τ (dom.getAppArgs.take nP) Ps →
      (Ps' ++ Fs).foldl app K' ∈ˢ X →
      (Ps' ++ Fs).foldl app K' = (Ps ++ Fs).foldl app K ∧
        ∃ (σ : BVarIdx → V) (R : Expr md),
          Fits M.cval env φ ρ (cvC.type.instantiateLevelParams cvC.levelParams ls) (Ps ++ Fs) σ R

/-- **The laws the development assumes of a model.** Each field says who is to supply it. -/
structure Laws {env : Env md} (M : Model V env) : Prop where
  /-- δ. IxVM side: `Model.defn_value`, a field, proved (`jcb/ixvmc-std-model`). -/
  defn_value : DefnValue M
  /-- ι. IxVM side: `Model.iota_rule`, a field, proved. -/
  iota_rule : IotaLaw M.cval env
  /-- level-parameter irrelevance. IxVM side: `Model.cval_params`, a field. -/
  cval_params : CvalParams M
  /-- the projection of a constructor, value form, at structures that are not propositions.
  IxVM side: scheduled. -/
  proj_ctor : ProjCtor M
  /-- the fifteen `Nat` operations on all literals. IxVM side: scheduled. -/
  nat_accel : NatAccel M
  /-- constructor canonicity at families that are not propositions. Not scheduled by anyone. -/
  ctor_canon : CtorCanon M

/-- **The laws other than canonicity, ι in the landed form**: what every lemma of the library that
does not read `ctor_canon` takes (the direct route's soundness, the heads, δ, the `Eq.rec` and
`case` model lemmas, level instantiation, the literals). Both law structures give it
(`lawsCore_of_laws`, `LawsNoCanon.core`). -/
structure LawsCore {env : Env md} (M : Model V env) : Prop where
  defn_value : DefnValue M
  iota_rule : IotaLaw M.cval env
  cval_params : CvalParams M
  proj_ctor : ProjCtor M
  nat_accel : NatAccel M

/-- `Laws` without its canonicity. -/
theorem lawsCore_of_laws {env : Env md} {M : Model V env} (hL : Laws M) : LawsCore M :=
  ⟨hL.defn_value, hL.iota_rule, hL.cval_params, hL.proj_ctor, hL.nat_accel⟩

/-- **The laws of the canonicity-free family** (`rootSound_noCanon` and its corollaries): no
`ctor_canon`, and ι in #678's guarded form.

| Field | #678's public `Model` (`jcb/ixvmc-int` at `d4c079de2`) |
| --- | --- |
| `defn_value` | its field `defn_value`, the same statement |
| `iota_rule` | its field `iota_rule`, less the graded conjunct (`IotaLawG`) |
| `cval_params` | its field `cval_params`, the same statement |
| `proj_ctor` | from its field `proj_law` (`projCtor_of_projLaw`, `IxCCGrounding.Adapt678`) |
| `nat_accel` | from its field `lit_ops`, under the decided premise `LitDefs` (every `Nat` role key stored is stored as a definition; `natAccel_of_litOps`) |

All five are derived from verbatim copies of #678's fields (`Laws678`, below; `lawsNoCanon_of_678`). -/
structure LawsNoCanon {env : Env md} (M : Model V env) : Prop where
  defn_value : DefnValue M
  iota_rule : IotaLawG M.cval env
  cval_params : CvalParams M
  proj_ctor : ProjCtor M
  nat_accel : NatAccel M

/-- The canonicity-free laws give the core (ι in the landed form, `IotaLawG.toIotaLaw`). -/
theorem LawsNoCanon.core {env : Env md} {M : Model V env} (hL : LawsNoCanon M) : LawsCore M :=
  ⟨hL.defn_value, hL.iota_rule.toIotaLaw, hL.cval_params, hL.proj_ctor, hL.nat_accel⟩

/-! ### #678's fields, copied (`Laws678`)

Verbatim copies of the definitions behind the five fields of #678's public `Model` that the
canonicity-free family uses, from `jcb/ixvmc-int` at `d4c079de2eca6ac8ba38a0aa9f131484e4191f87`,
`IxC/Kernel/Denotes.lean`; each docstring names its line range there. Two names differ from
theirs: `IotaRule678` and `IotaLaw678` (#678's `IotaRule` and `IotaLaw`), because `IotaRule` and
`IotaLaw` here name the earlier, unguarded form that `Laws` still takes. Everything the copies read
(`ProjEntry`, `Env.findProj?`, `Expr.stripPis`, `Expr.mkAppN`, the role keys, `Denotes`, `Fits`,
`DenotesList`, `SpineOk`) was compared at the same commit and is ours byte for byte modulo the
`IxC`/`IxCK` rename. -/

/-- **A graded reading** (#678, verbatim: `d4c079de2`, `IxC/Kernel/Denotes.lean:270-279`): every
application in the term applies a function that denotes a member of a dependent product to an
argument that denotes a member of the product's domain, through every binder at every member of its
domain. -/
def GradedBy (D : (BVarIdx → V) → Expr md → V → Prop) : (BVarIdx → V) → Expr md → Prop
  | ρ, .app f a => GradedBy D ρ f ∧ GradedBy D ρ a ∧
      ∃ (r : Nat) (A F X : V) (B : V → V), D ρ f F ∧ D ρ a X ∧ F ∈ˢ piR r A B ∧ X ∈ˢ A ∧
        (r = 0 → ∀ x, x ∈ˢ A → B x ∈ˢ univ 0)
  | ρ, .lam ty b _ =>
    GradedBy D ρ ty ∧ ∀ A, D ρ ty A → ∀ x, x ∈ˢ A → GradedBy D (push x ρ) b
  | ρ, .forallE ty b _ =>
    GradedBy D ρ ty ∧ ∀ A, D ρ ty A → ∀ x, x ∈ˢ A → GradedBy D (push x ρ) b
  | ρ, .proj _ _ e => GradedBy D ρ e
  | _, _ => True

/-- **ι at one stored rule** (#678's `IotaRule`, verbatim but for the name: `d4c079de2`,
`IxC/Kernel/Denotes.lean:330-350`). Our `IotaRuleG` is this less the `GradedBy` conjunct
(`IotaRule678.toG`). -/
def IotaRule678 (cval : Key md → (LevelParam → Nat) → V) (env : Env md) (r : Key md)
    (cv : ConstantVal md) (mI rP : Nat) (rl : RecRule md) : Prop :=
  ∀ (cvC : ConstantVal md) (nP nF : Nat),
    env.find? rl.ctor = some (.ctorInfo cvC nP nF) →
    ∀ (us : List Level) (φ : LevelParam → Nat) (ρ σ σC : BVarIdx → V) (xs ys : List V)
      (dom body RC : Expr md) (m : BinderMeta) (D : Key md) (ls : List Level) (R K X : V),
      us.length = cv.levelParams.length → xs.length = mI → ys.length = nP + nF →
      Denotes cval env φ ρ (.const r us) R →
      Fits cval env φ ρ (cv.type.instantiateLevelParams cv.levelParams us) xs σ
        (.forallE dom body m) →
      dom.getAppFn = .const D ls → Denotes cval env φ σ dom X →
      Denotes cval env φ ρ (.const rl.ctor ls) K →
      Fits cval env φ ρ (cvC.type.instantiateLevelParams cvC.levelParams ls) ys σC RC →
      ys.foldl app K ∈ˢ X →
      (rl.compareParams = true →
        DenotesList cval env φ σ (dom.getAppArgs.take nP) (ys.take nP)) →
      (mI ≠ rP → DenotesList cval env φ σC (RC.getAppArgs.drop nP) (xs.drop rP)) →
      ∃ H, Denotes cval env φ ρ (rl.rhs.instantiateLevelParams cv.levelParams us) H ∧
        GradedBy (Denotes cval env φ) ρ (rl.rhs.instantiateLevelParams cv.levelParams us) ∧
        SpineOk H (xs.take rP ++ ys.drop nP) ∧
        (xs ++ [ys.foldl app K]).foldl app R = (xs.take rP ++ ys.drop nP).foldl app H

/-- **ι at every stored rule** (#678's `IotaLaw`, verbatim but for the two names: `d4c079de2`,
`IxC/Kernel/Denotes.lean:377-380`). -/
def IotaLaw678 (cval : Key md → (LevelParam → Nat) → V) (env : Env md) : Prop :=
  ∀ (r : Key md) (cv : ConstantVal md) (mI rP : Nat) (rules : List (RecRule md))
    (rl : RecRule md),
    env.find? r = some (.recInfo cv mI rP rules) → rl ∈ rules → IotaRule678 cval env r cv mI rP rl

/-- **The projection table of a stored structure, and its two laws** (#678, verbatim:
`d4c079de2`, `IxC/Kernel/Denotes.lean:422-448`): the table is `T`'s; at universe arguments and
arguments that fit the constructor's type, field `i` of the constructor application is the field,
under the table's `Prop` guard; structure η. -/
def ProjLaw (cval : Key md → (LevelParam → Nat) → V) (env : Env md) : Prop :=
  ∀ (T : Key md) (i : Nat) (entry : ProjEntry md) (cvT : ConstantVal md) (capsT : IndCaps md),
    env.findProj? T i = some entry → env.find? T = some (.indInfo cvT capsT) →
    cvT.levelParams = entry.levelParams ∧
    (∃ bs, cvT.type.stripPis entry.numParams = some (bs, .sort entry.structSort)) ∧
    ∃ cvC : ConstantVal md,
      env.find? entry.ctor = some (.ctorInfo cvC entry.numParams entry.numFields) ∧
      cvC.levelParams = entry.levelParams ∧
      (∃ bs, cvC.type.stripPis (entry.numParams + entry.numFields) = some (bs,
        Expr.mkAppN (.const T (entry.levelParams.map .param))
          ((List.range entry.numParams).map fun k =>
            .bvar (entry.numFields + entry.numParams - 1 - k)))) ∧
      ∀ (us : List Level) (φ : LevelParam → Nat) (ρ : BVarIdx → V) (F K : V),
        us.length = entry.levelParams.length →
        Denotes cval env φ ρ (.const T us) F → Denotes cval env φ ρ (.const entry.ctor us) K →
        ((Level.eval (Level.substFn φ entry.levelParams us) entry.structSort = 0 →
            Level.eval (Level.substFn φ entry.levelParams us) entry.fieldSort = 0) →
          ∀ (σ : BVarIdx → V) (R : Expr md) (ys : List V),
            ys.length = entry.numParams + entry.numFields →
            Fits cval env φ ρ (cvC.type.instantiateLevelParams cvC.levelParams us) ys σ R →
            field (i + entry.off) (ys.foldl app K) = ys.getD (entry.numParams + i) empty) ∧
        ∀ (σ : BVarIdx → V) (R : Expr md) (ts : List V) (x : V),
          ts.length = entry.numParams →
          Fits cval env φ ρ (cvT.type.instantiateLevelParams cvT.levelParams us) ts σ R →
          x ∈ˢ ts.foldl app F →
          x = (ts ++ (List.range entry.numFields).map fun j => field (j + entry.off) x).foldl
            app K

/-- The binary `Nat` operations with a `Nat` value the kernel computes on literals, at their role
keys, each with Lean's function (#678, verbatim: `d4c079de2`, `IxC/Kernel/Denotes.lean:453-457`). -/
def natArithOps : List (Key md × (Nat → Nat → Nat)) :=
  [(natAddName, Nat.add), (natSubName, Nat.sub), (natMulName, Nat.mul), (natPowName, Nat.pow),
   (natDivName, Nat.div), (natModName, Nat.mod), (natGcdName, Nat.gcd),
   (natLandName, Nat.land), (natLorName, Nat.lor), (natXorName, Nat.xor),
   (natShiftLeftName, Nat.shiftLeft), (natShiftRightName, Nat.shiftRight)]

/-- The two `Nat` comparisons the kernel computes on literals (#678, verbatim: `d4c079de2`,
`IxC/Kernel/Denotes.lean:461-462`). -/
def natCmpOps : List (Key md × (Nat → Nat → Bool)) :=
  [(natBeqName, Nat.beq), (natBleName, Nat.ble)]

/-- **The `Nat` operations on literals compute as Lean's do, at every role a stored definition
binds** (#678, verbatim: `d4c079de2`, `IxC/Kernel/Denotes.lean:470-487`). -/
def NatLitLaw (cval : Key md → (LevelParam → Nat) → V) (env : Env md) : Prop :=
  (∀ (cv : ConstantVal md) (v : Expr md) (hint : ReducibilityHint),
    env.find? natPredName = some (.defnInfo cv v hint) →
    ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V) (a : Nat) (X : V),
      Denotes cval env φ ρ (.app (.const natPredName []) (.lit (.natVal a))) X →
      Denotes cval env φ ρ (.lit (.natVal (a - 1))) X) ∧
  (∀ (c : Key md) (f : Nat → Nat → Nat), (c, f) ∈ natArithOps →
    ∀ (cv : ConstantVal md) (v : Expr md) (hint : ReducibilityHint),
    env.find? c = some (.defnInfo cv v hint) →
    ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V) (a b : Nat) (X : V),
      Denotes cval env φ ρ (.app (.app (.const c []) (.lit (.natVal a))) (.lit (.natVal b))) X →
      Denotes cval env φ ρ (.lit (.natVal (f a b))) X) ∧
  ∀ (c : Key md) (f : Nat → Nat → Bool), (c, f) ∈ natCmpOps →
    ∀ (cv : ConstantVal md) (v : Expr md) (hint : ReducibilityHint),
    env.find? c = some (.defnInfo cv v hint) →
    ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V) (a b : Nat) (X : V),
      Denotes cval env φ ρ (.app (.app (.const c []) (.lit (.natVal a))) (.lit (.natVal b))) X →
      Denotes cval env φ ρ (.const (if f a b then boolTrueName else boolFalseName) []) X

/-- **The fields of #678's public `Model` the canonicity-free family uses**, verbatim and in #678's
order (`structure Model`, `d4c079de2`, `IxC/Kernel/Denotes.lean:640`; `cval` written `M.cval`):
`defn_value` `:673-676`, `iota_rule` `:682`, `proj_law` `:687`, `lit_ops` `:694`, `cval_params`
`:702-704`. At the ingest, `⟨M.defn_value, M.iota_rule, M.proj_law, M.lit_ops, M.cval_params⟩`
inhabits it for every model `M` of #678's `Model`. -/
structure Laws678 {env : Env md} (M : Model V env) : Prop where
  defn_value : ∀ (cv : ConstantVal md) (value : Expr md) (hint : ReducibilityHint),
    ConstantInfo.defnInfo cv value hint ∈ env.consts →
    ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V),
      Denotes M.cval env φ ρ value (M.cval cv.name φ)
  iota_rule : IotaLaw678 M.cval env
  proj_law : ProjLaw M.cval env
  lit_ops : NatLitLaw M.cval env
  cval_params : ∀ (n : Key md) (ci : ConstantInfo md), env.find? n = some ci →
    ∀ φ₁ φ₂ : LevelParam → Nat, (∀ p ∈ ci.toConstantVal.levelParams, φ₁ p = φ₂ p) →
      M.cval n φ₁ = M.cval n φ₂

/-- **#678's ι at one rule gives ours** (`IotaRuleG`): drop the `GradedBy` conjunct. -/
theorem IotaRule678.toG {cval : Key md → (LevelParam → Nat) → V} {env : Env md}
    {r : Key md} {cv : ConstantVal md} {mI rP : Nat} {rl : RecRule md}
    (h : IotaRule678 cval env r cv mI rP rl) : IotaRuleG cval env r cv mI rP rl := by
  intro cvC nP nF hC us φ ρ σ σC xs ys dom body RC m D ls R K X h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    h12
  obtain ⟨H, hH, -, hS, heq⟩ := h cvC nP nF hC us φ ρ σ σC xs ys dom body RC m D ls R K X h1 h2 h3
    h4 h5 h6 h7 h8 h9 h10 h11 h12
  exact ⟨H, hH, hS, heq⟩

/-- **#678's ι law gives ours** (`IotaLawG`). -/
theorem IotaLaw678.toG {cval : Key md → (LevelParam → Nat) → V} {env : Env md}
    (h : IotaLaw678 cval env) : IotaLawG cval env :=
  fun r cv mI rP rules rl hf hm => (h r cv mI rP rules rl hf hm).toG

/-- #678's `defn_value` is our `DefnValue` (the same statement). -/
theorem Laws678.defnValue {env : Env md} {M : Model V env} (hL : Laws678 M) : DefnValue M :=
  hL.defn_value

/-- #678's `cval_params` is our `CvalParams` (the same statement). -/
theorem Laws678.cvalParams {env : Env md} {M : Model V env} (hL : Laws678 M) : CvalParams M :=
  hL.cval_params

end Laws

end IxCC.Grounding
