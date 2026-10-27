import Ix.Cert.Statement
import IxC.Kernel.Rules.Rel

/-! # Source laws: recursor rules and capability laws in a value model

A value model (`ValueModel`) fixes types and the values of definitions. It
leaves the checker's other definitional equalities free. The final statement
asks more of the Source model it produces (`LawModel`):

* **recursor rules**: every ι step the checker takes in the environment from a
  closed, well-typed redex, at a stored recursor's fired rule (`IotaStep`: the premises of the checker's ι rule,
  `Ix.Kernel.Rules.Red.iota`, the major's preparation included), relates two
  terms that denote alike (`RecRuleLaws`);
* **capability laws**: the structure η rule and the unit-like structure rule of
  an η-capable or unit-like stored family (`StructEtaStep`, `StructUnitStep`: the
  premises of `Ix.Kernel.Rules.DefEq.structEta` and `DefEq.structUnit`), and the
  structural projection of a constructor at a stored projection table
  (`ProjStep`: the premises of `Red.proj`), each relate two closed, well-typed
  terms (or a well-typed projection and its field) that denote alike
  (`CapabilityLaws`).

These are the public counterparts of the laws a strong model of an accepted
environment keeps internally (`Ix.Kernel.Cached.StrongModel.rec_rule`, and the
capability and projection-tower laws of its invariant). They are stated over
public denotations (`DenoteAlike`): wherever both sides of a step denote, they
denote the same set, at every level assignment and variable valuation.

**Every step starts from well-typed terms** (`TypedClosed`: closed, and typed at
the full grade by the rules tier). Lean's kernel relates only well-typed terms by
these laws, and without the premise no model satisfies them. The public reading
is total on application: off a graph's domain, application yields the empty set
(`SetTheory.app_off_dom_of_mem_piSet`, `SetTheory.app_empty`). The step premises
leave some arguments unchecked:
* the licensed telescope walk skips every slot whose binder can never be a
  proposition (`Rules.Certs.skip`), and so does io-grade inference
  (`Rules.Infer.appSkip`);
* such a binder's λ β-reduces with no certificate (`Rules.Red.betaGate`).

So, for a `Type`-valued structure with a projection table such as `Prod`:
* `.proj Prod 0 (Prod.mk.{0,0} (Sort 1) (Sort 0) (Sort k) (Sort 0))` is a
  projection step to `Sort k`, with every slot skipped;
* its subject denotes `field off ∅` whatever `k` is, because `Sort 1` lies outside
  the domain `Type 0`;
* the right-hand side `Sort k` denotes a different universe for each `k`.

The internal laws make the same restriction: they are stated for graded
readings, whose applications stay inside their domains.

What a `Model` already carries of the roles: `False` denotes the empty set and
`Eq` denotes equality (`Model.false_empty`, `Model.eq_equality`). A `Nat` literal
denotes what its constructor form denotes by the definition of `Denotes`; the
structural and well-founded `Nat` operations are definitions, so their values
follow from definition values and the recursor rules.

Left out, deliberately: theorem and opaque values (the checker never unfolds
them, and a value model records none), the quotient's computation rule, and the
other conversion rules (β and function η, proof irrelevance, the unit-like basis
type), which the set semantics either gives directly or which the statement does
not need. -/

namespace Ix.Cert

open Ix.Kernel Ix.Kernel.Rules

universe w

variable {md : Mode}

/-- **Two terms denote alike** under the constant values `cval`: at every level
assignment and variable valuation, any denotation of the one is any denotation of
the other. -/
def DenoteAlike {V : Type w} [SetTheory V] (cval : Key md → (LevelParam → Nat) → V) (env : Env md)
    (e e' : Ix.Kernel.Expr md) : Prop :=
  ∀ (φ : LevelParam → Nat) (ρ : BVarIdx → V) (v v' : V),
    Denotes cval env φ ρ e v → Denotes cval env φ ρ e' v' → v = v'

/-- **A closed, well-typed term**: no free variable, no loose bound variable, and a
type at the full grade in the rules tier (`Rules.Infer`, the declaration front
door's typing, which checks every argument). The laws below relate such terms
only (see the module docstring). -/
def TypedClosed (env : Env md) (e : Ix.Kernel.Expr md) : Prop :=
  e.hasFvar = false ∧ e.looseBVarsBounded 0 = true ∧ ∃ t, Infer env .full 0 e t

/-- **One ι step** of `env` at the recursor `c` (stored as `.recInfo cv mI rP rules`)
and its rule `rl`: from a closed, well-typed redex `e`, the premises of the
checker's ι rule (`Red.iota`), at depth 0, to the rule's right-hand side `e'`. -/
def IotaStep (env : Env md) (c : Ix.Kernel.Key md) (cv : Ix.Kernel.ConstantVal md) (mI rP : Nat)
    (rules : List (RecRule md)) (rl : RecRule md) (e e' : Ix.Kernel.Expr md) : Prop :=
  TypedClosed env e ∧
  ∃ (us : List Ix.Kernel.Level) (major : Ix.Kernel.Expr md) (cj : Ix.Kernel.Key md) (usj : List Ix.Kernel.Level) (cvj : Ix.Kernel.ConstantVal md)
    (cnP cnF : Nat) (residual : Ix.Kernel.Expr md),
    e.getAppFn = .const c us ∧
    e.getAppArgs.length = mI + 1 ∧
    us.length = cv.levelParams.length ∧
    Red env 0 (e.getAppArgs.getD mI (.bvar 0)) major ∧
    major.getAppFn = .const cj usj ∧
    env.find? cj = some (.ctorInfo cvj cnP cnF) ∧
    rules.find? (fun r' => r'.ctor == cj) = some rl ∧
    major.getAppArgs.length = rl.ctorParams + rl.nfields ∧
    rl.fire ≠ .inert ∧
    Level.isEquivList usj
      (recFireComparands rl cv.levelParams us cvj.levelParams e.getAppArgs rP).1 = some true ∧
    (rl.compareParams = true →
      DefEqList env 0 (major.getAppArgs.take rl.ctorParams)
        (recFireComparands rl cv.levelParams us cvj.levelParams e.getAppArgs rP).2) ∧
    Certs env 0 true (cv.type.instantiateLevelParams cv.levelParams us)
      (e.getAppArgs.take mI ++ [major]) ∧
    Certs env 0 true (cvj.type.instantiateLevelParams cvj.levelParams usj) major.getAppArgs ∧
    (mI ≠ rP →
      piResidual (cvj.type.instantiateLevelParams cvj.levelParams usj) major.getAppArgs = some residual) ∧
    (mI ≠ rP →
      DefEqList env 0 (residual.getAppArgs.drop rl.ctorParams) ((e.getAppArgs.take mI).drop rP)) ∧
    e' = Expr.mkAppN (rl.rhs.instantiateLevelParams cv.levelParams us)
      (e.getAppArgs.take rP ++ major.getAppArgs.drop rl.ctorParams)

/-- **The recursor rules hold**: every ι step of every fired rule of every stored
recursor relates terms that denote alike. Keyed as the strong model's
`rec_rule` is: a stored recursor, a rule of it, the rule fired. -/
def RecRuleLaws {V : Type w} [SetTheory V] (cval : Key md → (LevelParam → Nat) → V) (env : Env md) :
    Prop :=
  ∀ (c : Ix.Kernel.Key md) (cv : Ix.Kernel.ConstantVal md) (mI rP : Nat) (rules : List (RecRule md)),
    env.find? c = some (.recInfo cv mI rP rules) → ∀ rl ∈ rules, rl.fire ≠ .inert →
      ∀ e e', IotaStep env c cv mI rP rules rl e e' → DenoteAlike cval env e e'

/-- **One structure η step** of `env` at the η-capable family `T` (stored as
`.indInfo cvT caps`): between closed, well-typed `a` and `b`, the premises of the
checker's structure η rule (`DefEq.structEta`), at depth 0, from a fully applied
constructor `a` to `b`. -/
def StructEtaStep (env : Env md) (T : Key md) (cvT : Ix.Kernel.ConstantVal md) (caps : Ix.Kernel.IndCaps md)
    (a b : Ix.Kernel.Expr md) : Prop :=
  TypedClosed env a ∧ TypedClosed env b ∧
  ∃ (tb wtb : Ix.Kernel.Expr md) (c : Ix.Kernel.Key md) (us : List Ix.Kernel.Level) (cvc : Ix.Kernel.ConstantVal md) (cnP cnF : Nat)
    (us' : List Ix.Kernel.Level),
    Infer env .io 0 b tb ∧ Red env 0 tb wtb ∧
    a.getAppFn = .const c us ∧
    env.find? c = some (.ctorInfo cvc cnP cnF) ∧
    a.getAppArgs.length = cnP + cnF ∧
    wtb.getAppFn = .const T us' ∧
    caps.eta = true ∧ caps.etaCtor = some c ∧
    reservedBasisNames.contains T = false ∧
    reservedBasisNames.contains c = false ∧
    wtb.getAppArgs.length = caps.etaParams ∧
    us'.length = cvT.levelParams.length ∧
    cvc.levelParams = cvT.levelParams ∧
    (towerSlotsAll env T caps.etaFields || recSlotsAll env T caps.etaFields) = true ∧
    Level.isEquivList us us' = some true ∧
    Certs env 0 false (cvT.type.instantiateLevelParams cvT.levelParams us') wtb.getAppArgs ∧
    (towerSlotsAll env T caps.etaFields = false →
      EtaProjCerts env 0 T us' wtb.getAppArgs b cvT.levelParams (List.range caps.etaFields)) ∧
    DefEqList env 0 (a.getAppArgs.take caps.etaParams) wtb.getAppArgs ∧
    DefEqList env 0 (a.getAppArgs.drop caps.etaParams)
      (etaProjs env T us' wtb.getAppArgs b caps.etaFields)

/-- **One unit-like structure step** of `env` at the unit-like family `T` (stored
as `.indInfo cvT caps`): between closed, well-typed `a` and `b`, the premises of
the checker's unit-like structure rule (`DefEq.structUnit`), at depth 0. -/
def StructUnitStep (env : Env md) (T : Key md) (cvT : Ix.Kernel.ConstantVal md) (caps : Ix.Kernel.IndCaps md)
    (a b : Ix.Kernel.Expr md) : Prop :=
  TypedClosed env a ∧ TypedClosed env b ∧
  ∃ (ta wta tb wtb : Ix.Kernel.Expr md) (us' : List Ix.Kernel.Level),
    Infer env .io 0 a ta ∧ Red env 0 ta wta ∧
    wta.getAppFn = .const T us' ∧
    caps.unitlike = true ∧
    reservedBasisNames.contains T = false ∧
    wta.getAppArgs.length = caps.unitParams ∧
    us'.length = cvT.levelParams.length ∧
    Infer env .io 0 b tb ∧ Red env 0 tb wtb ∧
    DefEq env 0 wta wtb ∧
    Certs env 0 false (cvT.type.instantiateLevelParams cvT.levelParams us') wta.getAppArgs

/-- **One structural projection step** of `env` at field `i` of the structure
`sn`: from a closed, well-typed projection `e` of a constructor application, the
premises of the checker's projection rule (`Red.proj`), at depth 0, to the field. -/
def ProjStep (env : Env md) (sn : Ix.Kernel.Key md) (i : Nat) (e e' : Ix.Kernel.Expr md) : Prop :=
  TypedClosed env e ∧
  ∃ (u : Ix.Kernel.Expr md) (entry : ProjEntry md) (us : List Ix.Kernel.Level) (cvC : Ix.Kernel.ConstantVal md) (nP nF : Nat),
    e = .proj sn i u ∧
    env.findProj? sn i = some entry ∧
    u.getAppFn = .const entry.ctor us ∧
    i < entry.numFields ∧
    u.getAppArgs.length = entry.numParams + entry.numFields ∧
    us.length = entry.levelParams.length ∧
    entry.fireOk us = true ∧
    env.find? entry.ctor = some (.ctorInfo cvC nP nF) ∧
    Certs env 0 true (cvC.type.instantiateLevelParams cvC.levelParams us) u.getAppArgs ∧
    e' = u.getAppArgs.getD (entry.numParams + i) (.bvar 0)

/-- **The capability laws hold**: every structure η step of an η-capable stored
family, every unit-like step of a unit-like stored family, and every structural
projection step relate terms that denote alike. -/
def CapabilityLaws {V : Type w} [SetTheory V] (cval : Key md → (LevelParam → Nat) → V)
    (env : Env md) : Prop :=
  (∀ (T : Key md) (cvT : Ix.Kernel.ConstantVal md) (caps : Ix.Kernel.IndCaps md),
    env.find? T = some (.indInfo cvT caps) → ∀ a b, StructEtaStep env T cvT caps a b →
      DenoteAlike cval env a b) ∧
  (∀ (T : Key md) (cvT : Ix.Kernel.ConstantVal md) (caps : Ix.Kernel.IndCaps md),
    env.find? T = some (.indInfo cvT caps) → ∀ a b, StructUnitStep env T cvT caps a b →
      DenoteAlike cval env a b) ∧
  (∀ (sn : Ix.Kernel.Key md) (i : Nat) (e e' : Ix.Kernel.Expr md), ProjStep env sn i e e' → DenoteAlike cval env e e')

/-- **A value model with the Source laws**: every stored definition denotes its
value (`ValueModel`), and the recursor rules (`RecRuleLaws`) and the capability
laws (`CapabilityLaws`) hold. Theorem and opaque values and the quotient's
computation rule are not required (see the module docstring). -/
structure LawModel (V : Type w) [SetTheory V] (env : Env md) extends ValueModel V env where
  rec_rule : RecRuleLaws cval env
  caps : CapabilityLaws cval env

end Ix.Cert
