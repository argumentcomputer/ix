module

public import ConLeche.Kernel.CoreDefs

@[expose] public section

/-!
# The rules tier: a relational description of the core checker (task #305)

The moves the `.verified` core checker makes, as six mutually inductive
relations over the checker's own `Expr`, indexed by the environment and
the opening depth `d` (an `fvar` carries its type, so there is no context
list; a binder opens with `.fvar d ty` at depth `d + 1`, exactly as the
checker does):

* `Red env d e e'` — one relation for `whnfCore` and the `whnf` loop: β
  (gated and certified), ι with the stuck-major rescues, the projection
  rule, literal acceleration, δ, the two literal expansions, and the
  congruences the bodies recurse through (`appFn`, `projArg`).  `refl`
  and `trans` are constructors: a reduction is a denotation identity,
  so chaining costs nothing semantically, and the checker's loops and
  the major's preparation are chains.
* `DefEq env d a b` — definitional equality.  **No `trans`** (ruling 1):
  every non-leaf rule carries a further `DefEq` premise modelling the
  recursive structure of `isDefEq` — `redL` is "reduce the left side,
  then the continuation is definitionally equal", and with `Red` holding
  δ and the literal steps it is every continuation of the lazy-delta
  loop at once.  `symm` is a constructor; the right-hand variants of
  the one-sided rules are derived (`ConLeche/Rules/Derived.lean`).
* `Infer env g d e t` — type inference at a grade `g` (`Grade.full` for
  the front door, `Grade.io` for the infer-only lane).  The grade
  propagates to the recursive premises as `CoreFns.ioView` does; the
  io application rule at a `.never` binder has no argument certificate
  (`appSkip`), and the io λ rule runs no domain-sort check (the
  `g = .full →` premises).
* `Certs env d lic T args` — `iotaCerts`: the telescope certificate of a
  spine, licensed (`lic = true`, the ι and projection slots) or not (the
  rescues' synthetic spines).
* `DefEqList env d as bs` — `defEqList`, pairwise.
* `EtaProjCerts …` — `structEtaProjCerts`, the per-field telescope
  certificates of a projection-function family.

**Premise discipline.**  Each rule's premises are the certificates the
`.verified` checker runs at the cited site — the sub-runs (`Infer`,
`DefEq`, `Red`, the list walks) and the Boolean guards that determine
the *shape* of the conclusion (the stored data read, the arity tests,
the level checks).  Pure dispatch guards that only select a branch and
contribute nothing to the conclusion's shape or to soundness are not
premises (the `a == b` fast path, `quickPair`, `notProofFast`,
`isCtorApp`), so the relation is a superset of the run relation, and
every rule is sound on its own.  No mode index: the relation describes
the `.verified` checker (`betaGate = verifiedChecks = true`), so the
β gate reads `mb.pw.isNever` outright and every telescope walk the
fire paths run is licensed.

Scoping (`WScoped`, `looseBVarsBounded`, `LeavesBounded`, `CtxOk`) and
readability (`denoteMeta … = some _`) are NOT part of the inductive;
they are premises of the semantic soundness theorems
(`ConLeche/Model/Rules/*`), whose motives conclude the reduct's and the
inferred type's frame and reading (`Model/Rules/Motive.lean`).

Every rule's docstring cites its checker site in
`ConLeche/Kernel/Core.lean` (`Core.lean:N` below).  The checker is the
source of truth; a premise that reads wrong against the cited body is
a finding.

The bridge `run ⇒ derivation` is `ConLeche/Verify/Rules/*`; the
soundness `derivation ⇒ P currency` is `ConLeche/Model/Rules/*`.  This
module and its siblings under `ConLeche/Rules/` import the checker's
*definitions* (`Kernel/CoreDefs`: the fuel-free, monad-free helpers
the rules name) and never the bodies, the fueled entry points or the
knot — `tests/layering.sh`'s rules clause is the fence.
-/

namespace ConLeche.Rules

/-- The inference grade: `full` is the declaration front door
(`inferBody`, official's `infer_type_core(e, infer_only = false)`),
`io` the infer-only lane (`inferBodyIO`). -/
inductive Grade where
  | full
  | io
  deriving DecidableEq, Repr

/-- The fourteen binary `Nat` operations `reduceNat` accelerates
(`Core.lean:180-183`; official `reduce_nat`, `type_checker.cpp:639-668`):
the six structural ones and the eight pin-certified WF ones. -/
def natBinOpNames : List Name :=
  [natAddName, natSubName, natMulName, natPowName, natBeqName, natBleName] ++
    natDivModNames

mutual

/-- **Reduction**: the head steps of `whnfCore` and the `whnf` loop,
chained. -/
inductive Red (env : Env) : Nat → Expr → Expr → Prop where
  /-- Every `pure e` exit: the value clauses of `whnfCoreBody`
  (`Core.lean:970-975`), the stuck fallbacks (`:1003`, `:1033-1035`),
  an uncertified redex (`:1001`), `iotaRec = none` (`:1003`), the
  loop's fixpoint (`whnfStep`'s `pure e₁`, `:1088`). -/
  | refl {d : Nat} {e : Expr} : Red env d e e
  /-- The recursive `whnfCore` continuations after β/ι/proj
  (`Core.lean:990`, `:997`, `:1002`, `:1033`), the `whnf` loop
  (`whnfLoop`, `:1091-1095`), and the major's preparation chain
  (`prepareMajor`, `:785-807`). -/
  | trans {d : Nat} {e₁ e₂ e₃ : Expr} :
      Red env d e₁ e₂ → Red env d e₂ e₃ → Red env d e₁ e₃
  /-- Head normalisation inside an application (`whnfCoreBody`'s
  `.app` clause, `Core.lean:976-977`: `whnfCore f` before the redex
  tests). -/
  | appFn {d : Nat} {f f' a : Expr} :
      Red env d f f' → Red env d (.app f a) (.app f' a)
  /-- Reduction of a projection's scrutinee (`whnfCoreBody`'s `.proj`
  clause, `Core.lean:1004-1006`: `whnf pe`). -/
  | projArg {d : Nat} {sn : Name} {i : Nat} {e e' : Expr} :
      Red env d e e' → Red env d (.proj sn i e) (.proj sn i e')
  /-- **β at a fired gate** (`Core.lean:989-990`, `betaGateFires` at
  `.verified`): a λ whose validated annotation datum is `.never`
  reduces with no certificate — the graph-regime licence
  (`WellDenotedV_beta_gate`, `Model/Steps/Gate.lean`). -/
  | betaGate {d : Nat} {ty body a : Expr} {mb : BinderMeta} :
      mb.pw.isNever = true →
      Red env d (.app (.lam ty body mb) a) (body.instantiate1 a)
  /-- **β, certified** (`Core.lean:996-998`): the argument's io-grade
  type is definitionally equal to the domain. -/
  | beta {d : Nat} {ty body a ta : Expr} {mb : BinderMeta} :
      Infer env .io d a ta → DefEq env d ta ty →
      Red env d (.app (.lam ty body mb) a) (body.instantiate1 a)
  /-- **δ** (`whnfStep`, `Core.lean:1079-1089`; also every lazy-delta
  continuation of `defeqStep`, `:1537-1577`): one definition unfolded
  at the head.  A theorem never unfolds (`unfoldDefinition`). -/
  | delta {d : Nat} {e e' : Expr} :
      unfoldDefinition env e = some e' → Red env d e e'
  /-- A `Nat`-literal major converts to constructor form, one layer
  (`litMajorToCtor`'s `litToCtorIfNat` arm, `Core.lean:739`). -/
  | natLit {d : Nat} {n : Nat} :
      natLitSupported env = true →
      Red env d (.lit (.natVal n)) (natLitToConstructor n)
  /-- A `String` literal expands to its constructor form
  (`litMajorToCtor`, `Core.lean:736-738`; `projLitToCtor`, `:752-754`;
  `defeqStep`'s string arms, `:1610-1617` — one rule for the three
  sites; the sites that re-reduce chain a `Red` after it). -/
  | strLit {d : Nat} {s : String} :
      strLitSupported env = true →
      Red env d (.lit (.strVal s)) (strLitToConstructor s)
  /-- **`Nat.succ` packing** (`reduceNat`, `Core.lean:171-178`): the
  argument reduces to a literal reading. -/
  | natSucc {d : Nat} {a w : Expr} {n : Nat} :
      natLitSupported env = true →
      Red env d a w → rawNatLit? w = some n →
      Red env d (.app (.const natSuccName []) a) (.lit (.natVal (n + 1)))
  /-- **Binary `Nat` acceleration** (`reduceNat`, `Core.lean:181-201`):
  a stored operation on two arguments that reduce to literal readings
  folds to `natOpResult`. -/
  | natOp {d : Nat} {c : Name} {a wa b wb r : Expr} {n₁ n₂ : Nat} :
      c ∈ natBinOpNames → natOpStored env c = true →
      Red env d a wa → rawNatLit? wa = some n₁ →
      Red env d b wb → rawNatLit? wb = some n₂ →
      natOpResult c n₁ n₂ = some r →
      Red env d (.app (.app (.const c []) a) b) r
  /-- **The structural projection** `proj_i (ctor p⃗ x⃗) ↦ x_i`
  (`whnfCoreBody`'s `.proj` clause, `Core.lean:1013-1030`), driven by
  the projection table, fired under the entry's guard, and certified
  by the constructor spine's licensed telescope certificate
  (`projCertAt` at `.verified` = `projCert`, `:940-965`). -/
  | proj {d : Nat} {sn : Name} {i : Nat} {e : Expr} {entry : ProjEntry}
      {us : List Level} {cvC : ConstantVal} {nP nF : Nat} :
      env.findProj? sn i = some entry →
      e.getAppFn = .const entry.ctor us →
      i < entry.numFields →
      e.getAppArgs.length = entry.numParams + entry.numFields →
      us.length = entry.levelParams.length →
      entry.fireOk us = true →
      env.find? entry.ctor = some (.ctorInfo cvC nP nF) →
      Certs env d true (cvC.type.instantiateLevelParams cvC.levelParams us)
        e.getAppArgs →
      Red env d (.proj sn i e) (e.getAppArgs.getD (entry.numParams + i) (.bvar 0))
  /-- **ι** (`iotaRec`, `Core.lean:809-938`): a stored recursor
  applied to exactly its telescope, whose prepared major (the `Red`
  premise: `prepareMajor`'s whnf / literal / rescue chain) is a
  constructor application with a firing rule.  The level comparands,
  the parameter comparison, the two licensed telescope certificates
  and the index comparison are the checker's, in its order. -/
  | iota {d : Nat} {e : Expr} {c : Name} {us : List Level} {cv : ConstantVal}
      {mI rP : Nat} {rules : List RecRule} {major : Expr} {cj : Name}
      {usj : List Level} {cvj : ConstantVal} {cnP cnF : Nat} {rl : RecRule}
      {residual : Expr} :
      e.getAppFn = .const c us →
      env.find? c = some (.recInfo cv mI rP rules) →
      e.getAppArgs.length = mI + 1 →
      us.length = cv.levelParams.length →
      Red env d (e.getAppArgs.getD mI (.bvar 0)) major →
      major.getAppFn = .const cj usj →
      env.find? cj = some (.ctorInfo cvj cnP cnF) →
      rules.find? (fun r' => r'.ctor == cj) = some rl →
      major.getAppArgs.length = rl.ctorParams + rl.nfields →
      rl.fire ≠ .inert →
      Level.isEquivList usj
        (recFireComparands rl cv.levelParams us cvj.levelParams
          e.getAppArgs rP).1 = some true →
      (rl.compareParams = true →
        DefEqList env d (major.getAppArgs.take rl.ctorParams)
          (recFireComparands rl cv.levelParams us cvj.levelParams
            e.getAppArgs rP).2) →
      Certs env d true (cv.type.instantiateLevelParams cv.levelParams us)
        (e.getAppArgs.take mI ++ [major]) →
      Certs env d true (cvj.type.instantiateLevelParams cvj.levelParams usj)
        major.getAppArgs →
      (mI ≠ rP →
        piResidual (cvj.type.instantiateLevelParams cvj.levelParams usj)
          major.getAppArgs = some residual) →
      (mI ≠ rP →
        DefEqList env d (residual.getAppArgs.drop rl.ctorParams)
          ((e.getAppArgs.take mI).drop rP)) →
      Red env d e
        (Expr.mkAppN (rl.rhs.instantiateLevelParams cv.levelParams us)
          (e.getAppArgs.take rP ++ major.getAppArgs.drop rl.ctorParams))
  /-- **The K rescue** (`majorToCtor`'s K branch, `Core.lean:570-620`;
  official `to_cnstr_when_K`): at a K-flagged single-rule recursor the
  parameters-only constructor application is fabricated from the
  major's io-inferred, head-normalised type, scope-guarded, certified
  against the constructor's telescope, type-checked against the major's
  type, and equated to the major by proof irrelevance (the last `DefEq`
  premise: the bridge builds it from `proofIrrel`'s two arms). -/
  | rescueK {d : Nat} {major tm tmaj fab tf : Expr} {recName : Name}
      {cv : ConstantVal} {mI rP : Nat} {rl : RecRule} {cvj : ConstantVal}
      {cnP cnF : Nat} {T : Name} {tus ust : List Level} {cvT : ConstantVal}
      {caps : IndCaps} :
      env.find? recName = some (.recInfo cv mI rP [rl]) →
      rl.k = true →
      env.find? rl.ctor = some (.ctorInfo cvj cnP cnF) →
      (cvj.type.piResult).getAppFn = .const T tus →
      env.find? T = some (.indInfo cvT caps) →
      Infer env .io d major tm → Red env d tm tmaj →
      tmaj.getAppFn = .const T ust →
      cvj.levelParams.length = ust.length →
      cnP ≤ tmaj.getAppArgs.length →
      fab = Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP) →
      fab.wscopedB d = true → fab.looseBVarsBounded 0 = true →
      fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l) = true →
      Certs env d false (cvj.type.instantiateLevelParams cvj.levelParams ust)
        (tmaj.getAppArgs.take cnP) →
      Infer env .io d fab tf → DefEq env d tmaj tf →
      DefEq env d fab major →
      Red env d major fab
  /-- **The structure-η rescue** (`majorToCtor`'s η branch,
  `Core.lean:621-672`; official `to_cnstr_when_structure`): at an
  η-flagged single-rule recursor whose major's type is a never-`Prop`
  instance of the structure, the constructor of the major's
  projections is fabricated, scope-guarded, certified against the
  constructor's telescope, and equated to the major by the structure-η
  certificate (or, at a field-less structure, by proof irrelevance —
  either way the last `DefEq` premise).  At a projection-function
  family the per-field telescope certificates are a premise of their
  own, as in `DefEq.structEta`: the rescue's η certificate runs
  `structEtaProjCerts` there (`structEtaCertWith`, `Core.lean:412-417`),
  and the fabrication READS only through those slots' storage. -/
  | rescueEta {d : Nat} {major tm tmaj fab : Expr} {recName : Name}
      {cv : ConstantVal} {mI rP : Nat} {rl : RecRule} {cvj : ConstantVal}
      {cnP cnF : Nat} {T : Name} {tus ust : List Level} {cvT : ConstantVal}
      {caps : IndCaps} :
      env.find? recName = some (.recInfo cv mI rP [rl]) →
      rl.eta = true →
      env.find? rl.ctor = some (.ctorInfo cvj cnP cnF) →
      (cvj.type.piResult).getAppFn = .const T tus →
      env.find? T = some (.indInfo cvT caps) →
      Infer env .io d major tm → Red env d tm tmaj →
      tmaj.getAppFn = .const T ust →
      tmaj.getAppArgs.length = caps.etaParams →
      ust.length = cvT.levelParams.length →
      capsNeverZero cvT.levelParams ust caps = true →
      fab = Expr.mkAppN (.const caps.etaCtor ust)
        (etaFabArgsE env T ust tmaj.getAppArgs major caps.etaFields) →
      fab.wscopedB d = true → fab.looseBVarsBounded 0 = true →
      fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l) = true →
      Certs env d false (cvj.type.instantiateLevelParams cvj.levelParams ust)
        (etaFabArgsE env T ust tmaj.getAppArgs major caps.etaFields) →
      (towerSlotsAll env T caps.etaFields = false →
        EtaProjCerts env d T ust tmaj.getAppArgs major cvT.levelParams
          (List.range caps.etaFields)) →
      DefEq env d fab major →
      Red env d major fab
  /-- **The `And` rescue** (`majorToCtor`'s `And` branch,
  `Core.lean:673-732`; `And` only, by ruling): `And.intro a b
  (.proj And 0 h) (.proj And 1 h)` is fabricated for a stuck proof
  `h`, certified the K branch's way. -/
  | rescueAnd {d : Nat} {major tm tmaj fab tf : Expr} {recName : Name}
      {cv : ConstantVal} {mI rP : Nat} {rl : RecRule} {cvj : ConstantVal}
      {cnP cnF : Nat} {tus ust : List Level} {cvT : ConstantVal}
      {caps : IndCaps} :
      env.find? recName = some (.recInfo cv mI rP [rl]) →
      env.find? rl.ctor = some (.ctorInfo cvj cnP cnF) →
      (cvj.type.piResult).getAppFn = .const andName tus →
      env.find? andName = some (.indInfo cvT caps) →
      Infer env .io d major tm → Red env d tm tmaj →
      tmaj.getAppFn = .const andName ust →
      tmaj.getAppArgs.length = cnP →
      cvj.levelParams.length = ust.length →
      andRescueSlots env rl.ctor cnP ust = true →
      fab = Expr.mkAppN (.const rl.ctor ust)
        (tmaj.getAppArgs ++ [.proj andName 0 major, .proj andName 1 major]) →
      fab.wscopedB d = true → fab.looseBVarsBounded 0 = true →
      fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l) = true →
      Certs env d false (cvj.type.instantiateLevelParams cvj.levelParams ust)
        (tmaj.getAppArgs ++ [.proj andName 0 major, .proj andName 1 major]) →
      Infer env .io d fab tf → DefEq env d tmaj tf →
      DefEq env d fab major →
      Red env d major fab

/-- **Definitional equality**: the verdict `true` of `isDefEq`.

**There is no `trans` rule, deliberately, and none can be added**
(task #309, the experiment recorded in DESIGN.md).  The relation is
not an equivalence on terms: it is the checker's verdict, and the
checker only ever compares terms that are well-formed *together* — a
fact the rules never state, because well-formedness (scoping, the
readability of annotations, the grading of the reading) is semantic
and may not enter this inductive.  Every rule respects one syntactic
discipline instead: **the subject of each `DefEq` premise is either a
subterm of the conclusion or is produced by an existence-form `Red` /
`Infer` premise** (a reduct, an inferred type), so the soundness proof
(`ConLeche/Model/Rules/Sound.lean`) always has the premise's terms in
hand.  `trans` is the unique rule that would break it: its middle
term comes from nowhere, and with it two rules that are each sound
alone meet — `fvar` compares free variables by index only (their
annotations are not compared, as the checker does not), while
`proofFast` *reads* an annotation to decide "definitely a proof" —
and derive `DefEq env d (.fvar i ty) (.fvar i' ty')` for every
`i`, `i'`, which no model satisfies.  The recursive-structure rules
(`redL`, `natSucc`, `eta`, `structUnit`) are therefore not a
proof-engineering convenience but what keeps the relation sound; the
one chaining that is sound, "reduce, then continue", is `redL`, and
its right-hand and δ variants are derived in `Derived.lean`. -/
inductive DefEq (env : Env) : Nat → Expr → Expr → Prop where
  /-- The syntactic fast paths (`defeqStep`, `Core.lean:1463`, `:1472`),
  the literal leaf (`:1582`), a same-index `fvar` pair is `fvar`
  below. -/
  | refl {d : Nat} {a : Expr} : DefEq env d a a
  /-- Symmetry.  Not a checker move: the constructor from which every
  right-hand-side variant of a one-sided rule is derived. -/
  | symm {d : Nat} {a b : Expr} : DefEq env d a b → DefEq env d b a
  /-- **Reduce the left side, then continue** — the recursive-structure
  rule (ruling 1).  Covers `whnfCore` of both sides (`Core.lean:1466-1467`,
  with `symm`), literal acceleration (`:1517-1529`), every lazy-delta
  continuation (`:1537-1577`), and the string-literal expansion. -/
  | redL {d : Nat} {a a' b : Expr} :
      Red env d a a' → DefEq env d a' b → DefEq env d a b
  /-- Two sorts (`Core.lean:1581`). -/
  | sort {d : Nat} {u v : Level} :
      Level.isEquiv u v = some true → DefEq env d (.sort u) (.sort v)
  /-- Two free variables of the same index (`Core.lean:1618-1620`).  The
  annotations are NOT compared, as the checker does not compare them:
  at a well-formed call `CtxOk` pins every opened variable's
  annotation, so the reading ignores them.  This is one half of why
  the relation has no `trans` (see the inductive's docstring). -/
  | fvar {d i : Nat} {ty₁ ty₂ : Expr} :
      DefEq env d (.fvar i ty₁) (.fvar i ty₂)
  /-- Two constants of the same name at equivalent levels
  (`Core.lean:1621-1626`). -/
  | const {d : Nat} {n : Name} {us us' : List Level} :
      Level.isEquivList us us' = some true →
      DefEq env d (.const n us) (.const n us')
  /-- The packed zero against `Nat.zero` (`Core.lean:1586-1591`; no
  support guard is read there). -/
  | natZero {d : Nat} : DefEq env d (.lit (.natVal 0)) (.const natZeroName [])
  /-- A packed successor against `Nat.succ x`: unpack one layer and
  continue (`Core.lean:1592-1597`). -/
  | natSucc {d : Nat} {k : Nat} {x : Expr} :
      DefEq env d (.lit (.natVal k)) x →
      DefEq env d (.lit (.natVal (k + 1))) (.app (.const natSuccName []) x)
  /-- ∀-congruence (`Core.lean:1627-1643`): domains, then bodies opened
  with the RIGHT domain, then the annotation agreement. -/
  | forallE {d : Nat} {ty₁ body₁ ty₂ body₂ : Expr} {m₁ m₂ : BinderMeta} :
      DefEq env d ty₁ ty₂ →
      DefEq env (d + 1) (body₁.instantiate1 (.fvar d ty₂))
        (body₂.instantiate1 (.fvar d ty₂)) →
      m₁.pw = m₂.pw →
      DefEq env d (.forallE ty₁ body₁ m₁) (.forallE ty₂ body₂ m₂)
  /-- λ-congruence (`Core.lean:1644-1651`), as for ∀. -/
  | lam {d : Nat} {ty₁ body₁ ty₂ body₂ : Expr} {m₁ m₂ : BinderMeta} :
      DefEq env d ty₁ ty₂ →
      DefEq env (d + 1) (body₁.instantiate1 (.fvar d ty₂))
        (body₂.instantiate1 (.fvar d ty₂)) →
      m₁.pw = m₂.pw →
      DefEq env d (.lam ty₁ body₁ m₁) (.lam ty₂ body₂ m₂)
  /-- Per-node application congruence.  The checker's spine-wise
  congruence (`Core.lean:1652-1678`) and the same-head short-circuit
  (`defeqSpine`, `:1426-1458`) are derived from it
  (`DefEq.spine`, `DefEq.constSpine`). -/
  | app {d : Nat} {f₁ a₁ f₂ a₂ : Expr} :
      DefEq env d f₁ f₂ → DefEq env d a₁ a₂ →
      DefEq env d (.app f₁ a₁) (.app f₂ a₂)
  /-- Projection congruence at the same table slot (`Core.lean:1679-1689`). -/
  | proj {d : Nat} {s : Name} {i : Nat} {e₁ e₂ : Expr} :
      DefEq env d e₁ e₂ → DefEq env d (.proj s i e₁) (.proj s i e₂)
  /-- **η** (`etaCert`, `Core.lean:508-534`, at the one-sided λ arm
  `:1690-1692`): `b`'s io-inferred type head-normalises to a ∀ whose
  domain is definitionally equal to the λ's, the body is pointwise
  `b` applied, and the annotations agree. -/
  | eta {d : Nat} {ty₁ body₁ b tb ty₂ B : Expr} {m₁ m₂ : BinderMeta} :
      Infer env .io d b tb → Red env d tb (.forallE ty₂ B m₂) →
      DefEq env d ty₂ ty₁ →
      DefEq env (d + 1) (body₁.instantiate1 (.fvar d ty₁))
        (.app b (.fvar d ty₁)) →
      m₁.pw = m₂.pw →
      DefEq env d (.lam ty₁ body₁ m₁) b
  /-- **The `isProofFast` yes-arm** (`propIrrel`, `Core.lean:331-332`):
  both heads' validated data say "a proposition at every valuation" —
  the squash-regime licence (`prf_of_isProofFast`). -/
  | proofFast {d : Nat} {a b : Expr} :
      isProofFast env.find? a = true → isProofFast env.find? b = true →
      DefEq env d a b
  /-- **Proof irrelevance** (`propIrrel`'s slow arm, `Core.lean:338-356`,
  and `proofIrrel`'s `Prop` arm, `:295-325`): both sides' io-inferred
  types have sort `Prop`.  The two types are never compared — the
  model licenses that (every proof is the point). -/
  | proofIrrel {d : Nat} {a ta tta b tb ttb : Expr} {u v : Level} :
      Infer env .io d a ta → Infer env .io d ta tta →
      Red env d tta (.sort u) → Level.isEquiv u .zero = some true →
      Infer env .io d b tb → Infer env .io d tb ttb →
      Red env d ttb (.sort v) → Level.isEquiv v .zero = some true →
      DefEq env d a b
  /-- **Unit-likeness** (`proofIrrel`'s first arm, `Core.lean:287-294`):
  both sides' io-inferred types head-normalise to the basis unit type. -/
  | unitLike {d : Nat} {a ta wta b tb wtb : Expr} :
      Infer env .io d a ta → Red env d ta wta → isUnitLikeTy env wta = true →
      Infer env .io d b tb → Red env d tb wtb → isUnitLikeTy env wtb = true →
      DefEq env d a b
  /-- **Structure η** (`structEtaCert` → `structEtaCertWith`,
  `Core.lean:379-458`, `:460-476`; the same certificate serves the
  η rescue at the type it already computed): `a` is a fully applied
  constructor of an η-capable stored structure, `b`'s io-inferred type
  head-normalises to that structure at agreeing levels, the type
  application is certified against the former's telescope, the
  per-field telescopes of a projection-function family are certified,
  the parameters agree pairwise, and every field is the corresponding
  projection of `b`. -/
  | structEta {d : Nat} {a b tb wtb : Expr} {c : Name} {us : List Level}
      {cvc : ConstantVal} {cnP cnF : Nat} {T : Name} {us' : List Level}
      {cvT : ConstantVal} {caps : IndCaps} :
      Infer env .io d b tb → Red env d tb wtb →
      a.getAppFn = .const c us →
      env.find? c = some (.ctorInfo cvc cnP cnF) →
      a.getAppArgs.length = cnP + cnF →
      wtb.getAppFn = .const T us' →
      env.find? T = some (.indInfo cvT caps) →
      caps.eta = true → caps.etaCtor = c →
      reservedBasisNames.contains T = false →
      reservedBasisNames.contains c = false →
      wtb.getAppArgs.length = caps.etaParams →
      us'.length = cvT.levelParams.length →
      cvc.levelParams = cvT.levelParams →
      (towerSlotsAll env T caps.etaFields ||
        recSlotsAll env T caps.etaFields) = true →
      Level.isEquivList us us' = some true →
      Certs env d false (cvT.type.instantiateLevelParams cvT.levelParams us')
        wtb.getAppArgs →
      (towerSlotsAll env T caps.etaFields = false →
        EtaProjCerts env d T us' wtb.getAppArgs b cvT.levelParams
          (List.range caps.etaFields)) →
      DefEqList env d (a.getAppArgs.take caps.etaParams) wtb.getAppArgs →
      DefEqList env d (a.getAppArgs.drop caps.etaParams)
        (etaProjs env T us' wtb.getAppArgs b caps.etaFields) →
      DefEq env d a b
  /-- **Unit-like structure** (`structUnitCert`, `Core.lean:478-506`):
  both sides inhabit the same stored unit-like family — `a`'s
  io-inferred type head-normalises to it, `b`'s type is definitionally
  equal, and the type application is certified against the family's
  telescope. -/
  | structUnit {d : Nat} {a ta wta b tb wtb : Expr} {T : Name}
      {us' : List Level} {cvT : ConstantVal} {caps : IndCaps} :
      Infer env .io d a ta → Red env d ta wta →
      wta.getAppFn = .const T us' →
      env.find? T = some (.indInfo cvT caps) →
      caps.unitlike = true →
      reservedBasisNames.contains T = false →
      wta.getAppArgs.length = caps.unitParams →
      us'.length = cvT.levelParams.length →
      Infer env .io d b tb → Red env d tb wtb →
      DefEq env d wta wtb →
      Certs env d false (cvT.type.instantiateLevelParams cvT.levelParams us')
        wta.getAppArgs →
      DefEq env d a b

/-- **Type inference** at a grade. -/
inductive Infer (env : Env) : Grade → Nat → Expr → Expr → Prop where
  /-- `Core.lean:1114` / `:1294`. -/
  | sort {g : Grade} {d : Nat} {u : Level} :
      Infer env g d (.sort u) (.sort (.succ u))
  /-- `Core.lean:1115-1123` / `:1295-1297`: an opened variable's stored
  type, at the leaf scope check. -/
  | fvar {g : Grade} {d idx : Nat} {ty : Expr} :
      idx < d → Infer env g d (.fvar idx ty) ty
  /-- `Core.lean:1125-1136` / `:1298-1309`: a stored constant that is
  not a projection table, at the right level arity. -/
  | const {g : Grade} {d : Nat} {n : Name} {us : List Level}
      {ci : ConstantInfo} :
      env.find? n = some ci → ci.isTowerEntry = false →
      us.length = ci.toConstantVal.levelParams.length →
      Infer env g d (.const n us)
        (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us)
  /-- `Core.lean:1137-1139` / `:1310-1312`. -/
  | natLit {g : Grade} {d n : Nat} :
      natLitSupported env = true →
      Infer env g d (.lit (.natVal n)) (.const natName [])
  /-- `Core.lean:1140-1146` / `:1313-1316`. -/
  | strLit {g : Grade} {d : Nat} {s : String} :
      strLitSupported env = true →
      Infer env g d (.lit (.strVal s)) (.const stringName [])
  /-- **∀-formation** (`Core.lean:1147-1163` / `:1317-1326`): the domain's
  type reduces to a sort, the opened body's type reduces to a sort, and
  the node's datum is the codomain sort's zero-ness (validated at
  `.verified`). -/
  | forallE {g : Grade} {d : Nat} {ty body s bs : Expr} {u v : Level}
      {mb : BinderMeta} :
      Infer env g d ty s → Red env d s (.sort u) →
      Infer env g (d + 1) (body.instantiate1 (.fvar d ty)) bs →
      Red env (d + 1) bs (.sort v) →
      Level.zeronessOf v = mb.pw →
      Infer env g d (.forallE ty body mb) (.sort (.imax u v))
  /-- **λ** (`Core.lean:1164-1214` / `:1327-1348`).  At the full grade the
  domain's type reduces to a sort (`g = .full →`: official's
  `infer_lambda` skips it at `infer_only`, and so does the io body);
  the opened body is inferred at the grade; the codomain datum is
  validated once per λ-chain — at an inner λ by datum equality with
  the neighbour, at the innermost binder by the io-grade sort
  computation on the body type (`body.lamPw = none →`).  The `s u btt
  v` witnesses are junk where their premise is vacuous. -/
  | lam {g : Grade} {d : Nat} {ty body s bt btt : Expr} {u v : Level}
      {mb : BinderMeta} :
      (g = .full → Infer env .full d ty s) →
      (g = .full → Red env d s (.sort u)) →
      Infer env g (d + 1) (body.instantiate1 (.fvar d ty)) bt →
      (∀ pwI, body.lamPw = some pwI → mb.pw = pwI) →
      (body.lamPw = none → Infer env .io (d + 1) bt btt) →
      (body.lamPw = none → Red env (d + 1) btt (.sort v)) →
      (body.lamPw = none → Level.zeronessOf v = mb.pw) →
      Infer env g d (.lam ty body mb) (.forallE ty (bt.abstract1 d) mb)
  /-- **Application, certified** (`Core.lean:1215-1227`; the io body at
  a possibly-zero datum, `:1367-1370`): the head's type reduces to a
  ∀, and the argument's type at the grade is definitionally equal to
  the domain. -/
  | app {g : Grade} {d : Nat} {f a tf ty body ta : Expr} {mt : BinderMeta} :
      Infer env g d f tf → Red env d tf (.forallE ty body mt) →
      Infer env g d a ta → DefEq env d ta ty →
      Infer env g d (.app f a) (body.instantiate1 a)
  /-- **THE io SITE** (`Core.lean:1349-1372`): at the io grade, a ∀ whose
  validated datum is `.never` needs no argument certificate — the
  graph-regime licence (`io_domain_transfer`, `Model/IOLicense.lean`). -/
  | appSkip {d : Nat} {f a tf ty body : Expr} {mt : BinderMeta} :
      Infer env .io d f tf → Red env d tf (.forallE ty body mt) →
      mt.pw.isNever = true →
      Infer env .io d (.app f a) (body.instantiate1 a)
  /-- **Projection** (`Core.lean:1228-1289` / `:1373-1409`): the
  scrutinee's type reduces to an application of the node's own
  structure with a table entry at the right arities, the `Prop`
  restriction holds, and the type is the entry's body at the spine
  and the subject. -/
  | proj {g : Grade} {d : Nat} {sn : Name} {i : Nat} {pe tpe te : Expr}
      {us : List Level} {entry : ProjEntry} :
      Infer env g d pe tpe → Red env d tpe te →
      te.getAppFn = .const sn us →
      env.findProj? sn i = some entry →
      te.getAppArgs.length = entry.numParams →
      us.length = entry.levelParams.length →
      (Level.isEquiv entry.structSort .zero = some true →
        Level.isEquiv (Level.subst entry.levelParams us entry.fieldSort) .zero
          = some true) →
      Infer env g d (.proj sn i pe) (entry.typeAt us te.getAppArgs pe)

/-- **The telescope certificate** (`iotaCerts`, `Core.lean:230-244`):
each argument's io-grade type is definitionally equal to its binder
domain, the domains instantiated along the spine; at a licensed walk a
`.never` slot is skipped (the ι-slot licence, `Model/Steps/IotaGate.lean`). -/
inductive Certs (env : Env) : Nat → Bool → Expr → List Expr → Prop where
  | nil {d : Nat} {lic : Bool} {T : Expr} : Certs env d lic T []
  | skip {d : Nat} {lic : Bool} {ty body arg : Expr} {mb : BinderMeta}
      {rest : List Expr} :
      lic = true → mb.pw.isNever = true →
      Certs env d lic (body.instantiate1 arg) rest →
      Certs env d lic (.forallE ty body mb) (arg :: rest)
  | cert {d : Nat} {lic : Bool} {ty body arg ta : Expr} {mb : BinderMeta}
      {rest : List Expr} :
      Infer env .io d arg ta → DefEq env d ta ty →
      Certs env d lic (body.instantiate1 arg) rest →
      Certs env d lic (.forallE ty body mb) (arg :: rest)

/-- **Pairwise definitional equality** (`defEqList`, `Core.lean:246-252`). -/
inductive DefEqList (env : Env) : Nat → List Expr → List Expr → Prop where
  | nil {d : Nat} : DefEqList env d [] []
  | cons {d : Nat} {a b : Expr} {as bs : List Expr} :
      DefEq env d a b → DefEqList env d as bs →
      DefEqList env d (a :: as) (b :: bs)

/-- **The per-field telescope certificates of a structure-η
certification at a projection-function family**
(`structEtaProjCerts`, `Core.lean:358-377`). -/
inductive EtaProjCerts (env : Env) :
    Nat → Name → List Level → List Expr → Expr → List Name → List Nat → Prop
    where
  | nil {d : Nat} {T : Name} {us' : List Level} {targs : List Expr} {b : Expr}
      {lpsT : List Name} :
      EtaProjCerts env d T us' targs b lpsT []
  | cons {d : Nat} {T : Name} {us' : List Level} {targs : List Expr} {b : Expr}
      {lpsT : List Name} {i : Nat} {rest : List Nat} {cvp : ConstantVal}
      {mI rP : Nat} {rules : List RecRule} :
      env.find? (projFnName T i) = some (.recInfo cvp mI rP rules) →
      cvp.levelParams = lpsT →
      (cvp.type.stripPis (targs.length + 1)).isSome = true →
      Certs env d false (cvp.type.instantiateLevelParams cvp.levelParams us')
        (targs ++ [b]) →
      EtaProjCerts env d T us' targs b lpsT rest →
      EtaProjCerts env d T us' targs b lpsT (i :: rest)

end

end ConLeche.Rules
