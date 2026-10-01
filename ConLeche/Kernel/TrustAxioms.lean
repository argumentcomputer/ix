module

public import ConLeche.Kernel.StdAxioms
public meta import ConLeche.Kernel.BasisA
public import ConLeche.Kernel.Core
public import ConLeche.Kernel.TrustPins

@[expose] public section

/-!
# The compiler-trust axiom family (task #95)

`Init`'s compiler-trust scaffolding is installed rather than
declined:

* `Lean.trustCompiler : True` is trivially realizable — it is
  installed as an *opaque* (stored `thmInfo`, exactly like a checked
  `opaque` declaration) with value `True.intro`, over a pinned `True`
  family.  No new meta-axiom: the model is `True.intro`'s own
  interpretation.
* `Lean.reduceNat` / `Lean.reduceBool` then check as ordinary
  `opaque`s (their exported values are identity functions modulo the
  `have := trustCompiler` wrapper); at install their stored values are
  pinned against the identity function
  (`ConLeche/Kernel/TrustPins.lean`, hand-pinned since task #273 —
  every toolchain's definition after zeta) by definitional equality —
  the task-#47 pattern: drift declines, never silently.
* `Lean.ofReduceNat` / `Lean.ofReduceBool` are pinned axioms over
  those stored opaques (the task-#34 standard-axioms machinery).  With
  the stored reduce operation certified to be the identity (a
  definitional-equality certificate at the axiom's own install,
  `checkOfReduceAx`), `∀ a b, reduceNat a = b → a = b` interprets to
  an inhabited proposition (the hypothesis *is* the conclusion), so
  both axioms are true in the set model with the proof point as value.

`sorryAx` remains the only axiom tolerated as a *declaration*: its
record installs nothing and any use of it declines
(`sorryAxName`, `ConLeche/Kernel/Basis/Names.lean`).

Raw pins below, hand-written through the builder in
`ConLeche/Kernel/Basis/Builder.lean`; the annotated forms are computed
from them at elaboration time by `#annotate_pins`
(`ConLeche/Kernel/BasisGen.lean`).
-/

namespace ConLeche

open Name (anonymous)
open BasisDSL

/-- The name `True`. -/
def trueName : Name := anonymous |>.str "True"

/-- The name `True.intro`. -/
def trueIntroName : Name := trueName |>.str "intro"

/-- The name `Lean.trustCompiler`. -/
def trustCompilerName : Name := (anonymous |>.str "Lean") |>.str "trustCompiler"

/-- The name `Lean.reduceNat`. -/
def reduceNatName : Name := (anonymous |>.str "Lean") |>.str "reduceNat"

/-- The name `Lean.reduceBool`. -/
def reduceBoolName : Name := (anonymous |>.str "Lean") |>.str "reduceBool"

/-- The name `Lean.ofReduceNat`. -/
def ofReduceNatName : Name := (anonymous |>.str "Lean") |>.str "ofReduceNat"

/-- The name `Lean.ofReduceBool`. -/
def ofReduceBoolName : Name := (anonymous |>.str "Lean") |>.str "ofReduceBool"

/-- The reduce operations pinned at their `opaque` install. -/
def reduceOpNames : List Name := [reduceNatName, reduceBoolName]

/-- The reduce operation an `ofReduce*` axiom speaks about. -/
def ofReduceOp (n : Name) : Name :=
  if n = ofReduceNatName then reduceNatName else reduceBoolName

/-! ## Pinned shapes

The `True` family, `Bool`, and the reduce operations' types have no
binders below a codomain (or none at all), so their annotated forms
coincide with the raw pins except for the one codomain annotation on
`… → …`; the reduce-operation and `ofReduce*` types are annotated by
`#annotate_pins` below.
-/

/-- Pinned `True` (shape only; capabilities are not pinned). -/
def trueCvA : ConstantVal := ⟨trueName, [], .sort .zero⟩

/-- Pinned `True.intro`. -/
def trueIntroCvA : ConstantVal := ⟨trueIntroName, [], .const trueName []⟩

/-- Pinned `Lean.trustCompiler`. -/
def trustCompilerA : ConstantVal := ⟨trustCompilerName, [], .const trueName []⟩

/-- Pinned `Bool` (shape only). -/
def boolCvA : ConstantVal := ⟨boolName, [], .sort (.succ .zero)⟩

/-- The element inductive of a reduce operation. -/
def reduceElemName (c : Name) : Name :=
  if c = reduceNatName then natName else boolName

/-- The element type of a reduce operation, as the pinned constant. -/
def reduceElemTy (c : Name) : Expr :=
  if c = reduceNatName then .const natName [] else .const boolName []

/-- Raw pinned type of `Lean.reduceNat` / `Lean.reduceBool`. -/
def reduceOpRaw (c : Name) : ConstantVal :=
  ⟨c, [], pi "n" (reduceElemTy c) (reduceElemTy c)⟩

/-- Raw pinned type of `Lean.ofReduceNat` / `Lean.ofReduceBool`:
`∀ (a b : τ), reduce a = b → a = b` at `τ = Nat` / `Bool`. -/
def ofReduceRaw (n : Name) : ConstantVal :=
  let c := ofReduceOp n
  let τ := reduceElemTy c
  let eqApp : Expr → Expr → Expr := fun x y =>
    ap3 (cnst eqName [.succ .zero]) τ x y
  ⟨n, [],
    pi "a" τ <|
    pi "b" τ <|
    pi "h" (eqApp (.app (cnst c) (bv 1)) (bv 0)) (eqApp (bv 2) (bv 1))⟩

/-! ## The annotated pins

Computed from the raw pins above by the checker's own annotation pass
while this module elaborates (`#annotate_pins`,
`ConLeche/Kernel/BasisGen.lean`), over the pinned prerequisites the
types mention: the `Eq`/`Nat` basis, the pinned `True` family, the
installed `Lean.trustCompiler` and the pinned `Bool`.  The `ofReduce*`
statements speak about the reduce operations, so those are annotated
first and passed in the second command's environment. -/

/-- The environment the reduce-operation pins are annotated over. -/
private def trustPinEnv : List ConstantInfo :=
  [.indInfo boolCvA {}, .axiomInfo trustCompilerA,
   .ctorInfo trueIntroCvA 0 0, .indInfo trueCvA {}, natA, eqA]

#annotate_pins over trustPinEnv
  | reduceNatCvA := reduceOpRaw reduceNatName
  | reduceBoolCvA := reduceOpRaw reduceBoolName

#annotate_pins over
    (.axiomInfo reduceBoolCvA :: .axiomInfo reduceNatCvA :: trustPinEnv)
  | ofReduceNatA := ofReduceRaw ofReduceNatName
  | ofReduceBoolA := ofReduceRaw ofReduceBoolName

/-- The annotated pinned type of a reduce operation. -/
def reduceOpCvA (c : Name) : ConstantVal :=
  if c = reduceNatName then reduceNatCvA else reduceBoolCvA

/-- The annotated pin an `ofReduce*` axiom is matched against. -/
def ofReducePinA (n : Name) : ConstantVal :=
  if n = ofReduceNatName then ofReduceNatA else ofReduceBoolA

/-! ## Environment predicates -/

/-- Is `Lean.trustCompiler` installable here?  The `True` family must
be stored with the pinned shapes (so the synthesized value
`True.intro` resolves and inhabits the pinned type), and the checked
axiom's type must match the pin. -/
def trustCompilerOk (env : Env) (cvA : ConstantVal) : Bool :=
  (match env.find? trueName with
   | some (.indInfo cvT _) => ConstantVal.matchesPin cvT trueCvA
   | _ => false) &&
  (match env.find? trueIntroName with
   | some (.ctorInfo cvTi 0 0) => ConstantVal.matchesPin cvTi trueIntroCvA
   | _ => false) &&
  ConstantVal.matchesPin cvA trustCompilerA

/-- Is the reduce operation `c` stored as a checked opaque
(`axiomInfo`, the storage kind of every checked `opaque`) of the
pinned type? -/
def reduceStoredOk (env : Env) (c : Name) : Bool :=
  match env.find? c with
  | some (.axiomInfo cvR) => ConstantVal.matchesPin cvR (reduceOpCvA c)
  | _ => false

/-- The element-inductive shape an `ofReduce*` axiom needs: the pinned
`Nat` basis resp. a standardly-shaped stored `Bool`. -/
def reduceElemOk (env : Env) (c : Name) : Bool :=
  if c = reduceNatName then decide (env.find? natName = some natA)
  else
    match env.find? boolName with
    | some (.indInfo cvB _) => ConstantVal.matchesPin cvB boolCvA
    | _ => false

/-- Is this checked axiom a pinned `ofReduce*` over a standardly-shaped
environment?  Requires the pinned `Eq` basis (the type is an equality
implication), the element inductive, and the reduce operation stored
as a pinned opaque — whose install already ran the identity
certificate (`checkReducePin`), the fact the model consumes here. -/
def ofReduceAxOk (env : Env) (cvA : ConstantVal) : Bool :=
  let c := ofReduceOp cvA.name
  decide (env.find? eqName = some eqA) &&
  reduceElemOk env c &&
  reduceStoredOk env c &&
  ConstantVal.matchesPin cvA (ofReducePinA cvA.name)

/-! ## The reduce-operation install pin -/

/-- The pinned defining expression of a reduce operation
(`ConLeche/Kernel/TrustPins.lean`: the plain identity, hand-written
with the basis builder — every toolchain's `have := trustCompiler; b`
after zeta). -/
def reduceDeclPin (c : Name) : Expr :=
  if c = reduceNatName then reduceNatDeclPin else reduceBoolDeclPin

/-- Syntactic guards on the generated pin (checked once at install). -/
def reducePinGuard (env : Env) (c : Name) : Bool :=
  (reduceDeclPin c).looseBVarsBounded 0 && !(reduceDeclPin c).hasFvar &&
  (reduceDeclPin c).allLevelParamsDefined [] &&
  (reduceDeclPin c).constsResolve env

/-- The identity certificate's variable: `fvar 0` at the element
type. -/
def reduceCertVar (c : Name) : Expr :=
  .fvar 0 (reduceElemTy c)

end ConLeche
