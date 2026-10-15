module

public meta import Lean
public meta import IxC.Kernel.TypeChecker

/- `public section`, deliberately NOT `@[expose]`: every definition here is
elaboration-time machinery whose body no importer unfolds, and an exposed
body may not mention the module's `private` helpers (`splice`, the quoters,
the `evalX` wrappers). -/
public section

/-!
# `#annotate_basis` — the pinned declarations, annotated at elaboration time

The pinned basis blocks, the standard-axiom prerequisite families and
the compiler-trust pins are *stored annotated*: the installation
(`installBasisDecl`, `IxC/Kernel/Checker.lean`) puts them into the
environment verbatim, and the model proofs read their `pw` data off
the stored constants.  The annotated forms are not a second source of
truth — they are what **this checker's own annotation pass**
(`annotateCore` at `.verified`) computes from the raw pins.

Until 2026-09-06 that computation lived in an offline generator
(`AnnotateBasis.lean`, a `[[lean_exe]]`) whose `Repr` output was pasted
into the pin modules as ~1 900 lines of fully-qualified constructor
spellings.  The literals were therefore a *committed cache with no
checked relation to their source*: nothing in the build re-ran the
generator, and a stale paste would have been invisible.

`#annotate_basis` replaces the paste.  It runs the same recipe while
the pin module elaborates and defines the annotated constants with
`addDecl`/`compileDecl`, so the definition's value is the very term
`annotateCore` produced — the same closed literal the `decide`/`rfl`
consumers in `IxC/Kernel/Model/*` saw before, now *derived* rather than
transcribed, and re-derived on every build.  An annotation failure is
an elaboration error, never a silently stale constant.

## The recipe

Exactly what `checkDecl`'s `.basisDecl` install would do, in
dependency order:

* the constant's **type** is annotated over the environment holding
  the pins annotated so far (`over` gives that environment's tail);
* for a recursor, the install-computed rule fields are filled first —
  `ctorParams` from the stored constructor, `fire` from
  `Expr.recRulePlain` — and then each rule's **rhs** is annotated over
  the environment extended by the recursor itself (a rule's rhs may
  mention it, as `Nat.rec`'s successor rule does);
* the result is appended to the environment for the next entry.

## The two commands

```
#annotate_basis over <env : List ConstantInfo>
  | eqA := eqRaw
  | ...
```
defines `ConstantInfo` constants and threads each one into the
environment for the entries that follow.

```
#annotate_pins over <env : List ConstantInfo>
  | propextA := propextRaw
  | ...
```
defines `ConstantVal` constants (the two standard axioms and the four
compiler-trust pins), each annotated over the *same* environment; a
pin that must be visible to a later one is passed in the next
command's `over`.

The `over` term is elaborated and evaluated at `List ConstantInfo`, so
it may name constants this command defined earlier in the file.
-/

/- The whole module is elaboration-time code: quoters, the `#eval`-style
evaluators and the two command elaborators.  The module system wants a
`CommandElab` to be `meta` (`Cannot add attribute … must be marked as
`meta``), and `meta section` is how a file that is meta THROUGHOUT says
so once. -/
meta section

namespace Ix.Kernel.BasisGen

open Lean Elab Command Term Meta

/-! ## Quoting a `Ix.Kernel` value back into a `Lean.Expr`

The annotation runs on real `Ix.Kernel` values; the definition it splices
must carry them as terms.  These are the structural quoters — one
constructor application each, with no sharing (the pins are small; the
biggest is `Quot.lift`'s rule, a few hundred nodes). -/

private def qBool : Bool → Lean.Expr
  | true => mkConst ``Bool.true
  | false => mkConst ``Bool.false

private def qList (ty : Lean.Expr) (xs : List Lean.Expr) : Lean.Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [Lean.Level.zero]) ty x acc)
    (mkApp (mkConst ``List.nil [Lean.Level.zero]) ty)

private def levelParamTy : Lean.Expr := mkConst ``Ix.Kernel.LevelParam
private def levelTy : Lean.Expr := mkConst ``Ix.Kernel.Level
/-- The kernel types at the mode `mdE` (a `Lean.Expr` of type `Mode`). -/
private def exprTy (mdE : Lean.Expr) : Lean.Expr := mkApp (mkConst ``Ix.Kernel.Expr) mdE
private def keyTy (mdE : Lean.Expr) : Lean.Expr := mkApp (mkConst ``Ix.Kernel.Key) mdE
private def recRuleTy (mdE : Lean.Expr) : Lean.Expr := mkApp (mkConst ``Ix.Kernel.RecRule) mdE
private def constantInfoTy (mdE : Lean.Expr) : Lean.Expr :=
  mkApp (mkConst ``Ix.Kernel.ConstantInfo) mdE
private def constantValTy (mdE : Lean.Expr) : Lean.Expr :=
  mkApp (mkConst ``Ix.Kernel.ConstantVal) mdE
private def modeTy : Lean.Expr := mkConst ``Ix.Kernel.Mode
private def anonE : Lean.Expr := mkConst ``Ix.Kernel.Mode.anon

/-- A role's constructor (`Role` derives `Repr` with the constructor's full
name). -/
private def qRole (r : Ix.Kernel.Role) : Lean.Expr := mkConst (reprStr r).toName

/-- A derived shape, constructor by constructor. -/
private def qDerived : Ix.Kernel.Derived → Lean.Expr
  | .model => mkConst ``Ix.Kernel.Derived.model
  | .impl => mkConst ``Ix.Kernel.Derived.impl
  | .tag => mkConst ``Ix.Kernel.Derived.tag
  | .auxFamily => mkConst ``Ix.Kernel.Derived.auxFamily
  | .member k => mkApp (mkConst ``Ix.Kernel.Derived.member) (mkRawNatLit k)
  | .ctor j => mkApp (mkConst ``Ix.Kernel.Derived.ctor) (mkRawNatLit j)
  | .recursor => mkConst ``Ix.Kernel.Derived.recursor
  | .iota j => mkApp (mkConst ``Ix.Kernel.Derived.iota) (mkRawNatLit j)
  | .eta => mkConst ``Ix.Kernel.Derived.eta
  | .unitlike => mkConst ``Ix.Kernel.Derived.unitlike
  | .projModel i => mkApp (mkConst ``Ix.Kernel.Derived.projModel) (mkRawNatLit i)
  | .projIota => mkConst ``Ix.Kernel.Derived.projIota
  | .projFn i => mkApp (mkConst ``Ix.Kernel.Derived.projFn) (mkRawNatLit i)
  | .projTable => mkConst ``Ix.Kernel.Derived.projTable
  | .pack j => mkApp (mkConst ``Ix.Kernel.Derived.pack) (mkRawNatLit j)
  | .unpack j => mkApp (mkConst ``Ix.Kernel.Derived.unpack) (mkRawNatLit j)
  | .unpackPack j => mkApp (mkConst ``Ix.Kernel.Derived.unpackPack) (mkRawNatLit j)
  | .packUnpack j => mkApp (mkConst ``Ix.Kernel.Derived.packUnpack) (mkRawNatLit j)
  | .congrPack j => mkApp (mkConst ``Ix.Kernel.Derived.congrPack) (mkRawNatLit j)
  | .unpackAll => mkConst ``Ix.Kernel.Derived.unpackAll
  | .packUnpackAll => mkConst ``Ix.Kernel.Derived.packUnpackAll
  | .implRec => mkConst ``Ix.Kernel.Derived.implRec

/-- A key that names no input constant: a role key, or one derived from it.
The generated declarations hold only such keys (`pinnedOnly`), which mean the
same in every mode; an input key's id is an address in `.anon` and has no
counterpart in `.source`. -/
private def roleBased : Ix.Kernel.Key .anon → Bool
  | .id _ => false
  | .role _ => true
  | .aux k _ => roleBased k

private def roleBasedExpr : Ix.Kernel.Expr .anon → Bool
  | .const n _ => roleBased n
  | .proj s _ e => roleBased s && roleBasedExpr e
  | .fvar _ ty => roleBasedExpr ty
  | .app f a | .lam f a _ | .forallE f a _ => roleBasedExpr f && roleBasedExpr a
  | .letE t v b _ => roleBasedExpr t && roleBasedExpr v && roleBasedExpr b
  | _ => true

private def roleBasedVal (cv : Ix.Kernel.ConstantVal .anon) : Bool :=
  roleBased cv.name && roleBasedExpr cv.type

/-- Every key of a generated declaration is role-based. -/
private def pinnedOnly : Ix.Kernel.ConstantInfo .anon → Bool
  | .axiomInfo cv | .ctorInfo cv _ _ => roleBasedVal cv
  | .defnInfo cv v _ | .thmInfo cv v => roleBasedVal cv && roleBasedExpr v
  | .indInfo cv caps => roleBasedVal cv && caps.etaCtor.all roleBased
  | .recInfo cv _ _ rules => roleBasedVal cv && rules.all fun r =>
      roleBased r.ctor && roleBasedExpr r.rhs && match r.fire with
        | .nested _ pins => pins.all roleBasedExpr
        | _ => true
  | .projInfo _ => false

/-- A key at mode `mdE`: a role key as `roleKey`, a derived key as `auxKey`.
An input key does not occur (`pinnedOnly` is checked first); it is quoted as
the unbound name `inputKey`, which no declaration elaborates with. -/
private def qKey (mdE : Lean.Expr) : Ix.Kernel.Key .anon → Lean.Expr
  | .id _ => mkConst `inputKey
  | .role r => mkApp2 (mkConst ``Ix.Kernel.roleKey) mdE (qRole r)
  | .aux k d => mkApp3 (mkConst ``Ix.Kernel.auxKey) mdE (qKey mdE k) (qDerived d)

private def qLevelParams (ps : List Ix.Kernel.LevelParam) : Lean.Expr :=
  qList levelParamTy (ps.map mkRawNatLit)

private def qLevel : Ix.Kernel.Level → Lean.Expr
  | .zero => mkConst ``Ix.Kernel.Level.zero
  | .succ a => mkApp (mkConst ``Ix.Kernel.Level.succ) (qLevel a)
  | .max a b => mkApp2 (mkConst ``Ix.Kernel.Level.max) (qLevel a) (qLevel b)
  | .imax a b => mkApp2 (mkConst ``Ix.Kernel.Level.imax) (qLevel a) (qLevel b)
  | .param n => mkApp (mkConst ``Ix.Kernel.Level.param) (mkRawNatLit n)

private def qLevels (us : List Ix.Kernel.Level) : Lean.Expr :=
  qList levelTy (us.map qLevel)

/-- The zero-ness datum through its public API (the representation is
`private` to `IxC/Kernel/PropWhen.lean`): `never`, or `ifAllZero`
of its parameter list. -/
private def qPropWhen (pw : Ix.Kernel.PropWhen) : Lean.Expr :=
  match pw.toList? with
  | none => mkConst ``Ix.Kernel.PropWhen.never
  | some ps => mkApp (mkConst ``Ix.Kernel.PropWhen.ifAllZero) (qLevelParams ps)

private def qUses : Ixon.Uses → Lean.Expr
  | .erased => mkConst ``Ixon.Uses.erased
  | .linear => mkConst ``Ixon.Uses.linear
  | .affine => mkConst ``Ixon.Uses.affine
  | .many => mkConst ``Ixon.Uses.many

private def qValueContract (v : Ixon.ValueContract) : Lean.Expr :=
  mkApp2 (mkConst ``Ixon.ValueContract.mk)
    (match v.owned with
      | .unique => mkConst ``Ixon.Owned.unique
      | .shared => mkConst ``Ixon.Owned.shared)
    (match v.locality with
      | .unrestricted => mkConst ``Ixon.Locality.unrestricted
      | .local => mkConst ``Ixon.Locality.local)

/-- Defaults are quoted as the default constants, so a quoted pin is the
same term `{ pw := … }` elaborates to. -/
private def qBinderContract (c : Ixon.BinderContract) : Lean.Expr :=
  if c == .many then mkConst ``Ixon.BinderContract.many else
    mkApp2 (mkConst ``Ixon.BinderContract.mk) (qUses c.uses) (qValueContract c.value)

/-- A let's metadata: its contract, field by field. -/
private def qLetMeta (l : Ix.Kernel.LetMeta) : Lean.Expr :=
  mkApp (mkConst ``Ix.Kernel.LetMeta.mk)
    (mkApp3 (mkConst ``Ixon.LetContract.mk) (qBool l.contract.nonDep)
      (match l.contract.kind with
        | .value => mkConst ``Ixon.LetKind.value
        | .borrowShared => mkConst ``Ixon.LetKind.borrowShared)
      (qBinderContract l.contract.binder))

private def qBinderMeta (m : Ix.Kernel.BinderMeta) : Lean.Expr :=
  mkApp3 (mkConst ``Ix.Kernel.BinderMeta.mk) (qPropWhen m.pw) (qBinderContract m.contract)
    (if m.result == .shared then mkConst ``Ixon.ValueContract.shared else
      qValueContract m.result)

private def qLiteral : Ix.Kernel.Literal → Lean.Expr
  | .natVal n => mkApp (mkConst ``Ix.Kernel.Literal.natVal) (mkRawNatLit n)
  | .strVal s => mkApp (mkConst ``Ix.Kernel.Literal.strVal) (mkStrLit s)

private def qExpr (mdE : Lean.Expr) : Ix.Kernel.Expr .anon → Lean.Expr
  | .bvar i => mkApp2 (mkConst ``Ix.Kernel.Expr.bvar) mdE (mkRawNatLit i)
  | .fvar i ty => mkApp3 (mkConst ``Ix.Kernel.Expr.fvar) mdE (mkRawNatLit i) (qExpr mdE ty)
  | .sort u => mkApp2 (mkConst ``Ix.Kernel.Expr.sort) mdE (qLevel u)
  | .const n us => mkApp3 (mkConst ``Ix.Kernel.Expr.const) mdE (qKey mdE n) (qLevels us)
  | .app f a => mkApp3 (mkConst ``Ix.Kernel.Expr.app) mdE (qExpr mdE f) (qExpr mdE a)
  | .lam ty b m =>
    mkApp4 (mkConst ``Ix.Kernel.Expr.lam) mdE (qExpr mdE ty) (qExpr mdE b) (qBinderMeta m)
  | .forallE ty b m =>
    mkApp4 (mkConst ``Ix.Kernel.Expr.forallE) mdE (qExpr mdE ty) (qExpr mdE b) (qBinderMeta m)
  | .letE ty v b l =>
    mkApp5 (mkConst ``Ix.Kernel.Expr.letE) mdE (qExpr mdE ty) (qExpr mdE v) (qExpr mdE b)
      (qLetMeta l)
  | .lit l => mkApp2 (mkConst ``Ix.Kernel.Expr.lit) mdE (qLiteral l)
  | .proj s i e =>
    mkApp4 (mkConst ``Ix.Kernel.Expr.proj) mdE (qKey mdE s) (mkRawNatLit i) (qExpr mdE e)

private def qConstantVal (mdE : Lean.Expr) (cv : Ix.Kernel.ConstantVal .anon) : Lean.Expr :=
  mkApp4 (mkConst ``Ix.Kernel.ConstantVal.mk) mdE (qKey mdE cv.name)
    (qLevelParams cv.levelParams) (qExpr mdE cv.type)

private def qRecRuleFire (mdE : Lean.Expr) : Ix.Kernel.RecRuleFire .anon → Lean.Expr
  | .inert => mkApp (mkConst ``Ix.Kernel.RecRuleFire.inert) mdE
  | .plain => mkApp (mkConst ``Ix.Kernel.RecRuleFire.plain) mdE
  | .nested lvls pins =>
    mkApp3 (mkConst ``Ix.Kernel.RecRuleFire.nested) mdE (qLevels lvls)
      (qList (exprTy mdE) (pins.map (qExpr mdE)))

private def qRecRule (mdE : Lean.Expr) (r : Ix.Kernel.RecRule .anon) : Lean.Expr :=
  mkAppN (mkConst ``Ix.Kernel.RecRule.mk)
    #[mdE, qKey mdE r.ctor, mkRawNatLit r.nfields, mkRawNatLit r.ctorParams,
      qRecRuleFire mdE r.fire, qExpr mdE r.rhs, qBool r.k, qBool r.eta,
      qBool r.paramsBlind]

private def qOptionKey (mdE : Lean.Expr) : Option (Ix.Kernel.Key .anon) → Lean.Expr
  | some k => mkApp2 (mkConst ``Option.some [Lean.Level.zero]) (keyTy mdE) (qKey mdE k)
  | none => mkApp (mkConst ``Option.none [Lean.Level.zero]) (keyTy mdE)

private def qIndCaps (mdE : Lean.Expr) (c : Ix.Kernel.IndCaps .anon) : Lean.Expr :=
  mkAppN (mkConst ``Ix.Kernel.IndCaps.mk)
    #[mdE, qBool c.eta, qOptionKey mdE c.etaCtor, mkRawNatLit c.etaParams,
      mkRawNatLit c.etaFields, qBool c.unitlike, mkRawNatLit c.unitParams,
      qBool c.ruleK, qPropWhen c.sortZ]

private def qReducibilityHint : Ix.Kernel.ReducibilityHint → Lean.Expr
  | .«opaque» => mkConst ``Ix.Kernel.ReducibilityHint.«opaque»
  | .«abbrev» => mkConst ``Ix.Kernel.ReducibilityHint.«abbrev»
  | .regular h => mkApp (mkConst ``Ix.Kernel.ReducibilityHint.regular) (mkRawNatLit h)

private def qConstantInfo (mdE : Lean.Expr) (ci : Ix.Kernel.ConstantInfo .anon) : CoreM Lean.Expr := do
  if let .projInfo _ := ci then
    throwError "#annotate_basis: a projection table is not a pinnable declaration"
  unless pinnedOnly ci do
    throwError "#annotate_basis: a generated declaration names an input constant"
  match ci with
  | .axiomInfo cv =>
    pure (mkApp2 (mkConst ``Ix.Kernel.ConstantInfo.axiomInfo) mdE (qConstantVal mdE cv))
  | .defnInfo cv v h =>
    pure (mkApp4 (mkConst ``Ix.Kernel.ConstantInfo.defnInfo) mdE (qConstantVal mdE cv)
      (qExpr mdE v) (qReducibilityHint h))
  | .thmInfo cv v =>
    pure (mkApp3 (mkConst ``Ix.Kernel.ConstantInfo.thmInfo) mdE (qConstantVal mdE cv)
      (qExpr mdE v))
  | .indInfo cv caps =>
    pure (mkApp3 (mkConst ``Ix.Kernel.ConstantInfo.indInfo) mdE (qConstantVal mdE cv)
      (qIndCaps mdE caps))
  | .ctorInfo cv nP nF =>
    pure (mkApp4 (mkConst ``Ix.Kernel.ConstantInfo.ctorInfo) mdE (qConstantVal mdE cv)
      (mkRawNatLit nP) (mkRawNatLit nF))
  | .recInfo cv mI rP rules =>
    pure (mkAppN (mkConst ``Ix.Kernel.ConstantInfo.recInfo)
      #[mdE, qConstantVal mdE cv, mkRawNatLit mI, mkRawNatLit rP,
        qList (recRuleTy mdE) (rules.map (qRecRule mdE))])
  | .projInfo _ =>
    throwError "#annotate_basis: a projection table is not a pinnable declaration"

/-! ## The recipe -/

/-- Annotate one raw `ConstantInfo` over `env`, exactly as the basis
install does: the type first, then — for a recursor — the
install-computed rule fields (`ctorParams` off the stored constructor,
`fire` off `Expr.recRulePlain`) and the rules' right-hand sides over
the environment extended with the recursor itself. -/
def annotateInfo (env : Ix.Kernel.Env .anon) (ci : Ix.Kernel.ConstantInfo .anon) :
    Ix.Kernel.CheckM (Ix.Kernel.ConstantInfo .anon) := do
  let cv := ci.toConstantVal
  let ty' ← Ix.Kernel.annotateCore .verified env Ix.Kernel.checkFuel 0 cv.type
  let cv' : Ix.Kernel.ConstantVal .anon := { cv with type := ty' }
  match ci with
  | .indInfo _ caps => return .indInfo cv' caps
  | .ctorInfo _ nP nF => return .ctorInfo cv' nP nF
  | .axiomInfo _ => return .axiomInfo cv'
  | .defnInfo _ v h => return .defnInfo cv' v h
  | .thmInfo _ v => return .thmInfo cv' v
  | .projInfo tbl => return .projInfo tbl
  | .recInfo _ mI rP rules =>
    let rules := rules.map fun r =>
      let cnP := match env.find? r.ctor with
        | some (.ctorInfo _ nP _) => nP
        | _ => 0
      Ix.Kernel.recRuleBits env.find? cv'.name
        { r with ctorParams := cnP,
                 fire := if Ix.Kernel.Expr.recRulePlain ty' mI rP cnP then .plain else .inert,
                 paramsBlind := true }
    let envSelf : Ix.Kernel.Env .anon := ⟨.recInfo cv' mI rP rules :: env.consts⟩
    let mut out : List (Ix.Kernel.RecRule .anon) := []
    for r in rules do
      let rhs' ← Ix.Kernel.annotateCore .verified envSelf Ix.Kernel.checkFuel 0 r.rhs
      out := out ++ [{ r with rhs := rhs' }]
    return .recInfo cv' mI rP out

/-- Annotate one raw `ConstantVal` pin's type over `env`. -/
def annotateVal (env : Ix.Kernel.Env .anon) (cv : Ix.Kernel.ConstantVal .anon) :
    Ix.Kernel.CheckM (Ix.Kernel.ConstantVal .anon) := do
  let ty' ← Ix.Kernel.annotateCore .verified env Ix.Kernel.checkFuel 0 cv.type
  return { cv with type := ty' }

/-! ## Evaluating the raw pins

`Lean.Elab.Term.evalTerm` is `unsafe`; the safe wrappers below are the
standard `@[implemented_by]` pairing (their own bodies are never run —
`implemented_by` replaces the compiled code). -/

private unsafe def evalInfoUnsafe (stx : Syntax) : TermElabM (Ix.Kernel.ConstantInfo .anon) :=
  Term.evalTerm (Ix.Kernel.ConstantInfo .anon) (constantInfoTy anonE) stx

@[implemented_by evalInfoUnsafe]
private def evalInfo (_stx : Syntax) : TermElabM (Ix.Kernel.ConstantInfo .anon) :=
  throwError "unreachable"

private unsafe def evalValUnsafe (stx : Syntax) : TermElabM (Ix.Kernel.ConstantVal .anon) :=
  Term.evalTerm (Ix.Kernel.ConstantVal .anon) (constantValTy anonE) stx

@[implemented_by evalValUnsafe]
private def evalVal (_stx : Syntax) : TermElabM (Ix.Kernel.ConstantVal .anon) :=
  throwError "unreachable"

private unsafe def evalEnvUnsafe (stx : Syntax) : TermElabM (List (Ix.Kernel.ConstantInfo .anon)) :=
  Term.evalTerm (List (Ix.Kernel.ConstantInfo .anon))
    (mkApp (mkConst ``List [Lean.Level.zero]) (constantInfoTy anonE)) stx

@[implemented_by evalEnvUnsafe]
private def evalEnv (_stx : Syntax) : TermElabM (List (Ix.Kernel.ConstantInfo .anon)) :=
  throwError "unreachable"

/-! ## Splicing -/

/-- Define `declName : ∀ {md : Mode}, ty md := fun {md} => value` (kernel-checked,
then compiled), with the reducibility hint an ordinary `def` of the same body
would get. `value` mentions the mode as the loose bound variable `#0`: a pin
is closed over role keys, so the same term serves every mode. -/
private def splice (declName : Lean.Name) (ty : Lean.Expr → Lean.Expr) (value : Lean.Expr) :
    TermElabM Unit := do
  let ty := Lean.mkForall `md .implicit modeTy (ty (.bvar 0))
  let value := Lean.mkLambda `md .implicit modeTy value
  let hints : Lean.ReducibilityHints := .regular (getMaxHeight (← getEnv) value + 1)
  let decl : Lean.Declaration := .defnDecl
    (← mkDefinitionValInferringUnsafe declName [] ty value hints)
  -- MODULE SYSTEM (task #231).  A spliced constant must land in the *public*
  -- scope with its body exposed, exactly as the `def` it replaces would:
  -- `addDecl` otherwise derives an opaque `axiom` presentation for the public
  -- view (`Lean/AddDecl.lean`), and downstream `rfl`/`decide` proofs over the
  -- pins — every `Model/Basis*` consumer — would lose the value they read.
  withExporting (isExporting := true) do
    addDecl decl (forceExpose := true)
  compileDecl decl

/-! ## The commands -/

/-- One `| name := rawTerm` entry.  The leading `|` is what keeps the
entries from being parsed as one applied term. -/
syntax annotEntry := " | " ident " := " term

/-- `#annotate_basis over <env> | nameA := nameRaw ...` — annotate raw
`ConstantInfo` pins in order, each over the environment of `<env>`
extended by the ones already annotated, and define the results. -/
syntax (name := annotateBasisCmd)
  "#annotate_basis" " over " term (annotEntry)+ : command

/-- `#annotate_pins over <env> | nameA := nameRaw ...` — annotate raw
`ConstantVal` pins, each over the *same* environment, and define the
results. -/
syntax (name := annotatePinsCmd)
  "#annotate_pins" " over " term (annotEntry)+ : command

@[command_elab annotateBasisCmd]
def elabAnnotateBasis : CommandElab := fun stx => do
  let entries := stx[3].getArgs
  let mut consts : List (Ix.Kernel.ConstantInfo .anon) ←
    liftTermElabM (evalEnv stx[2])
  for e in entries do
    let id := e[1]
    let rawStx := e[3]
    let raw ← liftTermElabM (evalInfo rawStx)
    let ci ←
      match annotateInfo ⟨consts⟩ raw with
      | .ok ci => pure ci
      | .error err =>
        throwErrorAt rawStx
          "#annotate_basis: annotating {id.getId} failed: {toString err}"
    liftTermElabM do
      splice ((← getCurrNamespace) ++ id.getId) constantInfoTy (← qConstantInfo (.bvar 0) ci)
    consts := ci :: consts

@[command_elab annotatePinsCmd]
def elabAnnotatePins : CommandElab := fun stx => do
  let entries := stx[3].getArgs
  let consts : List (Ix.Kernel.ConstantInfo .anon) ← liftTermElabM (evalEnv stx[2])
  for e in entries do
    let id := e[1]
    let rawStx := e[3]
    let raw ← liftTermElabM (evalVal rawStx)
    let cv ←
      match annotateVal ⟨consts⟩ raw with
      | .ok cv => pure cv
      | .error err =>
        throwErrorAt rawStx
          "#annotate_pins: annotating {id.getId} failed: {toString err}"
    liftTermElabM do
      unless roleBasedVal cv do
        throwErrorAt rawStx "#annotate_pins: {id.getId} names an input constant"
      splice ((← getCurrNamespace) ++ id.getId) constantValTy (qConstantVal (.bvar 0) cv)

end Ix.Kernel.BasisGen

end  -- meta section
