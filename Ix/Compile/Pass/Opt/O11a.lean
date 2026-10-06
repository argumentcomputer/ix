/- # O11a: Lean's mutual `_sizeOf_N` of a split member, in the instance form

**Status (A6f): definitional, run.** The `rfl` the plan asks for holds
under the three kernels (below), so O11a is not proof-justified. Its output
references `T._sizeOf_inst` (and `SizeOf.sizeOf`) from `_sizeOf_N`,
references the input constant does not have; the scheduler orders blocks by
the input's reference graph, so without help `_sizeOf_N` could compile
before the instance (measured by A4: `missingConstant …IneqCnstr._sizeOf_inst`),
and gating the pass on "already compiled" would make the bytes depend on the
schedule (§6). `sizeOfEdges` below adds exactly those references to the
scheduler's input (the condensation's block dependencies, `addSizeOfEdges`,
called by the Lean pipeline after `CondenseM.run`), so the instance is
always compiled first and O11a runs in `Engine.passes`, before O2.

## Contract
Input: an occurrence `r.{us} ps ms mins is t e` of a Lean recursor `r` of a
split block with no collapsed class (O2's pattern) that is **the recursion of
Lean's `sizeOf` family**: for every field of a constructor of `r`'s component
`c` that is recursive into another component, of type `T` (a member of the
block with no parameters and no indices, the field not reflexive), Lean's
instance `T._sizeOf_inst` is `@SizeOf.mk.{l} T T._sizeOf_k` (or its η-expansion `fun t => T._sizeOf_k t`) and
`T._sizeOf_k := λ t. T.rec ps ms mins t` with **the occurrence's own**
`ps ms mins` (α-equal): the occurrence is one of the block's mutual
`_sizeOf_N` (Lean's `mkSizeOfFns` passes one telescope to every member's
recursor), and the relocated recursion into `T` *is* `T`'s `sizeOf`.

Output: as O2, `ρ.{ℓs[us]} ps (ms ∘ σ) mins″ is t e`, except that the Ix
minor of a constructor with such a field is the user's minor `mⱼ = λ fs ihs.
b` with the binder of every IH over a cross field `f : T` **removed** and
the variable replaced by `@SizeOf.sizeOf.{l} T T._sizeOf_inst f`:
`λ fs ihsᶜ. b[ih_f := sizeOf f]`, its binders `mⱼ`'s own. This is the minor
Lean's `mkSizeOfFns` builds when the components are declared separately (a
cross field is then not recursive, and its size comes from the instance), so
the occurrence becomes the separately declared component's `_sizeOf`: the
canonical term.

## Faithfulness (definitional, δ, β, projection; no induction)
From O2's output (definitionally the baseline) the IH argument for `f` is the
relocated call `ρ_T (ms ∘ σ_T) (mins ∘ σ′_T) f`, the engine's rewrite of
`T.rec ps ms mins f`, and the adapted minor is `λ fs ihsᶜ. mⱼ fs ih⃗`.
`@SizeOf.sizeOf T T._sizeOf_inst f ≡δ (SizeOf.mk T._sizeOf_k).1 f ≡proj
T._sizeOf_k f ≡δβ T.rec ps ms mins f` (the side condition), and the
relocated call is that recursor occurrence rewritten (a definitional pass).
So replacing the IH argument by the instance form is a conversion, and the
β-redex `mⱼ fs ih⃗` contracted at the replaced positions gives `b[ih_f :=
sizeOf f]` under `mⱼ`'s own binders: one β per binder. Measured: one `rfl`
per member of `Linear.EqCnstr` (`(fun t => @sizeOf Orig.X Orig.X._sizeOf_inst
t) = (fun t => @sizeOf Twin.X Twin.X._sizeOf_inst t)`, the library twins of
`Oracle.Lib`) is accepted by `Ix.Tc`, the Rust kernel and the certified
checker (`pass3` suite, twins unit, line `o11a`).

## Canonicity
The output is Lean's separately declared `_sizeOf` of the component: it
depends on the component's canonical recursor (through O2), the user's
minors (which Lean's `mkSizeOfFns` builds from the constructors alone) and
the instance names' addresses, which are the components' own `_sizeOf`
instances. Two presentations (the mutual block, the components declared
separately, any member order) give the same term.

## Side condition and fallback
Decidable: O2's side condition; every cross field's type is a block member
with no parameters and no indices, not reflexive; its instance and its
`_sizeOf` function have the shapes above, with the occurrence's telescope
(α-equality); every adapted minor is a syntactic λ over its fields and IHs.
Otherwise O11a declines and O2 runs (the relocated form, faithful). When the
occurrence is the recursion of Lean's `sizeOf` family of its block (its
telescope is that of an `all₀._sizeOf_N` of the input) and has a cross
field, every such decline is recorded with the failing condition as its
cause (`O11a.declineCause?`, M1-h): a parametric, indexed or
universe-polymorphic cross target, a reflexive or indexed cross field, an
instance or size function not of Lean's shape, a recursor telescope that is
not the occurrence's, a minor that is not a λ over its fields and IHs, and
(below) an absent instance. An occurrence of a split block's recursor that
is not that recursion (a user's function) is O2's and canonical: nothing is
recorded.

**A reference the input does not have** (design document §6.3, the four
obligations of a pass whose output adds a reference):
1. *visible*: `T._sizeOf_inst` is an auxiliary of the same Lean declaration
   as `all₀._sizeOf_N` (one logical unit, §6.3's table of allowed cases);
2. *declared*: `sizeOfEdges` gives the scheduler the edge
   `all₀._sizeOf_N → T._sizeOf_inst` when the instance is in the input, and
   every closure producer carries it: the selected producers carry the whole
   unit of every block they reach (`Lean.unitMembers`, M1-d) and, before
   that, the family's instances (`Lean.compilerSupportOf`);
3. *acyclic*: argued in the section on the scheduling edges below;
4. *absent*: when the instance is absent from the input (a hand-built input,
   or a closure that did not carry the unit), O11a declines, O2 gives the
   relocated-recursor form, and the decline is **recorded**:
   `O11a.declineCause?` names the missing instances and the driver puts the
   constant in the compile's non-canonical set
   (`CompileEnv.p3NonCanonical`). It never guesses an address and never
   keeps the relocated form without a record. (Before M1-c the decline was
   silent: `sizeOfInstance?` failed, O11a returned `none`, O2 fired, and
   nothing recorded that the canonical form was not reached.)

## Non-canonical set and evidence
None on a closure that carries the unit. On an input without
`T._sizeOf_inst`: the `_sizeOf_N` with the cause above
(`Tests/Ix/Compile/O11aDecline.lean`: the withheld instance declines with
the record, the valid neighbour with the instance rewrites).
Library load: the 7 `Linear.EqCnstr._sizeOf_N`. Evidence: the twins
unit's `o11a` line (the `rfl`), the library twins `Oracle.Lib` Linear family
(Orig's `_sizeOf` instances equal Twin's with the switch on), the
`O2Split` fixture's `_sizeOf`.
-/
module
public import Ix.Compile.Pass.Opt.Core
public import Ix.Compile.Pass.Opt.O2
public import Ix.Compile.Pass.Opt.O5
public import Ix.Compile.Image.Expr
public import Ix.CondenseM
public section

namespace Ix.Compile.Pass.Opt

open Ix (Name Level Expr ConstantInfo RecursorVal)
open Ix.Compile.Canon (mkAppN getAppFnArgs)

def nSizeOfMk : Name := Ix.Compile.Image.leanName ``SizeOf.mk
def nSizeOf : Name := Ix.Compile.Image.leanName ``SizeOf.sizeOf

/-- The body under at most `k` leading λs. -/
def lamBody : Expr → Nat → Expr
  | .lam _ _ b _ _, k + 1 => lamBody b k
  | e, _ => e

/-- O11a's verdict while it reads an occurrence (M1-h): `.error none` when the
occurrence is not O11a's pattern (nothing to record), `.error (some c)` when
O11a declines because side condition `c` fails. `O11a.apply` keeps only the
success; `O11a.declineCause?` reads the cause. -/
abbrev O11aM := Except (Option String)

/-- Not O11a's pattern: decline with nothing to record. -/
def O11aM.pattern (x : Option α) : O11aM α :=
  match x with
  | some a => pure a
  | none => throw none

/-- A side condition: decline with `cause` when it fails. -/
def O11aM.side (x : Option α) (cause : String) : O11aM α :=
  match x with
  | some a => pure a
  | none => throw (some cause)

/-- A Boolean side condition. -/
def O11aM.need (b : Bool) (cause : String) : O11aM Unit :=
  if b then pure () else throw (some cause)

open O11aM in
/-- The checks on the cross target `T` itself (a block member with no
parameters, indices or universe parameters). -/
def sizeOfTargetE (env : OptEnv) (T : Name) : O11aM Unit := do
  let tv ← side (match env.const? T with | some (.inductInfo tv) => some tv | _ => none)
    s!"the cross target {T.pretty} is not an inductive type of the input"
  need (tv.numParams == 0) s!"the cross target {T.pretty} has {tv.numParams} parameter(s)"
  need (tv.numIndices == 0) s!"the cross target {T.pretty} has {tv.numIndices} index(es)"
  need tv.cnst.levelParams.isEmpty s!"the cross target {T.pretty} has universe parameters"

open O11aM in
/-- `T`'s `sizeOf` instance when it is `@SizeOf.mk.{l} T T._sizeOf_k` with
`T._sizeOf_k := λ t. T.rec tel t` and `tel` α-equal to `telescope`: the
instance's name and level; otherwise the failing side condition. -/
def sizeOfInstanceE (env : OptEnv) (T : Name) (telescope : Array Expr) : O11aM (Name × Level) := do
  sizeOfTargetE env T
  let inst := Name.mkStr T "_sizeOf_inst"
  let ici ← side (env.const? inst)
    s!"the size instance {inst.pretty} of a lower component is absent from the input"
  let iv ← side (match ici with | .defnInfo iv => some iv | _ => none)
    s!"the size instance {inst.pretty} is not a definition"
  need iv.cnst.levelParams.isEmpty s!"the size instance {inst.pretty} has universe parameters"
  let shape := s!"the size instance {inst.pretty} is not `@SizeOf.mk {T.pretty} k`"
  let (h, args) := getAppFnArgs iv.value
  let (mk, ls) ← side (match h with | .const mk ls _ => some (mk, ls) | _ => none) shape
  need (mk == nSizeOfMk && args.size == 2) shape
  let l ← side ls[0]? shape
  need (match args[0]! with | .const ty _ _ => ty == T | _ => false) shape
  -- `T._sizeOf_k` or its η-expansion `fun t => T._sizeOf_k t`
  let k ← side (match args[1]! with
    | .const k _ _ => some k
    | .lam _ _ (.app (.const k _ _) (.bvar 0 _) _) _ _ => some k
    | _ => none) shape
  let kshape := s!"the size function {k.pretty} of {inst.pretty} is not `λ t. {T.pretty}.rec … t`"
  let kv ← side (match env.const? k with | some (.defnInfo kv) => some kv | _ => none) kshape
  let body ← side (match kv.value with | .lam _ _ body _ _ => some body | _ => none) kshape
  let (rh, rargs) := getAppFnArgs body
  need (match rh with | .const rn _ _ => rn == Name.mkStr T "rec" | _ => false) kshape
  need (match rargs.back? with | some (.bvar 0 _) => true | _ => false) kshape
  let tel := s!"the recursor telescope of {k.pretty} is not the occurrence's (one mutual size family)"
  need (rargs.size == telescope.size + 1) tel
  for (x, y) in (rargs.extract 0 telescope.size).zip telescope do
    need (Ix.Compile.Image.alphaEq x y) tel
  return (inst, l)

/-- `T`'s `sizeOf` instance (`sizeOfInstanceE`, the success only). -/
def sizeOfInstance? (env : OptEnv) (T : Name) (telescope : Array Expr) : Option (Name × Level) :=
  (sizeOfInstanceE env T telescope).toOption

open O11aM in
/-- The instance-form minor of Lean minor `j` (`some none` when no field of
its constructor is recursive into another component). -/
def sizeOfMinorWith (env : OptEnv) (inst? : Name → Array Expr → O11aM (Name × Level))
    (rv : RecursorVal) (inBlock : Array Bool) (us : Array Level)
    (ps ms mins : Array Expr) (j : Nat) : O11aM (Option Expr) := do
  let ienv := env.ienv
  let auxSigs := Ix.AuxGen.auxMotiveSigs rv us ps ms ienv
  let unread := s!"the constructor and minor type of minor {j} cannot be read"
  let (_, ctor) ← side (Ix.AuxGen.sourceCtorForMinor j rv ienv auxSigs) unread
  let minorTy ← side (Ix.AuxGen.sourceMinorType rv us ps ms mins j) unread
  let (fieldDecls, _, _) ← side (Ix.AuxGen.peelBinders minorTy ctor.numFields "split_field" 0) unread
  let mut recFields : Array (Nat × Ix.AuxGen.SourceRecTarget) := #[]
  for (decl, fieldIdx) in fieldDecls.zipIdx do
    if let some target := Ix.AuxGen.findSourceRecTarget decl.domain rv.all
        ps ienv "split_xs" fieldIdx auxSigs then
      recFields := recFields.push (fieldIdx, target)
  if !recFields.any (fun (_, t) => !(inBlock.getD t.sourcePos false)) then
    return none
  -- the user's minor, opened over its fields and IHs
  let m ← side mins[j]? unread
  let nb := ctor.numFields + recFields.size
  let telescope := ps ++ ms ++ mins
  let mut cur := m
  let mut decls : Array Ix.AuxGen.LocalDecl := #[]
  let mut fvars : Array Expr := #[]
  for i in [0:nb] do
    let (bn, dom, b, bi) ← side (match cur with
      | .lam bn dom b bi _ => some (bn, dom, b, bi)
      | _ => none) s!"minor {j} is not a λ over its {ctor.numFields} field(s) and \
        {recFields.size} induction hypothesis(es)"
    let (fvName, fv) := Ix.AuxGen.freshFVar "o11a" i
    if i < ctor.numFields then
      decls := decls.push { fvarName := fvName, binderName := bn, domain := dom, info := bi }
      fvars := fvars.push fv
      cur := Ix.AuxGen.instantiate1 b fv
    else
      let (fieldIdx, target) := recFields[i - ctor.numFields]!
      if inBlock.getD target.sourcePos false then
        decls := decls.push { fvarName := fvName, binderName := bn, domain := dom, info := bi }
        cur := Ix.AuxGen.instantiate1 b fv
      else
        let T ← side rv.all[target.sourcePos]? unread
        need target.xsFvars.isEmpty s!"field {fieldIdx} of minor {j} is reflexive (a function \
          into the cross target {T.pretty})"
        need target.idxArgs.isEmpty s!"field {fieldIdx} of minor {j} has index arguments \
          (its cross target {T.pretty} is indexed)"
        let (inst, l) ← inst? T telescope
        let field ← side fvars[fieldIdx]? unread
        let sz := mkAppN (Expr.mkConst nSizeOf #[l])
          #[Expr.mkConst T #[], Expr.mkConst inst #[], field]
        cur := Ix.AuxGen.instantiate1 b sz
  return some (Ix.AuxGen.mkLambda cur decls)

open O11aM in
/-- O11a at an occurrence with the instance lookup `inst?`: the rewrite, or
why not (`O11aM`). O2's pattern failing is `.error none`. -/
def O11a.applyWithE (env : OptEnv) (inst? : Name → Array Expr → O11aM (Name × Level))
    (o : Occ) : O11aM Expr := do
  let (k, r) ← pattern (classify o.head)
  if k != .kRec then throw none
  let b ← pattern (env.blockOf o.head)
  if !b.change.split || b.change.collapse then throw none
  let s ← pattern (b.shapes.get? r)
  let rv ← pattern (match env.const? r with | some (.recInfo rv) => some rv | _ => none)
  let n ← pattern (standardTelescope env s .kRec o.head)
  if o.args.size < n then throw none
  let ls ← pattern (O5.levels s o.us)
  let a := o.args
  let ps := a.extract 0 s.np
  let ms := a.extract s.np (s.np + s.nm)
  let mins := a.extract (s.np + s.nm) (s.np + s.nm + s.nmin)
  let tail := a.extract (s.np + s.nm + s.nmin) n
  let inBlock : Array Bool := (Array.range s.nm).map s.motiveSrc.contains
  let ms' ← pattern (pick ms s.motiveSrc)
  let mut mins' : Array Expr := #[]
  let mut any := false
  for (src?, t) in s.minorSrc.zip s.minorTerms do
    let j ← match src? with
      | some j => pure j
      | none => pattern (wrappedMinorSrc s.arity s.np s.nm s.nmin t)
    match ← sizeOfMinorWith env inst? rv inBlock o.us ps ms mins j with
    | some w =>
      need src?.isNone s!"minor {j} has a cross field but O2 passes it unadapted"
      any := true
      mins' := mins'.push w
    | none => mins' := mins'.push (← pattern mins[j]?)
  -- no cross field into another component: O2's output is already the
  -- separately declared component's term
  if !any then throw none
  return mkAppN (Expr.mkConst s.ixRec ls) (ps ++ ms' ++ mins' ++ tail ++ a.extract n a.size)

def O11a.applyWith (env : OptEnv) (inst? : Name → Array Expr → O11aM (Name × Level))
    (o : Occ) : Option Expr :=
  (O11a.applyWithE env inst? o).toOption

/-- O11a at an occurrence: the instances are read from the input
(`sizeOfInstanceE`). -/
def O11a.apply (env : OptEnv) (o : Occ) : Option Expr :=
  O11a.applyWith env (sizeOfInstanceE env) o

/-- The instance lookup of `declineCause?`: as `sizeOfInstanceE`, except that
an instance `T._sizeOf_inst` **absent from the input** (for a cross target
`T` of the shape O11a needs: a member with no parameters, indices or
universe parameters) is assumed, under its own name. Used only to decide
whether the absence is what made O11a decline; its output is never used. -/
def sizeOfInstanceAssumingAbsent (env : OptEnv) (T : Name) (telescope : Array Expr) :
    O11aM (Name × Level) := do
  sizeOfTargetE env T
  let inst := Name.mkStr T "_sizeOf_inst"
  match env.const? inst with
  | none => pure (inst, Level.mkZero)
  | some _ => sizeOfInstanceE env T telescope

/-- The occurrence is **the recursion of Lean's `sizeOf` family** of its
block: its telescope (parameters, motives, minors: the first `k` arguments)
is α-equal to the one the value of some `all₀._sizeOf_N` of the input
applies its recursor to (Lean's `mkSizeOfFns` passes one telescope to every
member's recursor). This is what makes a decline of O11a a non-canonical
outcome: any other occurrence of a split block's recursor (a user's
function) is O2's, whose output is already canonical. Read from the input's
own `_sizeOf_N` constants only (the block's unit, §6.3). -/
def isSizeOfOccurrence (env : OptEnv) (rv : RecursorVal) (o : Occ) (k : Nat) : Bool := Id.run do
  let some all₀ := rv.all[0]? | return false
  let some (.inductInfo v) := env.const? all₀ | return false
  if o.args.size < k then return false
  for i in [1:v.all.size + v.numNested + 1] do
    let some (.defnInfo dv) := env.const? (Name.mkStr all₀ s!"_sizeOf_{i}") | continue
    let (h, args) := getAppFnArgs (lamBody dv.value 64)
    let .const _ _ _ := h | continue
    if args.size < k then continue
    if (List.range k).all fun j => Ix.Compile.Image.alphaEq args[j]! o.args[j]! then
      return true
  return false

/-- **The recorded decline** (design document §6.3; plan decision 1:
non-canonical cases are emitted and recorded with a cause). At an occurrence
that is the recursion of Lean's `sizeOf` family of a split block
(`isSizeOfOccurrence`) and has a cross field into a lower component, O11a
either fires or declines; when it declines, O2 gives the relocated-recursor
form (faithful, not the separately declared components' term), and this
returns the cause, which the driver records with the constant in the
compile's non-canonical set (`CompileEnv.p3NonCanonical`). Never silent.

The causes: one or more size instances `T._sizeOf_inst` its output would
reference are absent from the input (obligation 4 of a pass whose output
adds a reference: a closure that did not carry the unit, or a hand-built
input; the cause names every missing instance); otherwise the side condition
that failed (the cross target has parameters, indices or universe
parameters; the field is reflexive or has index arguments; the instance or
its size function does not have Lean's shape; their recursor telescope is
not the occurrence's; a minor is not a λ over its fields and IHs). A failing
side condition takes precedence over absence (O11a would decline with the
instances present too).

`none` when O11a fires, when the occurrence is not O2's pattern, when no
minor has a cross field (O2's output is already canonical), and when the
occurrence is not the `sizeOf` recursion. -/
def O11a.declineCause? (env : OptEnv) (o : Occ) : Option String := do
  let cause ← match O11a.applyWithE env (sizeOfInstanceE env) o with
    | .ok _ | .error none => none
    | .error (some c) => some c
  let (_, r) ← classify o.head
  let b ← env.blockOf o.head
  let s ← b.shapes.get? r
  let some (.recInfo rv) := env.const? r | none
  if !isSizeOfOccurrence env rv o (s.np + s.nm + s.nmin) then none
  let tail := s!"the occurrence of {o.head.pretty} keeps O2's relocated-recursor form"
  match O11a.applyWithE env (sizeOfInstanceAssumingAbsent env) o with
  | .ok e =>
    let missing := (Ix.Compile.Image.usedConstants e).filter fun n =>
      (match n with
        | .str _ "_sizeOf_inst" _ => true
        | _ => false) && (env.const? n).isNone
    if missing.isEmpty then return s!"O11a declined: {cause}; {tail}"
    let names := ", ".intercalate (missing.toList.map (·.pretty))
    return s!"O11a declined: the size instance {names} of a lower component is absent from \
      the input; {tail}"
  | .error (some c) => return s!"O11a declined: {c}; {tail}"
  | .error none => return s!"O11a declined: {cause}; {tail}"

/-! ## The scheduling edges O11a's rewrite needs

O11a's output for Lean's `all₀._sizeOf_N` of a split block references
`T._sizeOf_inst` for a cross field into another component `T`, and
`SizeOf.sizeOf`. The scheduler orders blocks by the input's references
(`CondensedBlocks.blockRefs`), so these references are added to it.

**Which edges.** For every Lean inductive block `all` (keyed by `all₀`, at
least two members) whose members the condensation puts in more than one
component (a split block), the *cross targets of a component* `C` are the
members `T` of another component that a member `Y ∈ C` references (in `Y`'s
type or a constructor type: a cross field into `T`). For every
`all₀._sizeOf_N` of the input whose value is `λ … . r …`:
- `r = X.rec` for a member `X`: add `all₀._sizeOf_N → T._sizeOf_inst` for
  every cross target `T` of `X`'s component (the fields O11a can rewrite);
- `r = all₀.rec_j` (a nested auxiliary's `sizeOf`): the same for the cross
  targets of every component (a superset, which only delays the schedule);
and `all₀._sizeOf_N → SizeOf.sizeOf` when it is in the input. Only targets
present in the input, never inside one component.

**No cycle** (A6f learnt this the hard way: edges to *every* cross target
from *every* `_sizeOf_N` close the cycle `T._sizeOf_k → T._sizeOf_inst →
T._sizeOf_k`, measured as "Circular dependency detected"). In the input,
`T._sizeOf_inst := SizeOf.mk T T._sizeOf_k` references exactly one member
`_sizeOf` (`T`'s own), and the member `_sizeOf`s are non-recursive
definitions over Lean's recursor whose motives and minors mention the
block's inductives and constructors, `Nat` and the `SizeOf` instances of
*external* field types (in-block fields use the induction hypotheses), so in
the input no `_sizeOf` of the block reaches another one, and nothing reaches
a nested auxiliary's `_sizeOf`. An added path therefore alternates
`X._sizeOf → T._sizeOf_inst → T._sizeOf → U._sizeOf_inst → …` with each
target's component a cross target of the previous member's component: a
direct reference between two components of one block, which descends
strictly in the condensation DAG. It ends, so there is no cycle (nested
`_sizeOf`s have no incoming path at all). `SizeOf.sizeOf` is a projection of
Init's `SizeOf`, below every user block. The condensation of the augmented
graph is the input's with these extra block dependencies: the components
and representatives do not change (`addSizeOfEdges` adds to `blockRefs`
only; Tarjan is not re-run, so the presentation of design document §6.1 is
untouched). Were the argument wrong, the fold would stop with its
"circular dependency" error, never compile out of order.

**Bytes.** No component, representative or iteration order of `blocks` or
`lowLinks` changes; only the ready order of the fold, which the schedule-
identity gate requires to be immaterial. With the switch off nothing
reads the new references; the edge is added in both switch states. -/

/-- The scheduling edges `(source, target)` of O11a (see the section
docstring); `refs` is the reference graph the condensation was built from. -/
def sizeOfEdges (const? : Name → Option ConstantInfo) (refs : Ix.Map Name (Ix.Set Name))
    (lowLinks : Ix.Map Name Name) : Array (Name × Name) := Id.run do
  let mut out : Array (Name × Name) := #[]
  for (n, _) in refs do
    let some (.inductInfo v) := const? n | continue
    if v.all[0]? != some n || v.all.size < 2 then continue
    let comp := fun (m : Name) => lowLinks.get? m
    if v.all.all (comp · == comp n) then continue
    let members : Ix.Set Name := v.all.foldl (·.insert ·) {}
    -- the cross targets of each component: members of another component
    -- that a member of it references
    let mut cross : Std.HashMap (Option Name) (Array Name) := {}
    let mut allTargets : Array Name := #[]
    for y in v.all do
      let some (.inductInfo yv) := const? y | continue
      for c in #[y] ++ yv.ctors do
        for r in refs.getD c {} do
          if members.contains r && comp r != comp y then
            let ts := cross.getD (comp y) #[]
            if !ts.contains r then cross := cross.insert (comp y) (ts.push r)
            if !allTargets.contains r then allTargets := allTargets.push r
    if allTargets.isEmpty then continue
    -- the block's sizeOf family `all₀._sizeOf_N`
    for i in [1:v.all.size + v.numNested + 1] do
      let d := Name.mkStr n s!"_sizeOf_{i}"
      if !refs.contains d then continue
      let some (.defnInfo dv) := const? d | continue
      -- the recursor the value applies, under its λs
      let (h, _) := getAppFnArgs (lamBody dv.value 64)
      let .const r _ _ := h | continue
      let mut targets : Array Name := #[]
      match r with
      | .str x "rec" _ =>
        if members.contains x then targets := cross.getD (comp x) #[] else continue
      | .str _ s _ => if s.startsWith "rec_" then targets := allTargets else continue
      | _ => continue
      if refs.contains nSizeOf && comp d != comp nSizeOf then out := out.push (d, nSizeOf)
      for t in targets do
        let inst := Name.mkStr t "_sizeOf_inst"
        if refs.contains inst && comp d != comp inst then out := out.push (d, inst)
  return out

/-- Add O11a's scheduling edges to the condensation's block dependencies. -/
def addSizeOfEdges (const? : Name → Option ConstantInfo) (refs : Ix.Map Name (Ix.Set Name))
    (blocks : Ix.CondensedBlocks) : Ix.CondensedBlocks := Id.run do
  let mut blockRefs := blocks.blockRefs
  for (d, t) in sizeOfEdges const? refs blocks.lowLinks do
    let some lo := blocks.lowLinks.get? d | continue
    blockRefs := blockRefs.alter lo fun
      | some s => some (s.insert t)
      | none => some (({} : Ix.Set Name).insert t)
  return { blocks with blockRefs }

end Ix.Compile.Pass.Opt

end
