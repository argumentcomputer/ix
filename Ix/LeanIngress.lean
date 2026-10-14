import Ix.CondenseM
import Ix.LeanIngress.Expr
import IxC.Kernel.Ixon.Prelude
import IxC.Kernel.Cached.Installed

/-! # Source mode: Lean environments as the checker's declarations

`leanIngress` turns an `Ix.Environment`, `Ix.CanonM`'s canonicalization of a
Lean environment and the compiler's own input (`Ix.CompileM.compileEnv`), into
the `Array Ix.Kernel.Declaration` that the verified fold
`Ix.Kernel.Cached.checkDecls` consumes; `checkSource` runs the fold on it.
It is the Source-mode counterpart of the Ixon reader (`Ix.Kernel.Reader`): the
source semantics and the compiler start from the same object, and both front
ends lower through the reader's own back half.

## Soundness: nothing here is trusted

`Ix.Kernel.model_exists` holds for every array the fold accepts, so no
property of this module is needed for the consistency of what `checkSource`
accepts (`Ix.LeanIngress.Theorems`). What the ingress decides is coverage and
the faithfulness of the accepted environment to the Lean environment.

## Keys

The kernel key is Lean's own name (`ingressName`). The checker's pinned names
are Lean's names, so the pin table is the identity and no `ix.<hex>` name
occurs. A recursor keeps its Lean name, which is the name the checker's
frontend derives (`T.rec`, `T.rec_j`). Level parameters are positions
(`Numbering`): a constant's `i`-th Lean level parameter is `i`, except at a
large eliminator, whose elimination level is the fresh position `n` after
its block's `n` and whose other parameters are the block's, the shape
`elim :: lps` the checker recognises, numbered as the Ixon reader numbers
them. Nothing is hashed and nothing is rewritten: terms are converted by
`Ix.LeanIngress.Expr` (Lean's levels as they are up to the numbering,
`mdata` erased, binder names, binder infos and `nonDep` dropped,
`pw := .never`).

## Grouping

* An **inductive block** is taken as Lean gives it (`groupsOf`): one group per
  `all` list, its members in `all` order, each member's constructors in
  order, then its recursors, `T.rec` for each member `T` in `all` order and
  then `T₀.rec_j` for the first member `T₀` and `j = 1 … numNested`. It
  becomes one `indDecl` at the block's declared `numParams`, preceded by the
  modeller's records for a mutual or nested block (`Reader.lowerInductive`).
* **Definitions, theorems and opaques** are grouped by the strongly connected
  components of the reference graph (`Ix.CondensedBlocks`), as the compiler
  groups them into `muts` blocks. A singleton becomes one declaration
  (`Reader.lowerDefinition`). A larger component is handled as the reader
  handles a definition block: the safety policy first, member by member, then
  `Reader.defOrder` over the references between the members, and one
  declaration per member in that order.
* **Axioms** and **quotient constants** become one declaration each.
* Hints are Lean's own `ReducibilityHints`; the safety policy (an unsafe or
  partial definition, an unsafe opaque, an unsafe axiom or inductive decline)
  is the reader's.
* A constant the grouping cannot place (a constructor or recursor outside its
  block, a component that mixes inductives and definitions) is a group of its
  own that fails with the reader's reason.

## Order

The groups follow a depth-first postorder of the reference graph between
groups (`orderOf`): every group follows the groups its constants reference
(the condensation's `blockRefs`), and a group that contains a literal follows
the constants the literal references (`Reader.literalEdges`'s edges, by
name). A group whose reference graph has a cycle through other groups is
refused. The fold's input is then `Frontend.preparePrelude`'s, as for the
Ixon reader: the stream's own copies of the prelude's declarations move to
the front, the prelude fills in the ones the environment lacks.

## The reader's back half

Every group is lowered by the reader's own functions, against the reader's
`State` threaded group by group (`State.commit`): `Reader.lowerInductive`
(the stream's consistency checks, the projection rewrite's owners, the
in-process modeller), `Reader.lowerDefinition` (the projection rewrite, the
safety policy, the hint), and `State.note`/`noteGenerated` through
`State.commit`. -/

namespace Ix.LeanIngress

open Ix.Kernel.Reader (CName CExpr CVal CDecl ReadError State Read BlockRead RecCounts)

/-! ## Declaration groups -/

/-- A declaration group of the environment: what becomes one reading. -/
inductive Group where
  /-- an inductive block: its members in `all` order, each member's
  constructors in order, its recursors -/
  | inductive (types : Array Ix.InductiveVal) (ctors : Array (Array Ix.ConstructorVal))
      (recs : Array Ix.RecursorVal)
  /-- definitions, theorems and opaques: one, or a strongly connected
  component of the reference graph -/
  | definitions (members : Array Ix.ConstantInfo)
  | axiom (v : Ix.AxiomVal)
  | quot (v : Ix.QuotVal)
  /-- constants the grouping cannot place, and why -/
  | invalid (names : Array Ix.Name) (error : ReadError)

instance : Inhabited Group := ⟨.invalid #[] default⟩

/-- The constants a group declares. -/
def Group.names : Group → Array Ix.Name
  | .inductive types ctors recs =>
    types.map (·.cnst.name) ++ ctors.flatMap (·.map (·.cnst.name)) ++ recs.map (·.cnst.name)
  | .definitions ms => ms.map (·.getCnst.name)
  | .axiom v => #[v.cnst.name]
  | .quot v => #[v.cnst.name]
  | .invalid ns _ => ns

/-- The name a group is reported under: its first constant's. -/
def Group.name (g : Group) : CName :=
  match g.names[0]? with
  | some n => ingressName n
  | none => .anonymous

/-- Whether `n` is `parent.s`. -/
def isStrName (parent : Ix.Name) (s : String) : Ix.Name → Bool
  | .str p s' _ => s' == s && p == parent
  | _ => false

/-- The recursors of an inductive block among `candidates` (the recursors
that name the block), in Lean's order: `T.rec` for every member `T`, then
`T₀.rec_j` for the first member `T₀` and `j = 1 … numNested`; the first name
that has no recursor, if one has none. -/
def blockRecursors (first : Ix.InductiveVal) (candidates : Array Ix.RecursorVal) :
    Except String (Array Ix.RecursorVal) := do
  let find (parent : Ix.Name) (s : String) : Except String Ix.RecursorVal :=
    match candidates.find? (isStrName parent s ·.cnst.name) with
    | some r => pure r
    | none => throw s!"{ingressName parent}.{s}"
  let own ← first.all.mapM (find · "rec")
  let aux ← (Array.range first.numNested).mapM fun j => find first.cnst.name s!"rec_{j + 1}"
  return own ++ aux

/-- The group of the inductive block whose first member is `first`, with the
recursors that name the block (`candidates`). A block whose members,
constructors or recursors are not as Lean lays them out is an invalid group
claiming the names it would have declared. -/
def inductiveGroup (env : Ix.Environment) (first : Ix.InductiveVal)
    (candidates : Array Ix.RecursorVal) : Group := Id.run do
  let block := first.all
  let ctorsOf (n : Ix.Name) : Array Ix.Name :=
    match env.consts.get? n with
    | some (.inductInfo v) => v.ctors
    | _ => #[]
  let claim := block ++ block.flatMap ctorsOf ++ candidates.map (·.cnst.name)
  let bad (e : ReadError) : Group := .invalid claim e
  let mut types : Array Ix.InductiveVal := #[]
  for n in block do
    let some (.inductInfo v) := env.consts.get? n
      | return bad (.malformed s!"inductive block member {ingressName n} is missing or not an inductive")
    unless v.all == block do
      return bad (.malformed s!"inductive {ingressName n} names a different block")
    types := types.push v
  let mut ctors : Array (Array Ix.ConstructorVal) := #[]
  for v in types do
    let mut cs : Array Ix.ConstructorVal := #[]
    for (c, j) in v.ctors.zipIdx do
      let some (.ctorInfo cv) := env.consts.get? c
        | return bad (.malformed s!"constructor {ingressName c} of {ingressName v.cnst.name} is \
            missing or not a constructor")
      unless cv.induct == v.cnst.name do
        return bad (.malformed s!"constructor {ingressName c} names another inductive")
      unless cv.cidx == j do return bad (.malformed "constructor index differs from its position")
      cs := cs.push cv
    ctors := ctors.push cs
  match blockRecursors first candidates with
  | .ok recs => return .inductive types ctors recs
  | .error _ => return bad (.declined "inductive block without a recursor in the input")

def isFamily : Ix.ConstantInfo → Bool
  | .inductInfo _ | .ctorInfo _ | .recInfo _ => true
  | _ => false

def isDefinition : Ix.ConstantInfo → Bool
  | .defnInfo _ | .thmInfo _ | .opaqueInfo _ => true
  | _ => false

/-- The group of a strongly connected component's constants outside the
inductive families (none if it has none), its members in name-hash order. -/
def componentGroup (env : Ix.Environment) (members : Ix.Set Ix.Name) : Option Group :=
  let cis : Array Ix.ConstantInfo := members.toArray.filterMap (env.consts.get? ·)
  let others := (cis.filter (!isFamily ·)).qsort fun a b =>
    Ix.nameCompare a.getCnst.name b.getCnst.name == .lt
  let names := others.map (·.getCnst.name)
  if others.isEmpty then none
  else if cis.any isFamily then some (.invalid names (.malformed "a block mixes inductives and definitions"))
  else if others.all isDefinition then some (.definitions others)
  else match others with
    | #[.axiomInfo v] => some (.axiom v)
    | #[.quotInfo v] => some (.quot v)
    | _ => some (.invalid names (.malformed "a cyclic block of axioms or quotients"))

/-- A constant no group claims: the reader's reason. -/
def unplaced (n : Ix.Name) : Ix.ConstantInfo → Group
  | .recInfo _ => .invalid #[n] (.declined "recursor whose inductive block is not in the input")
  | .ctorInfo _ =>
    .invalid #[n] (.malformed s!"constructor {ingressName n} is not in its inductive's block")
  | .inductInfo _ => .invalid #[n] (.malformed s!"inductive {ingressName n} is not in its block's group")
  | _ => .invalid #[n] (.malformed s!"constant {ingressName n} is not in the condensation")

/-- **The groups** of an environment under its condensation: the inductive
blocks, the components' other constants, and a group of its own for every
constant neither claims. -/
def groupsOf (env : Ix.Environment) (blocks : Ix.CondensedBlocks) : Array Group := Id.run do
  let mut recsOf : Ix.Map Ix.Name (Array Ix.RecursorVal) := {}
  for (_, ci) in env.consts do
    if let .recInfo rv := ci then
      if let some first := rv.all[0]? then
        recsOf := recsOf.insert first ((recsOf.getD first #[]).push rv)
  let mut out : Array Group := #[]
  for (n, ci) in env.consts do
    if let .inductInfo v := ci then
      if v.all[0]? == some n then out := out.push (inductiveGroup env v (recsOf.getD n #[]))
  for (_, members) in blocks.blocks do
    if let some g := componentGroup env members then out := out.push g
  let mut claimed : Ix.Set Ix.Name := {}
  for g in out do
    for n in g.names do claimed := claimed.insert n
  for (n, ci) in env.consts do
    unless claimed.contains n do out := out.push (unplaced n ci)
  return out

/-! ## Conversion

A group's terms are converted together (`ingressExprs`, one memo for the
terms of the group's constants that number their level parameters alike),
before any state is read; what the lowering reads is `Converted`. -/

/-- How a constant's Lean level parameters `names` become the checker's
positions: name `i` is position `i`, except at a large eliminator (`large`:
a recursor with one level parameter more than its block's `n`), whose first
name, the elimination level, is the fresh position `n` and whose name
`i + 1` is the block's position `i`, as the Ixon reader numbers a recursor
(`Reader.recLps`). A name that is not among `names` is the position
`names.size`, which no parameter of the constant has. -/
structure Numbering where
  names : Array Ix.Name
  large : Bool := false
  deriving BEq

/-- The position of a level-parameter name. -/
def Numbering.pos (σ : Numbering) (n : Ix.Name) : Ix.Kernel.LevelParam :=
  match σ.names.findIdx? (· == n) with
  | none => σ.names.size
  | some 0 => if σ.large then σ.names.size - 1 else 0
  | some (i + 1) => if σ.large then i else i + 1

/-- The constant's own level parameters, numbered. -/
def Numbering.params (σ : Numbering) : List Ix.Kernel.LevelParam :=
  σ.names.toList.map σ.pos

def hintOf : Lean.ReducibilityHints → Ix.Kernel.ReducibilityHint
  | .opaque => .opaque
  | .abbrev => .abbrev
  | .regular h => .regular h.toNat

def quotKindOf : Lean.QuotKind → Ix.Kernel.QuotKind
  | .type => .type
  | .ctor => .ctor
  | .lift => .lift
  | .ind => .ind

def safetyOf : Lean.DefinitionSafety → Ix.DefinitionSafety
  | .unsafe => .unsaf
  | .safe => .safe
  | .partial => .part

/-- A definition member's kind, safety (as the compiler stores them: an opaque
is unsafe or safe, a theorem safe) and hint. -/
def definitionShape : Ix.ConstantInfo → Option (Ix.DefKind × Ix.DefinitionSafety × Ix.Kernel.ReducibilityHint)
  | .defnInfo v => some (.defn, safetyOf v.safety, hintOf v.hints)
  | .thmInfo _ => some (.thm, .safe, .opaque)
  | .opaqueInfo v => some (.opaq, if v.isUnsafe then .unsaf else .safe, .opaque)
  | _ => none

def definitionValue : Ix.ConstantInfo → Option Ix.Expr
  | .defnInfo v => some v.value
  | .thmInfo v => some v.value
  | .opaqueInfo v => some v.value
  | _ => none

/-- A definition member, converted: its header and value, kind, safety and
hint. -/
structure DefMember where
  cv : CVal
  value : CExpr
  kind : Ix.DefKind
  safety : Ix.DefinitionSafety
  hint : Ix.Kernel.ReducibilityHint
  deriving Inhabited

/-- A group's terms converted: what the lowering reads. -/
inductive Converted where
  | inductive (rb : BlockRead)
  /-- definition members, in the order they are lowered -/
  | definitions (members : Array DefMember)
  | axiom (cv : CVal)
  | quot (kind : Ix.Kernel.QuotKind) (cv : CVal)

/-- The conversion of terms, each under its constant's numbering: a run of
consecutive terms under one numbering is converted together (one memo). A
term conversion failure is a malformed group. -/
def exprsOf (items : Array (Numbering × Ix.Expr)) : Except ReadError (Array CExpr) := do
  let flush (σ : Numbering) (es : Array Ix.Expr) (out : Array CExpr) :
      Except ReadError (Array CExpr) :=
    match ingressExprs σ.pos es.toList with
    | .ok ks => .ok (out ++ ks.toArray)
    | .error e => .error (.malformed s!"source term: {e}")
  let mut out : Array CExpr := Array.mkEmpty items.size
  let mut run : Option (Numbering × Array Ix.Expr) := none
  for (σ, e) in items do
    match run with
    | some (τ, es) =>
      if σ == τ then run := some (τ, es.push e)
      else
        out ← flush τ es out
        run := some (σ, #[e])
    | none => run := some (σ, #[e])
  if let some (τ, es) := run then out ← flush τ es out
  return out

/-- An inductive block converted, with the reader's own checks on it: unsafe
members decline, members that disagree on `numParams` decline, a
constructor's field count must be its type's telescope past the block's
parameters. A recursor with one level parameter more than the block's first
member is a large eliminator. -/
def convertInductive (types : Array Ix.InductiveVal) (ctors : Array (Array Ix.ConstructorVal))
    (recs : Array Ix.RecursorVal) : Except ReadError Converted := do
  let some first := types[0]? | throw (.malformed "empty inductive block")
  if types.any (·.isUnsafe) || ctors.any (·.any (·.isUnsafe)) || recs.any (·.isUnsafe) then
    throw (.declined "unsafe inductive declaration")
  let nPd := first.numParams
  unless types.all (·.numParams == nPd) do
    throw (.declined "inductive block whose type records disagree on numParams")
  let own (cv : Ix.ConstantVal) : Numbering := ⟨cv.levelParams, false⟩
  let ofRec (r : Ix.RecursorVal) : Numbering :=
    ⟨r.cnst.levelParams, r.cnst.levelParams.size == first.cnst.levelParams.size + 1⟩
  let items : Array (Numbering × Ix.Expr) :=
    types.map (fun v => (own v.cnst, v.cnst.type)) ++
      ctors.flatMap (·.map fun c => (own c.cnst, c.cnst.type)) ++
      recs.flatMap fun r => #[(ofRec r, r.cnst.type)] ++ r.rules.map ((ofRec r, ·.rhs))
  let ks ← exprsOf items
  let mut i := 0
  let mut tys : Array (CVal × Nat × Nat) := #[]
  for v in types do
    tys := tys.push (⟨ingressName v.cnst.name, (own v.cnst).params, ks[i]!⟩, v.numParams,
      v.numIndices)
    i := i + 1
  let mut cts : Array (CVal × Nat × Nat) := #[]
  let mut ctorNames : Array (List CName) := #[]
  for cs in ctors do
    let mut names : List CName := []
    for c in cs do
      let cv : CVal := ⟨ingressName c.cnst.name, (own c.cnst).params, ks[i]!⟩
      i := i + 1
      unless nPd + c.numFields == Ix.Kernel.Reader.piTeleLen cv.type do
        throw (.malformed s!"constructor {cv.name} declares {c.numFields} fields at {nPd} parameters; \
          its type has {Ix.Kernel.Reader.piTeleLen cv.type} binders")
      cts := cts.push (cv, c.numParams, c.numFields)
      names := names ++ [cv.name]
    ctorNames := ctorNames.push names
  let mut rs : Array (CVal × RecCounts × List Ix.Kernel.RecRule) := #[]
  for r in recs do
    let cv : CVal := ⟨ingressName r.cnst.name, (ofRec r).params, ks[i]!⟩
    i := i + 1
    let mut rules : List Ix.Kernel.RecRule := []
    for rule in r.rules do
      rules := rules ++ [Ix.Kernel.RecRule.mk (ingressName rule.ctor) rule.nfields 0 .inert ks[i]!
        false false false]
      i := i + 1
    rs := rs.push (cv, ⟨r.numParams, r.numMotives, r.numMinors, r.numIndices, r.k⟩, rules)
  return .inductive ⟨nPd, tys, cts, ctorNames, rs⟩

/-- A definition group converted. A singleton is lowered as the reader lowers
a `defn` record. A larger group is handled as the reader handles a definition
`muts` block: the safety policy first, member by member (a block with a member
that is not safe declines with that member's reason), then `defOrder` over the
references between the members (a cycle declines). -/
def convertDefinitions (members : Array Ix.ConstantInfo) : Except ReadError Converted := do
  let shapes ← members.mapM fun ci => match definitionShape ci, definitionValue ci with
    | some s, some v => pure (ci, s, v)
    | _, _ => throw (.malformed "a definition group holds a constant that is not a definition")
  if shapes.size > 1 then
    if let some why := shapes.findSome? fun (_, (k, s, _), _) => Ix.Kernel.Reader.safetyDeclineOf k s then
      throw (.declined why)
  let own (ci : Ix.ConstantInfo) : Numbering := ⟨ci.getCnst.levelParams, false⟩
  let ks ← exprsOf (shapes.flatMap fun (ci, _, v) => #[(own ci, ci.getCnst.type), (own ci, v)])
  let ms : Array DefMember := shapes.zipIdx.map fun ((ci, (kind, safety, hint), _), j) =>
    ⟨⟨ingressName ci.getCnst.name, (own ci).params, ks[2 * j]!⟩, ks[2 * j + 1]!, kind, safety,
      hint⟩
  if ms.size ≤ 1 then return .definitions ms
  let names := ms.map (·.cv.name)
  let deps : Array (Std.HashSet Nat) := ms.map fun m =>
    names.zipIdx.foldl (init := {}) fun acc (n, j) =>
      if Ix.Kernel.Frontend.occursConstFast n m.cv.type || Ix.Kernel.Frontend.occursConstFast n m.value
      then acc.insert j else acc
  let some order := Ix.Kernel.Reader.defOrder deps
    | throw (.declined "mutually recursive definition block")
  return .definitions (order.map (ms[·]!))

/-- **A group's conversion.** -/
def convert : Group → Except ReadError Converted
  | .inductive types ctors recs => convertInductive types ctors recs
  | .definitions members => convertDefinitions members
  | .axiom v => do
    if v.isUnsafe then throw (.declined "unsafe axiom")
    let σ : Numbering := ⟨v.cnst.levelParams, false⟩
    let ks ← exprsOf #[(σ, v.cnst.type)]
    return .axiom ⟨ingressName v.cnst.name, σ.params, ks[0]!⟩
  | .quot v => do
    let σ : Numbering := ⟨v.cnst.levelParams, false⟩
    let ks ← exprsOf #[(σ, v.cnst.type)]
    return .quot (quotKindOf v.kind) ⟨ingressName v.cnst.name, σ.params, ks[0]!⟩
  | .invalid _ e => throw e

/-! ## Lowering -/

/-- A converted group's declarations, through the reader's back half: the
state is read, not changed (`State.commit` applies what the group taught). -/
def lower (st : State) : Converted → Ix.Kernel.Reader.ReadM Read
  | .inductive rb => Ix.Kernel.Reader.lowerInductive st rb
  | .definitions #[m] => do
    let (decl, rw) ← Ix.Kernel.Reader.lowerDefinition (some m.hint) st (st.heights.getD · 0)
      m.cv m.value m.kind m.safety
    pure { decls := #[decl], projRewrites := if rw then 1 else 0 }
  | .definitions ms => do
    let mut blockHeights : Std.HashMap CName Nat := {}
    let mut out : Array CDecl := #[]
    let mut rewrites := 0
    for m in ms do
      let heights : CName → Nat := fun n => blockHeights.getD n (st.heights.getD n 0)
      let (decl, rw) ← Ix.Kernel.Reader.lowerDefinition (some m.hint) st heights m.cv m.value
        m.kind m.safety
      if let .defnDecl cv _ h := decl then
        blockHeights := blockHeights.insert cv.name (Ix.Kernel.Frontend.InModel.hintHeight h)
      if rw then rewrites := rewrites + 1
      out := out.push decl
    pure { decls := out, projRewrites := rewrites }
  | .axiom cv => pure { decls := #[.axiomDecl cv] }
  | .quot kind cv => pure { decls := #[.quotDecl kind cv] }

/-! ## Order -/

/-- Whether a converted group's terms contain a `Nat` literal and a `String`
literal: `(nat, str)`. Every term is walked once on its DAG. -/
def literalKinds (c : Converted) : Bool × Bool := Id.run do
  let exprs : Array CExpr := match c with
    | .inductive rb =>
      rb.types.map (·.1.type) ++ rb.ctors.map (·.1.type) ++
        rb.recs.flatMap fun (cv, _, rules) => #[cv.type] ++ rules.toArray.map (·.rhs)
    | .definitions ms => ms.flatMap fun m => #[m.cv.type, m.value]
    | .axiom cv | .quot _ cv => #[cv.type]
  let mut seen : Std.HashSet CExpr := {}
  let mut todo := exprs
  let mut nat := false
  let mut str := false
  while h : todo.size > 0 do
    let e := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains e then continue
    seen := seen.insert e
    match e with
    | .lit (.natVal _) => nat := true
    | .lit (.strVal _) => str := true
    | .app f a => todo := todo.push f |>.push a
    | .lam t b _ | .forallE t b _ => todo := todo.push t |>.push b
    | .letE t v b => todo := todo.push t |>.push v |>.push b
    | .proj _ _ b => todo := todo.push b
    | _ => pure ()
  return (nat, str)

/-- Whether an environment key is a checker name (`ingressName n = k`,
decided without building the name). -/
def nameIs : Ix.Name → CName → Bool
  | .anonymous _, .anonymous => true
  | .str p s _, .str q t => s == t && nameIs p q
  | .num p i _, .num q j => i == j && nameIs p q
  | _, _ => false

/-- What the order is computed from: the groups, their conversions, and for
every group the groups it references (`hard`), the groups of the constants
its literals reference (`literal`), and a reference the order cannot place
(`unplaced`: a constant the environment does not have, or a member the
condensation does not have). -/
structure Graph where
  groups : Array Group
  converted : Array (Except ReadError Converted)
  hard : Array (Array Nat)
  literal : Array (Array Nat)
  unplaced : Array (Option ReadError)

/-- The reference graph between groups, from the condensation's `blockRefs`. -/
def graphOf (blocks : Ix.CondensedBlocks) (groups : Array Group)
    (converted : Array (Except ReadError Converted)) : Graph := Id.run do
  let supportNames := Ix.Kernel.Reader.strLitSupportNames
  let mut groupOf : Ix.Map Ix.Name Nat := {}
  let mut supportOf : Std.HashMap CName Nat := {}
  for (g, i) in groups.zipIdx do
    for n in g.names do
      groupOf := groupOf.insert n i
      if let some k := supportNames.find? (nameIs n) then supportOf := supportOf.insert k i
  let mut hard : Array (Array Nat) := #[]
  let mut unplaced : Array (Option ReadError) := #[]
  for (g, i) in groups.zipIdx do
    let mut seenLo : Ix.Set Ix.Name := {}
    let mut ds : Std.HashSet Nat := {}
    let mut bad : Option ReadError := none
    for n in g.names do
      let some lo := blocks.lowLinks.get? n
        | if bad.isNone then
            bad := some (.malformed s!"constant {ingressName n} is not in the condensation")
      if seenLo.contains lo then continue
      seenLo := seenLo.insert lo
      for r in (blocks.blockRefs.get? lo).getD {} do
        match groupOf.get? r with
        | some j => if j != i then ds := ds.insert j
        | none =>
          if bad.isNone then
            bad := some (.malformed s!"references {ingressName r}, which is not in the environment")
    hard := hard.push (ds.toArray.qsort (· < ·))
    unplaced := unplaced.push bad
  let support (names : List CName) : Array Nat :=
    names.foldl (fun acc n => match supportOf[n]? with
      | some j => if acc.contains j then acc else acc.push j
      | none => acc) #[]
  let natTargets := support Ix.Kernel.Reader.natLitSupportNames
  let strTargets := support supportNames
  let literal := converted.zipIdx.map fun (c, i) => match c with
    | .ok c =>
      let (nat, str) := literalKinds c
      (if str then strTargets else if nat then natTargets else #[]).filter (· != i)
    | .error _ => #[]
  return ⟨groups, converted, hard, literal, unplaced⟩

/-- **The order**: a depth-first postorder over the hard and literal edges,
from the groups in their own order. -/
def orderOf (g : Graph) : Array Nat := Id.run do
  let n := g.groups.size
  let mut done : Array Bool := Array.replicate n false
  let mut active : Array Bool := Array.replicate n false
  let mut out : Array Nat := #[]
  for root in [0:n] do
    if done[root]! then continue
    let mut stack : Array (Nat × Bool) := #[(root, false)]
    while h : stack.size > 0 do
      let (node, expanded) := stack[stack.size - 1]
      stack := stack.pop
      if expanded then
        active := active.set! node false
        unless done[node]! do
          done := done.set! node true
          out := out.push node
      else unless done[node]! || active[node]! do
        active := active.set! node true
        stack := stack.push (node, true)
        for d in g.hard[node]! ++ g.literal[node]! do
          unless done[d]! || active[d]! do stack := stack.push (d, false)
  return out

/-- The groups in order, by index, each with its conversion or the reason it
is refused before lowering: its conversion's, an unplaced reference, or a
group it references that does not come before it (a cycle). -/
def scheduleOf (g : Graph) : Array (Nat × Except ReadError Converted) := Id.run do
  let order := orderOf g
  let mut position : Array Nat := Array.replicate g.groups.size 0
  for (i, p) in order.zipIdx do position := position.set! i p
  return order.map fun i => (i, do
    let c ← g.converted[i]!
    if let some e := g.unplaced[i]! then throw e
    unless g.hard[i]!.all (position[·]! < position[i]!) do
      throw (.malformed "a reference cycle through another declaration group")
    return c)

/-! ## The ingress -/

/-- A refusal: the group it happened at (its first constant's name and its
position in the order) and the reader's error. -/
structure IngressError where
  name : CName
  position : Nat
  error : ReadError

instance : ToString IngressError where
  toString e := s!"{e.name} (group {e.position}): {e.error}"

/-- The reference graph of an environment's groups under its condensation,
with their conversions (`groupsOf`, `convert`, `graphOf`). -/
def graph (env : Ix.Environment) (blocks : Ix.CondensedBlocks) : Graph :=
  let groups := groupsOf env blocks
  graphOf blocks groups (groups.map convert)

/-- Lower the scheduled groups of `g` from `st`, threading the reader's
state. -/
def lowerAll (st : State) (g : Graph) (scheduled : Array (Nat × Except ReadError Converted)) :
    Except IngressError (State × Array CDecl) := do
  let mut st := st
  let mut out : Array CDecl := #[]
  for ((gi, c), i) in scheduled.zipIdx do
    let fail (e : ReadError) : IngressError := ⟨g.groups[gi]!.name, i, e⟩
    let c ← c.mapError fail
    let r ← (lower st c).mapError fail
    st := st.commit r
    out := out ++ r.decls
  return (st, out)

/-- **The Source-mode ingress**: the declarations of an environment under its
condensation, in dependency order, lowered through the reader's back half
from the reader state `st` (the fold's input before `preparePrelude`). -/
def leanIngress (env : Ix.Environment) (blocks : Ix.CondensedBlocks) (st : State := {}) :
    Except IngressError (Array CDecl) := do
  let g := graph env blocks
  return (← lowerAll st g (scheduleOf g)).2

/-! ## The Source-mode check -/

/-- Ingress, prelude and checker failures, kept apart. -/
inductive SourceError where
  | ingress (error : IngressError)
  /-- the committed prelude does not load (a corrupted file) -/
  | prelude (reason : String)
  | kernel (error : Ix.Kernel.CheckError) (position : Nat)

instance : ToString SourceError where
  toString
    | .ingress e => s!"ingress: {e}"
    | .prelude r => s!"prelude: {r}"
    | .kernel e p => s!"kernel at {p}: {e}"

/-- The fold's input: the ingress from the prelude's reader state, prepared by
`Frontend.preparePrelude` with the prelude's declarations. -/
def prepareSource (pre : Ix.Kernel.Reader.Prelude) (env : Ix.Environment)
    (blocks : Ix.CondensedBlocks) : Except SourceError (Array CDecl) := do
  let decls ← (leanIngress env blocks pre.state).mapError .ingress
  pure (Ix.Kernel.Frontend.preparePrelude pre.ix decls)

/-- The Source-mode check over an explicit prelude and `Nat`-operation pin
list. -/
def checkSourceWith (pre : Ix.Kernel.Reader.Prelude) (natPins : List Ix.Kernel.NatOpPinSet)
    (env : Ix.Environment) (blocks : Ix.CondensedBlocks) : Except SourceError Ix.Kernel.Env := do
  let decls ← prepareSource pre env blocks
  (Ix.Kernel.Cached.checkDecls .verified natPins decls).mapError fun (e, i) => .kernel e i

/-- **The Source-mode check**: `leanIngress` behind the committed prelude
(the Ixon reader's, whose constants carry Lean's names), then the verified
fold at the empty `Nat`-operation pin list (the pinned `Nat` operations
decline). -/
def checkSource (env : Ix.Environment) (blocks : Ix.CondensedBlocks) :
    Except SourceError Ix.Kernel.Env := do
  let pre ← Ix.Kernel.Reader.builtinPrelude.mapError .prelude
  checkSourceWith pre [] env blocks

end Ix.LeanIngress
