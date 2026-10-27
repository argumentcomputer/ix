module

public import Ix.CondenseM
public import Ix.LeanIngress.Expr
public import Ix.LeanIngress.Names
public import Ix.LeanIngress.Order
public import Ix.LeanIngress.Collapse
public import IxC.Kernel.Ixon.Prelude
public import IxC.Kernel.Cached.Installed
public import Ix.RoleEvidence
public import IxC.Kernel.Tier.Check
public import IxC.Kernel.Tier.Ind

/-! # Source mode: Lean environments as the checker's declarations

`leanIngress` turns an `Ix.Environment`, `Ix.CanonM`'s canonicalization of a
Lean environment and the compiler's own input (`Ix.Cert.compile`, whose fold
is `Ix.CompileM.compileEnvFold`), into the `Array Ix.Kernel.Declaration` that
the verified fold `Ix.Kernel.Cached.checkDecls` consumes; `checkSource` runs
the fold on it. It is the Source-mode counterpart of the Ixon reader (`Ix.Kernel.Reader`): the
source semantics and the compiler start from the same object, and both front
ends lower through the reader's own back half.

## Soundness: nothing here is trusted

`Ix.Kernel.model_exists` holds for every array the fold accepts, so no
property of this module is needed for the consistency of what `checkSource`
accepts (`Ix.LeanIngress.Theorems`). What the ingress decides is coverage and
the faithfulness of the accepted environment to the Lean environment.

## Keys

A constant's key is its role's key if Source mode's fixed table binds its Lean
name to a role (`sourceBinding`: role `r` is the constant named `r.leanName`),
and otherwise the input key of its Lean name (`ingressKey`, a `Key .source`). A recursor is keyed by its own Lean name (`T.rec`, `T.rec_j`),
as any input constant. Level parameters are positions
(`Numbering`): a constant's `i`-th Lean level parameter is `i`, except at a
large eliminator, whose elimination level is the fresh position `n` after
its block's `n` and whose other parameters are the block's, the shape
`elim :: lps` the checker recognises, numbered as the Ixon reader numbers
them. Nothing is hashed and nothing is rewritten: terms are converted by
`Ix.LeanIngress.Expr` (Lean's levels as they are up to the numbering,
`mdata` erased except the compiler's contract frames, whose contracts go on the
binders they wrap, binder names, binder infos and `nonDep` dropped,
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
  `Reader.defOrder` over the references between the members (taken in Lean's
  name order), and one declaration per member in that order.
* **Axioms** and **quotient constants** become one declaration each.
* Hints are Lean's own `ReducibilityHints`; the safety policy (an unsafe or
  partial definition, an unsafe opaque, an unsafe axiom or inductive decline)
  is the reader's.
* A constant the grouping cannot place (a constructor or recursor outside its
  block, a component that mixes inductives and definitions) is a group of its
  own that fails with the reader's reason.

## Order

The groups follow a depth-first postorder of the reference graph between
groups (`orderOf`), with roots and successors taken in Lean's name order
(`nameCmp`), so the order is a function of the environment's names and
references, not of hash-map iteration or name hashes. Every group follows the
groups its constants reference (the condensation's `blockRefs`), and a group
that contains a literal follows the constants the literal references
(`Reader.literalEdges`'s edges, by name). A group whose reference graph has a
cycle through other groups is refused. The fold's input is then
`Frontend.preparePrelude`'s, as for the Ixon reader: the stream's own copies
of the prelude's declarations move to the front, the prelude fills in the
ones the environment lacks.

## The reader's back half

Every group is lowered by the reader's own functions, against the reader's
`State` threaded group by group (`State.commit`): `Reader.lowerInductive`
(the stream's consistency checks, the projection rewrite's owners, the
in-process modeller), `Reader.lowerDefinition` (the projection rewrite, the
safety policy, the hint), and `State.note`/`noteGenerated` through
`State.commit`. -/

@[expose] public section

namespace Ix.LeanIngress

open Ix.Kernel.Reader (CName CExpr CVal CDecl ReadError State Read BlockRead RecCounts)

/-! ## Names, compared structurally

`Ix.Name`'s `==` compares the root's stored hash only, so the ingress compares
names structurally (`Ix.Name.beqRaw`) and keys its own tables by `TableName`, as
the compiler's tables do since CQ2.25. The environment's map
(`Ix.Environment.consts`) and the condensation's (`Ix.CondensedBlocks`) are
inputs, looked up as they come. -/

/-- A name as a key of the ingress's own tables: compared structurally
(`Ix.Name.beqRaw`), hashed by its stored hash. A type synonym, so that a name
is a key as it is. -/
def TableName : Type := Ix.Name

instance : BEq TableName := ⟨fun a b => Ix.Name.beqRaw a b⟩
instance : Hashable TableName := ⟨fun n => hash (Ix.Name.getHash n)⟩

instance : LawfulBEq TableName where
  eq_of_beq same := Ix.Name.beqRaw_iff.mp same
  rfl := Ix.Name.beqRaw_iff.mpr rfl

instance : LawfulHashable TableName where
  hash_eq a b same := by
    have equal : a = b := Ix.Name.beqRaw_iff.mp same
    subst equal
    rfl

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
def Group.name (g : Group) : CName .source :=
  match g.names[0]? with
  | some n => ingressKey n
  | none => .id .anonymous

/-- Whether `n` is `parent.s`. -/
def isStrName (parent : Ix.Name) (s : String) : Ix.Name → Bool
  | .str p s' _ => s' == s && Ix.Name.beqRaw p parent
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
def inductiveGroupUsing {m : Type → Type} [Monad m]
    (lookup : Ix.Name → m (Option Ix.ConstantInfo)) (first : Ix.InductiveVal)
    (candidates : Array Ix.RecursorVal) : m Group := do
  let block := first.all
  let ctorsOf (n : Ix.Name) : m (Array Ix.Name) := do
    return match ← lookup n with
    | some (.inductInfo v) => v.ctors
    | _ => #[]
  let claimedCtors ← block.flatMapM ctorsOf
  let claim := block ++ claimedCtors ++ candidates.map (·.cnst.name)
  let bad (e : ReadError) : Group := .invalid claim e
  let mut types : Array Ix.InductiveVal := #[]
  for n in block do
    let some (.inductInfo v) ← lookup n
      | return bad (.malformed s!"inductive block member {ingressName n} is missing or not an inductive")
    unless v.all.isEqv block Ix.Name.beqRaw do
      return bad (.malformed s!"inductive {ingressName n} names a different block")
    types := types.push v
  let mut ctors : Array (Array Ix.ConstructorVal) := #[]
  for v in types do
    let mut cs : Array Ix.ConstructorVal := #[]
    for (c, j) in v.ctors.zipIdx do
      let some (.ctorInfo cv) ← lookup c
        | return bad (.malformed s!"constructor {ingressName c} of {ingressName v.cnst.name} is \
            missing or not a constructor")
      unless Ix.Name.beqRaw cv.induct v.cnst.name do
        return bad (.malformed s!"constructor {ingressName c} names another inductive")
      unless cv.cidx == j do return bad (.malformed "constructor index differs from its position")
      cs := cs.push cv
    ctors := ctors.push cs
  match blockRecursors first candidates with
  | .ok recs => return .inductive types ctors recs
  | .error _ => return bad (.declined "inductive block without a recursor in the input")

/-- Existing callers retain the exact stored-map lookup and grouping policy.
Effectful callers may propagate lookup errors without fabricating absence. -/
def inductiveGroup (env : Ix.Environment) (first : Ix.InductiveVal)
    (candidates : Array Ix.RecursorVal) : Group :=
  Id.run (inductiveGroupUsing (m := Id) (env.consts.get? ·) first candidates)

def isFamily : Ix.ConstantInfo → Bool
  | .inductInfo _ | .ctorInfo _ | .recInfo _ => true
  | _ => false

def isDefinition : Ix.ConstantInfo → Bool
  | .defnInfo _ | .thmInfo _ | .opaqueInfo _ => true
  | _ => false

/-- **Lean's name order**, structural (`Ix.Name.leanCmp`). It reads no hash. -/
abbrev nameCmp : Ix.Name → Ix.Name → Ordering := Ix.Name.leanCmp

/-- `names` before `names'` in Lean's name order, first name first. -/
def namesLt (names names' : Array Ix.Name) : Bool := Id.run do
  for (a, b) in names.zip names' do
    match nameCmp a b with
    | .lt => return true
    | .gt => return false
    | .eq => pure ()
  return names.size < names'.size

/-- The group of a strongly connected component's constants outside the
inductive families (none if it has none), its members in Lean's order
(`Ix.sourceOrderLt`: their positions in their Lean block's `all`, as the
compiler lays the block out). -/
def componentGroupUsing {m : Type → Type} [Monad m]
    (lookup : Ix.Name → m (Option Ix.ConstantInfo)) (members : Ix.Set Ix.Name) : m (Option Group) := do
  let cis ← members.toArray.filterMapM lookup
  let others := (cis.filter (!isFamily ·)).qsort fun a b =>
    Ix.sourceOrderLt (a.blockPosition, a.getCnst.name) (b.blockPosition, b.getCnst.name)
  let names := others.map (·.getCnst.name)
  return if others.isEmpty then none
  else if cis.any isFamily then some (.invalid names (.malformed "a block mixes inductives and definitions"))
  else if others.all isDefinition then some (.definitions others)
  else match others with
    | #[.axiomInfo v] => some (.axiom v)
    | #[.quotInfo v] => some (.quot v)
    | _ => some (.invalid names (.malformed "a cyclic block of axioms or quotients"))

def componentGroup (env : Ix.Environment) (members : Ix.Set Ix.Name) : Option Group :=
  Id.run (componentGroupUsing (m := Id) (env.consts.get? ·) members)

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
  let mut recsOf : Ix.Map TableName (Array Ix.RecursorVal) := {}
  for (_, ci) in env.consts do
    if let .recInfo rv := ci then
      if let some first := rv.all[0]? then
        recsOf := recsOf.insert first ((recsOf.getD first #[]).push rv)
  let mut out : Array Group := #[]
  for (n, ci) in env.consts do
    if let .inductInfo v := ci then
      if v.all[0]?.any (Ix.Name.beqRaw · n) then out := out.push (inductiveGroup env v (recsOf.getD n #[]))
  for (_, members) in blocks.blocks do
    if let some g := componentGroup env members then out := out.push g
  let mut claimed : Ix.Set TableName := {}
  for g in out do
    for n in g.names do claimed := claimed.insert n
  for (n, ci) in env.consts do
    unless claimed.contains n do out := out.push (unplaced n ci)
  return out

/-! ## Conversion

A group's terms are converted together (`ingressExprs`, one memo for the
terms of the group's constants that number their level parameters alike),
before any state is read; what the lowering reads is `Converted`. A
constant's level parameters are numbered by `Numbering`
(`Ix.LeanIngress.Expr`). -/

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
  cv : CVal .source
  value : CExpr .source
  kind : Ix.DefKind
  safety : Ix.DefinitionSafety
  hint : Ix.Kernel.ReducibilityHint
  deriving Inhabited

/-- A group's terms converted: what the lowering reads. -/
inductive Converted where
  | inductive (rb : BlockRead .source)
  /-- definition members, in the order they are lowered -/
  | definitions (members : Array DefMember)
  | axiom (cv : CVal .source)
  | quot (kind : Ix.Kernel.QuotKind) (cv : CVal .source)

/-- The conversion of terms, each under its constant's numbering: a run of
consecutive terms under one numbering is converted together (one memo). A
term conversion failure is a malformed group. The converted terms carry Lean's binder
names (`nameExprs`, display only: they are the conversions, `nameExprs_eq`). -/
def exprsOf (items : Array (Numbering × Ix.Expr)) : Except ReadError (Array (CExpr .source)) := do
  let flush (σ : Numbering) (es : Array Ix.Expr) (out : Array (CExpr .source)) :
      Except ReadError (Array (CExpr .source)) :=
    match ingressExprs σ.pos es.toList with
    | .ok ks => .ok (out ++ (nameExprs es.toList ks).toArray)
    | .error e => .error (.malformed s!"source term: {e}")
  let mut out : Array (CExpr .source) := Array.mkEmpty items.size
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
  let mut tys : Array (CVal .source × Nat × Nat) := #[]
  for v in types do
    tys := tys.push (⟨ingressKey v.cnst.name, (own v.cnst).params, ks[i]!⟩, v.numParams,
      v.numIndices)
    i := i + 1
  let mut cts : Array (CVal .source × Nat × Nat) := #[]
  let mut ctorNames : Array (List (CName .source)) := #[]
  for cs in ctors do
    let mut names : List (CName .source) := []
    for c in cs do
      let cv : CVal .source := ⟨ingressKey c.cnst.name, (own c.cnst).params, ks[i]!⟩
      i := i + 1
      unless nPd + c.numFields == Ix.Kernel.Reader.piTeleLen cv.type do
        throw (.malformed s!"constructor {cv.name} declares {c.numFields} fields at {nPd} parameters; \
          its type has {Ix.Kernel.Reader.piTeleLen cv.type} binders")
      cts := cts.push (cv, c.numParams, c.numFields)
      names := names ++ [cv.name]
    ctorNames := ctorNames.push names
  let mut rs : Array (CVal .source × RecCounts × List (Ix.Kernel.RecRule .source)) := #[]
  for r in recs do
    let cv : CVal .source := ⟨ingressKey r.cnst.name, (ofRec r).params, ks[i]!⟩
    i := i + 1
    let mut rules : List (Ix.Kernel.RecRule .source) := []
    for rule in r.rules do
      rules := rules ++ [Ix.Kernel.RecRule.mk (ingressKey rule.ctor) rule.nfields 0 .inert ks[i]!
        false false false]
      i := i + 1
    -- the motive a recursor eliminates, by Lean's naming: `T.rec` eliminates `T`
    let motive := match r.cnst.name with
      | .str T "rec" _ => types.findIdx? (Ix.Name.beqRaw ·.cnst.name T)
      | _ => none
    rs := rs.push (cv, ⟨r.numParams, r.numMotives, r.numMinors, r.numIndices, r.k, motive⟩, rules)
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
    ⟨⟨ingressKey ci.getCnst.name, (own ci).params, ks[2 * j]!⟩, ks[2 * j + 1]!, kind, safety,
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
    return .axiom ⟨ingressKey v.cnst.name, σ.params, ks[0]!⟩
  | .quot v => do
    let σ : Numbering := ⟨v.cnst.levelParams, false⟩
    let ks ← exprsOf #[(σ, v.cnst.type)]
    return .quot (quotKindOf v.kind) ⟨ingressKey v.cnst.name, σ.params, ks[0]!⟩
  | .invalid _ e => throw e

/-! ## Lowering -/

/-- A converted group's declarations, through the reader's back half: the
state is read, not changed (`State.commit` applies what the group taught). -/
def lower (st : State .source) : Converted → Ix.Kernel.Reader.ReadM (Read .source)
  | .inductive rb => Ix.Kernel.Reader.lowerInductive st rb
  | .definitions #[m] => do
    let (decl, rw) ← Ix.Kernel.Reader.lowerDefinition (some m.hint) st (st.heights.getD · 0)
      m.cv m.value m.kind m.safety
    pure { decls := #[decl], projRewrites := if rw then 1 else 0 }
  | .definitions ms => do
    let mut blockHeights : Std.HashMap (CName .source) Nat := {}
    let mut out : Array (CDecl .source) := #[]
    let mut rewrites := 0
    for m in ms do
      let heights : CName .source → Nat := fun n => blockHeights.getD n (st.heights.getD n 0)
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
  let exprs : Array (CExpr .source) := match c with
    | .inductive rb =>
      rb.types.map (·.1.type) ++ rb.ctors.map (·.1.type) ++
        rb.recs.flatMap fun (cv, _, rules) => #[cv.type] ++ rules.toArray.map (·.rhs)
    | .definitions ms => ms.flatMap fun m => #[m.cv.type, m.value]
    | .axiom cv | .quot _ cv => #[cv.type]
  let mut seen : Std.HashSet (CExpr .source) := {}
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
    | .letE t v b _ => todo := todo.push t |>.push v |>.push b
    | .proj _ _ b => todo := todo.push b
    | _ => pure ()
  return (nat, str)

/-- Whether an environment name spells a checker name (`ingressName n = m`),
decided without building the name. -/
def nameIsName : Ix.Name → Ix.Kernel.Name → Bool
  | .anonymous _, .anonymous => true
  | .str p s _, .str q t => s == t && nameIsName p q
  | .num p i _, .num q j => i == j && nameIsName p q
  | _, _ => false

/-- Whether an environment name is a checker key (`ingressKey n = k`), decided
without building the name: a role key by its role's Lean name, an input key
by its name when no role has that name, and never a derived key. -/
def nameIs (n : Ix.Name) : CName .source → Bool
  | .id m => nameIsName n m && !Ix.Kernel.Role.byLeanName.contains m
  | .role r => nameIsName n r.leanName
  | .aux .. => false

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
  let mut groupOf : Ix.Map TableName Nat := {}
  let mut supportOf : Std.HashMap (CName .source) Nat := {}
  for (g, i) in groups.zipIdx do
    for n in g.names do
      groupOf := groupOf.insert n i
      if let some k := supportNames.find? (nameIs n) then supportOf := supportOf.insert k i
  let mut hard : Array (Array Nat) := #[]
  let mut unplaced : Array (Option ReadError) := #[]
  for (g, i) in groups.zipIdx do
    let mut seenLo : Ix.Set TableName := {}
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
  let support (names : List (CName .source)) : Array Nat :=
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

/-- Each group's successors over the hard and literal edges, highest rank
first: the walk pushes them in this order, so it visits them lowest rank
first. -/
def succsByRank (g : Graph) (rank : Array Nat) : Array (Array Nat) :=
  (Array.range g.groups.size).map fun i =>
    (g.hard[i]! ++ g.literal[i]!).qsort fun a b => rank[a]! > rank[b]!

/-- **The order**: a depth-first postorder over the hard and literal edges
(`Order.dfs`, a structural walk with an explicit stack). The roots are
taken, and every group's successors visited, in Lean's name order of the
groups' constants (`namesLt`), so the order depends on the environment's
names and references and not on the groups' indices, which follow the
environment's hash-map iteration. Every group is in the order
(`orderOf_complete`). -/
def orderOf (g : Graph) : Array Nat :=
  let n := g.groups.size
  let byName := (Array.range n).qsort fun i j => namesLt g.groups[i]!.names g.groups[j]!.names
  let rank := byName.zipIdx.foldl (fun rank (i, r) => rank.set! i r) (Array.replicate n 0)
  let succs := succsByRank g rank
  Order.dfs n byName (succs[·]!) (Order.fuelOf n (Order.maxBelow n (succs[·]!.size)))

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
  name : CName .source
  position : Nat
  error : ReadError

instance : ToString IngressError where
  toString e := s!"{e.name} (group {e.position}): {e.error}"

/-- The reference graph of an environment's groups under its condensation,
with their conversions (`groupsOf`, `convert`, `graphOf`). -/
def graph (env : Ix.Environment) (blocks : Ix.CondensedBlocks) : Graph :=
  let groups := groupsOf env blocks
  graphOf blocks groups (groups.map convert)

/-! ## Canonical levels on the lowered declarations

Every level of a lowered declaration is put in the compiler's canonical form
(`canonLevelIn`, over each constant's own level-parameter list), after the
lowering: the reader's state, and so the in-process modeller of later
groups, keeps Lean's levels, as Lean's kernel builds its auxiliaries from
them. (Quotient Source instead canonicalizes every group before lowering it,
`Converted.quotient`, as the Ixon reader reads compiled, canonical levels.) -/

/-- A term's levels in canonical form, one memo per constant. -/
def canonExprM (lps : List Ix.Kernel.LevelParam) (e : CExpr .source) :
    StateM (Std.HashMap (CExpr .source) (CExpr .source)) (CExpr .source) :=
  fun memo => mapLevelsGo (canonLevelIn lps) memo e

def canonValM (cv : Ix.Kernel.ConstantVal .source) :
    StateM (Std.HashMap (CExpr .source) (CExpr .source)) (Ix.Kernel.ConstantVal .source) := do
  return { cv with type := ← canonExprM cv.levelParams cv.type }

/-- A constant's levels in canonical form, over its own level parameters. -/
def canonInfo (ci : Ix.Kernel.ConstantInfo .source) : Ix.Kernel.ConstantInfo .source :=
  (go ci).run' {}
where
  go : Ix.Kernel.ConstantInfo .source →
      StateM (Std.HashMap (CExpr .source) (CExpr .source)) (Ix.Kernel.ConstantInfo .source)
    | .axiomInfo cv => return .axiomInfo (← canonValM cv)
    | .defnInfo cv v h => return .defnInfo (← canonValM cv) (← canonExprM cv.levelParams v) h
    | .thmInfo cv v => return .thmInfo (← canonValM cv) (← canonExprM cv.levelParams v)
    | .indInfo cv caps => return .indInfo (← canonValM cv) caps
    | .ctorInfo cv nP nF => return .ctorInfo (← canonValM cv) nP nF
    | .recInfo cv m p rules => do
      let cv' ← canonValM cv
      let rules' ← rules.mapM fun r => do
        let fire ← match r.fire with
          | .nested lvls pins => do
            let ps ← pins.mapM (canonExprM cv.levelParams)
            pure (Ix.Kernel.RecRuleFire.nested (lvls.map (canonLevelIn cv.levelParams)) ps)
          | f => pure f
        return { r with rhs := ← canonExprM cv.levelParams r.rhs, fire }
      return .recInfo cv' m p rules'
    | .projInfo tbl => do
      let f := canonLevelIn tbl.levelParams
      return .projInfo { tbl with
        structSort := f tbl.structSort, guards := tbl.guards.map f,
        bodies := ← tbl.bodies.mapM (canonExprM tbl.levelParams) }

/-- **A lowered declaration's levels in the compiler's canonical form.** -/
def canonDecl : CDecl .source → CDecl .source
  | .axiomDecl cv => .axiomDecl ((canonValM cv).run' {})
  | .defnDecl cv v h => (do return .defnDecl (← canonValM cv) (← canonExprM cv.levelParams v) h :
      StateM _ _).run' {}
  | .thmDecl cv v => (do return .thmDecl (← canonValM cv) (← canonExprM cv.levelParams v) :
      StateM _ _).run' {}
  | .opaqueDecl cv v => (do return .opaqueDecl (← canonValM cv) (← canonExprM cv.levelParams v) :
      StateM _ _).run' {}
  | .basisDecl k => .basisDecl k
  | .indDecl block nP => .indDecl (block.map canonInfo) nP
  | .quotDecl k cv => .quotDecl k ((canonValM cv).run' {})

/-- Lower the scheduled groups of `g` from `st`, threading the reader's
state; the declarations come out with canonical levels (`canonDecl`). -/
def lowerAll (st : State .source) (g : Graph) (scheduled : Array (Nat × Except ReadError Converted)) :
    Except IngressError (State .source × Array (CDecl .source)) := do
  let mut st := st
  let mut out : Array (CDecl .source) := #[]
  for ((gi, c), i) in scheduled.zipIdx do
    let fail (e : ReadError) : IngressError := ⟨g.groups[gi]!.name, i, e⟩
    let c ← c.mapError fail
    let r ← (lower st c).mapError fail
    st := st.commit r
    out := out ++ r.decls.map canonDecl
  return (st, out)

/-- **The Source-mode ingress**: the declarations of an environment under its
condensation, in dependency order, lowered through the reader's back half
from the reader state `st` (the fold's input before `preparePrelude`). -/
def leanIngress (env : Ix.Environment) (blocks : Ix.CondensedBlocks) (st : State .source := {}) :
    Except IngressError (Array (CDecl .source)) := do
  let g := graph env blocks
  return (← lowerAll st g (scheduleOf g)).2

/-! ## The Source-mode check -/

/-- Ingress, prelude and checker failures, kept apart. -/
inductive SourceError where
  | ingress (error : IngressError)
  /-- the committed prelude does not load (a corrupted file) -/
  | prelude (reason : String)
  | kernel (error : Ix.Kernel.CheckError .source) (position : Nat)
  /-- quotient Source: a declaration (or an inductive group's block) meets an
  alias fiber's representative without being its declaration (`lowerAllCollapsed`) -/
  | collapse (error : CollapseError)
  /-- quotient Source: the reader state after the lowering holds, at a key the prelude's
  state holds, another entry than the prelude's (`State.keepsPrelude`): a stream's copy
  of a prelude declaration installs other state than the prelude's -/
  | preludeCopy

instance : ToString SourceError where
  toString
    | .ingress e => s!"ingress: {e}"
    | .prelude r => s!"prelude: {r}"
    | .kernel e p => s!"kernel at {p}: {e}"
    | .collapse e => s!"collapse: {e}"
    | .preludeCopy => "prelude copy: the stream's lowering leaves other reader entries than the prelude's at a prelude key"

/-- The fold's input: the ingress from the prelude's reader state, prepared by
`Frontend.preparePrelude` with the prelude's declarations. -/
def prepareSource (pre : Ix.Kernel.Reader.Prelude .source) (env : Ix.Environment)
    (blocks : Ix.CondensedBlocks) : Except SourceError (Array (CDecl .source)) := do
  let decls ← (leanIngress env blocks pre.state).mapError .ingress
  pure (Ix.Kernel.Frontend.preparePrelude pre.ix decls)

/-! ## Source mode's role table

**The table is fixed**: every role is bound to the constant under its Lean
name (`Role.leanName`). The ingress renames that constant to its role's key
(`ingressKey`, through `Ix.Kernel.Key.ofName`), as the Ixon reader renames a
bound address; a declaration under a role's name with another shape is
rejected or declined by the fold, as for Ixon.

**The evidence** is fixed too: the structural operations' `defeq` entries,
and for each well-founded operation the certificate theorems of
`IxC/Kernel/PinGen/Certs.lean` (`Ix.RoleEvidence.certTheorems`) under their
Lean names, **ingested with the environment**: an environment that imports
`IxC.Kernel.PinGen.Certs` carries them as ordinary declarations, which the
fold checks as theorems like any other. Each proof is closed over the
operation's dependency closure (`Ix.RoleEvidence.closedProofs`) before the
fold receives it, as the fold's locality condition requires. An operation
whose theorems are not in the environment, or do not close, gets no evidence,
and declines. -/

/-- Source mode's binding: role `r` is the constant named `r.leanName`. -/
def sourceBinding (r : Ix.Kernel.Role) : Ix.Kernel.Name := r.leanName

/-- **Source mode's evidence** over the prepared declarations, with the
reason each well-founded operation without evidence has none. -/
def sourceEvidenceReport (decls : Array (CDecl .source)) : Ix.Kernel.Evidences .source × List String := Id.run do
  let uni : Ix.RoleEvidence.Universe .source := decls.foldl Ix.RoleEvidence.Universe.add {}
  let lookMap := Ix.RoleEvidence.lookupOf decls
  let look : CName .source → Option (Ix.Kernel.ConstantInfo .source) := (lookMap[·]?)
  let mut ev : Ix.Kernel.Evidences .source :=
    Ix.RoleEvidence.defeqRoles.map fun r => (r, Ix.RoleEvidence.defeqEvidence r)
  let mut why : List String := []
  for (r, _) in Ix.RoleEvidence.certTheorems do
    match Ix.RoleEvidence.closedProofs decls uni look Ix.RoleEvidence.ofLeanName r with
    | .ok ps => ev := ev ++ [(r, ps.map fun p => .proof p)]
    | .error e => why := why ++ [s!"{repr r}: {e}"]
  return (ev, why)

/-- **Source mode's evidence** over the prepared declarations. -/
def sourceEvidence (decls : Array (CDecl .source)) : Ix.Kernel.Evidences .source := (sourceEvidenceReport decls).1

/-- The Source-mode check over an explicit prelude and evidence. -/
def checkSourceWith (pre : Ix.Kernel.Reader.Prelude .source) (ev : Ix.Kernel.Evidences .source)
    (env : Ix.Environment) (blocks : Ix.CondensedBlocks) : Except SourceError (Ix.Kernel.Env .source) := do
  let decls ← prepareSource pre env blocks
  (Ix.Kernel.Cached.checkDecls .verified ev decls).mapError fun (e, i) => .kernel e i

/-- **The Source-mode check**: `leanIngress` behind the committed prelude
(the Ixon reader's, whose constants carry Lean's names), then the verified
fold at Source mode's evidence (`sourceEvidence`: the certificate theorems the
environment carries, closed). -/
def checkSourceUsing (prelude : Except String (Ix.Kernel.Reader.Prelude .source)) (env : Ix.Environment)
    (blocks : Ix.CondensedBlocks) : Except SourceError (Ix.Kernel.Env .source) := do
  let pre ← prelude.mapError .prelude
  let decls ← prepareSource pre env blocks
  (Ix.Kernel.Cached.checkDecls .verified (sourceEvidence decls) decls).mapError
    fun (e, i) => .kernel e i

def checkSource (env : Ix.Environment) (blocks : Ix.CondensedBlocks) :
    Except SourceError (Ix.Kernel.Env .source) :=
  checkSourceUsing Ix.Kernel.Reader.builtinPrelude env blocks

/-- The Source-mode check at the pinned bundle evidence, over a source of preludes. -/
def checkSourceBundledUsing (prelude : Except String (Ix.Kernel.Reader.Prelude .source))
    (env : Ix.Environment) (blocks : Ix.CondensedBlocks) : Except SourceError (Ix.Kernel.Env .source) := do
  let pre ← prelude.mapError .prelude
  checkSourceWith pre (Ix.RoleEvidence.bundleEvidence ()) env blocks

/-- **The Source-mode check at the pinned bundle evidence** (owner, 2026-10-20):
the committed prelude, and the committed bundle's evidence
(`Ix.RoleEvidence.bundleEvidence`, RoleData's `sourceEvidence`: the verifier's
configuration, the Source twin of the role table's evidence), whatever the
input carries. `checkSource` takes its evidence from the certificate theorems
the input carries, which a closure of user roots never does, so it declines
every closure with a well-founded `Nat` operation; this check does not. -/
def checkSourceBundled (env : Ix.Environment) (blocks : Ix.CondensedBlocks) :
    Except SourceError (Ix.Kernel.Env .source) :=
  checkSourceBundledUsing Ix.Kernel.Reader.builtinPrelude env blocks

/-! ## Hint overrides

A definition's hint orders δ-unfolding only: the fold's soundness holds at
every hint, so a Source check under other hints still means that the
environment is well typed. The compiler ships one hint per address, merged
over an alias fiber (`Ixon.Env.anonHints`), where Lean has one per name;
Route A (B7, option (a1)) runs Source at the shipped hints, through
`checkSourceHinted` with the artifact's per-key hints. With no override it
is `checkSource` (`checkSourceHinted_none`). -/

/-- A converted group with its definitions' hints overridden where `hints`
gives one. -/
def Converted.withHints (hints : CName .source → Option Ix.Kernel.ReducibilityHint) :
    Converted → Converted
  | .definitions ms => .definitions (ms.map fun m =>
      match hints m.cv.name with
      | some h => { m with hint := h }
      | none => m)
  | c => c

/-- The reference graph, its definitions' hints overridden by `hints`. -/
def graphHinted (hints : CName .source → Option Ix.Kernel.ReducibilityHint) (env : Ix.Environment)
    (blocks : Ix.CondensedBlocks) : Graph :=
  let g := graph env blocks
  { g with converted := g.converted.map fun c => c.map (Converted.withHints hints) }

/-- `leanIngress` with the definitions' hints overridden by `hints`. -/
def leanIngressHinted (hints : CName .source → Option Ix.Kernel.ReducibilityHint)
    (env : Ix.Environment) (blocks : Ix.CondensedBlocks) (st : State .source := {}) :
    Except IngressError (Array (CDecl .source)) := do
  let g := graphHinted hints env blocks
  return (← lowerAll st g (scheduleOf g)).2

/-- `prepareSource` with the definitions' hints overridden by `hints`. -/
def prepareSourceHinted (hints : CName .source → Option Ix.Kernel.ReducibilityHint)
    (pre : Ix.Kernel.Reader.Prelude .source) (env : Ix.Environment)
    (blocks : Ix.CondensedBlocks) : Except SourceError (Array (CDecl .source)) := do
  let decls ← (leanIngressHinted hints env blocks pre.state).mapError .ingress
  pure (Ix.Kernel.Frontend.preparePrelude pre.ix decls)

/-- `checkSourceUsing` with the definitions' hints overridden by `hints`. -/
def checkSourceHintedUsing (prelude : Except String (Ix.Kernel.Reader.Prelude .source))
    (hints : CName .source → Option Ix.Kernel.ReducibilityHint) (env : Ix.Environment)
    (blocks : Ix.CondensedBlocks) : Except SourceError (Ix.Kernel.Env .source) := do
  let pre ← prelude.mapError .prelude
  let decls ← prepareSourceHinted hints pre env blocks
  (Ix.Kernel.Cached.checkDecls .verified (sourceEvidence decls) decls).mapError
    fun (e, i) => .kernel e i

/-- **The Source-mode check at hint overrides**: `checkSource`, every
definition whose key `hints` maps running that hint instead of Lean's. -/
def checkSourceHinted (hints : CName .source → Option Ix.Kernel.ReducibilityHint)
    (env : Ix.Environment) (blocks : Ix.CondensedBlocks) : Except SourceError (Ix.Kernel.Env .source) :=
  checkSourceHintedUsing Ix.Kernel.Reader.builtinPrelude hints env blocks

theorem Converted.withHints_none (c : Converted) : Converted.withHints (fun _ => none) c = c := by
  cases c with
  | definitions ms =>
    simp only [Converted.withHints]
    congr 1
    conv => rhs; rw [← Array.map_id ms]
    rfl
  | _ => rfl

theorem graphHinted_none (env : Ix.Environment) (blocks : Ix.CondensedBlocks) :
    graphHinted (fun _ => none) env blocks = graph env blocks := by
  have h : (fun c : Except ReadError Converted => c.map (Converted.withHints fun _ => none)) = id := by
    funext c
    cases c <;> simp [Except.map, Converted.withHints_none]
  simp only [graphHinted, h, Array.map_id]

theorem leanIngressHinted_none (env : Ix.Environment) (blocks : Ix.CondensedBlocks) (st : State .source) :
    leanIngressHinted (fun _ => none) env blocks st = leanIngress env blocks st := by
  simp only [leanIngressHinted, leanIngress, graphHinted_none]

theorem prepareSourceHinted_none :
    prepareSourceHinted (fun _ => none) = prepareSource := by
  funext pre env blocks
  simp only [prepareSourceHinted, prepareSource, leanIngressHinted_none]

/-- **With no override, the hinted check is `checkSource`.** -/
theorem checkSourceHinted_none (env : Ix.Environment) (blocks : Ix.CondensedBlocks) :
    checkSourceHinted (fun _ => none) env blocks = checkSource env blocks := by
  simp only [checkSourceHinted, checkSourceHintedUsing, checkSource, checkSourceUsing,
    prepareSourceHinted_none]

/-- Lean's hint as the checker's. -/
def hintOfLean : Lean.ReducibilityHints → Ix.Kernel.ReducibilityHint
  | .opaque => .opaque
  | .abbrev => .abbrev
  | .regular h => .regular h.toNat

/-- **The artifact's hints by Source key** (Route A, B7 (a1)): for every name
the artifact publishes (`Ixon.Env.named`), the hint it ships at that name's
address (`Ixon.Env.anonHints`; for an alias fiber, the merge of its names'
hints), under the name's Source key (`ingressKey`). A function of the
artifact's data only. -/
def fiberHintsMap (ixe : Ixon.Env) : Std.HashMap (CName .source) Ix.Kernel.ReducibilityHint :=
  ixe.named.fold (init := {}) fun m n named =>
    match ixe.anonHints.get? named.addr with
    | some h => m.insert (ingressKey n) (hintOfLean h)
    | none => m

/-- The hint Source runs for the key `k` under the artifact `ixe`
(`checkSourceHinted (fiberHints ixe)`): the one the artifact ships at the
address it publishes for `k`'s name, so the two sides run one hint per alias
fiber. -/
def fiberHints (ixe : Ixon.Env) (k : CName .source) : Option Ix.Kernel.ReducibilityHint :=
  (fiberHintsMap ixe)[k]?

/-! ## Quotient Source (`ALPHA-COLLAPSE.md` §8.4)

The Source-mode check with every alias fiber collapsed to its representative
(`Ix.LeanIngress.Collapse`), **before lowering**: every group, converted with
its hints overridden as `leanIngressHinted` overrides them (so hints are looked
up by the input's names), is renamed to its fibers' representatives and given
the compiler's canonical levels (`Converted.quotient`: `Converted.substKeys`,
then `Converted.canon`; `graphCollapsed`), and only then lowered
(`lowerAllCollapsed`), so the reader's state and the in-process modeller see
representatives and canonical levels only, as the Ixon reader sees the
compiled group:
* an inductive group whose block is a kept group's (every name of it that
  group's, the block equal: `BlockRead.beqF`) is that group's alias, never
  lowered or committed, so the modeller never runs on it; one that meets a kept
  name otherwise is refused;
* every other group is lowered, and its declarations are collapsed one by one
  (`CollapseState.step`: kept, dropped when equal to the kept declaration of
  their names, `FiberHyp` decided, or refused) before the reader's state
  learns the kept ones. They are not canonicalized again: the modeller's
  records stay as it builds them, as the Ixon reader keeps them.
Then the prelude is prepared and the verified fold runs, at Source mode's
evidence over the collapsed declarations. The fibers and the hints are data: at
an artifact, its alias fibers (`fiberAlias`, role-aware) and its per-fiber
hints (`fiberHints`), so that the two sides run one declaration and one hint
per address. Grouping and order are the ingress's own (components,
`componentGroup`; `scheduleOf` on the input's names). -/

/-- A definition member renamed to its fibers' representatives. -/
def DefMember.substKeys (ρ : FiberMap) (m : DefMember) : DefMember :=
  { m with cv := ConstantVal.substKeys ρ m.cv, value := Expr.substKeys ρ m.value }

/-- An inductive block, as read, renamed to its fibers' representatives. -/
def BlockRead.substKeys (ρ : FiberMap) (rb : BlockRead .source) : BlockRead .source :=
  { rb with
    types := rb.types.map fun (cv, p, i) => (ConstantVal.substKeys ρ cv, p, i)
    ctors := rb.ctors.map fun (cv, p, f) => (ConstantVal.substKeys ρ cv, p, f)
    ctorNames := rb.ctorNames.map (·.map (Key.subst ρ))
    recs := rb.recs.map fun (cv, rc, rules) =>
      (ConstantVal.substKeys ρ cv, rc, rules.map (RecRule.substKeys ρ)) }

/-- **A converted group renamed to its fibers' representatives** (`Key.subst`
at every key it declares or mentions). -/
def Converted.substKeys (ρ : FiberMap) : Converted → Converted
  | .inductive rb => .inductive (BlockRead.substKeys ρ rb)
  | .definitions ms => .definitions (ms.map (DefMember.substKeys ρ))
  | .axiom cv => .axiom (ConstantVal.substKeys ρ cv)
  | .quot k cv => .quot k (ConstantVal.substKeys ρ cv)

/-- A block's levels in the compiler's canonical form, each constant's over its
own level parameters, as `canonDecl` puts its `indDecl`'s (`canonInfo`). -/
def BlockRead.canon (rb : BlockRead .source) : BlockRead .source :=
  let cv (c : CVal .source) : CVal .source := (canonValM c).run' {}
  { rb with
    types := rb.types.map fun (c, p, i) => (cv c, p, i)
    ctors := rb.ctors.map fun (c, p, f) => (cv c, p, f)
    recs := rb.recs.map fun (c, rc, rules) =>
      match canonInfo (.recInfo c 0 0 rules) with
      | .recInfo c' _ _ rules' => (c', rc, rules')
      | _ => (c, rc, rules) }

/-- A definition member's levels in the compiler's canonical form, over its own
level parameters, as `canonDecl` puts its declaration's. -/
def DefMember.canon (m : DefMember) : DefMember :=
  (do return { m with cv := ← canonValM m.cv, value := ← canonExprM m.cv.levelParams m.value } :
    StateM _ _).run' {}

/-- **A converted group's levels in the compiler's canonical form**, each
constant's over its own level parameters (`canonLevelIn`, the form the compiler
stores and the Ixon reader reads). -/
def Converted.canon : Converted → Converted
  | .inductive rb => .inductive (BlockRead.canon rb)
  | .definitions ms => .definitions (ms.map DefMember.canon)
  | .axiom cv => .axiom ((canonValM cv).run' {})
  | .quot k cv => .quot k ((canonValM cv).run' {})

/-- **A converted group as quotient Source lowers it**: renamed to its fibers'
representatives (`Converted.substKeys`), then with canonical levels
(`Converted.canon`). -/
def Converted.quotient (ρ : FiberMap) (c : Converted) : Converted :=
  Converted.canon (Converted.substKeys ρ c)

/-- **Quotient Source's graph**: `graphHinted`'s, every conversion renamed to its
fibers' representatives with canonical levels after the hint override
(`Converted.quotient`). The groups, edges and order are the input's. -/
def graphCollapsed (ρ : FiberMap) (hints : CName .source → Option Ix.Kernel.ReducibilityHint)
    (env : Ix.Environment) (blocks : Ix.CondensedBlocks) : Graph :=
  let g := graphHinted hints env blocks
  { g with converted := g.converted.map fun c => c.map (Converted.quotient ρ) }

/-- The names a block declares: its types', constructors' and recursors', in the
order its `indDecl` declares them. -/
def BlockRead.names (rb : BlockRead .source) : List (CName .source) :=
  rb.types.toList.map (·.1.name) ++ rb.ctors.toList.map (·.1.name) ++
    rb.recs.toList.map (·.1.name)

/-- Two blocks' types or constructors are equal (the memoised term comparison). -/
def headsBeqF : List (CVal .source × Nat × Nat) → List (CVal .source × Nat × Nat) → Bool
  | [], [] => true
  | (c, p, i) :: as, (c', p', i') :: bs =>
    ConstantVal.beqF c c' && p == p' && i == i' && headsBeqF as bs
  | _, _ => false

/-- Two recursors' declared counts are equal. -/
def RecCounts.beqF (a b : RecCounts) : Bool :=
  a.params == b.params && a.motives == b.motives && a.minors == b.minors &&
    a.indices == b.indices && a.k == b.k && a.motive == b.motive

/-- Two blocks' recursors are equal (the memoised term comparison). -/
def recsBeqF : List (CVal .source × RecCounts × List (Ix.Kernel.RecRule .source)) →
    List (CVal .source × RecCounts × List (Ix.Kernel.RecRule .source)) → Bool
  | [], [] => true
  | (c, rc, rs) :: as, (c', rc', rs') :: bs =>
    ConstantVal.beqF c c' && RecCounts.beqF rc rc' && RecRule.listBeqF rs rs' && recsBeqF as bs
  | _, _ => false

/-- **Two blocks are equal**, deciding `a = b` with the memoised term comparison
(`BlockRead.beqF_eq_true`). -/
def BlockRead.beqF (a b : BlockRead .source) : Bool :=
  a.numParams == b.numParams && headsBeqF a.types.toList b.types.toList &&
    headsBeqF a.ctors.toList b.ctors.toList && decide (a.ctorNames = b.ctorNames) &&
    recsBeqF a.recs.toList b.recs.toList

theorem headsBeqF_eq_true : ∀ {as bs : List (CVal .source × Nat × Nat)},
    headsBeqF as bs = true → as = bs
  | [], [], _ => rfl
  | (c, p, i) :: as, (c', p', i') :: bs, h => by
    simp only [headsBeqF, ConstantVal.beqF_eq, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, h⟩ := h
    rw [headsBeqF_eq_true h]

theorem RecCounts.beqF_eq_true {a b : RecCounts} (h : RecCounts.beqF a b = true) : a = b := by
  obtain ⟨_, _, _, _, _, _⟩ := a
  obtain ⟨_, _, _, _, _, _⟩ := b
  simp only [RecCounts.beqF, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := h
  rfl

theorem recsBeqF_eq_true :
    ∀ {as bs : List (CVal .source × RecCounts × List (Ix.Kernel.RecRule .source))},
      recsBeqF as bs = true → as = bs
  | [], [], _ => rfl
  | (c, rc, rs) :: as, (c', rc', rs') :: bs, h => by
    simp only [recsBeqF, ConstantVal.beqF_eq, RecRule.listBeqF_eq, Bool.and_eq_true,
      decide_eq_true_eq] at h
    obtain ⟨⟨⟨rfl, hrc⟩, rfl⟩, h⟩ := h
    rw [RecCounts.beqF_eq_true hrc, recsBeqF_eq_true h]

/-- **`BlockRead.beqF` decides equality.** -/
theorem BlockRead.beqF_eq_true {a b : BlockRead .source} (h : BlockRead.beqF a b = true) :
    a = b := by
  obtain ⟨n, ts, cs, cn, rs⟩ := a
  obtain ⟨n', ts', cs', cn', rs'⟩ := b
  simp only [BlockRead.beqF, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨rfl, hts⟩, hcs⟩, rfl⟩, hrs⟩ := h
  rw [Array.toList_inj.mp (headsBeqF_eq_true hts), Array.toList_inj.mp (headsBeqF_eq_true hcs),
    Array.toList_inj.mp (recsBeqF_eq_true hrs)]

/-- The inductive groups quotient Source's lowering kept: each one's block (as
lowered: renamed, canonical levels), and the kept block each of their names
belongs to. -/
structure KeptBlocks where
  blocks : Array (BlockRead .source) := #[]
  blockOf : Std.HashMap (CName .source) Nat := {}

/-- A kept inductive group's block recorded. -/
def KeptBlocks.push (kb : KeptBlocks) (rb : BlockRead .source) : KeptBlocks :=
  let ⟨blocks, blockOf⟩ := kb
  let i := blocks.size
  { blocks := blocks.push rb,
    blockOf := (BlockRead.names rb).foldl (fun m n => m.insert n i) blockOf }

/-- **An inductive group against the kept ones** (`FiberHyp` at the block,
decided), both as quotient Source lowers them (`Converted.quotient`): `none`
when none of its names is kept yet (it is lowered); `some k` when every name of
it is kept block `k`'s, and its block is `k`'s (it is `k`'s alias, not
lowered); otherwise refused, reported at `first`. -/
def KeptBlocks.alias (kb : KeptBlocks) (s : CollapseState) (first : CName .source)
    (rb : BlockRead .source) : Except CollapseError (Option Nat) :=
  let ns := BlockRead.names rb
  let refuse : CollapseError := .mismatch first (ns.head?.getD (.id .anonymous))
  if !ns.any s.owner.contains then .ok none
  else match ns.head?.bind (kb.blockOf[·]?) with
    | some k =>
      if ns.all (kb.blockOf[·]? == some k) && (kb.blocks[k]?.any (BlockRead.beqF rb)) then
        .ok (some k)
      else .error refuse
    | none => .error refuse

/-- A lowered group's declarations, as lowered (no level is rewritten: the group
was canonical before lowering, and the modeller's records stay as it builds
them), collapsed one by one (`CollapseState.step`, refusals reported at
`first`): the collapse's new state, and the reading's kept part (with how many
of them the modeller generated: what the reader's state learns) with the names
of the dropped ones. A refusal comes back with the state as it was before the
group (`CollapseState.restore`). -/
def collapseRead (s : CollapseState) (first : CName .source) (r : Read .source) :
    CollapseState × Except CollapseError (Read .source × Array (CName .source)) := Id.run do
  let n := s.kept.size
  let mut s := s
  let mut keep : Array (CDecl .source) := #[]
  let mut gen := 0
  let mut dropped : Array (CName .source) := #[]
  for (d, j) in r.decls.zipIdx do
    let (s', res) := s.step first d
    s := s'
    match res with
    | .error e => return (s.restore n, .error e)
    | .ok true =>
      keep := keep.push d
      if j < r.generated then gen := gen + 1
    | .ok false => dropped := dropped.push (d.names.head?.getD (.id .anonymous))
  return (s, .ok ({ r with decls := keep, generated := gen }, dropped))

/-- What one renamed group does in quotient Source's lowering. Every outcome
carries the collapse's state and kept blocks on (a caller that threads them
never holds the old ones, so they are updated in place). -/
inductive CollapseStep where
  /-- kept block `k`'s alias: not lowered, nothing learned -/
  | alias (k : Nat) (s : CollapseState) (kb : KeptBlocks)
  /-- lowered and collapsed: the collapse's new state and kept blocks, the kept
  part of the reading (what the reader's state learns), and the names of the
  dropped declarations -/
  | lowered (s : CollapseState) (kb : KeptBlocks) (r : Read .source) (dropped : Array (CName .source))
  /-- refused (an ingress failure or a collapse mismatch), the state as it was -/
  | refused (e : SourceError) (s : CollapseState) (kb : KeptBlocks)

/-- **One renamed group of quotient Source's lowering** (`c`, at `position` in
the order, reported under the input's name `first`), from the reader's state
`st`: an inductive group that is a kept block's alias is not lowered
(`KeptBlocks.alias`); any other group is lowered (`lower`) and its declarations
collapsed (`collapseRead`). A refusal is an ingress failure or a collapse
mismatch. -/
def collapseGroup (st : State .source) (s : CollapseState) (kb : KeptBlocks)
    (first : CName .source) (position : Nat) (c : Except ReadError Converted) : CollapseStep :=
  let fail (e : ReadError) : SourceError := .ingress ⟨first, position, e⟩
  match c with
  | .error e => .refused (fail e) s kb
  | .ok c =>
    let blockAlias : Except CollapseError (Option Nat) := match c with
      | .inductive rb => kb.alias s first rb
      | _ => .ok none
    match blockAlias with
    | .error e => .refused (.collapse e) s kb
    | .ok (some k) => .alias k s kb
    | .ok none =>
      match lower st c with
      | .error e => .refused (fail e) s kb
      | .ok r =>
        match collapseRead s first r with
        | (s, .error e) => .refused (.collapse e) s kb
        | (s, .ok (r, dropped)) =>
          let kb := match c with
            | .inductive rb => kb.push rb
            | _ => kb
          .lowered s kb r dropped

/-- **Quotient Source's lowering**: the scheduled groups of a renamed graph
(`graphCollapsed`) from `st`, one by one (`collapseGroup`), threading the
reader's state, which learns only the kept declarations; the first refusal ends
it. The kept declarations, in order, as lowered. -/
def lowerAllCollapsed (st : State .source) (g : Graph)
    (scheduled : Array (Nat × Except ReadError Converted)) :
    Except SourceError (State .source × Array (CDecl .source)) := do
  let mut st := st
  let mut s : CollapseState := {}
  let mut kb : KeptBlocks := {}
  for ((gi, c), i) in scheduled.zipIdx do
    match collapseGroup st s kb g.groups[gi]!.name i c with
    | .refused e _ _ => throw e
    | .alias _ s' kb' =>
      s := s'
      kb := kb'
    | .lowered s' kb' r _ =>
      s := s'
      kb := kb'
      st := st.commit r
  return (st, s.kept)

/-- **Quotient Source's fold input**: the groups at `hints`, renamed by `ρ`
with canonical levels before they are lowered and collapsed (`graphCollapsed`,
`lowerAllCollapsed`), then prepared behind the prelude. The reader state the
lowering ends in must keep the prelude's entries (`State.keepsPrelude`): the
stream's own copies of the prelude's declarations (Lean's `Nat` at `.role nat`)
install exactly what the prelude installed there, or the stream is refused
(`SourceError.preludeCopy`). -/
def prepareSourceCollapsed (ρ : FiberMap) (hints : CName .source → Option Ix.Kernel.ReducibilityHint)
    (pre : Ix.Kernel.Reader.Prelude .source) (env : Ix.Environment)
    (blocks : Ix.CondensedBlocks) : Except SourceError (Array (CDecl .source)) := do
  let g := graphCollapsed ρ hints env blocks
  let (st, decls) ← lowerAllCollapsed pre.state g (scheduleOf g)
  if Ix.Kernel.Reader.State.keepsPrelude pre.state st then
    pure (Ix.Kernel.Frontend.preparePrelude pre.ix decls)
  else throw .preludeCopy

/-- **Quotient Source's fold input is a lowering that keeps the prelude**: the
lowering succeeded, its final reader state keeps the prelude's entries
(`State.keepsPrelude_iff`), and the input is its declarations prepared. -/
theorem prepareSourceCollapsed_keepsPrelude {ρ : FiberMap}
    {hints : CName .source → Option Ix.Kernel.ReducibilityHint}
    {pre : Ix.Kernel.Reader.Prelude .source} {env : Ix.Environment} {blocks : Ix.CondensedBlocks}
    {ds : Array (CDecl .source)} (h : prepareSourceCollapsed ρ hints pre env blocks = .ok ds) :
    ∃ st decls, lowerAllCollapsed pre.state (graphCollapsed ρ hints env blocks)
        (scheduleOf (graphCollapsed ρ hints env blocks)) = .ok (st, decls) ∧
      Ix.Kernel.Reader.State.keepsPrelude pre.state st = true ∧
      ds = Ix.Kernel.Frontend.preparePrelude pre.ix decls := by
  unfold prepareSourceCollapsed at h
  cases hl : lowerAllCollapsed pre.state (graphCollapsed ρ hints env blocks)
      (scheduleOf (graphCollapsed ρ hints env blocks)) with
  | error e => simp [hl, bind, Except.bind] at h
  | ok p =>
    obtain ⟨st, decls⟩ := p
    simp only [hl, bind, Except.bind] at h
    split at h
    · rename_i hk
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact ⟨st, decls, rfl, hk, h.symm⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- Quotient Source over an explicit prelude, fiber map and hints. -/
def checkSourceCollapsedUsing (prelude : Except String (Ix.Kernel.Reader.Prelude .source))
    (ρ : FiberMap) (hints : CName .source → Option Ix.Kernel.ReducibilityHint)
    (env : Ix.Environment) (blocks : Ix.CondensedBlocks) :
    Except SourceError (Ix.Kernel.Env .source) := do
  let pre ← prelude.mapError .prelude
  let decls ← prepareSourceCollapsed ρ hints pre env blocks
  (Ix.Kernel.Cached.checkDecls .verified (sourceEvidence decls) decls).mapError
    fun (e, i) => .kernel e i

/-- **Quotient Source at a compiled artifact**: the committed prelude, the
artifact's alias fibers (`fiberAlias`, role-aware) and its per-fiber hints
(`fiberHints`). -/
def checkSourceCollapsed (ixe : Ixon.Env) (env : Ix.Environment) (blocks : Ix.CondensedBlocks) :
    Except SourceError (Ix.Kernel.Env .source) :=
  let hints := fiberHintsMap ixe
  checkSourceCollapsedUsing Ix.Kernel.Reader.builtinPrelude (fiberAlias ixe) (hints[·]?) env blocks

/-- Evidence renamed onto the fiber representatives (`Key.subst`, `Expr.substKeys`): the
bundle's certificate theorems mention constants by their input keys, which quotient
Source renames. -/
def evidenceSubst (ρ : FiberMap) (ev : Ix.Kernel.Evidences .source) : Ix.Kernel.Evidences .source :=
  ev.map fun (r, es) => (r, es.map fun
    | .defeq => .defeq
    | .proof (k, p) => .proof (Key.subst ρ k, Expr.substKeys ρ p))

/-- Quotient Source at the pinned bundle evidence, over an explicit prelude source,
fiber map and hints. -/
def checkSourceCollapsedBundledUsing (prelude : Except String (Ix.Kernel.Reader.Prelude .source))
    (ρ : FiberMap) (hints : CName .source → Option Ix.Kernel.ReducibilityHint)
    (env : Ix.Environment) (blocks : Ix.CondensedBlocks) :
    Except SourceError (Ix.Kernel.Env .source) := do
  let pre ← prelude.mapError .prelude
  let decls ← prepareSourceCollapsed ρ hints pre env blocks
  (Ix.Kernel.Cached.checkDecls .verified (evidenceSubst ρ (Ix.RoleEvidence.quotientEvidence ())) decls).mapError
    fun (e, i) => .kernel e i

/-- **Quotient Source at a compiled artifact, at the pinned bundle evidence**
(`checkSourceCollapsed` at `Ix.RoleEvidence.quotientEvidence` renamed onto the fiber
representatives, as `checkSourceBundled` is `checkSource` at it). -/
def checkSourceCollapsedBundled (ixe : Ixon.Env) (env : Ix.Environment) (blocks : Ix.CondensedBlocks) :
    Except SourceError (Ix.Kernel.Env .source) :=
  let hints := fiberHintsMap ixe
  checkSourceCollapsedBundledUsing Ix.Kernel.Reader.builtinPrelude (fiberAlias ixe) (hints[·]?) env blocks

/-- **Quotient Source at a compiled artifact, the role read off the table** `t`
(`fiberAliasAt` at `roleAtMap t`): an alias of a role's content is that role's
even where its fiber holds no role name. -/
def checkSourceCollapsedAt (ixe : Ixon.Env) (t : Ix.Kernel.RoleTable) (env : Ix.Environment)
    (blocks : Ix.CondensedBlocks) : Except SourceError (Ix.Kernel.Env .source) :=
  let hints := fiberHintsMap ixe
  checkSourceCollapsedUsing Ix.Kernel.Reader.builtinPrelude (fiberAliasAt ixe (roleAtMap t))
    (hints[·]?) env blocks

/-! ## The bundle's evidence at the artifact's addresses

Quotient Source checks with the committed quotient bundle's evidence
(`Ix.RoleEvidence.quotientEvidence`), whose proofs name the bundle's constants:
the certificate theorems and the constants they cite, some of which the artifact
does not publish. The bundle is the default table's own evidence records read by
name: the address its names table (`RoleData.quotientNames`) gives a name is the
content address in the compiled Init that the records cite. The renaming onto
the artifact's keys sends a published name to its content address in the
artifact (`addrOf`) and a bundle-only name to its **bundle address**, the one the
names table gives it. Two facts make that injective: the names table is a map
from addresses to names, so two names never share a bundle address in it
(`bundleAddrs_inj`, proved from the table, no collision resistance assumed); and
no bundle-only name's bundle address is an address the artifact publishes
(`bundleDisjointB`, decided, checked by `collapsedChecks`). Where every published
name the records cite sits at the address they cite, the renamed evidence is the
Ixon run's. -/

/-- **The bundle's addresses by Source name** (the names table, inverted). -/
def bundleAddrs (b : Ix.RoleEvidence.Bundle) : Std.HashMap Ix.Kernel.Name Address :=
  b.names.fold (fun m a n => m.insert (Ix.Kernel.Name.ofLeanName n) a) {}

/-- The addresses an artifact publishes. -/
def publishedAddrs (ixe : Ixon.Env) : Std.HashSet Address :=
  (sourceAddrs ixe).fold (fun s _ a => s.insert a) {}

/-- **No bundle-only name's hash is an address the artifact publishes** (decided). -/
def bundleDisjointB (ixe : Ixon.Env) (b : Ix.RoleEvidence.Bundle) : Bool :=
  let pub := publishedAddrs ixe
  let src := sourceAddrs ixe
  (bundleAddrs b).toList.all fun (n, a) => src.contains n || !pub.contains a

/-- **Is `n` a representative of the artifact**: no role's name, published
(`src`, the artifact's `sourceAddrs`), and fixed by the fiber map `ρ`. -/
def qRepAtB (src : Std.HashMap Ix.Kernel.Name Address) (ρ : FiberMap) (n : Ix.Kernel.Name) : Bool :=
  roleOf n == none && src.contains n && Key.subst ρ (.id n) == .id n

/-- **Is `n` a representative or a bundle-only name** (no role's name, not
published, and among the bundle's names `ba`). -/
def qEvB (src : Std.HashMap Ix.Kernel.Name Address) (ρ : FiberMap)
    (ba : Std.HashMap Ix.Kernel.Name Address) (n : Ix.Kernel.Name) : Bool :=
  qRepAtB src ρ n || (roleOf n == none && !src.contains n && ba.contains n)

/-- **The checks that make quotient Source's prepared stream `ds` a renaming onto
a compiled artifact's keys**, the role read off the table `t`:
* every key of `ds` is a representative (`qRepAtB`);
* the bundle is disjoint from the artifact: no bundle-only name's hash is an
  address the artifact publishes (`bundleDisjointB`);
* every key of the bundle's evidence, renamed onto the representatives, is a
  representative or a bundle-only name (`qEvB`).
A failure is a decline (`SourceError.collapse`). -/
def collapsedChecksWith (ixe : Ixon.Env) (t : Ix.Kernel.RoleTable) (b : Ix.RoleEvidence.Bundle)
    (ev : Ix.Kernel.Evidences .source) (ds : Array (CDecl .source)) : Option CollapseError :=
  let ρ := fiberAliasAt ixe (roleAtMap t)
  let src := sourceAddrs ixe
  if !declsGoodB (qRepAtB src ρ) ds then some .notRepresentative
  else if !bundleDisjointB ixe b then some .bundleAlias
  else if !evidenceGoodB (qEvB src ρ (bundleAddrs b)) (evidenceSubst ρ ev) then some .evidence
  else none

/-- `collapsedChecksWith` over a bundle source and its evidence (the committed
ones in `prepareSourceCollapsedAt`; parameters here, as the prelude is in the
`…Using` checks, so that statements about the checks never unfold the
committed data). -/
def collapsedChecksUsing (bundle : Except String Ix.RoleEvidence.Bundle)
    (ev : Ix.Kernel.Evidences .source) (ixe : Ixon.Env) (t : Ix.Kernel.RoleTable)
    (ds : Array (CDecl .source)) : Except SourceError Unit :=
  match bundle with
  | .error e => .error (.prelude e)
  | .ok b =>
    match collapsedChecksWith ixe t b ev ds with
    | some e => .error (.collapse e)
    | none => .ok ()

/-- **Quotient Source's prepared stream at a compiled artifact**, over a bundle
source and its evidence: the table rule's collapse (`fiberAliasAt`), then the
checks that make it a renaming onto the artifact's keys (`collapsedChecksWith`). -/
def prepareSourceCollapsedAtUsing (bundle : Except String Ix.RoleEvidence.Bundle)
    (ev : Ix.Kernel.Evidences .source) (ixe : Ixon.Env) (t : Ix.Kernel.RoleTable)
    (hints : CName .source → Option Ix.Kernel.ReducibilityHint)
    (pre : Ix.Kernel.Reader.Prelude .source) (env : Ix.Environment)
    (blocks : Ix.CondensedBlocks) : Except SourceError (Array (CDecl .source)) :=
  match prepareSourceCollapsed (fiberAliasAt ixe (roleAtMap t)) hints pre env blocks with
  | .error e => .error e
  | .ok ds =>
    match collapsedChecksUsing bundle ev ixe t ds with
    | .error e => .error e
    | .ok () => .ok ds

/-- **Quotient Source's prepared stream at a compiled artifact**, the role read
off the table `t`, at the committed bundle and its evidence
(`prepareSourceCollapsedAtUsing`). -/
def prepareSourceCollapsedAt (ixe : Ixon.Env) (t : Ix.Kernel.RoleTable)
    (hints : CName .source → Option Ix.Kernel.ReducibilityHint)
    (pre : Ix.Kernel.Reader.Prelude .source) (env : Ix.Environment)
    (blocks : Ix.CondensedBlocks) : Except SourceError (Array (CDecl .source)) :=
  prepareSourceCollapsedAtUsing (Ix.RoleEvidence.quotientBundle ()) (Ix.RoleEvidence.quotientEvidence ())
    ixe t hints pre env blocks

/-- `checkSourceCollapsedBundledAt` over explicit sources: the prelude, the
bundle and its evidence. -/
def checkSourceCollapsedBundledAtUsing (prelude : Except String (Ix.Kernel.Reader.Prelude .source))
    (bundle : Except String Ix.RoleEvidence.Bundle) (ev : Ix.Kernel.Evidences .source)
    (ixe : Ixon.Env) (t : Ix.Kernel.RoleTable) (env : Ix.Environment) (blocks : Ix.CondensedBlocks) :
    Except SourceError (Ix.Kernel.Env .source) :=
  match prelude with
  | .error e => .error (.prelude e)
  | .ok pre =>
    let hints := fiberHintsMap ixe
    match prepareSourceCollapsedAtUsing bundle ev ixe t (hints[·]?) pre env blocks with
    | .error e => .error e
    | .ok decls =>
      match Ix.Kernel.Cached.checkDecls .verified
          (evidenceSubst (fiberAliasAt ixe (roleAtMap t)) ev) decls with
      | .error (e, i) => .error (.kernel e i)
      | .ok kenv => .ok kenv

/-- `checkSourceCollapsedBundled`, the role read off the table `t`, on the
checked prepared stream (`prepareSourceCollapsedAt`): at the committed prelude,
bundle and evidence. -/
def checkSourceCollapsedBundledAt (ixe : Ixon.Env) (t : Ix.Kernel.RoleTable) (env : Ix.Environment)
    (blocks : Ix.CondensedBlocks) : Except SourceError (Ix.Kernel.Env .source) :=
  checkSourceCollapsedBundledAtUsing Ix.Kernel.Reader.builtinPrelude (Ix.RoleEvidence.quotientBundle ())
    (Ix.RoleEvidence.quotientEvidence ()) ixe t env blocks

/-! ## The typing tier: partial and unsafe declarations

`checkSource` declines every group with a member that is not safe. The
**tiered** check gives a group of `partial` definitions (Lean's
`_unsafe_rec` companions), of `unsafe` definitions, an unsafe opaque and an
unsafe axiom the typing tier's verdict instead (`Ix.Kernel.Tier`): the
logical groups are checked exactly as `checkSource` checks them, and then
the tier groups, at the accepted environment's index, staged as Lean's
lattice requires (`Tier.staged`), with every tier constant opaque. Unsafe
inductives stay logical and decline, as in `checkSource`.

* **The partition** (`isTierGroup`): a definition group with a member that
  is not safe, or an unsafe axiom. It decides coverage only.
* **Order.** The groups are ordered as `leanIngress` orders them; a tier
  group is converted by the tier's conversion (`convertTier`: the same term
  conversion, no safety policy, no definition order, since the tier installs
  a block's headers before its values) behind the schedule's placement
  checks (an unplaced reference, a cycle through another group).
* **The fence.** A logical group that references a tier group is refused
  with the reason (`TierSourceError.fence`). Without that test it would still
  be refused: the fold resolves every term it stores, and a tier constant is
  never installed in the logical environment. -/

open Ix.Kernel.Tier (TierDecl TierConst)

/-- A definition's safety in the tier: anything but safe. -/
def tierSafetyOf? : Lean.DefinitionSafety → Option Ix.Kernel.Tier.Safety
  | .partial => some .part
  | .unsafe => some .unsaf
  | .safe => none

/-- **A tier group**: a definition group with a member that is not safe (a
`partial` or `unsafe` definition, or an unsafe opaque), or an unsafe axiom.
Unsafe inductives are not: they stay logical, where the reader declines
them. -/
def isTierGroup : Group → Bool
  | .definitions ms => ms.any fun
    | .defnInfo v => (tierSafetyOf? v.safety).isSome
    | .opaqueInfo v => v.isUnsafe
    | _ => false
  | .axiom v => v.isUnsafe
  | _ => false

/-- **A tier group's conversion**, each header and value under its own
numbering, as `convertDefinitions` converts them, in the group's order: an
unsafe axiom, its header; a lone unsafe opaque, itself; otherwise a
definition block, every member a definition of the first member's safety,
which is not safe (else declined: a mixed-safety block, a theorem, or an
opaque in a block). -/
def convertTier : Group → Except ReadError (TierDecl .source)
  | .axiom v => do
    let σ : Numbering := ⟨v.cnst.levelParams, false⟩
    let ks ← exprsOf #[(σ, v.cnst.type)]
    return .unsafeAxiom ⟨ingressKey v.cnst.name, σ.params, ks[0]!⟩
  | .definitions #[.opaqueInfo v] => do
    unless v.isUnsafe do throw (.declined "tier: a safe opaque")
    let σ : Numbering := ⟨v.cnst.levelParams, false⟩
    let ks ← exprsOf #[(σ, v.cnst.type), (σ, v.value)]
    return .unsafeOpaque ⟨ingressKey v.cnst.name, σ.params, ks[0]!⟩ ks[1]!
  | .definitions members => do
    let some (Ix.ConstantInfo.defnInfo v₀) := members[0]?
      | throw (.declined "tier: a block with a member that is not a definition")
    let some s := tierSafetyOf? v₀.safety
      | throw (.declined s!"tier: a block of safety \
          '{Ix.Kernel.Reader.safetyWord (safetyOf v₀.safety)}' with a member that is not safe")
    let mut items : Array (Numbering × Ix.Expr) := #[]
    for ci in members do
      let .defnInfo v := ci
        | throw (.declined s!"tier: a {s.word} block with a member that is not a definition")
      unless v.safety == v₀.safety do
        throw (.declined s!"tier: a {s.word} block with a member of safety \
          '{Ix.Kernel.Reader.safetyWord (safetyOf v.safety)}'")
      let σ : Numbering := ⟨v.cnst.levelParams, false⟩
      items := items.push (σ, v.cnst.type) |>.push (σ, v.value)
    let ks ← exprsOf items
    let ms := members.zipIdx.map fun (ci, j) =>
      let σ : Numbering := ⟨ci.getCnst.levelParams, false⟩
      ((⟨ingressKey ci.getCnst.name, σ.params, ks[2 * j]!⟩ : CVal .source), ks[2 * j + 1]!)
    return .defs s ms.toList
  | _ => throw (.declined "tier: not a tier group")

/-! ### Inductive blocks for the tier's answers (M7 Q1)

An unsafe inductive group stays logical in the tiered check above, where it
declines. The Source service installs it typing only instead
(`Ix.Kernel.Tier.indC`), to answer AuxGen's questions about it; so does a
regenerated family before its recursors exist (a group with no recursor).
Neither is a verdict. -/

/-- **An unsafe inductive group**: a member, a constructor or a recursor is
unsafe. -/
def isTierInductive : Group → Bool
  | .inductive types ctors recs =>
    types.any (·.isUnsafe) || ctors.any (·.any (·.isUnsafe)) || recs.any (·.isUnsafe)
  | _ => false

/-- A block read as the tier takes it: each constructor with its former's
position (by `ctorNames`), each recursor with its counts. -/
def tierIndOf (rb : Ix.Kernel.Reader.BlockRead .source) : Ix.Kernel.Tier.TierInd .source :=
  { numParams := rb.numParams
    types := rb.types.toList.map fun (cv, _, nIdx) => (cv, nIdx)
    ctors := rb.ctors.toList.map fun (cv, _, nF) =>
      (cv, (rb.ctorNames.findIdx? (·.contains cv.name)).getD rb.types.size, nF)
    recs := rb.recs.toList.map fun (cv, c, rules) =>
      (cv, ⟨c.params, c.motives, c.minors, c.indices⟩, rules) }

/-- **An inductive group's conversion for the tier**: `convertInductive`'s,
unsafe or not (the safety flags are the only thing it reads that the tier
does not), as the tier takes it. A block without recursors converts too. -/
def convertTierInductive (types : Array Ix.InductiveVal) (ctors : Array (Array Ix.ConstructorVal))
    (recs : Array Ix.RecursorVal) : Except ReadError (Ix.Kernel.Tier.TierInd .source) := do
  let c ← convertInductive (types.map fun v => { v with isUnsafe := false })
    (ctors.map (·.map fun v => { v with isUnsafe := false }))
    (recs.map fun v => { v with isUnsafe := false })
  match c with
  | .inductive rb => pure (tierIndOf rb)
  | _ => throw (.malformed "tier: an inductive group converted to something else")

/-- Failures of the tiered Source-mode check, kept apart. -/
inductive TierSourceError where
  /-- the logical check's: ingress, prelude, fold -/
  | source (error : SourceError)
  /-- a logical group (named by its first constant) references a tier group -/
  | fence (group : CName .source) (tier : CName .source)
  /-- the tier fold, at the failing tier group's position among the tier groups -/
  | tier (error : Ix.Kernel.CheckError .source) (position : Nat)

instance : ToString TierSourceError where
  toString
    | .source e => toString e
    | .fence g t => s!"fence: the group {g} references the tier group {t}"
    | .tier e p => s!"tier at {p}: {e}"

/-- **The tiered ingress** over a graph: the logical groups lowered as
`leanIngress` lowers them (the schedule without the tier groups), and the tier
groups' conversions, in the schedule's order, each behind the schedule's
placement checks. -/
def leanIngressTieredOf (g : Graph) (st : State .source := {}) :
    Except IngressError (Array (CDecl .source) × Array (TierDecl .source)) := do
  let tierConv : Array (Option (Except ReadError (TierDecl .source))) := g.groups.map fun grp =>
    if isTierGroup grp then some (convertTier grp) else none
  -- the tier groups' slots pass the conversion, so that the schedule's verdict
  -- on them is the placement checks alone; the order is the graph's, unchanged
  let gT : Graph := { g with converted := g.converted.zipIdx.map fun (c, i) =>
    if (tierConv[i]!).isSome then .ok (.definitions #[]) else c }
  let sched := scheduleOf gT
  let (_, decls) ← lowerAll st gT (sched.filter fun (i, _) => (tierConv[i]!).isNone)
  let mut tier : Array (TierDecl .source) := #[]
  for ((gi, c), k) in sched.zipIdx do
    if let some t := tierConv[gi]! then
      let fail (e : ReadError) : IngressError := ⟨g.groups[gi]!.name, k, e⟩
      let _ ← c.mapError fail
      tier := tier.push (← t.mapError fail)
  return (decls, tier)

/-- The tiered ingress of an environment under its condensation. -/
def leanIngressTiered (env : Ix.Environment) (blocks : Ix.CondensedBlocks)
    (st : State .source := {}) :
    Except IngressError (Array (CDecl .source) × Array (TierDecl .source)) :=
  leanIngressTieredOf (graph env blocks) st

/-- The fence's test: the first logical group that references a tier group,
and that tier group. -/
def sourceFenceOf (g : Graph) : Option (CName .source × CName .source) :=
  (Array.range g.groups.size).findSome? fun i =>
    if isTierGroup g.groups[i]! then none
    else (g.hard[i]!.find? (isTierGroup g.groups[·]!)).map fun j => (g.groups[i]!.name, g.groups[j]!.name)

/-- The tiered Source-mode check over a prelude source: the fence's test, the
logical groups through the fold at Source mode's evidence, exactly as
`checkSourceUsing` does over them, then the tier fold over the tier groups at
the accepted environment's index. -/
def checkSourceTieredUsing (prelude : Except String (Ix.Kernel.Reader.Prelude .source))
    (env : Ix.Environment) (blocks : Ix.CondensedBlocks) :
    Except TierSourceError (Ix.Kernel.Env .source × List (TierConst .source)) := do
  let pre ← prelude.mapError (.source ∘ .prelude)
  let g := graph env blocks
  if let some (a, t) := sourceFenceOf g then throw (.fence a t)
  let (decls, tier) ← (leanIngressTieredOf g pre.state).mapError (.source ∘ .ingress)
  let prepared := Ix.Kernel.Frontend.preparePrelude pre.ix decls
  let kenv ← (Ix.Kernel.Cached.checkDecls .verified (sourceEvidence prepared) prepared).mapError
    fun (e, i) => .source (.kernel e i)
  match Ix.Kernel.Tier.checkTierC (Ix.Kernel.mkFEnv kenv) tier.toList with
  | .ok (_, ts) => pure (kenv, ts)
  | .error (e, k) => throw (.tier e k)

/-- **The tiered Source-mode check**: `checkSource` over the logical groups
behind the committed prelude, then the typing tier over the tier groups
(partial and unsafe). The result is the logical environment, model-backed as `checkSource`'s, and
the tier constants, typed with every tier constant opaque
(`Ix.LeanIngress.checkSourceTiered_ok`). -/
def checkSourceTiered (env : Ix.Environment) (blocks : Ix.CondensedBlocks) :
    Except TierSourceError (Ix.Kernel.Env .source × List (TierConst .source)) :=
  checkSourceTieredUsing Ix.Kernel.Reader.builtinPrelude env blocks

end Ix.LeanIngress
