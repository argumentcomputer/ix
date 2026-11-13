module

public import IxC.Resource.Syntax
public import IxC.Resource.ModeSource
public import IxC.Ixon.WireCheck
public import IxC.Kernel.Ixon.Reader
public import IxC.Kernel.ExprOps

/-!
# The reading: records to a run program

`readProg s cl` reads the run program of a claim's closure (`Subject`): one
`RunDef` per constant. It is a function of the records, the role table, the run
table and the extern set, and of a **class oracle** `cl` (`Classifier`), which
gives the class of a term or of a type's values from the kernel's reading of
them. The statement (`IxC.Resource.Statement`) reads with the canonical oracle,
the kernel's own judgements; the checker reads with a fueled one.

* **Modes** come from the records by position (`IxC.Resource.ModeSource`). The
  reading consumes each block's nodes in pre-order as it walks the expression,
  and fails on any mismatch (a node of the wrong kind, a missing or surplus node,
  a share node naming a variant with no block).
* **Run bodies.** A safe definition runs its value, its leading λs as its
  parameters. Its λ telescope and its type's ∀ telescope agree node for node,
  modes and domain skeletons both; a λ beyond the type's ∀s, or a ∀ beyond the
  λs, has the default mode; a λ's result before the last is `shared`. A
  definition the run table binds runs its equation's right side under its own
  type's binder modes.
* **Case shapes** are recognised from the records alone (`caseOf`): a recursor
  with one motive whose minor premises, as written in a definition, forward
  their fields (never their induction hypotheses) to one of the definition's
  parameters, or a definition forwarding its alternatives to another case
  shape. A full application of one reads as `Term.case`.
* **Externs** are the constants of the extern set, **primitives** the role
  table's `Nat` operations, and every other constant without a run body is
  `stuck` with its interface.
* **Raw recursors.** A recursor a run term calls (not through a case shape)
  has rules that pass each field its constructor erases only to a binder of the
  dispatched minor premise that erases it (`Reading.recRules`).

**No supplied behaviour reads what an interface erases.** A case rule, a
primitive, a constructor and an extern run in place of a body, so their modes
are read against what they do, and a record that disagrees does not read: a
case definition's major premise and alternatives are not erased, and its other
parameters are default or erased (`caseModes`); a constant the role table binds
sits in a record with only default modes; a constant with no run body outside
the extern set has the default interface (`stuckAt`); a run body's interface,
read for itself or for its callers, is its telescopes' agreed reading
(`teleAgree`). `IxC.Resource.ReadsRespectErasure` states the consequence.

Telescopes are read through sharing references: a binder inside a sharing entry
is read in that entry's block, as the telescope's (`readTele`).
-/

@[expose] public section

namespace IxC.Resource

open Ixon
open Ix.Kernel (ConstRef)

abbrev KExpr := Ix.Kernel.Expr .anon

/-- **What a modes claim binds** besides its typing: the role table, the
records and blobs, the seeds, the run-table record and the extern set. -/
structure Subject where
  table : Ix.Kernel.RoleTable
  store : Ix.Kernel.Reader.Store
  blob : Address → Option ByteArray := fun _ => none
  seeds : List Address
  runTable : Option Address := none
  externs : List Address := []

/-- **A class oracle**: the class of the terms of a type (`type`), and of a term
(`node`), each opened at a depth (its free variables are the kernel's `fvar`s
below it). -/
structure Classifier where
  type : Nat → KExpr → Except String Cls
  node : Nat → KExpr → Except String Cls

/-- A class oracle that answers `val`, for readings that use no class. -/
def noClasses : Classifier := { type := fun _ _ => .ok .val, node := fun _ _ => .ok .val }

/-! ## Cursors over binder blocks -/

structure Cursor where
  nodes : Array ModeNode := #[]
  pos : Nat := 0

abbrev RM := StateT Cursor (Except String)

def nextNode : RM ModeNode := do
  let c ← get
  match c.nodes[c.pos]? with
  | some n => do set { c with pos := c.pos + 1 }; pure n
  | none => throw "a binder block has fewer nodes than its expression"

def nextBinder : RM AllMode := do
  match ← nextNode with
  | .binder m => pure m
  | .share _ => throw "a share node where the expression has a binder"

def nextShare : RM Nat := do
  match ← nextNode with
  | .share v => pure v
  | .binder _ => throw "a binder node where the expression has a share"

/-- Run `k` on block `key` with a cursor of its own, checking `k` uses every node. -/
def inBlock {α : Type} (rm : RecordModes) (key : BlockKey) (k : RM α) : RM α := do
  let saved ← get
  set ({ nodes := (rm.block? key).getD #[], pos := 0 } : Cursor)
  let r ← k
  let c ← get
  unless c.pos == c.nodes.size do throw "a binder block has more nodes than its expression"
  set saved
  pure r

/-- Run `k` on sharing entry `n` at the variant the current share node names. -/
def enterShare {α : Type} (rm : RecordModes) (n : Nat) (k : RM α) : RM α := do
  if rm.binderfulAt n then
    let v ← nextShare
    let key : BlockKey := { shared := true, index := n, variant := v }
    unless (rm.block? key).isSome do throw "a share node names a variant with no block"
    inBlock rm key k
  else inBlock rm { shared := true, index := n, variant := 0 } k

/-- Consume the nodes of `e` without reading it (a share is not entered). -/
def skip (rm : RecordModes) : Nat → Ixon.Expr → RM Unit
  | 0, _ => throw "expression too large"
  | n + 1, e => do
    match ← view e with
    | .lam ty b | .all ty b => do let _ ← nextBinder; skip rm n ty; skip rm n b
    | .app f a => do skip rm n f; skip rm n a
    | .letE _ t v b => do skip rm n t; skip rm n v; skip rm n b
    | .prj _ _ v => skip rm n v
    | .share i =>
      if rm.binderfulAt i then do
        let v ← nextShare
        unless (rm.block? { shared := true, index := i, variant := v }).isSome do
          throw "a share node names a variant with no block"
      else pure ()
    | _ => pure ()

/-! ## Syntactic spines -/

/-- The head and arguments of an application, through `app` nodes only. -/
def ixSpine : Nat → Ixon.Expr → Except String (Ixon.Expr × Array Ixon.Expr)
  | 0, _ => throw "expression too large"
  | n + 1, e => do
    match ← view e with
    | .app f a => do
      let (h, as) ← ixSpine n f
      pure (h, as.push a)
    | _ => pure (e, #[])

/-- The head and arguments of a run term, whole: by structural recursion, not
cut by a fuel. (As landed it took the caller's fuel, and the checker passed its
remaining depth, so a spine longer than that depth was judged as a shorter call
followed by applications of a function value: the checker-side shape of
finding 7. A bound that exists for termination must not change what a spine
means.) -/
def termSpine : Term → Term × Array Term
  | .app f a _ =>
    let (h, as) := termSpine f
    (h, as.push a)
  | t => (t, #[])

/-- The relevant free variables of a run term, under `d` binders, as indices
outside them. -/
def freeVars : Nat → Nat → Term → Except String (List Nat)
  | 0, _, _ => throw "term too large"
  | n + 1, d, t =>
    match t with
    | .irr | .const .. | .natLit _ | .strLit _ => pure []
    | .var i _ => pure (if i ≥ d then [i - d] else [])
    | .app f a _ => do pure (natUnion (← freeVars n d f) (← freeVars n d a))
    | .lam _ _ _ _ b => freeVars n (d + 1) b
    | .letE _ _ v b => do pure (natUnion (← freeVars n d v) (← freeVars n (d + 1) b))
    | .proj _ _ e _ => freeVars n d e
    | .case _ mj alts ex _ => do
      let mut acc ← freeVars n d mj
      for a in alts do acc := natUnion acc (← freeVars n d a)
      for a in ex do acc := natUnion acc (← freeVars n d a)
      pure acc

/-! ## The reading context -/

/-- A variable in scope: the kernel's opened variable and its class. -/
structure Local where
  fv : KExpr
  cls : Cls

/-- The constants of a role table, by reference. -/
def roleOf? (s : Subject) (r : Ref) : Option Ix.Kernel.Role :=
  (s.table.bound.find? fun (_, a) => Ix.Kernel.Reader.resolve s.store a == some r).map (·.1)

/-- The reference a role is bound to. -/
def roleRef? (s : Subject) (role : Ix.Kernel.Role) : Option Ref := do
  Ix.Kernel.Reader.resolve s.store (← s.table.addressOf? role)

/-- The inductive member at a reference. -/
def inductiveAt? (s : Subject) : Ref → Option Ixon.Inductive
  | .member b i => do
    let .muts ms := (← s.store b).info | none
    let .indc ind ← ms[i]? | none
    pure ind
  | .ctor .. => none

/-- **A reading in progress**: the subject, and the kernel reader's context
over the closure's records. -/
structure Reading where
  s : Subject
  cx : Ix.Kernel.Reader.Ctx .anon
  /-- the closure's record addresses -/
  closure : Array Address
  /-- the closure's walk finished within its step limit (else `closure` is a part of it) -/
  walked : Bool

/-- What reading one member of one record needs. -/
structure RCx where
  rd : Reading
  cl : Classifier
  owner : Address
  c : Ixon.Constant
  rm : RecordModes
  mr : Ix.Kernel.Reader.MemberReader .anon
  /-- `recur i`'s reference -/
  recur : Nat → Option Ref

def RCx.s (x : RCx) : Subject := x.rd.s

def RCx.refAt (x : RCx) (i : Nat) : Except String Ref := do
  let some a := x.c.refs[i]? | throw "reference index out of range"
  let some r := Ix.Kernel.Reader.resolve x.s.store a | throw s!"reference {a} does not resolve"
  pure r

def RCx.blobAt (x : RCx) (i : Nat) : Except String ByteArray := do
  let some a := x.c.refs[i]? | throw "literal index out of range"
  let some b := x.s.blob a | throw s!"literal blob {a} is missing"
  pure b

/-- The kernel's reading of `e` (an expression of this member), opened at `ctx`. -/
def RCx.toK (x : RCx) (ctx : List Local) (e : Ixon.Expr) : Except String KExpr :=
  match x.mr.read e with
  | .ok k => .ok (Ix.Kernel.Expr.instantiateList k (ctx.map (·.fv)))
  | .error err => .error (toString err)

/-- Whether the head `e` names an inductive type. -/
def RCx.isInd (x : RCx) (e : Ixon.Expr) : Bool :=
  match view e with
  | .ok (.ref i) => match x.refAt i with
    | .ok r => (inductiveAt? x.s r).isSome
    | .error _ => false
  | .ok (.recur i) => match x.recur i with
    | some r => (inductiveAt? x.s r).isSome
    | none => false
  | _ => false

/-- Whether the reading claims that no value of type `ty` is a leaf: never. The
claim (a function type, a sort, an inductive with other than one constructor)
was true of `Nat` itself, which has two, and false in the sense the checker used
it at function types, at data holding closures and under an absurd hypothesis
(findings 1 to 3); the checker no longer reads `Param.noLeaf`. Enforcing such a
claim in `runR`, as a stuck run, can come back as a widening. -/
def RCx.noLeafType (_x : RCx) (_ty : Ixon.Expr) : Bool := false

/-! ## Skeletons -/

/-- **A type's mode skeleton**, read from the record (no unfolding): a ∀ its
node's modes; an inductive type or a sort `data`, applied to its arguments'
skeletons; a variable or a definition `unknown`. Consumes the type's nodes. -/
def readSkel (x : RCx) : Nat → Ixon.Expr → RM Skel
  | 0, _ => throw "expression too large"
  | n + 1, e => do
    match ← view e with
    | .all ty b => do
      let m ← nextBinder
      let d ← readSkel x n ty
      let cd ← readSkel x n b
      pure (.arrow m.input d m.result cd)
    | .sort | .nat _ | .str _ => pure .data
    | .ref _ | .recur _ => pure (if x.isInd e then .data else .unknown)
    | .app .. => do
      let (h, args) ← ixSpine n e
      if x.isInd h then
        let mut s := Skel.data
        for a in args do s := .dataApp s (← readSkel x n a)
        pure s
      else do skip x.rm n e; pure .unknown
    | .share i => do
      let some ent := x.c.sharing[i]? | throw "sharing reference out of range"
      enterShare x.rm i (readSkel x n ent)
    | .var _ => pure .unknown
    | _ => do skip x.rm n e; pure .unknown

/-- A skeleton's arrow chain: `params`' ∀s over `cod`. -/
def arrowChain : List (AllMode × Skel) → Skel → Skel
  | [], cod => cod
  | (m, d) :: rest, cod => .arrow m.input d m.result (arrowChain rest cod)

/-! ## Terms -/

/-- Fold arguments into applications: the last at class `c`. -/
def foldApp (h : Term) (args : Array Term) (c : Cls) : Term :=
  (args.zipIdx.foldl (fun f (a, i) => Term.app f a (if i + 1 == args.size then c else .val)) h)


/-- **Read a relevant term**: its class from the oracle (a variable's from its
binder), `irr` skipped. Returns the term and its class. -/
def readTerm (x : RCx) (caseOf : Ref → Option CaseInfo) :
    Nat → List Local → Ixon.Expr → RM (Term × Cls)
  | 0, _, _ => throw "expression too large"
  | n + 1, ctx, e => do
    let v ← view e
    if let .var i := v then
      let some l := ctx[i]? | throw "variable out of scope"
      return (if l.cls == .irr then .irr else .var i l.cls, l.cls)
    let c ← x.cl.node ctx.length (← x.toK ctx e)
    if c == .irr then
      skip x.rm n e
      return (.irr, .irr)
    match v with
    | .var _ | .sort | .all .. => do skip x.rm n e; pure (.irr, .irr)
    | .ref i => return (.const (← x.refAt i) c, c)
    | .recur i =>
      match x.recur i with
      | some r => pure (.const r c, c)
      | none => throw "recursive reference outside its block"
    | .nat i => return (.natLit (Ix.Kernel.Reader.natural (← x.blobAt i)), c)
    | .str i => do
      let some s := String.fromUTF8? (← x.blobAt i) | throw "string literal is not valid UTF-8"
      pure (.strLit s, c)
    | .prj t f v => do
      let s ← x.refAt t
      let (vt, _) ← readTerm x caseOf n ctx v
      pure (.proj s f vt c, c)
    | .app .. => do
      let (h, args) ← ixSpine n e
      let (ht, _) ← readTerm x caseOf n ctx h
      let mut ats : Array Term := #[]
      for a in args do ats := ats.push (← readTerm x caseOf n ctx a).1
      let (h', pre) := termSpine ht
      let all := pre ++ ats
      match h' with
      | .const r _ =>
        match caseOf r with
        | some k =>
          if all.size ≥ k.arity then
            let alts := k.alts.map fun a => all[a.alt]?.getD .irr
            return (.case k (all[k.major]?.getD .irr) alts (all.extract k.arity all.size) c, c)
          else pure (foldApp h' all c, c)
        | none => pure (foldApp h' all c, c)
      | _ => pure (foldApp h' all c, c)
    | .lam ty b => do
      let m ← nextBinder
      let k ← x.toK ctx ty
      let pc ← x.cl.type ctx.length k
      let ps ← readSkel x n ty
      let (bt, bc) ← readTerm x caseOf n (⟨.fvar ctx.length k, pc⟩ :: ctx) b
      let fvs ← freeVars n 1 bt
      pure (.lam { mode := m.input, cls := pc, skel := ps, noLeaf := x.noLeafType ty } m.result bc
        fvs.toArray bt, c)
    | .letE m ty v b => do
      let k ← x.toK ctx ty
      let dc ← x.cl.type ctx.length k
      skip x.rm n ty
      let (vt, _) ← readTerm x caseOf n ctx v
      let (bt, bc) ← readTerm x caseOf n (⟨.fvar ctx.length k, dc⟩ :: ctx) b
      pure (.letE m dc vt bt, bc)
    | .share i => do
      let some ent := x.c.sharing[i]? | throw "sharing reference out of range"
      enterShare x.rm i (readTerm x caseOf n ctx ent)


/-! ## Telescopes and interfaces -/

/-- The fuel of every syntactic walk. -/
def readFuel : Nat := 1 <<< 20

/-- A telescope's binder: its node's mode, its domain's skeleton and its domain. -/
abbrev TeleBinder := AllMode × Skel × Ixon.Expr

/-- Whether a sharing entry continues a telescope: through sharing references, a λ (`lam`) or
a ∀ (otherwise). -/
def continuesTele (c : Ixon.Constant) (lam : Bool) (e : Ixon.Expr) : Bool :=
  match Ix.Kernel.Reader.unshare c e with
  | .lam .. => lam
  | .all .. => !lam
  | _ => false

/-- **A telescope**: the leading λs (`lam`) or ∀s of an expression, stepping through a sharing
reference whose entry continues it (the entry is read in its block, at the variant its share
node names); each binder's node's mode, its domain's skeleton and its domain; then `k` on the
binders, in order, and on what follows them, in the block that holds it. Consumes the nodes.
(As landed the walk stopped at the first sharing reference, so binders inside a sharing entry
were read as part of the codomain or the body, their modes unchecked as parameters: note 12
§2 item 2.) -/
def readTele {β : Type} (x : RCx) (lam : Bool) (k : List TeleBinder → Ixon.Expr → RM β) :
    Nat → List TeleBinder → Ixon.Expr → RM β
  | 0, _, _ => throw "expression too large"
  | n + 1, acc, e => do
    match ← view e with
    | .all ty b =>
      if lam then k acc.reverse e else do
        let m ← nextBinder
        let d ← readSkel x n ty
        readTele x lam k n ((m, d, ty) :: acc) b
    | .lam ty b =>
      if lam then do
        let m ← nextBinder
        let d ← readSkel x n ty
        readTele x lam k n ((m, d, ty) :: acc) b
      else k acc.reverse e
    | .share i =>
      match x.c.sharing[i]? with
      | some ent =>
        if continuesTele x.c lam ent then enterShare x.rm i (readTele x lam k n acc ent)
        else k acc.reverse e
      | none => k acc.reverse e
    | _ => k acc.reverse e

/-- A type's leading ∀s, through sharing references (`readTele`), and `k` on its codomain.
Returns the binders, the codomain and `k`'s answer. -/
def readForalls {β : Type} (x : RCx) (fuel : Nat) (ty : Ixon.Expr) (k : Ixon.Expr → RM β) :
    RM (List TeleBinder × Ixon.Expr × β) :=
  readTele x false (fun alls cod => do pure (alls, cod, ← k cod)) fuel [] ty

/-- A telescope's parameters, opened in order: each binder's mode, its domain's
class (by the oracle) and skeleton; and the context under them. -/
def openParams (x : RCx) (tele : List (AllMode × Skel × Ixon.Expr)) :
    Except String (List Local × Array Param) := do
  let mut ctx : List Local := []
  let mut ps : Array Param := #[]
  for (m, sk, dom) in tele do
    let k ← x.toK ctx dom
    let pc ← x.cl.type ctx.length k
    ps := ps.push { mode := m.input, cls := pc, skel := sk, noLeaf := x.noLeafType dom }
    ctx := ⟨.fvar ctx.length k, pc⟩ :: ctx
  pure (ctx, ps)

/-- **An interface from a type**: its ∀s as parameters (mode, class, skeleton)
and its codomain's result mode, class and skeleton. A result mode before the
last ∀'s is `shared`. Reads in the type's block. -/
def readIface (x : RCx) (fuel : Nat) (ty : Ixon.Expr) :
    RM (Array Param × ResultMode × Cls × Skel) := do
  let (alls, cod, codSkel) ← readForalls x fuel ty (readSkel x fuel)
  let (ctx, ps) ← openParams x alls
  let n := alls.length
  for (m, _, _) in alls.take (n - 1) do
    unless m.result == .shared do throw "a non-default result mode before an interface's last binder"
  let res := (alls.getLast?.map (·.1.result)).getD .shared
  let rc ← x.cl.type ctx.length (← x.toK ctx cod)
  pure (ps, res, rc, codSkel)

/-- The λs of a definition's value, through sharing references (`readTele`), and `k` on them and
on the body. Returns the binders, the body and `k`'s answer. -/
def readLamNodes {β : Type} (x : RCx) (fuel : Nat) (val : Ixon.Expr)
    (k : List TeleBinder → Ixon.Expr → RM β) : RM (List TeleBinder × Ixon.Expr × β) :=
  readTele x true (fun lams body => do pure (lams, body, ← k lams body)) fuel [] val

/-- Strip `k` leading ∀s of an expression of `c`, through sharing references (as `readForalls`
reads them; as landed it stopped at the first sharing reference). -/
def dropAlls (c : Ixon.Constant) : Nat → Ixon.Expr → Except String Ixon.Expr
  | 0, e => pure e
  | k + 1, e => do
    match ← view (Ix.Kernel.Reader.unshare c e) with
    | .all _ b => dropAlls c k b
    | _ => throw "fewer binders than expected"

/-- **Telescope agreement**: a value's λs and its type's ∀s agree node for node,
modes and domain skeletons both; a λ beyond the ∀s, or a ∀ beyond the λs, has
the default mode (and a λ beyond them a default skeleton); a λ's result before
the last is `shared`. -/
def teleAgree (alls lams : List (AllMode × Skel × Ixon.Expr)) : Except String Unit := do
  let j := alls.length
  let k := lams.length
  for i in [0:k] do
    let (lm, lsk, _) := lams[i]!
    if i < j then
      let (tm, tsk, _) := alls[i]!
      unless lm == tm do throw "a λ's mode differs from its type's ∀"
      unless tsk.admits lsk do throw "a λ's domain skeleton differs from its type's ∀"
    else
      unless lm.isDefault && lsk.isDefault do throw "a moded λ beyond its type's ∀s"
    if i + 1 < k then
      unless lm.result == .shared do throw "a non-default result mode before a definition's last λ"
  for i in [k:j] do
    let (tm, _, _) := alls[i]!
    unless tm.isDefault do throw "a moded ∀ beyond its definition's λs"

/-- The class of a body read for its interface only: a variable's from its
binder, anything else's from the oracle. -/
def bodyClass (x : RCx) (ctx : List Local) (e : Ixon.Expr) : Except String Cls := do
  if let .var i := (← view e) then
    let some l := ctx[i]? | throw "variable out of scope"
    return l.cls
  x.cl.node ctx.length (← x.toK ctx e)

/-- **A definition's run body**: its value's λs and its type's ∀s, agreeing
(`teleAgree`); the body under the λs. `tyKey`/`valKey` are the two roots'
blocks. With `bodies = false` the body is not read (its nodes are consumed) and
the definition is read for its interface: the same telescopes, the same
agreement, the same parameters, with `Term.irr` for the body. -/
def readBody (x : RCx) (caseOf : Ref → Option CaseInfo) (fuel : Nat) (bodies : Bool)
    (ty val : Ixon.Expr) (tyKey valKey : BlockKey) : Except String RunDef := do
  let ((alls, _, codSkel), _) ← (inBlock x.rm tyKey (readForalls x fuel ty (readSkel x fuel))).run {}
  let ((lams, body, ctx, params, bodyT, bodyC?), _) ← (inBlock x.rm valKey
      (readLamNodes x fuel val fun lams body => do
        let (ctx, params) ← openParams x lams
        if bodies then
          let (bt, bc) ← readTerm x caseOf fuel ctx body
          pure (ctx, params, bt, some bc)
        else do
          skip x.rm fuel body
          pure (ctx, params, Term.irr, none))).run {}
  teleAgree alls lams
  let k := lams.length
  let res := (lams.getLast?.map (·.1.result)).getD .shared
  if k ≤ alls.length then
    let rest ← dropAlls x.c k ty
    let rc ← x.cl.type ctx.length (← x.toK ctx rest)
    let rs := arrowChain ((alls.drop k).map fun (m, s, _) => (m, s)) codSkel
    pure (.body params res rc rs bodyT)
  else
    let bodyC ← match bodyC? with
      | some c => pure c
      | none => bodyClass x ctx body
    pure (.body params res bodyC .unknown bodyT)

/-- **A case definition's modes**: its type's and value's telescopes agree as a
run body's do (`teleAgree`); every binder's result mode is `shared`; and every
parameter's mode is the default, except that a position the case rule does not
read (neither the major premise nor an alternative) may be `erased`, at the
same position in the type and the value. The case rule reads the major premise
and the selected alternative and nothing else, so these are exactly the modes
it honours. The value's body is not read: the case rule runs in its place. -/
def caseModes (x : RCx) (k : CaseInfo) (ty val : Ixon.Expr) (tyKey valKey : BlockKey) :
    Except String Unit := do
  let ((alls, _, _), _) ← (inBlock x.rm tyKey (readForalls x readFuel ty (readSkel x readFuel))).run {}
  let ((lams, _, _), _) ← (inBlock x.rm valKey
      (readLamNodes x readFuel val fun _ body => skip x.rm readFuel body)).run {}
  teleAgree alls lams
  for ((m, _, _), i) in lams.zipIdx do
    unless m.result == .shared do throw "a case definition's binder with a result mode"
    if i == k.major || k.alts.any (·.alt == i) then
      unless m.input == .many do
        throw "a case definition's major premise or alternative is not of the default mode: \
          its case rule reads it"
    else
      unless m.input == .many || m.input == .erased do
        throw "a case definition's binder with a mode other than erased"

/-! ## Case shapes -/

/-- Strip `m` leading λs, following sharing references. -/
def stripLamsU (c : Ixon.Constant) : Nat → Ixon.Expr → Option Ixon.Expr
  | 0, e => some e
  | m + 1, e =>
    match view (Ix.Kernel.Reader.unshare c e) with
    | .ok (.lam _ b) => stripLamsU c m b
    | _ => none

/-- A variable, through sharing references. -/
def varOf? (c : Ixon.Constant) (e : Ixon.Expr) : Option Nat :=
  match view (Ix.Kernel.Reader.unshare c e) with
  | .ok (.var i) => some i
  | _ => none

/-- An alternative forwarded under `m` binders, mapped by `map`: the body
`p a₁ … aₗ` with `p` one of the `k` parameters outside the binders and each
`aᵢ` a binder or `()`. Returns the parameter and the composed arguments. -/
def forwarded (s : Subject) (c : Ixon.Constant) (k m : Nat) (map : Nat → Option FieldArg)
    (e : Ixon.Expr) : Option CaseAlt := do
  let body ← stripLamsU c m e
  let (h, args) ← (ixSpine 4096 (Ix.Kernel.Reader.unshare c body)).toOption
  let w ← varOf? c h
  guard (m ≤ w && w < m + k)
  let p := k - 1 - (w - m)
  let unit := roleRef? s .punitUnit
  let mut out : Array FieldArg := #[]
  for a in args do
    match varOf? c a with
    | some y =>
      guard (y < m)
      out := out.push (← map (m - 1 - y))
    | none =>
      match view (Ix.Kernel.Reader.unshare c a) with
      | .ok (.ref i) =>
        let some addr := c.refs[i]? | none
        guard (unit.isSome && Ix.Kernel.Reader.resolve s.store addr == unit)
        out := out.push .unit
      | _ => none
  pure { alt := p, args := out }

/-- The recursor member at a reference. -/
def recursorAt? (s : Subject) : Ref → Option (Ixon.Constant × Ixon.Recursor)
  | .member b i => do
    let c ← s.store b
    match c.info with
    | .recr rr => if i == 0 then some (c, rr) else none
    | .muts ms => match ms[i]? with
      | some (.recr rr) => some (c, rr)
      | _ => none
    | _ => none
  | .ctor .. => none

/-- The definition member at a reference, with its record. -/
def definitionAt? (s : Subject) : Ref → Option (Ixon.Constant × Ixon.Definition)
  | .member b i => do
    let c ← s.store b
    match c.info with
    | .defn d => if i == 0 then some (c, d) else none
    | .muts ms => match ms[i]? with
      | some (.defn d) => some (c, d)
      | _ => none
    | _ => none
  | .ctor .. => none

/-- The references a record's `recur i` names. -/
def recurOf (owner : Address) (c : Ixon.Constant) (i : Nat) : Option Ref :=
  match c.info with
  | .muts ms => if i < ms.size then some (.member owner i) else none
  | _ => if i == 0 then some (.member owner 0) else none

/-- The reference of an expression's head (through sharing references). -/
def headRefOf (s : Subject) (owner : Address) (c : Ixon.Constant) (h : Ixon.Expr) : Option Ref :=
  match view (Ix.Kernel.Reader.unshare c h) with
  | .ok (.ref i) => do Ix.Kernel.Reader.resolve s.store (← c.refs[i]?)
  | .ok (.recur i) => recurOf owner c i
  | _ => none

/-- Whether the run table binds `r`. -/
def runBound (rt : Array (Ref × RunDef)) (r : Ref) : Bool := rt.any (·.1 == r)

/-- **The case shape of a constant**, if it has one (recognised from the
records; `fuel` bounds the chain of definitions). -/
def caseShape (s : Subject) (rt : Array (Ref × RunDef)) : Nat → Ref → Option CaseInfo
  | 0, _ => none
  | fuel + 1, r => do
    guard (!runBound rt r)
    let (c, d) ← definitionAt? s r
    guard (d.kind == .defn && d.safety == .safe)
    let owner := r.block
    -- the value's λs and the head it applies
    let mut k := 0
    let mut body := d.value
    for _ in [0:4096] do
      match view body with
      | .ok (.lam _ b) => do k := k + 1; body := b
      | _ => break
    let (h, args) ← (ixSpine 4096 (Ix.Kernel.Reader.unshare c body)).toOption
    let hr ← headRefOf s owner c h
    let major (pos : Nat) : Option Nat := do
      let w ← varOf? c (← args[pos]?)
      guard (w < k)
      pure (k - 1 - w)
    match recursorAt? s hr with
    | some (rc, rr) =>
      guard (rr.motives == 1 && rr.rules.size == rr.minors.toNat)
      let nP := rr.params.toNat
      let nMin := rr.minors.toNat
      let arity := nP + 1 + nMin + rr.indices.toNat + 1
      guard (args.size == arity)
      let mj ← major (arity - 1)
      -- the minor premises' telescopes, from the recursor's type
      let (doms, rest) ← Ix.Kernel.Reader.stripAll rc (nP + 1 + nMin + rr.indices.toNat) rr.typ
      let majorTy ← match view (Ix.Kernel.Reader.unshare rc rest) with
        | .ok (.all ty _) => some ty
        | _ => none
      let ind ← Ix.Kernel.Reader.headRef s.store hr.block rc majorTy
      let mut alts : Array CaseAlt := #[]
      for j in [0:nMin] do
        let nf := rr.rules[j]!.fields.toNat
        let dom ← doms[nP + 1 + j]?
        let tele := (Ix.Kernel.Reader.stripAllFull rc 4096 dom).1.length
        guard (nf ≤ tele)
        let nih := tele - nf
        let arg ← args[nP + 1 + j]?
        match varOf? c arg with
        | some w =>
          -- a parameter as the minor premise: only with no induction hypothesis
          guard (nih == 0 && w < k)
          alts := alts.push { alt := k - 1 - w, args := (List.range nf).toArray.map fun q => FieldArg.field q }
        | none =>
          let a ← forwarded s c k tele (fun q => if q < nf then some (.field q) else none) arg
          alts := alts.push a
      pure { ind, arity := k, major := mj, alts }
    | none =>
      let ch ← caseShape s rt fuel hr
      guard (args.size == ch.arity)
      let mj ← major ch.major
      let mut alts : Array CaseAlt := #[]
      for ca in ch.alts do
        let arg ← args[ca.alt]?
        match varOf? c arg with
        | some w =>
          guard (w < k)
          alts := alts.push { alt := k - 1 - w, args := ca.args }
        | none =>
          let map (q : Nat) : Option FieldArg := do
            let fa ← ca.args[q]?
            guard (fa != .irr)
            pure fa
          let a ← forwarded s c k ca.args.size map arg
          alts := alts.push a
      pure { ind := ch.ind, arity := k, major := mj, alts }

/-! ## The closure and the reading context -/

/-- The default step limit of the closure's walk (`closureOf`). -/
def closureFuel : Nat := 1 <<< 24

/-- The record addresses reachable from `roots` (through references and the
blocks projections name), and whether the walk finished within `fuel` steps.
As landed a walk cut at its limit returned what it had found so far, silently,
so a larger closure was read in part (V5): the caller now sees the cut, and
`Reading.complete` declines on it. -/
def closureOf (store : Ix.Kernel.Reader.Store) (roots : List Address) (fuel : Nat := closureFuel) :
    Array Address × Bool := Id.run do
  let mut seen : Std.HashSet Address := {}
  let mut out : Array Address := #[]
  let mut todo := roots
  for _ in [0:fuel] do
    match todo with
    | [] => break
    | a :: rest =>
      todo := rest
      if seen.contains a then continue
      seen := seen.insert a
      match store a with
      | none => pure ()
      | some c =>
        out := out.push a
        todo := c.refs.toList ++ todo
        match c.info with
        | .dPrj p => todo := p.block :: todo
        | .iPrj p => todo := p.block :: todo
        | .cPrj p => todo := p.block :: todo
        | .rPrj p => todo := p.block :: todo
        | _ => pure ()
  return (out, todo.isEmpty)

/-- The subject's closure's records, and the kernel reader's context over them;
`walked` says whether the closure's walk finished within `fuel` steps. -/
def Reading.make (s : Subject) (fuel : Nat := closureFuel) : Reading :=
  let roots := s.seeds ++ s.runTable.toList ++ s.externs
  let (closure, walked) := closureOf s.store roots fuel
  let records := closure.filterMap fun a => (s.store a).map (a, ·)
  { s, cx := Ix.Kernel.Reader.contextWith (md := .anon) s.store s.blob s.table records, closure,
    walked }

/-- A reading with no closure, for the walks that read no kernel expression (a
telescope's modes and skeletons: `ifaceErased`); its kernel reader indexes no
record. -/
def Reading.bare (s : Subject) : Reading :=
  { s, cx := Ix.Kernel.Reader.contextWith (md := .anon) s.store s.blob s.table #[], closure := #[],
    walked := true }

/-- The closure's walk finished (else a decline: a closure cut at the walk's
limit is never read in part), and every record of the reading's closure has a
complete binder-data section (`Ixon.Constant.bindersComplete`: a block for each
root and each variant of a sharing entry with a binder, each node of a binder's
kind). A closure with an incomplete section is not read. -/
def Reading.complete (rd : Reading) : Except String Unit := do
  unless rd.walked do throw "decline: the closure's walk reached its step limit"
  for a in rd.closure do
    let some c := rd.s.store a | continue
    unless c.bindersComplete do throw s!"record {a}: its binder-data section is incomplete"

/-- The reading context of member `r`'s record. -/
def Reading.rcx (rd : Reading) (cl : Classifier) (r : Ref) : Except String RCx := do
  let owner := r.block
  let some c := rd.s.store owner | throw s!"record {owner} is missing"
  let rm ← recordModes c
  let self : Nat → Option (Ix.Kernel.Reader.ReadM (Ix.Kernel.Reader.CName .anon)) := fun j =>
    (recurOf owner c j).map fun ref => rd.cx.memberKey ref
  let mr := Ix.Kernel.Reader.MemberReader.mk' rd.cx c id self
  pure { rd, cl, owner, c, rm, mr, recur := recurOf owner c }

/-- The number of roots a block member contributes, and the index of member
`i`'s first root. -/
def rootsOf : Ixon.MutConst → Nat
  | .defn _ => 2
  | .indc i => 1 + i.ctors.size
  | .recr r => 1 + r.rules.size

def rootBase (c : Ixon.Constant) (i : Nat) : Nat :=
  match c.info with
  | .muts ms => ((ms.toList.take i).map rootsOf).foldl (· + ·) 0
  | _ => 0

def rootKey (i : Nat) : BlockKey := { shared := false, index := i, variant := 0 }

/-- The primitive a role names. -/
def primOf (s : Subject) : Ix.Kernel.Role → Option Prim
  | .natZero => some .zero
  | .natSucc => some .succ
  | .natPred => some .pred
  | .natAdd => some .add
  | .natSub => some .sub
  | .natMul => some .mul
  | .natDiv => some .div
  | .natMod => some .mod
  | .natPow => some .pow
  | .natGcd => some .gcd
  | .natLand => some .land
  | .natLor => some .lor
  | .natXor => some .xor
  | .natShiftLeft => some .shiftLeft
  | .natShiftRight => some .shiftRight
  | .natBeq => do pure (.beq (← roleRef? s .boolTrue) (← roleRef? s .boolFalse))
  | .natBle => do pure (.ble (← roleRef? s .boolTrue) (← roleRef? s .boolFalse))
  | _ => none

/-- A stuck constant's or an extern's interface, from its type root. -/
def ifaceAt (x : RCx) (ty : Ixon.Expr) (key : BlockKey) :
    Except String (Array Param × ResultMode × Cls × Skel) :=
  ((inBlock x.rm key (readIface x readFuel ty)).run {}).map (·.1)

/-- Whether `r`'s record is in the extern set (by its address, or its block's). -/
def isExtern (s : Subject) (r : Ref) : Bool :=
  s.externs.any fun a => Ix.Kernel.Reader.resolve s.store a == some r

/-- A constructor's fields: each field binder's mode (`erased` or `many`) and
class, and the constructor's field mode. Its type's ∀s are exactly its
parameters and its `nFields` fields (as landed nothing compared them, and a
field inside a sharing entry was not read: note 12 §2 item 2). -/
def readCtorFields (x : RCx) (member ci : Nat) (nParams nFields : Nat) (ty : Ixon.Expr) (key : BlockKey) :
    Except String (Array Field) := do
  let ((alls, _, _), _) ← (inBlock x.rm key (readForalls x readFuel ty (readSkel x readFuel))).run {}
  unless alls.length == nParams + nFields do
    throw "a constructor's type's binders are not its parameters and fields"
  let mut ctx : List Local := []
  let mut out : Array Field := #[]
  for ((m, _, dom), i) in alls.zipIdx do
    let k ← x.toK ctx dom
    let pc ← x.cl.type ctx.length k
    ctx := ⟨.fvar ctx.length k, pc⟩ :: ctx
    unless m.result == .shared do throw "a constructor binder with a result mode"
    if i < nParams then
      unless m.input == .many do throw "a moded constructor parameter"
    else
      unless m.input == .many || m.input == .erased do
        throw "a constructor field binder with a mode other than erased"
      out := out.push { mode := m.input, fmode := fieldMode x.c member ci (i - nParams), cls := pc }
  pure out

/-- An extern's interface: its type's, with any modes. -/
def externAt (x : RCx) (ty : Ixon.Expr) (key : BlockKey) : Except String RunDef := do
  let (ps, res, rc, rs) ← ifaceAt x ty key
  pure (.extern ps res rc rs)

/-- **A constant with no run body** outside the extern set (an axiom, an opaque,
a theorem, an unsafe or `partial` constant, a quotient, a recursor): `stuck`,
with its interface, whose parameters and result must have the default modes.
Nothing checks what such a constant does with its arguments (`runR` stops at
it; a compiler links or runs it natively), so its modes would be promises; the
extern set is where a constant with no body may carry modes. -/
def stuckAt (x : RCx) (ty : Ixon.Expr) (key : BlockKey) : Except String RunDef := do
  let (ps, res, rc, rs) ← ifaceAt x ty key
  unless ps.all (·.mode == .many) && res == .shared do
    throw "an annotated constant with no run body is not in the extern set: its modes are promises \
      nothing checks"
  pure (.stuck ps res rc rs)

/-- Whether an expression's `let`s all have the default mode. -/
def letsDefault : Nat → Ixon.Expr → Except String Bool
  | 0, _ => throw "expression too large"
  | n + 1, e => do
    match ← view e with
    | .letE m t v b =>
      pure (m == .value .many && (← letsDefault n t) && (← letsDefault n v) && (← letsDefault n b))
    | .lam t b | .all t b => pure ((← letsDefault n t) && (← letsDefault n b))
    | .app f a => pure ((← letsDefault n f) && (← letsDefault n a))
    | .prj _ _ v => letsDefault n v
    | _ => pure true

/-- Whether a record carries only default modes (binders, `let`s, fields). -/
def recordDefault (c : Ixon.Constant) : Except String Bool := do
  let rm ← recordModes c
  let mut ok := rm.blocks.all fun (_, ns) => ns.all fun
    | .binder m => m.isDefault
    | .share _ => true
  for root in binderRoots c.info ++ c.sharing do
    ok := ok && (← letsDefault readFuel root)
  pure (ok && fieldModesDefault c)

/-- **The run definition of a constant** (`bodies = false` reads a run body's
telescopes and not its body, for an interface).

* A constant the role table binds sits in a record carrying only default modes:
  `runR` runs the primitives natively, and the classes read `Nat`'s and `BitVec`'s
  representation from the roles, so no mode of such a record is honoured.
* A case shape's modes are read (`caseModes`).
* A constant with no run body outside the extern set has the default interface
  (`stuckAt`). -/
def Reading.readDef (rd : Reading) (cl : Classifier) (rt : Array (Ref × RunDef)) (bodies : Bool)
    (r : Ref) : Except String RunDef := do
  if let some role := roleOf? rd.s r then
    let some c := rd.s.store r.block | throw s!"record {r.block} is missing"
    unless (← recordDefault c) do
      throw "a constant the role table binds sits in a record that carries modes"
    if let some p := primOf rd.s role then return .prim p
  if let some (_, d) := rt.find? (·.1 == r) then
    return d
  let x ← rd.rcx cl r
  let caseOf := caseShape rd.s rt 16
  match r with
  | .ctor b i ci => do
    let .muts ms := x.c.info | throw "a constructor outside a block"
    let some (.indc ind) := ms[i]? | throw "a constructor of no inductive"
    let some ctor := ind.ctors[ci]? | throw "constructor index out of range"
    let fields ← readCtorFields x i ci ind.params.toNat ctor.fields.toNat ctor.typ
      (rootKey (rootBase x.c i + 1 + ci))
    pure (.ctor (.member b i) ci ind.params.toNat fields)
  | .member _ i => do
    let base := rootBase x.c i
    if let some info := caseOf r then
      let some (_, d) := definitionAt? rd.s r | throw "a case shape that is no definition"
      caseModes x info d.typ d.value (rootKey base) (rootKey (base + 1))
      return .caseDef info
    let member : Option Ixon.MutConst := match x.c.info with
      | .muts ms => ms[i]?
      | .defn d => some (.defn d)
      | .recr rr => some (.recr rr)
      | _ => none
    match x.c.info, member with
    | .axio a, _ =>
      if isExtern rd.s r then externAt x a.typ (rootKey 0) else stuckAt x a.typ (rootKey 0)
    | .quot q, _ => stuckAt x q.typ (rootKey 0)
    | _, some (.indc ind) =>
      pure (.ind ((List.range ind.ctors.size).toArray.map fun ci => ConstRef.ctor r.block i ci))
    | _, some (.recr rr) => stuckAt x rr.typ (rootKey base)
    | _, some (.defn d) =>
      let runnable := d.kind == .defn && d.safety == .safe
      if isExtern rd.s r then externAt x d.typ (rootKey base)
      else if runnable then readBody x caseOf readFuel bodies d.typ d.value (rootKey base) (rootKey (base + 1))
      else stuckAt x d.typ (rootKey base)
    | _, _ => throw "no constant at this reference"

/-- The type root of the constant `r` in its record `c`: its block number and
its expression. -/
def typeRootOf (c : Ixon.Constant) : Ref → Option (Nat × Ixon.Expr)
  | .member _ i =>
    match c.info with
    | .defn d => if i == 0 then some (0, d.typ) else none
    | .recr rr => if i == 0 then some (0, rr.typ) else none
    | .axio a => if i == 0 then some (0, a.typ) else none
    | .quot q => if i == 0 then some (0, q.typ) else none
    | .muts ms =>
      match ms[i]? with
      | some (.defn d) => some (rootBase c i, d.typ)
      | some (.indc ind) => some (rootBase c i, ind.typ)
      | some (.recr rr) => some (rootBase c i, rr.typ)
      | none => none
    | _ => none
  | .ctor _ i ci =>
    match c.info with
    | .muts ms =>
      match ms[i]? with
      | some (.indc ind) => (ind.ctors[ci]?).map fun ctor => (rootBase c i + 1 + ci, ctor.typ)
      | _ => none
    | _ => none

/-- **The positions a constant's interface erases**: the leading ∀s of its type
whose binder mode is `erased`, read from its record by the walk every interface
is read by (`readForalls`, through sharing references, in its type's block; as
landed a walk of its own, `leadingBinders`, stopped at the first sharing
reference: note 12 §2 item 2, B.20). -/
def ifaceErased (s : Subject) (r : Ref) : Except String (List Nat) := do
  let some c := s.store r.block | throw s!"record {r.block} is missing"
  let some (root, ty) := typeRootOf c r | throw "no constant at this reference"
  let x ← (Reading.bare s).rcx noClasses r
  let ((alls, _, _), _) ← (inBlock x.rm (rootKey root) (readForalls x readFuel ty (readSkel x readFuel))).run {}
  pure (alls.zipIdx.filterMap fun ((m, _, _), i) => if m.input == .erased then some i else none)

/-! ## The run table -/

/-- One equation of the run table: `∀ xs, f xs = rhs`, read in the run-table
record's type block. Returns `f` and its run body; `f`'s binder modes and
skeletons come from `f`'s own type. -/
def readEquation (rd : Reading) (cl : Classifier) (x : RCx) (eqRef andRef : Option Ref) :
    Nat → List Local → Ixon.Expr → RM (Array (Ref × RunDef))
  | 0, _, _ => throw "run table too large"
  | n + 1, ctx, e => do
    match ← view e with
    | .all ty b => do
      let m ← nextBinder
      unless m.isDefault do throw "a moded binder in the run table"
      let k ← x.toK ctx ty
      let pc ← cl.type ctx.length k
      skip x.rm n ty
      readEquation rd cl x eqRef andRef n (⟨.fvar ctx.length k, pc⟩ :: ctx) b
    | .app .. => do
      let (h, args) ← ixSpine n e
      let hr := match view h with
        | .ok (.ref i) => (x.refAt i).toOption
        | _ => none
      if ctx.isEmpty && hr.isSome && hr == andRef && args.size == 2 then
        let a ← readEquation rd cl x eqRef andRef n [] args[0]!
        let b ← readEquation rd cl x eqRef andRef n [] args[1]!
        return a ++ b
      unless hr.isSome && hr == eqRef && args.size == 3 do throw "a run-table entry is not an equation"
      let xs := ctx.length
      -- the left side: `f` applied to exactly the bound variables, in order
      let (lh, largs) ← ixSpine n args[1]!
      let f ← match view lh with
        | .ok (.ref i) => x.refAt i
        | _ => throw "a run-table equation's left side is not a constant"
      unless largs.size == xs do throw "a run-table equation's left side is not fully applied"
      for (a, i) in largs.zipIdx do
        unless (match view a with | .ok (.var j) => j == xs - 1 - i | _ => false) do
          throw "a run-table equation's left side does not apply its constant to its binders"
      let tyK ← x.toK ctx args[0]!
      let rc ← cl.type xs tyK
      skip x.rm n args[0]!
      skip x.rm n args[1]!
      let (rhs, _) ← readTerm x (caseShape rd.s #[] 16) n ctx args[2]!
      -- `f`'s modes, from its own type
      let some (fc, fd) := definitionAt? rd.s f | throw "a run-table equation names no definition"
      unless fd.kind == .defn && fd.safety == .safe do throw "a run-table equation names no safe definition"
      let fx ← rd.rcx cl f
      let base := match f with
        | .member _ i => rootBase fc i
        | _ => 0
      let ((alls, _, codSkel), _) ←
        (inBlock fx.rm (rootKey base) (readForalls fx readFuel fd.typ (readSkel fx readFuel))).run {}
      unless xs ≤ alls.length do throw "a run-table equation has more binders than its definition's type"
      for (m, _, _) in alls.drop xs do
        unless m.isDefault do throw "a moded ∀ beyond a run-table equation's binders"
      for (m, _, _) in alls.take (xs - 1) do
        unless m.result == .shared do throw "a non-default result mode before a definition's last binder"
      let clsList := (ctx.reverse.map (·.cls)).toArray
      let params := ((alls.take xs).zipIdx.map fun ((m, sk, dom), i) =>
        ({ mode := m.input, cls := clsList[i]?.getD .val, skel := sk, noLeaf := fx.noLeafType dom } : Param)).toArray
      let res := ((alls.take xs).getLast?.map (·.1.result)).getD .shared
      let rs := arrowChain ((alls.drop xs).map fun (m, s, _) => (m, s)) codSkel
      return #[(f, .body params res rc rs rhs)]
    | _ => throw "a run-table entry is not an equation"

/-- **The run table**: its record's statement, a conjunction of equations. -/
def Reading.runTable (rd : Reading) (cl : Classifier) : Except String (Array (Ref × RunDef)) := do
  let some a := rd.s.runTable | return #[]
  let some r := Ix.Kernel.Reader.resolve rd.s.store a | throw "the run table does not resolve"
  let some (c, d) := definitionAt? rd.s r | throw "the run table is not a definition"
  unless d.kind == .thm do throw "the run table is not a theorem"
  let x ← rd.rcx cl r
  let base := match r with
    | .member _ i => rootBase c i
    | _ => 0
  let entries ← ((inBlock x.rm (rootKey base)
      (readEquation rd cl x (roleRef? rd.s .eq) (roleRef? rd.s .and) readFuel [] d.typ)).run {}).map (·.1)
  for (f, _) in entries do
    unless (entries.filter (·.1 == f)).size == 1 do throw "a definition bound twice by the run table"
  pure entries

/-! ## Raw recursors (note 12 §2.1)

A raw recursor is `stuck` in `runR`, but our evaluator and compiled code fire it by its stored
rules, and the rules hand a constructor's fields to the minor premise they dispatch. So a raw
recursor a run term calls must pass a field its constructor writes erased only to a binder that
erases it, and must read it nowhere else. -/

/-- The head and arguments of an application, stepping through sharing references at every node
of the spine. -/
def ixSpineU (c : Ixon.Constant) : Nat → Ixon.Expr → Except String (Ixon.Expr × Array Ixon.Expr)
  | 0, _ => throw "expression too large"
  | n + 1, e =>
    match Ix.Kernel.Reader.unshare c e with
    | .app f a => do
      let (h, as) ← ixSpineU c n f
      pure (h, as.push a)
    | e' => pure (e', #[])

/-- Whether the variable `v` (a de Bruijn index at `e`'s top) occurs in `e`, through sharing
references. -/
def mentions (c : Ixon.Constant) : Nat → Nat → Ixon.Expr → Except String Bool
  | 0, _, _ => throw "expression too large"
  | n + 1, v, e =>
    match Ix.Kernel.Reader.unshare c e with
    | .var i => pure (i.toNat == v)
    | .app f a => do pure ((← mentions c n v f) || (← mentions c n v a))
    | .lam t b | .all t b => do pure ((← mentions c n v t) || (← mentions c n (v + 1) b))
    | .letE _ _ t x b => do
      pure ((← mentions c n v t) || (← mentions c n v x) || (← mentions c n (v + 1) b))
    | .prj _ _ x => mentions c n v x
    | .share _ => throw "sharing reference out of range"
    | _ => pure false

/-- The modes of a skeleton's arrows, outermost first: a type's leading ∀s, as `readSkel` reads
them (through sharing references). -/
def arrowModes : Skel → List (BinderMode × ResultMode)
  | .arrow i _ r c => (i, r) :: arrowModes c
  | _ => []

/-- The modes of constructor `ci`'s field binders (its type's ∀s past its inductive's
parameters), read as `readCtorFields` reads them. -/
def Reading.ctorFieldModes (rd : Reading) (cl : Classifier) (ind : Ref) (ci : Nat) :
    Except String (List AllMode) := do
  let .member _ i := ind | throw "a constructor of no inductive"
  let some indV := inductiveAt? rd.s ind | throw "a recursor's major premise is of no inductive"
  let some ctor := indV.ctors[ci]? | throw "constructor index out of range"
  let x ← rd.rcx cl ind
  let ((alls, _, _), _) ← (inBlock x.rm (rootKey (rootBase x.c i + 1 + ci))
    (readForalls x readFuel ctor.typ (readSkel x readFuel))).run {}
  pure ((alls.drop indV.params.toNat).map (·.1))

/-- **A raw recursor's rules against its inductive's constructors** (note 12 §2.1). The
recursor's type's ∀s are its parameters, motives, minor premises, indices and major premise,
all of the default mode; its inductive is the head of its major premise's type, and its rules
are exactly that inductive's constructors (a mutual recursor takes the minor premises of every
constructor of its block, and has rules only for its own inductive's). For rule `j`, of
constructor `j`: its field count is the constructor's; its right-hand side, past
`params + motives + minors + fields` λs (through sharing references), applies a minor premise
`m` (the rule dispatches the minor its body applies, not the one at index `j`), and `m`'s
telescope has at least the constructor's fields; each field the constructor's record writes
erased is bound erased in `m`'s telescope, is passed as `m`'s argument at its own position, and
is mentioned in no other argument of the body (the λs' domains are types, not read); the
binders of `m`'s telescope past the fields (its induction hypotheses) are of the default mode.
The pairing is decided from the records alone; nothing is assumed of the kernel's rules. -/
def Reading.recRules (rd : Reading) (cl : Classifier) (r : Ref) : Except String Unit := do
  let some (c, rr) := recursorAt? rd.s r | throw "no recursor at this reference"
  let x ← rd.rcx cl r
  let base := match r with
    | .member _ i => rootBase c i
    | _ => 0
  let nP := rr.params.toNat
  let nMot := rr.motives.toNat
  let nMin := rr.minors.toNat
  let ((alls, _, _), _) ← (inBlock x.rm (rootKey base) (readForalls x readFuel rr.typ (readSkel x readFuel))).run {}
  unless alls.all (·.1.isDefault) do throw "a recursor's binder with a mode"
  let some (_, _, majorTy) := alls[nP + nMot + nMin + rr.indices.toNat]? |
    throw "a recursor's type has fewer binders than its counts"
  let some ind := Ix.Kernel.Reader.headRef rd.s.store x.owner c majorTy |
    throw "a recursor's major premise is of no inductive"
  let some indV := inductiveAt? rd.s ind | throw "a recursor's major premise is of no inductive"
  unless rr.rules.size == indV.ctors.size do throw "a recursor's rules are not its inductive's constructors"
  for (rule, j) in rr.rules.zipIdx do
    let some ctor := indV.ctors[j]? | throw "a recursor's rules are not its inductive's constructors"
    let nf := rule.fields.toNat
    unless nf == ctor.fields.toNat do throw s!"rule {j}: its field count is not its constructor's"
    let fms ← rd.ctorFieldModes cl ind j
    unless fms.length == nf do throw s!"rule {j}: its constructor's type has not its field count of binders"
    let some body := stripLamsU c (nP + nMot + nMin + nf) rule.rhs |
      throw s!"rule {j}: its right-hand side has fewer λs than its counts"
    let (h, args) ← ixSpineU c readFuel body
    let some w := varOf? c h | throw s!"rule {j}: its right-hand side applies no minor premise"
    unless nf ≤ w && w < nf + nMin do throw s!"rule {j}: its right-hand side applies no minor premise"
    let m := nMin - 1 - (w - nf)
    let some (_, minorSkel, _) := alls[nP + nMot + m]? | throw s!"rule {j}: no minor premise {m}"
    let tele := arrowModes minorSkel
    unless nf ≤ tele.length do
      throw s!"rule {j}: minor premise {m} has fewer binders than its constructor has fields"
    for (fm, q) in fms.zipIdx do
      unless fm.input == .erased do continue
      unless (tele[q]?.map (·.1)) == some .erased do
        throw s!"rule {j}: field {q} is erased in its constructor and not in minor premise {m}, which the rule dispatches"
      let fv := nf - 1 - q
      unless (args[q]?.bind (varOf? c)) == some fv do
        throw s!"rule {j}: its erased field {q} is not passed to minor premise {m} at its own position"
      for (a, p) in args.zipIdx do
        if p != q then
          if (← mentions c readFuel fv a) then
            throw s!"rule {j}: its erased field {q} is mentioned other than at its own position"
    for (i, res) in tele.drop nf do
      unless i == .many && res == .shared do
        throw s!"rule {j}: an induction hypothesis's binder in minor premise {m} has a mode"

/-- The constant heads of a run term's spines, each with its number of arguments: a spine's head
constant, and a constant standing alone (with none). A `Term.case` is a case shape fully
applied, not a call of its constant. -/
def constHeads : Nat → Term → Except String (List (Ref × Nat))
  | 0, _ => throw "term too large"
  | n + 1, t =>
    match t with
    | .app .. => do
      let (h, args) := termSpine t
      let mut out : List (Ref × Nat) ← match h with
        | .const r _ => pure [(r, args.size)]
        | _ => constHeads n h
      for a in args do out := out ++ (← constHeads n a)
      pure out
    | .const r _ => pure [(r, 0)]
    | .lam _ _ _ _ b => constHeads n b
    | .letE _ _ v b => do pure ((← constHeads n v) ++ (← constHeads n b))
    | .proj _ _ e _ => constHeads n e
    | .case _ mj alts ex _ => do
      let mut out ← constHeads n mj
      for a in alts do out := out ++ (← constHeads n a)
      for a in ex do out := out ++ (← constHeads n a)
      pure out
    | .irr | .var .. | .natLit _ | .strLit _ => pure []

/-- **The raw recursors the run bodies call** meet `Reading.recRules`. -/
def Reading.rawRecursors (rd : Reading) (cl : Classifier) (defs : Array (Ref × RunDef)) :
    Except String Unit := do
  let mut seen : Array Ref := #[]
  for (_, d) in defs do
    let .body _ _ _ _ t := d | continue
    for (r, _) in ← constHeads readFuel t do
      if (recursorAt? rd.s r).isSome && !seen.contains r then
        seen := seen.push r
        match rd.recRules cl r with
        | .ok () => pure ()
        | .error e => throw s!"a raw recursor a run body calls ({(repr r).pretty}): {e}"

/-! ## The run program -/

/-- The references of a record: its members, and its inductives' constructors. -/
def refsOf (a : Address) (c : Ixon.Constant) : Array Ref :=
  match c.info with
  | .defn _ | .recr _ | .axio _ | .quot _ => #[.member a 0]
  | .muts ms => Id.run do
    let mut out : Array Ref := #[]
    for (m, i) in ms.zipIdx do
      out := out.push (.member a i)
      if let .indc ind := m then
        for ci in [0:ind.ctors.size] do out := out.push (.ctor a i ci)
    return out
  | _ => #[]

/-- **The run program of a subject**, read with the class oracle `cl`; every raw recursor its run
bodies call meets `Reading.recRules` (V1). -/
def readProg (s : Subject) (cl : Classifier) : Except String Prog := do
  let rd := Reading.make s
  rd.complete
  let rt ← rd.runTable cl
  let mut defs : Array (Ref × RunDef) := #[]
  for a in rd.closure do
    let some c := s.store a | continue
    for r in refsOf a c do
      defs := defs.push (r, ← rd.readDef cl rt true r)
  rd.rawRecursors cl defs
  pure { defs, nat := roleRef? s .nat }


/-! ## Constructor shapes (moved here from `Statement.lean`, so that the class oracle, which
uses them, can sit below the statement that reads with it) -/

section
open Ix.Kernel (Env Key)


/-- A constructor, as the classes need it: its kernel type, its parameter count,
and which of its fields are erased (its binders' modes in its record). -/
structure CtorShape where
  type : KExpr
  nParams : Nat
  erased : List Bool

/-- The record address a kernel key names. -/
def keyAddress (s : Subject) : Key .anon → Option Address
  | .id a => some a
  | .role r => s.table.addressOf? r
  | .aux _ _ => none

/-- The constructors of the inductive type a key names, from the records. -/
def ctorShapes (rd : Reading) (k : Key .anon) : Option (List CtorShape) := do
  let a ← keyAddress rd.s k
  let r ← Ix.Kernel.Reader.resolve rd.s.store a
  let ind ← inductiveAt? rd.s r
  let x ← (rd.rcx noClasses r).toOption
  let .member _ i := r | none
  let base := rootBase x.c i
  let nP := ind.params.toNat
  (List.range ind.ctors.size).mapM fun ci => do
    let ctor ← ind.ctors[ci]?
    let type ← (x.toK [] ctor.typ).toOption
    let ((alls, _, _), _) ← ((inBlock x.rm (rootKey (base + 1 + ci))
      (readForalls x readFuel ctor.typ (readSkel x readFuel))).run {}).toOption
    pure { type, nParams := nP, erased := (alls.drop nP).map fun (m, _, _) => m.input == .erased }


/-- Instantiate a type's leading ∀s with `args`. -/
def instParams : KExpr → List KExpr → Option KExpr
  | t, [] => some t
  | .forallE _ b _, a :: as => instParams (b.instantiate1 a) as
  | _, _ :: _ => none

end

end IxC.Resource

end
