import Compilatrix.Ixon.Eval
import Compilatrix.IxIR0.Eval

/-!
# The erasure pass: Ixon → IxIR₀

The middle of the certification spine. Executable, total (fueled),
and **arity-preserving**: erased binders keep their lambda (and their
argument slot), but

- arguments in erased **positions** are replaced by the unevaluated
  `◻` literal — dropping their *evaluation* is the semantic content
  of erasure (gate A);
- occurrences of dropped binders erase to `◻` (never to a variable
  read — dropped slots are dead by construction);
- types (`sort`, `all`) erase to `◻` wholesale;
- recursor **index** arguments and constructor **param** arguments
  are removed from spines outright — the two deliberate arity
  changes. Constructor values carry kept fields only (the IxIR₀
  object-model contract); complete visible indexed recursor spines
  are covered by the simulation theorem. Arity *trimming* of ghost
  slots is a later IxIR₀ˢ optimization, not erasure's job.

A binder/position is erased when its mode is 0 **or** its domain is
syntactically sort-like (`Sort`, or a Π-chain into one, through
shares) — Coq-extraction-style type-scheme erasure, no typing needed.
The approximation degrades safely: an undetected type flows as a
value and meets `◻` only where syntax reveals it.

Recursors erase **structurally** (their stored counts, not modes):
motives are ghost positions, indices are dropped, minors and value
params are kept. A rule's right-hand side (a kernel-shaped closed
lambda chain over params/motives/minors/fields) is peeled and
re-expressed in the `RecRule` environment convention; the source's
`recur`-self becomes the recSelf slot — `var mask.length`, the index
just past all peeled binders, exactly where IxIR₀'s ι binds the
unapplied recursor.

Addresses survive erasure as environment keys. Members of a `muts`
block get fixed-width synthetic addresses (`memberAddr`; scaffolding
until erased IR is content-addressed);
projection constants become indirections (`defn (ref member)`), ctor
projections become `Decl.ctor` directly, inductive-type constants
become `defn ◻`, opaque/partial definitions and axioms become
`Decl.extern` (the ledger boundary), and quotients compile away
(`mk ↦ λλλ.v₀`, `lift ↦ λ⁶. f q`, `ind ↦ λ⁵. mk q`).

Known v1 gaps (recorded): unknown-telescope **ghost** positions
(higher-order heads) keep their arguments — sound but unerased. The
structural **drop** policies for constructor parameters and recursor
indices require a syntactically visible known head; split or
unknown-head spines can desynchronize source and target arities.
For **constructor parameters** this is no longer a silent gap: a
reference to a known constructor with a nonzero dropped-parameter
count appearing outside a spine that supplies the complete parameter
prefix is an erase-time error (`strictCtorParams`, on by default —
the residual ghost parameters would otherwise still be applied by the
surrounding context and saturate the target constructor early, i.e.
stuck code where the source runs). Split **indexed recursor** spines
remain a recorded gap, rejected only by the validator. Literal
blobs are resolved and inlined at erase time; `natLit` peeling is
enabled by well-known-address comparison against the Nat block.

The pass is validated two ways: differential `#guard`s below run the
same programs through the Ixon reference evaluator and the erased
IxIR₀ interpreter, and `Compilatrix/Sim.lean` proves the simulation
theorem against a proof-producing relational erasure certificate.
-/

namespace Compilatrix.Erase

open Compilatrix.Ixon (Address Uses Owned Constant ConstantInfo MutConst
  Recursor RecursorRule Constructor Definition Univ)
open Compilatrix.Ixon.Eval (Blob unfoldable)

inductive EraseErr where
  | fuel
  | unsupported (msg : String)
  | unknownBlob (adr : Address)
  deriving BEq, Repr

structure EraseCtx where
  resolve : Address → Option Constant
  blobs : Address → Option Blob := fun _ => none
  /-- Well-known address of the `Nat` block: sets `natLit` on its
  recursor's erasure. -/
  natBlock : Option Address := none
  /-- Reject a reference to a known constructor with a nonzero
  dropped-parameter count unless it heads a visible application spine
  supplying the complete parameter prefix. Such split/under-saturated
  heads erase to code whose arity has desynchronized from the source
  (the escaped ghost parameters are still applied by the surrounding
  context and saturate the target constructor early — stuck code where
  the source evaluates). On by default; the proof-producing validator
  turns it off because its substrate is the raw eraser output and it
  rejects the same shapes itself with relation-level diagnostics. -/
  strictCtorParams : Bool := true

/-- Tables of the constant being erased, plus rule-erasure state. -/
structure ETables where
  sharing : Array Compilatrix.Ixon.Expr := #[]
  refs : Array Address := #[]
  selfMuts : Array MutConst := #[]
  curBlock : Option Address := none
  /-- When erasing a recursor rule: the member index whose `recur`
  occurrences map to the recSelf slot. -/
  recSelf : Option Nat := none

/-- Synthetic address for member `idx` of a mutual block (v1
scaffolding — erased IR gets real content addressing later). The
member number is mixed into the final eight bytes without changing
the address width. -/
def memberAddr (block : Address) (idx : Nat) : Address :=
  Address.ofFn fun i =>
    if i.val < 24 then block.get i
    else block.get i ^^^
      UInt8.ofNat (((idx + 1) >>> (8 * (i.val - 24))) % 256)

@[simp] theorem memberAddr_get (block : Address) (idx : Nat) (i : Fin 32) :
    (memberAddr block idx).get i =
      if i.val < 24 then block.get i
      else block.get i ^^^
        UInt8.ofNat (((idx + 1) >>> (8 * (i.val - 24))) % 256) := by
  simp [memberAddr]

def defaultFuel : Nat := 100000

/-! ## Syntactic classification -/

def expandShare (sharing : Array Compilatrix.Ixon.Expr) :
    Nat → Compilatrix.Ixon.Expr → Except EraseErr Compilatrix.Ixon.Expr
  | 0, _ => .error .fuel
  | fuel + 1, e =>
    match e with
    | .share i =>
      match sharing[i.toNat]? with
      | some e' => expandShare sharing fuel e'
      | none => .error (.unsupported s!"share {i.toNat} out of range")
    | e => .ok e

/-- Is this type expression a type *scheme* — `Sort`, or a Π-chain
into one (through shares)? Binders with sort-like domains are erased. -/
def sortLike (sharing : Array Compilatrix.Ixon.Expr) :
    Nat → Compilatrix.Ixon.Expr → Bool
  | 0, _ => false
  | fuel + 1, e =>
    match e with
    | .sort _ => true
    | .all _ _ _ cod => sortLike sharing fuel cod
    | .share i =>
      match sharing[i.toNat]? with
      | some e' => sortLike sharing fuel e'
      | none => false
    | _ => false

/-- Telescope binders (uses, domain) of a type, through shares. -/
def teleBinders (sharing : Array Compilatrix.Ixon.Expr) :
    Nat → Compilatrix.Ixon.Expr → List (Uses × Compilatrix.Ixon.Expr)
  | 0, _ => []
  | fuel + 1, e =>
    match e with
    | .all u _ dom cod => (u, dom) :: teleBinders sharing fuel cod
    | .share i =>
      match sharing[i.toNat]? with
      | some e' => teleBinders sharing fuel e'
      | none => []
    | _ => []

/-- The result world promised by the innermost arrow in a definition
type. A non-function (or an unresolved type share) defaults to shared,
matching `UsageCheck.peelDefn`; fuel exhaustion retains the last visible
arrow rather than inventing a stronger promise. -/
private def teleResultOwned? (sharing : Array Compilatrix.Ixon.Expr) :
    Nat → Compilatrix.Ixon.Expr → Option Owned
  | 0, _ => none
  | fuel + 1, e =>
    match e with
    | .all _ result _ cod =>
      match teleResultOwned? sharing fuel cod with
      | some inner => some inner
      | none => some result
    | .share i =>
      match sharing[i.toNat]? with
      | some e' => teleResultOwned? sharing fuel e'
      | none => none
    | _ => none

def teleResultOwned (sharing : Array Compilatrix.Ixon.Expr) (fuel : Nat)
    (typ : Compilatrix.Ixon.Expr) : Owned :=
  (teleResultOwned? sharing fuel typ).getD .shared

/-- Should a binder with this mode and domain be erased? -/
def dropBinder (sharing : Array Compilatrix.Ixon.Expr) (fuel : Nat)
    (u : Uses) (dom : Compilatrix.Ixon.Expr) : Bool :=
  u == .erased || sortLike sharing fuel dom

/-! ## Argument policies -/

/-- What erasure does to an argument at a given telescope position. -/
inductive ArgPolicy where
  | keep
  | ghost
  | drop
  deriving BEq, Repr

def telePolicies (sharing : Array Compilatrix.Ixon.Expr) (fuel : Nat)
    (typ : Compilatrix.Ixon.Expr) : List ArgPolicy :=
  (teleBinders sharing fuel typ).map fun (u, dom) =>
    if dropBinder sharing fuel u dom then .ghost else .keep

/-- Structural policies for a recursor's applications: value params
kept, type params ghost, motives ghost, minors kept, indices dropped. -/
def recPolicies (sharing : Array Compilatrix.Ixon.Expr) (fuel : Nat)
    (r : Recursor) : List ArgPolicy :=
  let doms := (teleBinders sharing fuel r.typ).take r.params.toNat
  let pPol := doms.map fun (u, dom) =>
    if dropBinder sharing fuel u dom then ArgPolicy.ghost else .keep
  let pPol := pPol ++ List.replicate (r.params.toNat - pPol.length) .keep
  pPol ++ List.replicate r.motives.toNat .ghost
    ++ List.replicate r.minors.toNat .keep
    ++ List.replicate r.indices.toNat .drop

def ctorPolicies (ct : Constructor) : List ArgPolicy :=
  List.replicate ct.params.toNat .drop
    ++ List.replicate ct.fields.toNat .keep

private def mutMember (ctx : EraseCtx) (block : Address) (idx : Nat) :
    Option (Constant × MutConst) := do
  let bc ← ctx.resolve block
  match bc.info with
  | .muts ms => do
    let m ← ms[idx]?
    some (bc, m)
  | _ => none

def memberPolicies (ctx : EraseCtx) (fuel : Nat)
    (sharing : Array Compilatrix.Ixon.Expr) : MutConst → List ArgPolicy
  | .defn d => telePolicies sharing fuel d.typ
  | .recr r => recPolicies sharing fuel r
  | .indc _ => []

/-- Argument policies for a reference to a resolved constant. Unknown
resolution degrades to keep-everything (sound, unerased). -/
def constPolicies (ctx : EraseCtx) (fuel : Nat) (c : Constant) :
    List ArgPolicy :=
  match c.info with
  | .defn d => telePolicies c.sharing fuel d.typ
  | .axio a => telePolicies c.sharing fuel a.typ
  | .quot q => telePolicies c.sharing fuel q.typ
  | .recr r => recPolicies c.sharing fuel r
  | .cPrj p =>
    match mutMember ctx p.block p.idx.toNat with
    | some (_, .indc ind) =>
      match ind.ctors[p.cidx.toNat]? with
      | some ct => ctorPolicies ct
      | none => []
    | _ => []
  | .rPrj p =>
    match mutMember ctx p.block p.idx.toNat with
    | some (bc, .recr r) => recPolicies bc.sharing fuel r
    | _ => []
  | .dPrj p =>
    match mutMember ctx p.block p.idx.toNat with
    | some (bc, .defn d) => telePolicies bc.sharing fuel d.typ
    | _ => []
  | .iPrj _ => []
  | .muts _ => []

/-- Dropped-parameter count of reference `idx` when it resolves to a
known constructor (`cPrj`); `0` for anything else or unresolved. -/
def refCtorParams (ctx : EraseCtx) (T : ETables) (idx : UInt64) : Nat :=
  match T.refs[idx.toNat]? with
  | none => 0
  | some a =>
    match ctx.resolve a with
    | none => 0
    | some c =>
      match c.info with
      | .cPrj p =>
        match mutMember ctx p.block p.idx.toNat with
        | some (_, .indc ind) =>
          match ind.ctors[p.cidx.toNat]? with
          | some ct => ct.params.toNat
          | none => 0
        | _ => 0
      | _ => 0

/-- The pinned `strictCtorParams` diagnostic (exact-message guarded). -/
def splitCtorSpineMsg : String :=
  "constructor parameter prefix is not fully applied (split or under-saturated constructor spine)"

/-- The `strictCtorParams` gate: a known constructor reference with a
nonzero dropped-parameter count must see its complete parameter prefix
in the visible spine (`params ≤ visibleArgs`). Ordinary ghost arguments
at definition heads are untouched — the check keys on `cPrj` structural
drop counts only, never on `ghost` policies. -/
def checkCtorSaturation (ctx : EraseCtx) (T : ETables) (idx : UInt64)
    (visibleArgs : Nat) : Except EraseErr Unit :=
  if !ctx.strictCtorParams then .ok ()
  else
    let params := refCtorParams ctx T idx
    if params == 0 || params ≤ visibleArgs then .ok ()
    else .error (.unsupported splitCtorSpineMsg)

/-- Target of a `recur` reference: the recSelf slot when erasing the
recursor's own rules, a member address otherwise. -/
def recurTarget (T : ETables) (mask : List Bool) (idx : Nat) :
    Except EraseErr IxIR0.Expr :=
  if T.recSelf == some idx then .ok (.var mask.length)
  else
    match T.curBlock with
    | some blk => .ok (.ref (memberAddr blk idx))
    | none => .error (.unsupported "recur reference outside a mutual block")

def headPolicies (ctx : EraseCtx) (fuel : Nat) (T : ETables) :
    Compilatrix.Ixon.Expr → List ArgPolicy
  | .ref idx _ =>
    match T.refs[idx.toNat]? with
    | some a =>
      match ctx.resolve a with
      | some c => constPolicies ctx fuel c
      | none => []
    | none => []
  | .recur idx _ =>
    match T.selfMuts[idx.toNat]? with
    | some m => memberPolicies ctx fuel T.sharing m
    | none => []
  | e@(.lam ..) =>
    (Compilatrix.Ixon.Expr.collectLam e).1.map fun (u, dom) =>
      if dropBinder T.sharing fuel u dom then ArgPolicy.ghost else .keep
  | _ => []

/-! ## Expression erasure -/

mutual

def eraseExpr (ctx : EraseCtx) (fuel : Nat) (T : ETables)
    (mask : List Bool) (e : Compilatrix.Ixon.Expr) :
    Except EraseErr IxIR0.Expr :=
  match fuel with
  | 0 => .error .fuel
  | fuel + 1 =>
    match e with
    | .var i =>
      match mask[i.toNat]? with
      | some true => .ok (.var i.toNat)
      | some false => .ok .erased
      | none => .error (.unsupported s!"unbound variable {i.toNat}")
    | .sort _ => .ok .erased
    | .all _ _ _ _ => .ok .erased
    | .lam u dom body =>
      let dropped := dropBinder T.sharing fuel u dom
      let u' := if dropped then Uses.many else u
      (.lam u' ·) <$> eraseExpr ctx fuel T ((!dropped) :: mask) body
    | .letE _ _ val body => do
      let val' ← eraseExpr ctx fuel T mask val
      let body' ← eraseExpr ctx fuel T (true :: mask) body
      .ok (.letE .many val' body')
    | .prj _ fieldIdx val =>
      (.proj fieldIdx.toNat ·) <$> eraseExpr ctx fuel T mask val
    | .nat idx =>
      match T.refs[idx.toNat]? with
      | none => .error (.unsupported s!"nat literal ref {idx.toNat} out of range")
      | some a =>
        match ctx.blobs a with
        | some (.natB n) => .ok (.lit (.nat n))
        | some (.strB _) => .error (.unsupported "nat literal address holds a string")
        | none => .error (.unknownBlob a)
    | .str idx =>
      match T.refs[idx.toNat]? with
      | none => .error (.unsupported s!"str literal ref {idx.toNat} out of range")
      | some a =>
        match ctx.blobs a with
        | some (.strB s) => .ok (.lit (.str s))
        | some (.natB _) => .error (.unsupported "str literal address holds a nat")
        | none => .error (.unknownBlob a)
    | .share i =>
      match T.sharing[i.toNat]? with
      | none => .error (.unsupported s!"share {i.toNat} out of range")
      | some e' => eraseExpr ctx fuel T mask e'
    | .ref idx _ => do
      -- a bare reference sees zero spine arguments (spine heads are
      -- checked against their visible argument count in `.app` below)
      checkCtorSaturation ctx T idx 0
      match T.refs[idx.toNat]? with
      | some a => pure (.ref a)
      | none => .error (.unsupported s!"ref {idx.toNat} out of range")
    | .recur idx _ => recurTarget T mask idx.toNat
    | .app f a => do
      let (args, base₀) := Compilatrix.Ixon.Expr.collectApp (.app f a)
      let base ← expandShare T.sharing fuel base₀
      let pols := headPolicies ctx fuel T base
      let head : IxIR0.Expr ←
        match base with
        | .ref idx _ => do
          checkCtorSaturation ctx T idx args.length
          match T.refs[idx.toNat]? with
          | some a => pure (.ref a)
          | none => .error (.unsupported s!"ref {idx.toNat} out of range")
        | _ => eraseExpr ctx fuel T mask base
      eraseArgs ctx fuel T mask pols 0 args head
  termination_by fuel

/-- Fold spine arguments over their policies onto the erased head. -/
def eraseArgs (ctx : EraseCtx) (fuel : Nat) (T : ETables)
    (mask : List Bool) (pols : List ArgPolicy) (i : Nat)
    (args : List Compilatrix.Ixon.Expr) (head : IxIR0.Expr) :
    Except EraseErr IxIR0.Expr :=
  match fuel with
  | 0 => .error .fuel
  | fuel + 1 =>
    match args with
    | [] => .ok head
    | a :: rest =>
      match pols[i]? with
      | some .ghost =>
        eraseArgs ctx fuel T mask pols (i + 1) rest (.app head .erased)
      | some .drop => eraseArgs ctx fuel T mask pols (i + 1) rest head
      | _ => do
        let a' ← eraseExpr ctx fuel T mask a
        eraseArgs ctx fuel T mask pols (i + 1) rest (.app head a')
  termination_by fuel

end

/-! ## Constant erasure -/

/-- Peel a kernel-shaped lambda chain against outermost-first keep
flags, accumulating the (innermost-first) mask. -/
def peelRule (sharing : Array Compilatrix.Ixon.Expr) :
    Nat → List Bool → List Bool → Compilatrix.Ixon.Expr →
    Except EraseErr (List Bool × Compilatrix.Ixon.Expr)
  | 0, _, _, _ => .error .fuel
  | _ + 1, [], mask, e => .ok (mask, e)
  | fuel + 1, flag :: flags, mask, e => do
    match ← expandShare sharing fuel e with
    | .lam _ _ body => peelRule sharing fuel flags (flag :: mask) body
    | _ => .error (.unsupported "recursor rule is not a kernel-shaped lambda chain")

def eraseRecursor (ctx : EraseCtx) (fuel : Nat) (T : ETables)
    (blockAddr : Address) (selfIdx : Nat) (r : Recursor) :
    Except EraseErr IxIR0.Decl := do
  let p := r.params.toNat
  let m := r.motives.toNat
  let mi := r.minors.toNat
  let doms := (teleBinders T.sharing fuel r.typ).take p
  let pFlags := doms.map fun (u, dom) => !dropBinder T.sharing fuel u dom
  let pFlags := pFlags ++ List.replicate (p - pFlags.length) true
  let flags := pFlags ++ List.replicate m false ++ List.replicate mi true
  let rules ← r.rules.mapM fun rule => do
    let fl := flags ++ List.replicate rule.fields.toNat true
    let (mask, body) ← peelRule T.sharing fuel fl [] rule.rhs
    let rhs ← eraseExpr ctx fuel { T with recSelf := some selfIdx } mask body
    pure ({ fields := rule.fields.toNat, rhs } : IxIR0.RecRule)
  pure (.recursor (p + m + mi) (ctx.natBlock == some blockAddr) rules)

private def quotMkBody : IxIR0.Expr :=
  .lam .many (.lam .many (.lam .many (.var 0)))

private def quotLiftBody : IxIR0.Expr :=
  .lam .many (.lam .many (.lam .many (.lam .many (.lam .many (.lam .many
    (.app (.var 2) (.var 0)))))))

private def quotIndBody : IxIR0.Expr :=
  .lam .many (.lam .many (.lam .many (.lam .many (.lam .many
    (.app (.var 1) (.var 0))))))

/-- Erase one constant into environment entries (a block yields one
entry per member). -/
def eraseConstant (ctx : EraseCtx) (adr : Address) (c : Constant)
    (fuel : Nat := defaultFuel) :
    Except EraseErr (List (Address × IxIR0.Decl)) := do
  let T : ETables :=
    { sharing := c.sharing, refs := c.refs
      selfMuts := Ixon.Eval.selfMutsOf c.info }
  match c.info with
  | .defn d =>
    if unfoldable d then do
      let body ← eraseExpr ctx fuel T [] d.value
      pure [(adr, .defn (teleResultOwned c.sharing fuel d.typ) body)]
    else
      pure [(adr, .extern (teleBinders c.sharing fuel d.typ).length)]
  | .axio a => pure [(adr, .extern (teleBinders c.sharing fuel a.typ).length)]
  | .quot q =>
    let result := teleResultOwned c.sharing fuel q.typ
    match q.kind with
    | .type => pure [(adr, .defn result .erased)]
    | .ctor => pure [(adr, .defn result quotMkBody)]
    | .lift => pure [(adr, .defn result quotLiftBody)]
    | .ind => pure [(adr, .defn result quotIndBody)]
  | .recr r => do
    let d ← eraseRecursor ctx fuel { T with curBlock := some adr } adr 0 r
    pure [(adr, d)]
  | .cPrj p =>
    match mutMember ctx p.block p.idx.toNat with
    | some (_, .indc ind) =>
      match ind.ctors[p.cidx.toNat]? with
      | some ct => pure [(adr, .ctor p.cidx.toNat ct.fields.toNat)]
      | none => .error (.unsupported "constructor projection out of range")
    | _ => .error (.unsupported "unresolvable constructor projection")
  | .iPrj _ => pure [(adr, .defn .shared .erased)]
  | .rPrj p => pure [(adr, .defn .shared (.ref (memberAddr p.block p.idx.toNat)))]
  | .dPrj p =>
    let result := match mutMember ctx p.block p.idx.toNat with
      | some (bc, .defn d) => teleResultOwned bc.sharing fuel d.typ
      | _ => .shared
    pure [(adr, .defn result (.ref (memberAddr p.block p.idx.toNat)))]
  | .muts ms => do
    let T := { T with curBlock := some adr }
    let mut out := []
    for hi : i in [0:ms.size] do
      match ms[i]! with
      | .defn d =>
        if unfoldable d then do
          let body ← eraseExpr ctx fuel T [] d.value
          let result := teleResultOwned c.sharing fuel d.typ
          out := out ++ [(memberAddr adr i, IxIR0.Decl.defn result body)]
        else
          out := out ++ [(memberAddr adr i,
            IxIR0.Decl.extern (teleBinders c.sharing fuel d.typ).length)]
      | .indc _ =>
        out := out ++ [(memberAddr adr i, IxIR0.Decl.defn .shared .erased)]
      | .recr r => do
        let d ← eraseRecursor ctx fuel T adr i r
        out := out ++ [(memberAddr adr i, d)]
    pure out

/-- Erase a set of constants into an IxIR₀ environment listing. -/
def eraseProgram (ctx : EraseCtx)
    (consts : List (Address × Constant)) (fuel : Nat := defaultFuel) :
    Except EraseErr (List (Address × IxIR0.Decl)) := do
  let mut out := []
  for (adr, c) in consts do
    out := out ++ (← eraseConstant ctx adr c fuel)
  pure out

/-! ## Differential tests

The same store as the reference-evaluator suite (Nat block with
kernel-shaped rules, projection constants, unerased `add`, literal
blobs, a two-param `Pair`), erased and run on **both** interpreters —
an independent executable check of recursors, ghost motives, dropped
constructor parameters, and literal peeling alongside the simulation theorem.
-/

section Tests

open Compilatrix.Ixon.Eval

private def addrOf (n : UInt8) : Address :=
  Address.replicate n

private def aNatBlock := addrOf 0x10
private def aNat := addrOf 0x11
private def aZero := addrOf 0x12
private def aSucc := addrOf 0x13
private def aNatRec := addrOf 0x14
private def aAdd := addrOf 0x15
private def aTwo := addrOf 0x16
private def aThree := addrOf 0x17
private def aPairBlock := addrOf 0x20
private def aMk := addrOf 0x21

private def natInd : Compilatrix.Ixon.Inductive :=
  { isUnsafe := false, lvls := 0, params := 0, indices := 0
    typ := .sort 0
    ctors := #[
      { isUnsafe := false, lvls := 0, cidx := 0, params := 0, fields := 0
        typ := .recur 0 #[] },
      { isUnsafe := false, lvls := 0, cidx := 1, params := 0, fields := 1
        typ := .all .many .shared (.recur 0 #[]) (.recur 0 #[]) }] }

private def natRec : Recursor :=
  { k := false, isUnsafe := false, lvls := 1, params := 0, indices := 0
    motives := 1, minors := 2, typ := .sort 0
    rules := #[
      { fields := 0
        rhs := .lam .many (.sort 0) (.lam .many (.sort 0)
          (.lam .many (.sort 0) (.var 1))) },
      { fields := 1
        rhs := .lam .many (.sort 0) (.lam .many (.sort 0)
          (.lam .many (.sort 0) (.lam .many (.recur 0 #[])
            (.app (.app (.var 1) (.var 0))
              (.app (.app (.app (.app (.recur 1 #[0]) (.var 3)) (.var 2))
                (.var 1)) (.var 0)))))) }] }

private def cNatBlock : Constant :=
  { info := .muts #[.indc natInd, .recr natRec]
    sharing := #[], refs := #[], univs := #[.var 0] }

private def prjConst (info : ConstantInfo) : Constant :=
  { info, sharing := #[], refs := #[], univs := #[] }

private def cNat := prjConst (.iPrj { idx := 0, block := aNatBlock })
private def cZero := prjConst (.cPrj { idx := 0, cidx := 0, block := aNatBlock })
private def cSucc := prjConst (.cPrj { idx := 0, cidx := 1, block := aNatBlock })
private def cNatRec := prjConst (.rPrj { idx := 1, block := aNatBlock })

private def cAdd : Constant :=
  { info := .defn
      { kind := .defn, safety := .safe, lvls := 0
        typ := .all .many .shared (.ref 0 #[])
          (.all .many .shared (.ref 0 #[]) (.ref 0 #[]))
        value := .lam .many (.ref 0 #[]) (.lam .many (.ref 0 #[])
          (.app
            (.app (.app (.app (.ref 3 #[0])
              (.lam .many (.ref 0 #[]) (.ref 0 #[])))
              (.var 1))
              (.lam .many (.ref 0 #[]) (.lam .many (.ref 0 #[])
                (.app (.ref 2 #[]) (.var 0)))))
            (.var 0))) }
    sharing := #[], refs := #[aNat, aZero, aSucc, aNatRec]
    univs := #[.succ .zero] }

/-- A focused non-Lean-fragment declaration proving that result ownership
is read from the source arrow rather than defaulted by erasure. -/
private def cUniqueIdentity : Constant :=
  { info := .defn
      { kind := .defn, safety := .safe, lvls := 0
        typ := .all .affine .unique (.ref 0 #[]) (.ref 0 #[])
        value := .lam .affine (.ref 0 #[]) (.var 0) }
    sharing := #[], refs := #[aNat], univs := #[] }

private def pairInd : Compilatrix.Ixon.Inductive :=
  { isUnsafe := false, lvls := 0, params := 2, indices := 0
    typ := .sort 0
    ctors := #[{ isUnsafe := false, lvls := 0, cidx := 0, params := 2
                 fields := 2, typ := .sort 0 }] }

private def cPairBlock : Constant :=
  { info := .muts #[.indc pairInd]
    sharing := #[], refs := #[], univs := #[.zero] }

private def cMk := prjConst (.cPrj { idx := 0, cidx := 0, block := aPairBlock })

private def program : List (Address × Constant) :=
  [(aNatBlock, cNatBlock), (aNat, cNat), (aZero, cZero), (aSucc, cSucc),
   (aNatRec, cNatRec), (aAdd, cAdd), (aPairBlock, cPairBlock), (aMk, cMk)]

private def resolver : Address → Option Constant := fun a =>
  (program.find? (fun p => p.1 == a)).map (·.2)

private def testBlobs : Address → Option Blob := fun a =>
  if a == aTwo then some (.natB 2)
  else if a == aThree then some (.natB 3)
  else none

private def sctx : EvalCtx :=
  { resolve := resolver, blobs := testBlobs, natBlock := some aNatBlock }

private def ectx : EraseCtx :=
  { resolve := resolver, blobs := testBlobs, natBlock := some aNatBlock }

/-- Test frame refs: 0 = add, 1 = zero, 2 = succ, 3 = blob 2,
4 = blob 3, 5 = mk. -/
private def testF : Frame :=
  { refs := #[aAdd, aZero, aSucc, aTwo, aThree, aMk]
    univs := #[.succ (.succ .zero)] }

private def testT : ETables :=
  { refs := #[aAdd, aZero, aSucc, aTwo, aThree, aMk] }

private def ienv : IxIR0.Env :=
  IxIR0.Env.ofList ((eraseProgram ectx program).toOption.getD [])

private def ictx : IxIR0.Ctx := { env := ienv }

private def sToNatGo : Nat → Value → Option Nat
  | 0, _ => none
  | _, .litV (.natL n) => some n
  | _, .ctorV _ _ 0 [] => some 0
  | f + 1, .ctorV _ _ 1 [v] => (sToNatGo f v).map (· + 1)
  | _, _ => none

private def iToNatGo : Nat → IxIR0.Value → Option Nat
  | 0, _ => none
  | _, .lit (.nat n) => some n
  | _, .ctor _ 0 [] => some 0
  | f + 1, .ctor _ 1 [v] => (iToNatGo f v).map (· + 1)
  | _, _ => none

/-- The differential oracle: source-evaluate, erase, target-evaluate,
compare through the numeral decoders. Demands source success. -/
private def diffNat (e : Compilatrix.Ixon.Expr) : Bool :=
  let sv := match evalClosed sctx testF e with
    | .ok v => sToNatGo 1000000 v
    | .error _ => none
  let tv := match eraseExpr ectx defaultFuel testT [] e with
    | .ok e' =>
      match IxIR0.eval ictx 100000 [] e' with
      | .ok v => iToNatGo 1000000 v
      | .error _ => none
    | .error _ => none
  sv.isSome && sv == tv

private def natE : Nat → Compilatrix.Ixon.Expr
  | 0 => .ref 1 #[]
  | n + 1 => .app (.ref 2 #[]) (natE n)

-- β, let, ctor numerals through the erased env
#guard diffNat (natE 5)
#guard diffNat (.app (.lam .many (.ref 1 #[]) (.var 0)) (natE 4))
#guard diffNat (.letE false (.sort 0) (natE 2) (.app (.ref 2 #[]) (.var 0)))

-- recursor ι with ghost motive slots, both numeral forms
#guard diffNat (.app (.app (.ref 0 #[]) (natE 2)) (natE 3))
#guard diffNat (.app (.app (.ref 0 #[]) (natE 0)) (natE 0))
#guard diffNat (.app (.app (.ref 0 #[]) (natE 7)) (natE 0))
#guard diffNat (.app (.app (.ref 0 #[]) (.nat 3)) (.nat 4))
#guard diffNat (.app (.app (.ref 0 #[]) (natE 1)) (.nat 4))

-- dropped ctor params + projections: mk A B x y, prj skips params on
-- the source side and params are gone on the target side
#guard diffNat (.prj 0 0 (.app (.app (.app (.app (.ref 5 #[]) (.sort 0))
  (.sort 0)) (natE 1)) (natE 2)))
#guard diffNat (.prj 0 1 (.app (.app (.app (.app (.ref 5 #[]) (.sort 0))
  (.sort 0)) (natE 1)) (natE 2)))

-- an erased-binder redex: the argument slot gets ◻ on the target side
#guard diffNat (.app (.app (.lam .many (.sort 0)
  (.lam .many (.ref 1 #[]) (.var 0))) (.sort 0)) (natE 3))

-- structural expectations on the erased declarations
#guard teleResultOwned #[] 100
  (.all .many .shared (.sort 0)
    (.all .affine .unique (.sort 0) (.sort 0))) == .unique
#guard teleResultOwned
  #[.all .many .unique (.sort 0) (.sort 0)] 100 (.share 0) == .unique
#guard
  match eraseConstant ectx (addrOf 0x22) cUniqueIdentity with
  | .ok [(_, .defn .unique (.lam .affine (.var 0)))] => true
  | _ => false
#guard (match ienv aSucc with | some (.ctor 1 1) => true | _ => false)
#guard (match ienv aZero with | some (.ctor 0 0) => true | _ => false)
#guard (match ienv (memberAddr aNatBlock 1) with
  | some (.recursor 3 true _) => true | _ => false)
#guard (match ienv aNat with
  | some (.defn .shared .erased) => true | _ => false)
#guard (match ienv aNatRec with
  | some (.defn .shared (.ref _)) => true | _ => false)

/-! Split/under-saturated constructor-parameter spines are erase-time
errors — the formerly silent stuck-code miscompile — pinned by exact
message (the `lowersErr` house pattern). The complete visible prefix
and ghost arguments at definition heads keep compiling as before. -/

/-- The eraser statically rejects `e` with exactly the expected
diagnostic. -/
private def erasesErr (e : Compilatrix.Ixon.Expr) (expected : String) : Bool :=
  match eraseExpr ectx defaultFuel testT [] e with
  | .error (.unsupported msg) => msg == expected
  | _ => false

/-- `(let f := mk A in f) B x y`: the dropped-parameter prefix escapes
the visible spine. The source saturates fine through the binding. -/
private def splitSpine : Compilatrix.Ixon.Expr :=
  .app (.app (.app (.letE false (.sort 0)
    (.app (.ref 5 #[]) (.sort 0)) (.var 0)) (.sort 0)) (natE 1)) (natE 2)

-- differential negative: the source evaluates to the full pair while
-- erasure (previously stuck target code) now fails closed
#guard (match evalClosed sctx testF splitSpine with
  | .ok (.ctorV _ 0 0 [_, _, _, _]) => true
  | _ => false)
#guard erasesErr splitSpine splitCtorSpineMsg

-- bare head, under-param spine, and a bare head under a let binding
#guard erasesErr (.ref 5 #[]) splitCtorSpineMsg
#guard erasesErr (.app (.ref 5 #[]) (.sort 0)) splitCtorSpineMsg
#guard erasesErr (.letE false (.sort 0) (.ref 5 #[])
    (.app (.app (.app (.app (.var 0) (.sort 0)) (.sort 0)) (natE 1))
      (natE 2)))
  splitCtorSpineMsg

-- the complete parameter prefix still erases to the first-class head
#guard (match eraseExpr ectx defaultFuel testT []
    (.app (.app (.ref 5 #[]) (.sort 0)) (.sort 0)) with
  | .ok (.ref a) => a == aMk
  | _ => false)

end Tests

end Compilatrix.Erase
