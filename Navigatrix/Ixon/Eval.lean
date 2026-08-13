import Navigatrix.Ixon.Const

/-!
# The Ixon reference evaluator

The **source-side** semantics for the erasure simulation: the unerased
twin of `Navigatrix/IxIR0/Eval.lean`, in the same house style
(functional big-step, uniform fuel decrement across the mutual
functions, `∃ fuel` termination statements). This is the runtime
anchor for Ixon terms — NOT a defeq/whnf engine (that is Ix.Tc's and
ix4lean's job).

Semantics choices:

- **Weak CBV**: `lam` and `all` are closure values (no evaluation
  under binders, domains stay lazy); lets are strict; application is
  left-to-right. Types compute for real when they sit in term
  position: `sort` evaluates its level to a natural (closed levels
  always reduce to one), `all` becomes a `piV` closure.
- **Frames**: an expression only means something against its
  constant's tables, so every closure carries a `Frame` (sharing,
  refs, univs, block members, universe instantiation). Entering a
  `ref` switches frames, evaluating the reference's universe
  arguments in the caller's frame to build the callee's `uinst`.
  Universe arities are checked at every reference.
- **Recursor ι is kernel-shaped**: at a saturated recursor, the
  selected rule's (closed) right-hand side is evaluated in the
  recursor's frame and applied to `params ++ motives ++ minors ++
  fields` — indices and the major are not passed, and the ctor
  value's leading params are dropped. Self-reference inside rules is
  ordinary `recur` through the block frame (IxIR₀'s recSelf binding
  is the *erased* target's trick; the source needs none).
- **Unfolding policy**: `defn` and `thm` definitions unfold; `opaq`
  and `partial` do not. Non-unfolding constants (axioms, quotients,
  opaque definitions, inductive types) are **neutral**: applying them
  accumulates a `papV` that never fires — a value, not a stuck state.
- **Literals**: `.nat`/`.str` carry refs-table indices; the address
  resolves through a store-blob oracle (`EvalCtx.blobs`). This pins
  the v2 "blob table" reading: the blob table IS the refs table, and
  literal payloads are content-addressed store blobs. Byte-level blob
  canonicalization (trimmed-LE nats, UTF-8) belongs to the store
  layer; the oracle hands back interpreted values.
- **Nat identity by address**: literal ι-peeling (`0 ↦ ctor 0`,
  `n+1 ↦ ctor 1 [lit n]`) activates when `EvalCtx.natBlock` is set —
  in a nameless world, "this recursor is `Nat.rec`" is a well-known-
  address configuration, not a name check. (v0 peels any literal
  major when configured; only well-typed programs put literals at
  `Nat.rec`, so the block identity is not re-checked.)
- **Modes are inert**: `lam`/`all` modes ride in closure values and
  are never consulted — the source half of "modes don't change
  semantics".

Deferred, recorded: quotient ι (`Quot.lift/ind` on `Quot.mk`), K-like
reduction (a defeq rule, not a runtime one), `String.rec` peeling,
cross-checks of `prj`'s type ref and of ctor-vs-recursor block
agreement (well-typedness makes them redundant; strictness can add
them later).
-/

namespace Navigatrix.Ixon.Eval

/-! ## Universe evaluation -/

/-- Evaluate a level under an instantiation of its variables. Closed
levels always reduce to a natural. Out-of-range variables read as 0
(reachable only from a malformed univs table; arities at references
are checked). -/
def evalUniv (uinst : List Nat) : Univ → Nat
  | .zero => 0
  | .succ u => evalUniv uinst u + 1
  | .max a b => Nat.max (evalUniv uinst a) (evalUniv uinst b)
  | .imax a b =>
    let vb := evalUniv uinst b
    if vb == 0 then 0 else Nat.max (evalUniv uinst a) vb
  | .var i => (uinst[i.toNat]?).getD 0

/-! ## Frames, literals, errors -/

private def selfMutsOf : ConstantInfo → Array MutConst
  | .muts ms => ms
  | _ => #[]

/-- The tables an expression is read against, plus the universe
instantiation of the constant it came from. Closures capture their
frame; entering a reference builds the callee's. -/
structure Frame where
  sharing : Array Expr := #[]
  refs : Array Address := #[]
  univs : Array Univ := #[]
  selfMuts : Array MutConst := #[]
  uinst : List Nat := []

def Frame.ofConst (c : Constant) (uinst : List Nat := []) : Frame :=
  { sharing := c.sharing, refs := c.refs, univs := c.univs
    selfMuts := selfMutsOf c.info, uinst }

inductive Lit where
  | natL (n : Nat)
  | strL (s : String)
  deriving BEq, Repr

/-- A store blob, pre-interpreted (the byte-level codec is the store
layer's concern). -/
inductive Blob where
  | natB (n : Nat)
  | strB (s : String)
  deriving BEq, Repr

inductive Err where
  | fuel
  | stuck (msg : String)
  | unknownRef (adr : Address)
  | unknownBlob (adr : Address)
  deriving BEq, Repr

structure EvalCtx where
  resolve : Address → Option Constant
  blobs : Address → Option Blob := fun _ => none
  /-- Well-known address of the `Nat` mutual block; enables literal
  ι-peeling at recursors. -/
  natBlock : Option Address := none

/-! ## Values -/

inductive NeutralId where
  | const (adr : Address)
  | member (idx : Nat)
  deriving BEq, Repr

/-- Pre-major arity of a recursor (params + motives + minors +
indices), plus one for the major premise. -/
def recArity (r : Recursor) : Nat :=
  r.params.toNat + r.motives.toNat + r.minors.toNat + r.indices.toNat + 1

inductive Head where
  | ctorH (block : Address) (indIdx cidx arity : Nat)
  | recH (recr : Recursor) (F : Frame)
  | neuH (id : NeutralId)

def Head.arity? : Head → Option Nat
  | .ctorH _ _ _ a => some a
  | .recH r _ => some (recArity r)
  | .neuH _ => none

inductive Value where
  | sortV (lvl : Nat)
  | piV (uses : Uses) (owned : Owned) (F : Frame) (env : List Value)
      (dom cod : Expr)
  | closV (uses : Uses) (F : Frame) (env : List Value) (dom body : Expr)
  | papV (h : Head) (args : List Value)
  /-- Constructor application: `args` = param values ++ field values,
  in application order. -/
  | ctorV (block : Address) (indIdx cidx : Nat) (args : List Value)
  | litV (l : Lit)

/-! ## Non-recursive helpers -/

def unfoldable (d : Definition) : Bool :=
  d.kind != .opaq && d.safety != .part

private def guardLvls (lvls : UInt64) (uinst : List Nat) :
    Except Err Unit :=
  if uinst.length == lvls.toNat then .ok ()
  else .error (.stuck
    s!"universe arity mismatch: expected {lvls.toNat}, got {uinst.length}")

def resolveMut (ctx : EvalCtx) (block : Address) (idx : Nat) :
    Except Err (Constant × MutConst) :=
  match ctx.resolve block with
  | none => .error (.unknownRef block)
  | some bc =>
    match (selfMutsOf bc.info)[idx]? with
    | some m => .ok (bc, m)
    | none => .error (.stuck s!"mutual block member {idx} out of range")

def evalUnivArgs (F : Frame) (idxs : Array UInt64) :
    Except Err (List Nat) := do
  let mut out := []
  for i in idxs do
    match F.univs[i.toNat]? with
    | some u => out := out ++ [evalUniv F.uinst u]
    | none => throw (.stuck s!"universe index {i.toNat} out of range")
  return out

/-- View a recursor's major premise as a constructor application,
peeling Nat literals when the context declares a Nat block. -/
def majorCtor (ctx : EvalCtx) : Value → Except Err (Nat × List Value)
  | .ctorV _ _ cidx cargs => .ok (cidx, cargs)
  | .litV (.natL n) =>
    match ctx.natBlock with
    | some _ =>
      match n with
      | 0 => .ok (0, [])
      | n + 1 => .ok (1, [.litV (.natL n)])
    | none => .error (.stuck "literal major premise (no Nat block configured)")
  | _ => .error (.stuck "recursor major premise is not a constructor")

/-! ## The interpreter -/

mutual

def eval (ctx : EvalCtx) (fuel : Nat) (F : Frame) (env : List Value)
    (e : Expr) : Except Err Value :=
  match fuel with
  | 0 => .error .fuel
  | fuel + 1 =>
    match e with
    | .var i =>
      match env[i.toNat]? with
      | some v => .ok v
      | none => .error (.stuck s!"unbound de Bruijn index {i.toNat}")
    | .sort uidx =>
      match F.univs[uidx.toNat]? with
      | some u => .ok (.sortV (evalUniv F.uinst u))
      | none => .error (.stuck s!"sort: universe index {uidx.toNat} out of range")
    | .nat idx =>
      match F.refs[idx.toNat]? with
      | none => .error (.stuck s!"nat literal: ref index {idx.toNat} out of range")
      | some a =>
        match ctx.blobs a with
        | some (.natB n) => .ok (.litV (.natL n))
        | some (.strB _) => .error (.stuck "nat literal address holds a string blob")
        | none => .error (.unknownBlob a)
    | .str idx =>
      match F.refs[idx.toNat]? with
      | none => .error (.stuck s!"str literal: ref index {idx.toNat} out of range")
      | some a =>
        match ctx.blobs a with
        | some (.strB s) => .ok (.litV (.strL s))
        | some (.natB _) => .error (.stuck "str literal address holds a nat blob")
        | none => .error (.unknownBlob a)
    | .lam u dom body => .ok (.closV u F env dom body)
    | .all u o dom cod => .ok (.piV u o F env dom cod)
    | .letE _ _ val body => do
      let v ← eval ctx fuel F env val
      eval ctx fuel F (v :: env) body
    | .app f a => do
      let fv ← eval ctx fuel F env f
      let av ← eval ctx fuel F env a
      apply ctx fuel fv av
    | .prj _ fieldIdx val => do
      match ← eval ctx fuel F env val with
      | .ctorV block indIdx _ args =>
        match resolveMut ctx block indIdx with
        | .ok (_, .indc ind) =>
          match args[ind.params.toNat + fieldIdx.toNat]? with
          | some v => .ok v
          | none => .error (.stuck s!"projection {fieldIdx.toNat} out of range")
        | .ok _ => .error (.stuck "projection: value's inductive not found in block")
        | .error err => .error err
      | .litV _ => .error (.stuck "projection from a literal")
      | _ => .error (.stuck "projection from a non-constructor value")
    | .share i =>
      match F.sharing[i.toNat]? with
      | none => .error (.stuck s!"share index {i.toNat} out of range")
      | some e' => eval ctx fuel F env e'
    | .ref refIdx univIdxs =>
      match F.refs[refIdx.toNat]? with
      | none => .error (.stuck s!"ref index {refIdx.toNat} out of range")
      | some a => do
        let uinst' ← evalUnivArgs F univIdxs
        evalRef ctx fuel a uinst'
    | .recur recIdx univIdxs => do
      let uinst' ← evalUnivArgs F univIdxs
      match F.selfMuts[recIdx.toNat]? with
      | none => .error (.stuck s!"recur index {recIdx.toNat} out of range")
      | some (.defn d) => do
        guardLvls d.lvls uinst'
        if unfoldable d then
          eval ctx fuel { F with uinst := uinst' } [] d.value
        else
          .ok (.papV (.neuH (.member recIdx.toNat)) [])
      | some (.recr r) => do
        guardLvls r.lvls uinst'
        .ok (.papV (.recH r { F with uinst := uinst' }) [])
      | some (.indc ind) => do
        guardLvls ind.lvls uinst'
        .ok (.papV (.neuH (.member recIdx.toNat)) [])
  termination_by fuel

/-- Evaluate a reference to a resolved address: switch frames,
dispatch on the constant's shape. -/
def evalRef (ctx : EvalCtx) (fuel : Nat) (a : Address) (uinst : List Nat) :
    Except Err Value :=
  match fuel with
  | 0 => .error .fuel
  | fuel + 1 =>
    match ctx.resolve a with
    | none => .error (.unknownRef a)
    | some c =>
      match c.info with
      | .defn d => do
        guardLvls d.lvls uinst
        if unfoldable d then
          eval ctx fuel (Frame.ofConst c uinst) [] d.value
        else
          .ok (.papV (.neuH (.const a)) [])
      | .axio ax => do
        guardLvls ax.lvls uinst
        .ok (.papV (.neuH (.const a)) [])
      | .quot q => do
        guardLvls q.lvls uinst
        .ok (.papV (.neuH (.const a)) [])
      | .recr r => do
        guardLvls r.lvls uinst
        .ok (.papV (.recH r (Frame.ofConst c uinst)) [])
      | .iPrj p =>
        match resolveMut ctx p.block p.idx.toNat with
        | .ok (_, .indc ind) => do
          guardLvls ind.lvls uinst
          .ok (.papV (.neuH (.const a)) [])
        | .ok _ => .error (.stuck "inductive projection targets a non-inductive")
        | .error err => .error err
      | .cPrj p =>
        match resolveMut ctx p.block p.idx.toNat with
        | .ok (_, .indc ind) =>
          match ind.ctors[p.cidx.toNat]? with
          | none => .error (.stuck "constructor projection out of range")
          | some ct => do
            guardLvls ct.lvls uinst
            saturate ctx fuel
              (.ctorH p.block p.idx.toNat p.cidx.toNat
                (ct.params.toNat + ct.fields.toNat)) []
        | .ok _ => .error (.stuck "constructor projection targets a non-inductive")
        | .error err => .error err
      | .rPrj p =>
        match resolveMut ctx p.block p.idx.toNat with
        | .ok (bc, .recr r) => do
          guardLvls r.lvls uinst
          .ok (.papV (.recH r (Frame.ofConst bc uinst)) [])
        | .ok _ => .error (.stuck "recursor projection targets a non-recursor")
        | .error err => .error err
      | .dPrj p =>
        match resolveMut ctx p.block p.idx.toNat with
        | .ok (bc, .defn d) => do
          guardLvls d.lvls uinst
          if unfoldable d then
            eval ctx fuel (Frame.ofConst bc uinst) [] d.value
          else
            .ok (.papV (.neuH (.const a)) [])
        | .ok _ => .error (.stuck "definition projection targets a non-definition")
        | .error err => .error err
      | .muts _ => .error (.stuck "direct reference to a mutual block")
  termination_by fuel

def apply (ctx : EvalCtx) (fuel : Nat) (f a : Value) : Except Err Value :=
  match fuel with
  | 0 => .error .fuel
  | fuel + 1 =>
    match f with
    | .closV _ F env _ body => eval ctx fuel F (a :: env) body
    | .papV h args => saturate ctx fuel h (args ++ [a])
    | _ => .error (.stuck "application of a non-function value")
  termination_by fuel

def applyMany (ctx : EvalCtx) (fuel : Nat) (f : Value) (args : List Value) :
    Except Err Value :=
  match fuel with
  | 0 => .error .fuel
  | fuel + 1 =>
    match args with
    | [] => .ok f
    | a :: rest => do
      let f' ← apply ctx fuel f a
      applyMany ctx fuel f' rest
  termination_by fuel

def saturate (ctx : EvalCtx) (fuel : Nat) (h : Head) (args : List Value) :
    Except Err Value :=
  match fuel with
  | 0 => .error .fuel
  | fuel + 1 =>
    match h.arity? with
    | some ar =>
      if args.length == ar then fire ctx fuel h args
      else .ok (.papV h args)
    | none => .ok (.papV h args)
  termination_by fuel

def fire (ctx : EvalCtx) (fuel : Nat) (h : Head) (args : List Value) :
    Except Err Value :=
  match fuel with
  | 0 => .error .fuel
  | fuel + 1 =>
    match h with
    | .ctorH block indIdx cidx _ => .ok (.ctorV block indIdx cidx args)
    | .neuH _ => .ok (.papV h args)
    | .recH r F =>
      match args.getLast? with
      | none => .error (.stuck "recursor fired with no arguments")
      | some major => do
        let (cidx, cargs) ← majorCtor ctx major
        match r.rules[cidx]? with
        | none => .error (.stuck s!"no recursor rule for constructor {cidx}")
        | some rule =>
          if cargs.length != r.params.toNat + rule.fields.toNat then
            .error (.stuck "constructor arity does not match recursor rule")
          else do
            let ruleArgs := args.take
              (r.params.toNat + r.motives.toNat + r.minors.toNat)
            let fields := cargs.drop r.params.toNat
            let rhsV ← eval ctx fuel F [] rule.rhs
            applyMany ctx fuel rhsV (ruleArgs ++ fields)
  termination_by fuel

end

/-! ## Entry points -/

def defaultFuel : Nat := 100000

/-- Evaluate a closed expression against a frame. -/
def evalClosed (ctx : EvalCtx) (F : Frame) (e : Expr)
    (fuel : Nat := defaultFuel) : Except Err Value :=
  eval ctx fuel F [] e

/-- Evaluate a definition constant's value under a universe
instantiation. -/
def evalConst (ctx : EvalCtx) (c : Constant) (uinst : List Nat := [])
    (fuel : Nat := defaultFuel) : Except Err Value :=
  match c.info with
  | .defn d => eval ctx fuel (Frame.ofConst c uinst) [] d.value
  | _ => .error (.stuck "evalConst: not a definition")

/-! ## Elaboration-time tests

A hand-written store: the `Nat` mutual block (inductive + recursor
with real kernel-shaped rules), projection constants for
`Nat`/`zero`/`succ`/`Nat.rec`, an unerased `add`, literal blobs, a
2-parameter `Pair` structure, and unfolding-policy probes. Pure — no
FFI — so the suite runs at elaboration on every build.
-/

private def addrOf (n : UInt8) : Address :=
  ⟨ByteArray.mk (Array.mk (List.replicate 32 n))⟩

private def aNatBlock := addrOf 0x10
private def aNat := addrOf 0x11
private def aZero := addrOf 0x12
private def aSucc := addrOf 0x13
private def aNatRec := addrOf 0x14
private def aAdd := addrOf 0x15
private def aTwo := addrOf 0x16
private def aThree := addrOf 0x17
private def aHello := addrOf 0x18
private def aAx := addrOf 0x19
private def aThm := addrOf 0x1A
private def aOpq := addrOf 0x1B
private def aPairBlock := addrOf 0x20
private def aMk := addrOf 0x21
private def aSortAt := addrOf 0x22
private def aMissing := addrOf 0x30

private def natInd : Inductive :=
  { isUnsafe := false, lvls := 0, params := 0, indices := 0
    typ := .sort 0
    ctors := #[
      { isUnsafe := false, lvls := 0, cidx := 0, params := 0, fields := 0
        typ := .recur 0 #[] },
      { isUnsafe := false, lvls := 0, cidx := 1, params := 0, fields := 1
        typ := .all .many .shared (.recur 0 #[]) (.recur 0 #[]) }] }

/-- `fun motive z s => z` -/
private def natRecZeroRule : RecursorRule :=
  { fields := 0
    rhs := .lam .many (.sort 0) (.lam .many (.sort 0)
      (.lam .many (.sort 0) (.var 1))) }

/-- `fun motive z s n => s n (Nat.rec motive z s n)` — the recursive
reference is `recur 1` (this block's member 1) re-instantiated at the
block's own universe variable (`univs[0] = var 0`). -/
private def natRecSuccRule : RecursorRule :=
  { fields := 1
    rhs := .lam .many (.sort 0) (.lam .many (.sort 0)
      (.lam .many (.sort 0) (.lam .many (.recur 0 #[])
        (.app (.app (.var 1) (.var 0))
          (.app (.app (.app (.app (.recur 1 #[0]) (.var 3)) (.var 2))
            (.var 1)) (.var 0)))))) }

private def natRec : Recursor :=
  { k := false, isUnsafe := false, lvls := 1, params := 0, indices := 0
    motives := 1, minors := 2, typ := .sort 0
    rules := #[natRecZeroRule, natRecSuccRule] }

private def cNatBlock : Constant :=
  { info := .muts #[.indc natInd, .recr natRec]
    sharing := #[], refs := #[], univs := #[.var 0] }

private def prjConst (info : ConstantInfo) : Constant :=
  { info, sharing := #[], refs := #[], univs := #[] }

private def cNat := prjConst (.iPrj { idx := 0, block := aNatBlock })
private def cZero := prjConst (.cPrj { idx := 0, cidx := 0, block := aNatBlock })
private def cSucc := prjConst (.cPrj { idx := 0, cidx := 1, block := aNatBlock })
private def cNatRec := prjConst (.rPrj { idx := 1, block := aNatBlock })

/-- `fun m n => Nat.rec.{1} (fun _ => Nat) m (fun k ih => succ ih) n` —
refs: 0 = Nat, 1 = zero, 2 = succ, 3 = Nat.rec; `univs[0] = 1` is the
motive universe instantiation. -/
private def cAdd : Constant :=
  { info := .defn
      { kind := .defn, safety := .safe, lvls := 0
        typ := .all .many .shared (.ref 0 #[])
          (.all .many .shared (.ref 0 #[]) (.ref 0 #[]))
        value := .lam .many (.ref 0 #[]) (.lam .many (.ref 0 #[])
          (.app (.app (.app (.app (.ref 3 #[0])
            (.lam .many (.ref 0 #[]) (.ref 0 #[])))
            (.var 1))
            (.lam .many (.ref 0 #[]) (.lam .many (.ref 0 #[])
              (.app (.ref 2 #[]) (.var 0)))))
            (.var 0))) }
    sharing := #[], refs := #[aNat, aZero, aSucc, aNatRec]
    univs := #[.succ .zero] }

private def cAx : Constant :=
  { info := .axio { isUnsafe := false, lvls := 0, typ := .sort 0 }
    sharing := #[], refs := #[], univs := #[.zero] }

private def cThm : Constant :=
  { info := .defn
      { kind := .thm, safety := .safe, lvls := 0
        typ := .ref 0 #[], value := .ref 1 #[] }
    sharing := #[], refs := #[aNat, aZero], univs := #[] }

private def cOpq : Constant :=
  { info := .defn
      { kind := .opaq, safety := .safe, lvls := 0
        typ := .ref 0 #[], value := .ref 1 #[] }
    sharing := #[], refs := #[aNat, aZero], univs := #[] }

private def pairInd : Inductive :=
  { isUnsafe := false, lvls := 0, params := 2, indices := 0
    typ := .sort 0
    ctors := #[{ isUnsafe := false, lvls := 0, cidx := 0, params := 2
                 fields := 2, typ := .sort 0 }] }

private def cPairBlock : Constant :=
  { info := .muts #[.indc pairInd]
    sharing := #[], refs := #[], univs := #[.zero] }

private def cMk := prjConst (.cPrj { idx := 0, cidx := 0, block := aPairBlock })

/-- `Sort u` at its own universe variable: instantiation probe. -/
private def cSortAt : Constant :=
  { info := .defn
      { kind := .defn, safety := .safe, lvls := 1
        typ := .sort 0, value := .sort 0 }
    sharing := #[], refs := #[], univs := #[.var 0] }

private def resolver : Address → Option Constant := fun a =>
  (([(aNatBlock, cNatBlock), (aNat, cNat), (aZero, cZero), (aSucc, cSucc),
     (aNatRec, cNatRec), (aAdd, cAdd), (aAx, cAx), (aThm, cThm),
     (aOpq, cOpq), (aPairBlock, cPairBlock), (aMk, cMk),
     (aSortAt, cSortAt)] : List (Address × Constant)).find?
    (fun p => p.1 == a)).map (·.2)

private def testBlobs : Address → Option Blob := fun a =>
  if a == aTwo then some (.natB 2)
  else if a == aThree then some (.natB 3)
  else if a == aHello then some (.strB "hello")
  else none

private def ctx : EvalCtx :=
  { resolve := resolver, blobs := testBlobs, natBlock := some aNatBlock }

/-- Test frame refs: 0 = add, 1 = zero, 2 = succ, 3 = blob 2,
4 = blob 3, 5 = mk, 6 = axiom, 7 = thm, 8 = opaq, 9 = sortAt,
10 = "hello" blob, 11 = Nat, 12 = unresolvable. -/
private def testF : Frame :=
  { refs := #[aAdd, aZero, aSucc, aTwo, aThree, aMk, aAx, aThm, aOpq,
              aSortAt, aHello, aNat, aMissing]
    univs := #[.succ (.succ .zero)]
    sharing := #[.app (.ref 2 #[]) (.ref 1 #[])] }

private def run (e : Expr) : Except Err Value := evalClosed ctx testF e

private def natE : Nat → Expr
  | 0 => .ref 1 #[]
  | n + 1 => .app (.ref 2 #[]) (natE n)

private def toNatGo : Nat → Value → Option Nat
  | 0, _ => none
  | _, .litV (.natL n) => some n
  | _, .ctorV _ _ 0 [] => some 0
  | f + 1, .ctorV _ _ 1 [v] => (toNatGo f v).map (· + 1)
  | _, _ => none

private def runNat? (e : Expr) : Option Nat :=
  match run e with
  | .ok v => toNatGo 1000000 v
  | .error _ => none

-- β, strict let, sharing table
#guard runNat? (.app (.lam .many (.sort 0) (.var 0)) (natE 4)) == some 4
#guard runNat? (.letE false (.sort 0) (natE 2)
  (.app (.ref 2 #[]) (.var 0))) == some 3
#guard runNat? (.share 0) == some 1

-- ctor saturation: zero fires at ref-time, succ stays curried
#guard (match run (.ref 1 #[]) with
  | .ok (.ctorV _ _ 0 []) => true | _ => false)
#guard (match run (.ref 2 #[]) with
  | .ok (.papV (.ctorH _ _ 1 1) []) => true | _ => false)

-- recursor ι through the block, with full universe plumbing
#guard runNat? (.app (.app (.ref 0 #[]) (natE 2)) (natE 3)) == some 5
#guard runNat? (.app (.app (.ref 0 #[]) (natE 0)) (natE 0)) == some 0
#guard runNat? (.app (.app (.ref 0 #[]) (natE 7)) (natE 0)) == some 7

-- literal blobs and ι-peeling (mixed literal/ctor chains decode)
#guard runNat? (.nat 3) == some 2
#guard runNat? (.app (.app (.ref 0 #[]) (.nat 3)) (.nat 4)) == some 5
#guard runNat? (.app (.app (.ref 0 #[]) (natE 1)) (.nat 4)) == some 4
#guard (match run (.str 10) with
  | .ok (.litV (.strL "hello")) => true | _ => false)

-- projections skip constructor params: mk A B x y
#guard runNat? (.prj 0 0 (.app (.app (.app (.app (.ref 5 #[]) (.sort 0))
  (.sort 0)) (natE 1)) (natE 2))) == some 1
#guard runNat? (.prj 0 1 (.app (.app (.app (.app (.ref 5 #[]) (.sort 0))
  (.sort 0)) (natE 1)) (natE 2))) == some 2

-- universes: sorts evaluate, instantiation flows through references
#guard (match run (.sort 0) with | .ok (.sortV 2) => true | _ => false)
#guard (match run (.ref 9 #[0]) with | .ok (.sortV 2) => true | _ => false)

-- Pi and lam are weak-head values
#guard (match run (.all .many .shared (.sort 0) (.sort 0)) with
  | .ok (.piV .many .shared ..) => true | _ => false)

-- unfolding policy: axioms accumulate neutrally, thm unfolds, opaq not
#guard (match run (.app (.ref 6 #[]) (natE 1)) with
  | .ok (.papV (.neuH (.const _)) [_]) => true | _ => false)
#guard (match run (.ref 7 #[]) with
  | .ok (.ctorV _ _ 0 []) => true | _ => false)
#guard (match run (.ref 8 #[]) with
  | .ok (.papV (.neuH (.const _)) []) => true | _ => false)

-- universe arity strictness (sortAt has 1 level, given 0)
#guard (match run (.ref 9 #[]) with | .error (.stuck _) => true | _ => false)

-- error taxonomy
#guard (match run (.ref 99 #[]) with | .error (.stuck _) => true | _ => false)
#guard (match run (.ref 12 #[]) with
  | .error (.unknownRef _) => true | _ => false)
#guard (match run (.nat 12) with
  | .error (.unknownBlob _) => true | _ => false)
#guard (match run (.app (natE 0) (natE 0)) with
  | .error (.stuck _) => true | _ => false)
#guard (match run (.prj 0 0 (natE 0)) with
  | .error (.stuck _) => true | _ => false)

-- fuel: Ω diverges; a starved success is `.fuel`, not `.stuck`
private def delta : Expr := .lam .many (.sort 0) (.app (.var 0) (.var 0))
#guard (match run (.app delta delta) with
  | .error .fuel => true | _ => false)
#guard (match evalClosed ctx testF
    (.app (.app (.ref 0 #[]) (natE 2)) (natE 3)) (fuel := 10) with
  | .error .fuel => true | _ => false)

end Navigatrix.Ixon.Eval
