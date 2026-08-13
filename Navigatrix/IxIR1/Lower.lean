import Navigatrix.IxIR1.Eval
import Navigatrix.IxIR0.Examples

/-!
# The IxIR₀ → IxIR₁ lowering (stage 2: mode-directed)

The two RC strategies of the plan, in one pass. Binder modes (`Uses`
on IxIR₀ `lam`/`letE`, inert until now) direct the memory lowering:

- **`many` → the shared world** (the v1 path): `alloc .shared`,
  Perceus dup/drop from source-occurrence counting.
- **`linear`/`affine` → the unique world**: `alloc .unique`,
  move-only discipline — a unique variable used more than once is a
  *lowering* error (the operational linear check), a dead `linear`
  binding is an error, a dead `affine` binding deep-frees via
  `dropU`. Unique values induce **zero refcount operations** — the
  no-RC strategy, pinned by counter guards.

Worlds flow as top-down **demands**: a let demands its binder-mode
world of the bound value; a saturated known call demands each
argument's world from the callee's lam modes; a constructor
application allocates in the demanded world and demands the same of
its fields (whole-value modes, gate B). Static mode errors at the
boundary: a shared variable at unique demand is dereliction; a unique
variable at shared demand would need a freeze (deferred — needs a
deep-freeze op); both are rejected at lowering time, and whatever the
static layer trusts (call result worlds) the interpreter's dynamic
discipline checker still polices.

Deliberately shared this slice, recorded: function values (paps) and
their captures; partial applications (pap `got` lives under a shared
node); recursor calls entirely (the Lean fragment is all-`many`;
mode-polymorphic recursors arrive with usage polymorphism/IxIR₀ˢ);
projection results (unique destructuring needs a real `case`);
**defn results** (threading result-`Owned` through erasure into
`IxIR0.Decl.defn` is a recorded seam — until then unique values flow
through lets, saturated-call arguments, and constructor fields of a
main expression). Reuse *pairing* (free+alloc → `reuse`) stays
IxIR₂'s optimization as planned: recursor-compiled code allocates
inside its minors, out of reach of alt-local pairing.

## Stage 1 recap (unchanged mechanics)

ANF over absolute compile-time slots; spine saturation against known
heads (exact `call`/`alloc`/`extern`, under-fill `papp`, over-fill
call-then-`apply`); recursors to `case`(+`peelNat`)/`callSelf` with
v1's self-saturation requirement; lambda lifting (a closure is a
`papp` of its captures) and eta wrappers for first-class ctors;
`apply` consumes its pap per the `Eval.lean` convention; case
alternatives dup their fields *before* dropping the scrutinee.

Recorded corners: runtime-◻ into `apply`/`fetch` through a variable
is stuck here, absorbed at IxIR₀ (erasure never produces it);
harness error agreement is coarse; closures compare opaquely against
paps; synthetic addresses are placeholder bytes; `CtorId.block`
carries the source constructor address.

The differential harness runs the corpus through both semantics
(modes are inert at IxIR₀, so source values are unaffected): readback
trees must agree and every successful run must be leak-free — unique
results released by deep free, shared ones by drop.
-/

namespace Navigatrix.IxIR1.Lower

open Navigatrix.Ixon (Address Owned Uses)
open Navigatrix.IxIR0 (Literal)

/-! ## Source-side analyses -/

/-- Occurrences of de Bruijn variable `i` in `e`, any position. -/
def countUses (i : Nat) : IxIR0.Expr → Nat
  | .var j => if j == i then 1 else 0
  | .ref _ | .lit _ | .erased => 0
  | .app f a => countUses i f + countUses i a
  | .lam _ b => countUses (i + 1) b
  | .letE _ v b => countUses i v + countUses (i + 1) b
  | .proj _ s => countUses i s

/-- Length of the leading `lam` run. -/
def lamArity : IxIR0.Expr → Nat
  | .lam _ b => lamArity b + 1
  | _ => 0

/-- Strip the leading `lam` run. -/
def stripLams : IxIR0.Expr → IxIR0.Expr
  | .lam _ b => stripLams b
  | e => e

/-- The binder modes of the leading `lam` run — a known callee's
argument-world signature. -/
def lamUses : IxIR0.Expr → List Uses
  | .lam u b => u :: lamUses b
  | _ => []

/-- The world a binder mode assigns (gate B whole-value scoping):
linear/affine values are unique, everything else shared. -/
def worldOfUses : Uses → Owned
  | .linear | .affine => .unique
  | _ => .shared

/-- Truncate/pad an argument-world list to length `k` (missing
positions — beyond a callee's telescope — demand shared). -/
def padWorlds (ws : List Owned) (k : Nat) : List Owned :=
  ws.take k ++ List.replicate (k - ws.length) .shared

/-! ## The lowering monad -/

/-- Placeholder synthetic address (lifted functions, constructor
wrappers): marker byte + counter, disjoint from the hand-written
corpus space. IxIR₁ content addressing replaces this. -/
def synthAddr (n : Nat) : Address :=
  ⟨ByteArray.mk <| Array.ofFn (n := 32) fun i =>
    if i.val == 0 then 0xFE
    else if i.val ≤ 8 then UInt8.ofNat ((n >>> (8 * (i.val - 1))) % 256)
    else 0xEE⟩

structure LowSt where
  /-- Lifted lambdas and constructor wrappers, accumulated. -/
  extra : List (Address × Decl) := []
  /-- Constructor-wrapper memo: ctor address ↦ wrapper address. -/
  wrappers : List (Address × Address) := []
  fresh : Nat := 0

abbrev LowerM := EStateM String LowSt

def freshAddr : LowerM Address := do
  let st ← get
  set { st with fresh := st.fresh + 1 }
  pure (synthAddr st.fresh)

def pushExtra (d : Address × Decl) : LowerM Unit :=
  modify fun st => { st with extra := d :: st.extra }

/-- v1 constructor identity: the constructor's own IxIR₀ address as
the block, its tag as `cidx`. -/
def ctorIdOf (adr : Address) (tag : Nat) : CtorId := ⟨adr, 0, tag⟩

/-- Eta-expanding wrapper for a first-class constructor use:
`fun a₁ … aₙ => alloc cid a₁ … aₙ`, memoized per address. Wrappers
allocate shared (partial constructor applications live behind shared
paps this slice). -/
def wrapperFor (a : Address) (tag ar : Nat) : LowerM Address := do
  let st ← get
  match st.wrappers.find? (·.1 == a) with
  | some (_, w) => pure w
  | none =>
    let w := synthAddr st.fresh
    let atoms : Array Atom := .ofFn (n := ar) fun i => .var (ar - 1 - i.val)
    let body : Code := .letOp (.alloc .shared (ctorIdOf a tag) atoms)
      (.ret (.var 0))
    set { st with
      fresh := st.fresh + 1,
      wrappers := (a, w) :: st.wrappers,
      extra := (w, .fn ⟨ar, body⟩) :: st.extra }
    pure w

/-! ## Compile-time environment

Runtime positions are tracked as **absolute** slots (distance from the
bottom of the runtime env), immune to later bindings; relative de
Bruijn indices are materialized only at the op that mentions them.
Entries carry their binder mode: `remaining` counts source occurrences
not yet emitted; in the shared world a use that leaves
`remaining > 0` dups and the last use moves, while a unique entry is
move-only (a second use is a lowering error); `held` records whether
the slot's ownership is still with it. -/

inductive VEntry where
  | slot (abs remaining : Nat) (uses : Uses) (held : Bool)
  /-- The rule-environment recursor slot: only a saturated spine head
  (compiled to `callSelf`) is supported in v1. -/
  | recSelf (arity : Nat)

structure VEnv where
  entries : List VEntry := []
  depth : Nat := 0

def VEnv.rel (Γ : VEnv) (abs : Nat) : Nat := Γ.depth - 1 - abs

def VEnv.bump (Γ : VEnv) : VEnv := { Γ with depth := Γ.depth + 1 }

def VEnv.pop (Γ : VEnv) : VEnv := { Γ with entries := Γ.entries.tail }

def VEnv.setEntry (Γ : VEnv) (i : Nat) (e : VEntry) : VEnv :=
  { Γ with entries := Γ.entries.set i e }

/-- A lowered value: an owned runtime slot or an inert scalar atom. -/
inductive AVal where
  | slotA (abs : Nat)
  | constA (a : Atom)

def AVal.toAtom (Γ : VEnv) : AVal → Atom
  | .slotA abs => .var (Γ.rel abs)
  | .constA a => a

/-! ## Emission -/

abbrev Emit := Code → Code

def emitOp (op : Op) : Emit := fun c => .letOp op c

/-- Release owned slots at a binder boundary, by mode: `many` drops,
`affine` deep-frees, a dead `linear` binding is an error. -/
def releaseSlots (Γ : VEnv) : List (Nat × Uses) → LowerM (VEnv × Emit)
  | [] => pure (Γ, id)
  | (abs, u) :: rest => do
    let em ← match u with
      | .many => pure (emitOp (.drop (.var (Γ.rel abs))))
      | .affine => pure (emitOp (.dropU (.var (Γ.rel abs))))
      | .linear => throw "unused linear binding"
      | .erased => throw "internal: erased binder mode survived erasure"
    let (Γ', em') ← releaseSlots Γ.bump rest
    pure (Γ', em ∘ em')

/-- Release owned shared values whose result is discarded
(◻ absorption; arguments there are demanded shared). -/
def releaseAll (Γ : VEnv) : List AVal → VEnv × Emit
  | [] => (Γ, id)
  | .constA _ :: rest => releaseAll Γ rest
  | .slotA abs :: rest =>
    let em := emitOp (.drop (.var (Γ.rel abs)))
    let (Γ', em') := releaseAll Γ.bump rest
    (Γ', em ∘ em')

private def fuelMsg : String := "lowering fuel exhausted"

mutual

/-- Lower `e` in a consuming position at demanded world `w`: the
returned value carries one ownership, which the caller must consume
exactly once. Static producers (allocs, paps, projections) are
world-checked here; call results are trusted to the demand — the
interpreter's dynamic discipline checker polices the rest. -/
def lowerE (src : IxIR0.Env) (fuel : Nat) (Γ : VEnv) (w : Owned)
    (e : IxIR0.Expr) : LowerM (VEnv × Emit × AVal) :=
  match fuel with
  | 0 => throw fuelMsg
  | fuel + 1 =>
    match e with
    | .var i =>
      match Γ.entries[i]? with
      | none => throw s!"unbound source variable {i}"
      | some (.recSelf _) =>
        throw "recSelf escapes: v1 supports only saturated self-calls"
      | some (.slot abs remaining uses held) =>
        if !held then throw s!"internal: variable {i} used after release"
        else if worldOfUses uses != w then
          if worldOfUses uses == .unique then
            throw "freeze needed: unique value at shared demand (deferred)"
          else
            throw "dereliction: shared value at unique demand"
        else if remaining ≥ 2 then
          if worldOfUses uses == .unique then
            throw "unique variable used more than once"
          else
            let Γ := Γ.setEntry i (.slot abs (remaining - 1) uses true)
            let dupAbs := Γ.depth
            pure (Γ.bump, emitOp (.dup (.var (Γ.rel abs))), .slotA dupAbs)
        else if remaining == 1 then
          let Γ := Γ.setEntry i (.slot abs 0 uses false)
          pure (Γ, id, .slotA abs)
        else throw s!"internal: variable {i} overcounted"
    | .lit l => pure (Γ, id, .constA (.lit l))
    | .erased => pure (Γ, id, .constA .erased)
    | .lam _ _ =>
      if w == .unique then
        throw "function values live in the shared world (one-shot closures deferred)"
      else lowerLam src fuel Γ e
    | .letE u val body => do
      let (Γ, em1, av) ← lowerE src fuel Γ (worldOfUses u) val
      let n := countUses 0 body
      match av with
      | .slotA abs =>
        if n == 0 then
          let em2 ← match u with
            | .many => pure (emitOp (.drop (.var (Γ.rel abs))))
            | .affine => pure (emitOp (.dropU (.var (Γ.rel abs))))
            | .linear => throw "unused linear binding"
            | .erased => throw "internal: erased binder mode survived erasure"
          let Γ := { Γ with entries := .slot abs 0 u false :: Γ.entries,
                            depth := Γ.depth + 1 }
          let (Γ, em3, r) ← lowerE src fuel Γ w body
          pure (Γ.pop, em1 ∘ em2 ∘ em3, r)
        else
          let Γ := { Γ with entries := .slot abs n u true :: Γ.entries }
          let (Γ, em3, r) ← lowerE src fuel Γ w body
          pure (Γ.pop, em1 ∘ em3, r)
      | .constA a =>
        let slotAbs := Γ.depth
        let em2 := emitOp (.pure a)
        let ent : VEntry := if n == 0 then .slot slotAbs 0 u false
                            else .slot slotAbs n u true
        let Γ := { Γ with entries := ent :: Γ.entries,
                          depth := Γ.depth + 1 }
        let (Γ, em3, r) ← lowerE src fuel Γ w body
        pure (Γ.pop, em1 ∘ em2 ∘ em3, r)
    | .app f a => lowerSpine src fuel Γ w f [a]
    | .proj i s => do
      if w == .unique then
        throw "projection produces a shared field (unique destructuring deferred)"
      let (Γ, em1, sv, release) ← lowerBorrow src fuel Γ s
      match sv with
      | .constA .erased => pure (Γ, em1, .constA .erased)  -- ◻ absorbs
      | .constA a =>
        -- scalar struct: runtime-stuck on both sides, emit faithfully
        let em2 := emitOp (.fetch a i)
        pure (Γ.bump, em1 ∘ em2, .slotA Γ.depth)
      | .slotA abs =>
        let em2 := emitOp (.fetch (.var (Γ.rel abs)) i)
        let fAbs := Γ.depth
        let Γ := Γ.bump
        let em3 := emitOp (.dup (.var (Γ.rel fAbs)))  -- own the field
        let dAbs := Γ.depth
        let Γ := Γ.bump
        if release then
          let em4 := emitOp (.drop (.var (Γ.rel abs)))
          pure (Γ.bump, em1 ∘ em2 ∘ em3 ∘ em4, .slotA dAbs)
        else
          pure (Γ, em1 ∘ em2 ∘ em3, .slotA dAbs)
    | .ref a =>
      match src a with
      | none => throw "unknown source reference"
      | some (.defn body) =>
        let n := lamArity body
        if n == 0 then
          -- computed global: evaluate now (IxIR₀ evaluates at `ref`)
          pure (Γ.bump, emitOp (.call a #[]), .slotA Γ.depth)
        else if w == .unique then
          throw "function values live in the shared world (one-shot closures deferred)"
        else
          pure (Γ.bump, emitOp (.papp a #[]), .slotA Γ.depth)
      | some (.ctor tag ar) =>
        if ar == 0 then
          pure (Γ.bump, emitOp (.alloc w (ctorIdOf a tag) #[]),
            .slotA Γ.depth)
        else if w == .unique then
          throw "partial constructor applications are shared (deferred)"
        else do
          let w' ← wrapperFor a tag ar
          pure (Γ.bump, emitOp (.papp w' #[]), .slotA Γ.depth)
      | some (.recursor _ _ _) =>
        if w == .unique then
          throw "function values live in the shared world (one-shot closures deferred)"
        else
          pure (Γ.bump, emitOp (.papp a #[]), .slotA Γ.depth)
      | some (.extern ar) =>
        if ar == 0 then
          pure (Γ.bump, emitOp (.extern a #[]), .slotA Γ.depth)
        else if w == .unique then
          throw "function values live in the shared world (one-shot closures deferred)"
        else
          pure (Γ.bump, emitOp (.papp a #[]), .slotA Γ.depth)
  termination_by fuel

/-- Lower `e` in a borrowing position (`fetch` target — shared only:
unique destructuring is deferred with real `case`). The returned flag
says whether the caller must release the value (emit `drop`) right
after the borrowing op: true for temporaries and for a variable's
last occurrence. -/
def lowerBorrow (src : IxIR0.Env) (fuel : Nat) (Γ : VEnv)
    (e : IxIR0.Expr) : LowerM (VEnv × Emit × AVal × Bool) :=
  match fuel with
  | 0 => throw fuelMsg
  | fuel + 1 =>
    match e with
    | .var i =>
      match Γ.entries[i]? with
      | none => throw s!"unbound source variable {i}"
      | some (.recSelf _) => throw "recSelf in a borrowing position"
      | some (.slot abs remaining uses held) =>
        if !held then throw s!"internal: variable {i} borrowed after release"
        else if worldOfUses uses == .unique then
          throw "projection from a unique value (unique destructuring deferred)"
        else if remaining == 1 then
          let Γ := Γ.setEntry i (.slot abs 0 uses false)
          pure (Γ, id, .slotA abs, true)   -- last occurrence: release after
        else if remaining ≥ 2 then
          let Γ := Γ.setEntry i (.slot abs (remaining - 1) uses true)
          pure (Γ, id, .slotA abs, false)
        else throw s!"internal: variable {i} overcounted"
    | _ => do
      let (Γ, em, av) ← lowerE src fuel Γ .shared e
      let release := match av with | .slotA _ => true | .constA _ => false
      pure (Γ, em, av, release)
  termination_by fuel

/-- Flatten and dispatch an application spine; `w` is the demanded
world of the spine's result (allocs use it, call results are trusted
to it). -/
def lowerSpine (src : IxIR0.Env) (fuel : Nat) (Γ : VEnv) (w : Owned)
    (h : IxIR0.Expr) (args : List IxIR0.Expr) :
    LowerM (VEnv × Emit × AVal) :=
  match fuel with
  | 0 => throw fuelMsg
  | fuel + 1 =>
    match h with
    | .app f a => lowerSpine src fuel Γ w f (a :: args)
    | .erased =>
      -- ◻ head: arguments are still evaluated (then discarded), the
      -- application is absorbed statically
      applyRest src fuel Γ id (.constA .erased) args
    | .var i =>
      match Γ.entries[i]? with
      | some (.recSelf arity) =>
        if args.length < arity then
          throw "under-applied recSelf (v1 requires saturated self-calls)"
        else
          knownCall src fuel Γ (.callSelf ·) arity
            (List.replicate arity .shared) args
      | _ => do
        let (Γ, em1, f) ← lowerE src fuel Γ .shared h
        applyRest src fuel Γ em1 f args
    | .ref a =>
      match src a with
      | none => throw "unknown source reference"
      | some (.defn body) =>
        let n := lamArity body
        if args.length < n then
          -- partial application: the arguments live under a shared pap
          knownCall src fuel Γ (.papp a ·) args.length
            (List.replicate args.length .shared) args
        else
          knownCall src fuel Γ (.call a ·) n
            ((lamUses body).map worldOfUses) args
      | some (.ctor tag ar) =>
        if args.length < ar then
          if w == .unique then
            throw "partial constructor applications are shared (deferred)"
          else do
            let w' ← wrapperFor a tag ar
            knownCall src fuel Γ (.papp w' ·) args.length
              (List.replicate args.length .shared) args
        else
          -- whole-value modes: fields are demanded the node's world
          knownCall src fuel Γ (.alloc w (ctorIdOf a tag) ·) ar
            (List.replicate ar w) args
      | some (.recursor numArgs _ _) =>
        -- recursors are the all-`many` fragment this slice
        let arity := numArgs + 1
        if args.length < arity then
          knownCall src fuel Γ (.papp a ·) args.length
            (List.replicate args.length .shared) args
        else
          knownCall src fuel Γ (.call a ·) arity
            (List.replicate arity .shared) args
      | some (.extern ar) =>
        if args.length < ar then
          knownCall src fuel Γ (.papp a ·) args.length
            (List.replicate args.length .shared) args
        else
          knownCall src fuel Γ (.extern a ·) ar
            (List.replicate ar .shared) args
    | _ => do
      let (Γ, em1, f) ← lowerE src fuel Γ .shared h
      applyRest src fuel Γ em1 f args
  termination_by fuel

/-- Lower the first `n` spine arguments at the given per-argument
worlds, emit `build` over them, and feed any remaining arguments
through `apply`. -/
def knownCall (src : IxIR0.Env) (fuel : Nat) (Γ : VEnv)
    (build : Array Atom → Op) (n : Nat) (argWs : List Owned)
    (args : List IxIR0.Expr) : LowerM (VEnv × Emit × AVal) :=
  match fuel with
  | 0 => throw fuelMsg
  | fuel + 1 => do
    let (Γ, em1, avs) ← lowerArgs src fuel Γ
      ((args.take n).zip (padWorlds argWs n))
    let atoms := (avs.map (·.toAtom Γ)).toArray
    let res := Γ.depth
    let Γ := Γ.bump
    let em := em1 ∘ emitOp (build atoms)
    if args.length ≤ n then pure (Γ, em, .slotA res)
    else applyRest src fuel Γ em (.slotA res) (args.drop n)
  termination_by fuel

/-- Left-to-right argument lowering (matching IxIR₀'s evaluation
order), each at its demanded world; atoms are materialized by the
caller at the consuming op. -/
def lowerArgs (src : IxIR0.Env) (fuel : Nat) (Γ : VEnv)
    (args : List (IxIR0.Expr × Owned)) :
    LowerM (VEnv × Emit × List AVal) :=
  match fuel with
  | 0 => throw fuelMsg
  | fuel + 1 =>
    match args with
    | [] => pure (Γ, id, [])
    | (a, aw) :: rest => do
      let (Γ, em1, av) ← lowerE src fuel Γ aw a
      let (Γ, em2, avs) ← lowerArgs src fuel Γ rest
      pure (Γ, em1 ∘ em2, av :: avs)
  termination_by fuel

/-- Apply a function value to further arguments (`apply` consumes the
function per the `Eval.lean` convention); unknown callees demand
shared arguments. A syntactic ◻ function is absorbed statically —
arguments are lowered and released. -/
def applyRest (src : IxIR0.Env) (fuel : Nat) (Γ : VEnv) (pre : Emit)
    (f : AVal) (args : List IxIR0.Expr) : LowerM (VEnv × Emit × AVal) :=
  match fuel with
  | 0 => throw fuelMsg
  | fuel + 1 =>
    match f with
    | .constA .erased => do
      let (Γ, em, avs) ← lowerArgs src fuel Γ
        (args.map (fun a => (a, Owned.shared)))
      let (Γ, em2) := releaseAll Γ avs
      pure (Γ, pre ∘ em ∘ em2, .constA .erased)
    | _ => do
      let (Γ, em, avs) ← lowerArgs src fuel Γ
        (args.map (fun a => (a, Owned.shared)))
      let fAtom := f.toAtom Γ
      let atoms := (avs.map (·.toAtom Γ)).toArray
      let res := Γ.depth
      pure (Γ.bump, pre ∘ em ∘ emitOp (.apply fAtom atoms), .slotA res)
  termination_by fuel

/-- Lift a `lam` run to a fresh top-level function over
captures ++ parameters (captures must be shared — paps are shared
nodes); the site value is a `papp` of the captures. -/
def lowerLam (src : IxIR0.Env) (fuel : Nat) (Γ : VEnv)
    (e : IxIR0.Expr) : LowerM (VEnv × Emit × AVal) :=
  match fuel with
  | 0 => throw fuelMsg
  | fuel + 1 => do
    let nParams := lamArity e
    let us := lamUses e
    let body := stripLams e
    let caps := (List.range Γ.entries.length).filter
      (fun i => countUses i e > 0)
    -- consume one ownership per capture at the site
    let (Γ, emC, capVals) ←
      caps.foldlM (init := (Γ, (id : Emit), ([] : List AVal)))
        fun (Γ, em, acc) i => do
          match Γ.entries[i]? with
          | some (.slot abs r uses held) =>
            if !held then throw "internal: capture of a released variable"
            else if worldOfUses uses == .unique then
              throw "a lambda captures a unique value (deferred)"
            else
              let inLam := countUses i e
              if r > inLam then
                let Γ := Γ.setEntry i (.slot abs (r - inLam) uses true)
                let dupAbs := Γ.depth
                pure (Γ.bump, em ∘ emitOp (.dup (.var (Γ.rel abs))),
                  acc ++ [.slotA dupAbs])
              else if r == inLam then
                let Γ := Γ.setEntry i (.slot abs 0 uses false)
                pure (Γ, em, acc ++ [.slotA abs])
              else throw "internal: capture overcount"
          | some (.recSelf _) =>
            throw "recSelf captured by a lambda (v1 unsupported)"
          | none => throw "internal: capture out of range"
    let fnAddr ← freshAddr
    let k := caps.length
    let fnArity := k + nParams
    -- lifted body venv: runtime env = params.reverse ++ caps.reverse,
    -- so capture j sits at abs j, parameter i (source var i, innermost
    -- first) at abs (k + nParams - 1 - i); parameters keep their
    -- binder modes (a linear parameter is a unique value in the body)
    let paramEnts := (List.range nParams).map fun i =>
      (.slot (k + nParams - 1 - i) (countUses i body)
        (us[i]?.getD .many) true : VEntry)
    let outerEnts := (List.range Γ.entries.length).map fun m =>
      if caps.contains m then
        (.slot (caps.idxOf m) (countUses (nParams + m) body) .many true
          : VEntry)
      else .slot 0 0 .many false   -- not free: never referenced
    let paramDrops := (List.range nParams).filterMap fun i =>
      if countUses i body == 0 then
        some (k + nParams - 1 - i, us[i]?.getD .many)
      else none
    let code ← lowerFnBody src fuel
      ⟨paramEnts ++ outerEnts, fnArity⟩ paramDrops .shared body
    pushExtra (fnAddr, .fn ⟨fnArity, code⟩)
    let capAtoms := (capVals.map (·.toAtom Γ)).toArray
    let res := Γ.depth
    pure (Γ.bump, emC ∘ emitOp (.papp fnAddr capAtoms), .slotA res)
  termination_by fuel

/-- Lower a function body at result demand `w`: mode-directed entry
releases for dead parameters, then the body, closed with `ret`. -/
def lowerFnBody (src : IxIR0.Env) (fuel : Nat) (Γ : VEnv)
    (drops : List (Nat × Uses)) (w : Owned) (body : IxIR0.Expr) :
    LowerM Code :=
  match fuel with
  | 0 => throw fuelMsg
  | fuel + 1 => do
    let (Γ, em0) ← releaseSlots Γ drops
    let (Γ, em, av) ← lowerE src fuel Γ w body
    pure (em0 (em (.ret (av.toAtom Γ))))
  termination_by fuel

end

/-! ## Declaration lowering -/

/-- Compile a recursor to a function: one `case` on the major premise
(last argument), alternatives from the rules. Per alternative: dup the
fields the rule uses (they are borrowed from the scrutinee), *then*
drop the major, then drop parameters dead in this branch, then the
lowered rule rhs. The rule-environment convention
`fields.reverse ++ preMajor.reverse ++ [recSelf]` maps onto case-field
and parameter slots; the recSelf slot compiles to `callSelf`.
Recursors are the all-`many` fragment this slice — everything shared. -/
def lowerRecursor (src : IxIR0.Env) (fuel : Nat) (numArgs : Nat)
    (natLit : Bool) (rules : Array IxIR0.RecRule) : LowerM FnDef := do
  let arity := numArgs + 1
  let dead : VEntry := .slot 0 0 .many false
  let altsL ← rules.toList.zipIdx.mapM fun (rule, tag) => do
    let nf := rule.fields
    let d0 := arity + nf
    -- entry runtime env (bottom-up): pre₁ … pre_numArgs, major,
    -- field₁ … field_nf; field j (1-based) ↔ source var (nf - j)
    let (Γ0, emDups, fieldArr) :=
      (List.range nf).foldl
        (init := ((⟨[], d0⟩ : VEnv), (id : Emit),
                  (List.replicate nf dead).toArray))
        fun (Γ, em, arr) jm1 =>
          let j := jm1 + 1
          let srcVar := nf - j
          let uses := countUses srcVar rule.rhs
          if uses == 0 then (Γ, em, arr)
          else
            let dupAbs := Γ.depth
            (Γ.bump, em ∘ emitOp (.dup (.var (Γ.rel (numArgs + j)))),
             arr.set! srcVar (.slot dupAbs uses .many true))
    -- the rules never see the major: release it (after the field dups)
    let emMaj := emitOp (.drop (.var (Γ0.rel numArgs)))
    let Γ1 := Γ0.bump
    -- pre_k (k = 1..numArgs) at abs (k-1) ↔ source var (nf + numArgs - k)
    let (Γ2, emPar, parArr) :=
      (List.range numArgs).foldl
        (init := (Γ1, (id : Emit), (List.replicate numArgs dead).toArray))
        fun (Γ, em, arr) k0 =>
          let k := k0 + 1
          let srcVar := nf + numArgs - k
          let uses := countUses srcVar rule.rhs
          if uses == 0 then
            (Γ.bump, em ∘ emitOp (.drop (.var (Γ.rel (k - 1)))), arr)
          else
            (Γ, em, arr.set! (srcVar - nf) (.slot (k - 1) uses .many true))
    let entries := fieldArr.toList ++ parArr.toList ++ [.recSelf arity]
    let Γrhs : VEnv := { entries, depth := Γ2.depth }
    let (Γ3, emR, av) ← lowerE src fuel Γrhs .shared rule.rhs
    let code := emDups (emMaj (emPar (emR (.ret (av.toAtom Γ3)))))
    pure (Alt.mk tag nf code)
  pure ⟨arity, .case (.var 0) natLit altsL.toArray⟩

/-- Lower one declaration. Constructors get no declaration of their
own (saturated sites `alloc`; first-class sites go through wrappers,
which land in the accumulated extras). Defn parameters keep their
binder modes (linear parameters are unique values in the body); defn
*results* are lowered at shared demand — threading result-`Owned`
through erasure into `IxIR0.Decl.defn` is a recorded seam. -/
def lowerDecl (src : IxIR0.Env) (fuel : Nat) :
    Address × IxIR0.Decl → LowerM (Option (Address × Decl))
  | (a, .defn body) => do
    let n := lamArity body
    let us := lamUses body
    let b := stripLams body
    let entries := (List.range n).map fun i =>
      (.slot (n - 1 - i) (countUses i b) (us[i]?.getD .many) true : VEntry)
    let drops := (List.range n).filterMap fun i =>
      if countUses i b == 0 then some (n - 1 - i, us[i]?.getD .many)
      else none
    let code ← lowerFnBody src fuel ⟨entries, n⟩ drops .shared b
    pure (some (a, .fn ⟨n, code⟩))
  | (_, .ctor _ _) => pure none
  | (a, .recursor numArgs natLit rules) => do
    pure (some (a, .fn (← lowerRecursor src fuel numArgs natLit rules)))
  | (a, .extern ar) => pure (some (a, .extern ar))

/-- Lower a whole program plus a closed main expression, at the given
result world for the main expression. -/
def lowerAll (decls : List (Address × IxIR0.Decl)) (main : IxIR0.Expr)
    (mainW : Owned := .shared) (fuel : Nat := 10000) :
    Except String (List (Address × Decl) × Code) :=
  let src := IxIR0.Env.ofList decls
  let act : LowerM (List (Address × Decl) × Code) := do
    let base ← decls.filterMapM (lowerDecl src fuel)
    let mainC ← lowerFnBody src fuel ⟨[], 0⟩ [] mainW main
    let st ← get
    pure (base ++ st.extra, mainC)
  match act.run {} with
  | .ok v _ => .ok v
  | .error e _ => .error e

/-! ## Readback and the differential harness

Both semantics read back to first-order trees. Constructor identity
compares by the source address (which v1 threads through
`CtorId.block`); pap nodes compare by missing-arity and stored
arguments (their function addresses differ by construction — wrappers
and lifts are synthetic); IxIR₀ closures are opaque and match any
function-shaped tree. -/

inductive Tree where
  | ctorT (adr : Address) (tag : Nat) (args : List Tree)
  | litT (l : Literal)
  | erasedT
  | papT (missing : Nat) (args : List Tree)
  | funT

mutual

def Tree.agree : Tree → Tree → Bool
  | .ctorT a t as, .ctorT a' t' as' => a == a' && t == t' && agreeList as as'
  | .litT l, .litT l' => l == l'
  | .erasedT, .erasedT => true
  | .papT m as, .papT m' as' => m == m' && agreeList as as'
  | .funT, .papT _ _ => true
  | .papT _ _, .funT => true
  | .funT, .funT => true
  | _, _ => false

def Tree.agreeList : List Tree → List Tree → Bool
  | [], [] => true
  | x :: xs, y :: ys => Tree.agree x y && Tree.agreeList xs ys
  | _, _ => false

end

mutual

def treeOfVal (fuel : Nat) (v : IxIR0.Value) : Option Tree :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match v with
    | .lit l => some (.litT l)
    | .erased => some .erasedT
    | .clos _ _ _ => some .funT
    | .pap h args => (treeOfVals fuel args).map
        (.papT (h.arity - args.length) ·)
    | .ctor a t args => (treeOfVals fuel args).map (.ctorT a t ·)
  termination_by fuel

def treeOfVals (fuel : Nat) (vs : List IxIR0.Value) :
    Option (List Tree) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match vs with
    | [] => some []
    | v :: rest => do
      let t ← treeOfVal fuel v
      let ts ← treeOfVals fuel rest
      pure (t :: ts)
  termination_by fuel

end

mutual

def treeOfR (s : Store) (fuel : Nat) (v : RVal) : Option Tree :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match v with
    | .lit l => some (.litT l)
    | .erased => some .erasedT
    | .loc l =>
      match s.get? l with
      | none => none
      | some box =>
        match box.node with
        | .ctorN cid fields =>
          (treeOfRs s fuel fields.toList).map (.ctorT cid.block cid.cidx ·)
        | .papN _ ar got =>
          (treeOfRs s fuel got.toList).map (.papT (ar - got.size) ·)
  termination_by fuel

def treeOfRs (s : Store) (fuel : Nat) (vs : List RVal) :
    Option (List Tree) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match vs with
    | [] => some []
    | v :: rest => do
      let t ← treeOfR s fuel v
      let ts ← treeOfRs s fuel rest
      pure (t :: ts)
  termination_by fuel

end

/-- Nat decoding on trees (accepting literal tails, as at IxIR₀). -/
def natT? : Tree → Option Nat
  | .ctorT _ 0 [] => some 0
  | .ctorT _ 1 [t] => (natT? t).map (· + 1)
  | .litT (.nat n) => some n
  | _ => none

/-- Target-side oracle mirroring the corpus ledger entry. -/
def tgtOracle : Address → List RVal → Option RVal := fun a args =>
  if a == IxIR0.Examples.natAddExt then
    match args with
    | [.lit (.nat m), .lit (.nat n)] => some (.lit (.nat (m + n)))
    | _ => none
  else none

/-- Release a run's result by its world: unique trees deep-free,
shared ones drop, scalars are inert. -/
def releaseResult (ctx : Ctx) (fuel : Nat) (store : Store) (v : RVal) :
    Except Err Store :=
  match v with
  | .loc l =>
    match store.get? l with
    | none => .error (.mem s!"release of a dead location {l}")
    | some box =>
      match box.world with
      | .unique => dropUVal ctx fuel store v
      | .shared => dropVal ctx fuel store v
  | _ => .ok store

/-- The differential check: lower the corpus + `e` (main at world
`mainW`), run both semantics; on success the readback trees must
agree AND releasing the result must leave the store empty
(leak-freedom of the inserted memory ops); on failure both sides must
fail (kinds not compared — recorded as coarse). -/
def diffExpr (e : IxIR0.Expr) (mainW : Owned := .shared)
    (runFuel : Nat := 100000) : Bool :=
  match lowerAll IxIR0.Examples.declList e mainW with
  | .error _ => false
  | .ok (ds, mainC) =>
    let tctx : Ctx := { decls := Env.ofList ds, oracle := tgtOracle }
    match IxIR0.Examples.ctx.run e runFuel, runMain tctx mainC runFuel with
    | .ok v, .ok (store, r) =>
      (match treeOfVal 1000 v, treeOfR store 1000 r with
       | some a, some b => Tree.agree a b
       | _, _ => false)
      && (match releaseResult tctx runFuel store r with
          | .ok s => s.live == 0
          | .error _ => false)
    | .error _, .error _ => true
    | _, _ => false

/-- Target-only run for counter guards. -/
def checkLowered (e : IxIR0.Expr) (mainW : Owned)
    (p : Store → RVal → Bool) : Bool :=
  match lowerAll IxIR0.Examples.declList e mainW with
  | .error _ => false
  | .ok (ds, mainC) =>
    match runMain { decls := Env.ofList ds, oracle := tgtOracle } mainC with
    | .ok (store, r) => p store r
    | .error _ => false

/-- The lowering statically rejects `e` at the given main world. -/
def lowersErr (e : IxIR0.Expr) (mainW : Owned) : Bool :=
  match lowerAll IxIR0.Examples.declList e mainW with
  | .error _ => true
  | .ok _ => false

section Guards

open Navigatrix.IxIR0.Examples

/-! β, let, dup (a variable consumed twice), projection -/

#guard diffExpr (.app (.lam .many (.var 0)) (natE 4))
#guard diffExpr (.letE .many (natE 2) (.app (.ref natSucc) (.var 0)))
#guard diffExpr (.letE .many (natE 2)
  (.app (.app (.ref pairMk) (.var 0)) (.var 0)))
#guard diffExpr (.proj 0 (.app (.app (.ref pairMk) (natE 1)) (natE 2)))
#guard diffExpr (.proj 1 (.app (.app (.ref pairMk) (natE 1)) (natE 2)))
#guard diffExpr (.proj 5 (.app (.app (.ref pairMk) (natE 1)) (natE 2)))
#guard diffExpr (.app (.ref pairMk) (natE 1))   -- first-class ctor pap

-- dead binding: the inserted drop reclaims the unused 1̂
#guard diffExpr (.letE .many (natE 1) (natE 2))

-- a struct borrowed twice: released only after its last projection
#guard diffExpr (.letE .many (.app (.app (.ref pairMk) (natE 1)) (natE 2))
  (.app (.app (.ref natAddDef) (.proj 0 (.var 0))) (.proj 1 (.var 0))))

/-! Recursor ι: `case` + `callSelf`, constructor and peeled-literal
majors -/

#guard diffExpr (.app (.app (.ref natAddDef) (natE 2)) (natE 3))
#guard diffExpr (.app (.app (.ref natAddDef) (natE 0)) (natE 0))
#guard diffExpr (.app (.app (.ref natAddDef) (natE 7)) (natE 0))
#guard diffExpr (.app (.app (.ref natAddDef) (.lit (.nat 2))) (.lit (.nat 3)))
#guard diffExpr (.app (.app (.ref natAddDef) (natE 1)) (.lit (.nat 3)))

/-! List recursion, including a shared (dup'd) list argument -/

#guard diffExpr
  (.app (.app (.ref appendDef) (listE natE [1, 2])) (listE natE [3]))
#guard diffExpr
  (.app (.app (.ref appendDef) (listE natE [])) (listE natE []))
#guard diffExpr (.app (.ref lengthDef) (listE natE [5, 6, 7]))
#guard diffExpr (.letE .many (listE natE [1])
  (.app (.app (.ref appendDef) (.var 0)) (.var 0)))

/-! Externs (success and both-sides refusal) -/

#guard diffExpr
  (.app (.app (.ref natAddExt) (.lit (.nat 20))) (.lit (.nat 22)))
#guard diffExpr (.app (.app (.ref natAddExt) (natE 1)) (.lit (.nat 1)))

/-! ◻ absorption (arguments still lowered, then released), stuckness -/

#guard diffExpr (.app .erased (natE 1))
#guard diffExpr (.proj 0 .erased)
#guard diffExpr (.app (.lit (.nat 1)) (.lit (.nat 2)))

/-! Lambda lifting with a capture:
`(fun x => (fun y => add x y) 2̂) 3̂` -/

#guard diffExpr (.app (.lam .many (.app (.lam .many
  (.app (.app (.ref natAddDef) (.var 1)) (.var 0))) (natE 2))) (natE 3))

/-! Divergence: Ω exhausts fuel on both sides -/

#guard diffExpr
  (.app (.lam .many (.app (.var 0) (.var 0)))
    (.lam .many (.app (.var 0) (.var 0))))
  (runFuel := 300)

/-! The lowering rejects unknown references at compile time -/

#guard
  match lowerAll IxIR0.Examples.declList (.ref (synthAddr 999)) with
  | .error _ => true
  | .ok _ => false

/-! Target-side readback: lowered 2+3 really is 5̂ -/

#guard
  match lowerAll IxIR0.Examples.declList
      (.app (.app (.ref natAddDef) (natE 2)) (natE 3)) with
  | .ok (ds, c) =>
    (match runMain { decls := Env.ofList ds, oracle := tgtOracle } c with
     | .ok (s, v) => ((treeOfR s 1000 v).bind natT?) == some 5
     | _ => false)
  | _ => false

/-! ## Stage 2: the unique world

The same corpus expressions flip worlds by demand: `natE`/`pairMk`
spines at unique demand allocate unique. Linear/affine programs run
with **zero refcount operations** — the no-RC strategy, as counter
`#guard`s — and unique results release by deep free in the harness. -/

-- linear pair of linear nats: values agree with IxIR₀, leak-free
private def linPair : IxIR0.Expr :=
  .letE .linear (natE 2) (.letE .linear (natE 3)
    (.app (.app (.ref pairMk) (.var 1)) (.var 0)))

#guard diffExpr linPair (mainW := .unique)

-- …and with zero RC traffic: 8 unique allocations, nothing else
#guard checkLowered linPair .unique fun s _ =>
  s.allocs == 8 && s.rcops == 0 && s.frees == 0 && s.live == 8

-- a whole unique tree without lets
#guard diffExpr (.app (.app (.ref pairMk) (natE 1)) (natE 2))
  (mainW := .unique)
#guard checkLowered (.app (.app (.ref pairMk) (natE 1)) (natE 2))
  .unique fun s _ => s.allocs == 6 && s.rcops == 0 && s.live == 6

-- dead affine: dropU deep-frees the unused 2̂ (3 nodes), no RC ops
private def affDead : IxIR0.Expr := .letE .affine (natE 2) (natE 1)

#guard diffExpr affDead (mainW := .unique)
#guard checkLowered affDead .unique fun s _ =>
  s.allocs == 5 && s.frees == 3 && s.rcops == 0 && s.live == 2

/-! Static mode errors: the lowering is the operational usage check -/

-- a dead linear binding
#guard lowersErr (.letE .linear (natE 1) (natE 2)) .shared

-- a unique variable used twice
#guard lowersErr (.letE .linear (natE 1)
  (.app (.app (.ref pairMk) (.var 0)) (.var 0))) .unique

-- dereliction: a shared value at unique demand
#guard lowersErr (.letE .many (natE 1) (.app (.ref natSucc) (.var 0)))
  .unique

-- freeze needed: a unique value at shared demand
#guard lowersErr (.letE .linear (natE 1) (.app (.ref natSucc) (.var 0)))
  .shared

-- a unique value into a recursor (the all-`many` fragment)
#guard lowersErr (.letE .linear (natE 1)
  (.app (.app (.ref natAddDef) (.var 0)) (natE 1))) .shared

-- function values live in the shared world
#guard lowersErr (.letE .linear (.lam .many (.var 0)) (.var 0)) .shared

-- projection from a unique value
#guard lowersErr
  (.letE .linear (.app (.app (.ref pairMk) (natE 1)) (natE 2))
    (.proj 0 (.var 0))) .shared

end Guards

end Navigatrix.IxIR1.Lower
