import Navigatrix.IxIR1.Eval
import Navigatrix.IxIR0.Examples

/-!
# The IxIR₀ → IxIR₁ lowering (v1: all-shared)

The first executable pass onto the store IR, per the recorded plan
split: **v1 puts every node in the `shared` world** and inserts
Perceus-style refcounting (`dup`/`drop`); the mode-directed stage —
`unique` worlds, `reuse` instead of free+alloc — is stage 2, and
`reuse_sound` is its theorem. What v1 establishes is the *shape*:

- **ANF**: the curried expression tree becomes let-normalized code;
  every intermediate is a binding.
- **Saturation** (gate C): application spines against known heads
  compile to exact-arity `call`/`alloc`/`extern`, under-fill to
  `papp`, over-fill to a saturated call followed by `apply`; unknown
  heads go through `apply` wholesale.
- **Recursor elimination**: a `recursor` declaration becomes a
  function whose body is one `case` on the major premise (with
  `peelNat` mirroring `natLit`); rule right-hand sides are lowered
  with the rule-environment convention mapped onto case fields and
  parameters, and the recursor-self slot compiles to `callSelf` —
  v1 requires self-saturation (an escaping or under-applied recSelf
  is a lowering error, recorded).
- **Lambda lifting**: a `lam` run becomes a fresh top-level function
  over captures ++ parameters; the site builds its value with `papp`
  (a closure *is* a pap). First-class constructors get eta-expanding
  wrapper functions the same way.
- **RC insertion, fused**: source-level occurrence counting drives
  `dup` (a use that is not the last) and `drop` (dead binders, dead
  branch variables, released borrows). Ownership follows the
  `Eval.lean` calling convention: every argument position consumes;
  `fetch` and `case` borrow — a projected field is dup'd to own it,
  and case alternatives dup the fields they use *before* dropping the
  scrutinee. Leak-freedom (`live = 0` after dropping the result) is
  checked by the differential harness on every program.

Synthetic addresses (lifted functions, wrappers) are placeholder
bytes — IxIR₁ content addressing replaces them later. `CtorId.block`
is v1-abused to carry the constructor's own IxIR₀ address (readback
comparison keys on it).

Recorded v1 corners: a *runtime* ◻ flowing into `apply`/`fetch`
through a variable is stuck here but absorbed at IxIR₀ (erasure
discipline never produces it — syntactic ◻ heads are absorbed
statically, with their arguments still lowered and then dropped);
error agreement in the harness is coarse (both-error, kinds not
matched); closures compare opaquely against pap trees.

The differential harness runs the whole hand-written IxIR₀ corpus
through both semantics: readback trees must agree and the lowered run
must be leak-free.
-/

namespace Navigatrix.IxIR1.Lower

open Navigatrix.Ixon (Address Owned)
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
`fun a₁ … aₙ => alloc cid a₁ … aₙ`, memoized per address. -/
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
Every live entry is *owned* — case fields are dup'd into owned slots
at alternative entry — so ownership discipline is uniform: `remaining`
counts source occurrences not yet emitted; a use that leaves
`remaining > 0` dups, the last use moves, and `held` records whether
the slot's ownership is still with it (for branch-entry drops). -/

inductive VEntry where
  | slot (abs remaining : Nat) (held : Bool)
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

/-- Drop the given absolute slots (each drop binds a junk slot). -/
def dropSlots (Γ : VEnv) : List Nat → VEnv × Emit
  | [] => (Γ, id)
  | abs :: rest =>
    let em := emitOp (.drop (.var (Γ.rel abs)))
    let (Γ', em') := dropSlots Γ.bump rest
    (Γ', em ∘ em')

/-- Release owned values whose result is discarded (◻ absorption). -/
def releaseAll (Γ : VEnv) : List AVal → VEnv × Emit
  | [] => (Γ, id)
  | .constA _ :: rest => releaseAll Γ rest
  | .slotA abs :: rest =>
    let em := emitOp (.drop (.var (Γ.rel abs)))
    let (Γ', em') := releaseAll Γ.bump rest
    (Γ', em ∘ em')

private def fuelMsg : String := "lowering fuel exhausted"

mutual

/-- Lower `e` in a consuming position: the returned value carries one
ownership, which the caller must consume exactly once. -/
def lowerE (src : IxIR0.Env) (fuel : Nat) (Γ : VEnv) (e : IxIR0.Expr) :
    LowerM (VEnv × Emit × AVal) :=
  match fuel with
  | 0 => throw fuelMsg
  | fuel + 1 =>
    match e with
    | .var i =>
      match Γ.entries[i]? with
      | none => throw s!"unbound source variable {i}"
      | some (.recSelf _) =>
        throw "recSelf escapes: v1 supports only saturated self-calls"
      | some (.slot abs remaining held) =>
        if !held then throw s!"internal: variable {i} used after release"
        else if remaining ≥ 2 then
          let Γ := Γ.setEntry i (.slot abs (remaining - 1) true)
          let dupAbs := Γ.depth
          pure (Γ.bump, emitOp (.dup (.var (Γ.rel abs))), .slotA dupAbs)
        else if remaining == 1 then
          let Γ := Γ.setEntry i (.slot abs 0 false)
          pure (Γ, id, .slotA abs)
        else throw s!"internal: variable {i} overcounted"
    | .lit l => pure (Γ, id, .constA (.lit l))
    | .erased => pure (Γ, id, .constA .erased)
    | .lam _ _ => lowerLam src fuel Γ e
    | .letE _ val body => do
      let (Γ, em1, av) ← lowerE src fuel Γ val
      let n := countUses 0 body
      match av with
      | .slotA abs =>
        if n == 0 then
          let em2 := emitOp (.drop (.var (Γ.rel abs)))
          let Γ := { Γ with entries := .slot abs 0 false :: Γ.entries,
                            depth := Γ.depth + 1 }
          let (Γ, em3, r) ← lowerE src fuel Γ body
          pure (Γ.pop, em1 ∘ em2 ∘ em3, r)
        else
          let Γ := { Γ with entries := .slot abs n true :: Γ.entries }
          let (Γ, em3, r) ← lowerE src fuel Γ body
          pure (Γ.pop, em1 ∘ em3, r)
      | .constA a =>
        let slotAbs := Γ.depth
        let em2 := emitOp (.pure a)
        let ent : VEntry := if n == 0 then .slot slotAbs 0 false
                            else .slot slotAbs n true
        let Γ := { Γ with entries := ent :: Γ.entries,
                          depth := Γ.depth + 1 }
        let (Γ, em3, r) ← lowerE src fuel Γ body
        pure (Γ.pop, em1 ∘ em2 ∘ em3, r)
    | .app f a => lowerSpine src fuel Γ f [a]
    | .proj i s => do
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
        else
          pure (Γ.bump, emitOp (.papp a #[]), .slotA Γ.depth)
      | some (.ctor tag ar) =>
        if ar == 0 then
          pure (Γ.bump, emitOp (.alloc .shared (ctorIdOf a tag) #[]),
            .slotA Γ.depth)
        else do
          let w ← wrapperFor a tag ar
          pure (Γ.bump, emitOp (.papp w #[]), .slotA Γ.depth)
      | some (.recursor _ _ _) =>
        pure (Γ.bump, emitOp (.papp a #[]), .slotA Γ.depth)
      | some (.extern ar) =>
        if ar == 0 then
          pure (Γ.bump, emitOp (.extern a #[]), .slotA Γ.depth)
        else
          pure (Γ.bump, emitOp (.papp a #[]), .slotA Γ.depth)
  termination_by fuel

/-- Lower `e` in a borrowing position (`fetch` target). The returned
flag says whether the caller must release the value (emit `drop`)
right after the borrowing op: true for temporaries and for a
variable's last occurrence. -/
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
      | some (.slot abs remaining held) =>
        if !held then throw s!"internal: variable {i} borrowed after release"
        else if remaining == 1 then
          let Γ := Γ.setEntry i (.slot abs 0 false)
          pure (Γ, id, .slotA abs, true)   -- last occurrence: release after
        else if remaining ≥ 2 then
          let Γ := Γ.setEntry i (.slot abs (remaining - 1) true)
          pure (Γ, id, .slotA abs, false)
        else throw s!"internal: variable {i} overcounted"
    | _ => do
      let (Γ, em, av) ← lowerE src fuel Γ e
      let release := match av with | .slotA _ => true | .constA _ => false
      pure (Γ, em, av, release)
  termination_by fuel

/-- Flatten and dispatch an application spine. -/
def lowerSpine (src : IxIR0.Env) (fuel : Nat) (Γ : VEnv)
    (h : IxIR0.Expr) (args : List IxIR0.Expr) :
    LowerM (VEnv × Emit × AVal) :=
  match fuel with
  | 0 => throw fuelMsg
  | fuel + 1 =>
    match h with
    | .app f a => lowerSpine src fuel Γ f (a :: args)
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
          knownCall src fuel Γ (.callSelf ·) arity args
      | _ => do
        let (Γ, em1, f) ← lowerE src fuel Γ h
        applyRest src fuel Γ em1 f args
    | .ref a =>
      match src a with
      | none => throw "unknown source reference"
      | some (.defn body) =>
        let n := lamArity body
        if args.length < n then
          knownCall src fuel Γ (.papp a ·) args.length args
        else
          knownCall src fuel Γ (.call a ·) n args
      | some (.ctor tag ar) =>
        if args.length < ar then do
          let w ← wrapperFor a tag ar
          knownCall src fuel Γ (.papp w ·) args.length args
        else
          knownCall src fuel Γ (.alloc .shared (ctorIdOf a tag) ·) ar args
      | some (.recursor numArgs _ _) =>
        let arity := numArgs + 1
        if args.length < arity then
          knownCall src fuel Γ (.papp a ·) args.length args
        else
          knownCall src fuel Γ (.call a ·) arity args
      | some (.extern ar) =>
        if args.length < ar then
          knownCall src fuel Γ (.papp a ·) args.length args
        else
          knownCall src fuel Γ (.extern a ·) ar args
    | _ => do
      let (Γ, em1, f) ← lowerE src fuel Γ h
      applyRest src fuel Γ em1 f args
  termination_by fuel

/-- Lower the first `n` spine arguments, emit `build` over them, and
feed any remaining arguments through `apply`. -/
def knownCall (src : IxIR0.Env) (fuel : Nat) (Γ : VEnv)
    (build : Array Atom → Op) (n : Nat) (args : List IxIR0.Expr) :
    LowerM (VEnv × Emit × AVal) :=
  match fuel with
  | 0 => throw fuelMsg
  | fuel + 1 => do
    let (Γ, em1, avs) ← lowerArgs src fuel Γ (args.take n)
    let atoms := (avs.map (·.toAtom Γ)).toArray
    let res := Γ.depth
    let Γ := Γ.bump
    let em := em1 ∘ emitOp (build atoms)
    if args.length ≤ n then pure (Γ, em, .slotA res)
    else applyRest src fuel Γ em (.slotA res) (args.drop n)
  termination_by fuel

/-- Left-to-right argument lowering (matching IxIR₀'s evaluation
order); atoms are materialized by the caller at the consuming op. -/
def lowerArgs (src : IxIR0.Env) (fuel : Nat) (Γ : VEnv)
    (args : List IxIR0.Expr) : LowerM (VEnv × Emit × List AVal) :=
  match fuel with
  | 0 => throw fuelMsg
  | fuel + 1 =>
    match args with
    | [] => pure (Γ, id, [])
    | a :: rest => do
      let (Γ, em1, av) ← lowerE src fuel Γ a
      let (Γ, em2, avs) ← lowerArgs src fuel Γ rest
      pure (Γ, em1 ∘ em2, av :: avs)
  termination_by fuel

/-- Apply a function value to further arguments (`apply` consumes the
function per the `Eval.lean` convention). A syntactic ◻ function is
absorbed statically — arguments are lowered and released. -/
def applyRest (src : IxIR0.Env) (fuel : Nat) (Γ : VEnv) (pre : Emit)
    (f : AVal) (args : List IxIR0.Expr) : LowerM (VEnv × Emit × AVal) :=
  match fuel with
  | 0 => throw fuelMsg
  | fuel + 1 =>
    match f with
    | .constA .erased => do
      let (Γ, em, avs) ← lowerArgs src fuel Γ args
      let (Γ, em2) := releaseAll Γ avs
      pure (Γ, pre ∘ em ∘ em2, .constA .erased)
    | _ => do
      let (Γ, em, avs) ← lowerArgs src fuel Γ args
      let fAtom := f.toAtom Γ
      let atoms := (avs.map (·.toAtom Γ)).toArray
      let res := Γ.depth
      pure (Γ.bump, pre ∘ em ∘ emitOp (.apply fAtom atoms), .slotA res)
  termination_by fuel

/-- Lift a `lam` run to a fresh top-level function over
captures ++ parameters; the site value is a `papp` of the captures. -/
def lowerLam (src : IxIR0.Env) (fuel : Nat) (Γ : VEnv)
    (e : IxIR0.Expr) : LowerM (VEnv × Emit × AVal) :=
  match fuel with
  | 0 => throw fuelMsg
  | fuel + 1 => do
    let nParams := lamArity e
    let body := stripLams e
    let caps := (List.range Γ.entries.length).filter
      (fun i => countUses i e > 0)
    -- consume one ownership per capture at the site
    let (Γ, emC, capVals) ←
      caps.foldlM (init := (Γ, (id : Emit), ([] : List AVal)))
        fun (Γ, em, acc) i => do
          match Γ.entries[i]? with
          | some (.slot abs r held) =>
            if !held then throw "internal: capture of a released variable"
            else
              let inLam := countUses i e
              if r > inLam then
                let Γ := Γ.setEntry i (.slot abs (r - inLam) true)
                let dupAbs := Γ.depth
                pure (Γ.bump, em ∘ emitOp (.dup (.var (Γ.rel abs))),
                  acc ++ [.slotA dupAbs])
              else if r == inLam then
                let Γ := Γ.setEntry i (.slot abs 0 false)
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
    -- first) at abs (k + nParams - 1 - i)
    let paramEnts := (List.range nParams).map fun i =>
      (.slot (k + nParams - 1 - i) (countUses i body) true : VEntry)
    let outerEnts := (List.range Γ.entries.length).map fun m =>
      if caps.contains m then
        (.slot (caps.idxOf m) (countUses (nParams + m) body) true : VEntry)
      else .slot 0 0 false   -- not free: never referenced
    let paramDrops := (List.range nParams).filterMap fun i =>
      if countUses i body == 0 then some (k + nParams - 1 - i) else none
    let code ← lowerFnBody src fuel
      ⟨paramEnts ++ outerEnts, fnArity⟩ paramDrops body
    pushExtra (fnAddr, .fn ⟨fnArity, code⟩)
    let capAtoms := (capVals.map (·.toAtom Γ)).toArray
    let res := Γ.depth
    pure (Γ.bump, emC ∘ emitOp (.papp fnAddr capAtoms), .slotA res)
  termination_by fuel

/-- Lower a function body: entry drops for dead parameters, then the
body, closed with `ret`. -/
def lowerFnBody (src : IxIR0.Env) (fuel : Nat) (Γ : VEnv)
    (drops : List Nat) (body : IxIR0.Expr) : LowerM Code :=
  match fuel with
  | 0 => throw fuelMsg
  | fuel + 1 => do
    let (Γ, em0) := dropSlots Γ drops
    let (Γ, em, av) ← lowerE src fuel Γ body
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
and parameter slots; the recSelf slot compiles to `callSelf`. -/
def lowerRecursor (src : IxIR0.Env) (fuel : Nat) (numArgs : Nat)
    (natLit : Bool) (rules : Array IxIR0.RecRule) : LowerM FnDef := do
  let arity := numArgs + 1
  let dead : VEntry := .slot 0 0 false
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
             arr.set! srcVar (.slot dupAbs uses true))
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
            (Γ, em, arr.set! (srcVar - nf) (.slot (k - 1) uses true))
    let entries := fieldArr.toList ++ parArr.toList ++ [.recSelf arity]
    let Γrhs : VEnv := { entries, depth := Γ2.depth }
    let (Γ3, emR, av) ← lowerE src fuel Γrhs rule.rhs
    let code := emDups (emMaj (emPar (emR (.ret (av.toAtom Γ3)))))
    pure (Alt.mk tag nf code)
  pure ⟨arity, .case (.var 0) natLit altsL.toArray⟩

/-- Lower one declaration. Constructors get no declaration of their
own (saturated sites `alloc`; first-class sites go through wrappers,
which land in the accumulated extras). -/
def lowerDecl (src : IxIR0.Env) (fuel : Nat) :
    Address × IxIR0.Decl → LowerM (Option (Address × Decl))
  | (a, .defn body) => do
    let n := lamArity body
    let b := stripLams body
    let entries := (List.range n).map fun i =>
      (.slot (n - 1 - i) (countUses i b) true : VEntry)
    let drops := (List.range n).filterMap fun i =>
      if countUses i b == 0 then some (n - 1 - i) else none
    let code ← lowerFnBody src fuel ⟨entries, n⟩ drops b
    pure (some (a, .fn ⟨n, code⟩))
  | (_, .ctor _ _) => pure none
  | (a, .recursor numArgs natLit rules) => do
    pure (some (a, .fn (← lowerRecursor src fuel numArgs natLit rules)))
  | (a, .extern ar) => pure (some (a, .extern ar))

/-- Lower a whole program plus a closed main expression. -/
def lowerAll (decls : List (Address × IxIR0.Decl)) (main : IxIR0.Expr)
    (fuel : Nat := 10000) :
    Except String (List (Address × Decl) × Code) :=
  let src := IxIR0.Env.ofList decls
  let act : LowerM (List (Address × Decl) × Code) := do
    let base ← decls.filterMapM (lowerDecl src fuel)
    let mainC ← lowerFnBody src fuel ⟨[], 0⟩ [] main
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

/-- The differential check: lower the corpus + `e`, run both
semantics; on success the readback trees must agree AND dropping the
result must leave the store empty (leak-freedom of the inserted RC);
on failure both sides must fail (kinds not compared — recorded as
coarse). -/
def diffExpr (e : IxIR0.Expr) (runFuel : Nat := 100000) : Bool :=
  match lowerAll IxIR0.Examples.declList e with
  | .error _ => false
  | .ok (ds, mainC) =>
    let tctx : Ctx := { decls := Env.ofList ds, oracle := tgtOracle }
    match IxIR0.Examples.ctx.run e runFuel, runMain tctx mainC runFuel with
    | .ok v, .ok (store, r) =>
      (match treeOfVal 1000 v, treeOfR store 1000 r with
       | some a, some b => Tree.agree a b
       | _, _ => false)
      && (match dropVal tctx runFuel store r with
          | .ok s => s.live == 0
          | .error _ => false)
    | .error _, .error _ => true
    | _, _ => false

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

end Guards

end Navigatrix.IxIR1.Lower
