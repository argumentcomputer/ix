import Ix.Compiler.IxIR1.Eval
import Ix.Compiler.IxIR0.Examples

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
variable at shared demand would need a deep freeze. The v0 contract
rejects both directions in `UsageCheck` and retains these lowering
checks as backstops; the planned freeze lift and its wake conditions
are recorded in `docs/compiler/lowering-restrictions.md`.

Function values (paps) and their captures are deliberately shared in
this slice. Since `apply` consequently supplies shared arguments, only
all-`many` telescopes may become function values or partial
applications; a non-`many` function is accepted only as a saturated
known call, otherwise lowering rejects it. Also deliberately shared:
recursor calls entirely (the Lean fragment is all-`many`;
mode-polymorphic recursors arrive with usage polymorphism/IxIR₀ˢ),
projection results (unique destructuring needs a real `case`). Definition
result worlds are carried by both IRs and checked at every statically known
call; unknown `apply` remains shared-only until paps carry a richer callable
type. Extern calls use the evaluator's enforced scalar-only
ABI; a future heap-valued extern needs an explicit ownership policy.
Reuse *pairing* (free+alloc → `reuse`) stays
IxIR₂'s optimization as planned: recursor-compiled code allocates
inside its minors, out of reach of alt-local pairing.

## Stage 1 recap (unchanged mechanics)

ANF over absolute compile-time slots; spine saturation against known
heads (exact `call`/`alloc`/`extern`, sound under-fill `papp`, over-fill
call-then-`apply`); recursors to `case`(+`peelNat`)/`callSelf` with
v1's self-saturation requirement; lambda lifting (a closure is a
`papp` of its captures) and eta wrappers for first-class ctors;
`apply` consumes its pap per the `Eval.lean` convention; case
alternatives dup their fields *before* dropping the scrutinee.

Recorded corners: runtime-◻ into `apply`/`fetch` through a variable
is stuck here, absorbed at IxIR₀ (erasure never produces it);
closures compare opaquely against
paps; synthetic addresses are placeholder bytes; `CtorId.block`
carries the source constructor address.

The differential harness runs the corpus through both semantics
(modes are inert at IxIR₀, so source values are unaffected): readback
trees must agree and every successful run must be leak-free — unique
results released by deep free, shared ones by drop. Error runs agree
only through the deliberate `errAgree` mapping (exact kinds,
addresses, and pinned message pairs — never any-error-vs-any-error).
-/

namespace Ix.Compiler.IxIR1.Lower

open Ix.Compiler.Ixon (Address Owned Uses)
open Ix.Compiler.IxIR0 (Literal)

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

@[simp] theorem lamUses_length (e : IxIR0.Expr) :
    (lamUses e).length = lamArity e := by
  induction e <;> simp [lamUses, lamArity, *]

/-- Shared paps can soundly accept only shared (`many`) parameters.
Non-`many` functions must remain visible as saturated known calls. -/
def papSafe (e : IxIR0.Expr) : Bool :=
  (lamUses e).all fun u => u == .many

/-- Stable diagnostic for the v0 no-freeze policy.  Kept public so the
executable restriction corpus cannot drift from the lowerer. -/
def freezeNeededMsg : String :=
  "freeze not in v0: unique value at non-unique sink (see docs/compiler/lowering-restrictions.md)"

/-- Stable diagnostic for first-class functions whose telescope is not
all-`many`. -/
def nonManyPapMsg : String :=
  "non-many function values require saturated known calls (one-shot paps deferred)"

/-- Stable diagnostic for consuming projection from a unique source. -/
def uniqueDestructuringMsg : String :=
  "projection from a unique value (unique destructuring deferred)"

/-- Stable diagnostic for a unique value captured by a shared closure. -/
def uniqueCaptureMsg : String :=
  "a lambda captures a unique value (deferred)"

/-- Stable diagnostic for a recursive-self value used below saturation. -/
def underAppliedRecSelfMsg : String :=
  "under-applied recSelf (v1 requires saturated self-calls)"

/-- The complete policy inventory for the current IxIR₀ → IxIR₁ lowerer.
Each entry has an exact executable rejection witness in `Guards`; the design
ledger and wake conditions live in `docs/compiler/lowering-restrictions.md`. -/
inductive RestrictionKind where
  | freeze
  | uniqueDestructuring
  | sharedFunctionValues
  | uniqueCapture
  | modeMonomorphicRecursors
  | saturatedRecSelf
  deriving BEq, DecidableEq, Repr, Inhabited

namespace RestrictionKind

def all : Array RestrictionKind := #[
  .freeze,
  .uniqueDestructuring,
  .sharedFunctionValues,
  .uniqueCapture,
  .modeMonomorphicRecursors,
  .saturatedRecSelf
]

/-- The diagnostic pinned by the representative witness for each policy.
Mode-monomorphic recursors reject a unique major through the already-decided
no-freeze boundary, so those two categories deliberately share a message. -/
def diagnostic : RestrictionKind → String
  | .freeze | .modeMonomorphicRecursors => freezeNeededMsg
  | .uniqueDestructuring => uniqueDestructuringMsg
  | .sharedFunctionValues => nonManyPapMsg
  | .uniqueCapture => uniqueCaptureMsg
  | .saturatedRecSelf => underAppliedRecSelfMsg

end RestrictionKind

#guard RestrictionKind.all.size == 6
#guard RestrictionKind.all.toList.eraseDups.length == 6

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
  Address.ofFn fun i =>
    if i.val == 0 then 0xFE
    else if i.val ≤ 8 then UInt8.ofNat ((n >>> (8 * (i.val - 1))) % 256)
    else 0xEE

structure WrapperMemo where
  source : Address
  tag : Nat
  arity : Nat
  wrapper : Address
  deriving BEq

def WrapperMemo.matches (memo : WrapperMemo) (source : Address)
    (tag arity : Nat) : Bool :=
  memo.source == source && memo.tag == tag && memo.arity == arity

structure LowSt where
  /-- Lifted lambdas and constructor wrappers, accumulated. -/
  extra : List (Address × Decl) := []
  /-- Constructor-wrapper memo, including the source shape used to build
  the wrapper. Recording the shape makes cache consistency explicit and
  prevents an inconsistent internal caller from reusing the wrong eta
  expansion for the same address. -/
  wrappers : List WrapperMemo := []
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

/-- The declaration installed for one first-class constructor wrapper. -/
def descendingVars : Nat → List Atom
  | 0 => []
  | arity + 1 => .var arity :: descendingVars arity

@[simp] theorem descendingVars_length (arity : Nat) :
    (descendingVars arity).length = arity := by
  induction arity with
  | zero => rfl
  | succ arity ih => simp [descendingVars, ih]

def ctorWrapperDecl (source : Address) (tag arity : Nat) : Decl :=
  let atoms := (descendingVars arity).toArray
  .fn ⟨arity, .shared, true,
    .letOp (.alloc .shared (ctorIdOf source tag) atoms)
      (.ret (.var 0))⟩

/-- Eta-expanding wrapper for a first-class constructor use:
`fun a₁ … aₙ => alloc cid a₁ … aₙ`, memoized per address. Wrappers
allocate shared (partial constructor applications live behind shared
paps this slice). -/
def wrapperFor (a : Address) (tag ar : Nat) : LowerM Address := do
  let st ← get
  match st.wrappers.find? (·.matches a tag ar) with
  | some memo => pure memo.wrapper
  | none =>
    let w := synthAddr st.fresh
    set { st with
      fresh := st.fresh + 1,
      wrappers := ⟨a, tag, ar, w⟩ :: st.wrappers,
      extra := (w, ctorWrapperDecl a tag ar) :: st.extra }
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

/-- Canonical parameter entries, listed in source-variable order
(innermost first). `base` is the number of older absolute slots below the
parameter telescope; `remaining i` is the occurrence count of source
de-Bruijn variable `i`. -/
def parameterEntries (base : Nat) :
    List Uses → (Nat → Nat) → List VEntry
  | [], _ => []
  | uses :: tail, remaining =>
    parameterEntries (base + 1) tail remaining ++
      [.slot base (remaining tail.length) uses true]

/-- Dependent traversal for the canonical parameter-entry builder.  Tail
layout, absolute-slot advancement, and outer-slot construction recurse once;
clients provide only empty and appended-slot result constructors. -/
theorem parameterEntries_traverse
    (remaining : Nat → Nat)
    {Result : Nat → List Uses → List VEntry → Prop}
    (hnil : ∀ base, Result base [] [])
    (hcons : ∀ {base : Nat} {mode : Uses} {modes : List Uses}
        {tail : List VEntry},
      Result (base + 1) modes tail →
      Result base (mode :: modes)
        (tail ++ [.slot base (remaining modes.length) mode true])) :
    ∀ (base : Nat) (modes : List Uses),
      Result base modes (parameterEntries base modes remaining) := by
  intro base modes
  induction modes generalizing base with
  | nil => exact hnil base
  | cons mode modes ih =>
    simpa [parameterEntries] using hcons (ih (base + 1))

/-- Logical entries for an ordered subset of older slots captured by a lifted
lambda. Selected entries receive consecutive absolute capture slots; entries
outside the subset remain as released proof-side placeholders so source
de-Bruijn indices are preserved. -/
def selectedEntriesFrom (selected : Nat → Bool) (remaining : Nat → Nat) :
    List Nat → Nat → List VEntry
  | [], _ => []
  | index :: rest, next =>
      if selected index then
        .slot next (remaining index) .many true ::
          selectedEntriesFrom selected remaining rest (next + 1)
      else
        .slot 0 0 .many false ::
          selectedEntriesFrom selected remaining rest next

/-- Dependent traversal for the selected-entry builder.  Selection dispatch,
absolute-slot advancement, and released/held entry construction recurse once;
clients provide only empty, unselected, and selected result constructors. -/
theorem selectedEntriesFrom_traverse
    (selected : Nat → Bool) (remaining : Nat → Nat)
    {Result : List Nat → Nat → List VEntry → Prop}
    (hnil : ∀ next, Result [] next [])
    (hfalse : ∀ {index : Nat} {rest : List Nat} {next : Nat}
        {tail : List VEntry},
      selected index = false →
      Result rest next tail →
      Result (index :: rest) next
        (.slot 0 0 .many false :: tail))
    (htrue : ∀ {index : Nat} {rest : List Nat} {next : Nat}
        {tail : List VEntry},
      selected index = true →
      Result rest (next + 1) tail →
      Result (index :: rest) next
        (.slot next (remaining index) .many true :: tail)) :
    ∀ (indices : List Nat) (next : Nat),
      Result indices next
        (selectedEntriesFrom selected remaining indices next) := by
  intro indices
  induction indices with
  | nil => exact hnil
  | cons index rest ih =>
    intro next
    cases hselected : selected index with
    | false =>
      simpa [selectedEntriesFrom, hselected] using
        hfalse hselected (ih next)
    | true =>
      simpa [selectedEntriesFrom, hselected] using
        htrue hselected (ih (next + 1))

@[simp] theorem selectedEntriesFrom_length (selected : Nat → Bool)
    (remaining : Nat → Nat) (indices : List Nat) (next : Nat) :
    (selectedEntriesFrom selected remaining indices next).length =
      indices.length := by
  exact selectedEntriesFrom_traverse selected remaining
    (Result := fun sourceIndices _ entries =>
      entries.length = sourceIndices.length)
    (hnil := fun _ => rfl)
    (hfalse := by
      intro index rest current tail hselected htail
      simpa using congrArg Nat.succ htail)
    (htrue := by
      intro index rest current tail hselected htail
      simpa using congrArg Nat.succ htail)
    indices next

@[simp] theorem parameterEntries_length (base : Nat) (modes : List Uses)
    (remaining : Nat → Nat) :
    (parameterEntries base modes remaining).length = modes.length := by
  exact parameterEntries_traverse remaining
    (Result := fun _ sourceModes entries =>
      entries.length = sourceModes.length)
    (hnil := fun _ => rfl)
    (hcons := by
      intro current mode rest tail htail
      simpa using congrArg Nat.succ htail)
    base modes

/-- One dead parameter to release at function entry. Recording both its
source-entry index and absolute runtime slot lets the emitted operation and
the proof-side ownership environment advance together. -/
structure SlotDrop where
  entry : Nat
  abs : Nat
  uses : Uses

/-- Shift a release descriptor past a leading block of unrelated `VEnv`
entries. Absolute runtime positions are unchanged. -/
def SlotDrop.offsetEntry (offset : Nat) (drop : SlotDrop) : SlotDrop :=
  { drop with entry := offset + drop.entry }

/-- The canonical inner-to-outer release plan for parameters with no body
occurrences. -/
def parameterDrops (base : Nat) :
    List Uses → (Nat → Nat) → List SlotDrop
  | [], _ => []
  | uses :: tail, remaining =>
    parameterDrops (base + 1) tail remaining ++
      if remaining tail.length == 0 then
        [⟨tail.length, base, uses⟩]
      else []

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
def releaseSlots (Γ : VEnv) : List SlotDrop → LowerM (VEnv × Emit)
  | [] => pure (Γ, id)
  | drop :: rest => do
    let em ← match drop.uses with
      | .many => pure (emitOp (.drop (.var (Γ.rel drop.abs))))
      | .affine => pure (emitOp (.dropU (.var (Γ.rel drop.abs))))
      | .linear => throw "unused linear binding"
      | .erased => throw "internal: erased binder mode survived erasure"
    let Γ := Γ.setEntry drop.entry
      (.slot drop.abs 0 drop.uses false)
    let (Γ', em') ← releaseSlots Γ.bump rest
    pure (Γ', em ∘ em')

/-- One borrowed constructor field that a recursor alternative retains before
dropping its major. `entry` is the rule-source variable slot, `fieldAbs` is
the borrowed field's original absolute runtime position, and `remaining` is
its body occurrence count. -/
structure RecursorFieldRetain where
  entry : Nat
  fieldAbs : Nat
  remaining : Nat

/-- Canonical constructor-order retain list. Rule source variables list fields
in the opposite order, so entry indices count down while physical field
positions count up. -/
def recursorFieldRetains (fieldAbs : Nat) (rhs : IxIR0.Expr) :
    Nat → List RecursorFieldRetain
  | 0 => []
  | fieldCount + 1 =>
    let uses := countUses fieldCount rhs
    (if uses == 0 then [] else [⟨fieldCount, fieldAbs, uses⟩]) ++
      recursorFieldRetains (fieldAbs + 1) rhs fieldCount

/-- Dependent traversal for the canonical recursor-field retain builder.
Descending source-entry indices, ascending absolute field slots, and the
zero-use retain omission recurse once; clients provide only empty, skipped,
and retained-field result constructors. -/
theorem recursorFieldRetains_traverse
    (rhs : IxIR0.Expr)
    {Result : Nat → Nat → List RecursorFieldRetain → Prop}
    (hnil : ∀ fieldAbs, Result fieldAbs 0 [])
    (hskip : ∀ {fieldAbs fieldCount : Nat}
        {tail : List RecursorFieldRetain},
      countUses fieldCount rhs = 0 →
      Result (fieldAbs + 1) fieldCount tail →
      Result fieldAbs (fieldCount + 1) tail)
    (hretain : ∀ {fieldAbs fieldCount : Nat}
        {tail : List RecursorFieldRetain},
      countUses fieldCount rhs ≠ 0 →
      Result (fieldAbs + 1) fieldCount tail →
      Result fieldAbs (fieldCount + 1)
        (⟨fieldCount, fieldAbs, countUses fieldCount rhs⟩ :: tail)) :
    ∀ (fieldAbs fieldCount : Nat),
      Result fieldAbs fieldCount
        (recursorFieldRetains fieldAbs rhs fieldCount) := by
  intro fieldAbs fieldCount
  induction fieldCount generalizing fieldAbs with
  | zero => exact hnil fieldAbs
  | succ fieldCount ih =>
    by_cases hzero : countUses fieldCount rhs = 0
    · simpa [recursorFieldRetains, hzero] using
        hskip hzero (ih (fieldAbs + 1))
    · simpa [recursorFieldRetains, hzero] using
        hretain hzero (ih (fieldAbs + 1))

/-- Execute a canonical field-retain list, updating the field-entry block and
building the exact `dup` emitter used by a recursor alternative. -/
def applyRecursorFieldRetains (Γ : VEnv) :
    List RecursorFieldRetain → VEnv × Emit
  | [] => (Γ, id)
  | retain :: rest =>
    let em := emitOp (.dup (.var (Γ.rel retain.fieldAbs)))
    let Γ :=
      (Γ.setEntry retain.entry
        (.slot Γ.depth retain.remaining .many true)).bump
    let (Γ', em') := applyRecursorFieldRetains Γ rest
    (Γ', em ∘ em')

/-- Release owned shared values whose result is discarded
(◻ absorption; arguments there are demanded shared). -/
def releaseAll (Γ : VEnv) : List AVal → VEnv × Emit
  | [] => (Γ, id)
  | .constA _ :: rest => releaseAll Γ rest
  | .slotA abs :: rest =>
    let em := emitOp (.drop (.var (Γ.rel abs)))
    let (Γ', em') := releaseAll Γ.bump rest
    (Γ', em ∘ em')

/-- Check a statically known heap-result world against its consuming
demand. Scalars satisfy either world dynamically, but without a scalar
result type the lowering must conservatively respect the declaration. -/
def requireResultWorld (actual demand : Owned) : LowerM Unit := do
  if actual == demand then pure ()
  else if actual == .unique then
    throw freezeNeededMsg
  else
    throw "call result is shared at unique demand"

private def fuelMsg : String := "lowering fuel exhausted"

mutual

/-- Lower `e` in a consuming position at demanded world `w`: the
returned value carries one ownership, which the caller must consume
exactly once. Static producers and declared call results are checked
against that demand. -/
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
            throw freezeNeededMsg
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
      | some (.defn result body) =>
        let n := lamArity body
        if n == 0 then do
          -- computed global: evaluate now (IxIR₀ evaluates at `ref`)
          requireResultWorld result w
          pure (Γ.bump, emitOp (.call a #[]), .slotA Γ.depth)
        else if w == .unique then
          throw "function values live in the shared world (one-shot closures deferred)"
        else if result == .unique then
          throw "partial applications of unique-result definitions are deferred"
        else if !papSafe body then
          throw nonManyPapMsg
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
          throw uniqueDestructuringMsg
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
world of the spine's result. Allocations use it and known calls check
their declared result against it. -/
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
      applyRest src fuel Γ w id (.constA .erased) args
    | .var i =>
      match Γ.entries[i]? with
      | some (.recSelf arity) =>
        if args.length < arity then
          throw underAppliedRecSelfMsg
        else do
          requireResultWorld .shared w
          knownCall src fuel Γ (.callSelf ·) arity
            (List.replicate arity .shared) w args
      | _ => do
        let (Γ, em1, f) ← lowerE src fuel Γ .shared h
        applyRest src fuel Γ w em1 f args
    | .ref a =>
      match src a with
      | none => throw "unknown source reference"
      | some (.defn result body) =>
        let n := lamArity body
        if args.length < n then
          if w == .unique then
            throw "function values live in the shared world (one-shot closures deferred)"
          else if result == .unique then
            throw "partial applications of unique-result definitions are deferred"
          else if !papSafe body then
            throw nonManyPapMsg
          else
            -- partial application: all parameters and pap storage are shared
            knownCall src fuel Γ (.papp a ·) args.length
              (List.replicate args.length .shared) w args
        else do
          requireResultWorld result (if args.length == n then w else .shared)
          knownCall src fuel Γ (.call a ·) n
            ((lamUses body).map worldOfUses) w args
      | some (.ctor tag ar) =>
        if args.length < ar then
          if w == .unique then
            throw "partial constructor applications are shared (deferred)"
          else do
            let w' ← wrapperFor a tag ar
            knownCall src fuel Γ (.papp w' ·) args.length
              (List.replicate args.length .shared) w args
        else
          -- whole-value modes: fields are demanded the node's world
          knownCall src fuel Γ (.alloc w (ctorIdOf a tag) ·) ar
            (List.replicate ar w) w args
      | some (.recursor numArgs _ _) =>
        -- recursors are the all-`many` fragment this slice
        let arity := numArgs + 1
        if args.length < arity then
          if w == .unique then
            throw "function values live in the shared world (one-shot closures deferred)"
          else
            knownCall src fuel Γ (.papp a ·) args.length
              (List.replicate args.length .shared) w args
        else do
          requireResultWorld .shared w
          knownCall src fuel Γ (.call a ·) arity
            (List.replicate arity .shared) w args
      | some (.extern ar) =>
        if args.length < ar then
          if w == .unique then
            throw "function values live in the shared world (one-shot closures deferred)"
          else
            knownCall src fuel Γ (.papp a ·) args.length
              (List.replicate args.length .shared) w args
        else
          knownCall src fuel Γ (.extern a ·) ar
            (List.replicate ar .shared) w args
    | _ => do
      let (Γ, em1, f) ← lowerE src fuel Γ .shared h
      applyRest src fuel Γ w em1 f args
  termination_by fuel

/-- Lower the first `n` spine arguments at the given per-argument
worlds, emit `build` over them, and feed any remaining arguments
through `apply`. -/
def knownCall (src : IxIR0.Env) (fuel : Nat) (Γ : VEnv)
    (build : Array Atom → Op) (n : Nat) (argWs : List Owned)
    (resultW : Owned) (args : List IxIR0.Expr) :
    LowerM (VEnv × Emit × AVal) :=
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
    else applyRest src fuel Γ resultW em (.slotA res) (args.drop n)
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
def applyRest (src : IxIR0.Env) (fuel : Nat) (Γ : VEnv) (resultW : Owned)
    (pre : Emit) (f : AVal) (args : List IxIR0.Expr) :
    LowerM (VEnv × Emit × AVal) :=
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
      requireResultWorld .shared resultW
      let (Γ, em, avs) ← lowerArgs src fuel Γ
        (args.map (fun a => (a, Owned.shared)))
      let fAtom := f.toAtom Γ
      let atoms := (avs.map (·.toAtom Γ)).toArray
      let res := Γ.depth
      pure (Γ.bump, pre ∘ em ∘ emitOp (.apply fAtom atoms), .slotA res)
  termination_by fuel

/-- Consume one shared outer value into a lifted lambda's capture prefix.
The source occurrence count inside the lambda is discharged all at once:
retain when later source uses remain, otherwise move the existing owner. -/
def lowerCapture (e : IxIR0.Expr) (Γ : VEnv) (i : Nat) :
    LowerM (VEnv × Emit × AVal) := do
  match Γ.entries[i]? with
  | some (.slot abs r uses held) =>
    if !held then throw "internal: capture of a released variable"
    else if worldOfUses uses == .unique then
      throw uniqueCaptureMsg
    else
      let inLam := countUses i e
      if r > inLam then
        let Γ := Γ.setEntry i (.slot abs (r - inLam) uses true)
        let dupAbs := Γ.depth
        pure (Γ.bump, emitOp (.dup (.var (Γ.rel abs))), .slotA dupAbs)
      else if r == inLam then
        let Γ := Γ.setEntry i (.slot abs 0 uses false)
        pure (Γ, id, .slotA abs)
      else throw "internal: capture overcount"
  | some (.recSelf _) =>
    throw "recSelf captured by a lambda (v1 unsupported)"
  | none => throw "internal: capture out of range"

/-- Structurally recursive capture traversal. Factoring this out of
`lowerLam` exposes the exact induction boundary while preserving the old
left-to-right `foldlM` order and output vector. -/
def lowerCaptures (e : IxIR0.Expr) :
    VEnv → List Nat → LowerM (VEnv × Emit × List AVal)
  | Γ, [] => pure (Γ, id, [])
  | Γ, i :: rest => do
    let (Γ, emitHead, value) ← lowerCapture e Γ i
    let (Γ, emitTail, values) ← lowerCaptures e Γ rest
    pure (Γ, emitHead ∘ emitTail, value :: values)

/-- Lift an all-`many` `lam` run to a fresh top-level function over
captures ++ parameters (captures must be shared — paps are shared
nodes); the site value is a `papp` of the captures. Non-`many` local
lambdas would require a one-shot pap representation and are rejected. -/
def lowerLam (src : IxIR0.Env) (fuel : Nat) (Γ : VEnv)
    (e : IxIR0.Expr) : LowerM (VEnv × Emit × AVal) :=
  match fuel with
  | 0 => throw fuelMsg
  | fuel + 1 => do
    let nParams := lamArity e
    let us := lamUses e
    unless papSafe e do
      throw nonManyPapMsg
    let body := stripLams e
    let caps := (List.range Γ.entries.length).filter
      (fun i => countUses i e > 0)
    -- consume one ownership per capture at the site
    let (Γ, emC, capVals) ← lowerCaptures e Γ caps
    let fnAddr ← freshAddr
    let k := caps.length
    let fnArity := k + nParams
    -- lifted body venv: runtime env = params.reverse ++ caps.reverse,
    -- so capture j sits at abs j, parameter i (source var i, innermost
    -- first) at abs (k + nParams - 1 - i); parameters keep their
    -- binder modes (a linear parameter is a unique value in the body),
    -- and `us` is outermost-first, so var i's mode sits at nParams-1-i
    let paramEnts := parameterEntries k us fun i => countUses i body
    let outerEnts := selectedEntriesFrom
      (fun m => countUses m e > 0)
      (fun m => countUses (nParams + m) body)
      (List.range Γ.entries.length) 0
    let paramDrops := parameterDrops k us fun i => countUses i body
    let code ← lowerFnBody src fuel
      ⟨paramEnts ++ outerEnts, fnArity⟩ paramDrops .shared body
    pushExtra (fnAddr, .fn ⟨fnArity, .shared, true, code⟩)
    let capAtoms := (capVals.map (·.toAtom Γ)).toArray
    let res := Γ.depth
    pure (Γ.bump, emC ∘ emitOp (.papp fnAddr capAtoms), .slotA res)
  termination_by fuel

/-- Lower a function body at result demand `w`: mode-directed entry
releases for dead parameters, then the body, closed with `ret`. -/
def lowerFnBody (src : IxIR0.Env) (fuel : Nat) (Γ : VEnv)
    (drops : List SlotDrop) (w : Owned) (body : IxIR0.Expr) :
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

/-- Lower one indexed recursor rule. Factoring this out of the array traversal
keeps the generated-alternative proof aligned with the executable compiler. -/
def lowerRecursorRule (src : IxIR0.Env) (fuel : Nat) (numArgs : Nat) :
    IxIR0.RecRule × Nat → LowerM Alt
  | (rule, tag) => do
  let arity := numArgs + 1
  let dead : VEntry := .slot 0 0 .many false
  let nf := rule.fields
  let d0 := arity + nf
  -- entry runtime env (bottom-up): pre₁ … pre_numArgs, major,
  -- field₁ … field_nf; field j (1-based) ↔ source var (nf - j)
  let fieldRetains :=
    recursorFieldRetains (numArgs + 1) rule.rhs nf
  let (Γ0, emDups) :=
    applyRecursorFieldRetains
      ⟨List.replicate nf dead, d0⟩ fieldRetains
  -- the rules never see the major: release it (after the field dups)
  let emMaj := emitOp (.drop (.var (Γ0.rel numArgs)))
  let Γ1 := Γ0.bump
  -- Pre-major parameters reuse the canonical declaration layout/release
  -- path. Their entries sit after the field block, so only proof-side entry
  -- indices are offset; absolute runtime positions stay `0 .. numArgs-1`.
  let paramModes := List.replicate numArgs .many
  let paramRemaining : Nat → Nat :=
    fun i => countUses (nf + i) rule.rhs
  let paramEnts := parameterEntries 0 paramModes paramRemaining
  let paramDrops :=
    (parameterDrops 0 paramModes paramRemaining).map
      (SlotDrop.offsetEntry nf)
  let Γparams : VEnv :=
    ⟨Γ0.entries ++ paramEnts ++ [.recSelf arity], Γ1.depth⟩
  let (Γrhs, emPar) ← releaseSlots Γparams paramDrops
  let (Γ3, emR, av) ← lowerE src fuel Γrhs .shared rule.rhs
  let code := emDups (emMaj (emPar (emR (.ret (av.toAtom Γ3)))))
  pure (Alt.mk tag nf code)

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
  let altsL ← rules.toList.zipIdx.mapM
    (lowerRecursorRule src fuel numArgs)
  pure ⟨arity, .shared, true, .case (.var 0) natLit altsL.toArray⟩

/-- Lower one declaration. Constructors get no declaration of their
own (saturated sites `alloc`; first-class sites go through wrappers,
which land in the accumulated extras). Definition parameters keep
their binder modes, while the declared result world directs body
lowering and is preserved in `FnDef`. -/
def lowerDecl (src : IxIR0.Env) (fuel : Nat) :
    Address × IxIR0.Decl → LowerM (Option (Address × Decl))
  | (a, .defn result body) => do
    let n := lamArity body
    let us := lamUses body
    let b := stripLams body
    let entries := parameterEntries 0 us fun i => countUses i b
    let drops := parameterDrops 0 us fun i => countUses i b
    let code ← lowerFnBody src fuel ⟨entries, n⟩ drops result b
    pure (some (a, .fn
      ⟨n, result, result == .shared && papSafe body, code⟩))
  | (_, .ctor _ _) => pure none
  | (a, .recursor numArgs natLit rules) => do
    pure (some (a, .fn (← lowerRecursor src fuel numArgs natLit rules)))
  | (a, .extern ar) => pure (some (a, .extern ar))

/-- The stateful whole-program action. Factoring it from `lowerAll` exposes
the final generated-declaration and wrapper-cache state to proofs while the
transient lowering API returns only declarations and main code. Production
artifacts cross `LowerAddressed.lowerAllAddressed`, which consumes this final
state and replaces generated names with declaration content addresses. -/
def lowerAllAction (decls : List (Address × IxIR0.Decl))
    (main : IxIR0.Expr) (mainW : Owned) (fuel : Nat) :
    LowerM (List (Address × Decl) × Code) := do
  let src := IxIR0.Env.ofList decls
  let base ← decls.filterMapM (lowerDecl src fuel)
  let mainC ← lowerFnBody src fuel ⟨[], 0⟩ [] mainW main
  let st ← get
  pure (base ++ st.extra, mainC)

/-- Lower a whole program plus a closed main expression, at the given result
world for the main expression. This theorem-facing result still contains
transient generated names; use `lowerAllAddressed` for an emitted artifact. -/
def lowerAll (decls : List (Address × IxIR0.Decl)) (main : IxIR0.Expr)
    (mainW : Owned := .shared) (fuel : Nat := 10000) :
    Except String (List (Address × Decl) × Code) :=
  match (lowerAllAction decls main mainW fuel).run {} with
  | .ok v _ => .ok v
  | .error e _ => .error e

/-- The indexed form of the stateful whole-program action.  Keeping the final
state observable lets the compiled artifact boundary distinguish generated
declarations from source-backed declarations without recognizing the
temporary address spelling. -/
def lowerAllIndexedAction (decls : List (Address × IxIR0.Decl))
    (main : IxIR0.Expr) (mainW : Owned) (fuel : Nat) :
    LowerM (List (Address × Decl) × Code) :=
  let sourceIndex := IxIR0.Env.Index.ofList decls
  let src := sourceIndex.toEnv
  do
    let base ← decls.filterMapM (lowerDecl src fuel)
    let mainC ← lowerFnBody src fuel ⟨[], 0⟩ [] mainW main
    let st ← get
    pure (base ++ st.extra, mainC)

/-- The indexed action is propositionally the transparent action: its
captured index implements exactly `Env.ofList` lookup semantics. -/
theorem lowerAllIndexedAction_eq_lowerAllAction
    (decls : List (Address × IxIR0.Decl)) (main : IxIR0.Expr)
    (mainW : Owned) (fuel : Nat) :
    lowerAllIndexedAction decls main mainW fuel =
      lowerAllAction decls main mainW fuel := by
  simp only [lowerAllIndexedAction, lowerAllAction,
    IxIR0.Env.Index.toEnv_ofList]

/-- Corpus-scale transient entry point. It constructs the source address index
once, then runs the same declaration/main lowering action against the captured
lookup closure. `lowerAllIndexed_eq_lowerAll` keeps the transparent list
environment as the proof specification; emitted artifacts use
`lowerAllIndexedAddressed`. -/
def lowerAllIndexed (decls : List (Address × IxIR0.Decl))
    (main : IxIR0.Expr) (mainW : Owned := .shared) (fuel : Nat := 10000) :
    Except String (List (Address × Decl) × Code) :=
  match (lowerAllIndexedAction decls main mainW fuel).run {} with
  | .ok value _ => .ok value
  | .error error _ => .error error

theorem lowerAllIndexed_eq_lowerAll
    (decls : List (Address × IxIR0.Decl)) (main : IxIR0.Expr)
    (mainW : Owned) (fuel : Nat) :
    lowerAllIndexed decls main mainW fuel = lowerAll decls main mainW fuel := by
  simp only [lowerAllIndexed, lowerAllIndexedAction, lowerAll, lowerAllAction,
    IxIR0.Env.Index.toEnv_ofList]

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

/-- Pinned cross-IR stuck-message pairs (source, target) — every stuck
agreement the corpus exercises, by exact text. An unlisted pair counts
as divergence: extend the table deliberately when a new fixture
legitimately sticks on both sides. -/
def stuckPairs : List (String × String) :=
  [("application of a non-function value", "apply of a non-node value"),
   ("projection 5 out of bounds", "fetch field 5 out of range")]

/-- Deliberate error-agreement mapping between the two semantics
(`lowersErr`'s exactness, extended across IRs):

- `fuel` pairs only with `fuel` (a stuck side against a diverging side
  is a divergence, not agreement);
- unknown references pair by exact address;
- the IxIR₀ `oracleMissing` boundary pairs with the two ways IxIR₁
  refuses the *same* extern call: a `none` oracle answer on scalar
  arguments (surfaced as `unknownRef`, matched by address) or the
  scalar-only ABI's `mem` rejection of heap arguments (which the
  literals-only source oracle observes as a domain miss) — pinned to
  that exact ABI message;
- stuck messages pair only through `stuckPairs`;
- everything else — including IxIR₁ `mem` discipline faults, which
  have no source counterpart — disagrees. -/
def errAgree : IxIR0.Err → Err → Bool
  | .fuel, .fuel => true
  | .unknownRef a, .unknownRef b => a == b
  | .oracleMissing a, .unknownRef b => a == b
  | .oracleMissing _, .mem msg =>
    msg == "extern heap arguments require an ownership policy"
  | .stuck msg, .stuck msg' => stuckPairs.contains (msg, msg')
  | _, _ => false

/-- The differential check: lower the corpus + `e` (main at world
`mainW`), run both semantics; on success the readback trees must
agree AND releasing the result must leave the store empty
(leak-freedom of the inserted memory ops); on failure both sides must
fail with errors related by the `errAgree` mapping. No leak check runs
on error runs: the evaluator's `Except Err` aborts without returning a
store, so the state at an error is unobservable at this API (a
transactional evaluator would make it checkable; today only successful
runs carry a store to audit). -/
def diffExpr (e : IxIR0.Expr) (mainW : Owned := .shared)
    (runFuel : Nat := 100000) : Bool :=
  match lowerAllIndexed IxIR0.Examples.declList e mainW with
  | .error _ => false
  | .ok (ds, mainC) =>
    let targetIndex := Env.Index.ofList ds
    let tctx : Ctx := { decls := targetIndex.toEnv, oracle := tgtOracle }
    match IxIR0.Examples.ctx.run e runFuel, runMain tctx mainC runFuel with
    | .ok v, .ok (store, r) =>
      (match treeOfVal 1000 v, treeOfR store 1000 r with
       | some a, some b => Tree.agree a b
       | _, _ => false)
      && (match releaseResult tctx runFuel store r with
          | .ok s => s.live == 0
          | .error _ => false)
    | .error source, .error target => errAgree source target
    | _, _ => false

/-- Target-only run for counter guards. -/
def checkLowered (e : IxIR0.Expr) (mainW : Owned)
    (p : Store → RVal → Bool) : Bool :=
  match lowerAllIndexed IxIR0.Examples.declList e mainW with
  | .error _ => false
  | .ok (ds, mainC) =>
    let targetIndex := Env.Index.ofList ds
    match runMain { decls := targetIndex.toEnv, oracle := tgtOracle } mainC with
    | .ok (store, r) => p store r
    | .error _ => false

/-- The lowering statically rejects `e` at the given main world with
the expected diagnostic. Keeping the message in the assertion stops
one mode error from accidentally satisfying a guard for another. -/
def lowersErr (e : IxIR0.Expr) (mainW : Owned) (expected : String) : Bool :=
  match lowerAllIndexed IxIR0.Examples.declList e mainW with
  | .error msg => msg == expected
  | .ok _ => false

section Guards

open Ix.Compiler.IxIR0.Examples

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
  "unused linear binding"

-- a unique variable used twice
#guard lowersErr (.letE .linear (natE 1)
  (.app (.app (.ref pairMk) (.var 0)) (.var 0))) .unique
  "unique variable used more than once"

-- dereliction: a shared value at unique demand
#guard lowersErr (.letE .many (natE 1) (.app (.ref natSucc) (.var 0)))
  .unique "dereliction: shared value at unique demand"

-- freeze needed: a unique value at shared demand
#guard lowersErr (.letE .linear (natE 1) (.app (.ref natSucc) (.var 0)))
  .shared freezeNeededMsg

-- a unique value into a recursor (the all-`many` fragment)
#guard lowersErr (.letE .linear (natE 1)
  (.app (.app (.ref natAddDef) (.var 0)) (natE 1))) .shared
  freezeNeededMsg

-- function values live in the shared world
#guard lowersErr (.letE .linear (.lam .many (.var 0)) (.var 0)) .shared
  "function values live in the shared world (one-shot closures deferred)"

-- projection from a unique value
#guard lowersErr
  (.letE .linear (.app (.app (.ref pairMk) (natE 1)) (natE 2))
    (.proj 0 (.var 0))) .shared
  uniqueDestructuringMsg

-- shared paps cannot own a captured unique value
private def uniqueCaptureRestriction : IxIR0.Expr :=
  .letE .linear (natE 1) (.lam .many (.var 1))

#guard lowersErr uniqueCaptureRestriction .shared uniqueCaptureMsg

-- a direct recursor call demands every argument in the shared world
private def modeMonomorphicRecursorRestriction : IxIR0.Expr :=
  .letE .linear (natE 1)
    (.app
      (.app
        (.app (.ref natRec) (natE 0))
        (.lam .many (.lam .many (.app (.ref natSucc) (.var 0)))))
      (.var 0))

#guard lowersErr modeMonomorphicRecursorRestriction .shared freezeNeededMsg

-- `recSelf` exists only in recursor-rule environments.  A one-parameter
-- recursor has self arity two, so this one-argument rule call witnesses the
-- exact saturation restriction while the declaration itself is lowered.
private def underAppliedRecSelfAddr : Address := synthAddr 92

private def underAppliedRecSelfRule : IxIR0.RecRule :=
  { fields := 0, rhs := .app (.var 1) (.var 0) }

private def underAppliedRecSelfRejected : Bool :=
  match lowerAll
      (IxIR0.Examples.declList ++
        [(underAppliedRecSelfAddr,
          .recursor 1 false #[underAppliedRecSelfRule])])
      (natE 0) with
  | .error message => message == underAppliedRecSelfMsg
  | .ok _ => false

#guard underAppliedRecSelfRejected

/-- Executable coverage for the complete six-entry policy inventory.  The
individual guards above retain readable failure locations; this aggregate
guard prevents a newly listed restriction from landing without a witness. -/
private def restrictionWitness : RestrictionKind → Bool
  | kind@(.freeze) =>
    lowersErr (.letE .linear (natE 1) (.app (.ref natSucc) (.var 0)))
      .shared kind.diagnostic
  | kind@(.uniqueDestructuring) =>
    lowersErr
      (.letE .linear (.app (.app (.ref pairMk) (natE 1)) (natE 2))
        (.proj 0 (.var 0)))
      .shared kind.diagnostic
  | kind@(.sharedFunctionValues) =>
    lowersErr (.app (.lam .affine (.lit (.nat 7))) (natE 3))
      .shared kind.diagnostic
  | kind@(.uniqueCapture) =>
    lowersErr uniqueCaptureRestriction .shared kind.diagnostic
  | kind@(.modeMonomorphicRecursors) =>
    lowersErr modeMonomorphicRecursorRestriction .shared kind.diagnostic
  | .saturatedRecSelf => underAppliedRecSelfRejected

#guard RestrictionKind.all.all restrictionWitness

/-! Non-`many` function values are rejected before they can reach the
all-shared `apply` path: direct lambdas, bare known references, and
under-applied known definitions all pin the same exact diagnostic.
All-`many` partial applications remain supported. -/

#guard lowersErr
  (.app (.lam .affine (.lit (.nat 7))) (natE 3)) .shared
  nonManyPapMsg

#guard lowersErr (.ref dropFstDef) .shared nonManyPapMsg

#guard lowersErr (.app (.ref dropFstDef) (natE 1)) .shared nonManyPapMsg

#guard diffExpr (.app (.ref natAddDef) (natE 2))

/-! Declared result worlds close the old call seam: a shared result at
unique demand is rejected statically, before a mismatched `dropU` can
reach the evaluator. -/

#guard lowersErr
  (.letE .affine
    (.app (.app (.ref natAddDef) (natE 1)) (natE 1))
    (natE 0)) .shared
  "call result is shared at unique demand"

private def uniqueResultDef : Address := synthAddr 91

private def uniqueResultDecls : List (Address × IxIR0.Decl) :=
  IxIR0.Examples.declList ++
    [(uniqueResultDef, .defn .unique (natE 1))]

/-! A declared unique computed global is lowered in the unique world,
its signature survives in `FnDef`, and an unused affine caller can
deep-free the returned tree with no RC traffic. -/

#guard
  match lowerAll uniqueResultDecls
      (.letE .affine (.ref uniqueResultDef) (natE 0)) with
  | .ok (ds, c) =>
    match (Env.ofList ds) uniqueResultDef,
        runMain { decls := Env.ofList ds, oracle := tgtOracle } c with
    | some (.fn d), .ok (s, _) =>
      d.result == .unique && s.allocs == 3 && s.frees == 2 &&
        s.rcops == 0 && s.live == 1
    | _, _ => false
  | .error _ => false

#guard
  match lowerAll uniqueResultDecls (.ref uniqueResultDef) .shared with
  | .error msg =>
    msg == freezeNeededMsg
  | .ok _ => false

/-! Mixed-mode telescopes: the binder-mode signature is
outermost-first while de Bruijn vars count innermost-first, so
entries, entry drops, and `knownCall` argument worlds must agree
per-parameter. Both orders exercise declaration lowering and saturated
known calls; first-class mixed-mode lambdas are rejected above. -/

#guard diffExpr (.app (.app (.ref dropFstDef) (natE 1)) (natE 2))
#guard diffExpr (.app (.app (.ref dropSndDef) (natE 2)) (natE 1))

-- the dead affine argument (2 unique nodes) deep-frees at entry with
-- zero RC traffic; the shared result (3 nodes) survives
#guard checkLowered (.app (.app (.ref dropFstDef) (natE 1)) (natE 2))
  .shared fun s _ =>
    s.allocs == 5 && s.frees == 2 && s.rcops == 0 && s.live == 3
#guard checkLowered (.app (.app (.ref dropSndDef) (natE 2)) (natE 1))
  .shared fun s _ =>
    s.allocs == 5 && s.frees == 2 && s.rcops == 0 && s.live == 3

-- A mixed-mode lambda cannot escape into the all-shared papp/apply path.
#guard lowersErr (.lam .affine (.lam .many (.var 0))) .shared
  nonManyPapMsg

-- a dead linear binder in a mixed telescope is rejected *as such*
-- (not as a freeze error on the wrong binder)
#guard
  match lowerAll (IxIR0.Examples.declList ++
      [(synthAddr 90,
        .defn .shared (.lam .linear (.lam .many (.var 0))))])
      (natE 0) with
  | .error "unused linear binding" => true
  | _ => false

end Guards

end Ix.Compiler.IxIR1.Lower
