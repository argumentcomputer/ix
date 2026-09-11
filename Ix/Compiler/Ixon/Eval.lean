import Ix.Compiler.Fuel
import Ix.Compiler.Ixon.Const

/-!
# The Ixon reference evaluator

The **source-side** semantics for the erasure simulation: the unerased
twin of `Ix/Compiler/IxIR0/Eval.lean`, in the same house style
(functional big-step, uniform fuel decrement across the mutual
functions, `∃ fuel` termination statements). This is the runtime
anchor for Ixon terms — NOT a defeq/whnf engine (that is Ix.Kernel's and
lean4ix's job).

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
  and `partial` do not. Authorized opaque/axiom addresses use the external
  oracle. For an opaque mutual member, the oracle identity is the same
  synthetic `(block, index)` address emitted into IxIR₀. Unconfigured
  quotients, opaque definitions, axioms, and inductive types are **neutral**:
  applying them accumulates a `papV` that never fires — a value, not a stuck
  state.
- **Literals**: `.nat`/`.str` carry refs-table indices; the address
  resolves through a store-blob oracle (`EvalCtx.blobs`). This pins
  the v2 "blob table" reading: the blob table IS the refs table, and
  literal payloads are content-addressed store blobs. Byte-level blob
  canonicalization (trimmed-LE nats, UTF-8) belongs to the store
  layer; the oracle hands back interpreted values.
- **Nat identity by address**: literal ι-peeling (`0 ↦ ctor 0`,
  `n+1 ↦ ctor 1 [lit n]`) activates when `EvalCtx.natBlock` is set —
  in a nameless world, "this recursor is `Nat.rec`" is a well-known-
  address configuration, not a name check. Recursor firing checks that its
  block is that configured address and rejects literal majors for recursors
  with parameters.
- **Modes are inert**: `lam`/`all` modes ride in closure values and
  are never consulted — the source half of "modes don't change
  semantics".

Configured quotient primitives reduce `Quot.lift/ind` on `Quot.mk` while
unconfigured quotient addresses retain the neutral behavior. In opt-in open
evaluation mode, neutral projections and saturated recursor applications
preserve their elimination spine rather than becoming stuck; strict mode is
the default and is required by certified erasure. Mutual-member neutral
identities include their block. Projection reduction also resolves and
cross-checks its encoded inductive-type reference. Address-configured String
literal majors expand through the upstream `String.ofList` / `List.cons.{0}` /
`Char.ofNat` term, with every representation detail evaluated through ordinary
resolved constants; certified strict mode excludes that source-only extension
until IxIR₀ represents it. K-like reduction remains deferred because it is a
defeq rule rather than a runtime one. Recursor firing checks constructor-block
agreement (and zero parameters for Nat-literal majors):
besides rejecting malformed untyped runs, that runtime fact is the layout
equality used when erasure drops constructor parameters and recursor indices.
-/

namespace Ix.Compiler.Ixon.Eval

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

/-- The tables an expression is read against, plus the universe
instantiation of the constant it came from. Closures capture their
frame; entering a reference builds the callee's. `selfAddr` is the
address of the mutual block `selfMuts` belongs to (set when the frame
is built through a block projection) — it gives `recur`-built
recursor heads their block identity, which literal ι-peeling keys
on. -/
structure Frame where
  sharing : Array Expr := #[]
  refs : Array Address := #[]
  univs : Array Univ := #[]
  selfMuts : Array MutConst := #[]
  uinst : List Nat := []
  selfAddr : Option Address := none

def Frame.ofConst (c : Constant) (uinst : List Nat := [])
    (selfAddr : Option Address := none) : Frame :=
  { sharing := c.sharing, refs := c.refs, univs := c.univs
    selfMuts := selfMutsOf c.info, uinst, selfAddr }

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

/-- Well-known constants used by the kernel's String-literal constructor
expansion.  The evaluator deliberately stores addresses rather than a baked-in
constructor layout: `String.ofList`, `Char.ofNat`, and the current `String`
representation remain ordinary resolved constants, so a toolchain address roll
or representation change is supplied by the caller's environment.

The generated application is exactly

`String.ofList (List.cons.{0} Char (Char.ofNat c) ... (List.nil.{0} Char))`.
-/
structure StringLiteralConfig where
  charType : Address
  charOfNat : Address
  stringOfList : Address
  listNil : Address
  listCons : Address
  deriving BEq, Repr

inductive Err where
  | fuel
  | stuck (msg : String)
  | unknownRef (adr : Address)
  | unknownBlob (adr : Address)
  | oracleMissing (adr : Address)
  deriving BEq, Repr

/-! ## Values -/

inductive NeutralId where
  | const (adr : Address)
  | member (block : Address) (idx : Nat)
  /-- A stuck projection elimination. The projected neutral is the first
  argument of the enclosing `papV`; later applications extend that spine. -/
  | projection (type : Address) (field : Nat)
  deriving BEq, Repr

/-- Pre-major arity of a recursor (params + motives + minors +
indices), plus one for the major premise. -/
def recArity (r : Recursor) : Nat :=
  r.params.toNat + r.motives.toNat + r.minors.toNat + r.indices.toNat + 1

/-- Source arities of Lean's four quotient primitives, before erasure. -/
def quotArity : QuotKind → Nat
  | .type => 2
  | .ctor => 3
  | .lift => 6
  | .ind => 5

inductive Head where
  | ctorH (block : Address) (indIdx cidx arity : Nat)
  /-- `block` is the recursor's mutual-block address when known —
  literal ι-peeling fires only when it equals the configured
  `natBlock` (the erased `natLit` flag is set by exactly the same
  comparison, so the two semantics peel in lockstep). -/
  | recH (block : Option Address) (recr : Recursor) (F : Frame)
  /-- Configured opaque/axiom runtime primitive. The explicit arity keeps
  partial application aligned with the erased `Decl.extern`. -/
  | extH (address : Address) (arity : Nat)
  /-- Configured quotient primitive. Saturated `.ctor` applications produce
  a distinct quotient wrapper; `.lift` and `.ind` inspect that value. -/
  | quotH (address : Address) (kind : QuotKind)
  | neuH (id : NeutralId)

def Head.arity? : Head → Option Nat
  | .ctorH _ _ _ a => some a
  | .recH _ r _ => some (recArity r)
  | .extH _ arity => some arity
  | .quotH _ kind => some (quotArity kind)
  | .neuH _ => none

inductive Value where
  | sortV (lvl : Nat)
  | piV (uses : Uses) (owned : Owned) (F : Frame) (env : List Value)
      (dom cod : Expr)
  | closV (uses : Uses) (F : Frame) (env : List Value) (dom body : Expr)
  | papV (h : Head) (args : List Value)
  /-- A saturated configured `Quot.mk`. Keeping the wrapper distinct from a
  pap makes accidental over-application stuck, while eliminators can recover
  the representative without relying on a hand-constructed argument list. -/
  | quotV (address : Address) (representative : Value)
  /-- Constructor application: `args` = param values ++ field values,
  in application order. -/
  | ctorV (block : Address) (indIdx cidx : Nat) (args : List Value)
  | litV (l : Lit)

/-- Runtime-neutral values. A recursor head becomes neutral only after it has
reached saturation and failed to expose a constructor because its major was
itself neutral; under-applied recursors remain ordinary function values. -/
def Value.isNeutral : Value → Bool
  | .papV (.neuH _) _ => true
  | .papV (.recH _ r _) args => recArity r ≤ args.length
  | _ => false

/-- Source extern semantics: pure, partial, and keyed by the same address as
the erased oracle. A separate simulation witness relates successful source
and target calls; merely installing an oracle grants no theorem. -/
abbrev Oracle := Address → List Value → Option Value

structure EvalCtx where
  resolve : Address → Option Constant
  blobs : Address → Option Blob := fun _ => none
  /-- Open-evaluation mode preserves neutral projection and recursor
  eliminations. Certified erasure uses `false`: its target-side projection
  safety theorem deliberately covers only strict runtime eliminations. -/
  preserveNeutralElims : Bool := false
  /-- Well-known address of the `Nat` mutual block; enables literal
  ι-peeling at recursors. -/
  natBlock : Option Address := none
  /-- Addresses for the kernel's String-literal constructor expansion.  When
  absent, String literals remain atomic runtime values and cannot be recursor
  majors.  Certified erasure currently requires this field to be absent. -/
  stringLiteral : Option StringLiteralConfig := none
  /-- Trusted identity map for the four quotient primitives. A resolved
  `.quot` constant computes only when this map assigns its address the same
  kind stored in the constant; unconfigured quotient constants stay neutral. -/
  quotientKind : Address → Option QuotKind := fun _ => none
  /-- Ledger-authorized arity for opaque definitions and axioms. Opaque mutual
  members use `Address.memberAddr block idx`, exactly matching their erased
  extern key. An address absent from this map retains the source evaluator's
  neutral behavior. -/
  externArity : Address → Option Nat := fun _ => none
  /-- Pure source oracle. It is called only by an authorized `extH` at exact
  saturation; semantic correspondence is an explicit simulation premise. -/
  oracle : Oracle := fun _ _ => none

/-- The source-evaluation mode admitted by certified erasure.  Open neutral
eliminations and String-literal constructor expansion both add successful
source behaviors that IxIR₀ does not yet represent, so the proof boundary
seals both switches together. -/
structure EvalCtx.Strict (ctx : EvalCtx) : Prop where
  neutralElims : ctx.preserveNeutralElims = false
  stringLiterals : ctx.stringLiteral = none

/-! ## Non-recursive helpers -/

def unfoldable (d : Definition) : Bool :=
  d.kind != .opaq && d.safety != .part

/-- Check that a universe instantiation has the declaration's expected arity.
Public so semantic-preservation proofs can follow evaluator dispatch exactly. -/
def guardLvls (lvls : UInt64) (uinst : List Nat) :
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

/-- Resolve the type-reference carried by a projection to the exact inductive
member it names. This turns the wire-level local index into a runtime layout
identity before either selecting a constructor field or constructing a neutral
projection spine. -/
def resolveProjectionTarget (ctx : EvalCtx) (F : Frame)
    (typeRefIdx : UInt64) : Except Err (Address × InductiveProj × Inductive) :=
  match F.refs[typeRefIdx.toNat]? with
  | none => .error (.stuck
      s!"projection type ref index {typeRefIdx.toNat} out of range")
  | some typeAddress =>
    match ctx.resolve typeAddress with
    | none => .error (.unknownRef typeAddress)
    | some typeConstant =>
      match typeConstant.info with
      | .iPrj projection =>
        match resolveMut ctx projection.block projection.idx.toNat with
        | .ok (_, .indc ind) => .ok (typeAddress, projection, ind)
        | .ok _ => .error
            (.stuck "projection type ref targets a non-inductive member")
        | .error err => .error err
      | _ => .error
          (.stuck "projection type ref is not an inductive projection")

/-- Construct a block-qualified neutral mutual-member head. A frame without a
block address cannot mint a globally meaningful member identity. -/
def neutralMember (block : Option Address) (idx : Nat) : Except Err Value :=
  match block with
  | some address => .ok (.papV (.neuH (.member address idx)) [])
  | none => .error (.stuck "neutral mutual member has no block identity")

/-- Reduce one projection after its value has been evaluated. Constructor
selection is guarded by the encoded type identity; neutral inputs retain the
projection as an explicit elimination head. -/
def projectValue (ctx : EvalCtx) (F : Frame) (typeRefIdx fieldIdx : UInt64)
    (value : Value) : Except Err Value :=
  match resolveProjectionTarget ctx F typeRefIdx with
  | .error err => .error err
  | .ok (typeAddress, projection, ind) =>
    match value with
    | .ctorV block indIdx _ args =>
      if block == projection.block && indIdx == projection.idx.toNat then
        match args[ind.params.toNat + fieldIdx.toNat]? with
        | some result => .ok result
        | none => .error
            (.stuck s!"projection {fieldIdx.toNat} out of range")
      else
        .error (.stuck "projection value does not match its type ref")
    | value =>
      if value.isNeutral && ctx.preserveNeutralElims then
        .ok (.papV (.neuH
          (.projection typeAddress fieldIdx.toNat)) [value])
      else if let .litV _ := value then
        .error (.stuck "projection from a literal")
      else
        .error (.stuck "projection from a non-constructor value")

/-- In strict runtime mode, every successful projection came from a
constructor whose block/member identity was cross-checked through the encoded
type reference. This is the precise boundary consumed by erasure's
constructor-only projection-safety proof. -/
theorem projectValue_ok_of_strict {ctx : EvalCtx} {F : Frame}
    {typeRefIdx fieldIdx : UInt64} {value result : Value}
    (hstrict : ctx.preserveNeutralElims = false)
    (hproject : projectValue ctx F typeRefIdx fieldIdx value = .ok result) :
    ∃ ind blockConstant block indIdx cidx args,
      resolveMut ctx block indIdx = .ok (blockConstant, .indc ind) ∧
      value = .ctorV block indIdx cidx args ∧
      args[ind.params.toNat + fieldIdx.toNat]? = some result := by
  unfold projectValue resolveProjectionTarget at hproject
  cases href : F.refs[typeRefIdx.toNat]? with
  | none =>
    rw [href] at hproject
    dsimp only at hproject
    contradiction
  | some typeAddress =>
    rw [href] at hproject
    dsimp only at hproject
    cases htype : ctx.resolve typeAddress with
    | none =>
      rw [htype] at hproject
      contradiction
    | some typeConstant =>
      rw [htype] at hproject
      dsimp only at hproject
      cases hinfo : typeConstant.info with
      | iPrj projection =>
        rw [hinfo] at hproject
        dsimp only at hproject
        cases hresolve : resolveMut ctx projection.block
            projection.idx.toNat with
        | error err =>
          rw [hresolve] at hproject
          contradiction
        | ok pair =>
          rcases pair with ⟨blockConstant, member⟩
          rw [hresolve] at hproject
          cases member with
          | defn definition => contradiction
          | recr recursor => contradiction
          | indc ind =>
            dsimp only at hproject
            cases value with
            | ctorV block indIdx cidx args =>
              dsimp only at hproject
              cases hmatches :
                  block == projection.block &&
                    indIdx == projection.idx.toNat with
              | false =>
                rw [hmatches] at hproject
                contradiction
              | true =>
                rw [hmatches] at hproject
                have hparts := Bool.and_eq_true_iff.mp hmatches
                have hblock : block = projection.block :=
                  beq_iff_eq.mp hparts.1
                have hidx : indIdx = projection.idx.toNat :=
                  beq_iff_eq.mp hparts.2
                cases harg : args[ind.params.toNat + fieldIdx.toNat]? with
                | none =>
                  rw [harg] at hproject
                  contradiction
                | some projected =>
                  rw [harg] at hproject
                  injection hproject with hresult
                  subst projected
                  subst block
                  subst indIdx
                  exact ⟨ind, blockConstant, projection.block,
                    projection.idx.toNat, cidx, args, hresolve, rfl, harg⟩
            | papV head args => simp [hstrict] at hproject
            | sortV | piV | closV | quotV | litV =>
              simp [Value.isNeutral, hstrict] at hproject
      | defn definition => rw [hinfo] at hproject; contradiction
      | recr recursor => rw [hinfo] at hproject; contradiction
      | axio ax => rw [hinfo] at hproject; contradiction
      | quot q => rw [hinfo] at hproject; contradiction
      | cPrj cp => rw [hinfo] at hproject; contradiction
      | rPrj rp => rw [hinfo] at hproject; contradiction
      | dPrj dp => rw [hinfo] at hproject; contradiction
      | muts members => rw [hinfo] at hproject; contradiction

def evalUnivArgs (F : Frame) (idxs : Array UInt64) :
    Except Err (List Nat) := do
  let mut out := []
  for i in idxs do
    match F.univs[i.toNat]? with
    | some u => out := out ++ [evalUniv F.uinst u]
    | none => throw (.stuck s!"universe index {i.toNat} out of range")
  return out

/-- View a recursor's major premise as a constructor application,
peeling Nat literals when `peel` is set — the firing recursor's block
must be the configured Nat block (mirroring the erased `natLit`
flag; peeling at an arbitrary recursor would diverge from the erased
semantics). -/
def majorCtor (peel : Bool) : Value → Except Err (Nat × List Value)
  | .ctorV _ _ cidx cargs => .ok (cidx, cargs)
  | .litV (.natL n) =>
    if peel then
      match n with
      | 0 => .ok (0, [])
      | n + 1 => .ok (1, [.litV (.natL n)])
    else .error (.stuck "literal major premise (not the Nat recursor)")
  | _ => .error (.stuck "recursor major premise is not a constructor")

/-- Check the layout identity that a typed recursor application gets for free.
A constructor major must come from the firing recursor's mutual block. A Nat
literal has no stored constructor parameters, so it can only feed a
zero-parameter recursor. The subsequent `majorCtor` check still rejects every
other value shape. -/
def guardRecMajor (block : Option Address) (params : Nat) :
    Value → Except Err Unit
  | .ctorV ctorBlock _ _ _ =>
    if some ctorBlock == block then .ok ()
    else .error (.stuck "constructor major belongs to a different recursor block")
  | .litV (.natL _) =>
    if params == 0 then .ok ()
    else .error (.stuck "literal major requires a zero-parameter recursor")
  | _ => .ok ()

/-- Recover the representative stored by a saturated configured `Quot.mk`.
Only the dedicated wrapper is accepted, so an ordinary or hand-built pap
cannot masquerade as a quotient package. -/
def quotientRep? : Value → Option Value
  | .quotV _ representative => some representative
  | _ => none

/-- Build the `List Char` tail of the kernel's String-literal expansion using
an abstract value application operation.  `chars` is supplied in reverse, as
in the upstream kernel, so each successful step prepends one character and the
result retains source order. -/
def applyStringChars
    (applyValue : Value → Value → Except Err Value)
    (charOfNat cons : Value) : List Char → Value → Except Err Value
  | [], list => .ok list
  | char :: chars, list => do
      let charValue ← applyValue charOfNat (.litV (.natL char.toNat))
      let partialCons ← applyValue cons charValue
      let list ← applyValue partialCons list
      applyStringChars applyValue charOfNat cons chars list

private theorem bindOk {α β : Type} (a : α) (f : α → Except Err β) :
    (Except.ok a >>= f) = f a := rfl

private theorem bindErr {α β : Type} (e : Err) (f : α → Except Err β) :
    ((Except.error e : Except Err α) >>= f) = Except.error e := rfl

/-- Successful character-list construction is preserved when every successful
application is preserved.  This is the higher-order seam used by evaluator
fuel monotonicity and sharing coherence. -/
theorem applyStringChars_map_ok
    {apply₁ apply₂ : Value → Value → Except Err Value}
    (happly : ∀ f a v, apply₁ f a = .ok v → apply₂ f a = .ok v)
    (charOfNat cons : Value) (chars : List Char) (list result : Value)
    (h : applyStringChars apply₁ charOfNat cons chars list = .ok result) :
    applyStringChars apply₂ charOfNat cons chars list = .ok result := by
  induction chars generalizing list with
  | nil => exact h
  | cons char chars ih =>
      simp only [applyStringChars] at h ⊢
      cases hchar : apply₁ charOfNat (.litV (.natL char.toNat)) with
      | error err => rw [hchar, bindErr] at h; contradiction
      | ok charValue =>
        rw [hchar, bindOk] at h
        rw [happly _ _ _ hchar, bindOk]
        cases hpartial : apply₁ cons charValue with
        | error err => rw [hpartial, bindErr] at h; contradiction
        | ok partialCons =>
          rw [hpartial, bindOk] at h
          rw [happly _ _ _ hpartial, bindOk]
          cases hlist : apply₁ partialCons list with
          | error err => rw [hlist, bindErr] at h; contradiction
          | ok nextList =>
            rw [hlist, bindOk] at h
            rw [happly _ _ _ hlist, bindOk]
            exact ih nextList h

/-- Prepare a recursor major exactly as the upstream kernel prepares a String
literal: construct the five configured constant heads, build the `List Char`
spine at universe zero, and evaluate `String.ofList` once.  Abstract callbacks
keep this definition outside the evaluator's recursive group and expose a
small proof seam. -/
def prepareStringMajor
    (evalReference : Address → List Nat → Except Err Value)
    (applyValue : Value → Value → Except Err Value)
    (config : Option StringLiteralConfig) (rawMajor : Value) :
    Except Err Value :=
  match rawMajor, config with
  | .litV (.strL value), some config => do
      let charType ← evalReference config.charType []
      let charOfNat ← evalReference config.charOfNat []
      let stringOfList ← evalReference config.stringOfList []
      let listNil ← evalReference config.listNil [0]
      let nil ← applyValue listNil charType
      let listCons ← evalReference config.listCons [0]
      let cons ← applyValue listCons charType
      let list ← applyStringChars applyValue charOfNat cons
        value.toList.reverse nil
      applyValue stringOfList list
  | _, _ => .ok rawMajor

@[simp] theorem prepareStringMajor_none
    (evalReference : Address → List Nat → Except Err Value)
    (applyValue : Value → Value → Except Err Value) (rawMajor : Value) :
    prepareStringMajor evalReference applyValue none rawMajor = .ok rawMajor := by
  cases rawMajor <;> try rfl
  case litV literal => cases literal <;> rfl

/-- Successful String-major preparation is preserved by pointwise-preserving
reference evaluation and application callbacks. -/
theorem prepareStringMajor_map_ok
    {evalReference₁ evalReference₂ : Address → List Nat → Except Err Value}
    {apply₁ apply₂ : Value → Value → Except Err Value}
    (href : ∀ address uinst value,
      evalReference₁ address uinst = .ok value →
        evalReference₂ address uinst = .ok value)
    (happly : ∀ f a value, apply₁ f a = .ok value →
      apply₂ f a = .ok value)
    (config : Option StringLiteralConfig) (rawMajor result : Value)
    (h : prepareStringMajor evalReference₁ apply₁ config rawMajor =
      .ok result) :
    prepareStringMajor evalReference₂ apply₂ config rawMajor = .ok result := by
  cases rawMajor with
  | litV literal =>
      cases literal with
      | natL n => exact h
      | strL string =>
        cases config with
        | none => exact h
        | some config =>
          simp only [prepareStringMajor] at h ⊢
          cases hcharType : evalReference₁ config.charType [] with
          | error err => rw [hcharType, bindErr] at h; contradiction
          | ok charType =>
            rw [hcharType, bindOk] at h
            rw [href _ _ _ hcharType, bindOk]
            cases hcharOfNat : evalReference₁ config.charOfNat [] with
            | error err => rw [hcharOfNat, bindErr] at h; contradiction
            | ok charOfNat =>
              rw [hcharOfNat, bindOk] at h
              rw [href _ _ _ hcharOfNat, bindOk]
              cases hstringOfList :
                  evalReference₁ config.stringOfList [] with
              | error err =>
                rw [hstringOfList, bindErr] at h
                contradiction
              | ok stringOfList =>
                rw [hstringOfList, bindOk] at h
                rw [href _ _ _ hstringOfList, bindOk]
                cases hlistNil : evalReference₁ config.listNil [0] with
                | error err => rw [hlistNil, bindErr] at h; contradiction
                | ok listNil =>
                  rw [hlistNil, bindOk] at h
                  rw [href _ _ _ hlistNil, bindOk]
                  cases hnil : apply₁ listNil charType with
                  | error err => rw [hnil, bindErr] at h; contradiction
                  | ok nil =>
                    rw [hnil, bindOk] at h
                    rw [happly _ _ _ hnil, bindOk]
                    cases hlistCons : evalReference₁ config.listCons [0] with
                    | error err =>
                      rw [hlistCons, bindErr] at h
                      contradiction
                    | ok listCons =>
                      rw [hlistCons, bindOk] at h
                      rw [href _ _ _ hlistCons, bindOk]
                      cases hcons : apply₁ listCons charType with
                      | error err => rw [hcons, bindErr] at h; contradiction
                      | ok cons =>
                        rw [hcons, bindOk] at h
                        rw [happly _ _ _ hcons, bindOk]
                        cases hlist : applyStringChars apply₁ charOfNat cons
                            string.toList.reverse nil with
                        | error err => rw [hlist, bindErr] at h; contradiction
                        | ok list =>
                          rw [hlist, bindOk] at h
                          rw [applyStringChars_map_ok happly charOfNat cons
                            string.toList.reverse nil list hlist, bindOk]
                          exact happly _ _ _ h
  | sortV | piV | closV | papV | quotV | ctorV => exact h

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
    | .prj typeRefIdx fieldIdx val => do
      let value ← eval ctx fuel F env val
      projectValue ctx F typeRefIdx fieldIdx value
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
          match F.selfAddr with
          | none => neutralMember F.selfAddr recIdx.toNat
          | some block =>
            let address := Address.memberAddr block recIdx.toNat
            match ctx.externArity address with
            | none => neutralMember F.selfAddr recIdx.toNat
            | some arity => saturate ctx fuel (.extH address arity) []
      | some (.recr r) => do
        guardLvls r.lvls uinst'
        .ok (.papV (.recH F.selfAddr r { F with uinst := uinst' }) [])
      | some (.indc ind) => do
        guardLvls ind.lvls uinst'
        neutralMember F.selfAddr recIdx.toNat
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
          match ctx.externArity a with
          | none => .ok (.papV (.neuH (.const a)) [])
          | some arity => saturate ctx fuel (.extH a arity) []
      | .axio ax => do
        guardLvls ax.lvls uinst
        match ctx.externArity a with
        | none => .ok (.papV (.neuH (.const a)) [])
        | some arity => saturate ctx fuel (.extH a arity) []
      | .quot q => do
        guardLvls q.lvls uinst
        match ctx.quotientKind a with
        | none => .ok (.papV (.neuH (.const a)) [])
        | some kind =>
          if kind == q.kind then .ok (.papV (.quotH a kind) [])
          else .error (.stuck "configured quotient kind mismatch")
      | .recr r => do
        guardLvls r.lvls uinst
        .ok (.papV (.recH (some a) r (Frame.ofConst c uinst (some a))) [])
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
          .ok (.papV
            (.recH (some p.block) r (Frame.ofConst bc uinst (some p.block)))
            [])
        | .ok _ => .error (.stuck "recursor projection targets a non-recursor")
        | .error err => .error err
      | .dPrj p =>
        match resolveMut ctx p.block p.idx.toNat with
        | .ok (bc, .defn d) => do
          guardLvls d.lvls uinst
          if unfoldable d then
            eval ctx fuel (Frame.ofConst bc uinst (some p.block)) [] d.value
          else
            let member := Address.memberAddr p.block p.idx.toNat
            match ctx.externArity member with
            | none => .ok (.papV (.neuH (.const a)) [])
            | some arity => saturate ctx fuel (.extH member arity) []
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
    | .extH address _ =>
      match ctx.oracle address args with
      | some value => .ok value
      | none => .error (.oracleMissing address)
    | .quotH address kind =>
      match kind with
      | .type => .ok (.papV h args)
      | .ctor =>
        match args[2]? with
        | some representative => .ok (.quotV address representative)
        | none => .error (.stuck "Quot.mk fired without a representative")
      | .lift =>
        match args[3]?, args[5]? with
        | some fn, some quotient =>
          match quotientRep? quotient with
          | some representative => apply ctx fuel fn representative
          | none => .error (.stuck "Quot.lift argument is not a quotient")
        | _, _ => .error (.stuck "Quot.lift fired with missing arguments")
      | .ind =>
        match args[3]?, args[4]? with
        | some motive, some quotient =>
          match quotientRep? quotient with
          | some representative => apply ctx fuel motive representative
          | none => .error (.stuck "Quot.ind argument is not a quotient")
        | _, _ => .error (.stuck "Quot.ind fired with missing arguments")
    | .recH blk r F =>
      match args.getLast? with
      | none => .error (.stuck "recursor fired with no arguments")
      | some rawMajor => do
        let major ← prepareStringMajor (evalRef ctx fuel) (apply ctx fuel)
          ctx.stringLiteral rawMajor
        if major.isNeutral && ctx.preserveNeutralElims then
          .ok (.papV (.recH blk r F) args)
        else do
            guardRecMajor blk r.params.toNat major
            let (cidx, cargs) ← majorCtor
              (blk.isSome && ctx.natBlock == blk) major
            match r.rules[cidx]? with
            | none =>
              .error (.stuck s!"no recursor rule for constructor {cidx}")
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

/-! ## Fuel monotonicity

Successful evaluation is stable under raising fuel for all six mutually
recursive evaluator functions. This is the composition principle used by
sharing/inlining coherence and source-to-erased simulation proofs.
-/

private def MonoAt (fuel : Nat) : Prop :=
  (∀ ctx F env e v, eval ctx fuel F env e = .ok v →
    eval ctx (fuel + 1) F env e = .ok v) ∧
  (∀ ctx a uinst v, evalRef ctx fuel a uinst = .ok v →
    evalRef ctx (fuel + 1) a uinst = .ok v) ∧
  (∀ ctx f a v, apply ctx fuel f a = .ok v →
    apply ctx (fuel + 1) f a = .ok v) ∧
  (∀ ctx f args v, applyMany ctx fuel f args = .ok v →
    applyMany ctx (fuel + 1) f args = .ok v) ∧
  (∀ ctx h args v, saturate ctx fuel h args = .ok v →
    saturate ctx (fuel + 1) h args = .ok v) ∧
  (∀ ctx h args v, fire ctx fuel h args = .ok v →
    fire ctx (fuel + 1) h args = .ok v)

private theorem monoAt : ∀ fuel, MonoAt fuel := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro ctx F env e v h; rw [eval.eq_def] at h; simp at h
    · intro ctx a uinst v h; rw [evalRef.eq_def] at h; simp at h
    · intro ctx f a v h; rw [apply.eq_def] at h; simp at h
    · intro ctx f args v h; rw [applyMany.eq_def] at h; simp at h
    · intro ctx hd args v h; rw [saturate.eq_def] at h; simp at h
    · intro ctx hd args v h; rw [fire.eq_def] at h; simp at h
  | succ n ihn =>
    obtain ⟨ihE, ihR, ihA, ihM, ihS, ihF⟩ := ihn
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro ctx F env e v h
      cases e with
      | var i =>
        rw [eval.eq_def] at h ⊢; dsimp only at h ⊢; exact h
      | sort i =>
        rw [eval.eq_def] at h ⊢; dsimp only at h ⊢; exact h
      | str i =>
        rw [eval.eq_def] at h ⊢; dsimp only at h ⊢; exact h
      | nat i =>
        rw [eval.eq_def] at h ⊢; dsimp only at h ⊢; exact h
      | lam u dom body =>
        rw [eval.eq_def] at h ⊢; dsimp only at h ⊢; exact h
      | all u o dom cod =>
        rw [eval.eq_def] at h ⊢; dsimp only at h ⊢; exact h
      | letE nd typ val body =>
        rw [eval.eq_def] at h ⊢; dsimp only at h ⊢
        cases hv : eval ctx n F env val with
        | error err => rw [hv, bindErr] at h; contradiction
        | ok valV =>
          rw [hv, bindOk] at h
          rw [ihE _ _ _ _ _ hv, bindOk]
          exact ihE _ _ _ _ _ h
      | app fn arg =>
        rw [eval.eq_def] at h ⊢; dsimp only at h ⊢
        cases hf : eval ctx n F env fn with
        | error err => rw [hf, bindErr] at h; contradiction
        | ok fv =>
          rw [hf, bindOk] at h
          rw [ihE _ _ _ _ _ hf, bindOk]
          cases ha : eval ctx n F env arg with
          | error err => rw [ha, bindErr] at h; contradiction
          | ok av =>
            rw [ha, bindOk] at h
            rw [ihE _ _ _ _ _ ha, bindOk]
            exact ihA _ _ _ _ h
      | prj typeIdx fieldIdx val =>
        rw [eval.eq_def] at h ⊢; dsimp only at h ⊢
        cases hv : eval ctx n F env val with
        | error err => rw [hv, bindErr] at h; contradiction
        | ok valV =>
          rw [hv, bindOk] at h
          rw [ihE _ _ _ _ _ hv, bindOk]
          exact h
      | share i =>
        rw [eval.eq_def] at h ⊢; dsimp only at h ⊢
        cases hs : F.sharing[i.toNat]? with
        | none => rw [hs] at h; simp at h
        | some shared =>
          rw [hs] at h
          simp only at h ⊢
          exact ihE _ _ _ _ _ h
      | ref refIdx univIdxs =>
        rw [eval.eq_def] at h ⊢; dsimp only at h ⊢
        cases hr : F.refs[refIdx.toNat]? with
        | none => rw [hr] at h; simp at h
        | some address =>
          rw [hr] at h
          simp only at h ⊢
          cases hu : evalUnivArgs F univIdxs with
          | error err => rw [hu, bindErr] at h; contradiction
          | ok uinst =>
            rw [hu, bindOk] at h
            rw [bindOk]
            exact ihR _ _ _ _ h
      | recur recIdx univIdxs =>
        rw [eval.eq_def] at h ⊢; dsimp only at h ⊢
        cases hu : evalUnivArgs F univIdxs with
        | error err => rw [hu, bindErr] at h; contradiction
        | ok uinst =>
          rw [hu, bindOk] at h
          rw [bindOk]
          cases hm : F.selfMuts[recIdx.toNat]? with
          | none => rw [hm] at h; simp at h
          | some member =>
            rw [hm] at h
            cases member with
            | defn d =>
              simp only at h ⊢
              cases hg : guardLvls d.lvls uinst with
              | error err => rw [hg, bindErr] at h; contradiction
              | ok checked =>
                rw [hg, bindOk] at h
                rw [bindOk]
                cases hu : unfoldable d with
                | false =>
                  rw [hu] at h
                  simp only [Bool.false_eq_true, if_false] at h ⊢
                  cases hsa : F.selfAddr with
                  | none =>
                    rw [hsa] at h
                    dsimp only at h ⊢
                    exact h
                  | some block =>
                    rw [hsa] at h
                    dsimp only at h ⊢
                    cases hext : ctx.externArity
                        (Address.memberAddr block recIdx.toNat) with
                    | none =>
                      rw [hext] at h
                      dsimp only at h ⊢
                      exact h
                    | some arity =>
                      rw [hext] at h
                      dsimp only at h ⊢
                      exact ihS _ _ _ _ h
                | true =>
                  rw [hu] at h
                  simp only [if_true] at h ⊢
                  exact ihE _ _ _ _ _ h
            | recr r => simp only at h ⊢; exact h
            | indc i => simp only at h ⊢; exact h
    · intro ctx address uinst v h
      rw [evalRef.eq_def] at h ⊢; dsimp only at h ⊢
      cases hr : ctx.resolve address with
      | none => rw [hr] at h; simp at h
      | some c =>
        rw [hr] at h
        simp only at h ⊢
        cases hi : c.info with
        | defn d =>
          rw [hi] at h
          simp only at h ⊢
          cases hg : guardLvls d.lvls uinst with
          | error err => rw [hg, bindErr] at h; contradiction
          | ok checked =>
            rw [hg, bindOk] at h
            rw [bindOk]
            cases hu : unfoldable d with
            | false =>
              rw [hu] at h
              simp only [Bool.false_eq_true, if_false] at h ⊢
              cases hext : ctx.externArity address with
              | none =>
                rw [hext] at h
                simpa using h
              | some arity =>
                rw [hext] at h
                simpa using ihS ctx (.extH address arity) [] v h
            | true =>
              rw [hu] at h
              simp only [if_true] at h ⊢
              exact ihE _ _ _ _ _ h
        | axio a =>
          rw [hi] at h
          simp only at h ⊢
          cases hg : guardLvls a.lvls uinst with
          | error err => rw [hg, bindErr] at h; contradiction
          | ok checked =>
            rw [hg, bindOk] at h
            rw [bindOk]
            cases hext : ctx.externArity address with
            | none =>
              rw [hext] at h
              simpa using h
            | some arity =>
              rw [hext] at h
              simpa using ihS ctx (.extH address arity) [] v h
        | quot q => rw [hi] at h; simpa using h
        | recr r => rw [hi] at h; simpa using h
        | iPrj p => rw [hi] at h; simpa using h
        | cPrj p =>
          rw [hi] at h
          simp only at h ⊢
          cases hm : resolveMut ctx p.block p.idx.toNat with
          | error err => rw [hm] at h; simp only at h ⊢; exact h
          | ok pair =>
            rw [hm] at h
            rcases pair with ⟨bc, member⟩
            cases member with
            | defn d => simp only at h ⊢; exact h
            | recr r => simp only at h ⊢; exact h
            | indc ind =>
              simp only at h ⊢
              cases hc : ind.ctors[p.cidx.toNat]? with
              | none => rw [hc] at h; simp only at h ⊢; exact h
              | some ct =>
                rw [hc] at h
                simp only at h ⊢
                cases hg : guardLvls ct.lvls uinst with
                | error err => rw [hg, bindErr] at h; contradiction
                | ok checked =>
                  rw [hg, bindOk] at h
                  rw [bindOk]
                  exact ihS _ _ _ _ h
        | rPrj p => rw [hi] at h; simpa using h
        | dPrj p =>
          rw [hi] at h
          simp only at h ⊢
          cases hm : resolveMut ctx p.block p.idx.toNat with
          | error err => rw [hm] at h; simp only at h ⊢; exact h
          | ok pair =>
            rw [hm] at h
            rcases pair with ⟨bc, member⟩
            cases member with
            | indc i => simp only at h ⊢; exact h
            | recr r => simp only at h ⊢; exact h
            | defn d =>
              simp only at h ⊢
              cases hg : guardLvls d.lvls uinst with
              | error err => rw [hg, bindErr] at h; contradiction
              | ok checked =>
                rw [hg, bindOk] at h
                rw [bindOk]
                cases hu : unfoldable d with
                | false =>
                  rw [hu] at h
                  simp only [Bool.false_eq_true, if_false] at h ⊢
                  cases hext : ctx.externArity
                      (Address.memberAddr p.block p.idx.toNat) with
                  | none =>
                    rw [hext] at h
                    dsimp only at h ⊢
                    exact h
                  | some arity =>
                    rw [hext] at h
                    dsimp only at h ⊢
                    exact ihS _ _ _ _ h
                | true =>
                  rw [hu] at h
                  simp only [if_true] at h ⊢
                  exact ihE _ _ _ _ _ h
        | muts ms => rw [hi] at h; simp at h
    · intro ctx f a v h
      cases f with
      | sortV lvl => rw [apply.eq_def] at h; simp at h
      | piV u o F env dom cod => rw [apply.eq_def] at h; simp at h
      | closV u F env dom body =>
        rw [apply.eq_def] at h ⊢; dsimp only at h ⊢
        exact ihE _ _ _ _ _ h
      | papV hd args =>
        rw [apply.eq_def] at h ⊢; dsimp only at h ⊢
        exact ihS _ _ _ _ h
      | quotV address representative => rw [apply.eq_def] at h; simp at h
      | ctorV block indIdx cidx args => rw [apply.eq_def] at h; simp at h
      | litV lit => rw [apply.eq_def] at h; simp at h
    · intro ctx f args v h
      cases args with
      | nil => rw [applyMany.eq_def] at h ⊢; dsimp only at h ⊢; exact h
      | cons a rest =>
        rw [applyMany.eq_def] at h ⊢; dsimp only at h ⊢
        cases ha : apply ctx n f a with
        | error err => rw [ha, bindErr] at h; contradiction
        | ok f' =>
          rw [ha, bindOk] at h
          rw [ihA _ _ _ _ ha, bindOk]
          exact ihM _ _ _ _ h
    · intro ctx hd args v h
      rw [saturate.eq_def] at h ⊢; dsimp only at h ⊢
      cases ha : hd.arity? with
      | none => rw [ha] at h; simp only at h ⊢; exact h
      | some arity =>
        rw [ha] at h
        simp only at h ⊢
        cases heq : args.length == arity with
        | false =>
          rw [heq] at h
          simp only [Bool.false_eq_true, if_false] at h ⊢
          exact h
        | true =>
          rw [heq] at h
          simp only [if_true] at h ⊢
          exact ihF _ _ _ _ h
    · intro ctx hd args v h
      cases hd with
      | ctorH block indIdx cidx arity =>
        rw [fire.eq_def] at h ⊢; dsimp only at h ⊢; exact h
      | neuH id =>
        rw [fire.eq_def] at h ⊢; dsimp only at h ⊢; exact h
      | extH address arity =>
        rw [fire.eq_def] at h ⊢; dsimp only at h ⊢; exact h
      | quotH address kind =>
        rw [fire.eq_def] at h ⊢; dsimp only at h ⊢
        cases kind with
        | type | ctor => exact h
        | lift =>
          simp only at h ⊢
          cases hfn : args[3]? with
          | none =>
            rw [hfn] at h
            dsimp only at h ⊢
            exact h
          | some fn =>
            rw [hfn] at h
            cases hquotient : args[5]? with
            | none =>
              rw [hquotient] at h
              dsimp only at h ⊢
              exact h
            | some quotient =>
              rw [hquotient] at h
              dsimp only at h ⊢
              cases hrep : quotientRep? quotient with
              | none =>
                rw [hrep] at h
                dsimp only at h ⊢
                exact h
              | some representative =>
                rw [hrep] at h
                dsimp only at h ⊢
                exact ihA _ _ _ _ h
        | ind =>
          simp only at h ⊢
          cases hmotive : args[3]? with
          | none =>
            rw [hmotive] at h
            dsimp only at h ⊢
            exact h
          | some motive =>
            rw [hmotive] at h
            cases hquotient : args[4]? with
            | none =>
              rw [hquotient] at h
              dsimp only at h ⊢
              exact h
            | some quotient =>
              rw [hquotient] at h
              dsimp only at h ⊢
              cases hrep : quotientRep? quotient with
              | none =>
                rw [hrep] at h
                dsimp only at h ⊢
                exact h
              | some representative =>
                rw [hrep] at h
                dsimp only at h ⊢
                exact ihA _ _ _ _ h
      | recH block r F =>
        rw [fire.eq_def] at h ⊢; dsimp only at h ⊢
        cases hl : args.getLast? with
        | none => rw [hl] at h; simp only at h ⊢; exact h
        | some major =>
          rw [hl] at h
          simp only at h ⊢
          cases hp : prepareStringMajor (evalRef ctx n) (apply ctx n)
              ctx.stringLiteral major with
          | error err => rw [hp, bindErr] at h; contradiction
          | ok prepared =>
            rw [hp, bindOk] at h
            have hp' : prepareStringMajor (evalRef ctx (n + 1))
                (apply ctx (n + 1)) ctx.stringLiteral major = .ok prepared :=
              prepareStringMajor_map_ok
                (fun address uinst value href =>
                  ihR ctx address uinst value href)
                (fun function argument value happly =>
                  ihA ctx function argument value happly)
                ctx.stringLiteral major prepared hp
            rw [hp', bindOk]
            cases hn : prepared.isNeutral && ctx.preserveNeutralElims with
            | true =>
              simp only [hn] at h ⊢
              exact h
            | false =>
              simp only [hn] at h ⊢
              cases hg : guardRecMajor block r.params.toNat prepared with
              | error err => rw [hg, bindErr] at h; contradiction
              | ok checked =>
                rw [hg, bindOk] at h
                rw [bindOk]
                cases hm : majorCtor
                    (block.isSome && ctx.natBlock == block) prepared with
                | error err => rw [hm, bindErr] at h; contradiction
                | ok pair =>
                  rcases pair with ⟨cidx, cargs⟩
                  rw [hm, bindOk] at h
                  rw [bindOk]
                  cases hr : r.rules[cidx]? with
                  | none => rw [hr] at h; simp only at h ⊢; exact h
                  | some rule =>
                    rw [hr] at h
                    simp only at h ⊢
                    cases heq :
                        cargs.length != r.params.toNat + rule.fields.toNat with
                    | false =>
                      rw [heq] at h
                      simp only [Bool.false_eq_true, if_false] at h ⊢
                      cases he : eval ctx n F [] rule.rhs with
                      | error err => rw [he, bindErr] at h; contradiction
                      | ok rhsV =>
                        rw [he, bindOk] at h
                        rw [ihE _ _ _ _ _ he, bindOk]
                        exact ihM _ _ _ _ h
                    | true =>
                      rw [heq] at h
                      simp only [if_true] at h ⊢
                      exact h

theorem eval_mono {ctx : EvalCtx} {fuel fuel' : Nat} {F : Frame}
    {env : List Value} {e : Expr} {v : Value} (hle : fuel ≤ fuel')
    (h : eval ctx fuel F env e = .ok v) :
    eval ctx fuel' F env e = .ok v := by
  exact fuel_mono_of_succ
    (fun current hrun => (monoAt current).1 _ _ _ _ _ hrun) hle h

theorem evalRef_mono {ctx : EvalCtx} {fuel fuel' : Nat} {a : Address}
    {uinst : List Nat} {v : Value} (hle : fuel ≤ fuel')
    (h : evalRef ctx fuel a uinst = .ok v) :
    evalRef ctx fuel' a uinst = .ok v := by
  exact fuel_mono_of_succ
    (fun current hrun => (monoAt current).2.1 _ _ _ _ hrun) hle h

theorem apply_mono {ctx : EvalCtx} {fuel fuel' : Nat} {f a v : Value}
    (hle : fuel ≤ fuel') (h : apply ctx fuel f a = .ok v) :
    apply ctx fuel' f a = .ok v := by
  exact fuel_mono_of_succ
    (fun current hrun => (monoAt current).2.2.1 _ _ _ _ hrun) hle h

theorem applyMany_mono {ctx : EvalCtx} {fuel fuel' : Nat} {f : Value}
    {args : List Value} {v : Value} (hle : fuel ≤ fuel')
    (h : applyMany ctx fuel f args = .ok v) :
    applyMany ctx fuel' f args = .ok v := by
  exact fuel_mono_of_succ
    (fun current hrun => (monoAt current).2.2.2.1 _ _ _ _ hrun) hle h

theorem saturate_mono {ctx : EvalCtx} {fuel fuel' : Nat} {h : Head}
    {args : List Value} {v : Value} (hle : fuel ≤ fuel')
    (hs : saturate ctx fuel h args = .ok v) :
    saturate ctx fuel' h args = .ok v := by
  exact fuel_mono_of_succ
    (fun current hrun => (monoAt current).2.2.2.2.1 _ _ _ _ hrun) hle hs

theorem fire_mono {ctx : EvalCtx} {fuel fuel' : Nat} {h : Head}
    {args : List Value} {v : Value} (hle : fuel ≤ fuel')
    (hs : fire ctx fuel h args = .ok v) :
    fire ctx fuel' h args = .ok v := by
  exact fuel_mono_of_succ
    (fun current hrun => (monoAt current).2.2.2.2.2 _ _ _ _ hrun) hle hs

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
  Address.replicate n

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
private def aPair := addrOf 0x1F
private def aPairBlock := addrOf 0x20
private def aMk := addrOf 0x21
private def aSortAt := addrOf 0x22
private def aDefBlock := addrOf 0x23
private def aDPrj := addrOf 0x24
private def aQuotMk := addrOf 0x25
private def aQuotLift := addrOf 0x26
private def aQuotInd := addrOf 0x27
private def aMissing := addrOf 0x30
private def aCharBlock := addrOf 0x31
private def aChar := addrOf 0x32
private def aCharMk := addrOf 0x33
private def aCharOfNat := addrOf 0x34
private def aListBlock := addrOf 0x35
private def aListNil := addrOf 0x36
private def aListCons := addrOf 0x37
private def aStringBlock := addrOf 0x38
private def aStringMk := addrOf 0x39
private def aStringOfList := addrOf 0x3A
private def aStringRec := addrOf 0x3B

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

private def cPair := prjConst (.iPrj { idx := 0, block := aPairBlock })
private def cMk := prjConst (.cPrj { idx := 0, cidx := 0, block := aPairBlock })

/-- `Sort u` at its own universe variable: instantiation probe. -/
private def cSortAt : Constant :=
  { info := .defn
      { kind := .defn, safety := .safe, lvls := 1
        typ := .sort 0, value := .sort 0 }
    sharing := #[], refs := #[], univs := #[.var 0] }

/-- A mutual block with one definition member (`succ zero`), reached
only through a `dPrj`; block refs: 0 = zero, 1 = succ. -/
private def cDefBlock : Constant :=
  { info := .muts #[
      .defn { kind := .defn, safety := .safe, lvls := 0
              typ := .ref 0 #[]
              value := .app (.ref 1 #[]) (.ref 0 #[]) }]
    sharing := #[], refs := #[aZero, aSucc], univs := #[] }

private def cDPrj := prjConst (.dPrj { idx := 0, block := aDefBlock })

/-- Configured quotient primitive stand-ins. -/
private def cQuotMk : Constant :=
  { info := .quot { kind := .ctor, lvls := 0, typ := .sort 0 }
    sharing := #[], refs := #[], univs := #[] }

private def cQuotLift : Constant :=
  { info := .quot { kind := .lift, lvls := 0, typ := .sort 0 }
    sharing := #[], refs := #[], univs := #[] }

private def cQuotInd : Constant :=
  { info := .quot { kind := .ind, lvls := 0, typ := .sort 0 }
    sharing := #[], refs := #[], univs := #[] }

/-! A small representation-faithful String fixture.  Its definitions are
deliberately much smaller than the upstream UTF-8 implementation, but the
constant graph and application telescope are exact: `Char.ofNat`,
`List.nil/cons.{0}`, then `String.ofList`. -/

private def charInd : Inductive :=
  { isUnsafe := false, lvls := 0, params := 0, indices := 0
    typ := .sort 0
    ctors := #[{ isUnsafe := false, lvls := 0, cidx := 0, params := 0
                 fields := 1, typ := .sort 0 }] }

private def cCharBlock : Constant :=
  { info := .muts #[.indc charInd]
    sharing := #[], refs := #[], univs := #[] }

private def cChar := prjConst (.iPrj { idx := 0, block := aCharBlock })
private def cCharMk :=
  prjConst (.cPrj { idx := 0, cidx := 0, block := aCharBlock })

private def cCharOfNat : Constant :=
  { info := .defn
      { kind := .defn, safety := .safe, lvls := 0
        typ := .sort 0
        value := .lam .many (.sort 0) (.app (.ref 0 #[]) (.var 0)) }
    sharing := #[], refs := #[aCharMk], univs := #[] }

private def listInd : Inductive :=
  { isUnsafe := false, lvls := 1, params := 1, indices := 0
    typ := .sort 0
    ctors := #[
      { isUnsafe := false, lvls := 1, cidx := 0, params := 1, fields := 0
        typ := .sort 0 },
      { isUnsafe := false, lvls := 1, cidx := 1, params := 1, fields := 2
        typ := .sort 0 }] }

private def cListBlock : Constant :=
  { info := .muts #[.indc listInd]
    sharing := #[], refs := #[], univs := #[] }

private def cListNil :=
  prjConst (.cPrj { idx := 0, cidx := 0, block := aListBlock })
private def cListCons :=
  prjConst (.cPrj { idx := 0, cidx := 1, block := aListBlock })

private def stringInd : Inductive :=
  { isUnsafe := false, lvls := 0, params := 0, indices := 0
    typ := .sort 0
    ctors := #[{ isUnsafe := false, lvls := 0, cidx := 0, params := 0
                 fields := 1, typ := .sort 0 }] }

private def stringRecRule : RecursorRule :=
  { fields := 1
    rhs := .lam .many (.sort 0) (.lam .many (.sort 0)
      (.lam .many (.sort 0) (.var 0))) }

private def stringRec : Recursor :=
  { k := false, isUnsafe := false, lvls := 0, params := 0, indices := 0
    motives := 1, minors := 1, typ := .sort 0
    rules := #[stringRecRule] }

private def cStringBlock : Constant :=
  { info := .muts #[.indc stringInd, .recr stringRec]
    sharing := #[], refs := #[], univs := #[] }

private def cStringMk :=
  prjConst (.cPrj { idx := 0, cidx := 0, block := aStringBlock })

private def cStringOfList : Constant :=
  { info := .defn
      { kind := .defn, safety := .safe, lvls := 0
        typ := .sort 0
        value := .lam .many (.sort 0) (.app (.ref 0 #[]) (.var 0)) }
    sharing := #[], refs := #[aStringMk], univs := #[] }

private def cStringRec :=
  prjConst (.rPrj { idx := 1, block := aStringBlock })

private def resolver : Address → Option Constant := fun a =>
  (([(aNatBlock, cNatBlock), (aNat, cNat), (aZero, cZero), (aSucc, cSucc),
     (aNatRec, cNatRec), (aAdd, cAdd), (aAx, cAx), (aThm, cThm),
     (aOpq, cOpq), (aPairBlock, cPairBlock), (aMk, cMk),
     (aPair, cPair),
     (aSortAt, cSortAt), (aDefBlock, cDefBlock), (aDPrj, cDPrj),
     (aQuotMk, cQuotMk), (aQuotLift, cQuotLift),
     (aQuotInd, cQuotInd),
     (aCharBlock, cCharBlock), (aChar, cChar), (aCharMk, cCharMk),
     (aCharOfNat, cCharOfNat), (aListBlock, cListBlock),
     (aListNil, cListNil), (aListCons, cListCons),
     (aStringBlock, cStringBlock), (aStringMk, cStringMk),
     (aStringOfList, cStringOfList), (aStringRec, cStringRec)] :
      List (Address × Constant)).find?
    (fun p => p.1 == a)).map (·.2)

private def testBlobs : Address → Option Blob := fun a =>
  if a == aTwo then some (.natB 2)
  else if a == aThree then some (.natB 3)
  else if a == aHello then some (.strB "hello")
  else none

private def quotientKinds : Address → Option QuotKind := fun address =>
  if address == aQuotMk then some .ctor
  else if address == aQuotLift then some .lift
  else if address == aQuotInd then some .ind
  else none

private def ctx : EvalCtx :=
  { resolve := resolver, blobs := testBlobs, natBlock := some aNatBlock
    quotientKind := quotientKinds }

/-- Test frame refs: 0 = add, 1 = zero, 2 = succ, 3 = blob 2,
4 = blob 3, 5 = mk, 6 = axiom, 7 = thm, 8 = opaq, 9 = sortAt,
10 = "hello" blob, 11 = Nat, 12 = unresolvable, 13 = dPrj,
14 = Quot.mk, 15 = Quot.lift, 16 = Quot.ind, 17 = Pair. -/
private def testF : Frame :=
  { refs := #[aAdd, aZero, aSucc, aTwo, aThree, aMk, aAx, aThm, aOpq,
              aSortAt, aHello, aNat, aMissing, aDPrj, aQuotMk, aQuotLift,
              aQuotInd, aPair]
    univs := #[.succ (.succ .zero)]
    sharing := #[.app (.ref 2 #[]) (.ref 1 #[])] }

private def run (e : Expr) : Except Err Value := evalClosed ctx testF e

private def neutralCtx : EvalCtx :=
  { ctx with preserveNeutralElims := true }

private def stringConfig : StringLiteralConfig :=
  { charType := aChar
    charOfNat := aCharOfNat
    stringOfList := aStringOfList
    listNil := aListNil
    listCons := aListCons }

private def stringCtx : EvalCtx :=
  { ctx with stringLiteral := some stringConfig }

private def runNeutral (e : Expr) : Except Err Value :=
  evalClosed neutralCtx testF e

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

private def apps : Expr → List Expr → Expr
  | function, [] => function
  | function, argument :: rest => apps (.app function argument) rest

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

-- malformed untyped majors are rejected before rule dispatch
#guard (match fire ctx 10 (.recH (some aNatBlock) natRec {})
    [.ctorV aPairBlock 0 0 []] with
  | .error (.stuck
      "constructor major belongs to a different recursor block") => true
  | _ => false)
#guard (match fire ctx 10
    (.recH (some aNatBlock) { natRec with params := 1 } {})
    [.litV (.natL 0)] with
  | .error (.stuck "literal major requires a zero-parameter recursor") => true
  | _ => false)

-- literal blobs and ι-peeling (mixed literal/ctor chains decode)
#guard runNat? (.nat 3) == some 2
#guard runNat? (.app (.app (.ref 0 #[]) (.nat 3)) (.nat 4)) == some 5
#guard runNat? (.app (.app (.ref 0 #[]) (natE 1)) (.nat 4)) == some 4
#guard (match run (.str 10) with
  | .ok (.litV (.strL "hello")) => true | _ => false)

private def stringListCodes : Nat → Value → Option (List Nat)
  | 0, _ => none
  | _, .ctorV block 0 0 [_] =>
      if block == aListBlock then some [] else none
  | fuel + 1, .ctorV block 0 1 [_, .ctorV charBlock 0 0
      [.litV (.natL codepoint)], tail] =>
      if block == aListBlock && charBlock == aCharBlock then
        (stringListCodes fuel tail).map (codepoint :: ·)
      else none
  | _, _ => none

private def stringF : Frame :=
  { refs := #[aStringRec, aHello]
    univs := #[.zero] }

private def stringLiteralEntry : Expr :=
  apps (.ref 0 #[]) [.sort 0, .sort 0, .str 1]

-- Exercise the ordinary ref/application/saturation route, not only `fire`.
#guard (match evalClosed stringCtx stringF stringLiteralEntry with
  | .ok list => stringListCodes 10 list == some [104, 101, 108, 108, 111]
  | _ => false)

private def fireStringLiteral (config : Option StringLiteralConfig)
    (block : Address) (value : String) : Except Err Value :=
  fire { ctx with stringLiteral := config } 1000
    (.recH (some block) stringRec
      (Frame.ofConst cStringBlock [] (some aStringBlock)))
    [.sortV 0, .sortV 0, .litV (.strL value)]

-- String literal majors follow the upstream constructor-expansion chain.
#guard (match fireStringLiteral (some stringConfig) aStringBlock "Aé" with
  | .ok list => stringListCodes 10 list == some [65, 233]
  | _ => false)
#guard (match fireStringLiteral (some stringConfig) aStringBlock "" with
  | .ok list => stringListCodes 10 list == some []
  | _ => false)

-- Configuration is opt-in, exact-addressed, and ordinary family checking
-- still rejects a String constructor at a different recursor block.
#guard (match fireStringLiteral none aStringBlock "A" with
  | .error (.stuck "recursor major premise is not a constructor") => true
  | _ => false)
#guard (match fireStringLiteral
    (some { stringConfig with charOfNat := aMissing }) aStringBlock "A" with
  | .error (.unknownRef address) => address == aMissing
  | _ => false)
#guard (match fireStringLiteral
    (some { stringConfig with stringOfList := aNat }) aStringBlock "A" with
  | .error (.stuck "recursor major premise is not a constructor") => true
  | _ => false)
#guard (match fireStringLiteral (some stringConfig) aNatBlock "A" with
  | .error (.stuck
      "constructor major belongs to a different recursor block") => true
  | _ => false)

-- Projections resolve their encoded type reference, cross-check the
-- constructor family, and skip constructor parameters: mk A B x y.
private def pairValueSource : Expr :=
  apps (.ref 5 #[]) [.sort 0, .sort 0, natE 1, natE 2]

#guard runNat? (.prj 17 0 pairValueSource) == some 1
#guard runNat? (.prj 17 1 pairValueSource) == some 2

#guard (match run (.prj 11 0 pairValueSource) with
  | .error (.stuck "projection value does not match its type ref") => true
  | _ => false)
#guard (match run (.prj 0 0 (natE 0)) with
  | .error (.stuck
      "projection type ref is not an inductive projection") => true
  | _ => false)
#guard (match run (.prj 99 0 (natE 0)) with
  | .error (.stuck "projection type ref index 99 out of range") => true
  | _ => false)
#guard (match run (.prj 12 0 (natE 0)) with
  | .error (.unknownRef address) => address == aMissing
  | _ => false)
#guard (match run (.prj 11 0 (natE 0)) with
  | .error (.stuck "projection 0 out of range") => true
  | _ => false)

-- Open evaluation retains neutral eliminations as explicit pap spines.
-- Strict evaluation preserves the constructor-only erasure boundary.
#guard (match runNeutral (.prj 11 0 (.ref 11 #[])) with
  | .ok (.papV (.neuH (.projection typeAddress 0))
      [.papV (.neuH (.const sourceAddress)) []]) =>
    typeAddress == aNat && sourceAddress == aNat
  | _ => false)
#guard (match run (.prj 11 0 (.ref 11 #[])) with
  | .error (.stuck "projection from a non-constructor value") => true
  | _ => false)
#guard (match runNeutral
    (.app (.prj 11 0 (.ref 11 #[])) (natE 0)) with
  | .ok (.papV (.neuH (.projection typeAddress 0))
      [.papV (.neuH (.const sourceAddress)) [],
       .ctorV block 0 0 []]) =>
    typeAddress == aNat && sourceAddress == aNat && block == aNatBlock
  | _ => false)

private def neutralMajor : Value :=
  .papV (.neuH (.const aNat)) []

private def neutralRecArgs : List Value :=
  [.sortV 0, .sortV 0, .sortV 0, neutralMajor]

#guard Value.isNeutral
  (.papV (.recH (some aNatBlock) natRec {}) neutralRecArgs)
#guard !Value.isNeutral
  (.papV (.recH (some aNatBlock) natRec {}) (neutralRecArgs.take 3))
#guard (match fire neutralCtx 10 (.recH (some aNatBlock) natRec {})
    neutralRecArgs with
  | .ok (.papV (.recH (some block) _ _) args) =>
    block == aNatBlock && args.length == neutralRecArgs.length
  | _ => false)
#guard (match fire ctx 10 (.recH (some aNatBlock) natRec {})
    neutralRecArgs with
  | .error (.stuck "recursor major premise is not a constructor") => true
  | _ => false)

private def neutralMemberFrame (block : Option Address) : Frame :=
  { selfMuts := #[.indc natInd], selfAddr := block }

#guard (match
    eval neutralCtx 10 (neutralMemberFrame (some aNatBlock)) [] (.recur 0 #[]),
    eval neutralCtx 10 (neutralMemberFrame (some aPairBlock)) [] (.recur 0 #[])
  with
  | .ok (.papV (.neuH (.member leftBlock 0)) []),
      .ok (.papV (.neuH (.member rightBlock 0)) []) =>
    leftBlock == aNatBlock && rightBlock == aPairBlock &&
      leftBlock != rightBlock
  | _, _ => false)
#guard (match eval neutralCtx 10 (neutralMemberFrame none) [] (.recur 0 #[]) with
  | .error (.stuck "neutral mutual member has no block identity") => true
  | _ => false)

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

-- dPrj unfolds its definition member through the block frame
#guard runNat? (.ref 13 #[]) == some 1

-- Configured quotient ι: both eliminators expose the representative stored
-- by a saturated Quot.mk. The ind witness is contentful (`succ 1 = 2`).
private def quotientMkOne : Expr :=
  apps (.ref 14 #[]) [.sort 0, .sort 0, natE 1]

private def quotientLiftOne : Expr :=
  apps (.ref 15 #[])
    [.sort 0, .sort 0, .sort 0,
      .lam .many (.sort 0) (.var 0), .sort 0, quotientMkOne]

private def quotientIndOne : Expr :=
  apps (.ref 16 #[])
    [.sort 0, .sort 0, .sort 0,
      .lam .many (.sort 0) (.app (.ref 2 #[]) (.var 0)), quotientMkOne]

#guard runNat? quotientLiftOne == some 1
#guard runNat? quotientIndOne == some 2

-- The semantic hook is address-configured: the same constants remain neutral
-- in a context that has not authorized quotient primitives.
private def neutralQuotientCtx : EvalCtx :=
  { ctx with quotientKind := fun _ => none }

#guard (match evalClosed neutralQuotientCtx testF quotientLiftOne with
  | .ok (.papV (.neuH (.const address)) args) =>
    address == aQuotLift && args.length == 6
  | _ => false)

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
#guard (match run (.prj 11 0 (.nat 3)) with
  | .error (.stuck "projection from a literal") => true | _ => false)

-- fuel: Ω diverges; a starved success is `.fuel`, not `.stuck`
private def delta : Expr := .lam .many (.sort 0) (.app (.var 0) (.var 0))
#guard (match run (.app delta delta) with
  | .error .fuel => true | _ => false)
#guard (match evalClosed ctx testF
    (.app (.app (.ref 0 #[]) (natE 2)) (natE 3)) (fuel := 10) with
  | .error .fuel => true | _ => false)

end Ix.Compiler.Ixon.Eval
