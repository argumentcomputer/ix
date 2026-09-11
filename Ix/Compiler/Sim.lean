import Ix.Compiler.Ixon.Sharing.Eval
import Ix.Compiler.IxIR0.Mono
import Ix.Compiler.IxIR0.ProjectionSafe
import Ix.Compiler.Sim.Segment

/-!
# The erasure simulation, stages 1 + 2a + 2b plus sharing composition

Stage 1 proved the theorem on the pure λ-fragment; stage 2a added
literals, constructors, projections, and reference
resolution with the program-level `Covered` relation. **Stage 2b puts
recursor ι under the theorem**, including parameterized List-shaped layouts,
protected split source-only index segments, and indexed recursive self calls.
Visible constructor-parameter prefixes stutter over their dropped target
arguments:

- `PErase` is now indexed by the frame's **refs, selfMuts, and
  selfAddr** (a `recur` reads the mutual block through the frame, and
  literal peeling keys on the block identity), plus a **self
  context** `sc : Option (Address × Nat)` — set to the (block,
  member) pair exactly while relating a recursor rule's body.
- `RecMember` is the per-recursor program correspondence: the source
  recursor resolves through its block, the erased declaration sits at
  the synthetic member address with `numArgs = params + motives + minors` and
  `natLit` pinned to the *same* well-known-address comparison the
  evaluator peels on, and every rule's right-hand side peels
  (`peelChain`) to a body related under the rule mask
  `fields·true ++ reverse(map policyKept recRulePolicy)` — ghost parameter
  and motive slots are dropped environment slots, the stage-1 insight again.
- The recursor-self slot: a rule-body `recur` of the block's own member relates
  to `var mask.length` through `recurS` for index-free heads and
  `RecEraseSpine.selfHead` for indexed spines, with **no
  program-level hypothesis** — requiring `RecMember` there would make
  the relation non-well-founded (the rule body would contain its own
  coverage). The obligations live in the **environment base**
  instead: `EnvRel.selfB` seats the unapplied target recursor pap
  below the rule binders, carrying `RecMember` — constructible at
  fire time, where coverage is in hand.
- Ghost parameter or motive arguments erase to applications of `◻` — `appG`,
  guarded by `RecPrefix` (the head is syntactically a recursor spine
  whose next policy is `ghost`). The guard is what makes the clause
  sound: an unguarded ghost application against a kept-binder closure
  is false. `recSpine_eval` pins the evaluated head to a recursor
  pap so the value relation can only be `papRec`.
- Ghost arguments at ordinary unfoldable definition heads use `appDG`.
  `DefSpine` follows the visible application spine through the definition's
  literal implementation lambdas, independently of the executable eraser's
  declaration-type policy. Both the type and the actual runtime binder must
  therefore classify the slot as dropped; a mismatched type/value telescope
  cannot justify erasure.
- `papRec` carries a `RuntimePolicyPrefix` cursor through parameter, motive,
  and minor applications. Kept slots require `ValRel`; ghost slots consume
  both sides but leave their runtime values unconstrained, while exact
  `PErase.appG` still emits `◻`. For indexed recursors, `RecEraseSpine`
  keeps the complete `recPolicy` cursor local while source-only indices
  stutter, then `papRecI` exposes only the ready-to-fire pre-major value. If
  the visible spine stops inside that index suffix, `recW` evaluates and
  let-captures the target pap before wrapping it in ignored continuations;
  `papRecIW` keeps the escaped wrapper closed under generic application and
  transitions to `papRecI` exactly at the final index. Intermediate raw target
  paps are deliberately excluded from `ValRel`: they are already one argument
  from firing while the source still owes indices.
- Constructor paps and values carry the reusable `PolicyPrefix` cursor from
  `Sim/Segment.lean`. `CtorParamSpine` handles every visible dropped-parameter
  prefix. A partial prefix emits ignored target lambdas (`ctorW`) and
  `papCtorParams` keeps those wrappers closed under later generic application,
  including after escape through a variable or let; after the last parameter,
  ordinary `papCtor`/`ctorV` application retains and relates the fields.
  Recursor firing guards constructor-block identity, and `RecMember` stores a
  finite `BlockParams` witness, so the global parameterized value relation
  cannot feed a mismatched recursor layout.
- At ι both sides select the same rule (same constructor index, or
  the same literal peel — the evaluator now carries the recursor's
  block identity precisely so the peels agree), the source enters the
  kernel-shaped lambda telescope (`applyMany_chain`), and the target
  evaluates the peeled body in the assembled rule environment;
  `fireSim` proves the two runs related.
- Configured opaque definitions and axioms lower to same-arity target
  externs. `papExtern` relates every under-saturated application prefix;
  exact saturation crosses the explicit per-address `OracleRelAt`
  hypothesis, which relates successful source-oracle calls to target-oracle
  results. `Covered` and the executable validator establish only the
  structural address/kind/arity correspondence: semantic oracle agreement
  remains a theorem premise supplied by the trusted ledger.

Mutual-member calls are closed by a finite simultaneous certificate:
`MemberScope.plan` names the admitted `(block, member)` keys and
`MemberCoverage` proves every unfoldable definition body or recursor rule set
against that same plan and pins configured opaque definitions to the exact
same synthetic member extern used by the source oracle. Public opaque `dPrj`
aliases use that identity directly. This admits genuinely cyclic non-self
definition and recursor `recur` heads (including indexed recursor spines)
without recursively nesting coverage proofs; non-self inductive heads retain
their direct structural clause. Still outside the core relation are
occurrences of variables bound in slots the executable eraser drops to `◻`. Raw
`.share` syntax deliberately remains outside `PErase`; the composition
theorems at the end of this file transport evaluation through full inlining
and then reuse the share-free relation unchanged.
That last case needs usage-checker soundness or a typed logical
relation: `EnvRel` deliberately leaves dropped slots unconstrained,
so a general `PErase.var` clause would be false. The differential
suite in `Erase.lean` witnesses the executable cases; this file is the
theorem catching up.

Higher-order or otherwise unknown application heads remain conservative:
without a visible declaration or recursor telescope the executable eraser
retains the argument, so no unchecked ghost-drop clause is needed.

Fuel handling is unchanged: strong induction on source fuel,
`IxIR0.eval_mono` to combine target sub-derivations.
-/

namespace Ix.Compiler.Sim

open Ix.Compiler.Ixon (Uses Owned Recursor RecursorRule MutConst Constant)

/-- Syntactic type-scheme test — share-free restriction of
`Erase.sortLike`. -/
def sortLikeP : Ixon.Expr → Bool
  | .sort _ => true
  | .all _ _ _ cod => sortLikeP cod
  | _ => false

/-- Is a binder with this mode and domain erased? Mirrors
`Erase.dropBinder` on the fragment. -/
def dropB (u : Uses) (dom : Ixon.Expr) : Bool :=
  u == .erased || sortLikeP dom

/-- Constructor identity resolved through the source context, including the
shared source parameter count and the runtime field count. -/
def CtorShape (ectx : Ixon.Eval.EvalCtx) (block : Ixon.Address)
    (indIdx cidx params fields : Nat) : Prop :=
  ∃ bc ind ct,
    Ixon.Eval.resolveMut ectx block indIdx = .ok (bc, .indc ind) ∧
    ind.ctors[cidx]? = some ct ∧
    ind.params.toNat = params ∧ ct.params.toNat = params ∧
    ct.fields.toNat = fields

/-- Every inductive member of a mutual block uses the recursor's parameter
count. Definitions and other recursors do not contribute constructor majors.
This is the finite table-layout fact that source typing normally implies. -/
inductive BlockParams (params : Nat) : List MutConst → Prop where
  | nil : BlockParams params []
  | defn {d rest} : BlockParams params rest →
      BlockParams params (.defn d :: rest)
  | recr {r rest} : BlockParams params rest →
      BlockParams params (.recr r :: rest)
  | indc {ind rest} : ind.params.toNat = params →
      BlockParams params rest → BlockParams params (.indc ind :: rest)

theorem BlockParams.lookup_indc {params : Nat} :
    ∀ {members : List MutConst}, BlockParams params members →
      ∀ {idx : Nat} {ind : Ix.Compiler.Ixon.Inductive},
        members[idx]? = some (MutConst.indc ind) →
        ind.params.toNat = params := by
  intro members h
  induction h with
  | nil => intro idx ind hget; simp at hget
  | defn hrest ih | recr hrest ih =>
    intro idx ind hget
    cases idx with
    | zero => simp at hget
    | succ idx =>
      simp only [List.getElem?_cons_succ] at hget
      exact ih hget
  | indc hparams hrest ih =>
    intro idx ind' hget
    cases idx with
    | zero =>
      simp only [List.getElem?_cons_zero] at hget
      injection hget with heq
      cases MutConst.indc.inj heq
      exact hparams
    | succ idx =>
      simp only [List.getElem?_cons_succ] at hget
      exact ih hget

/-- Peel exactly `n` lambdas (share-free — the kernel-rule chains the
relation covers are literal). -/
def peelChain : Nat → Ixon.Expr → Option Ixon.Expr
  | 0, e => some e
  | n + 1, .lam _ _ b => peelChain n b
  | _ + 1, _ => none

/-- Runtime policies for the first `params` binders of a recursor type.
Share-free all-binders use the same keep/ghost test as expression erasure;
a short or non-telescope type is conservatively padded with `keep`, matching
the executable eraser's fallback. -/
def recParamPolicy : Nat → Ixon.Expr → List Erase.ArgPolicy
  | 0, _ => []
  | params + 1, .all u _ dom cod =>
      (if dropB u dom then .ghost else .keep) :: recParamPolicy params cod
  | params + 1, _ => List.replicate (params + 1) .keep

/-- Policies for the source arguments passed to a recursor rule: parameters,
ghost motives, then kept minors. -/
def recRulePolicy (r : Recursor) : List Erase.ArgPolicy :=
  recParamPolicy r.params.toNat r.typ ++
    List.replicate r.motives.toNat .ghost ++
    List.replicate r.minors.toNat .keep

/-- Complete pre-major policy, adding source-only indices. -/
def recPolicy (r : Recursor) : List Erase.ArgPolicy :=
  recRulePolicy r ++ List.replicate r.indices.toNat .drop

def policyKept : Erase.ArgPolicy → Bool
  | .keep => true
  | .ghost | .drop => false

/-- A policy list with target slots at every position. Recursor rule
arguments have this shape; source-only drops occur only in the later index
segment. -/
inductive SlotPolicies : List Erase.ArgPolicy → Prop where
  | nil : SlotPolicies []
  | keep {rest} : SlotPolicies rest → SlotPolicies (.keep :: rest)
  | ghost {rest} : SlotPolicies rest → SlotPolicies (.ghost :: rest)

namespace SlotPolicies

theorem append {left right : List Erase.ArgPolicy}
    (hl : SlotPolicies left) (hr : SlotPolicies right) :
    SlotPolicies (left ++ right) := by
  induction hl with
  | nil => exact hr
  | keep _ ih => exact .keep ih
  | ghost _ ih => exact .ghost ih

theorem replicate_keep (n : Nat) :
    SlotPolicies (List.replicate n .keep) := by
  induction n with
  | zero => exact .nil
  | succ n ih => simpa [List.replicate_succ] using SlotPolicies.keep ih

theorem replicate_ghost (n : Nat) :
    SlotPolicies (List.replicate n .ghost) := by
  induction n with
  | zero => exact .nil
  | succ n ih => simpa [List.replicate_succ] using SlotPolicies.ghost ih

theorem targetArity_eq_length {policies : List Erase.ArgPolicy}
    (h : SlotPolicies policies) :
    policyTargetArity policies = policies.length := by
  induction h <;> simp_all [policyTargetArity]

theorem dropN {policies : List Erase.ArgPolicy}
    (h : SlotPolicies policies) (n : Nat) :
    SlotPolicies (policies.drop n) := by
  induction n generalizing policies with
  | zero => simpa using h
  | succ n ih =>
    cases h with
    | nil => exact .nil
    | keep hrest => exact ih hrest
    | ghost hrest => exact ih hrest

end SlotPolicies

/-- Rule environments are innermost-first: fields, minors, motives, then the
reversed parameter policy. -/
def recRuleMask (r : Recursor) (fields : Nat) : List Bool :=
  List.replicate fields true ++ ((recRulePolicy r).map policyKept).reverse

@[simp] theorem recParamPolicy_length (params : Nat) (typ : Ixon.Expr) :
    (recParamPolicy params typ).length = params := by
  induction params generalizing typ with
  | zero => rfl
  | succ params ih =>
    cases typ <;> simp [recParamPolicy, ih]

theorem recParamPolicy_slots (params : Nat) (typ : Ixon.Expr) :
    SlotPolicies (recParamPolicy params typ) := by
  induction params generalizing typ with
  | zero => exact .nil
  | succ params ih =>
    cases typ with
    | all u o dom cod =>
      simp only [recParamPolicy]
      split
      · exact .ghost (ih cod)
      · exact .keep (ih cod)
    | _ => exact SlotPolicies.replicate_keep (params + 1)

theorem recRulePolicy_slots (r : Recursor) :
    SlotPolicies (recRulePolicy r) := by
  simpa [recRulePolicy] using
    (recParamPolicy_slots r.params.toNat r.typ).append
      ((SlotPolicies.replicate_ghost r.motives.toNat).append
        (SlotPolicies.replicate_keep r.minors.toNat))

@[simp] theorem recRulePolicy_length (r : Recursor) :
    (recRulePolicy r).length =
      r.params.toNat + r.motives.toNat + r.minors.toNat := by
  simp [recRulePolicy]
  omega

@[simp] theorem recPolicy_length (r : Recursor) :
    (recPolicy r).length = Ixon.Eval.recArity r - 1 := by
  simp [recPolicy, Ixon.Eval.recArity]

@[simp] theorem recPolicy_length_exact (r : Recursor) :
    (recPolicy r).length = r.params.toNat + r.motives.toNat +
      r.minors.toNat + r.indices.toNat := by
  simp [recPolicy]

@[simp] theorem policyTargetArity_recParamPolicy
    (params : Nat) (typ : Ixon.Expr) :
    policyTargetArity (recParamPolicy params typ) = params := by
  calc
    policyTargetArity (recParamPolicy params typ) =
        (recParamPolicy params typ).length :=
      (recParamPolicy_slots params typ).targetArity_eq_length
    _ = params := recParamPolicy_length params typ

@[simp] theorem policyTargetArity_recRulePolicy (r : Recursor) :
    policyTargetArity (recRulePolicy r) =
      r.params.toNat + r.motives.toNat + r.minors.toNat := by
  simp [recRulePolicy]
  omega

@[simp] theorem policyTargetArity_recPolicy (r : Recursor) :
    policyTargetArity (recPolicy r) =
      r.params.toNat + r.motives.toNat + r.minors.toNat := by
  simp [recPolicy]

/-- An index-free recursor head. Heads resolve the way the evaluator resolves
them (through the refs table, or as the frame's own block member). -/
inductive RecPrefix (ectx : Ixon.Eval.EvalCtx) (refs : Array Ixon.Address)
    (muts : Array MutConst) (sa : Option Ixon.Address) :
    Ixon.Expr → Recursor → Prop where
  | refH {refIdx : UInt64} {u : Array UInt64} {a : Ixon.Address}
      {c : Constant} {p : Ix.Compiler.Ixon.RecursorProj} {bc : Constant}
      {r : Recursor} :
      refs[refIdx.toNat]? = some a →
      ectx.resolve a = some c →
      c.info = .rPrj p →
      Ixon.Eval.resolveMut ectx p.block p.idx.toNat = .ok (bc, .recr r) →
      r.indices.toNat = 0 →
      RecPrefix ectx refs muts sa (.ref refIdx u) r
  | recurH {recIdx : UInt64} {u : Array UInt64} {blk : Ixon.Address}
      {r : Recursor} :
      sa = some blk →
      muts[recIdx.toNat]? = some (.recr r) →
      r.indices.toNat = 0 →
      RecPrefix ectx refs muts sa (.recur recIdx u) r

/-- The spine form: a `RecPrefix` head under `j` applications, still before
the major and driven by `recRulePolicy`. -/
inductive RecSpine (ectx : Ixon.Eval.EvalCtx) (refs : Array Ixon.Address)
    (muts : Array MutConst) (sa : Option Ixon.Address) :
    Ixon.Expr → Recursor → Nat → Prop where
  | head {e r} : RecPrefix ectx refs muts sa e r →
      RecSpine ectx refs muts sa e r 0
  | step {f a r j} : RecSpine ectx refs muts sa f r j →
      j < (recRulePolicy r).length →
      RecSpine ectx refs muts sa (.app f a) r (j + 1)

/-- An unfoldable ordinary definition head followed through its literal
lambda telescope.  This witnesses the *implementation* binder reached by a
visible source application spine; the executable eraser's `headPolicies`
checks the declaration type independently.  Requiring both checks prevents
an ill-shaped type/value pair from justifying argument erasure. -/
inductive DefSpine (ectx : Ixon.Eval.EvalCtx)
    (refs : Array Ixon.Address) : Ixon.Expr → Ixon.Expr → Prop where
  | head {refIdx : UInt64} {univIdxs : Array UInt64}
      {address : Ixon.Address} {constant : Constant}
      {definition : Ix.Compiler.Ixon.Definition} :
      refs[refIdx.toNat]? = some address →
      ectx.resolve address = some constant →
      constant.info = .defn definition →
      Ixon.Eval.unfoldable definition = true →
      DefSpine ectx refs (.ref refIdx univIdxs) definition.value
  | step {function argument : Ixon.Expr} {uses : Uses}
      {domain body : Ixon.Expr} :
      DefSpine ectx refs function (.lam uses domain body) →
      DefSpine ectx refs (.app function argument) body

/-- A terminal type expression has no further arrow result and is not a
sharing indirection. -/
def resultTypeTerminal : Ixon.Expr → Bool
  | .all .. | .share .. => false
  | _ => true

/-- Fuel-free proof relation for the innermost result ownership of a
definition telescope.  Unlike `Erase.teleResultOwned`, cyclic sharing has no
derivation instead of acquiring a fuel-dependent default. -/
inductive TeleResultOwned (sharing : Array Ixon.Expr) :
    Ixon.Expr → Option Owned → Prop where
  | terminal {typ : Ixon.Expr} :
      resultTypeTerminal typ = true →
      TeleResultOwned sharing typ none
  | shareMissing {index : UInt64} :
      sharing[index.toNat]? = none →
      TeleResultOwned sharing (.share index) none
  | share {index : UInt64} {typ : Ixon.Expr} {result : Option Owned} :
      sharing[index.toNat]? = some typ →
      TeleResultOwned sharing typ result →
      TeleResultOwned sharing (.share index) result
  | allHere {uses : Uses} {result : Owned} {domain codomain : Ixon.Expr} :
      TeleResultOwned sharing codomain none →
      TeleResultOwned sharing (.all uses result domain codomain) (some result)
  | allInner {uses : Uses} {result inner : Owned}
      {domain codomain : Ixon.Expr} :
      TeleResultOwned sharing codomain (some inner) →
      TeleResultOwned sharing (.all uses result domain codomain) (some inner)

/-- The target declaration's result world is exactly the source telescope's
innermost result, defaulting a non-function to shared. -/
def DefinitionResultOwned (sharing : Array Ixon.Expr) (typ : Ixon.Expr)
    (result : Owned) : Prop :=
  ∃ candidate, TeleResultOwned sharing typ candidate ∧
    result = candidate.getD .shared

/-- A syntactically visible constructor head followed only by its dropped
parameter prefix.  The final index counts consumed source parameters; target
evaluation stutters throughout this spine. -/
inductive CtorParamSpine (ectx : Ixon.Eval.EvalCtx)
    (refs : Array Ixon.Address) : Ixon.Expr → Ixon.Address → Ixon.Address →
    Nat → Nat → Nat → Nat → Nat → Prop where
  | head {refIdx : UInt64} {univIdxs : Array UInt64}
      {a : Ixon.Address} {c : Constant}
      {p : Ix.Compiler.Ixon.ConstructorProj} {params fields : Nat} :
      refs[refIdx.toNat]? = some a →
      ectx.resolve a = some c →
      c.info = .cPrj p →
      CtorShape ectx p.block p.idx.toNat p.cidx.toNat params fields →
      CtorParamSpine ectx refs (.ref refIdx univIdxs) a p.block
        p.idx.toNat p.cidx.toNat params fields 0
  | step {f arg : Ixon.Expr} {a block : Ixon.Address}
      {indIdx cidx params fields consumed : Nat} :
      CtorParamSpine ectx refs f a block indIdx cidx params fields consumed →
      consumed < params →
      CtorParamSpine ectx refs (.app f arg) a block indIdx cidx params fields
        (consumed + 1)

/-- A member admitted through one simultaneous mutual-block certificate. -/
structure MemberKey where
  block : Ixon.Address
  idx : Nat
  deriving BEq, ReflBEq, LawfulBEq, DecidableEq, Repr

/-- The finite set of mutual members whose bodies may refer to one another.
The default scope is empty, preserving the closed relation used by existing
clients. -/
class MemberScope where
  plan : List MemberKey

/-- Existing certificates do not admit open mutual-member calls. A local
instance with a nonempty plan opts a validator run into simultaneous
certification. -/
instance (priority := low) defaultMemberScope : MemberScope where
  plan := []

section MemberScoped

variable [scope : MemberScope]

mutual
  /-- Relational erasure, read against a frame's tables. The mask
  records, per context slot, whether the binder was kept; `sc` names
  the recursor whose rule body is being related (its `recur` maps to
  the recSelf slot just below the mask). -/
  inductive PErase : Ixon.Eval.EvalCtx → IxIR0.Ctx →
      Option (Ixon.Address × Nat) → Array Ixon.Address →
      Array MutConst → Option Ixon.Address →
      List Bool → Ixon.Expr → IxIR0.Expr → Prop where
    | var {ectx ictx sc refs muts sa} {mask : List Bool} {i : UInt64} :
        mask[i.toNat]? = some true →
        PErase ectx ictx sc refs muts sa mask (.var i) (.var i.toNat)
    | sortE {ectx ictx sc refs muts sa} {mask : List Bool} {u : UInt64} :
        PErase ectx ictx sc refs muts sa mask (.sort u) .erased
    | allE {ectx ictx sc refs muts sa} {mask : List Bool} {u : Uses}
        {o : Ix.Compiler.Ixon.Owned} {dom cod : Ixon.Expr} :
        PErase ectx ictx sc refs muts sa mask (.all u o dom cod) .erased
    | lamK {ectx ictx sc refs muts sa} {mask : List Bool} {u : Uses}
        {dom body : Ixon.Expr} {body' : IxIR0.Expr} :
        dropB u dom = false →
        PErase ectx ictx sc refs muts sa (true :: mask) body body' →
        PErase ectx ictx sc refs muts sa mask (.lam u dom body)
          (.lam u body')
    | lamD {ectx ictx sc refs muts sa} {mask : List Bool} {u : Uses}
        {dom body : Ixon.Expr} {body' : IxIR0.Expr} :
        dropB u dom = true →
        PErase ectx ictx sc refs muts sa (false :: mask) body body' →
        PErase ectx ictx sc refs muts sa mask (.lam u dom body)
          (.lam .many body')
    | app {ectx ictx sc refs muts sa} {mask : List Bool} {f a : Ixon.Expr}
        {f' a' : IxIR0.Expr} :
        PErase ectx ictx sc refs muts sa mask f f' →
        PErase ectx ictx sc refs muts sa mask a a' →
        PErase ectx ictx sc refs muts sa mask (.app f a) (.app f' a')
    | appE {ectx ictx sc refs muts sa} {mask : List Bool} {u : Uses}
        {dom body a : Ixon.Expr} {f' : IxIR0.Expr} :
        dropB u dom = true →
        PErase ectx ictx sc refs muts sa mask (.lam u dom body) f' →
        PErase ectx ictx sc refs muts sa mask (.app (.lam u dom body) a)
          (.app f' .erased)
    | appG {ectx ictx sc refs muts sa} {mask : List Bool}
        {f a : Ixon.Expr} {f' : IxIR0.Expr} {r : Recursor} {j : Nat} :
        RecSpine ectx refs muts sa f r j →
        (recRulePolicy r)[j]? = some .ghost →
        PErase ectx ictx sc refs muts sa mask f f' →
        PErase ectx ictx sc refs muts sa mask (.app f a)
          (.app f' .erased)
    | appDG {ectx ictx sc refs muts sa} {mask : List Bool}
        {f a : Ixon.Expr} {f' : IxIR0.Expr} {uses : Uses}
        {domain body : Ixon.Expr} :
        DefSpine ectx refs f (.lam uses domain body) →
        dropB uses domain = true →
        PErase ectx ictx sc refs muts sa mask f f' →
        PErase ectx ictx sc refs muts sa mask (.app f a)
          (.app f' .erased)
    | recP {ectx ictx sc refs muts sa} {mask : List Bool}
        {e : Ixon.Expr} {e' : IxIR0.Expr} {r : Recursor} :
        RecEraseSpine ectx ictx sc refs muts sa mask e e' r [] →
        PErase ectx ictx sc refs muts sa mask e e'
    | recW {ectx ictx sc refs muts sa} {mask : List Bool}
        {e : Ixon.Expr} {e' : IxIR0.Expr} {r : Recursor}
        {remaining : Nat} :
        RecEraseSpine ectx ictx sc refs muts sa mask e e' r
          (List.replicate remaining .drop) →
        0 < remaining →
        PErase ectx ictx sc refs muts sa mask e
          (Erase.captureThenIgnoreN remaining e')
    | letE {ectx ictx sc refs muts sa} {mask : List Bool} {nd : Bool}
        {ty val body : Ixon.Expr} {val' body' : IxIR0.Expr} :
        PErase ectx ictx sc refs muts sa mask val val' →
        PErase ectx ictx sc refs muts sa (true :: mask) body body' →
        PErase ectx ictx sc refs muts sa mask (.letE nd ty val body)
          (.letE .many val' body')
    | ctorP {ectx ictx sc refs muts sa} {mask : List Bool}
        {e : Ixon.Expr} {a block : Ixon.Address}
        {indIdx cidx params fields : Nat} :
        0 < params →
        CtorParamSpine ectx refs e a block indIdx cidx params fields params →
        ictx.env a = some (.ctor cidx fields) →
        PErase ectx ictx sc refs muts sa mask e (.ref a)
    | ctorW {ectx ictx sc refs muts sa} {mask : List Bool}
        {e : Ixon.Expr} {a block : Ixon.Address}
        {indIdx cidx params fields consumed : Nat} :
        CtorParamSpine ectx refs e a block indIdx cidx params fields consumed →
        consumed < params →
        ictx.env a = some (.ctor cidx fields) →
        PErase ectx ictx sc refs muts sa mask e
          (.lam .many
            (Erase.lamManyN (params - consumed - 1) (.ref a)))
    | ref {ectx ictx sc refs muts sa} {mask : List Bool} {refIdx : UInt64}
        {univIdxs : Array UInt64} {a : Ixon.Address} :
        refs[refIdx.toNat]? = some a →
        Covered ectx ictx a →
        PErase ectx ictx sc refs muts sa mask (.ref refIdx univIdxs)
          (.ref a)
    | recurS {ectx ictx refs muts sa} {mask : List Bool}
        {block : Ixon.Address} {idx : Nat} {recIdx : UInt64}
        {univIdxs : Array UInt64} :
        recIdx.toNat = idx →
        (∀ r, muts[recIdx.toNat]? = some (.recr r) →
          r.indices.toNat = 0) →
        PErase ectx ictx (some (block, idx)) refs muts sa mask
          (.recur recIdx univIdxs) (.var mask.length)
    | recurI {ectx ictx sc refs muts sa} {mask : List Bool}
        {block : Ixon.Address} {recIdx : UInt64}
        {univIdxs : Array UInt64} {bc : Constant}
        {ind : Ix.Compiler.Ixon.Inductive} :
        sa = some block →
        Ixon.Eval.resolveMut ectx block recIdx.toNat =
          .ok (bc, .indc ind) →
        refs = bc.refs →
        muts[recIdx.toNat]? = some (.indc ind) →
        ictx.env (Erase.memberAddr block recIdx.toNat) =
          some (.defn .shared .erased) →
        PErase ectx ictx sc refs muts sa mask (.recur recIdx univIdxs)
          (.ref (Erase.memberAddr block recIdx.toNat))
    | recurD {ectx ictx sc refs muts sa} {mask : List Bool}
        {block : Ixon.Address} {recIdx : UInt64}
        {univIdxs : Array UInt64} {bc : Constant}
        {d : Ix.Compiler.Ixon.Definition} :
        sa = some block →
        Ixon.Eval.resolveMut ectx block recIdx.toNat =
          .ok (bc, .defn d) →
        refs = bc.refs →
        muts = Ixon.selfMutsOf bc.info →
        Ixon.Eval.unfoldable d = true →
        ⟨block, recIdx.toNat⟩ ∈ scope.plan →
        PErase ectx ictx sc refs muts sa mask (.recur recIdx univIdxs)
          (.ref (Erase.memberAddr block recIdx.toNat))
    | recurO {ectx ictx sc refs muts sa} {mask : List Bool}
        {block : Ixon.Address} {recIdx : UInt64}
        {univIdxs : Array UInt64} {bc : Constant}
        {d : Ix.Compiler.Ixon.Definition} {arity : Nat} :
        sa = some block →
        Ixon.Eval.resolveMut ectx block recIdx.toNat =
          .ok (bc, .defn d) →
        refs = bc.refs →
        muts = Ixon.selfMutsOf bc.info →
        Ixon.Eval.unfoldable d = false →
        ectx.externArity (Erase.memberAddr block recIdx.toNat) =
          some arity →
        ⟨block, recIdx.toNat⟩ ∈ scope.plan →
        PErase ectx ictx sc refs muts sa mask (.recur recIdx univIdxs)
          (.ref (Erase.memberAddr block recIdx.toNat))
    | recurR {ectx ictx sc refs muts sa} {mask : List Bool}
        {block : Ixon.Address} {recIdx : UInt64}
        {univIdxs : Array UInt64} {bc : Constant} {r : Recursor} :
        sa = some block →
        Ixon.Eval.resolveMut ectx block recIdx.toNat =
          .ok (bc, .recr r) →
        refs = bc.refs →
        muts = Ixon.selfMutsOf bc.info →
        r.indices.toNat = 0 →
        ⟨block, recIdx.toNat⟩ ∈ scope.plan →
        PErase ectx ictx sc refs muts sa mask (.recur recIdx univIdxs)
          (.ref (Erase.memberAddr block recIdx.toNat))
    | natE {ectx ictx sc refs muts sa} {mask : List Bool} {idx : UInt64}
        {a : Ixon.Address} {n : Nat} :
        refs[idx.toNat]? = some a →
        ectx.blobs a = some (.natB n) →
        PErase ectx ictx sc refs muts sa mask (.nat idx) (.lit (.nat n))
    | strE {ectx ictx sc refs muts sa} {mask : List Bool} {idx : UInt64}
        {a : Ixon.Address} {s : String} :
        refs[idx.toNat]? = some a →
        ectx.blobs a = some (.strB s) →
        PErase ectx ictx sc refs muts sa mask (.str idx) (.lit (.str s))
    | prjE {ectx ictx sc refs muts sa} {mask : List Bool}
        {tyRef fieldIdx : UInt64} {val : Ixon.Expr} {val' : IxIR0.Expr} :
        PErase ectx ictx sc refs muts sa mask val val' →
        PErase ectx ictx sc refs muts sa mask (.prj tyRef fieldIdx val)
          (.proj fieldIdx.toNat val')

  /-- Exact erasure of a fully supplied, syntactically visible indexed
  recursor spine. The global value relation sees only the final pre-major pap;
  intermediate paps with a pending source-only index are deliberately not
  exposed, because generic target application would otherwise fire early. -/
  inductive RecEraseSpine : Ixon.Eval.EvalCtx → IxIR0.Ctx →
      Option (Ixon.Address × Nat) → Array Ixon.Address →
      Array MutConst → Option Ixon.Address → List Bool →
      Ixon.Expr → IxIR0.Expr → Recursor → List Erase.ArgPolicy → Prop where
    | head {ectx ictx sc refs muts sa} {mask : List Bool}
        {refIdx : UInt64} {univIdxs : Array UInt64} {a : Ixon.Address}
        {c : Constant} {p : Ix.Compiler.Ixon.RecursorProj}
        {bc : Constant} {r : Recursor} :
        refs[refIdx.toNat]? = some a →
        ectx.resolve a = some c →
        c.info = .rPrj p →
        Ixon.Eval.resolveMut ectx p.block p.idx.toNat = .ok (bc, .recr r) →
        0 < r.indices.toNat →
        ictx.env a = some (.defn .shared (.ref
          (Erase.memberAddr p.block p.idx.toNat))) →
        RecMember ectx ictx p.block p.idx.toNat r →
        RecEraseSpine ectx ictx sc refs muts sa mask
          (.ref refIdx univIdxs) (.ref a) r (recPolicy r)
    | selfHead {ectx ictx sc refs muts sa} {mask : List Bool}
        {block : Ixon.Address} {idx : Nat} {recIdx : UInt64}
        {univIdxs : Array UInt64} {bc : Constant} {r : Recursor} :
        sc = some (block, idx) →
        sa = some block →
        recIdx.toNat = idx →
        Ixon.Eval.resolveMut ectx block idx = .ok (bc, .recr r) →
        refs = bc.refs →
        muts[recIdx.toNat]? = some (.recr r) →
        0 < r.indices.toNat →
        RecEraseSpine ectx ictx sc refs muts sa mask
          (.recur recIdx univIdxs) (.var mask.length) r (recPolicy r)
    | memberHead {ectx ictx sc refs muts sa} {mask : List Bool}
        {block : Ixon.Address} {recIdx : UInt64}
        {univIdxs : Array UInt64} {bc : Constant} {r : Recursor} :
        sa = some block →
        Ixon.Eval.resolveMut ectx block recIdx.toNat =
          .ok (bc, .recr r) →
        refs = bc.refs →
        muts = Ixon.selfMutsOf bc.info →
        0 < r.indices.toNat →
        ⟨block, recIdx.toNat⟩ ∈ scope.plan →
        RecEraseSpine ectx ictx sc refs muts sa mask
          (.recur recIdx univIdxs)
          (.ref (Erase.memberAddr block recIdx.toNat)) r (recPolicy r)
    | keep {ectx ictx sc refs muts sa} {mask : List Bool}
        {f a : Ixon.Expr} {f' a' : IxIR0.Expr} {r : Recursor}
        {rest : List Erase.ArgPolicy} :
        RecEraseSpine ectx ictx sc refs muts sa mask f f' r
          (.keep :: rest) →
        PErase ectx ictx sc refs muts sa mask a a' →
        RecEraseSpine ectx ictx sc refs muts sa mask
          (.app f a) (.app f' a') r rest
    | ghost {ectx ictx sc refs muts sa} {mask : List Bool}
        {f a : Ixon.Expr} {f' : IxIR0.Expr} {r : Recursor}
        {rest : List Erase.ArgPolicy} :
        RecEraseSpine ectx ictx sc refs muts sa mask f f' r
          (.ghost :: rest) →
        RecEraseSpine ectx ictx sc refs muts sa mask
          (.app f a) (.app f' .erased) r rest
    | drop {ectx ictx sc refs muts sa} {mask : List Bool}
        {f a : Ixon.Expr} {f' : IxIR0.Expr} {r : Recursor}
        {rest : List Erase.ArgPolicy} :
        RecEraseSpine ectx ictx sc refs muts sa mask f f' r
          (.drop :: rest) →
        RecEraseSpine ectx ictx sc refs muts sa mask (.app f a) f' r rest

  /-- The program correspondence at one address. -/
  inductive Covered : Ixon.Eval.EvalCtx → IxIR0.Ctx →
      Ixon.Address → Prop where
    | defn {ectx ictx} {a : Ixon.Address} {c : Constant}
        {d : Ix.Compiler.Ixon.Definition} {result : Owned}
        {body' : IxIR0.Expr} :
        ectx.resolve a = some c →
        c.info = .defn d →
        Ixon.Eval.unfoldable d = true →
        ictx.env a = some (.defn result body') →
        DefinitionResultOwned c.sharing d.typ result →
        PErase ectx ictx none c.refs (Ixon.selfMutsOf c.info) none
          [] d.value body' →
        Covered ectx ictx a
    | defnProj {ectx ictx} {a : Ixon.Address} {c bc : Constant}
        {p : Ix.Compiler.Ixon.DefinitionProj}
        {d : Ix.Compiler.Ixon.Definition} {result : Owned}
        {body' : IxIR0.Expr} :
        ectx.resolve a = some c →
        c.info = .dPrj p →
        Ixon.Eval.resolveMut ectx p.block p.idx.toNat = .ok (bc, .defn d) →
        Ixon.Eval.unfoldable d = true →
        ictx.env a = some (.defn result
          (.ref (Erase.memberAddr p.block p.idx.toNat))) →
        ictx.env (Erase.memberAddr p.block p.idx.toNat) =
          some (.defn result body') →
        DefinitionResultOwned bc.sharing d.typ result →
        PErase ectx ictx none bc.refs (Ixon.selfMutsOf bc.info)
          (some p.block) [] d.value body' →
        Covered ectx ictx a
    | externDefn {ectx ictx} {a : Ixon.Address} {c : Constant}
        {d : Ix.Compiler.Ixon.Definition} {arity : Nat} :
        ectx.resolve a = some c →
        c.info = .defn d →
        Ixon.Eval.unfoldable d = false →
        ectx.externArity a = some arity →
        ictx.env a = some (.extern arity) →
        Covered ectx ictx a
    | externDefnProj {ectx ictx} {a : Ixon.Address} {c bc : Constant}
        {p : Ix.Compiler.Ixon.DefinitionProj}
        {d : Ix.Compiler.Ixon.Definition} {result : Owned} {arity : Nat} :
        ectx.resolve a = some c →
        c.info = .dPrj p →
        Ixon.Eval.resolveMut ectx p.block p.idx.toNat = .ok (bc, .defn d) →
        Ixon.Eval.unfoldable d = false →
        ectx.externArity (Erase.memberAddr p.block p.idx.toNat) =
          some arity →
        ictx.env a = some (.defn result
          (.ref (Erase.memberAddr p.block p.idx.toNat))) →
        ictx.env (Erase.memberAddr p.block p.idx.toNat) =
          some (.extern arity) →
        DefinitionResultOwned bc.sharing d.typ result →
        Covered ectx ictx a
    | externAxio {ectx ictx} {a : Ixon.Address} {c : Constant}
        {ax : Ix.Compiler.Ixon.Axiom} {arity : Nat} :
        ectx.resolve a = some c →
        c.info = .axio ax →
        ectx.externArity a = some arity →
        ictx.env a = some (.extern arity) →
        Covered ectx ictx a
    | ctor {ectx ictx} {a : Ixon.Address} {c : Constant}
        {p : Ix.Compiler.Ixon.ConstructorProj} {fields : Nat} :
        ectx.resolve a = some c →
        c.info = .cPrj p →
        CtorShape ectx p.block p.idx.toNat p.cidx.toNat 0 fields →
        ictx.env a = some (.ctor p.cidx.toNat fields) →
        Covered ectx ictx a
    | tyf {ectx ictx} {a : Ixon.Address} {c : Constant}
        {p : Ix.Compiler.Ixon.InductiveProj} :
        ectx.resolve a = some c →
        c.info = .iPrj p →
        ictx.env a = some (.defn .shared .erased) →
        Covered ectx ictx a
    | quot {ectx ictx} {a : Ixon.Address} {c : Constant}
        {q : Ix.Compiler.Ixon.Quotient} {result : Owned} :
        ectx.resolve a = some c →
        c.info = .quot q →
        ectx.quotientKind a = some q.kind →
        ictx.env a = some (.defn result (Erase.quotientBody q.kind)) →
        DefinitionResultOwned c.sharing q.typ result →
        Covered ectx ictx a
    | recrP {ectx ictx} {a : Ixon.Address} {c : Constant}
        {p : Ix.Compiler.Ixon.RecursorProj} {bc : Constant} {r : Recursor} :
        ectx.resolve a = some c →
        c.info = .rPrj p →
        Ixon.Eval.resolveMut ectx p.block p.idx.toNat = .ok (bc, .recr r) →
        r.indices.toNat = 0 →
        ictx.env a = some (.defn .shared (.ref
          (Erase.memberAddr p.block p.idx.toNat))) →
        RecMember ectx ictx p.block p.idx.toNat r →
        Covered ectx ictx a

  /-- Per-recursor program correspondence: resolution, the erased
  declaration at the member address (arity `params + motives + minors`,
  `natLit` by the same block-identity comparison the evaluator peels
  on), and related rules. Source-only indices are handled by the enclosing
  complete-spine relation rather than the rule environment. -/
  inductive RecMember : Ixon.Eval.EvalCtx → IxIR0.Ctx → Ixon.Address →
      Nat → Recursor → Prop where
    | mk {ectx ictx} {block : Ixon.Address} {idx : Nat} {r : Recursor}
        {bc : Constant} {trules : Array IxIR0.RecRule} :
        Ixon.Eval.resolveMut ectx block idx = .ok (bc, .recr r) →
        BlockParams r.params.toNat
          (Ixon.selfMutsOf bc.info).toList →
        ictx.env (Erase.memberAddr block idx) =
          some (.recursor
            (r.params.toNat + r.motives.toNat + r.minors.toNat)
            (ectx.natBlock == some block) trules) →
        RulesRel ectx ictx block idx r bc.refs
          (Ixon.selfMutsOf bc.info) r.rules.toList trules.toList →
        RecMember ectx ictx block idx r

  /-- Pointwise rule correspondence: field counts agree and the peeled
  source body relates to the erased rhs under the rule mask, in
  self-context. -/
  inductive RulesRel : Ixon.Eval.EvalCtx → IxIR0.Ctx → Ixon.Address →
      Nat → Recursor → Array Ixon.Address → Array MutConst →
      List RecursorRule → List IxIR0.RecRule → Prop where
    | nil {ectx ictx block idx r refs muts} :
        RulesRel ectx ictx block idx r refs muts [] []
    | cons {ectx ictx block idx r refs muts}
        {rule : RecursorRule} {trule : IxIR0.RecRule}
        {rest : List RecursorRule} {trest : List IxIR0.RecRule}
        {B : Ixon.Expr} :
        trule.fields = rule.fields.toNat →
        peelChain (r.params.toNat + r.motives.toNat + r.minors.toNat +
          rule.fields.toNat)
          rule.rhs = some B →
        PErase ectx ictx (some (block, idx)) refs muts (some block)
          (recRuleMask r rule.fields.toNat)
          B trule.rhs →
        RulesRel ectx ictx block idx r refs muts rest trest →
        RulesRel ectx ictx block idx r refs muts (rule :: rest)
          (trule :: trest)
end

/-- Full correspondence for one member named by a simultaneous certificate.
Definition and recursor bodies may themselves use member holes from the same
`MemberScope`, which makes genuinely cyclic blocks finitely representable. -/
inductive MemberRel (ectx : Ixon.Eval.EvalCtx) (ictx : IxIR0.Ctx) :
    MemberKey → Prop where
  | defn {block : Ixon.Address} {idx : Nat} {bc : Constant}
      {d : Ix.Compiler.Ixon.Definition} {result : Owned}
      {body' : IxIR0.Expr} :
      Ixon.Eval.resolveMut ectx block idx = .ok (bc, .defn d) →
      Ixon.Eval.unfoldable d = true →
      ictx.env (Erase.memberAddr block idx) =
        some (.defn result body') →
      DefinitionResultOwned bc.sharing d.typ result →
      PErase ectx ictx none bc.refs (Ixon.selfMutsOf bc.info)
        (some block) [] d.value body' →
      MemberRel ectx ictx ⟨block, idx⟩
  | externDefn {block : Ixon.Address} {idx : Nat} {bc : Constant}
      {d : Ix.Compiler.Ixon.Definition} {arity : Nat} :
      Ixon.Eval.resolveMut ectx block idx = .ok (bc, .defn d) →
      Ixon.Eval.unfoldable d = false →
      ectx.externArity (Erase.memberAddr block idx) = some arity →
      ictx.env (Erase.memberAddr block idx) = some (.extern arity) →
      MemberRel ectx ictx ⟨block, idx⟩
  | recr {block : Ixon.Address} {idx : Nat} {r : Recursor} :
      RecMember ectx ictx block idx r →
      MemberRel ectx ictx ⟨block, idx⟩

/-- A finite, simultaneous proof for every key in a member plan. Recursive
references inside its entries point only to keys, never to nested copies of
the entries themselves. -/
inductive MemberCoverage (ectx : Ixon.Eval.EvalCtx) (ictx : IxIR0.Ctx) :
    List MemberKey → Prop where
  | nil : ectx.Strict →
      MemberCoverage ectx ictx []
  | cons {key : MemberKey} {rest : List MemberKey} :
      MemberRel ectx ictx key →
      MemberCoverage ectx ictx rest →
      MemberCoverage ectx ictx (key :: rest)

namespace MemberCoverage

theorem strict {ectx : Ixon.Eval.EvalCtx} {ictx : IxIR0.Ctx}
    {keys : List MemberKey} (coverage : MemberCoverage ectx ictx keys) :
    ectx.Strict := by
  induction coverage with
  | nil hstrict => exact hstrict
  | cons _ _ ih => exact ih

theorem lookup {ectx : Ixon.Eval.EvalCtx} {ictx : IxIR0.Ctx}
    {keys : List MemberKey} (coverage : MemberCoverage ectx ictx keys) :
    ∀ {key : MemberKey}, key ∈ keys → MemberRel ectx ictx key := by
  intro key hmem
  induction coverage with
  | nil _ => simp at hmem
  | @cons head rest hhead hrest ih =>
    simp only [List.mem_cons] at hmem
    cases hmem with
    | inl heq => cases heq; exact hhead
    | inr htail => exact ih htail

end MemberCoverage

namespace RecMember

theorem resolve {ectx : Ixon.Eval.EvalCtx} {ictx : IxIR0.Ctx}
    {block : Ixon.Address} {idx : Nat} {r : Recursor}
    (h : RecMember ectx ictx block idx r) :
    ∃ bc, Ixon.Eval.resolveMut ectx block idx = .ok (bc, .recr r) := by
  cases h with
  | mk hresolve _ _ _ => exact ⟨_, hresolve⟩

theorem target {ectx : Ixon.Eval.EvalCtx} {ictx : IxIR0.Ctx}
    {block : Ixon.Address} {idx : Nat} {r : Recursor}
    (h : RecMember ectx ictx block idx r) :
    ∃ trules, ictx.env (Erase.memberAddr block idx) =
      some (.recursor
        (r.params.toNat + r.motives.toNat + r.minors.toNat)
        (ectx.natBlock == some block) trules) := by
  cases h with
  | mk _ _ htarget _ => exact ⟨_, htarget⟩

end RecMember

/-- The executable eraser's constructor-address convention. Erasure emits
`Decl.ctor` only for constructor-projection constants, registered at the
projection constant's own address (`Erase.eraseConstant`, `.cPrj` case),
and the target evaluator stamps constructor values with the environment
key whose head it fired (`IxIR0.eval` at `.ref` / `IxIR0.fire`). A target
constructor address is therefore pinned to the source family: it must
resolve, in the **source** context, to a projection of exactly this block,
inductive, and constructor index. Without this premise `ValRel` would
relate same-index constructors of different inductive families, letting a
wrong-family eraser bug satisfy `erasure_sim`. -/
def CtorAddr (ectx : Ixon.Eval.EvalCtx) (a block : Ixon.Address)
    (indIdx cidx : Nat) : Prop :=
  ∃ c p, ectx.resolve a = some c ∧ c.info = .cPrj p ∧
    p.block = block ∧ p.idx.toNat = indIdx ∧ p.cidx.toNat = cidx

mutual
  /-- Source and target values related by erasure. -/
  inductive ValRel : Ixon.Eval.EvalCtx → IxIR0.Ctx →
      Ixon.Eval.Value → IxIR0.Value → Prop where
    | sort {ectx ictx l} : ValRel ectx ictx (.sortV l) .erased
    | pi {ectx ictx u o F env dom cod} :
        ValRel ectx ictx (.piV u o F env dom cod) .erased
    | clos {ectx ictx sc} {mask : List Bool} {b : Bool} {u : Uses}
        {F : Ixon.Eval.Frame} {env : List Ixon.Eval.Value}
        {dom body : Ixon.Expr} {u' : Uses} {ρ : List IxIR0.Value}
        {body' : IxIR0.Expr} :
        b = !dropB u dom →
        EnvRel ectx ictx sc F.refs F.selfMuts F.selfAddr mask env ρ →
        PErase ectx ictx sc F.refs F.selfMuts F.selfAddr (b :: mask)
          body body' →
        ValRel ectx ictx (.closV u F env dom body) (.clos u' ρ body')
    | litNat {ectx ictx} {n : Nat} :
        ValRel ectx ictx (.litV (.natL n)) (.lit (.nat n))
    | litStr {ectx ictx} {s : String} :
        ValRel ectx ictx (.litV (.strL s)) (.lit (.str s))
    | quotV {ectx ictx} {address : Ixon.Address}
        {representative : Ixon.Eval.Value} {target : IxIR0.Value} :
        ValRel ectx ictx representative target →
        ValRel ectx ictx (.quotV address representative) target
    | quotType {ectx ictx} {address : Ixon.Address}
        {args : List Ixon.Eval.Value} :
        ValRel ectx ictx (.papV (.quotH address .type) args) .erased
    | papQuot {ectx ictx} {address : Ixon.Address}
        {kind : Ix.Compiler.Ixon.QuotKind}
        {sourceArgs : List Ixon.Eval.Value}
        {targetArgs : List IxIR0.Value} :
        kind ≠ .type →
        sourceArgs.length < Ixon.Eval.quotArity kind →
        ValsRel ectx ictx sourceArgs targetArgs →
        ValRel ectx ictx (.papV (.quotH address kind) sourceArgs)
          (.clos .many targetArgs.reverse
            (Erase.lamManyN
              (Ixon.Eval.quotArity kind - sourceArgs.length - 1)
              (Erase.quotientCore kind)))
    | papExtern {ectx ictx} {address : Ixon.Address} {arity : Nat}
        {sourceArgs : List Ixon.Eval.Value}
        {targetArgs : List IxIR0.Value} :
        ectx.externArity address = some arity →
        sourceArgs.length < arity →
        ValsRel ectx ictx sourceArgs targetArgs →
        ValRel ectx ictx (.papV (.extH address arity) sourceArgs)
          (.pap (.ext address arity) targetArgs)
    | ctorV {ectx ictx} {block : Ixon.Address}
        {indIdx cidx params fields : Nat}
        {cargs : List Ixon.Eval.Value} {a : Ixon.Address}
        {fargs : List IxIR0.Value} :
        CtorShape ectx block indIdx cidx params fields →
        CtorAddr ectx a block indIdx cidx →
        ValsRel ectx ictx (cargs.drop params) fargs →
        PolicyRel (fun _ _ => True) .erased (ctorPolicy params fields)
          cargs fargs →
        ValRel ectx ictx (.ctorV block indIdx cidx cargs)
          (.ctor a cidx fargs)
    | papCtor {ectx ictx} {block : Ixon.Address}
        {indIdx cidx params fields arity tarity : Nat}
        {sargs : List Ixon.Eval.Value} {a : Ixon.Address}
        {targs : List IxIR0.Value} :
        CtorShape ectx block indIdx cidx params fields →
        CtorAddr ectx a block indIdx cidx →
        arity = params + fields → tarity = fields →
        params ≤ sargs.length →
        sargs.length < arity →
        ValsRel ectx ictx (sargs.drop params) targs →
        PolicyPrefix (fun _ _ => True) .erased (ctorPolicy params fields)
          sargs targs
            (List.replicate (params + fields - sargs.length) .keep) →
        ValRel ectx ictx (.papV (.ctorH block indIdx cidx arity) sargs)
          (.pap (.ctor a cidx tarity) targs)
    | papCtorParams {ectx ictx} {block : Ixon.Address}
        {indIdx cidx params fields arity : Nat}
        {sargs : List Ixon.Eval.Value} {a : Ixon.Address}
        {targetEnv : List IxIR0.Value} :
        CtorShape ectx block indIdx cidx params fields →
        CtorAddr ectx a block indIdx cidx →
        ictx.env a = some (.ctor cidx fields) →
        arity = params + fields →
        sargs.length < params →
        ValRel ectx ictx (.papV (.ctorH block indIdx cidx arity) sargs)
          (.clos .many targetEnv
            (Erase.lamManyN (params - sargs.length - 1) (.ref a)))
    | papRec {ectx ictx} {block : Ixon.Address} {idx : Nat}
        {r : Recursor} {F : Ixon.Eval.Frame} {bc : Constant}
        {sargs : List Ixon.Eval.Value} {targs : List IxIR0.Value}
        {rest : List Erase.ArgPolicy} :
        ectx.resolve block = some bc →
        F.refs = bc.refs →
        F.selfMuts = Ixon.selfMutsOf bc.info →
        F.selfAddr = some block →
        RecMember ectx ictx block idx r →
        r.indices.toNat = 0 →
        sargs.length = targs.length →
        sargs.length ≤ (recRulePolicy r).length →
        RuntimePolicyPrefix (ValRel ectx ictx) (recRulePolicy r)
          sargs targs rest →
        ValRel ectx ictx (.papV (.recH (some block) r F) sargs)
          (.pap (.rec_ (Erase.memberAddr block idx)
            (r.params.toNat + r.motives.toNat + r.minors.toNat + 1)) targs)
    | papRecI {ectx ictx} {block : Ixon.Address} {idx : Nat}
        {r : Recursor} {F : Ixon.Eval.Frame} {bc : Constant}
        {ruleArgs indexArgs : List Ixon.Eval.Value}
        {targs : List IxIR0.Value} :
        ectx.resolve block = some bc →
        F.refs = bc.refs →
        F.selfMuts = Ixon.selfMutsOf bc.info →
        F.selfAddr = some block →
        RecMember ectx ictx block idx r →
        0 < r.indices.toNat →
        indexArgs.length = r.indices.toNat →
        RuntimePolicyPrefix (ValRel ectx ictx) (recRulePolicy r)
          ruleArgs targs [] →
        ValRel ectx ictx
          (.papV (.recH (some block) r F) (ruleArgs ++ indexArgs))
          (.pap (.rec_ (Erase.memberAddr block idx)
            (r.params.toNat + r.motives.toNat + r.minors.toNat + 1)) targs)
    | papRecIW {ectx ictx} {block : Ixon.Address} {idx : Nat}
        {r : Recursor} {F : Ixon.Eval.Frame} {bc : Constant}
        {sargs : List Ixon.Eval.Value} {targs ignored : List IxIR0.Value}
        {baseEnv : List IxIR0.Value} {remaining anchor : Nat} :
        ectx.resolve block = some bc →
        F.refs = bc.refs →
        F.selfMuts = Ixon.selfMutsOf bc.info →
        F.selfAddr = some block →
        RecMember ectx ictx block idx r →
        0 < r.indices.toNat →
        0 < remaining →
        ignored.length + remaining = anchor →
        RuntimePolicyPrefix (ValRel ectx ictx) (recPolicy r)
          sargs targs (List.replicate remaining .drop) →
        ValRel ectx ictx (.papV (.recH (some block) r F) sargs)
          (.clos .many
            (ignored.reverse ++
              .pap (.rec_ (Erase.memberAddr block idx)
                (r.params.toNat + r.motives.toNat + r.minors.toNat + 1))
                targs :: baseEnv)
            (Erase.lamManyN (remaining - 1) (.var anchor)))
    | inductiveType {ectx ictx} {address : Ixon.Address}
        {c : Constant} {p : Ix.Compiler.Ixon.InductiveProj}
        {args : List Ixon.Eval.Value} :
        ectx.resolve address = some c →
        c.info = .iPrj p →
        ValRel ectx ictx (.papV (.neuH (.const address)) args) .erased
    | inductiveMember {ectx ictx} {block : Ixon.Address} {idx : Nat}
        {bc : Constant} {ind : Ix.Compiler.Ixon.Inductive}
        {args : List Ixon.Eval.Value} :
        ectx.resolve block = some bc →
        (Ixon.selfMutsOf bc.info)[idx]? = some (.indc ind) →
        ValRel ectx ictx (.papV (.neuH (.member block idx)) args) .erased

  /-- Environments related slot-wise along the mask against a frame's
  tables; dropped slots are unconstrained on both sides. A rule-body
  environment bottoms out at `selfB`: the recSelf slot below the
  binders, carrying the recursor's coverage. -/
  inductive EnvRel : Ixon.Eval.EvalCtx → IxIR0.Ctx →
      Option (Ixon.Address × Nat) → Array Ixon.Address →
      Array MutConst → Option Ixon.Address → List Bool →
      List Ixon.Eval.Value → List IxIR0.Value → Prop where
    | nil {ectx ictx refs muts sa} :
        EnvRel ectx ictx none refs muts sa [] [] []
    | selfB {ectx ictx} {refs : Array Ixon.Address} {muts : Array MutConst}
        {block : Ixon.Address} {idx : Nat} {r : Recursor} {bc : Constant} :
        ectx.resolve block = some bc →
        refs = bc.refs →
        muts = Ixon.selfMutsOf bc.info →
          RecMember ectx ictx block idx r →
        EnvRel ectx ictx (some (block, idx)) refs muts (some block) [] []
          [.pap (.rec_ (Erase.memberAddr block idx)
            (r.params.toNat + r.motives.toNat + r.minors.toNat + 1)) []]
    | keep {ectx ictx sc refs muts sa mask env ρ v v'} :
        ValRel ectx ictx v v' →
        EnvRel ectx ictx sc refs muts sa mask env ρ →
        EnvRel ectx ictx sc refs muts sa (true :: mask) (v :: env)
          (v' :: ρ)
    | drop {ectx ictx sc refs muts sa mask env ρ v v'} :
        EnvRel ectx ictx sc refs muts sa mask env ρ →
        EnvRel ectx ictx sc refs muts sa (false :: mask) (v :: env)
          (v' :: ρ)

  /-- Pointwise-related value lists (constructor fields, pap args). -/
  inductive ValsRel : Ixon.Eval.EvalCtx → IxIR0.Ctx →
      List Ixon.Eval.Value → List IxIR0.Value → Prop where
    | nil {ectx ictx} : ValsRel ectx ictx [] []
    | cons {ectx ictx v v' vs vs'} :
        ValRel ectx ictx v v' → ValsRel ectx ictx vs vs' →
        ValsRel ectx ictx (v :: vs) (v' :: vs')
end

/-- Semantic correspondence for one configured external address. Structural
coverage proves that both programs expose the same arity; this premise is the
trusted ledger entry that relates successful source-oracle calls to target
oracle calls. -/
def OracleRelAt (ectx : Ixon.Eval.EvalCtx) (ictx : IxIR0.Ctx)
    (address : Ixon.Address) (arity : Nat) : Prop :=
  ∀ sourceArgs targetArgs sourceValue,
    sourceArgs.length = arity →
    ValsRel ectx ictx sourceArgs targetArgs →
    ectx.oracle address sourceArgs = some sourceValue →
    ∃ targetValue,
      ictx.oracle address targetArgs = some targetValue ∧
      ValRel ectx ictx sourceValue targetValue

/-- Pointwise trusted-extern ledger for every address configured by the
source evaluator. -/
def OracleRel (ectx : Ixon.Eval.EvalCtx) (ictx : IxIR0.Ctx) : Prop :=
  ∀ address arity,
    ectx.externArity address = some arity →
    OracleRelAt ectx ictx address arity

namespace OracleRel

/-- A context with no configured external addresses has a vacuous oracle
ledger. This discharges the new semantic premise for the existing fragment. -/
theorem of_externFree {ectx : Ixon.Eval.EvalCtx} {ictx : IxIR0.Ctx}
    (hfree : ∀ address, ectx.externArity address = none) :
    OracleRel ectx ictx := by
  intro address arity hconfigured
  rw [hfree address] at hconfigured
  simp at hconfigured

end OracleRel

omit scope in
private theorem bindOk {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

omit scope in
private theorem bindErr {ε α β : Type} (er : ε) (f : α → Except ε β) :
    ((Except.error er : Except ε α) >>= f) = Except.error er := rfl

omit scope in
private theorem bind_ok_iff {ε α β : Type} {x : Except ε α}
    {f : α → Except ε β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bindErr]
  | ok a => simp [bindOk]

/-! ## List and resolution helpers -/

omit scope in
private theorem arrGet?_toList {α} (a : Array α) (i : Nat) :
    a.toList[i]? = a[i]? := by
  simp

omit scope in
private theorem drop_append_of_le {α} :
    ∀ (l₁ l₂ : List α) (n : Nat), n ≤ l₁.length →
    (l₁ ++ l₂).drop n = l₁.drop n ++ l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ n h
    simp at h
    subst h
    simp
  | cons x rest ih =>
    intro l₂ n h
    cases n with
    | zero => simp
    | succ k =>
      simp only [List.cons_append, List.drop_succ_cons]
      exact ih l₂ k (by simpa using h)

omit scope in
private theorem peelChain_succ {n : Nat} {e B : Ixon.Expr}
    (h : peelChain (n + 1) e = some B) :
    ∃ u d b, e = .lam u d b ∧ peelChain n b = some B := by
  cases e <;> first
    | exact ⟨_, _, _, rfl, h⟩
    | (rw [peelChain.eq_def] at h; simp at h)

omit scope in
private theorem resolveMut_ok {ectx : Ixon.Eval.EvalCtx}
    {b : Ixon.Address} {i : Nat} {bc : Constant} {m : MutConst}
    (h : Ixon.Eval.resolveMut ectx b i = .ok (bc, m)) :
    ectx.resolve b = some bc ∧
      (Ixon.selfMutsOf bc.info)[i]? = some m := by
  rw [Ixon.Eval.resolveMut.eq_def] at h
  split at h
  · simp at h
  · rename_i bc' hres
    split at h
    · rename_i m' hm
      injection h with h'
      injection h' with hbc hm'
      subst hbc
      subst hm'
      exact ⟨hres, hm⟩
    · simp at h

/-- A successful guarded constructor major has the recursor's parameter
layout. Runtime block agreement plus `RecMember`'s finite block witness replace
the source typing fact that is not yet exposed in this repository. -/
private theorem recMember_ctor_params {ectx : Ixon.Eval.EvalCtx}
    {ictx : IxIR0.Ctx} {block ctorBlock : Ixon.Address} {idx : Nat}
    {r : Recursor} {indIdx cidx params fields : Nat}
    {cargs : List Ixon.Eval.Value} {checked : Unit}
    (hmem : RecMember ectx ictx block idx r)
    (hguard : Ixon.Eval.guardRecMajor (some block) r.params.toNat
      (.ctorV ctorBlock indIdx cidx cargs) = .ok checked)
    (hshape : CtorShape ectx ctorBlock indIdx cidx params fields) :
    params = r.params.toNat := by
  have hblock : ctorBlock = block := by
    simp only [Ixon.Eval.guardRecMajor] at hguard
    split at hguard
    · rename_i heq
      exact Ixon.Address.eq_of_beq heq
    · simp at hguard
  subst ctorBlock
  obtain ⟨bcCtor, ind, ct, hrm, hct, hip, hcp, hcf⟩ := hshape
  cases hmem with
  | mk hres hparams hienv hrules =>
    rename_i bcRec trules
    have hbc : bcCtor = bcRec := by
      have hc := (resolveMut_ok hrm).1
      have hr := (resolveMut_ok hres).1
      rw [hr] at hc
      injection hc with hbc
      exact hbc.symm
    subst bcCtor
    have hget : (Ixon.selfMutsOf bcRec.info).toList[indIdx]? =
        some (.indc ind) := by
      rw [arrGet?_toList]
      exact (resolveMut_ok hrm).2
    have hip' := hparams.lookup_indc hget
    exact hip.symm.trans hip'

/-! ## Relation lemmas -/

section Lemmas

variable {ectx : Ixon.Eval.EvalCtx} {ictx : IxIR0.Ctx}
  {sc : Option (Ixon.Address × Nat)} {refs : Array Ixon.Address}
  {muts : Array MutConst} {sa : Option Ixon.Address}

private theorem envRel_lookup : ∀ (i : Nat) {mask : List Bool}
    {env : List Ixon.Eval.Value} {ρ : List IxIR0.Value},
    EnvRel ectx ictx sc refs muts sa mask env ρ →
    ∀ (v : Ixon.Eval.Value), mask[i]? = some true →
      env[i]? = some v →
      ∃ v', ρ[i]? = some v' ∧ ValRel ectx ictx v v' := by
  intro i
  induction i with
  | zero =>
    intro mask env ρ h v hm he
    cases h with
    | nil => simp at hm
    | selfB _ _ _ _ => simp at hm
    | keep hv henv =>
      simp only [List.getElem?_cons_zero] at he ⊢
      injection he with he'
      subst he'
      exact ⟨_, rfl, hv⟩
    | drop henv => simp at hm
  | succ j ihj =>
    intro mask env ρ h v hm he
    cases h with
    | nil => simp at hm
    | selfB _ _ _ _ => simp at hm
    | keep hv henv =>
      simp only [List.getElem?_cons_succ] at hm he ⊢
      exact ihj henv v hm he
    | drop henv =>
      simp only [List.getElem?_cons_succ] at hm he ⊢
      exact ihj henv v hm he

private theorem envRel_self : ∀ {mask : List Bool}
    {env : List Ixon.Eval.Value} {ρ : List IxIR0.Value}
    {block : Ixon.Address} {idx : Nat},
    EnvRel ectx ictx (some (block, idx)) refs muts sa mask env ρ →
    ∃ r bc, ectx.resolve block = some bc ∧ refs = bc.refs ∧
      muts = Ixon.selfMutsOf bc.info ∧ sa = some block ∧
      RecMember ectx ictx block idx r ∧
      ρ[mask.length]? = some (.pap (.rec_ (Erase.memberAddr block idx)
        (r.params.toNat + r.motives.toNat + r.minors.toNat + 1)) []) := by
  intro mask
  induction mask with
  | nil =>
    intro env ρ block idx henv
    cases henv with
    | selfB hres hrefs hmuts hmem =>
      exact ⟨_, _, hres, hrefs, hmuts, rfl, hmem, rfl⟩
  | cons b mrest ih =>
    intro env ρ block idx henv
    cases henv with
    | keep hv henv' =>
      obtain ⟨r, bc, hres, hrefs, hmuts, hsa, hmem, hslot⟩ := ih henv'
      exact ⟨r, bc, hres, hrefs, hmuts, hsa, hmem, by simpa using hslot⟩
    | drop henv' =>
      obtain ⟨r, bc, hres, hrefs, hmuts, hsa, hmem, hslot⟩ := ih henv'
      exact ⟨r, bc, hres, hrefs, hmuts, hsa, hmem, by simpa using hslot⟩

private theorem valsRel_length : ∀ {vs : List Ixon.Eval.Value}
    {vs' : List IxIR0.Value}, ValsRel ectx ictx vs vs' →
    vs.length = vs'.length := by
  intro vs
  induction vs with
  | nil => intro vs' h; cases h; rfl
  | cons v rest ih =>
    intro vs' h
    cases h with
    | cons hv hrest => simp [ih hrest]

/-- A configured external head either remains a related partial application
or, at exact saturation, crosses the trusted oracle ledger. -/
private theorem externSaturate_sim
    {ectx : Ixon.Eval.EvalCtx} {ictx : IxIR0.Ctx}
    {address : Ixon.Address} {arity sourceFuel : Nat}
    {sourceArgs : List Ixon.Eval.Value} {targetArgs : List IxIR0.Value}
    {sourceValue : Ixon.Eval.Value}
    (horacles : OracleRel ectx ictx)
    (hconfigured : ectx.externArity address = some arity)
    (hle : sourceArgs.length ≤ arity)
    (hargs : ValsRel ectx ictx sourceArgs targetArgs)
    (hsource : Ixon.Eval.saturate ectx sourceFuel
      (.extH address arity) sourceArgs = .ok sourceValue) :
    ∃ targetFuel targetValue,
      IxIR0.saturate ictx targetFuel (.ext address arity) targetArgs =
          .ok targetValue ∧
        ValRel ectx ictx sourceValue targetValue ∧
        IxIR0.ProjectionSafe.Saturate ictx targetFuel
          (.ext address arity) targetArgs targetValue := by
  have hlength := valsRel_length hargs
  cases sourceFuel with
  | zero =>
    rw [Ixon.Eval.saturate.eq_def] at hsource
    simp at hsource
  | succ fuel =>
    rw [Ixon.Eval.saturate.eq_def] at hsource
    dsimp only at hsource
    simp only [Ixon.Eval.Head.arity?] at hsource
    cases hfull : sourceArgs.length == arity with
    | false =>
      rw [hfull] at hsource
      injection hsource with hvalue
      subst hvalue
      have hne : sourceArgs.length ≠ arity := by
        intro heq
        subst heq
        simp at hfull
      have hlt : sourceArgs.length < arity := by omega
      have htne : targetArgs.length ≠ arity := by omega
      refine ⟨1, .pap (.ext address arity) targetArgs, ?_,
        .papExtern hconfigured hlt hargs, .pending ?_⟩
      · rw [IxIR0.saturate.eq_def]
        dsimp only
        simp [IxIR0.Head.arity, htne]
      · simpa [IxIR0.Head.arity] using htne
    | true =>
      rw [hfull] at hsource
      have hsourceLength : sourceArgs.length = arity :=
        beq_iff_eq.mp hfull
      have htargetLength : targetArgs.length = arity := by omega
      cases fuel with
      | zero =>
        rw [Ixon.Eval.fire.eq_def] at hsource
        simp at hsource
      | succ fireFuel =>
        rw [Ixon.Eval.fire.eq_def] at hsource
        dsimp only at hsource
        cases hsourceOracle : ectx.oracle address sourceArgs with
        | none =>
          rw [hsourceOracle] at hsource
          contradiction
        | some oracleValue =>
          rw [hsourceOracle] at hsource
          injection hsource with hvalue
          subst hvalue
          obtain ⟨targetValue, htargetOracle, hvalueRel⟩ :=
            horacles address arity hconfigured sourceArgs targetArgs
              oracleValue hsourceLength hargs hsourceOracle
          refine ⟨2, targetValue, ?_, hvalueRel,
            .full htargetLength (.extern htargetOracle)⟩
          rw [IxIR0.saturate.eq_def]
          dsimp only
          simp only [IxIR0.Head.arity, beq_iff_eq.mpr htargetLength,
            if_true]
          rw [IxIR0.fire.eq_def]
          dsimp only
          rw [htargetOracle]

private theorem trueListRel_of_valsRel : ∀
    {vs : List Ixon.Eval.Value} {vs' : List IxIR0.Value},
    ValsRel ectx ictx vs vs' → ListRel (fun _ _ => True) vs vs' := by
  intro vs
  induction vs with
  | nil =>
    intro vs' h
    cases h
    exact .nil
  | cons v rest ih =>
    intro vs' h
    cases h with
    | cons hv hrest => exact .cons trivial (ih hrest)

private theorem valsRel_append : ∀ {vs : List Ixon.Eval.Value}
    {vs' : List IxIR0.Value} {v v'},
    ValsRel ectx ictx vs vs' → ValRel ectx ictx v v' →
    ValsRel ectx ictx (vs ++ [v]) (vs' ++ [v']) := by
  intro vs
  induction vs with
  | nil =>
    intro vs' v v' h hv
    cases h
    exact .cons hv .nil
  | cons w rest ih =>
    intro vs' v v' h hv
    cases h with
    | cons hw hrest => exact .cons hw (ih hrest hv)

private theorem valsRel_lookup : ∀ (i : Nat) {vs : List Ixon.Eval.Value}
    {vs' : List IxIR0.Value}, ValsRel ectx ictx vs vs' →
    ∀ v, vs[i]? = some v →
    ∃ v', vs'[i]? = some v' ∧ ValRel ectx ictx v v' := by
  intro i
  induction i with
  | zero =>
    intro vs vs' h v he
    cases h with
    | nil => simp at he
    | cons hv hrest =>
      simp only [List.getElem?_cons_zero] at he ⊢
      injection he with he'
      subst he'
      exact ⟨_, rfl, hv⟩
  | succ j ihj =>
    intro vs vs' h v he
    cases h with
    | nil => simp at he
    | cons hv hrest =>
      simp only [List.getElem?_cons_succ] at he ⊢
      exact ihj hrest v he

private theorem quotientRep_valRel {source : Ixon.Eval.Value}
    {target : IxIR0.Value} {representative : Ixon.Eval.Value}
    (hrel : ValRel ectx ictx source target)
    (hrep : Ixon.Eval.quotientRep? source = some representative) :
    ValRel ectx ictx representative target := by
  cases hrel with
  | quotV hrepresentative =>
    simp only [Ixon.Eval.quotientRep?] at hrep
    cases hrep
    exact hrepresentative
  | sort | pi | clos | litNat | litStr | quotType | papQuot | papExtern |
      ctorV | papCtor | papCtorParams | papRec | papRecI | papRecIW |
      inductiveType | inductiveMember =>
    simp [Ixon.Eval.quotientRep?] at hrep

private theorem envRel_keepRev : ∀ {vs : List Ixon.Eval.Value}
    {vs' : List IxIR0.Value} {mask : List Bool}
    {env : List Ixon.Eval.Value} {ρ : List IxIR0.Value},
    ValsRel ectx ictx vs vs' →
    EnvRel ectx ictx sc refs muts sa mask env ρ →
    EnvRel ectx ictx sc refs muts sa
      (List.replicate vs.length true ++ mask)
      (vs.reverse ++ env) (vs'.reverse ++ ρ) := by
  intro vs
  induction vs with
  | nil =>
    intro vs' mask env ρ hv henv
    cases hv
    simpa using henv
  | cons v rest ih =>
    intro vs' mask env ρ hv henv
    cases hv with
    | cons hv1 hrest =>
      have h := ih hrest (.keep hv1 henv)
      simpa [List.replicate_succ', List.append_assoc] using h

private theorem envRel_dropAny : ∀ (n : Nat) {xs : List Ixon.Eval.Value}
    {ys : List IxIR0.Value} {mask : List Bool}
    {env : List Ixon.Eval.Value} {ρ : List IxIR0.Value},
    xs.length = n → ys.length = n →
    EnvRel ectx ictx sc refs muts sa mask env ρ →
    EnvRel ectx ictx sc refs muts sa
      (List.replicate n false ++ mask) (xs ++ env) (ys ++ ρ) := by
  intro n
  induction n with
  | zero =>
    intro xs ys mask env ρ hx hy henv
    cases xs with
    | nil =>
      cases ys with
      | nil => simpa using henv
      | cons _ _ => simp at hy
    | cons _ _ => simp at hx
  | succ k ih
  =>
    intro xs ys mask env ρ hx hy henv
    cases xs with
    | nil => simp at hx
    | cons x xrest =>
      cases ys with
      | nil => simp at hy
      | cons y yrest =>
        simp only [List.length_cons, Nat.succ.injEq] at hx hy
        simp only [List.replicate_succ, List.cons_append]
        exact .drop (ih hx hy henv)

/-- Turn a fully consumed keep/ghost runtime cursor into the reversed rule
environment relation, extending an existing recSelf base. -/
private theorem envRel_runtimePolicyRev :
    ∀ {policies : List Erase.ArgPolicy}
      {sargs : List Ixon.Eval.Value} {targs : List IxIR0.Value},
      SlotPolicies policies →
      RuntimePolicyRel (ValRel ectx ictx) policies sargs targs →
      ∀ {mask : List Bool} {env : List Ixon.Eval.Value}
        {ρ : List IxIR0.Value},
        EnvRel ectx ictx sc refs muts sa mask env ρ →
        EnvRel ectx ictx sc refs muts sa
          ((policies.map policyKept).reverse ++ mask)
          (sargs.reverse ++ env) (targs.reverse ++ ρ) := by
  intro policies sargs targs hslots hcursor mask env ρ henv
  induction hslots generalizing sargs targs mask env ρ with
  | nil =>
    cases hcursor
    simpa using henv
  | keep hslots ih =>
    cases hcursor with
    | keep hrel htail =>
      have hout := ih htail (.keep hrel henv)
      simpa [List.reverse_cons, List.append_assoc, policyKept] using hout
  | ghost hslots ih =>
    cases hcursor with
    | ghost htail =>
      rename_i sarg targ
      have hout := ih htail
        (.drop (v := sarg) (v' := targ) henv)
      simpa [List.reverse_cons, List.append_assoc, policyKept] using hout

private theorem rulesRel_lookup {block : Ixon.Address} {idx : Nat}
    {r : Recursor} : ∀ (i : Nat) {rules : List RecursorRule}
    {trules : List IxIR0.RecRule},
    RulesRel ectx ictx block idx r refs muts rules trules →
    ∀ {rule}, rules[i]? = some rule →
    ∃ trule B, trules[i]? = some trule ∧
      trule.fields = rule.fields.toNat ∧
      peelChain (r.params.toNat + r.motives.toNat + r.minors.toNat +
        rule.fields.toNat)
        rule.rhs = some B ∧
      PErase ectx ictx (some (block, idx)) refs muts (some block)
        (recRuleMask r rule.fields.toNat)
        B trule.rhs := by
  intro i
  induction i with
  | zero =>
    intro rules trules h rule hr
    cases h with
    | nil => simp at hr
    | cons hf hpeel hpe hrest =>
      simp only [List.getElem?_cons_zero] at hr ⊢
      injection hr with hr'
      subst hr'
      exact ⟨_, _, rfl, hf, hpeel, hpe⟩
  | succ j ihj =>
    intro rules trules h rule hr
    cases h with
    | nil => simp at hr
    | cons _ _ _ hrest =>
      simp only [List.getElem?_cons_succ] at hr ⊢
      exact ihj hrest hr

end Lemmas

/-! ## Evaluation-shape lemmas -/

omit scope in
private theorem ctorParamSpine_shape {ectx : Ixon.Eval.EvalCtx}
    {refs : Array Ixon.Address} {e : Ixon.Expr} {a block : Ixon.Address}
    {indIdx cidx params fields consumed : Nat}
    (h : CtorParamSpine ectx refs e a block indIdx cidx params fields consumed) :
    CtorShape ectx block indIdx cidx params fields := by
  induction h with
  | head _ _ _ hshape => exact hshape
  | step _ _ ih => exact ih

omit scope in
private theorem ctorParamSpine_addr {ectx : Ixon.Eval.EvalCtx}
    {refs : Array Ixon.Address} {e : Ixon.Expr} {a block : Ixon.Address}
    {indIdx cidx params fields consumed : Nat}
    (h : CtorParamSpine ectx refs e a block indIdx cidx params fields consumed) :
    CtorAddr ectx a block indIdx cidx := by
  induction h with
  | head _ hres hinfo _ => exact ⟨_, _, hres, hinfo, rfl, rfl, rfl⟩
  | step _ _ ih => exact ih

omit scope in
private theorem recPrefix_shape {ectx refs muts sa} {e : Ixon.Expr}
    {r : Recursor} (h : RecPrefix ectx refs muts sa e r) :
    r.indices.toNat = 0 := by
  cases h with
  | refH _ _ _ _ hi => exact hi
  | recurH _ _ hi => exact hi

omit scope in
private theorem recSpine_shape {ectx refs muts sa} :
    ∀ {e : Ixon.Expr} {r : Recursor} {j : Nat},
    RecSpine ectx refs muts sa e r j →
    r.indices.toNat = 0 := by
  intro e r j h
  induction h with
  | head hp => exact recPrefix_shape hp
  | step _ _ ih => exact ih

omit scope in
/-- Evaluating a recursor-spine prefix yields the recursor's pap with
exactly the prefix's argument count. -/
private theorem recSpine_eval {ectx : Ixon.Eval.EvalCtx}
    {F : Ixon.Eval.Frame} :
    ∀ {e : Ixon.Expr} {r : Recursor} {j : Nat},
    RecSpine ectx F.refs F.selfMuts F.selfAddr e r j →
    ∀ {fuel : Nat} {env : List Ixon.Eval.Value} {fv : Ixon.Eval.Value},
    Ixon.Eval.eval ectx fuel F env e = .ok fv →
    ∃ ob F' sargs, fv = .papV (.recH ob r F') sargs ∧ sargs.length = j := by
  intro e r j h
  induction h with
  | head hp =>
    cases hp with
    | refH href hres hinfo hrm hi0 =>
      intro fuel env fv hev
      cases fuel with
      | zero => rw [Ixon.Eval.eval.eq_def] at hev; simp at hev
      | succ g =>
        rw [Ixon.Eval.eval.eq_def] at hev
        dsimp only at hev
        rw [href] at hev
        dsimp only at hev
        rw [bind_ok_iff] at hev
        obtain ⟨uinst', _, hev⟩ := hev
        cases g with
        | zero => rw [Ixon.Eval.evalRef.eq_def] at hev; simp at hev
        | succ g' =>
          rw [Ixon.Eval.evalRef.eq_def] at hev
          dsimp only at hev
          rw [hres] at hev
          dsimp only at hev
          rw [hinfo] at hev
          dsimp only at hev
          rw [hrm] at hev
          dsimp only at hev
          rw [bind_ok_iff] at hev
          obtain ⟨_, _, hev⟩ := hev
          injection hev with hv
          exact ⟨_, _, _, hv.symm, rfl⟩
    | recurH hsa hlook hi0 =>
      intro fuel env fv hev
      cases fuel with
      | zero => rw [Ixon.Eval.eval.eq_def] at hev; simp at hev
      | succ g =>
        rw [Ixon.Eval.eval.eq_def] at hev
        dsimp only at hev
        rw [bind_ok_iff] at hev
        obtain ⟨uinst', _, hev⟩ := hev
        rw [hlook] at hev
        dsimp only at hev
        rw [bind_ok_iff] at hev
        obtain ⟨_, _, hev⟩ := hev
        injection hev with hv
        exact ⟨_, _, _, hv.symm, rfl⟩
  | step hpre hj ih =>
    rename_i f a r' j'
    intro fuel env fv hev
    cases fuel with
    | zero => rw [Ixon.Eval.eval.eq_def] at hev; simp at hev
    | succ g =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      cases hf : Ixon.Eval.eval ectx g F env f with
      | error err => rw [hf, bindErr] at hev; simp at hev
      | ok fv₁ =>
        rw [hf, bindOk] at hev
        cases ha : Ixon.Eval.eval ectx g F env a with
        | error err => rw [ha, bindErr] at hev; simp at hev
        | ok av =>
          rw [ha, bindOk] at hev
          obtain ⟨ob, F', sargs, hfv₁, hlen⟩ := ih hf
          subst hfv₁
          have hi0 := recSpine_shape hpre
          have hj' := hj
          rw [recRulePolicy_length] at hj'
          cases g with
          | zero => rw [Ixon.Eval.apply.eq_def] at hev; simp at hev
          | succ g₂ =>
            rw [Ixon.Eval.apply.eq_def] at hev
            dsimp only at hev
            cases g₂ with
            | zero => rw [Ixon.Eval.saturate.eq_def] at hev; simp at hev
            | succ g₃ =>
              rw [Ixon.Eval.saturate.eq_def] at hev
              simp only [Ixon.Eval.Head.arity?] at hev
              have hne : ((sargs ++ [av]).length ==
                  Ixon.Eval.recArity r') = false := by
                rw [beq_eq_false_iff_ne]
                simp only [List.length_append, List.length_cons,
                  List.length_nil, Ixon.Eval.recArity, hi0, Nat.add_zero,
                  hlen]
                omega
              rw [hne] at hev
              simp at hev
              refine ⟨ob, F', sargs ++ [av], hev.symm, ?_⟩
              simp [hlen]

omit scope in
/-- Evaluating a visible ordinary-definition spine whose residual body is a
lambda yields exactly that residual closure.  The lemma follows the source
implementation telescope, independently of the declaration-type policy used
by executable erasure. -/
private theorem defSpine_eval_clos {ectx : Ixon.Eval.EvalCtx}
    {F : Ixon.Eval.Frame} :
    ∀ {function residual : Ixon.Expr},
      DefSpine ectx F.refs function residual →
      ∀ {uses : Uses} {domain body : Ixon.Expr},
      residual = .lam uses domain body →
      ∀ {fuel : Nat} {env : List Ixon.Eval.Value}
        {value : Ixon.Eval.Value},
        Ixon.Eval.eval ectx fuel F env function = .ok value →
        ∃ closureFrame closureEnv,
          value = .closV uses closureFrame closureEnv domain body := by
  intro function residual hspine
  induction hspine with
  | head href hresolve hinfo hunfold =>
    intro uses domain body hresidual fuel env value heval
    cases fuel with
    | zero => rw [Ixon.Eval.eval.eq_def] at heval; simp at heval
    | succ refFuel =>
      rw [Ixon.Eval.eval.eq_def] at heval
      dsimp only at heval
      rw [href] at heval
      dsimp only at heval
      rw [bind_ok_iff] at heval
      obtain ⟨uinst, _, heval⟩ := heval
      cases refFuel with
      | zero => rw [Ixon.Eval.evalRef.eq_def] at heval; simp at heval
      | succ bodyFuel =>
        rw [Ixon.Eval.evalRef.eq_def] at heval
        dsimp only at heval
        rw [hresolve] at heval
        dsimp only at heval
        rw [hinfo] at heval
        dsimp only at heval
        rw [bind_ok_iff] at heval
        obtain ⟨_, _, heval⟩ := heval
        rw [hunfold] at heval
        simp only [if_true] at heval
        rw [hresidual] at heval
        cases bodyFuel with
        | zero => rw [Ixon.Eval.eval.eq_def] at heval; simp at heval
        | succ bodyFuel =>
          rw [Ixon.Eval.eval.eq_def] at heval
          dsimp only at heval
          injection heval with hvalue
          exact ⟨_, [], hvalue.symm⟩
  | step hprefix ih =>
    rename_i functionPrefix sourceArgument previousUses previousDomain
      previousBody
    intro uses domain body hresidual fuel env value heval
    cases fuel with
    | zero => rw [Ixon.Eval.eval.eq_def] at heval; simp at heval
    | succ applyFuel =>
      rw [Ixon.Eval.eval.eq_def] at heval
      dsimp only at heval
      cases hfunction : Ixon.Eval.eval ectx applyFuel F env functionPrefix with
      | error error => rw [hfunction, bindErr] at heval; simp at heval
      | ok functionValue =>
        rw [hfunction, bindOk] at heval
        cases hargument : Ixon.Eval.eval ectx applyFuel F env sourceArgument with
        | error error => rw [hargument, bindErr] at heval; simp at heval
        | ok argumentValue =>
          rw [hargument, bindOk] at heval
          obtain ⟨closureFrame, closureEnv, hvalue⟩ := ih rfl hfunction
          subst functionValue
          cases applyFuel with
          | zero => rw [Ixon.Eval.apply.eq_def] at heval; simp at heval
          | succ bodyFuel =>
            rw [Ixon.Eval.apply.eq_def] at heval
            dsimp only at heval
            rw [hresidual] at heval
            cases bodyFuel with
            | zero => rw [Ixon.Eval.eval.eq_def] at heval; simp at heval
            | succ bodyFuel =>
              rw [Ixon.Eval.eval.eq_def] at heval
              dsimp only at heval
              injection heval with hresult
              exact ⟨closureFrame, argumentValue :: closureEnv,
                hresult.symm⟩

omit scope in
/-- Before all constructor parameters have been consumed, a visible
constructor spine evaluates to a source pap with exactly the consumed
parameter values. -/
private theorem ctorParamSpine_eval_lt {ectx : Ixon.Eval.EvalCtx}
    {F : Ixon.Eval.Frame} :
    ∀ {e : Ixon.Expr} {a block : Ixon.Address}
      {indIdx cidx params fields consumed : Nat},
      CtorParamSpine ectx F.refs e a block indIdx cidx params fields consumed →
      consumed < params →
      ∀ {fuel : Nat} {env : List Ixon.Eval.Value}
        {fv : Ixon.Eval.Value},
        Ixon.Eval.eval ectx fuel F env e = .ok fv →
        ∃ sargs, sargs.length = consumed ∧
          fv = .papV (.ctorH block indIdx cidx (params + fields)) sargs := by
  intro e a block indIdx cidx params fields consumed h
  induction h with
  | head href hres hinfo hshape =>
    intro hlt fuel env fv hev
    obtain ⟨bc, ind, ct, hrm, hct, hip, hcp, hcf⟩ := hshape
    cases fuel with
    | zero => rw [Ixon.Eval.eval.eq_def] at hev; simp at hev
    | succ g =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      rw [href] at hev
      dsimp only at hev
      rw [bind_ok_iff] at hev
      obtain ⟨uinst', _, hev⟩ := hev
      cases g with
      | zero => rw [Ixon.Eval.evalRef.eq_def] at hev; simp at hev
      | succ g' =>
        rw [Ixon.Eval.evalRef.eq_def] at hev
        dsimp only at hev
        rw [hres] at hev
        dsimp only at hev
        rw [hinfo] at hev
        dsimp only at hev
        rw [hrm] at hev
        dsimp only at hev
        rw [hct] at hev
        dsimp only at hev
        rw [bind_ok_iff] at hev
        obtain ⟨_, _, hev⟩ := hev
        cases g' with
        | zero => rw [Ixon.Eval.saturate.eq_def] at hev; simp at hev
        | succ g'' =>
          rw [Ixon.Eval.saturate.eq_def] at hev
          simp only [Ixon.Eval.Head.arity?] at hev
          have hctpos : 0 < ct.params.toNat := by omega
          have hne : ((([] : List Ixon.Eval.Value).length ==
              ct.params.toNat + ct.fields.toNat) : Bool) = false := by
            rw [beq_eq_false_iff_ne]
            simp only [List.length_nil]
            omega
          rw [hne] at hev
          simp at hev
          exact ⟨[], rfl, by simpa [hcp, hcf] using hev.symm⟩
  | step hpre hj ih =>
    rename_i f arg a block indIdx cidx params fields consumed
    intro hlt fuel env fv hev
    cases fuel with
    | zero => rw [Ixon.Eval.eval.eq_def] at hev; simp at hev
    | succ g =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      cases hf : Ixon.Eval.eval ectx g F env f with
      | error err => rw [hf, bindErr] at hev; simp at hev
      | ok fv₁ =>
        rw [hf, bindOk] at hev
        cases ha : Ixon.Eval.eval ectx g F env arg with
        | error err => rw [ha, bindErr] at hev; simp at hev
        | ok av =>
          rw [ha, bindOk] at hev
          obtain ⟨sargs, hlen, hfv₁⟩ := ih hj hf
          subst fv₁
          cases g with
          | zero => rw [Ixon.Eval.apply.eq_def] at hev; simp at hev
          | succ g' =>
            rw [Ixon.Eval.apply.eq_def] at hev
            dsimp only at hev
            cases g' with
            | zero => rw [Ixon.Eval.saturate.eq_def] at hev; simp at hev
            | succ g'' =>
              rw [Ixon.Eval.saturate.eq_def] at hev
              simp only [Ixon.Eval.Head.arity?] at hev
              have hne : ((sargs ++ [av]).length == params + fields) =
                  false := by
                rw [beq_eq_false_iff_ne]
                simp only [List.length_append, List.length_cons,
                  List.length_nil]
                omega
              rw [hne] at hev
              simp at hev
              subst hev
              exact ⟨sargs ++ [av], by simp [hlen], rfl⟩

omit scope in
/-- After the entire dropped parameter prefix, source and target constructor
heads have synchronized runtime arities: a nullary target constructor has
fired, while a constructor with fields is an unapplied target pap. -/
private theorem ctorParamSpine_eval_full {ectx : Ixon.Eval.EvalCtx}
    {F : Ixon.Eval.Frame} {e : Ixon.Expr} {a block : Ixon.Address}
    {indIdx cidx params fields : Nat}
    (hpos : 0 < params)
    (h : CtorParamSpine ectx F.refs e a block indIdx cidx params fields params)
    {fuel : Nat} {env : List Ixon.Eval.Value} {v : Ixon.Eval.Value}
    (hev : Ixon.Eval.eval ectx fuel F env e = .ok v) :
    ∃ sargs, sargs.length = params ∧
      ((fields = 0 ∧ v = .ctorV block indIdx cidx sargs) ∨
       (0 < fields ∧
        v = .papV (.ctorH block indIdx cidx (params + fields)) sargs)) := by
  cases h with
  | head href hres hinfo hshape => omega
  | step hpre hj =>
    rename_i f arg consumed
    cases fuel with
    | zero => rw [Ixon.Eval.eval.eq_def] at hev; simp at hev
    | succ g =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      cases hf : Ixon.Eval.eval ectx g F env f with
      | error err => rw [hf, bindErr] at hev; simp at hev
      | ok fv =>
        rw [hf, bindOk] at hev
        cases ha : Ixon.Eval.eval ectx g F env arg with
        | error err => rw [ha, bindErr] at hev; simp at hev
        | ok av =>
          rw [ha, bindOk] at hev
          obtain ⟨sargs, hlen, hfv⟩ := ctorParamSpine_eval_lt hpre hj hf
          subst fv
          cases g with
          | zero => rw [Ixon.Eval.apply.eq_def] at hev; simp at hev
          | succ g' =>
            rw [Ixon.Eval.apply.eq_def] at hev
            dsimp only at hev
            cases g' with
            | zero => rw [Ixon.Eval.saturate.eq_def] at hev; simp at hev
            | succ g'' =>
              rw [Ixon.Eval.saturate.eq_def] at hev
              simp only [Ixon.Eval.Head.arity?] at hev
              cases fields with
              | zero =>
                have heq : ((sargs ++ [av]).length ==
                    (consumed + 1) + 0) = true := by
                  rw [beq_iff_eq]
                  simp only [List.length_append, List.length_cons,
                    List.length_nil]
                  omega
                rw [heq] at hev
                simp at hev
                cases g'' with
                | zero => rw [Ixon.Eval.fire.eq_def] at hev; simp at hev
                | succ g''' =>
                  rw [Ixon.Eval.fire.eq_def] at hev
                  dsimp only at hev
                  injection hev with hv
                  subst hv
                  exact ⟨sargs ++ [av], by simp [hlen], .inl ⟨rfl, rfl⟩⟩
              | succ fields' =>
                have hne : ((sargs ++ [av]).length ==
                    (consumed + 1) + (fields' + 1)) = false := by
                  rw [beq_eq_false_iff_ne]
                  simp only [List.length_append, List.length_cons,
                    List.length_nil]
                  omega
                rw [hne] at hev
                simp at hev
                subst hev
                exact ⟨sargs ++ [av], by simp [hlen],
                  .inr ⟨by omega, rfl⟩⟩

omit scope in
/-- Entering a kernel-shaped lambda telescope: applying the chain's
closure to all its arguments ends in evaluating the peeled body under
the reversed arguments. -/
private theorem applyMany_chain {ectx : Ixon.Eval.EvalCtx} :
    ∀ (rest : List Ixon.Eval.Value) {a : Ixon.Eval.Value} {fuel : Nat}
    {F : Ixon.Eval.Frame} {envAcc : List Ixon.Eval.Value} {u : Uses}
    {dom body B : Ixon.Expr} {v : Ixon.Eval.Value},
    peelChain rest.length body = some B →
    Ixon.Eval.applyMany ectx fuel (.closV u F envAcc dom body)
      (a :: rest) = .ok v →
    ∃ g, g ≤ fuel ∧
      Ixon.Eval.eval ectx g F (rest.reverse ++ a :: envAcc) B = .ok v := by
  intro rest
  induction rest with
  | nil =>
    intro a fuel F envAcc u dom body B v hpeel happ
    injection hpeel with hB
    subst hB
    cases fuel with
    | zero => rw [Ixon.Eval.applyMany.eq_def] at happ; simp at happ
    | succ fu =>
      rw [Ixon.Eval.applyMany.eq_def] at happ
      dsimp only at happ
      rw [bind_ok_iff] at happ
      obtain ⟨f', happly, hrest⟩ := happ
      cases fu with
      | zero => rw [Ixon.Eval.apply.eq_def] at happly; simp at happly
      | succ fu₂ =>
        rw [Ixon.Eval.applyMany.eq_def] at hrest
        dsimp only at hrest
        injection hrest with hv
        subst hv
        rw [Ixon.Eval.apply.eq_def] at happly
        dsimp only at happly
        exact ⟨fu₂, by omega, happly⟩
  | cons b rest' ihr =>
    intro a fuel F envAcc u dom body B v hpeel happ
    obtain ⟨u', d', b₂, hbody, hpeel'⟩ := peelChain_succ hpeel
    subst hbody
    cases fuel with
    | zero => rw [Ixon.Eval.applyMany.eq_def] at happ; simp at happ
    | succ fu =>
      rw [Ixon.Eval.applyMany.eq_def] at happ
      dsimp only at happ
      rw [bind_ok_iff] at happ
      obtain ⟨f', happly, hrest⟩ := happ
      cases fu with
      | zero => rw [Ixon.Eval.apply.eq_def] at happly; simp at happly
      | succ fu₂ =>
        rw [Ixon.Eval.apply.eq_def] at happly
        dsimp only at happly
        cases fu₂ with
        | zero => rw [Ixon.Eval.eval.eq_def] at happly; simp at happly
        | succ fu₃ =>
          rw [Ixon.Eval.eval.eq_def] at happly
          dsimp only at happly
          injection happly with hf'
          subst hf'
          obtain ⟨g, hg, hev⟩ := ihr hpeel' hrest
          refine ⟨g, by omega, ?_⟩
          simpa [List.append_assoc] using hev

omit scope in
/-- Chain entry from the rule's closed rhs: evaluate the chain (a
closure), apply all arguments, land in the body. -/
private theorem chain_enter {ectx : Ixon.Eval.EvalCtx} :
    ∀ (args : List Ixon.Eval.Value) {fuel : Nat} {F : Ixon.Eval.Frame}
    {chain B : Ixon.Expr} {rhsV v : Ixon.Eval.Value},
    peelChain args.length chain = some B →
    Ixon.Eval.eval ectx fuel F [] chain = .ok rhsV →
    Ixon.Eval.applyMany ectx fuel rhsV args = .ok v →
    ∃ g, g ≤ fuel ∧ Ixon.Eval.eval ectx g F args.reverse B = .ok v := by
  intro args
  cases args with
  | nil =>
    intro fuel F chain B rhsV v hpeel hchain happ
    injection hpeel with hB
    subst hB
    cases fuel with
    | zero => rw [Ixon.Eval.applyMany.eq_def] at happ; simp at happ
    | succ fu =>
      rw [Ixon.Eval.applyMany.eq_def] at happ
      dsimp only at happ
      injection happ with hv
      subst hv
      exact ⟨fu + 1, by omega, hchain⟩
  | cons a rest =>
    intro fuel F chain B rhsV v hpeel hchain happ
    obtain ⟨u, d, b, hchainEq, hpeel'⟩ := peelChain_succ hpeel
    subst hchainEq
    cases fuel with
    | zero => rw [Ixon.Eval.eval.eq_def] at hchain; simp at hchain
    | succ fu =>
      rw [Ixon.Eval.eval.eq_def] at hchain
      dsimp only at hchain
      injection hchain with hrhsV
      subst hrhsV
      obtain ⟨g, hg, hev⟩ := applyMany_chain rest hpeel' happ
      refine ⟨g, by omega, ?_⟩
      simpa using hev

omit scope in
private theorem strongNat {P : Nat → Prop}
    (step : ∀ n, (∀ m, m < n → P m) → P n) : ∀ n, P n := by
  have aux : ∀ k n, n < k → P n := by
    intro k
    induction k with
    | zero => intro n hn; exact absurd hn (Nat.not_lt_zero n)
    | succ k ihk =>
      intro n hn
      exact step n fun m hm =>
        ihk m (Nat.lt_of_lt_of_le hm (Nat.lt_succ_iff.mp hn))
  exact fun n => aux (n + 1) n (Nat.lt_succ_self n)

private def SimAt (fuel : Nat) : Prop :=
  ∀ (ectx : Ixon.Eval.EvalCtx) (F : Ixon.Eval.Frame)
    (env : List Ixon.Eval.Value) (e : Ixon.Expr) (v : Ixon.Eval.Value)
    (sc : Option (Ixon.Address × Nat)) (mask : List Bool)
    (ρ : List IxIR0.Value) (e' : IxIR0.Expr) (ictx : IxIR0.Ctx),
    MemberCoverage ectx ictx scope.plan →
    OracleRel ectx ictx →
    Ixon.Eval.eval ectx fuel F env e = .ok v →
    PErase ectx ictx sc F.refs F.selfMuts F.selfAddr mask e e' →
    EnvRel ectx ictx sc F.refs F.selfMuts F.selfAddr mask env ρ →
    ∃ fuel' v', IxIR0.eval ictx fuel' ρ e' = .ok v' ∧ ValRel ectx ictx v v'
      ∧ IxIR0.ProjectionSafe.Eval ictx fuel' ρ e' v'

/-- Reuse expression simulation as a value-application lemma.  Two kept
variables expose the already related function and argument; the one extra
evaluation layer is why callers supply the strict `fuel + 1 < bound` fact. -/
private theorem applyRel_sim {bound : Nat}
    (sim : ∀ m, m < bound → SimAt m)
    {ectx : Ixon.Eval.EvalCtx} {ictx : IxIR0.Ctx}
    {fuel : Nat} {function argument result : Ixon.Eval.Value}
    {targetFunction targetArgument : IxIR0.Value}
    (hmembers : MemberCoverage ectx ictx scope.plan)
    (horacles : OracleRel ectx ictx)
    (hbound : fuel + 1 < bound)
    (happly : Ixon.Eval.apply ectx fuel function argument = .ok result)
    (hfunction : ValRel ectx ictx function targetFunction)
    (hargument : ValRel ectx ictx argument targetArgument) :
    ∃ targetFuel targetResult,
      IxIR0.apply ictx targetFuel targetFunction targetArgument =
          .ok targetResult ∧
        ValRel ectx ictx result targetResult ∧
        IxIR0.ProjectionSafe.Apply ictx targetFuel targetFunction
          targetArgument targetResult := by
  cases fuel with
  | zero => rw [Ixon.Eval.apply.eq_def] at happly; simp at happly
  | succ fuel =>
    have hsource : Ixon.Eval.eval ectx (fuel + 2) {}
        [function, argument] (.app (.var 0) (.var 1)) = .ok result := by
      simpa [Ixon.Eval.eval, bindOk] using happly
    have hpe : PErase ectx ictx none #[] #[] none [true, true]
        (.app (.var 0) (.var 1)) (.app (.var 0) (.var 1)) :=
      .app (.var rfl) (.var rfl)
    have henv : EnvRel ectx ictx none #[] #[] none [true, true]
        [function, argument] [targetFunction, targetArgument] :=
      .keep hfunction (.keep hargument .nil)
    obtain ⟨targetFuel, targetResult, htarget, hresult, htrace⟩ :=
      sim (fuel + 2) (by omega) ectx {} [function, argument]
        (.app (.var 0) (.var 1)) result none [true, true]
        [targetFunction, targetArgument] (.app (.var 0) (.var 1)) ictx
        hmembers horacles hsource hpe henv
    cases htrace with
    | app htargetFunction htargetArgument happlyTrace =>
      cases htargetFunction with
      | var hlookupFunction =>
        simp only [List.getElem?_cons_zero] at hlookupFunction
        cases hlookupFunction
        cases htargetArgument with
        | var hlookupArgument =>
          simp only [List.getElem?_cons_succ,
            List.getElem?_cons_zero] at hlookupArgument
          cases hlookupArgument
          exact ⟨_, _, happlyTrace.run, hresult, happlyTrace⟩

/-- A visible indexed recursor spine simulates as one unit.  The result keeps
the complete policy cursor local until every source-only index has been
consumed, so no intermediate target pap is exposed to generic application. -/
private theorem recEraseSpine_sim {bound : Nat}
    (sim : ∀ m, m < bound → SimAt m)
    {ectx : Ixon.Eval.EvalCtx} {ictx : IxIR0.Ctx}
    (hmembers : MemberCoverage ectx ictx scope.plan)
    (horacles : OracleRel ectx ictx)
    {sc : Option (Ixon.Address × Nat)} {F : Ixon.Eval.Frame}
    {mask : List Bool} :
    ∀ {e : Ixon.Expr} {e' : IxIR0.Expr} {r : Recursor}
      {rest : List Erase.ArgPolicy},
      RecEraseSpine ectx ictx sc F.refs F.selfMuts F.selfAddr mask
        e e' r rest →
      ∀ {fuel : Nat} {env : List Ixon.Eval.Value}
        {v : Ixon.Eval.Value} {ρ : List IxIR0.Value},
        fuel ≤ bound →
        Ixon.Eval.eval ectx fuel F env e = .ok v →
        EnvRel ectx ictx sc F.refs F.selfMuts F.selfAddr mask env ρ →
        ∃ fuel' block idx F₂ bc sargs targs,
          v = .papV (.recH (some block) r F₂) sargs ∧
          IxIR0.eval ictx fuel' ρ e' =
            .ok (.pap (.rec_ (Erase.memberAddr block idx)
              (r.params.toNat + r.motives.toNat + r.minors.toNat + 1))
              targs) ∧
          IxIR0.ProjectionSafe.Eval ictx fuel' ρ e'
            (.pap (.rec_ (Erase.memberAddr block idx)
              (r.params.toNat + r.motives.toNat + r.minors.toNat + 1))
              targs) ∧
          ectx.resolve block = some bc ∧
          F₂.refs = bc.refs ∧
          F₂.selfMuts = Ixon.selfMutsOf bc.info ∧
          F₂.selfAddr = some block ∧
          RecMember ectx ictx block idx r ∧
          0 < r.indices.toNat ∧
          RuntimePolicyPrefix (ValRel ectx ictx) (recPolicy r)
            sargs targs rest := by
  intro e e' r rest hspine fuel env v ρ hbound hev henv
  induction fuel using strongNat generalizing e e' r rest v
  rename_i fuel fuelIH
  cases hspine with
  | head href hres hinfo hrm hipos hidecl hmem =>
    rename_i refIdx univIdxs a c p bc
    cases fuel with
    | zero => rw [Ixon.Eval.eval.eq_def] at hev; simp at hev
    | succ g =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      rw [href] at hev
      dsimp only at hev
      rw [bind_ok_iff] at hev
      obtain ⟨uinst', huinst, hev⟩ := hev
      cases g with
      | zero => rw [Ixon.Eval.evalRef.eq_def] at hev; simp at hev
      | succ g' =>
        rw [Ixon.Eval.evalRef.eq_def] at hev
        dsimp only at hev
        rw [hres] at hev
        dsimp only at hev
        rw [hinfo] at hev
        dsimp only at hev
        rw [hrm] at hev
        dsimp only at hev
        rw [bind_ok_iff] at hev
        obtain ⟨guarded, hguard, hev⟩ := hev
        injection hev with hv
        subst v
        obtain ⟨trules, hienv⟩ := hmem.target
        refine ⟨3, p.block, p.idx.toNat,
          Ixon.Eval.Frame.ofConst bc uinst' (some p.block), bc,
          [], [], rfl, ?_, .refDefn hidecl (.refRecursor hienv),
          (resolveMut_ok hrm).1, rfl, rfl, rfl,
          hmem, hipos, .stop (recPolicy r)⟩
        rw [IxIR0.eval.eq_def]
        dsimp only
        rw [hidecl]
        dsimp only
        rw [IxIR0.eval.eq_def]
        dsimp only
        rw [hienv]
  | selfHead hsc hsa hidx hrm hrefs hlookup hipos =>
    rename_i block idx recIdx univIdxs bc
    cases fuel with
    | zero => rw [Ixon.Eval.eval.eq_def] at hev; simp at hev
    | succ g =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      rw [bind_ok_iff] at hev
      obtain ⟨uinst', huinst, hev⟩ := hev
      rw [hlookup] at hev
      dsimp only at hev
      rw [bind_ok_iff] at hev
      obtain ⟨guarded, hguard, hev⟩ := hev
      rw [hsa] at hev
      injection hev with hvalue
      subst v
      rw [hsc] at henv
      obtain ⟨selfR, selfBc, hselfResolve, selfRefs, selfMuts, selfAddr,
          selfMember, hslot⟩ := envRel_self henv
      have hbc : selfBc = bc := by
        rw [(resolveMut_ok hrm).1] at hselfResolve
        injection hselfResolve with heq
        exact heq.symm
      subst selfBc
      obtain ⟨selfBc', hselfMut⟩ := selfMember.resolve
      rw [hrm] at hselfMut
      injection hselfMut with hpair
      injection hpair with hbc hr
      injection hr with hrecur
      subst selfR
      refine ⟨1, block, idx, { F with uinst := uinst', selfAddr := some block },
        bc, [], [], rfl,
        ?_, .var hslot, (resolveMut_ok hrm).1, selfRefs, selfMuts, rfl,
        selfMember,
        hipos, .stop (recPolicy r)⟩
      rw [IxIR0.eval.eq_def]
      dsimp only
      rw [hslot]
  | memberHead hsa hrm hrefs hmuts hipos hplan =>
    rename_i block recIdx univIdxs bc
    cases fuel with
    | zero => rw [Ixon.Eval.eval.eq_def] at hev; simp at hev
    | succ g =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      rw [bind_ok_iff] at hev
      obtain ⟨uinst', _, hev⟩ := hev
      have hlookup : F.selfMuts[recIdx.toNat]? = some (.recr r) := by
        rw [hmuts]
        exact (resolveMut_ok hrm).2
      rw [hlookup] at hev
      dsimp only at hev
      rw [bind_ok_iff] at hev
      obtain ⟨_, _, hev⟩ := hev
      rw [hsa] at hev
      injection hev with hv
      subst v
      have hrel := hmembers.lookup hplan
      cases hrel with
      | defn hother _ _ _ _ =>
        rw [hrm] at hother
        simp at hother
      | externDefn hother _ _ _ =>
        rw [hrm] at hother
        simp at hother
      | recr hmem =>
        obtain ⟨bc', hother⟩ := hmem.resolve
        rw [hrm] at hother
        injection hother with hpair
        injection hpair with hbc hr
        subst bc'
        cases hr
        obtain ⟨trules, hienv⟩ := hmem.target
        refine ⟨1, block, recIdx.toNat, { F with uinst := uinst' }, bc,
          [], [], (by simp [hsa]), ?_, .refRecursor hienv,
          (resolveMut_ok hrm).1, hrefs, hmuts, hsa, hmem, hipos,
          .stop (recPolicy r)⟩
        rw [IxIR0.eval.eq_def]
        dsimp only
        rw [hienv]
  | keep hpre harg =>
    rename_i f a f' a'
    cases fuel with
    | zero => rw [Ixon.Eval.eval.eq_def] at hev; simp at hev
    | succ g =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      cases hf : Ixon.Eval.eval ectx g F env f with
      | error err => rw [hf, bindErr] at hev; simp at hev
      | ok fv =>
        rw [hf, bindOk] at hev
        cases ha : Ixon.Eval.eval ectx g F env a with
        | error err => rw [ha, bindErr] at hev; simp at hev
        | ok av =>
          rw [ha, bindOk] at hev
          obtain ⟨n₁, block, idx, F₂, bc, sargs, targs, hfv, hfv', htraceF,
              hresolve, hFrefs, hFmuts, hFsa, hmem, hipos, hcursor⟩ :=
            fuelIH g (by omega) hpre (by omega) hf
          obtain ⟨n₂, av', hav', hrelA, htraceA⟩ :=
            sim g (by omega) ectx F env a av sc mask ρ a' ictx
              hmembers horacles ha harg henv
          rw [hfv] at hev
          cases g with
          | zero => rw [Ixon.Eval.apply.eq_def] at hev; simp at hev
          | succ g' =>
            rw [Ixon.Eval.apply.eq_def] at hev
            dsimp only at hev
            cases g' with
            | zero => rw [Ixon.Eval.saturate.eq_def] at hev; simp at hev
            | succ g'' =>
              rw [Ixon.Eval.saturate.eq_def] at hev
              simp only [Ixon.Eval.Head.arity?] at hev
              have hslen := hcursor.source_length
              have hne : ((sargs ++ [av]).length ==
                  Ixon.Eval.recArity r) = false := by
                rw [beq_eq_false_iff_ne]
                simp only [List.length_append, List.length_cons,
                  List.length_nil, Ixon.Eval.recArity]
                simp only [List.length_cons] at hslen
                rw [recPolicy_length_exact] at hslen
                omega
              rw [hne] at hev
              simp at hev
              subst v
              have hcursor' := hcursor.append_keep hrelA
              refine ⟨n₁ + n₂ + 4, block, idx, F₂, bc,
                sargs ++ [av], targs ++ [av'], rfl, ?_, ?_, hresolve,
                hFrefs, hFmuts, hFsa, hmem, hipos, hcursor'⟩
              rw [IxIR0.eval.eq_def]
              dsimp only
              rw [IxIR0.eval_mono (show n₁ ≤ n₁ + n₂ + 3 by omega)
                hfv', bindOk]
              rw [IxIR0.eval_mono (show n₂ ≤ n₁ + n₂ + 3 by omega)
                hav', bindOk]
              rw [IxIR0.apply.eq_def]
              dsimp only
              rw [IxIR0.saturate.eq_def]
              dsimp only
              have htlen := hcursor.target_length
              have hne' : ((targs ++ [av']).length ==
                  (r.params.toNat + r.motives.toNat +
                    r.minors.toNat + 1)) = false := by
                rw [beq_eq_false_iff_ne]
                simp only [List.length_append, List.length_cons,
                  List.length_nil]
                simp only [policyTargetArity,
                  policyTargetArity_recPolicy] at htlen
                omega
              simp only [IxIR0.Head.arity.eq_def, hne']
              simp
              have hsaturate : IxIR0.ProjectionSafe.Saturate ictx
                  (n₁ + n₂ + 2)
                  (.rec_ (Erase.memberAddr block idx)
                    (r.params.toNat + r.motives.toNat +
                      r.minors.toNat + 1))
                  (targs ++ [av'])
                  (.pap (.rec_ (Erase.memberAddr block idx)
                    (r.params.toNat + r.motives.toNat +
                      r.minors.toNat + 1)) (targs ++ [av'])) :=
                .pending (by
                  have htlen := hcursor.target_length
                  simp only [policyTargetArity,
                    policyTargetArity_recPolicy] at htlen
                  simp only [IxIR0.Head.arity, List.length_append,
                    List.length_cons, List.length_nil]
                  omega)
              exact .app
                (htraceF.mono_le (by omega))
                (htraceA.mono_le (by omega))
                (.pap hsaturate)
  | ghost hpre =>
    rename_i f a f'
    cases fuel with
    | zero => rw [Ixon.Eval.eval.eq_def] at hev; simp at hev
    | succ g =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      cases hf : Ixon.Eval.eval ectx g F env f with
      | error err => rw [hf, bindErr] at hev; simp at hev
      | ok fv =>
        rw [hf, bindOk] at hev
        cases ha : Ixon.Eval.eval ectx g F env a with
        | error err => rw [ha, bindErr] at hev; simp at hev
        | ok av =>
          rw [ha, bindOk] at hev
          obtain ⟨n₁, block, idx, F₂, bc, sargs, targs, hfv, hfv', htraceF,
              hresolve, hFrefs, hFmuts, hFsa, hmem, hipos, hcursor⟩ :=
            fuelIH g (by omega) hpre (by omega) hf
          rw [hfv] at hev
          cases g with
          | zero => rw [Ixon.Eval.apply.eq_def] at hev; simp at hev
          | succ g' =>
            rw [Ixon.Eval.apply.eq_def] at hev
            dsimp only at hev
            cases g' with
            | zero => rw [Ixon.Eval.saturate.eq_def] at hev; simp at hev
            | succ g'' =>
              rw [Ixon.Eval.saturate.eq_def] at hev
              simp only [Ixon.Eval.Head.arity?] at hev
              have hslen := hcursor.source_length
              have hne : ((sargs ++ [av]).length ==
                  Ixon.Eval.recArity r) = false := by
                rw [beq_eq_false_iff_ne]
                simp only [List.length_append, List.length_cons,
                  List.length_nil, Ixon.Eval.recArity]
                simp only [List.length_cons] at hslen
                rw [recPolicy_length_exact] at hslen
                omega
              rw [hne] at hev
              simp at hev
              subst v
              have hcursor' := hcursor.append_ghost
                (sarg := av) (targ := IxIR0.Value.erased)
              refine ⟨n₁ + 4, block, idx, F₂, bc, sargs ++ [av],
                targs ++ [.erased], rfl, ?_, ?_, hresolve, hFrefs, hFmuts,
                hFsa, hmem, hipos, hcursor'⟩
              rw [IxIR0.eval.eq_def]
              dsimp only
              rw [IxIR0.eval_mono (show n₁ ≤ n₁ + 3 by omega) hfv', bindOk]
              have hbox : IxIR0.eval ictx (n₁ + 3) ρ .erased =
                  .ok .erased := by rw [IxIR0.eval.eq_def]
              rw [hbox, bindOk]
              rw [IxIR0.apply.eq_def]
              dsimp only
              rw [IxIR0.saturate.eq_def]
              dsimp only
              have htlen := hcursor.target_length
              have hne' : ((targs ++ [IxIR0.Value.erased]).length ==
                  (r.params.toNat + r.motives.toNat +
                    r.minors.toNat + 1)) = false := by
                rw [beq_eq_false_iff_ne]
                simp only [List.length_append, List.length_cons,
                  List.length_nil]
                simp only [policyTargetArity,
                  policyTargetArity_recPolicy] at htlen
                omega
              simp only [IxIR0.Head.arity.eq_def, hne']
              simp
              have hsaturate : IxIR0.ProjectionSafe.Saturate ictx
                  (n₁ + 2)
                  (.rec_ (Erase.memberAddr block idx)
                    (r.params.toNat + r.motives.toNat +
                      r.minors.toNat + 1))
                  (targs ++ [.erased])
                  (.pap (.rec_ (Erase.memberAddr block idx)
                    (r.params.toNat + r.motives.toNat +
                      r.minors.toNat + 1)) (targs ++ [.erased])) :=
                .pending (by
                  have htlen := hcursor.target_length
                  simp only [policyTargetArity,
                    policyTargetArity_recPolicy] at htlen
                  simp only [IxIR0.Head.arity, List.length_append,
                    List.length_cons, List.length_nil]
                  omega)
              exact .app
                (htraceF.mono_le (by omega))
                (.erased)
                (.pap hsaturate)
  | drop hpre =>
    rename_i f a
    cases fuel with
    | zero => rw [Ixon.Eval.eval.eq_def] at hev; simp at hev
    | succ g =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      cases hf : Ixon.Eval.eval ectx g F env f with
      | error err => rw [hf, bindErr] at hev; simp at hev
      | ok fv =>
        rw [hf, bindOk] at hev
        cases ha : Ixon.Eval.eval ectx g F env a with
        | error err => rw [ha, bindErr] at hev; simp at hev
        | ok av =>
          rw [ha, bindOk] at hev
          obtain ⟨n₁, block, idx, F₂, bc, sargs, targs, hfv, hfv', htraceF,
              hresolve, hFrefs, hFmuts, hFsa, hmem, hipos, hcursor⟩ :=
            fuelIH g (by omega) hpre (by omega) hf
          rw [hfv] at hev
          cases g with
          | zero => rw [Ixon.Eval.apply.eq_def] at hev; simp at hev
          | succ g' =>
            rw [Ixon.Eval.apply.eq_def] at hev
            dsimp only at hev
            cases g' with
            | zero => rw [Ixon.Eval.saturate.eq_def] at hev; simp at hev
            | succ g'' =>
              rw [Ixon.Eval.saturate.eq_def] at hev
              simp only [Ixon.Eval.Head.arity?] at hev
              have hslen := hcursor.source_length
              have hne : ((sargs ++ [av]).length ==
                  Ixon.Eval.recArity r) = false := by
                rw [beq_eq_false_iff_ne]
                simp only [List.length_append, List.length_cons,
                  List.length_nil, Ixon.Eval.recArity]
                simp only [List.length_cons] at hslen
                rw [recPolicy_length_exact] at hslen
                omega
              rw [hne] at hev
              simp at hev
              subst v
              exact ⟨n₁, block, idx, F₂, bc, sargs ++ [av], targs,
                rfl, hfv', htraceF, hresolve, hFrefs, hFmuts, hFsa, hmem, hipos,
                hcursor.append_drop⟩

private theorem not_neutral_of_majorCtor_ok
    {peel : Bool} {major : Ixon.Eval.Value} {tag : Nat}
    {fields : List Ixon.Eval.Value}
    (hmajor : Ixon.Eval.majorCtor peel major = .ok (tag, fields)) :
    major.isNeutral = false := by
  cases major <;>
    simp [Ixon.Eval.majorCtor, Ixon.Eval.Value.isNeutral] at hmajor ⊢

/-- The ι correspondence: given a saturated recursor pap on both
sides, agreeing major analyses (`hmcS`/`htmc` — the same
block-identity peel), and related constructor fields, the source fire
and the target fire terminate related. -/
private theorem fireSim {ectx : Ixon.Eval.EvalCtx} {ictx : IxIR0.Ctx}
    {fuel : Nat} (ih : ∀ m, m < fuel → SimAt m)
    (hmembers : MemberCoverage ectx ictx scope.plan)
    (horacles : OracleRel ectx ictx)
    {g'' : Nat} (hg : g'' < fuel)
    {F₂ : Ixon.Eval.Frame} {block : Ixon.Address} {idx : Nat}
    {r : Recursor} {bc : Constant}
    (hresolve : ectx.resolve block = some bc)
    (hFrefs : F₂.refs = bc.refs)
    (hFmuts : F₂.selfMuts = Ixon.selfMutsOf bc.info)
    (hFsa : F₂.selfAddr = some block)
    (hmem : RecMember ectx ictx block idx r)
    {sargs : List Ixon.Eval.Value} {av : Ixon.Eval.Value}
    {indexArgs : List Ixon.Eval.Value}
    {targs : List IxIR0.Value} {av' : IxIR0.Value}
    (hlen2 : sargs.length = targs.length)
    (hslen : sargs.length = (recRulePolicy r).length)
    (hcursor : RuntimePolicyRel (ValRel ectx ictx) (recRulePolicy r)
      sargs targs)
    {cidx : Nat} {ccargs : List Ixon.Eval.Value} {tfields : List IxIR0.Value}
    (hmcS : Ixon.Eval.majorCtor (ectx.natBlock == some block) av =
      .ok (cidx, ccargs))
    (htmc : IxIR0.majorCtor (ectx.natBlock == some block) av' =
      .ok (cidx, tfields))
    (hcrel : ValsRel ectx ictx (ccargs.drop r.params.toNat) tfields)
    {v : Ixon.Eval.Value}
    (hfire : Ixon.Eval.fire ectx g'' (.recH (some block) r F₂)
      ((sargs ++ indexArgs) ++ [av]) = .ok v)
    {ρ : List IxIR0.Value} {fT aT : IxIR0.Expr} {n₁ n₂ : Nat}
    (hfv' : IxIR0.eval ictx n₁ ρ fT = .ok (.pap
      (.rec_ (Erase.memberAddr block idx)
        (r.params.toNat + r.motives.toNat + r.minors.toNat + 1)) targs))
    (hav' : IxIR0.eval ictx n₂ ρ aT = .ok av')
    (htraceF : IxIR0.ProjectionSafe.Eval ictx n₁ ρ fT (.pap
      (.rec_ (Erase.memberAddr block idx)
        (r.params.toNat + r.motives.toNat + r.minors.toNat + 1)) targs))
    (htraceA : IxIR0.ProjectionSafe.Eval ictx n₂ ρ aT av') :
    ∃ fuel' v', IxIR0.eval ictx fuel' ρ (.app fT aT) = .ok v' ∧
      ValRel ectx ictx v v' ∧
      IxIR0.ProjectionSafe.Eval ictx fuel' ρ (.app fT aT) v' := by
  obtain ⟨bc₂, trules, hres2, hienv, hrules⟩ :
      ∃ bc₂ trules,
        Ixon.Eval.resolveMut ectx block idx = .ok (bc₂, .recr r) ∧
        ictx.env (Erase.memberAddr block idx) =
          some (.recursor
            (r.params.toNat + r.motives.toNat + r.minors.toNat)
            (ectx.natBlock == some block) trules) ∧
        RulesRel ectx ictx block idx r bc₂.refs
          (Ixon.selfMutsOf bc₂.info) r.rules.toList trules.toList := by
    cases hmem with
    | mk hres2 hparams hienv hrules =>
      exact ⟨_, _, hres2, hienv, hrules⟩
  have hbc : bc₂ = bc := by
    have h1 := (resolveMut_ok hres2).1
    rw [hresolve] at h1
    injection h1 with h1'
    exact h1'.symm
  subst hbc
  have hstrict := hmembers.strict
  cases g'' with
  | zero => rw [Ixon.Eval.fire.eq_def] at hfire; simp at hfire
  | succ g₃ =>
    rw [Ixon.Eval.fire.eq_def] at hfire
    dsimp only at hfire
    rw [List.getLast?_concat] at hfire
    dsimp only at hfire
    simp only [Option.isSome_some, Bool.true_and] at hfire
    rw [hstrict.stringLiterals, Ixon.Eval.prepareStringMajor_none,
      bindOk] at hfire
    rw [not_neutral_of_majorCtor_ok hmcS] at hfire
    simp only [Bool.false_and, Bool.false_eq_true, if_false] at hfire
    obtain ⟨checked, hguard⟩ : ∃ checked,
        Ixon.Eval.guardRecMajor (some block) r.params.toNat av =
          .ok checked := by
      cases hgmajor : Ixon.Eval.guardRecMajor (some block) r.params.toNat av with
      | error err => rw [hgmajor, bindErr] at hfire; simp at hfire
      | ok checked => exact ⟨checked, rfl⟩
    rw [hguard, bindOk] at hfire
    rw [hmcS, bindOk] at hfire
    dsimp only at hfire
    split at hfire
    · simp at hfire
    · rename_i rule hrule
      split at hfire
      · simp at hfire
      · rename_i hfc
        have hfc' : ccargs.length =
            r.params.toNat + rule.fields.toNat := by
          simp at hfc
          omega
        have hslen' : sargs.length =
            r.params.toNat + r.motives.toNat + r.minors.toNat := by
          simpa using hslen
        have htake : ((sargs ++ indexArgs) ++ [av]).take
            (r.params.toNat + r.motives.toNat + r.minors.toNat) =
            sargs := by
          rw [List.append_assoc, List.take_left' hslen']
        rw [htake] at hfire
        rw [bind_ok_iff] at hfire
        obtain ⟨rhsV, hrhsV, happ⟩ := hfire
        have hruleL : r.rules.toList[cidx]? = some rule := by
          rw [arrGet?_toList]; exact hrule
        obtain ⟨trule, B, htruleL, hfields, hpeel, hpB⟩ :=
          rulesRel_lookup cidx hrules hruleL
        have htrule : trules[cidx]? = some trule := by
          rw [← arrGet?_toList]; exact htruleL
        have hcfields : (ccargs.drop r.params.toNat).length =
            rule.fields.toNat := by
          simp only [List.length_drop, hfc']
          omega
        have hlen3 : (sargs ++ ccargs.drop r.params.toNat).length =
            r.params.toNat + r.motives.toNat + r.minors.toNat +
              rule.fields.toNat := by
          simp only [List.length_append, hslen', hcfields]
        rw [← hlen3] at hpeel
        obtain ⟨gb, hgb, hbody⟩ :=
          chain_enter (sargs ++ ccargs.drop r.params.toNat)
            hpeel hrhsV happ
        have htflen : tfields.length = rule.fields.toNat := by
          rw [← valsRel_length hcrel]
          exact hcfields
        -- Build the rule-body environment from the policy cursor, then fields.
        have hbase : EnvRel ectx ictx (some (block, idx)) F₂.refs
            F₂.selfMuts F₂.selfAddr [] []
            [.pap (.rec_ (Erase.memberAddr block idx)
              (r.params.toNat + r.motives.toNat + r.minors.toNat + 1))
              []] := by
          rw [hFrefs, hFmuts, hFsa]
          exact .selfB hresolve rfl rfl hmem
        have hargs := envRel_runtimePolicyRev (recRulePolicy_slots r)
          hcursor hbase
        have hfieldsEnv := envRel_keepRev hcrel hargs
        have h3 : EnvRel ectx ictx (some (block, idx)) F₂.refs
            F₂.selfMuts F₂.selfAddr (recRuleMask r rule.fields.toNat)
            (sargs ++ ccargs.drop r.params.toNat).reverse
            (tfields.reverse ++ targs.reverse ++
              [.pap (.rec_ (Erase.memberAddr block idx)
                (r.params.toNat + r.motives.toNat + r.minors.toNat + 1))
                []]) := by
          simpa [recRuleMask, hcfields, List.reverse_append,
            List.append_assoc] using hfieldsEnv
        rw [← hFrefs, ← hFmuts, ← hFsa] at hpB
        obtain ⟨n₃, v', hv', hrel, htraceBody⟩ := ih gb (by omega) ectx F₂
          (sargs ++ ccargs.drop r.params.toNat).reverse B v
          (some (block, idx)) (recRuleMask r rule.fields.toNat)
          (tfields.reverse ++ targs.reverse ++
            [IxIR0.Value.pap (.rec_ (Erase.memberAddr block idx)
              (r.params.toNat + r.motives.toNat + r.minors.toNat + 1)) []])
          trule.rhs ictx hmembers horacles hbody hpB h3
        refine ⟨n₁ + n₂ + n₃ + 5, v', ?_, hrel, ?_⟩
        rw [IxIR0.eval.eq_def]
        dsimp only
        rw [IxIR0.eval_mono (show n₁ ≤ n₁ + n₂ + n₃ + 4 by omega) hfv',
          bindOk]
        rw [IxIR0.eval_mono (show n₂ ≤ n₁ + n₂ + n₃ + 4 by omega) hav',
          bindOk]
        rw [IxIR0.apply.eq_def]
        dsimp only
        rw [IxIR0.saturate.eq_def]
        dsimp only
        have hc2 : ((targs ++ [av']).length ==
            (r.params.toNat + r.motives.toNat + r.minors.toNat + 1)) =
            true := by
          simp only [List.length_append, List.length_cons, List.length_nil,
            beq_iff_eq]
          omega
        simp only [IxIR0.Head.arity.eq_def, hc2]
        simp only [if_true]
        rw [IxIR0.fire.eq_def]
        dsimp only
        rw [hienv]
        dsimp only
        rw [List.getLast?_concat]
        dsimp only
        rw [htmc, bindOk]
        dsimp only
        rw [htrule]
        dsimp only
        rw [if_neg (by simp [htflen, hfields])]
        rw [List.dropLast_concat]
        exact IxIR0.eval_mono (show n₃ ≤ n₁ + n₂ + n₃ + 1 by omega) hv'
        have hbodyTrace : IxIR0.ProjectionSafe.Eval ictx
            (n₁ + n₂ + n₃ + 1)
            (tfields.reverse ++ (targs ++ [av']).dropLast.reverse ++
              [.pap (.rec_ (Erase.memberAddr block idx)
                (r.params.toNat + r.motives.toNat + r.minors.toNat + 1))
                []]) trule.rhs v' := by
          simpa using htraceBody.mono_le
            (show n₃ ≤ n₁ + n₂ + n₃ + 1 by omega)
        have hfireTrace : IxIR0.ProjectionSafe.Fire ictx
            (n₁ + n₂ + n₃ + 2)
            (.rec_ (Erase.memberAddr block idx)
              (r.params.toNat + r.motives.toNat + r.minors.toNat + 1))
            (targs ++ [av']) v' :=
          .recursor hienv (by simp) htmc htrule
            (by simpa [hfields] using htflen) hbodyTrace
        have hsaturateTrace : IxIR0.ProjectionSafe.Saturate ictx
            (n₁ + n₂ + n₃ + 3)
            (.rec_ (Erase.memberAddr block idx)
              (r.params.toNat + r.motives.toNat + r.minors.toNat + 1))
            (targs ++ [av']) v' :=
          .full (by
            simp only [IxIR0.Head.arity, List.length_append,
              List.length_cons, List.length_nil]
            omega) hfireTrace
        exact .app
          (htraceF.mono_le (by omega))
          (htraceA.mono_le (by omega))
          (.pap hsaturateTrace)

private theorem simAt : ∀ fuel, SimAt fuel := by
  refine strongNat ?_
  intro fuel ih
  cases fuel with
  | zero =>
    intro ectx F env e v sc mask ρ e' ictx hmembers horacles hev hpe henv
    rw [Ixon.Eval.eval.eq_def] at hev
    simp at hev
  | succ n =>
    intro ectx F env e v sc mask ρ e' ictx hmembers horacles hev hpe henv
    have hstrict := hmembers.strict
    cases hpe with
    | var hm =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      split at hev
      · rename_i w heq
        injection hev with hv
        subst hv
        obtain ⟨v', hρ, hrel⟩ := envRel_lookup _ henv _ hm heq
        refine ⟨1, v', ?_, hrel, .var hρ⟩
        rw [IxIR0.eval.eq_def]
        dsimp only
        rw [hρ]
      · simp at hev
    | sortE =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      split at hev
      · rename_i u heq
        injection hev with hv
        subst hv
        exact ⟨1, .erased, by rw [IxIR0.eval.eq_def], .sort, .erased⟩
      · simp at hev
    | allE =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      injection hev with hv
      subst hv
      exact ⟨1, .erased, by rw [IxIR0.eval.eq_def], .pi, .erased⟩
    | lamK hnd hpb =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      injection hev with hv
      subst hv
      exact ⟨1, _, by rw [IxIR0.eval.eq_def],
        .clos (by simp [hnd]) henv hpb, .lam⟩
    | lamD hd hpb =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      injection hev with hv
      subst hv
      exact ⟨1, _, by rw [IxIR0.eval.eq_def],
        .clos (by simp [hd]) henv hpb, .lam⟩
    | letE hpv hpb =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      rename_i nd ty val body val' body'
      cases hval : Ixon.Eval.eval ectx n F env val with
      | error err => rw [hval, bindErr] at hev; simp at hev
      | ok w =>
        rw [hval, bindOk] at hev
        obtain ⟨n₁, w', hw', hrelW, htraceW⟩ :=
          ih n (by omega) ectx F env val w sc mask ρ val' ictx
            hmembers horacles hval hpv henv
        obtain ⟨n₂, v', hv', hrel, htraceBody⟩ :=
          ih n (by omega) ectx F (w :: env) body v sc (true :: mask)
            (w' :: ρ) body' ictx hmembers horacles hev hpb
              (.keep hrelW henv)
        refine ⟨n₁ + n₂ + 1, v', ?_, hrel, ?_⟩
        rw [IxIR0.eval.eq_def]
        dsimp only
        rw [IxIR0.eval_mono (show n₁ ≤ n₁ + n₂ by omega) hw', bindOk]
        exact IxIR0.eval_mono (show n₂ ≤ n₁ + n₂ by omega) hv'
        exact .letE (htraceW.mono_le (by omega))
          (htraceBody.mono_le (by omega))
    | natE hrefs hblob =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      rw [hrefs] at hev
      dsimp only at hev
      rw [hblob] at hev
      dsimp only at hev
      injection hev with hv
      subst hv
      exact ⟨1, _, by rw [IxIR0.eval.eq_def], .litNat, .lit⟩
    | strE hrefs hblob =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      rw [hrefs] at hev
      dsimp only at hev
      rw [hblob] at hev
      dsimp only at hev
      injection hev with hv
      subst hv
      exact ⟨1, _, by rw [IxIR0.eval.eq_def], .litStr, .lit⟩
    | recurS hidx hsafe =>
      rename_i block idx recIdx univIdxs
      obtain ⟨r, bc, hres, hrefs, hmuts, hsa, hmem, hslot⟩ :=
        envRel_self henv
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      rw [bind_ok_iff] at hev
      obtain ⟨uinst', _, hev⟩ := hev
      obtain ⟨bc₂, trules, hres2, hi0, hienv, hrules⟩ :
          ∃ bc₂ trules,
            Ixon.Eval.resolveMut ectx block idx = .ok (bc₂, .recr r) ∧
            r.indices.toNat = 0 ∧
            ictx.env (Erase.memberAddr block idx) =
              some (.recursor
                (r.params.toNat + r.motives.toNat + r.minors.toNat)
                (ectx.natBlock == some block) trules) ∧
            RulesRel ectx ictx block idx r bc₂.refs
              (Ixon.selfMutsOf bc₂.info) r.rules.toList
              trules.toList := by
        cases hmem with
        | mk hres2 hparams hienv hrules =>
          rename_i bc' trules
          have hbcEq : bc' = bc := by
            have h1 := (resolveMut_ok hres2).1
            rw [hres] at h1
            injection h1 with h1'
            exact h1'.symm
          cases hbcEq
          have hlook : F.selfMuts[recIdx.toNat]? = some (.recr r) := by
            rw [hidx, hmuts]
            exact (resolveMut_ok hres2).2
          have hi0 := hsafe r hlook
          exact ⟨_, _, hres2, hi0, hienv, hrules⟩
      have hbc : bc₂ = bc := by
        have h1 := (resolveMut_ok hres2).1
        rw [hres] at h1
        injection h1 with h1'
        exact h1'.symm
      subst hbc
      have hlook : F.selfMuts[recIdx.toNat]? = some (.recr r) := by
        rw [hidx, hmuts]
        exact (resolveMut_ok hres2).2
      have hi0 := hsafe r hlook
      rw [hlook] at hev
      dsimp only at hev
      rw [bind_ok_iff] at hev
      obtain ⟨_, _, hev⟩ := hev
      injection hev with hv
      subst hv
      refine ⟨1, .pap (.rec_ (Erase.memberAddr block idx)
        (r.params.toNat + r.motives.toNat + r.minors.toNat + 1)) [], ?_, ?_,
        .var hslot⟩
      · rw [IxIR0.eval.eq_def]
        dsimp only
        rw [hslot]
      · rw [hsa]
        exact .papRec hres hrefs hmuts rfl hmem hi0 rfl
          (Nat.zero_le _) (.stop (recRulePolicy r))
    | recurI hsa hresolve hrefs hlookup hidecl =>
      rename_i block recIdx univIdxs bc ind
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      rw [bind_ok_iff] at hev
      obtain ⟨uinst', _, hev⟩ := hev
      rw [hlookup] at hev
      dsimp only at hev
      rw [bind_ok_iff] at hev
      obtain ⟨_, _, hev⟩ := hev
      rw [hsa] at hev
      injection hev with hv
      subst hv
      refine ⟨2, .erased, ?_,
        .inductiveMember (resolveMut_ok hresolve).1 (resolveMut_ok hresolve).2,
        .refDefn hidecl .erased⟩
      rw [IxIR0.eval.eq_def]
      dsimp only
      rw [hidecl]
      dsimp only
      rw [IxIR0.eval.eq_def]
    | recurD hsa hresolve hrefs hmuts hunfold hplan =>
      rename_i block recIdx univIdxs bc d
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      rw [bind_ok_iff] at hev
      obtain ⟨uinst', _, hev⟩ := hev
      have hlookup : F.selfMuts[recIdx.toNat]? = some (.defn d) := by
        rw [hmuts]
        exact (resolveMut_ok hresolve).2
      rw [hlookup] at hev
      dsimp only at hev
      rw [bind_ok_iff] at hev
      obtain ⟨_, _, hev⟩ := hev
      rw [hunfold] at hev
      simp only [if_true] at hev
      have hrel := hmembers.lookup hplan
      cases hrel with
      | defn hresolve' _ hidecl _ hbody =>
        rw [hresolve] at hresolve'
        injection hresolve' with hpair
        injection hpair with hbc hd
        cases hbc
        cases hd
        have hbody' := hbody
        rw [← hrefs, ← hmuts, ← hsa] at hbody'
        obtain ⟨n₁, v', hv', hvalue, htrace⟩ :=
          ih n (by omega) ectx { F with uinst := uinst' } [] d.value v
            none [] [] _ ictx hmembers horacles hev hbody' .nil
        refine ⟨n₁ + 1, v', ?_, hvalue, .refDefn hidecl htrace⟩
        rw [IxIR0.eval.eq_def]
        dsimp only
        rw [hidecl]
        exact hv'
      | externDefn hresolve' hunfold' _ _ =>
        rw [hresolve] at hresolve'
        injection hresolve' with hpair
        injection hpair with hbc hd
        cases hbc
        cases hd
        rw [hunfold] at hunfold'
        simp at hunfold'
      | recr hmem =>
        obtain ⟨bc', hresolve'⟩ := hmem.resolve
        rw [hresolve] at hresolve'
        simp at hresolve'
    | recurO hsa hresolve hrefs hmuts hunfold hconfigured hplan =>
      rename_i block recIdx univIdxs bc d arity
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      rw [bind_ok_iff] at hev
      obtain ⟨uinst', _, hev⟩ := hev
      have hlookup : F.selfMuts[recIdx.toNat]? = some (.defn d) := by
        rw [hmuts]
        exact (resolveMut_ok hresolve).2
      rw [hlookup] at hev
      dsimp only at hev
      rw [bind_ok_iff] at hev
      obtain ⟨_, _, hev⟩ := hev
      rw [hunfold] at hev
      rw [hsa] at hev
      simp only [Bool.false_eq_true, if_false] at hev
      rw [hconfigured] at hev
      have hrel := hmembers.lookup hplan
      cases hrel with
      | defn hresolve' hunfold' _ _ _ =>
        rw [hresolve] at hresolve'
        injection hresolve' with hpair
        injection hpair with hbc hd
        cases hbc
        cases hd
        rw [hunfold] at hunfold'
        simp at hunfold'
      | externDefn hresolve' _ hconfigured' hidecl =>
        rw [hresolve] at hresolve'
        injection hresolve' with hpair
        injection hpair with hbc hd
        cases hbc
        cases hd
        rw [hconfigured] at hconfigured'
        injection hconfigured' with harity
        cases harity
        obtain ⟨targetFuel, targetValue, htarget, hvalue, htrace⟩ :=
          externSaturate_sim horacles hconfigured (Nat.zero_le _) .nil hev
        refine ⟨targetFuel + 1, targetValue, ?_, hvalue,
          .refExtern hidecl htrace⟩
        rw [IxIR0.eval.eq_def]
        dsimp only
        rw [hidecl]
        exact htarget
      | recr hmem =>
        obtain ⟨bc', hresolve'⟩ := hmem.resolve
        rw [hresolve] at hresolve'
        simp at hresolve'
    | recurR hsa hresolve hrefs hmuts hi0 hplan =>
      rename_i block recIdx univIdxs bc r
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      rw [bind_ok_iff] at hev
      obtain ⟨uinst', _, hev⟩ := hev
      have hlookup : F.selfMuts[recIdx.toNat]? = some (.recr r) := by
        rw [hmuts]
        exact (resolveMut_ok hresolve).2
      rw [hlookup] at hev
      dsimp only at hev
      rw [bind_ok_iff] at hev
      obtain ⟨_, _, hev⟩ := hev
      rw [hsa] at hev
      injection hev with hv
      subst v
      have hrel := hmembers.lookup hplan
      cases hrel with
      | defn hresolve' _ _ _ _ =>
        rw [hresolve] at hresolve'
        simp at hresolve'
      | externDefn hresolve' _ _ _ =>
        rw [hresolve] at hresolve'
        simp at hresolve'
      | recr hmem =>
        obtain ⟨bc', hresolve'⟩ := hmem.resolve
        rw [hresolve] at hresolve'
        injection hresolve' with hpair
        injection hpair with hbc hr
        subst bc'
        cases hr
        obtain ⟨trules, hienv⟩ := hmem.target
        refine ⟨1, .pap (.rec_ (Erase.memberAddr block recIdx.toNat)
            (r.params.toNat + r.motives.toNat + r.minors.toNat + 1)) [],
          ?_, ?_, .refRecursor hienv⟩
        · rw [IxIR0.eval.eq_def]
          dsimp only
          rw [hienv]
        · exact .papRec (resolveMut_ok hresolve).1 hrefs hmuts rfl hmem
            hi0 rfl (Nat.zero_le _) (.stop (recRulePolicy r))
    | prjE hpv =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      rename_i tyRef fieldIdx val val'
      cases hval : Ixon.Eval.eval ectx n F env val with
      | error err => rw [hval, bindErr] at hev; simp at hev
      | ok w =>
        rw [hval, bindOk] at hev
        obtain ⟨n₁, w', hw', hrelW, htraceW⟩ :=
          ih n (by omega) ectx F env val w sc mask ρ val' ictx
            hmembers horacles hval hpv henv
        obtain ⟨projectedInd, projectedBlockConstant, block, indIdx, cidx,
            cargs, hprojectedResolve, hw, hfield⟩ :=
          Ixon.Eval.projectValue_ok_of_strict hstrict.neutralElims hev
        subst w
        cases hrelW with
        | ctorV hshape _haddr hargs hcursor =>
          rename_i params fields a fargs
          obtain ⟨bc, ind, ct, hrm, hct, hip, hcp, hcf⟩ := hshape
          rw [hrm] at hprojectedResolve
          injection hprojectedResolve with hpair
          injection hpair with _ hind
          injection hind with hind
          subst projectedInd
          have hidxDrop : (cargs.drop params)[fieldIdx.toNat]? =
              some v := by
            rw [List.getElem?_drop]
            simpa [hip] using hfield
          obtain ⟨w0', hidx', hrel0⟩ :=
            valsRel_lookup _ hargs _ hidxDrop
          refine ⟨n₁ + 1, w0', ?_, hrel0, .proj htraceW hidx'⟩
          rw [IxIR0.eval.eq_def]
          dsimp only
          rw [IxIR0.eval_mono (Nat.le_refl n₁) hw', bindOk]
          dsimp only
          rw [hidx']
    | ctorW hspine hlt hidecl =>
      rename_i a block indIdx cidx params fields consumed
      have hshape := ctorParamSpine_shape hspine
      have haddr := ctorParamSpine_addr hspine
      obtain ⟨sargs, hlen, hv⟩ := ctorParamSpine_eval_lt hspine hlt hev
      subst v
      have hbody : params - consumed - 1 =
          params - sargs.length - 1 := by omega
      have htrace : IxIR0.ProjectionSafe.Eval ictx 1 ρ
          (.lam .many
            (Erase.lamManyN (params - consumed - 1) (.ref a)))
          (.clos .many ρ
            (Erase.lamManyN (params - sargs.length - 1) (.ref a))) := by
        rw [hbody]
        exact
          (IxIR0.ProjectionSafe.Eval.lam (ctx := ictx) (fuel := 0)
            (env := ρ) (uses := Uses.many)
            (body := Erase.lamManyN (params - sargs.length - 1) (.ref a)))
      exact ⟨1, _, htrace.run,
        .papCtorParams hshape haddr hidecl rfl (by omega), htrace⟩
    | ctorP hpos hspine hidecl =>
      rename_i a block indIdx cidx params fields
      have hshape := ctorParamSpine_shape hspine
      have haddr := ctorParamSpine_addr hspine
      obtain ⟨sargs, hlen, hresult⟩ :=
        ctorParamSpine_eval_full hpos hspine hev
      cases hresult with
      | inl hctor =>
        obtain ⟨hfields, hv⟩ := hctor
        subst fields
        subst v
        have hdrop : sargs.drop params = [] :=
          List.drop_eq_nil_of_le (by omega)
        have hargs : ValsRel ectx ictx (sargs.drop params) [] := by
          rw [hdrop]
          exact .nil
        have hcursor : PolicyRel (fun _ _ => True) IxIR0.Value.erased
            (ctorPolicy params 0) sargs [] := by
          have hc := PolicyPrefix.ctor_of_fields
            (R := fun _ _ => True) (ghost := IxIR0.Value.erased)
            (show params ≤ sargs.length by omega)
            (show sargs.length ≤ params + 0 by omega)
            (show ListRel (fun _ _ => True) (sargs.drop params) [] by
              rw [hdrop]
              exact ListRel.nil)
          simpa [hlen] using hc
        refine ⟨3, .ctor a cidx [], ?_, .ctorV hshape haddr hargs hcursor,
          .refCtor hidecl (.full (by simp [IxIR0.Head.arity]) .ctor)⟩
        rw [IxIR0.eval.eq_def]
        dsimp only
        rw [hidecl]
        dsimp only
        rw [IxIR0.saturate.eq_def]
        dsimp only
        simp [IxIR0.Head.arity]
        rw [IxIR0.fire.eq_def]
      | inr hpap =>
        obtain ⟨hfields, hv⟩ := hpap
        subst v
        have hdrop : sargs.drop params = [] :=
          List.drop_eq_nil_of_le (by omega)
        have hargs : ValsRel ectx ictx (sargs.drop params) [] := by
          rw [hdrop]
          exact .nil
        have hcursor : PolicyPrefix (fun _ _ => True) IxIR0.Value.erased
            (ctorPolicy params fields) sargs []
            (List.replicate (params + fields - sargs.length) .keep) :=
          PolicyPrefix.ctor_of_fields
            (show params ≤ sargs.length by omega)
            (show sargs.length ≤ params + fields by omega)
            (show ListRel (fun _ _ => True) (sargs.drop params) [] by
              rw [hdrop]
              exact ListRel.nil)
        refine ⟨2, .pap (.ctor a cidx fields) [], ?_,
          .papCtor hshape haddr rfl rfl (by omega) (by omega) hargs hcursor,
          .refCtor hidecl (.pending (by simp [IxIR0.Head.arity]; omega))⟩
        rw [IxIR0.eval.eq_def]
        dsimp only
        rw [hidecl]
        dsimp only
        rw [IxIR0.saturate.eq_def]
        dsimp only
        have hne : ((0 == fields) : Bool) = false := by
          rw [beq_eq_false_iff_ne]
          omega
        simp only [IxIR0.Head.arity.eq_def, List.length_nil, hne]
        simp
    | ref hrefs hcov =>
      rename_i refIdx univIdxs a
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      rw [hrefs] at hev
      dsimp only at hev
      rw [bind_ok_iff] at hev
      obtain ⟨uinst', _, hev⟩ := hev
      cases n with
      | zero => rw [Ixon.Eval.evalRef.eq_def] at hev; simp at hev
      | succ g =>
        rw [Ixon.Eval.evalRef.eq_def] at hev
        dsimp only at hev
        cases hcov with
        | defn hres hinfo hunf hidecl _ hpe' =>
          rw [hres] at hev
          dsimp only at hev
          rw [hinfo] at hev
          dsimp only at hev
          rw [bind_ok_iff] at hev
          obtain ⟨_, _, hev⟩ := hev
          rw [hunf] at hev
          simp at hev
          obtain ⟨n₁, v', hv', hrel, htraceBody⟩ :=
            ih g (by omega) ectx _ [] _ v none [] [] _ ictx
              hmembers horacles hev hpe' .nil
          refine ⟨n₁ + 1, v', ?_, hrel, .refDefn hidecl htraceBody⟩
          rw [IxIR0.eval.eq_def]
          dsimp only
          rw [hidecl]
          exact hv'
        | defnProj hres hinfo hrm hunf hidecl hmember _ hpe' =>
          rw [hres] at hev
          dsimp only at hev
          rw [hinfo] at hev
          dsimp only at hev
          rw [hrm] at hev
          dsimp only at hev
          rw [bind_ok_iff] at hev
          obtain ⟨_, _, hev⟩ := hev
          rw [hunf] at hev
          simp at hev
          obtain ⟨n₁, v', hv', hrel, htraceBody⟩ :=
            ih g (by omega) ectx _ [] _ v none [] [] _ ictx
              hmembers horacles hev hpe' .nil
          refine ⟨n₁ + 2, v', ?_, hrel,
            .refDefn hidecl (.refDefn hmember htraceBody)⟩
          rw [IxIR0.eval.eq_def]
          dsimp only
          rw [hidecl]
          dsimp only
          rw [IxIR0.eval.eq_def]
          dsimp only
          rw [hmember]
          exact hv'
        | externDefn hres hinfo hunf hconfigured hidecl =>
          rw [hres] at hev
          dsimp only at hev
          rw [hinfo] at hev
          dsimp only at hev
          rw [bind_ok_iff] at hev
          obtain ⟨_, _, hev⟩ := hev
          rw [hunf] at hev
          rw [hconfigured] at hev
          obtain ⟨targetFuel, targetValue, htarget, hrel, htrace⟩ :=
            externSaturate_sim horacles hconfigured (Nat.zero_le _) .nil hev
          refine ⟨targetFuel + 1, targetValue, ?_, hrel,
            .refExtern hidecl htrace⟩
          rw [IxIR0.eval.eq_def]
          dsimp only
          rw [hidecl]
          exact htarget
        | externDefnProj hres hinfo hrm hunf hconfigured hidecl hmember _ =>
          rw [hres] at hev
          dsimp only at hev
          rw [hinfo] at hev
          dsimp only at hev
          rw [hrm] at hev
          dsimp only at hev
          rw [bind_ok_iff] at hev
          obtain ⟨_, _, hev⟩ := hev
          rw [hunf] at hev
          rw [hconfigured] at hev
          obtain ⟨targetFuel, targetValue, htarget, hrel, htrace⟩ :=
            externSaturate_sim horacles hconfigured (Nat.zero_le _) .nil hev
          refine ⟨targetFuel + 2, targetValue, ?_, hrel,
            .refDefn hidecl (.refExtern hmember htrace)⟩
          rw [IxIR0.eval.eq_def]
          dsimp only
          rw [hidecl]
          dsimp only
          rw [IxIR0.eval.eq_def]
          dsimp only
          rw [hmember]
          exact htarget
        | externAxio hres hinfo hconfigured hidecl =>
          rw [hres] at hev
          dsimp only at hev
          rw [hinfo] at hev
          dsimp only at hev
          rw [bind_ok_iff] at hev
          obtain ⟨_, _, hev⟩ := hev
          rw [hconfigured] at hev
          obtain ⟨targetFuel, targetValue, htarget, hrel, htrace⟩ :=
            externSaturate_sim horacles hconfigured (Nat.zero_le _) .nil hev
          refine ⟨targetFuel + 1, targetValue, ?_, hrel,
            .refExtern hidecl htrace⟩
          rw [IxIR0.eval.eq_def]
          dsimp only
          rw [hidecl]
          exact htarget
        | ctor hres hinfo hshape hidecl =>
          rename_i c p fields
          obtain ⟨bc, ind, ct, hrm, hct, hip, hcp, hcf⟩ := hshape
          rw [hres] at hev
          dsimp only at hev
          rw [hinfo] at hev
          dsimp only at hev
          rw [hrm] at hev
          dsimp only at hev
          rw [hct] at hev
          dsimp only at hev
          rw [bind_ok_iff] at hev
          obtain ⟨_, _, hev⟩ := hev
          cases g with
          | zero => rw [Ixon.Eval.saturate.eq_def] at hev; simp at hev
          | succ g' =>
            rw [Ixon.Eval.saturate.eq_def] at hev
            simp only [Ixon.Eval.Head.arity?] at hev
            rw [hcp, hcf] at hev
            simp only [List.length_nil, Nat.zero_add] at hev
            cases fields with
            | zero =>
              simp at hev
              cases g' with
              | zero => rw [Ixon.Eval.fire.eq_def] at hev; simp at hev
              | succ g'' =>
                rw [Ixon.Eval.fire.eq_def] at hev
                dsimp only at hev
                injection hev with hv
                subst hv
                refine ⟨3, .ctor a p.cidx.toNat [], ?_,
                  .ctorV ⟨bc, ind, ct, hrm, hct, hip, hcp, hcf⟩
                    ⟨c, p, hres, hinfo, rfl, rfl, rfl⟩ .nil
                    (.stop []),
                  .refCtor hidecl (.full (by simp [IxIR0.Head.arity]) .ctor)⟩
                rw [IxIR0.eval.eq_def]
                dsimp only
                rw [hidecl]
                dsimp only
                rw [IxIR0.saturate.eq_def]
                dsimp only
                simp [IxIR0.Head.arity]
                rw [IxIR0.fire.eq_def]
            | succ f' =>
              simp at hev
              subst hev
              refine ⟨2, .pap (.ctor a p.cidx.toNat (f' + 1)) [], ?_,
                .papCtor ⟨bc, ind, ct, hrm, hct, hip, hcp, hcf⟩
                  ⟨c, p, hres, hinfo, rfl, rfl, rfl⟩ (by simp) rfl
                  (by simp) (by simp) .nil
                  (by simpa [ctorPolicy] using
                    (PolicyPrefix.stop (R := fun _ _ => True)
                      (ghost := IxIR0.Value.erased)
                      (ctorPolicy 0 (f' + 1)))),
                .refCtor hidecl (.pending (by simp [IxIR0.Head.arity]))⟩
              rw [IxIR0.eval.eq_def]
              dsimp only
              rw [hidecl]
              dsimp only
              rw [IxIR0.saturate.eq_def]
              dsimp only
              simp [IxIR0.Head.arity]
        | tyf hres hinfo hidecl =>
          rw [hres] at hev
          dsimp only at hev
          rw [hinfo] at hev
          dsimp only at hev
          split at hev
          · rw [bind_ok_iff] at hev
            obtain ⟨_, _, hev⟩ := hev
            injection hev with hv
            subst hv
            refine ⟨3, .erased, ?_, .inductiveType hres hinfo,
              .refDefn hidecl (.erased)⟩
            rw [IxIR0.eval.eq_def]
            dsimp only
            rw [hidecl]
            dsimp only
            rw [IxIR0.eval.eq_def]
          · simp at hev
          · simp at hev
        | quot hres hinfo hkind hidecl howned =>
          rename_i c q result
          rw [hres] at hev
          dsimp only at hev
          rw [hinfo] at hev
          dsimp only at hev
          rw [bind_ok_iff] at hev
          obtain ⟨_, _, hev⟩ := hev
          rw [hkind] at hev
          dsimp only at hev
          cases hqkind : q.kind with
          | type =>
            rw [hqkind] at hev
            rw [show ((Ixon.QuotKind.type == Ixon.QuotKind.type) : Bool) =
              true by rfl] at hev
            simp only [if_true] at hev
            injection hev with hv
            subst hv
            rw [hqkind] at hidecl
            refine ⟨2, .erased, ?_, .quotType,
              .refDefn hidecl .erased⟩
            rw [IxIR0.eval.eq_def]
            dsimp only
            rw [hidecl]
            dsimp only
            simp [Erase.quotientBody, IxIR0.eval]
          | ctor =>
            rw [hqkind] at hev
            rw [show ((Ixon.QuotKind.ctor == Ixon.QuotKind.ctor) : Bool) =
              true by rfl] at hev
            simp only [if_true] at hev
            injection hev with hv
            subst hv
            rw [hqkind] at hidecl
            refine ⟨2, _, ?_, .papQuot (by simp)
              (by simp [Ixon.Eval.quotArity]) .nil,
              .refDefn hidecl ?_⟩
            · rw [IxIR0.eval.eq_def]
              dsimp only
              rw [hidecl]
              dsimp only
              simp [Erase.quotientBody, Erase.quotMkBody,
                Erase.lamManyN, Ixon.Eval.quotArity, IxIR0.eval]
            · simpa [Erase.quotientBody, Erase.quotMkBody,
                Erase.lamManyN, Ixon.Eval.quotArity] using
                (IxIR0.ProjectionSafe.Eval.lam (ctx := ictx)
                  (fuel := 0) (env := ([] : List IxIR0.Value))
                  (uses := Uses.many)
                  (body := Erase.lamManyN 2 (Erase.quotientCore .ctor)))
          | lift =>
            rw [hqkind] at hev
            rw [show ((Ixon.QuotKind.lift == Ixon.QuotKind.lift) : Bool) =
              true by rfl] at hev
            simp only [if_true] at hev
            injection hev with hv
            subst hv
            rw [hqkind] at hidecl
            refine ⟨2, _, ?_, .papQuot (by simp)
              (by simp [Ixon.Eval.quotArity]) .nil,
              .refDefn hidecl ?_⟩
            · rw [IxIR0.eval.eq_def]
              dsimp only
              rw [hidecl]
              dsimp only
              simp [Erase.quotientBody, Erase.quotLiftBody,
                Erase.lamManyN, Ixon.Eval.quotArity, IxIR0.eval]
            · simpa [Erase.quotientBody, Erase.quotLiftBody,
                Erase.lamManyN, Ixon.Eval.quotArity] using
                (IxIR0.ProjectionSafe.Eval.lam (ctx := ictx)
                  (fuel := 0) (env := ([] : List IxIR0.Value))
                  (uses := Uses.many)
                  (body := Erase.lamManyN 5 (Erase.quotientCore .lift)))
          | ind =>
            rw [hqkind] at hev
            rw [show ((Ixon.QuotKind.ind == Ixon.QuotKind.ind) : Bool) =
              true by rfl] at hev
            simp only [if_true] at hev
            injection hev with hv
            subst hv
            rw [hqkind] at hidecl
            refine ⟨2, _, ?_, .papQuot (by simp)
              (by simp [Ixon.Eval.quotArity]) .nil,
              .refDefn hidecl ?_⟩
            · rw [IxIR0.eval.eq_def]
              dsimp only
              rw [hidecl]
              dsimp only
              simp [Erase.quotientBody, Erase.quotIndBody,
                Erase.lamManyN, Ixon.Eval.quotArity, IxIR0.eval]
            · simpa [Erase.quotientBody, Erase.quotIndBody,
                Erase.lamManyN, Ixon.Eval.quotArity] using
                (IxIR0.ProjectionSafe.Eval.lam (ctx := ictx)
                  (fuel := 0) (env := ([] : List IxIR0.Value))
                  (uses := Uses.many)
                  (body := Erase.lamManyN 4 (Erase.quotientCore .ind)))
        | recrP hres hinfo hrm hi0 hidecl hmem =>
          rename_i c p bc r
          rw [hres] at hev
          dsimp only at hev
          rw [hinfo] at hev
          dsimp only at hev
          rw [hrm] at hev
          dsimp only at hev
          rw [bind_ok_iff] at hev
          obtain ⟨_, _, hev⟩ := hev
          injection hev with hv
          subst hv
          obtain ⟨bc₂, trules, hres2, hi0, hienv, hrules⟩ :
              ∃ bc₂ trules,
                Ixon.Eval.resolveMut ectx p.block p.idx.toNat =
                  .ok (bc₂, .recr r) ∧
                r.indices.toNat = 0 ∧
                ictx.env (Erase.memberAddr p.block p.idx.toNat) =
                  some (.recursor
                    (r.params.toNat + r.motives.toNat + r.minors.toNat)
                    (ectx.natBlock == some p.block) trules) ∧
                RulesRel ectx ictx p.block p.idx.toNat r bc₂.refs
                  (Ixon.selfMutsOf bc₂.info) r.rules.toList
                  trules.toList := by
            cases hmem with
            | mk hres2 hparams hienv hrules =>
              exact ⟨_, _, hres2, hi0, hienv, hrules⟩
          have hbc : bc₂ = bc := by
            have h1 := (resolveMut_ok hres2).1
            rw [(resolveMut_ok hrm).1] at h1
            injection h1 with h1'
            exact h1'.symm
          subst hbc
          refine ⟨3, .pap (.rec_ (Erase.memberAddr p.block p.idx.toNat)
            (r.params.toNat + r.motives.toNat + r.minors.toNat + 1)) [], ?_, ?_,
            .refDefn hidecl (.refRecursor hienv)⟩
          · rw [IxIR0.eval.eq_def]
            dsimp only
            rw [hidecl]
            dsimp only
            rw [IxIR0.eval.eq_def]
            dsimp only
            rw [hienv]
          · exact .papRec (resolveMut_ok hrm).1 rfl rfl rfl hmem hi0 rfl
              (Nat.zero_le _)
              (.stop (recRulePolicy r))
    | appG hspine hj hpf =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      rename_i f a f' r j
      cases hf : Ixon.Eval.eval ectx n F env f with
      | error err => rw [hf, bindErr] at hev; simp at hev
      | ok fv =>
        rw [hf, bindOk] at hev
        cases ha : Ixon.Eval.eval ectx n F env a with
        | error err => rw [ha, bindErr] at hev; simp at hev
        | ok av =>
          rw [ha, bindOk] at hev
          obtain ⟨n₁, fv', hfv', hrelF, htraceF⟩ :=
            ih n (by omega) ectx F env f fv sc mask ρ f' ictx
              hmembers horacles hf hpf henv
          obtain ⟨ob, F₂, sargs, hfv, hlen⟩ := recSpine_eval hspine hf
          subst hfv
          cases hrelF with
          | papRec hresolve hFrefs hFmuts hFsa hmem hi0 hlen2 hle hcursor =>
            rename_i block idx bc₃ targs rest
            cases n with
            | zero => rw [Ixon.Eval.apply.eq_def] at hev; simp at hev
            | succ g =>
              rw [Ixon.Eval.apply.eq_def] at hev
              dsimp only at hev
              cases g with
              | zero => rw [Ixon.Eval.saturate.eq_def] at hev; simp at hev
              | succ g' =>
                rw [Ixon.Eval.saturate.eq_def] at hev
                simp only [Ixon.Eval.Head.arity?] at hev
                obtain ⟨hjlt, hget⟩ := getElem?_eq_some_iff.mp hj
                have hdrop := List.drop_eq_getElem_cons
                  (l := recRulePolicy r) hjlt
                rw [hget] at hdrop
                have hrest := hcursor.remaining_eq_drop
                rw [hlen, hdrop] at hrest
                rw [hrest] at hcursor
                have hcursor' := hcursor.append_ghost
                  (sarg := av) (targ := IxIR0.Value.erased)
                have hi0 := recSpine_shape hspine
                have hne : ((sargs ++ [av]).length ==
                    Ixon.Eval.recArity r) = false := by
                  rw [beq_eq_false_iff_ne]
                  simp only [List.length_append, List.length_cons,
                    List.length_nil, Ixon.Eval.recArity, hi0, Nat.add_zero,
                    hlen]
                  rw [recRulePolicy_length] at hjlt
                  omega
                rw [hne] at hev
                simp at hev
                subst hev
                refine ⟨n₁ + 4, .pap (.rec_ (Erase.memberAddr block idx)
                  (r.params.toNat + r.motives.toNat + r.minors.toNat + 1))
                  (targs ++ [IxIR0.Value.erased]), ?_, ?_, ?_⟩
                · rw [IxIR0.eval.eq_def]
                  dsimp only
                  rw [IxIR0.eval_mono (show n₁ ≤ n₁ + 3 by omega) hfv',
                    bindOk]
                  have hbox : IxIR0.eval ictx (n₁ + 3) ρ .erased =
                      .ok .erased := by rw [IxIR0.eval.eq_def]
                  rw [hbox, bindOk]
                  rw [IxIR0.apply.eq_def]
                  dsimp only
                  rw [IxIR0.saturate.eq_def]
                  dsimp only
                  have hne2 : ((targs ++ [IxIR0.Value.erased]).length ==
                      (r.params.toNat + r.motives.toNat +
                        r.minors.toNat + 1)) = false := by
                    rw [beq_eq_false_iff_ne]
                    simp only [List.length_append, List.length_cons,
                      List.length_nil, ← hlen2, hlen]
                    rw [recRulePolicy_length] at hjlt
                    omega
                  simp only [IxIR0.Head.arity.eq_def, hne2]
                  simp
                · refine .papRec hresolve hFrefs hFmuts hFsa hmem hi0
                    (by simp [hlen2])
                    (by simpa [hlen] using Nat.succ_le_of_lt hjlt) hcursor'
                · have hsaturate : IxIR0.ProjectionSafe.Saturate ictx
                      (n₁ + 2)
                      (.rec_ (Erase.memberAddr block idx)
                        (r.params.toNat + r.motives.toNat +
                          r.minors.toNat + 1))
                      (targs ++ [.erased])
                      (.pap (.rec_ (Erase.memberAddr block idx)
                        (r.params.toNat + r.motives.toNat +
                          r.minors.toNat + 1)) (targs ++ [.erased])) :=
                    .pending (by
                      simp only [IxIR0.Head.arity, List.length_append,
                        List.length_cons, List.length_nil, ← hlen2, hlen]
                      rw [recRulePolicy_length] at hjlt
                      omega)
                  exact .app (htraceF.mono_le (by omega)) .erased
                    (.pap hsaturate)
          | papRecI _ _ _ _ _ hipos _ _ =>
            have hi0 := recSpine_shape hspine
            omega
          | papRecIW _ _ _ _ _ hipos _ _ _ =>
            have hi0 := recSpine_shape hspine
            omega
    | appDG hspine hdrop hpf =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      rename_i f a f' uses domain body
      cases hf : Ixon.Eval.eval ectx n F env f with
      | error err => rw [hf, bindErr] at hev; simp at hev
      | ok fv =>
        rw [hf, bindOk] at hev
        cases ha : Ixon.Eval.eval ectx n F env a with
        | error err => rw [ha, bindErr] at hev; simp at hev
        | ok av =>
          rw [ha, bindOk] at hev
          obtain ⟨n₁, fv', hfv', hrelF, htraceF⟩ :=
            ih n (by omega) ectx F env f fv sc mask ρ f' ictx
              hmembers horacles hf hpf henv
          obtain ⟨closureFrame, closureEnv, hfv⟩ :=
            defSpine_eval_clos hspine rfl hf
          subst fv
          cases hrelF with
          | clos hdropC henvC hbodyC =>
            rename_i scC maskC bC uC' ρC bodyC'
            have hbC : bC = false := by
              simpa [hdrop] using hdropC
            have hbodyC' : PErase ectx ictx scC closureFrame.refs
                closureFrame.selfMuts closureFrame.selfAddr
                (false :: maskC) body bodyC' := by
              rw [← hbC]
              exact hbodyC
            cases n with
            | zero => rw [Ixon.Eval.apply.eq_def] at hev; simp at hev
            | succ bodyFuel =>
              rw [Ixon.Eval.apply.eq_def] at hev
              dsimp only at hev
              obtain ⟨n₂, v', hv', hrel, htraceBody⟩ :=
                ih bodyFuel (by omega) ectx closureFrame
                  (av :: closureEnv) body v scC
                  (false :: maskC) (.erased :: ρC) bodyC' ictx hmembers
                  horacles hev hbodyC' (.drop henvC)
              refine ⟨n₁ + n₂ + 2, v', ?_, hrel, ?_⟩
              rw [IxIR0.eval.eq_def]
              dsimp only
              rw [IxIR0.eval_mono (show n₁ ≤ n₁ + n₂ + 1 by omega)
                hfv', bindOk]
              have herased : IxIR0.eval ictx (n₁ + n₂ + 1) ρ .erased =
                  .ok .erased := by
                rw [IxIR0.eval.eq_def]
              rw [herased, bindOk]
              rw [IxIR0.apply.eq_def]
              dsimp only
              exact IxIR0.eval_mono (show n₂ ≤ n₁ + n₂ by omega) hv'
              exact .app
                (htraceF.mono_le (by omega))
                .erased
                (.clos (htraceBody.mono_le (by omega)))
    | recP hspine =>
      rename_i r
      obtain ⟨n₁, block, idx, F₂, bc, sargs, targs, hv, hv', htrace,
          hresolve,
          hFrefs, hFmuts, hFsa, hmem, hipos, hcursor⟩ :=
        recEraseSpine_sim ih hmembers horacles hspine (by omega) hev henv
      obtain ⟨ruleArgs, indexArgs, hsargs, hindices, hfront⟩ :
          ∃ ruleArgs indexArgs,
            sargs = ruleArgs ++ indexArgs ∧
            indexArgs.length = r.indices.toNat ∧
            RuntimePolicyRel (ValRel ectx ictx) (recRulePolicy r)
              ruleArgs targs := by
        simpa [recPolicy] using
          (hcursor.split_suffix_drops
            (policies := recRulePolicy r) (n := r.indices.toNat))
      subst v
      rw [hsargs]
      exact ⟨n₁, _, hv', .papRecI hresolve hFrefs hFmuts hFsa hmem
        hipos hindices hfront, htrace⟩
    | recW hspine hremaining =>
      rename_i e' r remaining
      obtain ⟨n₁, block, idx, F₂, bc, sargs, targs, hv, hv', htrace,
          hresolve, hFrefs, hFmuts, hFsa, hmem, hipos, hcursor⟩ :=
        recEraseSpine_sim ih hmembers horacles hspine (by omega) hev henv
      subst v
      cases remaining with
      | zero => omega
      | succ remaining =>
        let targetPap : IxIR0.Value :=
          .pap (.rec_ (Erase.memberAddr block idx)
            (r.params.toNat + r.motives.toNat + r.minors.toNat + 1)) targs
        have hbodyTrace : IxIR0.ProjectionSafe.Eval ictx (n₁ + 1)
            (targetPap :: ρ)
            (Erase.lamManyN (remaining + 1) (.var (remaining + 1)))
            (.clos .many (targetPap :: ρ)
              (Erase.lamManyN remaining (.var (remaining + 1)))) := by
          simpa [Erase.lamManyN] using
            (IxIR0.ProjectionSafe.Eval.lam (ctx := ictx) (fuel := n₁)
              (env := targetPap :: ρ) (uses := Uses.many)
              (body := Erase.lamManyN remaining (.var (remaining + 1))))
        have htargetTrace : IxIR0.ProjectionSafe.Eval ictx (n₁ + 2) ρ
            (Erase.captureThenIgnoreN (remaining + 1) e')
            (.clos .many (targetPap :: ρ)
              (Erase.lamManyN remaining (.var (remaining + 1)))) := by
          simpa [Erase.captureThenIgnoreN] using
            (IxIR0.ProjectionSafe.Eval.letE
              (htrace.mono_le (by omega)) hbodyTrace)
        refine ⟨n₁ + 2, _, htargetTrace.run, ?_, htargetTrace⟩
        simpa [targetPap] using
          (ValRel.papRecIW hresolve hFrefs hFmuts hFsa hmem hipos
            (show 0 < remaining + 1 by omega) (by simp) hcursor
            : ValRel ectx ictx
                (.papV (.recH (some block) r F₂) sargs)
                (.clos .many
                  ([].reverse ++ targetPap :: ρ)
                  (Erase.lamManyN ((remaining + 1) - 1)
                    (.var (remaining + 1)))))
    | app hpf hpa =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      rename_i fS aS fT aT
      cases hf : Ixon.Eval.eval ectx n F env fS with
      | error err => rw [hf, bindErr] at hev; simp at hev
      | ok fv =>
        rw [hf, bindOk] at hev
        cases ha : Ixon.Eval.eval ectx n F env aS with
        | error err => rw [ha, bindErr] at hev; simp at hev
        | ok av =>
          rw [ha, bindOk] at hev
          obtain ⟨n₁, fv', hfv', hrelF, htraceF⟩ :=
            ih n (by omega) ectx F env fS fv sc mask ρ fT ictx
              hmembers horacles hf hpf henv
          obtain ⟨n₂, av', hav', hrelA, htraceA⟩ :=
            ih n (by omega) ectx F env aS av sc mask ρ aT ictx
              hmembers horacles ha hpa henv
          cases hrelF with
          | sort =>
            rw [Ixon.Eval.apply.eq_def] at hev
            cases n <;> simp at hev
          | pi =>
            rw [Ixon.Eval.apply.eq_def] at hev
            cases n <;> simp at hev
          | litNat =>
            rw [Ixon.Eval.apply.eq_def] at hev
            cases n <;> simp at hev
          | litStr =>
            rw [Ixon.Eval.apply.eq_def] at hev
            cases n <;> simp at hev
          | ctorV _ _ _ _ =>
            rw [Ixon.Eval.apply.eq_def] at hev
            cases n <;> simp at hev
          | quotV _ =>
            rw [Ixon.Eval.apply.eq_def] at hev
            cases n <;> simp at hev
          | quotType =>
            rename_i address sourceArgs
            have hvalue : v = .papV (.quotH address .type)
                (sourceArgs ++ [av]) := by
              cases n with
              | zero => rw [Ixon.Eval.apply.eq_def] at hev; simp at hev
              | succ g =>
                rw [Ixon.Eval.apply.eq_def] at hev
                dsimp only at hev
                cases g with
                | zero => rw [Ixon.Eval.saturate.eq_def] at hev; simp at hev
                | succ g' =>
                  rw [Ixon.Eval.saturate.eq_def] at hev
                  dsimp only at hev
                  simp only [Ixon.Eval.Head.arity?, Ixon.Eval.quotArity] at hev
                  cases hcmp : (sourceArgs ++ [av]).length == 2 with
                  | false => rw [hcmp] at hev; simpa using hev.symm
                  | true =>
                    rw [hcmp] at hev
                    simp only [if_true] at hev
                    cases g' with
                    | zero => rw [Ixon.Eval.fire.eq_def] at hev; simp at hev
                    | succ g'' =>
                      rw [Ixon.Eval.fire.eq_def] at hev
                      dsimp only at hev
                      injection hev with hv
                      exact hv.symm
            subst v
            refine ⟨n₁ + n₂ + 3, .erased, ?_, .quotType, ?_⟩
            · rw [IxIR0.eval.eq_def]
              dsimp only
              rw [IxIR0.eval_mono (show n₁ ≤ n₁ + n₂ + 2 by omega)
                hfv', bindOk]
              rw [IxIR0.eval_mono (show n₂ ≤ n₁ + n₂ + 2 by omega)
                hav', bindOk]
              rw [IxIR0.apply.eq_def]
            · exact .app
                (htraceF.mono_le (by omega))
                (htraceA.mono_le (by omega))
                .erased
          | papQuot hkind hlt hargs =>
            rename_i address kind sourceArgs targetArgs
            have hlength := valsRel_length hargs
            cases n with
            | zero => rw [Ixon.Eval.apply.eq_def] at hev; simp at hev
            | succ g =>
              rw [Ixon.Eval.apply.eq_def] at hev
              dsimp only at hev
              cases g with
              | zero => rw [Ixon.Eval.saturate.eq_def] at hev; simp at hev
              | succ g' =>
                rw [Ixon.Eval.saturate.eq_def] at hev
                dsimp only at hev
                simp only [Ixon.Eval.Head.arity?] at hev
                cases hcmp : (sourceArgs ++ [av]).length ==
                    Ixon.Eval.quotArity kind with
                | false =>
                  rw [hcmp] at hev
                  simp only [Bool.false_eq_true, if_false] at hev
                  injection hev with hvalue
                  subst hvalue
                  have hlt' : (sourceArgs ++ [av]).length <
                      Ixon.Eval.quotArity kind := by
                    have hne := ne_of_beq_false hcmp
                    simp only [List.length_append, List.length_cons,
                      List.length_nil] at hne ⊢
                    omega
                  have hargs' : ValsRel ectx ictx (sourceArgs ++ [av])
                      (targetArgs ++ [av']) :=
                    valsRel_append hargs hrelA
                  have hexponent :
                      Ixon.Eval.quotArity kind - sourceArgs.length - 1 =
                        (Ixon.Eval.quotArity kind -
                          (sourceArgs ++ [av]).length - 1) + 1 := by
                    cases kind <;>
                      simp_all [Ixon.Eval.quotArity] <;> omega
                  have hbodyTrace : IxIR0.ProjectionSafe.Eval ictx 1
                      (av' :: targetArgs.reverse)
                      (Erase.lamManyN
                        (Ixon.Eval.quotArity kind - sourceArgs.length - 1)
                        (Erase.quotientCore kind))
                      (.clos .many (targetArgs ++ [av']).reverse
                        (Erase.lamManyN
                          (Ixon.Eval.quotArity kind -
                            (sourceArgs ++ [av]).length - 1)
                          (Erase.quotientCore kind))) := by
                    rw [hexponent]
                    simpa [Erase.lamManyN] using
                      (IxIR0.ProjectionSafe.Eval.lam (ctx := ictx)
                        (fuel := 0) (env := av' :: targetArgs.reverse)
                        (uses := Uses.many)
                        (body := Erase.lamManyN
                          (Ixon.Eval.quotArity kind -
                            (sourceArgs ++ [av]).length - 1)
                          (Erase.quotientCore kind)))
                  have happlyTrace : IxIR0.ProjectionSafe.Apply ictx 2
                      (.clos .many targetArgs.reverse
                        (Erase.lamManyN
                          (Ixon.Eval.quotArity kind - sourceArgs.length - 1)
                          (Erase.quotientCore kind))) av'
                      (.clos .many (targetArgs ++ [av']).reverse
                        (Erase.lamManyN
                          (Ixon.Eval.quotArity kind -
                            (sourceArgs ++ [av]).length - 1)
                          (Erase.quotientCore kind))) :=
                    .clos hbodyTrace
                  have htargetTrace : IxIR0.ProjectionSafe.Eval ictx
                      (n₁ + n₂ + 3) ρ (.app fT aT)
                      (.clos .many (targetArgs ++ [av']).reverse
                        (Erase.lamManyN
                          (Ixon.Eval.quotArity kind -
                            (sourceArgs ++ [av]).length - 1)
                          (Erase.quotientCore kind))) :=
                    .app (htraceF.mono_le (by omega))
                      (htraceA.mono_le (by omega))
                      (happlyTrace.mono_le (by omega))
                  exact ⟨_, _, htargetTrace.run,
                    .papQuot hkind hlt' hargs', htargetTrace⟩
                | true =>
                  rw [hcmp] at hev
                  simp only [if_true] at hev
                  cases g' with
                  | zero => rw [Ixon.Eval.fire.eq_def] at hev; simp at hev
                  | succ g'' =>
                    rw [Ixon.Eval.fire.eq_def] at hev
                    dsimp only at hev
                    cases kind with
                    | type => exact absurd rfl hkind
                    | ctor =>
                      have hsourceLength : sourceArgs.length = 2 := by
                        have heq := (beq_iff_eq).mp hcmp
                        simp only [List.length_append, List.length_cons,
                          List.length_nil, Ixon.Eval.quotArity] at heq
                        omega
                      have hrepresentative :
                          (sourceArgs ++ [av])[2]? = some av := by
                        rw [← hsourceLength]
                        exact List.getElem?_concat_length
                      rw [hrepresentative] at hev
                      injection hev with hvalue
                      subst hvalue
                      have hbodyTrace : IxIR0.ProjectionSafe.Eval ictx 1
                          (av' :: targetArgs.reverse)
                          (Erase.lamManyN
                            (Ixon.Eval.quotArity .ctor -
                              sourceArgs.length - 1)
                            (Erase.quotientCore .ctor)) av' := by
                        simpa [hsourceLength, Ixon.Eval.quotArity,
                          Erase.lamManyN, Erase.quotientCore] using
                          (IxIR0.ProjectionSafe.Eval.var (ctx := ictx)
                            (fuel := 0)
                            (env := av' :: targetArgs.reverse)
                            (index := 0) (value := av') rfl)
                      have happlyTrace : IxIR0.ProjectionSafe.Apply ictx 2
                          (.clos .many targetArgs.reverse
                            (Erase.lamManyN
                              (Ixon.Eval.quotArity .ctor -
                                sourceArgs.length - 1)
                              (Erase.quotientCore .ctor))) av' av' :=
                        .clos hbodyTrace
                      have htargetTrace : IxIR0.ProjectionSafe.Eval ictx
                          (n₁ + n₂ + 3) ρ (.app fT aT) av' :=
                        .app (htraceF.mono_le (by omega))
                          (htraceA.mono_le (by omega))
                          (happlyTrace.mono_le (by omega))
                      exact ⟨_, _, htargetTrace.run, .quotV hrelA,
                        htargetTrace⟩
                    | lift =>
                      have hsourceLength : sourceArgs.length = 5 := by
                        have heq := (beq_iff_eq).mp hcmp
                        simp only [List.length_append, List.length_cons,
                          List.length_nil, Ixon.Eval.quotArity] at heq
                        omega
                      have hfunctionBound : 3 < sourceArgs.length := by omega
                      let sourceFunction := sourceArgs[3]
                      have hfunction : sourceArgs[3]? =
                          some sourceFunction :=
                        List.getElem?_eq_getElem hfunctionBound
                      have hfunction' : (sourceArgs ++ [av])[3]? =
                          some sourceFunction := by
                        rw [List.getElem?_append_left hfunctionBound]
                        exact hfunction
                      have hquotient : (sourceArgs ++ [av])[5]? = some av := by
                        rw [← hsourceLength]
                        exact List.getElem?_concat_length
                      rw [hfunction', hquotient] at hev
                      simp only at hev
                      cases hrep : Ixon.Eval.quotientRep? av with
                      | none => rw [hrep] at hev; contradiction
                      | some representative =>
                        rw [hrep] at hev
                        dsimp only at hev
                        obtain ⟨targetFunction, htargetFunction,
                            hfunctionRel⟩ :=
                          valsRel_lookup 3 hargs sourceFunction hfunction
                        have hrepresentativeRel :
                            ValRel ectx ictx representative av' :=
                          quotientRep_valRel hrelA hrep
                        obtain ⟨targetFuel, targetResult, htargetApply,
                            hresultRel, htargetApplyTrace⟩ :=
                          applyRel_sim ih hmembers horacles (by omega) hev
                            hfunctionRel
                            hrepresentativeRel
                        have htargetLength : targetArgs.length = 5 := by
                          omega
                        have hreverse : targetArgs.reverse[1]? =
                            some targetFunction := by
                          rw [List.getElem?_reverse'
                            (l := targetArgs) (i := 1) (j := 3) (by omega)]
                          exact htargetFunction
                        have hlookup :
                            (av' :: targetArgs.reverse)[2]? =
                              some targetFunction := by simpa using hreverse
                        have hcoreTrace : IxIR0.ProjectionSafe.Eval ictx
                            (targetFuel + 2) (av' :: targetArgs.reverse)
                            (Erase.quotientCore .lift) targetResult := by
                          simpa [Erase.quotientCore] using
                            (IxIR0.ProjectionSafe.Eval.app
                              (IxIR0.ProjectionSafe.Eval.var
                                (ctx := ictx) (fuel := targetFuel)
                                (env := av' :: targetArgs.reverse)
                                (index := 2) (value := targetFunction) hlookup)
                              (IxIR0.ProjectionSafe.Eval.var
                                (ctx := ictx) (fuel := targetFuel)
                                (env := av' :: targetArgs.reverse)
                                (index := 0) (value := av') rfl)
                              htargetApplyTrace.mono)
                        have hclosureApply : IxIR0.ProjectionSafe.Apply ictx
                            (targetFuel + 3)
                            (.clos .many targetArgs.reverse
                              (Erase.lamManyN
                                (Ixon.Eval.quotArity .lift -
                                  sourceArgs.length - 1)
                                (Erase.quotientCore .lift))) av'
                            targetResult := by
                          simpa [hsourceLength, Ixon.Eval.quotArity,
                            Erase.lamManyN] using
                            (IxIR0.ProjectionSafe.Apply.clos hcoreTrace)
                        have htargetTrace : IxIR0.ProjectionSafe.Eval ictx
                            (n₁ + n₂ + targetFuel + 4) ρ
                            (.app fT aT) targetResult :=
                          .app (htraceF.mono_le (by omega))
                            (htraceA.mono_le (by omega))
                            (hclosureApply.mono_le (by omega))
                        exact ⟨_, _, htargetTrace.run, hresultRel,
                          htargetTrace⟩
                    | ind =>
                      have hsourceLength : sourceArgs.length = 4 := by
                        have heq := (beq_iff_eq).mp hcmp
                        simp only [List.length_append, List.length_cons,
                          List.length_nil, Ixon.Eval.quotArity] at heq
                        omega
                      have hmotiveBound : 3 < sourceArgs.length := by omega
                      let sourceMotive := sourceArgs[3]
                      have hmotive : sourceArgs[3]? = some sourceMotive :=
                        List.getElem?_eq_getElem hmotiveBound
                      have hmotive' : (sourceArgs ++ [av])[3]? =
                          some sourceMotive := by
                        rw [List.getElem?_append_left hmotiveBound]
                        exact hmotive
                      have hquotient : (sourceArgs ++ [av])[4]? = some av := by
                        rw [← hsourceLength]
                        exact List.getElem?_concat_length
                      rw [hmotive', hquotient] at hev
                      simp only at hev
                      cases hrep : Ixon.Eval.quotientRep? av with
                      | none => rw [hrep] at hev; contradiction
                      | some representative =>
                        rw [hrep] at hev
                        dsimp only at hev
                        obtain ⟨targetMotive, htargetMotive, hmotiveRel⟩ :=
                          valsRel_lookup 3 hargs sourceMotive hmotive
                        have hrepresentativeRel :
                            ValRel ectx ictx representative av' :=
                          quotientRep_valRel hrelA hrep
                        obtain ⟨targetFuel, targetResult, htargetApply,
                            hresultRel, htargetApplyTrace⟩ :=
                          applyRel_sim ih hmembers horacles (by omega) hev
                            hmotiveRel
                            hrepresentativeRel
                        have htargetLength : targetArgs.length = 4 := by
                          omega
                        have hreverse : targetArgs.reverse[0]? =
                            some targetMotive := by
                          rw [List.getElem?_reverse'
                            (l := targetArgs) (i := 0) (j := 3) (by omega)]
                          exact htargetMotive
                        have hlookup :
                            (av' :: targetArgs.reverse)[1]? =
                              some targetMotive := by simpa using hreverse
                        have hcoreTrace : IxIR0.ProjectionSafe.Eval ictx
                            (targetFuel + 2) (av' :: targetArgs.reverse)
                            (Erase.quotientCore .ind) targetResult := by
                          simpa [Erase.quotientCore] using
                            (IxIR0.ProjectionSafe.Eval.app
                              (IxIR0.ProjectionSafe.Eval.var
                                (ctx := ictx) (fuel := targetFuel)
                                (env := av' :: targetArgs.reverse)
                                (index := 1) (value := targetMotive) hlookup)
                              (IxIR0.ProjectionSafe.Eval.var
                                (ctx := ictx) (fuel := targetFuel)
                                (env := av' :: targetArgs.reverse)
                                (index := 0) (value := av') rfl)
                              htargetApplyTrace.mono)
                        have hclosureApply : IxIR0.ProjectionSafe.Apply ictx
                            (targetFuel + 3)
                            (.clos .many targetArgs.reverse
                              (Erase.lamManyN
                                (Ixon.Eval.quotArity .ind -
                                  sourceArgs.length - 1)
                                (Erase.quotientCore .ind))) av'
                            targetResult := by
                          simpa [hsourceLength, Ixon.Eval.quotArity,
                            Erase.lamManyN] using
                            (IxIR0.ProjectionSafe.Apply.clos hcoreTrace)
                        have htargetTrace : IxIR0.ProjectionSafe.Eval ictx
                            (n₁ + n₂ + targetFuel + 4) ρ
                            (.app fT aT) targetResult :=
                          .app (htraceF.mono_le (by omega))
                            (htraceA.mono_le (by omega))
                            (hclosureApply.mono_le (by omega))
                        exact ⟨_, _, htargetTrace.run, hresultRel,
                          htargetTrace⟩
          | papExtern hconfigured hlt hargs =>
            rename_i address arity sourceArgs targetArgs
            cases n with
            | zero => rw [Ixon.Eval.apply.eq_def] at hev; simp at hev
            | succ sourceFuel =>
              rw [Ixon.Eval.apply.eq_def] at hev
              dsimp only at hev
              have hargs' : ValsRel ectx ictx (sourceArgs ++ [av])
                  (targetArgs ++ [av']) := valsRel_append hargs hrelA
              obtain ⟨targetFuel, targetValue, htargetSaturate, hresultRel,
                  htargetSaturateTrace⟩ :=
                externSaturate_sim horacles hconfigured (by simp; omega)
                  hargs' hev
              have htargetApply : IxIR0.apply ictx (targetFuel + 1)
                  (.pap (.ext address arity) targetArgs) av' =
                    .ok targetValue := by
                rw [IxIR0.apply.eq_def]
                dsimp only
                exact htargetSaturate
              have htargetApplyTrace : IxIR0.ProjectionSafe.Apply ictx
                  (targetFuel + 1) (.pap (.ext address arity) targetArgs) av'
                  targetValue := .pap htargetSaturateTrace
              refine ⟨n₁ + n₂ + targetFuel + 2, targetValue, ?_,
                hresultRel, ?_⟩
              · rw [IxIR0.eval.eq_def]
                dsimp only
                rw [IxIR0.eval_mono
                  (show n₁ ≤ n₁ + n₂ + targetFuel + 1 by omega) hfv',
                  bindOk]
                rw [IxIR0.eval_mono
                  (show n₂ ≤ n₁ + n₂ + targetFuel + 1 by omega) hav',
                  bindOk]
                exact IxIR0.apply_mono
                  (show targetFuel + 1 ≤ n₁ + n₂ + targetFuel + 1 by omega)
                  htargetApply
              · exact .app
                  (htraceF.mono_le (by omega))
                  (htraceA.mono_le (by omega))
                  (htargetApplyTrace.mono_le (by omega))
          | clos hdropC henvC hbodyC =>
            rename_i scC maskC bC uC FC envC domC bodyC uC' ρC bodyC'
            cases n with
            | zero => rw [Ixon.Eval.apply.eq_def] at hev; simp at hev
            | succ g =>
              rw [Ixon.Eval.apply.eq_def] at hev
              dsimp only at hev
              have henv' : EnvRel ectx ictx scC FC.refs FC.selfMuts
                  FC.selfAddr (bC :: maskC) (av :: envC) (av' :: ρC) := by
                cases bC
                · exact .drop henvC
                · exact .keep hrelA henvC
              obtain ⟨n₃, v', hv', hrel, htraceBody⟩ :=
                ih g (by omega) ectx FC (av :: envC) bodyC v scC (bC :: maskC)
                  (av' :: ρC) bodyC' ictx hmembers horacles hev hbodyC henv'
              refine ⟨n₁ + n₂ + n₃ + 2, v', ?_, hrel, ?_⟩
              rw [IxIR0.eval.eq_def]
              dsimp only
              rw [IxIR0.eval_mono (show n₁ ≤ n₁ + n₂ + n₃ + 1 by omega)
                hfv', bindOk]
              rw [IxIR0.eval_mono (show n₂ ≤ n₁ + n₂ + n₃ + 1 by omega)
                hav', bindOk]
              rw [IxIR0.apply.eq_def]
              dsimp only
              exact IxIR0.eval_mono (show n₃ ≤ n₁ + n₂ + n₃ by omega) hv'
              exact .app
                (htraceF.mono_le (by omega))
                (htraceA.mono_le (by omega))
                (.clos (htraceBody.mono_le (by omega)))
          | inductiveType hres hinfo =>
            cases n with
            | zero => rw [Ixon.Eval.apply.eq_def] at hev; simp at hev
            | succ g =>
              rw [Ixon.Eval.apply.eq_def] at hev
              dsimp only at hev
              cases g with
              | zero => rw [Ixon.Eval.saturate.eq_def] at hev; simp at hev
              | succ g' =>
                rw [Ixon.Eval.saturate.eq_def] at hev
                simp only [Ixon.Eval.Head.arity?] at hev
                injection hev with hv
                subst hv
                refine ⟨n₁ + n₂ + 3, .erased, ?_,
                  .inductiveType hres hinfo, ?_⟩
                rw [IxIR0.eval.eq_def]
                dsimp only
                rw [IxIR0.eval_mono (show n₁ ≤ n₁ + n₂ + 2 by omega)
                  hfv', bindOk]
                rw [IxIR0.eval_mono (show n₂ ≤ n₁ + n₂ + 2 by omega)
                  hav', bindOk]
                rw [IxIR0.apply.eq_def]
                exact .app
                  (htraceF.mono_le (by omega))
                  (htraceA.mono_le (by omega))
                  .erased
          | inductiveMember hresolve hmember =>
            cases n with
            | zero => rw [Ixon.Eval.apply.eq_def] at hev; simp at hev
            | succ g =>
              rw [Ixon.Eval.apply.eq_def] at hev
              dsimp only at hev
              cases g with
              | zero => rw [Ixon.Eval.saturate.eq_def] at hev; simp at hev
              | succ g' =>
                rw [Ixon.Eval.saturate.eq_def] at hev
                simp only [Ixon.Eval.Head.arity?] at hev
                injection hev with hv
                subst hv
                refine ⟨n₁ + n₂ + 3, .erased, ?_,
                  .inductiveMember hresolve hmember, ?_⟩
                rw [IxIR0.eval.eq_def]
                dsimp only
                rw [IxIR0.eval_mono (show n₁ ≤ n₁ + n₂ + 2 by omega)
                  hfv', bindOk]
                rw [IxIR0.eval_mono (show n₂ ≤ n₁ + n₂ + 2 by omega)
                  hav', bindOk]
                rw [IxIR0.apply.eq_def]
                exact .app
                  (htraceF.mono_le (by omega))
                  (htraceA.mono_le (by omega))
                  .erased
          | papCtorParams hshape haddr hidecl harity hparams =>
            rename_i block indIdx cidx params fields arity sargs a targetEnv
            subst arity
            cases n with
            | zero => rw [Ixon.Eval.apply.eq_def] at hev; simp at hev
            | succ g =>
              rw [Ixon.Eval.apply.eq_def] at hev
              dsimp only at hev
              cases g with
              | zero => rw [Ixon.Eval.saturate.eq_def] at hev; simp at hev
              | succ g' =>
                rw [Ixon.Eval.saturate.eq_def] at hev
                simp only [Ixon.Eval.Head.arity?] at hev
                by_cases hstill : (sargs ++ [av]).length < params
                · have hcmp : ((sargs ++ [av]).length ==
                      params + fields) = false := by
                    rw [beq_eq_false_iff_ne]
                    omega
                  rw [hcmp] at hev
                  simp at hev
                  subst v
                  have hremaining : params - sargs.length - 1 =
                      (params - (sargs ++ [av]).length - 1) + 1 := by
                    simp only [List.length_append, List.length_cons,
                      List.length_nil] at hstill ⊢
                    omega
                  have hbodyTrace : IxIR0.ProjectionSafe.Eval ictx 1
                      (av' :: targetEnv)
                      (Erase.lamManyN (params - sargs.length - 1) (.ref a))
                      (.clos .many (av' :: targetEnv)
                        (Erase.lamManyN
                          (params - (sargs ++ [av]).length - 1) (.ref a))) := by
                    rw [hremaining]
                    simpa [Erase.lamManyN] using
                      (IxIR0.ProjectionSafe.Eval.lam (ctx := ictx) (fuel := 0)
                        (env := av' :: targetEnv) (uses := Uses.many)
                        (body := Erase.lamManyN
                          (params - (sargs ++ [av]).length - 1) (.ref a)))
                  have happlyTrace : IxIR0.ProjectionSafe.Apply ictx 2
                      (.clos .many targetEnv
                        (Erase.lamManyN (params - sargs.length - 1) (.ref a)))
                      av'
                      (.clos .many (av' :: targetEnv)
                        (Erase.lamManyN
                          (params - (sargs ++ [av]).length - 1) (.ref a))) :=
                    .clos hbodyTrace
                  have htargetTrace : IxIR0.ProjectionSafe.Eval ictx
                      (n₁ + n₂ + 3) ρ (.app fT aT)
                      (.clos .many (av' :: targetEnv)
                        (Erase.lamManyN
                          (params - (sargs ++ [av]).length - 1) (.ref a))) :=
                    .app (htraceF.mono_le (by omega))
                      (htraceA.mono_le (by omega))
                      (happlyTrace.mono_le (by omega))
                  exact ⟨_, _, htargetTrace.run,
                    .papCtorParams hshape haddr hidecl rfl hstill,
                    htargetTrace⟩
                · have hfull : (sargs ++ [av]).length = params := by
                    simp only [List.length_append, List.length_cons,
                      List.length_nil] at hstill ⊢
                    omega
                  have hbody : params - sargs.length - 1 = 0 := by
                    simp only [List.length_append, List.length_cons,
                      List.length_nil] at hfull
                    omega
                  have hdrop : (sargs ++ [av]).drop params = [] :=
                    List.drop_eq_nil_of_le (by omega)
                  have hargs : ValsRel ectx ictx
                      ((sargs ++ [av]).drop params) [] := by
                    rw [hdrop]
                    exact .nil
                  cases fields with
                  | zero =>
                    have hcmp : ((sargs ++ [av]).length == params + 0) = true :=
                      beq_iff_eq.mpr (by omega)
                    rw [hcmp] at hev
                    simp at hev
                    cases g' with
                    | zero => rw [Ixon.Eval.fire.eq_def] at hev; simp at hev
                    | succ g'' =>
                      rw [Ixon.Eval.fire.eq_def] at hev
                      dsimp only at hev
                      injection hev with hv
                      subst v
                      have hcursor : PolicyRel (fun _ _ => True)
                          IxIR0.Value.erased (ctorPolicy params 0)
                          (sargs ++ [av]) [] := by
                        have hc := PolicyPrefix.ctor_of_fields
                          (R := fun _ _ => True) (ghost := IxIR0.Value.erased)
                          (show params ≤ (sargs ++ [av]).length by omega)
                          (show (sargs ++ [av]).length ≤ params + 0 by omega)
                          (show ListRel (fun _ _ => True)
                              ((sargs ++ [av]).drop params) [] by
                            rw [hdrop]
                            exact .nil)
                        simpa [hfull] using hc
                      have hsaturate : IxIR0.ProjectionSafe.Saturate ictx 2
                          (.ctor a cidx 0) [] (.ctor a cidx []) :=
                        .full (by simp [IxIR0.Head.arity]) .ctor
                      have hrefTrace : IxIR0.ProjectionSafe.Eval ictx 3
                          (av' :: targetEnv) (.ref a) (.ctor a cidx []) :=
                        .refCtor hidecl hsaturate
                      have happlyTrace : IxIR0.ProjectionSafe.Apply ictx 4
                          (.clos .many targetEnv
                            (Erase.lamManyN
                              (params - sargs.length - 1) (.ref a)))
                          av' (.ctor a cidx []) := by
                        simpa [hbody, Erase.lamManyN] using
                          (IxIR0.ProjectionSafe.Apply.clos hrefTrace)
                      have htargetTrace : IxIR0.ProjectionSafe.Eval ictx
                          (n₁ + n₂ + 5) ρ (.app fT aT) (.ctor a cidx []) :=
                        .app (htraceF.mono_le (by omega))
                          (htraceA.mono_le (by omega))
                          (happlyTrace.mono_le (by omega))
                      exact ⟨_, _, htargetTrace.run,
                        .ctorV hshape haddr hargs hcursor, htargetTrace⟩
                  | succ fields' =>
                    have hcmp : ((sargs ++ [av]).length ==
                        params + (fields' + 1)) = false := by
                      rw [beq_eq_false_iff_ne]
                      omega
                    rw [hcmp] at hev
                    simp at hev
                    subst v
                    have hcursor : PolicyPrefix (fun _ _ => True)
                        IxIR0.Value.erased (ctorPolicy params (fields' + 1))
                        (sargs ++ [av]) []
                        (List.replicate
                          (params + (fields' + 1) - (sargs ++ [av]).length)
                          .keep) :=
                      PolicyPrefix.ctor_of_fields
                        (show params ≤ (sargs ++ [av]).length by omega)
                        (show (sargs ++ [av]).length ≤
                            params + (fields' + 1) by omega)
                        (show ListRel (fun _ _ => True)
                            ((sargs ++ [av]).drop params) [] by
                          rw [hdrop]
                          exact .nil)
                    have hsaturate : IxIR0.ProjectionSafe.Saturate ictx 1
                        (.ctor a cidx (fields' + 1)) []
                        (.pap (.ctor a cidx (fields' + 1)) []) :=
                      .pending (by simp [IxIR0.Head.arity])
                    have hrefTrace : IxIR0.ProjectionSafe.Eval ictx 2
                        (av' :: targetEnv) (.ref a)
                        (.pap (.ctor a cidx (fields' + 1)) []) :=
                      .refCtor hidecl hsaturate
                    have happlyTrace : IxIR0.ProjectionSafe.Apply ictx 3
                        (.clos .many targetEnv
                          (Erase.lamManyN
                            (params - sargs.length - 1) (.ref a)))
                        av' (.pap (.ctor a cidx (fields' + 1)) []) := by
                      simpa [hbody, Erase.lamManyN] using
                        (IxIR0.ProjectionSafe.Apply.clos hrefTrace)
                    have htargetTrace : IxIR0.ProjectionSafe.Eval ictx
                        (n₁ + n₂ + 4) ρ (.app fT aT)
                        (.pap (.ctor a cidx (fields' + 1)) []) :=
                      .app (htraceF.mono_le (by omega))
                        (htraceA.mono_le (by omega))
                        (happlyTrace.mono_le (by omega))
                    exact ⟨_, _, htargetTrace.run,
                      .papCtor hshape haddr rfl rfl (by omega) (by omega)
                        hargs hcursor,
                      htargetTrace⟩
          | papCtor hshape haddr harity htarity hparams hlt hargs hcursor =>
            rename_i block indIdx cidx params fields arity tarity sargs a
              targs
            subst arity
            subst tarity
            have hlen := valsRel_length hargs
            cases n with
            | zero => rw [Ixon.Eval.apply.eq_def] at hev; simp at hev
            | succ g =>
              rw [Ixon.Eval.apply.eq_def] at hev
              dsimp only at hev
              cases g with
              | zero => rw [Ixon.Eval.saturate.eq_def] at hev; simp at hev
              | succ g' =>
                rw [Ixon.Eval.saturate.eq_def] at hev
                simp only [Ixon.Eval.Head.arity?] at hev
                cases hcmp : (sargs ++ [av]).length == params + fields with
                | false =>
                  rw [hcmp] at hev
                  simp at hev
                  subst hev
                  have hne := ne_of_beq_false hcmp
                  have hparams' : params ≤ (sargs ++ [av]).length := by
                    simp only [List.length_append, List.length_cons,
                      List.length_nil]
                    omega
                  have hdrop : (sargs ++ [av]).drop params =
                      sargs.drop params ++ [av] :=
                    drop_append_of_le sargs [av] params hparams
                  have hargs' : ValsRel ectx ictx
                      ((sargs ++ [av]).drop params) (targs ++ [av']) := by
                    rw [hdrop]
                    exact valsRel_append hargs hrelA
                  have hlt' : (sargs ++ [av]).length < params + fields := by
                    simp only [List.length_append, List.length_cons,
                      List.length_nil] at hne ⊢
                    omega
                  have hcursor' : PolicyPrefix (fun _ _ => True) .erased
                      (ctorPolicy params fields) (sargs ++ [av])
                      (targs ++ [av'])
                      (List.replicate
                        (params + fields - (sargs ++ [av]).length) .keep) :=
                    PolicyPrefix.ctor_of_fields hparams'
                      (Nat.le_of_lt hlt') (trueListRel_of_valsRel hargs')
                  refine ⟨n₁ + n₂ + 4,
                    .pap (.ctor a cidx fields) (targs ++ [av']), ?_,
                    .papCtor hshape haddr rfl rfl hparams' hlt' hargs'
                      hcursor', ?_⟩
                  rw [IxIR0.eval.eq_def]
                  dsimp only
                  rw [IxIR0.eval_mono (show n₁ ≤ n₁ + n₂ + 3 by omega)
                    hfv', bindOk]
                  rw [IxIR0.eval_mono (show n₂ ≤ n₁ + n₂ + 3 by omega)
                    hav', bindOk]
                  rw [IxIR0.apply.eq_def]
                  dsimp only
                  rw [IxIR0.saturate.eq_def]
                  dsimp only
                  have hc2 : ((targs ++ [av']).length == fields) = false := by
                    rw [beq_eq_false_iff_ne] at hcmp ⊢
                    simp only [List.length_append, List.length_cons,
                      List.length_nil, List.length_drop] at hlen hcmp ⊢
                    omega
                  simp only [IxIR0.Head.arity.eq_def, hc2]
                  simp
                  have hsaturate : IxIR0.ProjectionSafe.Saturate ictx
                      (n₁ + n₂ + 2) (.ctor a cidx fields)
                      (targs ++ [av'])
                      (.pap (.ctor a cidx fields) (targs ++ [av'])) :=
                    .pending (by
                      have hsourceNe := ne_of_beq_false hcmp
                      simp only [List.length_append, List.length_cons,
                        List.length_nil, List.length_drop] at hlen hsourceNe ⊢
                      simp only [IxIR0.Head.arity]
                      omega)
                  exact .app
                    (htraceF.mono_le (by omega))
                    (htraceA.mono_le (by omega))
                    (.pap hsaturate)
                | true =>
                  rw [hcmp] at hev
                  simp at hev
                  cases g' with
                  | zero => rw [Ixon.Eval.fire.eq_def] at hev; simp at hev
                  | succ g'' =>
                    rw [Ixon.Eval.fire.eq_def] at hev
                    dsimp only at hev
                    injection hev with hv
                    subst hv
                    have heq := (beq_iff_eq).mp hcmp
                    have hparams' : params ≤ (sargs ++ [av]).length := by
                      simp only [List.length_append, List.length_cons,
                        List.length_nil]
                      omega
                    have hdrop : (sargs ++ [av]).drop params =
                        sargs.drop params ++ [av] :=
                      drop_append_of_le sargs [av] params hparams
                    have hargs' : ValsRel ectx ictx
                        ((sargs ++ [av]).drop params) (targs ++ [av']) := by
                      rw [hdrop]
                      exact valsRel_append hargs hrelA
                    have hcursor' : PolicyRel (fun _ _ => True) .erased
                        (ctorPolicy params fields) (sargs ++ [av])
                        (targs ++ [av']) := by
                      have hc := PolicyPrefix.ctor_of_fields
                        (ghost := IxIR0.Value.erased) hparams'
                        (show (sargs ++ [av]).length ≤ params + fields by
                          omega)
                        (trueListRel_of_valsRel hargs')
                      simpa [heq] using hc
                    refine ⟨n₁ + n₂ + 5,
                      .ctor a cidx (targs ++ [av']), ?_,
                      .ctorV hshape haddr hargs' hcursor', ?_⟩
                    rw [IxIR0.eval.eq_def]
                    dsimp only
                    rw [IxIR0.eval_mono (show n₁ ≤ n₁ + n₂ + 4 by omega)
                      hfv', bindOk]
                    rw [IxIR0.eval_mono (show n₂ ≤ n₁ + n₂ + 4 by omega)
                      hav', bindOk]
                    rw [IxIR0.apply.eq_def]
                    dsimp only
                    rw [IxIR0.saturate.eq_def]
                    dsimp only
                    have hc2 : ((targs ++ [av']).length == fields) = true := by
                      rw [beq_iff_eq]
                      simp only [List.length_append, List.length_cons,
                        List.length_nil, List.length_drop] at hlen heq ⊢
                      omega
                    simp only [IxIR0.Head.arity.eq_def, hc2]
                    simp only [if_true]
                    rw [IxIR0.fire.eq_def]
                    have hsaturate : IxIR0.ProjectionSafe.Saturate ictx
                        (n₁ + n₂ + 3) (.ctor a cidx fields)
                        (targs ++ [av']) (.ctor a cidx (targs ++ [av'])) :=
                      .full (by
                        simp only [IxIR0.Head.arity, List.length_append,
                          List.length_cons, List.length_nil,
                          List.length_drop] at hlen heq ⊢
                        omega) .ctor
                    exact .app
                      (htraceF.mono_le (by omega))
                      (htraceA.mono_le (by omega))
                      (.pap hsaturate)
          | papRec hresolve hFrefs hFmuts hFsa hmem hi0 hlen2 hle hcursor =>
            rename_i block idx r F₂ bc₃ sargs targs rest
            have hrestSlots : SlotPolicies rest := by
              rw [hcursor.remaining_eq_drop]
              exact (recRulePolicy_slots r).dropN sargs.length
            cases n with
            | zero => rw [Ixon.Eval.apply.eq_def] at hev; simp at hev
            | succ g =>
              rw [Ixon.Eval.apply.eq_def] at hev
              dsimp only at hev
              cases g with
              | zero => rw [Ixon.Eval.saturate.eq_def] at hev; simp at hev
              | succ g' =>
                rw [Ixon.Eval.saturate.eq_def] at hev
                simp only [Ixon.Eval.Head.arity?] at hev
                cases hcmp : ((sargs ++ [av]).length ==
                    Ixon.Eval.recArity r) with
                | false =>
                  rw [hcmp] at hev
                  simp at hev
                  subst hev
                  have hne : (sargs ++ [av]).length ≠
                      Ixon.Eval.recArity r := by
                    exact ne_of_beq_false hcmp
                  cases rest with
                  | nil =>
                    have hslen := hcursor.source_length
                    simp only [List.length_nil, Nat.add_zero] at hslen
                    exfalso
                    apply hne
                    simp only [List.length_append, List.length_cons,
                      List.length_nil, Ixon.Eval.recArity, hi0,
                      Nat.add_zero]
                    rw [recRulePolicy_length] at hslen
                    omega
                  | cons policy rest =>
                    have hcursor' : RuntimePolicyPrefix (ValRel ectx ictx)
                        (recRulePolicy r) (sargs ++ [av]) (targs ++ [av'])
                        rest := by
                      cases hrestSlots with
                      | keep _ => exact hcursor.append_keep hrelA
                      | ghost _ => exact hcursor.append_ghost
                    refine ⟨n₁ + n₂ + 4,
                      .pap (.rec_ (Erase.memberAddr block idx)
                        (r.params.toNat + r.motives.toNat +
                          r.minors.toNat + 1))
                        (targs ++ [av']), ?_, ?_, ?_⟩
                    · rw [IxIR0.eval.eq_def]
                      dsimp only
                      rw [IxIR0.eval_mono (show n₁ ≤ n₁ + n₂ + 3 by omega)
                        hfv', bindOk]
                      rw [IxIR0.eval_mono (show n₂ ≤ n₁ + n₂ + 3 by omega)
                        hav', bindOk]
                      rw [IxIR0.apply.eq_def]
                      dsimp only
                      rw [IxIR0.saturate.eq_def]
                      dsimp only
                      have hc2 : ((targs ++ [av']).length ==
                          (r.params.toNat + r.motives.toNat +
                            r.minors.toNat + 1)) = false := by
                        rw [beq_eq_false_iff_ne]
                        intro heq
                        apply hne
                        simp only [List.length_append, List.length_cons,
                          List.length_nil, Ixon.Eval.recArity, hi0,
                          Nat.add_zero] at heq ⊢
                        omega
                      simp only [IxIR0.Head.arity.eq_def, hc2]
                      simp
                    · refine .papRec hresolve hFrefs hFmuts hFsa hmem hi0
                        (by simp [hlen2]) ?_ hcursor'
                      have hsource := hcursor'.source_length
                      omega
                    · have hsaturate : IxIR0.ProjectionSafe.Saturate ictx
                          (n₁ + n₂ + 2)
                          (.rec_ (Erase.memberAddr block idx)
                            (r.params.toNat + r.motives.toNat +
                              r.minors.toNat + 1))
                          (targs ++ [av'])
                          (.pap (.rec_ (Erase.memberAddr block idx)
                            (r.params.toNat + r.motives.toNat +
                              r.minors.toNat + 1)) (targs ++ [av'])) :=
                        .pending (by
                          intro heq
                          apply hne
                          simp only [IxIR0.Head.arity, List.length_append,
                            List.length_cons, List.length_nil,
                            Ixon.Eval.recArity, hi0, Nat.add_zero] at heq ⊢
                          omega)
                      exact .app
                        (htraceF.mono_le (by omega))
                        (htraceA.mono_le (by omega))
                        (.pap hsaturate)
                | true =>
                  rw [hcmp] at hev
                  simp at hev
                  have hslen : sargs.length =
                      (recRulePolicy r).length := by
                    have h := (beq_iff_eq).mp hcmp
                    simp only [List.length_append, List.length_cons,
                      List.length_nil, Ixon.Eval.recArity, hi0,
                      Nat.add_zero] at h
                    rw [recRulePolicy_length]
                    omega
                  have hrestLen : rest.length = 0 := by
                    have hsource := hcursor.source_length
                    omega
                  have hrest : rest = [] :=
                    List.length_eq_zero_iff.mp hrestLen
                  subst rest
                  -- the fired major must analyze as a constructor
                  have hmc : ∃ checked p,
                      Ixon.Eval.guardRecMajor (some block) r.params.toNat av =
                        .ok checked ∧
                      Ixon.Eval.majorCtor
                        (ectx.natBlock == some block) av = .ok p := by
                    cases g' with
                    | zero =>
                      rw [Ixon.Eval.fire.eq_def] at hev; simp at hev
                    | succ g'' =>
                      rw [Ixon.Eval.fire.eq_def] at hev
                      dsimp only at hev
                      rw [List.getLast?_concat] at hev
                      dsimp only at hev
                      simp only [Option.isSome_some, Bool.true_and] at hev
                      simp [hstrict.neutralElims, hstrict.stringLiterals,
                        bindOk] at hev
                      cases hgmajor : Ixon.Eval.guardRecMajor (some block)
                          r.params.toNat av with
                      | error e =>
                        rw [hgmajor, bindErr] at hev
                        simp at hev
                      | ok checked =>
                        rw [hgmajor, bindOk] at hev
                        cases hm : Ixon.Eval.majorCtor
                            (ectx.natBlock == some block) av with
                        | error e => rw [hm, bindErr] at hev; simp at hev
                        | ok p => exact ⟨checked, p, rfl, rfl⟩
                  obtain ⟨checked, p0, hguard, hmc⟩ := hmc
                  have hfire0 : Ixon.Eval.fire ectx g'
                      (.recH (some block) r F₂)
                      ((sargs ++ []) ++ [av]) = .ok v := by
                    simpa using hev
                  cases hrelA with
                  | sort => simp [Ixon.Eval.majorCtor.eq_def] at hmc
                  | pi => simp [Ixon.Eval.majorCtor.eq_def] at hmc
                  | clos _ _ _ => simp [Ixon.Eval.majorCtor.eq_def] at hmc
                  | litStr => simp [Ixon.Eval.majorCtor.eq_def] at hmc
                  | quotV _ => simp [Ixon.Eval.majorCtor.eq_def] at hmc
                  | quotType => simp [Ixon.Eval.majorCtor.eq_def] at hmc
                  | papQuot _ _ _ =>
                    simp [Ixon.Eval.majorCtor.eq_def] at hmc
                  | papExtern _ _ _ =>
                    simp [Ixon.Eval.majorCtor.eq_def] at hmc
                  | papCtor _ _ _ _ _ _ _ _ =>
                    simp [Ixon.Eval.majorCtor.eq_def] at hmc
                  | papCtorParams _ _ _ _ _ =>
                    simp [Ixon.Eval.majorCtor.eq_def] at hmc
                  | papRec _ _ _ _ _ _ _ _ _ =>
                    simp [Ixon.Eval.majorCtor.eq_def] at hmc
                  | papRecI _ _ _ _ _ _ _ _ =>
                    simp [Ixon.Eval.majorCtor.eq_def] at hmc
                  | papRecIW _ _ _ _ _ _ _ _ _ =>
                    simp [Ixon.Eval.majorCtor.eq_def] at hmc
                  | inductiveType _ _ =>
                    simp [Ixon.Eval.majorCtor.eq_def] at hmc
                  | inductiveMember _ _ =>
                    simp [Ixon.Eval.majorCtor.eq_def] at hmc
                  | ctorV hshape _haddr hfargs hctorCursor =>
                    rename_i cblock cindIdx ccidx cparams cfields ccargs2 ca
                      tflds
                    have hmcS : Ixon.Eval.majorCtor
                        (ectx.natBlock == some block)
                        (.ctorV cblock cindIdx ccidx ccargs2) =
                        .ok (ccidx, ccargs2) := by
                      simp [Ixon.Eval.majorCtor.eq_def]
                    have htmc : IxIR0.majorCtor
                        (ectx.natBlock == some block)
                        (.ctor ca ccidx tflds) = .ok (ccidx, tflds) := by
                      simp [IxIR0.majorCtor.eq_def]
                    have hcparams :=
                      recMember_ctor_params hmem hguard hshape
                    rw [hcparams] at hfargs
                    exact fireSim ih hmembers horacles (by omega) hresolve
                      hFrefs hFmuts hFsa
                      hmem (indexArgs := []) hlen2 hslen hcursor hmcS htmc
                      hfargs hfire0 hfv' hav' htraceF htraceA
                  | litNat =>
                    rename_i nn
                    have hp0 : r.params.toNat = 0 := by
                      simp only [Ixon.Eval.guardRecMajor] at hguard
                      split at hguard
                      · rename_i hp
                        exact (beq_iff_eq.mp hp)
                      · simp at hguard
                    cases hNB : (ectx.natBlock == some block) with
                    | false =>
                      simp [Ixon.Eval.majorCtor.eq_def, hNB] at hmc
                    | true =>
                      cases nn with
                      | zero =>
                        have hmcS : Ixon.Eval.majorCtor
                            (ectx.natBlock == some block)
                            (.litV (.natL 0)) = .ok (0, []) := by
                          simp [Ixon.Eval.majorCtor.eq_def, hNB]
                        have htmc : IxIR0.majorCtor
                            (ectx.natBlock == some block)
                            (.lit (.nat 0)) = .ok (0, []) := by
                          simp [IxIR0.majorCtor.eq_def, hNB]
                        exact fireSim ih hmembers horacles (by omega) hresolve hFrefs hFmuts
                          hFsa hmem (indexArgs := []) hlen2 hslen hcursor
                          hmcS htmc
                          (by simpa [hp0] using
                            (ValsRel.nil : ValsRel ectx ictx [] []))
                          hfire0 hfv' hav' htraceF htraceA
                      | succ k =>
                        have hmcS : Ixon.Eval.majorCtor
                            (ectx.natBlock == some block)
                            (.litV (.natL (k + 1))) =
                            .ok (1, [.litV (.natL k)]) := by
                          simp [Ixon.Eval.majorCtor.eq_def, hNB]
                        have htmc : IxIR0.majorCtor
                            (ectx.natBlock == some block)
                            (.lit (.nat (k + 1))) =
                            .ok (1, [.lit (.nat k)]) := by
                          simp [IxIR0.majorCtor.eq_def, hNB]
                        exact fireSim ih hmembers horacles (by omega) hresolve hFrefs hFmuts
                          hFsa hmem (indexArgs := []) hlen2 hslen hcursor
                          hmcS htmc
                          (by simpa [hp0] using
                            (ValsRel.cons ValRel.litNat ValsRel.nil))
                          hfire0 hfv' hav' htraceF htraceA
          | papRecIW hresolve hFrefs hFmuts hFsa hmem hipos hremaining
              hanchor hcursor =>
            rename_i block idx r F₂ bc sargs targs ignored baseEnv remaining
              anchor
            cases remaining with
            | zero => omega
            | succ remaining =>
              have hsourcePending : ((sargs ++ [av]).length ==
                  Ixon.Eval.recArity r) = false := by
                rw [beq_eq_false_iff_ne]
                have hlen := hcursor.source_length
                simp only [List.length_replicate, List.length_append,
                  List.length_cons, List.length_nil] at hlen ⊢
                rw [recPolicy_length_exact] at hlen
                simp only [Ixon.Eval.recArity]
                omega
              cases n with
              | zero => rw [Ixon.Eval.apply.eq_def] at hev; simp at hev
              | succ g =>
                rw [Ixon.Eval.apply.eq_def] at hev
                dsimp only at hev
                cases g with
                | zero => rw [Ixon.Eval.saturate.eq_def] at hev; simp at hev
                | succ g' =>
                  rw [Ixon.Eval.saturate.eq_def] at hev
                  simp only [Ixon.Eval.Head.arity?, hsourcePending,
                    Bool.false_eq_true, if_false] at hev
                  injection hev with hvalue
                  subst v
                  let targetPap : IxIR0.Value :=
                    .pap (.rec_ (Erase.memberAddr block idx)
                      (r.params.toNat + r.motives.toNat +
                        r.minors.toNat + 1)) targs
                  have hcursor' : RuntimePolicyPrefix (ValRel ectx ictx)
                      (recPolicy r) (sargs ++ [av]) targs
                      (List.replicate remaining .drop) := by
                    have happend := hcursor.append_drop (sarg := av)
                    simpa [List.replicate_succ] using happend
                  cases remaining with
                  | zero =>
                    have hlookup :
                        (av' :: ignored.reverse ++ targetPap :: baseEnv)[anchor]? =
                          some targetPap := by
                      have hprefix : (av' :: ignored.reverse).length = anchor := by
                        simpa using hanchor
                      change
                        (((av' :: ignored.reverse) ++
                          (targetPap :: baseEnv))[anchor]? = some targetPap)
                      rw [← hprefix]
                      rw [List.getElem?_append_right (Nat.le_refl _)]
                      simp
                    have hbodyTrace : IxIR0.ProjectionSafe.Eval ictx 1
                        (av' :: ignored.reverse ++ targetPap :: baseEnv)
                        (.var anchor) targetPap :=
                      .var hlookup
                    have happlyTrace : IxIR0.ProjectionSafe.Apply ictx 2
                        (.clos .many
                          (ignored.reverse ++ targetPap :: baseEnv)
                          (.var anchor)) av' targetPap :=
                      .clos hbodyTrace
                    have htargetTrace : IxIR0.ProjectionSafe.Eval ictx
                        (n₁ + n₂ + 3) ρ (.app fT aT) targetPap :=
                      .app (htraceF.mono_le (by omega))
                        (htraceA.mono_le (by omega))
                        (happlyTrace.mono_le (by omega))
                    obtain ⟨ruleArgs, indexArgs, hsargs, hindices, hfront⟩ :=
                      hcursor'.split_suffix_drops
                        (policies := recRulePolicy r)
                        (n := r.indices.toNat)
                    rw [hsargs]
                    exact ⟨_, _, htargetTrace.run,
                      .papRecI hresolve hFrefs hFmuts hFsa hmem hipos
                        hindices hfront,
                      htargetTrace⟩
                  | succ remaining =>
                    have hbodyTrace : IxIR0.ProjectionSafe.Eval ictx 1
                        (av' :: ignored.reverse ++ targetPap :: baseEnv)
                        (Erase.lamManyN (remaining + 1) (.var anchor))
                        (.clos .many
                          (av' :: ignored.reverse ++ targetPap :: baseEnv)
                          (Erase.lamManyN remaining (.var anchor))) := by
                      simpa [Erase.lamManyN] using
                        (IxIR0.ProjectionSafe.Eval.lam (ctx := ictx)
                          (fuel := 0)
                          (env := av' :: ignored.reverse ++
                            targetPap :: baseEnv)
                          (uses := Uses.many)
                          (body := Erase.lamManyN remaining (.var anchor)))
                    have happlyTrace : IxIR0.ProjectionSafe.Apply ictx 2
                        (.clos .many
                          (ignored.reverse ++ targetPap :: baseEnv)
                          (Erase.lamManyN (remaining + 1) (.var anchor))) av'
                        (.clos .many
                          (av' :: ignored.reverse ++ targetPap :: baseEnv)
                          (Erase.lamManyN remaining (.var anchor))) :=
                      .clos hbodyTrace
                    have htargetTrace : IxIR0.ProjectionSafe.Eval ictx
                        (n₁ + n₂ + 3) ρ (.app fT aT)
                        (.clos .many
                          (av' :: ignored.reverse ++ targetPap :: baseEnv)
                          (Erase.lamManyN remaining (.var anchor))) :=
                      .app (htraceF.mono_le (by omega))
                        (htraceA.mono_le (by omega))
                        (happlyTrace.mono_le (by omega))
                    refine ⟨_, _, htargetTrace.run, ?_, htargetTrace⟩
                    simpa [targetPap] using
                      (ValRel.papRecIW hresolve hFrefs hFmuts hFsa hmem hipos
                        (show 0 < remaining + 1 by omega)
                        (show (ignored ++ [av']).length + (remaining + 1) =
                            anchor by
                          simp only [List.length_append, List.length_cons,
                            List.length_nil]
                          omega)
                        hcursor'
                        : ValRel ectx ictx
                            (.papV (.recH (some block) r F₂)
                              (sargs ++ [av]))
                            (.clos .many
                              ((ignored ++ [av']).reverse ++
                                targetPap :: baseEnv)
                              (Erase.lamManyN ((remaining + 1) - 1)
                                (.var anchor))))
          | papRecI hresolve hFrefs hFmuts hFsa hmem _hipos hindices
              hcursor =>
            rename_i block idx r F₂ bc ruleArgs indexArgs targs
            have hslen : ruleArgs.length = (recRulePolicy r).length := by
              simpa using hcursor.source_length
            have hlen2 : ruleArgs.length = targs.length := by
              calc
                ruleArgs.length = (recRulePolicy r).length := hslen
                _ = policyTargetArity (recRulePolicy r) :=
                  (recRulePolicy_slots r).targetArity_eq_length.symm
                _ = targs.length := by
                  simpa [policyTargetArity] using hcursor.target_length.symm
            cases n with
            | zero => rw [Ixon.Eval.apply.eq_def] at hev; simp at hev
            | succ g =>
              rw [Ixon.Eval.apply.eq_def] at hev
              dsimp only at hev
              cases g with
              | zero => rw [Ixon.Eval.saturate.eq_def] at hev; simp at hev
              | succ g' =>
                rw [Ixon.Eval.saturate.eq_def] at hev
                simp only [Ixon.Eval.Head.arity?] at hev
                have hcmp : (((ruleArgs ++ indexArgs) ++ [av]).length ==
                    Ixon.Eval.recArity r) = true := by
                  rw [beq_iff_eq]
                  simp only [List.length_append, List.length_cons,
                    List.length_nil, Ixon.Eval.recArity, hindices, hslen]
                  rw [recRulePolicy_length]
                rw [hcmp] at hev
                simp at hev
                have hmc : ∃ checked p,
                    Ixon.Eval.guardRecMajor (some block) r.params.toNat av =
                      .ok checked ∧
                    Ixon.Eval.majorCtor
                      (ectx.natBlock == some block) av = .ok p := by
                  cases g' with
                  | zero =>
                    rw [Ixon.Eval.fire.eq_def] at hev
                    simp at hev
                  | succ g'' =>
                    rw [Ixon.Eval.fire.eq_def] at hev
                    dsimp only at hev
                    rw [← List.append_assoc] at hev
                    rw [List.getLast?_concat] at hev
                    dsimp only at hev
                    simp only [Option.isSome_some, Bool.true_and] at hev
                    simp [hstrict.neutralElims, hstrict.stringLiterals,
                      bindOk] at hev
                    cases hgmajor : Ixon.Eval.guardRecMajor (some block)
                        r.params.toNat av with
                    | error e =>
                      rw [hgmajor, bindErr] at hev
                      simp at hev
                    | ok checked =>
                      rw [hgmajor, bindOk] at hev
                      cases hm : Ixon.Eval.majorCtor
                          (ectx.natBlock == some block) av with
                      | error e => rw [hm, bindErr] at hev; simp at hev
                      | ok p => exact ⟨checked, p, rfl, rfl⟩
                obtain ⟨checked, p0, hguard, hmc⟩ := hmc
                have hfireI : Ixon.Eval.fire ectx g'
                    (.recH (some block) r F₂)
                    ((ruleArgs ++ indexArgs) ++ [av]) = .ok v := by
                  simpa using hev
                cases hrelA with
                | sort => simp [Ixon.Eval.majorCtor.eq_def] at hmc
                | pi => simp [Ixon.Eval.majorCtor.eq_def] at hmc
                | clos _ _ _ => simp [Ixon.Eval.majorCtor.eq_def] at hmc
                | litStr => simp [Ixon.Eval.majorCtor.eq_def] at hmc
                | quotV _ => simp [Ixon.Eval.majorCtor.eq_def] at hmc
                | quotType => simp [Ixon.Eval.majorCtor.eq_def] at hmc
                | papQuot _ _ _ =>
                  simp [Ixon.Eval.majorCtor.eq_def] at hmc
                | papExtern _ _ _ =>
                  simp [Ixon.Eval.majorCtor.eq_def] at hmc
                | papCtor _ _ _ _ _ _ _ _ =>
                  simp [Ixon.Eval.majorCtor.eq_def] at hmc
                | papCtorParams _ _ _ _ _ =>
                  simp [Ixon.Eval.majorCtor.eq_def] at hmc
                | papRec _ _ _ _ _ _ _ _ _ =>
                  simp [Ixon.Eval.majorCtor.eq_def] at hmc
                | papRecI _ _ _ _ _ _ _ _ =>
                  simp [Ixon.Eval.majorCtor.eq_def] at hmc
                | papRecIW _ _ _ _ _ _ _ _ _ =>
                  simp [Ixon.Eval.majorCtor.eq_def] at hmc
                | inductiveType _ _ =>
                  simp [Ixon.Eval.majorCtor.eq_def] at hmc
                | inductiveMember _ _ =>
                  simp [Ixon.Eval.majorCtor.eq_def] at hmc
                | ctorV hshape _haddr hfargs hctorCursor =>
                  rename_i cblock cindIdx ccidx cparams cfields ccargs2 ca
                    tflds
                  have hmcS : Ixon.Eval.majorCtor
                      (ectx.natBlock == some block)
                      (.ctorV cblock cindIdx ccidx ccargs2) =
                      .ok (ccidx, ccargs2) := by
                    simp [Ixon.Eval.majorCtor.eq_def]
                  have htmc : IxIR0.majorCtor
                      (ectx.natBlock == some block)
                      (.ctor ca ccidx tflds) = .ok (ccidx, tflds) := by
                    simp [IxIR0.majorCtor.eq_def]
                  have hcparams := recMember_ctor_params hmem hguard hshape
                  rw [hcparams] at hfargs
                  exact fireSim ih hmembers horacles (by omega) hresolve hFrefs
                    hFmuts hFsa
                    hmem (indexArgs := indexArgs) hlen2 hslen hcursor hmcS
                    htmc hfargs hfireI hfv' hav' htraceF htraceA
                | litNat =>
                  rename_i nn
                  have hp0 : r.params.toNat = 0 := by
                    simp only [Ixon.Eval.guardRecMajor] at hguard
                    split at hguard
                    · rename_i hp
                      exact beq_iff_eq.mp hp
                    · simp at hguard
                  cases hNB : (ectx.natBlock == some block) with
                  | false =>
                    simp [Ixon.Eval.majorCtor.eq_def, hNB] at hmc
                  | true =>
                    cases nn with
                    | zero =>
                      have hmcS : Ixon.Eval.majorCtor
                          (ectx.natBlock == some block)
                          (.litV (.natL 0)) = .ok (0, []) := by
                        simp [Ixon.Eval.majorCtor.eq_def, hNB]
                      have htmc : IxIR0.majorCtor
                          (ectx.natBlock == some block)
                          (.lit (.nat 0)) = .ok (0, []) := by
                        simp [IxIR0.majorCtor.eq_def, hNB]
                      exact fireSim ih hmembers horacles (by omega) hresolve hFrefs hFmuts
                        hFsa hmem (indexArgs := indexArgs) hlen2 hslen
                        hcursor hmcS htmc
                        (by simpa [hp0] using
                          (ValsRel.nil : ValsRel ectx ictx [] []))
                        hfireI hfv' hav' htraceF htraceA
                    | succ k =>
                      have hmcS : Ixon.Eval.majorCtor
                          (ectx.natBlock == some block)
                          (.litV (.natL (k + 1))) =
                          .ok (1, [.litV (.natL k)]) := by
                        simp [Ixon.Eval.majorCtor.eq_def, hNB]
                      have htmc : IxIR0.majorCtor
                          (ectx.natBlock == some block)
                          (.lit (.nat (k + 1))) =
                          .ok (1, [.lit (.nat k)]) := by
                        simp [IxIR0.majorCtor.eq_def, hNB]
                      exact fireSim ih hmembers horacles (by omega) hresolve hFrefs hFmuts
                        hFsa hmem (indexArgs := indexArgs) hlen2 hslen
                        hcursor hmcS htmc
                        (by simpa [hp0] using
                          (ValsRel.cons ValRel.litNat ValsRel.nil))
                        hfireI hfv' hav' htraceF htraceA
    | appE hd hlam =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      rename_i u dom body aS fT
      cases hf : Ixon.Eval.eval ectx n F env (.lam u dom body) with
      | error err => rw [hf, bindErr] at hev; simp at hev
      | ok fv =>
        rw [hf, bindOk] at hev
        cases ha : Ixon.Eval.eval ectx n F env aS with
        | error err => rw [ha, bindErr] at hev; simp at hev
        | ok av =>
          rw [ha, bindOk] at hev
          cases n with
          | zero => rw [Ixon.Eval.eval.eq_def] at hf; simp at hf
          | succ g =>
            rw [Ixon.Eval.eval.eq_def] at hf
            dsimp only at hf
            injection hf with hfv
            subst hfv
            rw [Ixon.Eval.apply.eq_def] at hev
            dsimp only at hev
            cases hlam with
            | lamK hnd hpb => rw [hd] at hnd; simp at hnd
            | lamD hd' hpb =>
              rename_i bodyT
              obtain ⟨n₃, v', hv', hrel, htraceBody⟩ :=
                ih g (by omega) ectx F (av :: env) body v sc (false :: mask)
                  (.erased :: ρ) bodyT ictx hmembers horacles hev hpb
                    (.drop henv)
              have hlamT : IxIR0.eval ictx (n₃ + 1) ρ (.lam .many bodyT) =
                  .ok (.clos .many ρ bodyT) := by rw [IxIR0.eval.eq_def]
              have hboxT : IxIR0.eval ictx (n₃ + 1) ρ .erased =
                  .ok .erased := by rw [IxIR0.eval.eq_def]
              refine ⟨n₃ + 2, v', ?_, hrel,
                .app .lam .erased (.clos htraceBody)⟩
              rw [IxIR0.eval.eq_def]
              dsimp only
              rw [hlamT, bindOk, hboxT, bindOk]
              rw [IxIR0.apply.eq_def]
              dsimp only
              exact hv'
            | ctorP _ hspine _ => cases hspine
            | ctorW hspine _ _ => cases hspine
            | recP hspine => cases hspine
            | recW hspine _ => cases hspine

/-- **The erasure simulation (stages 1 + 2a + 2b).** If a source term
terminates with a value under the Ixon reference semantics, its
erasure terminates under the IxIR₀ semantics with a related value. -/
theorem erasure_sim_with_members {fuel : Nat} {ectx : Ixon.Eval.EvalCtx}
    {F : Ixon.Eval.Frame} {env : List Ixon.Eval.Value} {e : Ixon.Expr}
    {v : Ixon.Eval.Value} {sc : Option (Ixon.Address × Nat)}
    {mask : List Bool} {ρ : List IxIR0.Value}
    {e' : IxIR0.Expr} {ictx : IxIR0.Ctx}
    (hmembers : MemberCoverage ectx ictx scope.plan)
    (horacles : OracleRel ectx ictx)
    (hev : Ixon.Eval.eval ectx fuel F env e = .ok v)
    (hpe : PErase ectx ictx sc F.refs F.selfMuts F.selfAddr mask e e')
    (henv : EnvRel ectx ictx sc F.refs F.selfMuts F.selfAddr mask env ρ) :
    ∃ fuel' v', IxIR0.eval ictx fuel' ρ e' = .ok v' ∧
      ValRel ectx ictx v v' := by
  obtain ⟨fuel', v', hrun, hrel, _⟩ :=
    simAt fuel ectx F env e v sc mask ρ e' ictx hmembers horacles hev hpe henv
  exact ⟨fuel', v', hrun, hrel⟩

/-- Erasure simulation with a proof-producing, call-aware projection-safety
trace.  The witness follows every closure and recursor-rule body reached by
the successful source execution. -/
theorem erasure_sim_projectionSafe_with_members {fuel : Nat}
    {ectx : Ixon.Eval.EvalCtx} {F : Ixon.Eval.Frame}
    {env : List Ixon.Eval.Value} {e : Ixon.Expr} {v : Ixon.Eval.Value}
    {sc : Option (Ixon.Address × Nat)} {mask : List Bool}
    {ρ : List IxIR0.Value} {e' : IxIR0.Expr} {ictx : IxIR0.Ctx}
    (hmembers : MemberCoverage ectx ictx scope.plan)
    (horacles : OracleRel ectx ictx)
    (hev : Ixon.Eval.eval ectx fuel F env e = .ok v)
    (hpe : PErase ectx ictx sc F.refs F.selfMuts F.selfAddr mask e e')
    (henv : EnvRel ectx ictx sc F.refs F.selfMuts F.selfAddr mask env ρ) :
    ∃ fuel' v', IxIR0.ProjectionSafe.Eval ictx fuel' ρ e' v' ∧
      ValRel ectx ictx v v' := by
  obtain ⟨fuel', v', _, hrel, htrace⟩ :=
    simAt fuel ectx F env e v sc mask ρ e' ictx hmembers horacles hev hpe henv
  exact ⟨fuel', v', htrace, hrel⟩

end MemberScoped

/-- Compatibility specialization of `erasure_sim_with_members` to the empty
member scope. -/
theorem erasure_sim {fuel : Nat} {ectx : Ixon.Eval.EvalCtx}
    {F : Ixon.Eval.Frame} {env : List Ixon.Eval.Value} {e : Ixon.Expr}
    {v : Ixon.Eval.Value} {sc : Option (Ixon.Address × Nat)}
    {mask : List Bool} {ρ : List IxIR0.Value}
    {e' : IxIR0.Expr} {ictx : IxIR0.Ctx}
    (hstrict : ectx.Strict)
    (horacles : OracleRel ectx ictx)
    (hev : Ixon.Eval.eval ectx fuel F env e = .ok v)
    (hpe : PErase ectx ictx sc F.refs F.selfMuts F.selfAddr mask e e')
    (henv : EnvRel ectx ictx sc F.refs F.selfMuts F.selfAddr mask env ρ) :
    ∃ fuel' v', IxIR0.eval ictx fuel' ρ e' = .ok v' ∧
      ValRel ectx ictx v v' := by
  exact erasure_sim_with_members (.nil hstrict) horacles hev hpe henv

/-- Compatibility specialization of the call-aware theorem to the empty
member scope. -/
theorem erasure_sim_projectionSafe {fuel : Nat}
    {ectx : Ixon.Eval.EvalCtx} {F : Ixon.Eval.Frame}
    {env : List Ixon.Eval.Value} {e : Ixon.Expr} {v : Ixon.Eval.Value}
    {sc : Option (Ixon.Address × Nat)} {mask : List Bool}
    {ρ : List IxIR0.Value} {e' : IxIR0.Expr} {ictx : IxIR0.Ctx}
    (hstrict : ectx.Strict)
    (horacles : OracleRel ectx ictx)
    (hev : Ixon.Eval.eval ectx fuel F env e = .ok v)
    (hpe : PErase ectx ictx sc F.refs F.selfMuts F.selfAddr mask e e')
    (henv : EnvRel ectx ictx sc F.refs F.selfMuts F.selfAddr mask env ρ) :
    ∃ fuel' v', IxIR0.ProjectionSafe.Eval ictx fuel' ρ e' v' ∧
      ValRel ectx ictx v v' := by
  exact erasure_sim_projectionSafe_with_members (.nil hstrict) horacles hev hpe henv

/-- Successful projection in the source pins the erased projection target to
a constructor, not to IxIR₀'s extra erased-absorber case.  Besides the target
constructor evaluation, the witness identifies the selected erased field and
relates it to the actual Ixon projection result.  This is the local
admissibility fact needed to rule out erased-slot projection stuckness in the
subsequent IxIR₀ → IxIR₁ lowering proof. -/
theorem erasure_proj_sim {fuel : Nat} {ectx : Ixon.Eval.EvalCtx}
    {F : Ixon.Eval.Frame} {env : List Ixon.Eval.Value}
    {tyRef fieldIdx : UInt64} {source : Ixon.Expr}
    {sourceValue : Ixon.Eval.Value}
    {sc : Option (Ixon.Address × Nat)} {mask : List Bool}
    {ρ : List IxIR0.Value} {target : IxIR0.Expr} {ictx : IxIR0.Ctx}
    (hstrict : ectx.Strict)
    (horacles : OracleRel ectx ictx)
    (hev : Ixon.Eval.eval ectx fuel F env
      (.prj tyRef fieldIdx source) = .ok sourceValue)
    (hpe : PErase ectx ictx sc F.refs F.selfMuts F.selfAddr mask
      (.prj tyRef fieldIdx source) (.proj fieldIdx.toNat target))
    (henv : EnvRel ectx ictx sc F.refs F.selfMuts F.selfAddr mask env ρ) :
    ∃ targetFuel address tag fields targetValue,
      IxIR0.eval ictx targetFuel ρ target =
          .ok (.ctor address tag fields) ∧
        fields[fieldIdx.toNat]? = some targetValue ∧
        ValRel ectx ictx sourceValue targetValue := by
  cases hpe with
  | recP hspine => cases hspine
  | prjE hsourceErase =>
    cases fuel with
    | zero =>
      rw [Ixon.Eval.eval.eq_def] at hev
      simp at hev
    | succ fuel =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      cases hsourceRun : Ixon.Eval.eval ectx fuel F env source with
      | error error =>
        rw [hsourceRun, bindErr] at hev
        simp at hev
      | ok sourceTarget =>
        rw [hsourceRun, bindOk] at hev
        obtain ⟨projectedInd, projectedBlockConstant, block, indIdx, cidx,
            sourceArgs, hprojectedResolve, hsourceTarget, hfield⟩ :=
          Ixon.Eval.projectValue_ok_of_strict hstrict.neutralElims hev
        subst sourceTarget
        obtain ⟨targetFuel, targetTarget, htargetRun, htargetRel⟩ :=
          erasure_sim hstrict horacles hsourceRun hsourceErase henv
        cases htargetRel with
        | ctorV hshape haddress hargs hcursor =>
          rename_i params fieldCount address targetFields
          obtain ⟨blockConstant, indDecl, ctor, hresolve, hctor,
              hparams, hctorParams, hctorFields⟩ := hshape
          rw [hresolve] at hprojectedResolve
          injection hprojectedResolve with hpair
          injection hpair with _ hind
          injection hind with hind
          subst projectedInd
          have hfieldDrop :
              (sourceArgs.drop params)[fieldIdx.toNat]? =
                some sourceValue := by
            rw [List.getElem?_drop]
            simpa [hparams] using hfield
          obtain ⟨targetValue, htargetField, hvalueRel⟩ :=
            valsRel_lookup _ hargs _ hfieldDrop
          exact ⟨targetFuel, address, cidx, targetFields, targetValue,
            htargetRun, htargetField, hvalueRel⟩

/-- Any independently obtained successful evaluation of the erased
projection target has the constructor shape recovered by
`erasure_proj_sim`.  Fuel monotonicity joins the two evaluations, so this is
the convenient inversion form for a downstream compiler proof that already
has its own target-evaluation witness. -/
theorem erasure_proj_target_ctor {fuel targetFuel : Nat}
    {ectx : Ixon.Eval.EvalCtx}
    {F : Ixon.Eval.Frame} {env : List Ixon.Eval.Value}
    {tyRef fieldIdx : UInt64} {source : Ixon.Expr}
    {sourceValue : Ixon.Eval.Value}
    {sc : Option (Ixon.Address × Nat)} {mask : List Bool}
    {ρ : List IxIR0.Value} {target : IxIR0.Expr}
    {targetSource : IxIR0.Value} {ictx : IxIR0.Ctx}
    (hstrict : ectx.Strict)
    (horacles : OracleRel ectx ictx)
    (hev : Ixon.Eval.eval ectx fuel F env
      (.prj tyRef fieldIdx source) = .ok sourceValue)
    (hpe : PErase ectx ictx sc F.refs F.selfMuts F.selfAddr mask
      (.prj tyRef fieldIdx source) (.proj fieldIdx.toNat target))
    (henv : EnvRel ectx ictx sc F.refs F.selfMuts F.selfAddr mask env ρ)
    (htarget : IxIR0.eval ictx targetFuel ρ target = .ok targetSource) :
    ∃ address tag fields targetValue,
      targetSource = .ctor address tag fields ∧
        fields[fieldIdx.toNat]? = some targetValue ∧
        ValRel ectx ictx sourceValue targetValue := by
  obtain ⟨witnessFuel, address, tag, fields, targetValue,
      hwitness, hfield, hvalueRel⟩ :=
    erasure_proj_sim hstrict horacles hev hpe henv
  let common := max witnessFuel targetFuel
  have hwitness' : IxIR0.eval ictx common ρ target =
      .ok (.ctor address tag fields) :=
    IxIR0.eval_mono (Nat.le_max_left _ _) hwitness
  have htarget' : IxIR0.eval ictx common ρ target = .ok targetSource :=
    IxIR0.eval_mono (Nat.le_max_right _ _) htarget
  have hvalue : targetSource = .ctor address tag fields := by
    rw [hwitness'] at htarget'
    exact (Except.ok.inj htarget').symm
  exact ⟨address, tag, fields, targetValue, hvalue, hfield, hvalueRel⟩

/-- Closed-term corollary. -/
theorem erasure_sim_closed {fuel : Nat} {ectx : Ixon.Eval.EvalCtx}
    {F : Ixon.Eval.Frame} {e : Ixon.Expr} {v : Ixon.Eval.Value}
    {e' : IxIR0.Expr} {ictx : IxIR0.Ctx}
    (hstrict : ectx.Strict)
    (horacles : OracleRel ectx ictx)
    (hev : Ixon.Eval.eval ectx fuel F [] e = .ok v)
    (hpe : PErase ectx ictx none F.refs F.selfMuts F.selfAddr [] e e') :
    ∃ fuel' v', IxIR0.eval ictx fuel' [] e' = .ok v' ∧
      ValRel ectx ictx v v' :=
  erasure_sim hstrict horacles hev hpe .nil

/-- Closed-term call-aware projection-safe erasure simulation. -/
theorem erasure_sim_projectionSafe_closed {fuel : Nat}
    {ectx : Ixon.Eval.EvalCtx} {F : Ixon.Eval.Frame}
    {e : Ixon.Expr} {v : Ixon.Eval.Value}
    {e' : IxIR0.Expr} {ictx : IxIR0.Ctx}
    (hstrict : ectx.Strict)
    (horacles : OracleRel ectx ictx)
    (hev : Ixon.Eval.eval ectx fuel F [] e = .ok v)
    (hpe : PErase ectx ictx none F.refs F.selfMuts F.selfAddr [] e e') :
    ∃ fuel' v', IxIR0.ProjectionSafe.Eval ictx fuel' [] e' v' ∧
      ValRel ectx ictx v v' :=
  erasure_sim_projectionSafe hstrict horacles hev hpe .nil

/-! ## Sharing composition

Sharing is eliminated semantically before entering `PErase`.  The relation
therefore remains share-free: source evaluation is first transported to the
fully inlined context, frame, environment, and expression, then the existing
simulation theorem applies unchanged. -/

/-- A source value relates to an IxIR₀ value after every captured sharing
table and expression root in the source value has been fully inlined. -/
abbrev InlinedValRel (ectx : Ixon.Eval.EvalCtx) (ictx : IxIR0.Ctx)
    (value : Ixon.Eval.Value) (target : IxIR0.Value)
    [scope : MemberScope] : Prop :=
  ValRel ectx.inlineSharing ictx value.inlineSharing target

/-- General sharing composition.  Successful evaluation under a well-formed
sharing frame is transported to the share-free evaluator, after which an
ordinary `PErase` derivation supplies the existing erasure simulation. -/
theorem erasure_sim_inlineSharing {fuel : Nat}
    {ectx : Ixon.Eval.EvalCtx} {F : Ixon.Eval.Frame}
    {env : List Ixon.Eval.Value} {e : Ixon.Expr} {v : Ixon.Eval.Value}
    {sc : Option (Ixon.Address × Nat)} {mask : List Bool}
    {ρ : List IxIR0.Value} {e' : IxIR0.Expr} {ictx : IxIR0.Ctx}
    (hstrict : ectx.Strict)
    (horacles : OracleRel ectx.inlineSharing ictx)
    (hctx : ectx.SharingWF) (hF : F.SharingWF)
    (henvWF : Ixon.Eval.ValuesSharingWF env)
    (he : Ixon.Sharing.sharesBelow F.sharing.size e = true)
    (hev : Ixon.Eval.eval ectx fuel F env e = .ok v)
    (hpe : PErase ectx.inlineSharing ictx sc F.inlineSharing.refs
      F.inlineSharing.selfMuts F.inlineSharing.selfAddr mask
      (Ixon.Sharing.inlineExpr F.sharing e) e')
    (henv : EnvRel ectx.inlineSharing ictx sc F.inlineSharing.refs
      F.inlineSharing.selfMuts F.inlineSharing.selfAddr mask
      (Ixon.Eval.valuesInlineSharing env) ρ) :
    ∃ fuel' v', IxIR0.eval ictx fuel' ρ e' = .ok v' ∧
      InlinedValRel ectx ictx v v' := by
  have hinlined := Ixon.Eval.eval_inlineSharing hctx hF henvWF he hev
  exact erasure_sim hstrict.inlineSharing horacles hinlined.1 hpe henv

/-- Sharing-aware erasure simulation retaining the full call-aware
projection-safe target trace. -/
theorem erasure_sim_projectionSafe_inlineSharing {fuel : Nat}
    {ectx : Ixon.Eval.EvalCtx} {F : Ixon.Eval.Frame}
    {env : List Ixon.Eval.Value} {e : Ixon.Expr} {v : Ixon.Eval.Value}
    {sc : Option (Ixon.Address × Nat)} {mask : List Bool}
    {ρ : List IxIR0.Value} {e' : IxIR0.Expr} {ictx : IxIR0.Ctx}
    (hstrict : ectx.Strict)
    (horacles : OracleRel ectx.inlineSharing ictx)
    (hctx : ectx.SharingWF) (hF : F.SharingWF)
    (henvWF : Ixon.Eval.ValuesSharingWF env)
    (he : Ixon.Sharing.sharesBelow F.sharing.size e = true)
    (hev : Ixon.Eval.eval ectx fuel F env e = .ok v)
    (hpe : PErase ectx.inlineSharing ictx sc F.inlineSharing.refs
      F.inlineSharing.selfMuts F.inlineSharing.selfAddr mask
      (Ixon.Sharing.inlineExpr F.sharing e) e')
    (henv : EnvRel ectx.inlineSharing ictx sc F.inlineSharing.refs
      F.inlineSharing.selfMuts F.inlineSharing.selfAddr mask
      (Ixon.Eval.valuesInlineSharing env) ρ) :
    ∃ fuel' v', IxIR0.ProjectionSafe.Eval ictx fuel' ρ e' v' ∧
      InlinedValRel ectx ictx v v' := by
  have hinlined := Ixon.Eval.eval_inlineSharing hctx hF henvWF he hev
  exact erasure_sim_projectionSafe hstrict.inlineSharing horacles
    hinlined.1 hpe henv

/-- Closed-term sharing-aware call-aware erasure simulation. -/
theorem erasure_sim_projectionSafe_inlineSharing_closed {fuel : Nat}
    {ectx : Ixon.Eval.EvalCtx} {F : Ixon.Eval.Frame}
    {e : Ixon.Expr} {v : Ixon.Eval.Value}
    {e' : IxIR0.Expr} {ictx : IxIR0.Ctx}
    (hstrict : ectx.Strict)
    (horacles : OracleRel ectx.inlineSharing ictx)
    (hctx : ectx.SharingWF) (hF : F.SharingWF)
    (he : Ixon.Sharing.sharesBelow F.sharing.size e = true)
    (hev : Ixon.Eval.eval ectx fuel F [] e = .ok v)
    (hpe : PErase ectx.inlineSharing ictx none F.inlineSharing.refs
      F.inlineSharing.selfMuts F.inlineSharing.selfAddr []
      (Ixon.Sharing.inlineExpr F.sharing e) e') :
    ∃ fuel' v', IxIR0.ProjectionSafe.Eval ictx fuel' [] e' v' ∧
      InlinedValRel ectx ictx v v' := by
  apply erasure_sim_projectionSafe_inlineSharing hstrict horacles hctx hF .nil
    he hev hpe
  simpa [Ixon.Eval.valuesInlineSharing] using
    (EnvRel.nil (ectx := ectx.inlineSharing) (ictx := ictx)
      (refs := F.inlineSharing.refs) (muts := F.inlineSharing.selfMuts)
      (sa := F.inlineSharing.selfAddr))

/-- Sharing-aware projection corollary.  It transports the successful source
projection to the fully inlined semantics used by
`CertifiedSharedExpr`/`CertifiedSharedProgram`, then applies the same
constructor-only projection inversion as the share-free theorem. -/
theorem erasure_proj_sim_inlineSharing {fuel : Nat}
    {ectx : Ixon.Eval.EvalCtx} {F : Ixon.Eval.Frame}
    {env : List Ixon.Eval.Value} {tyRef fieldIdx : UInt64}
    {source : Ixon.Expr} {sourceValue : Ixon.Eval.Value}
    {sc : Option (Ixon.Address × Nat)} {mask : List Bool}
    {ρ : List IxIR0.Value} {target : IxIR0.Expr} {ictx : IxIR0.Ctx}
    (hstrict : ectx.Strict)
    (horacles : OracleRel ectx.inlineSharing ictx)
    (hctx : ectx.SharingWF) (hF : F.SharingWF)
    (henvWF : Ixon.Eval.ValuesSharingWF env)
    (hsourceBelow :
      Ixon.Sharing.sharesBelow F.sharing.size source = true)
    (hev : Ixon.Eval.eval ectx fuel F env
      (.prj tyRef fieldIdx source) = .ok sourceValue)
    (hpe : PErase ectx.inlineSharing ictx sc F.inlineSharing.refs
      F.inlineSharing.selfMuts F.inlineSharing.selfAddr mask
      (.prj tyRef fieldIdx (Ixon.Sharing.inlineExpr F.sharing source))
      (.proj fieldIdx.toNat target))
    (henv : EnvRel ectx.inlineSharing ictx sc F.inlineSharing.refs
      F.inlineSharing.selfMuts F.inlineSharing.selfAddr mask
      (Ixon.Eval.valuesInlineSharing env) ρ) :
    ∃ targetFuel address tag fields targetValue,
      IxIR0.eval ictx targetFuel ρ target =
          .ok (.ctor address tag fields) ∧
        fields[fieldIdx.toNat]? = some targetValue ∧
        InlinedValRel ectx ictx sourceValue targetValue := by
  have hwholeBelow : Ixon.Sharing.sharesBelow F.sharing.size
      (.prj tyRef fieldIdx source) = true := by
    simpa [Ixon.Sharing.sharesBelow] using hsourceBelow
  have hinlined := Ixon.Eval.eval_inlineSharing hctx hF henvWF
    hwholeBelow hev
  have hinlineEval : Ixon.Eval.eval ectx.inlineSharing fuel
      F.inlineSharing (Ixon.Eval.valuesInlineSharing env)
      (.prj tyRef fieldIdx (Ixon.Sharing.inlineExpr F.sharing source)) =
        .ok sourceValue.inlineSharing := by
    simpa [Ixon.Sharing.inlineExpr, Ixon.Sharing.substShares,
      Ixon.Sharing.substSharesList] using hinlined.1
  exact erasure_proj_sim hstrict.inlineSharing horacles hinlineEval hpe henv

/-- Fuel-joined inversion form of the sharing-aware projection theorem. -/
theorem erasure_proj_target_ctor_inlineSharing
    {fuel targetFuel : Nat}
    {ectx : Ixon.Eval.EvalCtx} {F : Ixon.Eval.Frame}
    {env : List Ixon.Eval.Value} {tyRef fieldIdx : UInt64}
    {source : Ixon.Expr} {sourceValue : Ixon.Eval.Value}
    {sc : Option (Ixon.Address × Nat)} {mask : List Bool}
    {ρ : List IxIR0.Value} {target : IxIR0.Expr}
    {targetSource : IxIR0.Value} {ictx : IxIR0.Ctx}
    (hstrict : ectx.Strict)
    (horacles : OracleRel ectx.inlineSharing ictx)
    (hctx : ectx.SharingWF) (hF : F.SharingWF)
    (henvWF : Ixon.Eval.ValuesSharingWF env)
    (hsourceBelow :
      Ixon.Sharing.sharesBelow F.sharing.size source = true)
    (hev : Ixon.Eval.eval ectx fuel F env
      (.prj tyRef fieldIdx source) = .ok sourceValue)
    (hpe : PErase ectx.inlineSharing ictx sc F.inlineSharing.refs
      F.inlineSharing.selfMuts F.inlineSharing.selfAddr mask
      (.prj tyRef fieldIdx (Ixon.Sharing.inlineExpr F.sharing source))
      (.proj fieldIdx.toNat target))
    (henv : EnvRel ectx.inlineSharing ictx sc F.inlineSharing.refs
      F.inlineSharing.selfMuts F.inlineSharing.selfAddr mask
      (Ixon.Eval.valuesInlineSharing env) ρ)
    (htarget : IxIR0.eval ictx targetFuel ρ target = .ok targetSource) :
    ∃ address tag fields targetValue,
      targetSource = .ctor address tag fields ∧
        fields[fieldIdx.toNat]? = some targetValue ∧
        InlinedValRel ectx ictx sourceValue targetValue := by
  obtain ⟨witnessFuel, address, tag, fields, targetValue,
      hwitness, hfield, hvalueRel⟩ :=
    erasure_proj_sim_inlineSharing hstrict horacles hctx hF henvWF hsourceBelow
      hev hpe henv
  let common := max witnessFuel targetFuel
  have hwitness' : IxIR0.eval ictx common ρ target =
      .ok (.ctor address tag fields) :=
    IxIR0.eval_mono (Nat.le_max_left _ _) hwitness
  have htarget' : IxIR0.eval ictx common ρ target = .ok targetSource :=
    IxIR0.eval_mono (Nat.le_max_right _ _) htarget
  have hvalue : targetSource = .ctor address tag fields := by
    rw [hwitness'] at htarget'
    exact (Except.ok.inj htarget').symm
  exact ⟨address, tag, fields, targetValue, hvalue, hfield, hvalueRel⟩

/-- Closed-term sharing composition, the entry point used by executable
certificates.  No `.share` constructor is added to `PErase`. -/
theorem erasure_sim_inlineSharing_closed {fuel : Nat}
    {ectx : Ixon.Eval.EvalCtx} {F : Ixon.Eval.Frame}
    {e : Ixon.Expr} {v : Ixon.Eval.Value} {e' : IxIR0.Expr}
    {ictx : IxIR0.Ctx} (hstrict : ectx.Strict)
    (hctx : ectx.SharingWF) (hF : F.SharingWF)
    (horacles : OracleRel ectx.inlineSharing ictx)
    (he : Ixon.Sharing.sharesBelow F.sharing.size e = true)
    (hev : Ixon.Eval.eval ectx fuel F [] e = .ok v)
    (hpe : PErase ectx.inlineSharing ictx none F.inlineSharing.refs
      F.inlineSharing.selfMuts F.inlineSharing.selfAddr []
      (Ixon.Sharing.inlineExpr F.sharing e) e') :
    ∃ fuel' v', IxIR0.eval ictx fuel' [] e' = .ok v' ∧
      InlinedValRel ectx ictx v v' := by
  apply erasure_sim_inlineSharing hstrict horacles hctx hF .nil he hev hpe
  simpa [Ixon.Eval.valuesInlineSharing] using
    (EnvRel.nil (ectx := ectx.inlineSharing) (ictx := ictx)
      (refs := F.inlineSharing.refs) (muts := F.inlineSharing.selfMuts)
      (sa := F.inlineSharing.selfAddr))

/-! Executable-pass agreement spot checks on fragment terms, and a
relation witness for the ι machinery. -/

private def ectx₀ : Erase.EraseCtx := { resolve := fun _ => none }

#guard (match Erase.eraseExpr ectx₀ 1000 {} []
    (.lam .many (.var 9) (.var 0)) with
  | .ok (.lam .many (.var 0)) => true
  | _ => false)

#guard (match Erase.eraseExpr ectx₀ 1000 {} []
    (.lam .many (.sort 0) (.lam .many (.var 0) (.var 0))) with
  | .ok (.lam .many (.lam .many (.var 0))) => true
  | _ => false)

example {ectx ictx sc refs muts sa} :
    PErase ectx ictx sc refs muts sa [] (.lam .many (.var 9) (.var 0))
      (.lam .many (.var 0)) :=
  .lamK rfl (.var rfl)

example {ectx ictx sc refs muts sa} :
    PErase ectx ictx sc refs muts sa []
      (.lam .many (.sort 0) (.lam .many (.var 0) (.var 0)))
      (.lam .many (.lam .many (.var 0))) :=
  .lamD rfl (.lamK rfl (.var rfl))

/-- The `Nat.rec` successor-rule body (kernel-shaped, peeled): source
`s n (rec motive z s n)` with the self-`recur`; the erasure rewires
self to the recSelf slot (`var 4` — just past the four peeled
binders) and the motive argument to `◻` through the guarded ghost
application. The rule mask drops the motive slot. -/
example {ectx ictx refs} {muts : Array MutConst} {blk : Ixon.Address}
    {r : Recursor}
    (hm : muts[1]? = some (.recr r))
    (hp : r.params.toNat = 0) (hi : r.indices.toNat = 0)
    (hmot : 0 < r.motives.toNat) :
    PErase ectx ictx (some (blk, 1)) refs muts (some blk)
      [true, true, true, false]
      (.app (.app (.var 1) (.var 0))
        (.app (.app (.app (.app (.recur 1 #[0]) (.var 3)) (.var 2))
          (.var 1)) (.var 0)))
      (.app (.app (.var 1) (.var 0))
      (.app (.app (.app (.app (.var 4) .erased) (.var 2)) (.var 1))
          (.var 0))) :=
  .app (.app (.var rfl) (.var rfl))
    (.app (.app (.app (.appG (.head (.recurH rfl hm hi))
      (by
        cases hmotive : r.motives.toNat with
        | zero => omega
        | succ motives =>
          simp [recRulePolicy, recParamPolicy, hp, hmotive,
            List.replicate_succ])
      (.recurS rfl (by
        intro r' hr
        have hm' : muts[UInt64.toNat 1]? = some (.recr r) := by
          simpa using hm
        rw [hm'] at hr
        injection hr with heq
        cases heq
        exact hi))) (.var rfl)) (.var rfl)) (.var rfl))

end Ix.Compiler.Sim
