import Compilatrix.Ixon.Sharing.Eval
import Compilatrix.IxIR0.Mono
import Compilatrix.Sim.Segment

/-!
# The erasure simulation, stages 1 + 2a + 2b plus sharing composition

Stage 1 proved the theorem on the pure λ-fragment; stage 2a added
literals, constructors, projections, and reference
resolution with the program-level `Covered` relation. **Stage 2b puts
recursor ι under the theorem**, including parameterized List-shaped layouts
and fully supplied, syntactically visible source-only index segments. Visible
fully supplied constructor-parameter prefixes stutter over their dropped
target arguments:

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
- The recursor-self slot: a rule-body `recur` of the block's own
  member relates to `var mask.length` (`recurS`) with **no
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
- `papRec` carries a `RuntimePolicyPrefix` cursor through parameter, motive,
  and minor applications. Kept slots require `ValRel`; ghost slots consume
  both sides but leave their runtime values unconstrained, while exact
  `PErase.appG` still emits `◻`. For indexed recursors, `RecEraseSpine`
  keeps the complete `recPolicy` cursor local while source-only indices
  stutter, then `papRecI` exposes only the ready-to-fire pre-major value.
  Intermediate target paps are deliberately excluded from `ValRel`: they are
  already one argument from firing while the source still owes indices.
- Constructor paps and values carry the reusable `PolicyPrefix` cursor from
  `Sim/Segment.lean`. `CtorParamSpine` handles a visible, complete dropped
  parameter prefix, after which ordinary application retains and relates the
  fields. Recursor firing guards constructor-block identity, and `RecMember`
  stores a finite `BlockParams` witness, so the global parameterized value
  relation cannot feed a mismatched recursor layout.
- At ι both sides select the same rule (same constructor index, or
  the same literal peel — the evaluator now carries the recursor's
  block identity precisely so the peels agree), the source enters the
  kernel-shaped lambda telescope (`applyMany_chain`), and the target
  evaluates the peeled body in the assembled rule environment;
  `fireSim` proves the two runs related.

Still outside the core relation: under-applied or split parameterized
constructor/indexed-recursor heads, indexed recursive self calls, member
references other than self (`memberAddr` coverage),
quotients/axioms/externs (the oracle correspondence), and occurrences
of variables bound in slots the executable eraser drops to `◻`. Raw
`.share` syntax deliberately remains outside `PErase`; the composition
theorems at the end of this file transport evaluation through full inlining
and then reuse the share-free relation unchanged.
That last case needs usage-checker soundness or a typed logical
relation: `EnvRel` deliberately leaves dropped slots unconstrained,
so a general `PErase.var` clause would be false. The differential
suite in `Erase.lean` witnesses the executable cases; this file is the
theorem catching up.

Fuel handling is unchanged: strong induction on source fuel,
`IxIR0.eval_mono` to combine target sub-derivations.
-/

namespace Compilatrix.Sim

open Compilatrix.Ixon (Uses Owned Recursor RecursorRule MutConst Constant)

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
      ∀ {idx : Nat} {ind : Compilatrix.Ixon.Inductive},
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
      {c : Constant} {p : Compilatrix.Ixon.RecursorProj} {bc : Constant}
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

/-- A syntactically visible constructor head followed only by its dropped
parameter prefix.  The final index counts consumed source parameters; target
evaluation stutters throughout this spine. -/
inductive CtorParamSpine (ectx : Ixon.Eval.EvalCtx)
    (refs : Array Ixon.Address) : Ixon.Expr → Ixon.Address → Ixon.Address →
    Nat → Nat → Nat → Nat → Nat → Prop where
  | head {refIdx : UInt64} {univIdxs : Array UInt64}
      {a : Ixon.Address} {c : Constant}
      {p : Compilatrix.Ixon.ConstructorProj} {params fields : Nat} :
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
        {o : Compilatrix.Ixon.Owned} {dom cod : Ixon.Expr} :
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
    | recP {ectx ictx sc refs muts sa} {mask : List Bool}
        {e : Ixon.Expr} {e' : IxIR0.Expr} {r : Recursor} :
        RecEraseSpine ectx ictx sc refs muts sa mask e e' r [] →
        PErase ectx ictx sc refs muts sa mask e e'
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
        {c : Constant} {p : Compilatrix.Ixon.RecursorProj}
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
        {d : Compilatrix.Ixon.Definition} {result : Owned}
        {body' : IxIR0.Expr} :
        ectx.resolve a = some c →
        c.info = .defn d →
        Ixon.Eval.unfoldable d = true →
        ictx.env a = some (.defn result body') →
        PErase ectx ictx none c.refs (Ixon.Eval.selfMutsOf c.info) none
          [] d.value body' →
        Covered ectx ictx a
    | ctor {ectx ictx} {a : Ixon.Address} {c : Constant}
        {p : Compilatrix.Ixon.ConstructorProj} {fields : Nat} :
        ectx.resolve a = some c →
        c.info = .cPrj p →
        CtorShape ectx p.block p.idx.toNat p.cidx.toNat 0 fields →
        ictx.env a = some (.ctor p.cidx.toNat fields) →
        Covered ectx ictx a
    | tyf {ectx ictx} {a : Ixon.Address} {c : Constant}
        {p : Compilatrix.Ixon.InductiveProj} :
        ectx.resolve a = some c →
        c.info = .iPrj p →
        ictx.env a = some (.defn .shared .erased) →
        Covered ectx ictx a
    | recrP {ectx ictx} {a : Ixon.Address} {c : Constant}
        {p : Compilatrix.Ixon.RecursorProj} {bc : Constant} {r : Recursor} :
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
          (Ixon.Eval.selfMutsOf bc.info).toList →
        ictx.env (Erase.memberAddr block idx) =
          some (.recursor
            (r.params.toNat + r.motives.toNat + r.minors.toNat)
            (ectx.natBlock == some block) trules) →
        RulesRel ectx ictx block idx r bc.refs
          (Ixon.Eval.selfMutsOf bc.info) r.rules.toList trules.toList →
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
        EnvRel ectx ictx sc F.refs F.selfMuts F.selfAddr mask env ρ →
        PErase ectx ictx sc F.refs F.selfMuts F.selfAddr (b :: mask)
          body body' →
        ValRel ectx ictx (.closV u F env dom body) (.clos u' ρ body')
    | litNat {ectx ictx} {n : Nat} :
        ValRel ectx ictx (.litV (.natL n)) (.lit (.nat n))
    | litStr {ectx ictx} {s : String} :
        ValRel ectx ictx (.litV (.strL s)) (.lit (.str s))
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
    | papRec {ectx ictx} {block : Ixon.Address} {idx : Nat}
        {r : Recursor} {F : Ixon.Eval.Frame} {bc : Constant}
        {sargs : List Ixon.Eval.Value} {targs : List IxIR0.Value}
        {rest : List Erase.ArgPolicy} :
        ectx.resolve block = some bc →
        F.refs = bc.refs →
        F.selfMuts = Ixon.Eval.selfMutsOf bc.info →
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
        F.selfMuts = Ixon.Eval.selfMutsOf bc.info →
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
    | neu {ectx ictx} {id : Ixon.Eval.NeutralId}
        {args : List Ixon.Eval.Value} :
        ValRel ectx ictx (.papV (.neuH id) args) .erased

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
        muts = Ixon.Eval.selfMutsOf bc.info →
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

private theorem bindOk {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

private theorem bindErr {ε α β : Type} (er : ε) (f : α → Except ε β) :
    ((Except.error er : Except ε α) >>= f) = Except.error er := rfl

private theorem bind_ok_iff {ε α β : Type} {x : Except ε α}
    {f : α → Except ε β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bindErr]
  | ok a => simp [bindOk]

/-! ## List and resolution helpers -/

private theorem arrGet?_toList {α} (a : Array α) (i : Nat) :
    a.toList[i]? = a[i]? := by
  simp

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

private theorem peelChain_succ {n : Nat} {e B : Ixon.Expr}
    (h : peelChain (n + 1) e = some B) :
    ∃ u d b, e = .lam u d b ∧ peelChain n b = some B := by
  cases e <;> first
    | exact ⟨_, _, _, rfl, h⟩
    | (rw [peelChain.eq_def] at h; simp at h)

private theorem resolveMut_ok {ectx : Ixon.Eval.EvalCtx}
    {b : Ixon.Address} {i : Nat} {bc : Constant} {m : MutConst}
    (h : Ixon.Eval.resolveMut ectx b i = .ok (bc, m)) :
    ectx.resolve b = some bc ∧
      (Ixon.Eval.selfMutsOf bc.info)[i]? = some m := by
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
    have hget : (Ixon.Eval.selfMutsOf bcRec.info).toList[indIdx]? =
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
      muts = Ixon.Eval.selfMutsOf bc.info ∧ sa = some block ∧
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

private theorem ctorParamSpine_shape {ectx : Ixon.Eval.EvalCtx}
    {refs : Array Ixon.Address} {e : Ixon.Expr} {a block : Ixon.Address}
    {indIdx cidx params fields consumed : Nat}
    (h : CtorParamSpine ectx refs e a block indIdx cidx params fields consumed) :
    CtorShape ectx block indIdx cidx params fields := by
  induction h with
  | head _ _ _ hshape => exact hshape
  | step _ _ ih => exact ih

private theorem ctorParamSpine_addr {ectx : Ixon.Eval.EvalCtx}
    {refs : Array Ixon.Address} {e : Ixon.Expr} {a block : Ixon.Address}
    {indIdx cidx params fields consumed : Nat}
    (h : CtorParamSpine ectx refs e a block indIdx cidx params fields consumed) :
    CtorAddr ectx a block indIdx cidx := by
  induction h with
  | head _ hres hinfo _ => exact ⟨_, _, hres, hinfo, rfl, rfl, rfl⟩
  | step _ _ ih => exact ih

private theorem recPrefix_shape {ectx refs muts sa} {e : Ixon.Expr}
    {r : Recursor} (h : RecPrefix ectx refs muts sa e r) :
    r.indices.toNat = 0 := by
  cases h with
  | refH _ _ _ _ hi => exact hi
  | recurH _ _ hi => exact hi

private theorem recSpine_shape {ectx refs muts sa} :
    ∀ {e : Ixon.Expr} {r : Recursor} {j : Nat},
    RecSpine ectx refs muts sa e r j →
    r.indices.toNat = 0 := by
  intro e r j h
  induction h with
  | head hp => exact recPrefix_shape hp
  | step _ _ ih => exact ih

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
    Ixon.Eval.eval ectx fuel F env e = .ok v →
    PErase ectx ictx sc F.refs F.selfMuts F.selfAddr mask e e' →
    EnvRel ectx ictx sc F.refs F.selfMuts F.selfAddr mask env ρ →
    ∃ fuel' v', IxIR0.eval ictx fuel' ρ e' = .ok v' ∧ ValRel ectx ictx v v'

/-- A visible indexed recursor spine simulates as one unit.  The result keeps
the complete policy cursor local until every source-only index has been
consumed, so no intermediate target pap is exposed to generic application. -/
private theorem recEraseSpine_sim {bound : Nat}
    (sim : ∀ m, m < bound → SimAt m)
    {ectx : Ixon.Eval.EvalCtx} {ictx : IxIR0.Ctx}
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
          ectx.resolve block = some bc ∧
          F₂.refs = bc.refs ∧
          F₂.selfMuts = Ixon.Eval.selfMutsOf bc.info ∧
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
          [], [], rfl, ?_, (resolveMut_ok hrm).1, rfl, rfl, rfl,
          hmem, hipos, .stop (recPolicy r)⟩
        rw [IxIR0.eval.eq_def]
        dsimp only
        rw [hidecl]
        dsimp only
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
          obtain ⟨n₁, block, idx, F₂, bc, sargs, targs, hfv, hfv',
              hresolve, hFrefs, hFmuts, hFsa, hmem, hipos, hcursor⟩ :=
            fuelIH g (by omega) hpre (by omega) hf
          obtain ⟨n₂, av', hav', hrelA⟩ :=
            sim g (by omega) ectx F env a av sc mask ρ a' ictx
              ha harg henv
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
                sargs ++ [av], targs ++ [av'], rfl, ?_, hresolve,
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
          obtain ⟨n₁, block, idx, F₂, bc, sargs, targs, hfv, hfv',
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
                targs ++ [.erased], rfl, ?_, hresolve, hFrefs, hFmuts,
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
          obtain ⟨n₁, block, idx, F₂, bc, sargs, targs, hfv, hfv',
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
                rfl, hfv', hresolve, hFrefs, hFmuts, hFsa, hmem, hipos,
                hcursor.append_drop⟩

/-- The ι correspondence: given a saturated recursor pap on both
sides, agreeing major analyses (`hmcS`/`htmc` — the same
block-identity peel), and related constructor fields, the source fire
and the target fire terminate related. -/
private theorem fireSim {ectx : Ixon.Eval.EvalCtx} {ictx : IxIR0.Ctx}
    {fuel : Nat} (ih : ∀ m, m < fuel → SimAt m)
    {g'' : Nat} (hg : g'' < fuel)
    {F₂ : Ixon.Eval.Frame} {block : Ixon.Address} {idx : Nat}
    {r : Recursor} {bc : Constant}
    (hresolve : ectx.resolve block = some bc)
    (hFrefs : F₂.refs = bc.refs)
    (hFmuts : F₂.selfMuts = Ixon.Eval.selfMutsOf bc.info)
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
    (hav' : IxIR0.eval ictx n₂ ρ aT = .ok av') :
    ∃ fuel' v', IxIR0.eval ictx fuel' ρ (.app fT aT) = .ok v' ∧
      ValRel ectx ictx v v' := by
  obtain ⟨bc₂, trules, hres2, hienv, hrules⟩ :
      ∃ bc₂ trules,
        Ixon.Eval.resolveMut ectx block idx = .ok (bc₂, .recr r) ∧
        ictx.env (Erase.memberAddr block idx) =
          some (.recursor
            (r.params.toNat + r.motives.toNat + r.minors.toNat)
            (ectx.natBlock == some block) trules) ∧
        RulesRel ectx ictx block idx r bc₂.refs
          (Ixon.Eval.selfMutsOf bc₂.info) r.rules.toList trules.toList := by
    cases hmem with
    | mk hres2 hparams hienv hrules =>
      exact ⟨_, _, hres2, hienv, hrules⟩
  have hbc : bc₂ = bc := by
    have h1 := (resolveMut_ok hres2).1
    rw [hresolve] at h1
    injection h1 with h1'
    exact h1'.symm
  subst hbc
  cases g'' with
  | zero => rw [Ixon.Eval.fire.eq_def] at hfire; simp at hfire
  | succ g₃ =>
    rw [Ixon.Eval.fire.eq_def] at hfire
    dsimp only at hfire
    rw [List.getLast?_concat] at hfire
    dsimp only at hfire
    simp only [Option.isSome_some, Bool.true_and] at hfire
    obtain ⟨checked, hguard⟩ : ∃ checked,
        Ixon.Eval.guardRecMajor (some block) r.params.toNat av =
          .ok checked := by
      cases hgmajor : Ixon.Eval.guardRecMajor (some block) r.params.toNat av with
      | error err => rw [hgmajor, bindErr] at hfire; contradiction
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
        obtain ⟨n₃, v', hv', hrel⟩ := ih gb (by omega) ectx F₂
          (sargs ++ ccargs.drop r.params.toNat).reverse B v
          (some (block, idx)) (recRuleMask r rule.fields.toNat)
          (tfields.reverse ++ targs.reverse ++
            [IxIR0.Value.pap (.rec_ (Erase.memberAddr block idx)
              (r.params.toNat + r.motives.toNat + r.minors.toNat + 1)) []])
          trule.rhs ictx hbody hpB h3
        refine ⟨n₁ + n₂ + n₃ + 5, v', ?_, hrel⟩
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

private theorem simAt : ∀ fuel, SimAt fuel := by
  refine strongNat ?_
  intro fuel ih
  cases fuel with
  | zero =>
    intro ectx F env e v sc mask ρ e' ictx hev hpe henv
    rw [Ixon.Eval.eval.eq_def] at hev
    simp at hev
  | succ n =>
    intro ectx F env e v sc mask ρ e' ictx hev hpe henv
    cases hpe with
    | var hm =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      split at hev
      · rename_i w heq
        injection hev with hv
        subst hv
        obtain ⟨v', hρ, hrel⟩ := envRel_lookup _ henv _ hm heq
        refine ⟨1, v', ?_, hrel⟩
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
        exact ⟨1, .erased, by rw [IxIR0.eval.eq_def], .sort⟩
      · simp at hev
    | allE =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      injection hev with hv
      subst hv
      exact ⟨1, .erased, by rw [IxIR0.eval.eq_def], .pi⟩
    | lamK hnd hpb =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      injection hev with hv
      subst hv
      exact ⟨1, _, by rw [IxIR0.eval.eq_def], .clos henv hpb⟩
    | lamD hd hpb =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      injection hev with hv
      subst hv
      exact ⟨1, _, by rw [IxIR0.eval.eq_def], .clos henv hpb⟩
    | letE hpv hpb =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      rename_i nd ty val body val' body'
      cases hval : Ixon.Eval.eval ectx n F env val with
      | error err => rw [hval, bindErr] at hev; simp at hev
      | ok w =>
        rw [hval, bindOk] at hev
        obtain ⟨n₁, w', hw', hrelW⟩ :=
          ih n (by omega) ectx F env val w sc mask ρ val' ictx hval hpv henv
        obtain ⟨n₂, v', hv', hrel⟩ :=
          ih n (by omega) ectx F (w :: env) body v sc (true :: mask)
            (w' :: ρ) body' ictx hev hpb (.keep hrelW henv)
        refine ⟨n₁ + n₂ + 1, v', ?_, hrel⟩
        rw [IxIR0.eval.eq_def]
        dsimp only
        rw [IxIR0.eval_mono (show n₁ ≤ n₁ + n₂ by omega) hw', bindOk]
        exact IxIR0.eval_mono (show n₂ ≤ n₁ + n₂ by omega) hv'
    | natE hrefs hblob =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      rw [hrefs] at hev
      dsimp only at hev
      rw [hblob] at hev
      dsimp only at hev
      injection hev with hv
      subst hv
      exact ⟨1, _, by rw [IxIR0.eval.eq_def], .litNat⟩
    | strE hrefs hblob =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      rw [hrefs] at hev
      dsimp only at hev
      rw [hblob] at hev
      dsimp only at hev
      injection hev with hv
      subst hv
      exact ⟨1, _, by rw [IxIR0.eval.eq_def], .litStr⟩
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
              (Ixon.Eval.selfMutsOf bc₂.info) r.rules.toList
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
        (r.params.toNat + r.motives.toNat + r.minors.toNat + 1)) [], ?_, ?_⟩
      · rw [IxIR0.eval.eq_def]
        dsimp only
        rw [hslot]
      · rw [hsa]
        exact .papRec hres hrefs hmuts rfl hmem hi0 rfl
          (Nat.zero_le _) (.stop (recRulePolicy r))
    | prjE hpv =>
      rw [Ixon.Eval.eval.eq_def] at hev
      dsimp only at hev
      rename_i tyRef fieldIdx val val'
      cases hval : Ixon.Eval.eval ectx n F env val with
      | error err => rw [hval, bindErr] at hev; simp at hev
      | ok w =>
        rw [hval, bindOk] at hev
        obtain ⟨n₁, w', hw', hrelW⟩ :=
          ih n (by omega) ectx F env val w sc mask ρ val' ictx hval hpv henv
        cases hrelW with
        | sort => dsimp only at hev; simp at hev
        | pi => dsimp only at hev; simp at hev
        | clos _ _ => dsimp only at hev; simp at hev
        | litNat => dsimp only at hev; simp at hev
        | litStr => dsimp only at hev; simp at hev
        | neu => dsimp only at hev; simp at hev
        | papCtor _ _ _ _ _ _ _ _ => dsimp only at hev; simp at hev
        | papRec _ _ _ _ _ _ _ _ _ => dsimp only at hev; simp at hev
        | papRecI _ _ _ _ _ _ _ _ => dsimp only at hev; simp at hev
        | ctorV hshape _haddr hargs hcursor =>
          rename_i block indIdx cidx params fields cargs a fargs
          obtain ⟨bc, ind, ct, hrm, hct, hip, hcp, hcf⟩ := hshape
          dsimp only at hev
          rw [hrm] at hev
          dsimp only at hev
          cases hidx : cargs[ind.params.toNat + fieldIdx.toNat]? with
          | none => rw [hidx] at hev; simp at hev
          | some w0 =>
            rw [hidx] at hev
            dsimp only at hev
            injection hev with hv
            subst hv
            have hidxDrop : (cargs.drop params)[fieldIdx.toNat]? =
                some w0 := by
              rw [List.getElem?_drop]
              simpa [hip] using hidx
            obtain ⟨w0', hidx', hrel0⟩ :=
              valsRel_lookup _ hargs _ hidxDrop
            refine ⟨n₁ + 1, w0', ?_, hrel0⟩
            rw [IxIR0.eval.eq_def]
            dsimp only
            rw [IxIR0.eval_mono (Nat.le_refl n₁) hw', bindOk]
            dsimp only
            rw [hidx']
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
        refine ⟨3, .ctor a cidx [], ?_, .ctorV hshape haddr hargs hcursor⟩
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
          .papCtor hshape haddr rfl rfl (by omega) (by omega) hargs hcursor⟩
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
        | defn hres hinfo hunf hidecl hpe' =>
          rw [hres] at hev
          dsimp only at hev
          rw [hinfo] at hev
          dsimp only at hev
          rw [bind_ok_iff] at hev
          obtain ⟨_, _, hev⟩ := hev
          rw [hunf] at hev
          simp at hev
          obtain ⟨n₁, v', hv', hrel⟩ :=
            ih g (by omega) ectx _ [] _ v none [] [] _ ictx hev hpe' .nil
          refine ⟨n₁ + 1, v', ?_, hrel⟩
          rw [IxIR0.eval.eq_def]
          dsimp only
          rw [hidecl]
          exact hv'
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
                    (.stop [])⟩
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
                      (ctorPolicy 0 (f' + 1))))⟩
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
            refine ⟨3, .erased, ?_, .neu⟩
            rw [IxIR0.eval.eq_def]
            dsimp only
            rw [hidecl]
            dsimp only
            rw [IxIR0.eval.eq_def]
          · simp at hev
          · simp at hev
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
                  (Ixon.Eval.selfMutsOf bc₂.info) r.rules.toList
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
            (r.params.toNat + r.motives.toNat + r.minors.toNat + 1)) [], ?_, ?_⟩
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
          obtain ⟨n₁, fv', hfv', hrelF⟩ :=
            ih n (by omega) ectx F env f fv sc mask ρ f' ictx hf hpf henv
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
                  (targs ++ [IxIR0.Value.erased]), ?_, ?_⟩
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
          | papRecI _ _ _ _ _ hipos _ _ =>
            have hi0 := recSpine_shape hspine
            omega
    | recP hspine =>
      rename_i r
      obtain ⟨n₁, block, idx, F₂, bc, sargs, targs, hv, hv', hresolve,
          hFrefs, hFmuts, hFsa, hmem, hipos, hcursor⟩ :=
        recEraseSpine_sim ih hspine (by omega) hev henv
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
        hipos hindices hfront⟩
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
          obtain ⟨n₁, fv', hfv', hrelF⟩ :=
            ih n (by omega) ectx F env fS fv sc mask ρ fT ictx hf hpf henv
          obtain ⟨n₂, av', hav', hrelA⟩ :=
            ih n (by omega) ectx F env aS av sc mask ρ aT ictx ha hpa henv
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
          | clos henvC hbodyC =>
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
              obtain ⟨n₃, v', hv', hrel⟩ :=
                ih g (by omega) ectx FC (av :: envC) bodyC v scC (bC :: maskC)
                  (av' :: ρC) bodyC' ictx hev hbodyC henv'
              refine ⟨n₁ + n₂ + n₃ + 2, v', ?_, hrel⟩
              rw [IxIR0.eval.eq_def]
              dsimp only
              rw [IxIR0.eval_mono (show n₁ ≤ n₁ + n₂ + n₃ + 1 by omega)
                hfv', bindOk]
              rw [IxIR0.eval_mono (show n₂ ≤ n₁ + n₂ + n₃ + 1 by omega)
                hav', bindOk]
              rw [IxIR0.apply.eq_def]
              dsimp only
              exact IxIR0.eval_mono (show n₃ ≤ n₁ + n₂ + n₃ by omega) hv'
          | neu =>
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
                refine ⟨n₁ + n₂ + 3, .erased, ?_, .neu⟩
                rw [IxIR0.eval.eq_def]
                dsimp only
                rw [IxIR0.eval_mono (show n₁ ≤ n₁ + n₂ + 2 by omega)
                  hfv', bindOk]
                rw [IxIR0.eval_mono (show n₂ ≤ n₁ + n₂ + 2 by omega)
                  hav', bindOk]
                rw [IxIR0.apply.eq_def]
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
                      hcursor'⟩
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
                      .ctorV hshape haddr hargs' hcursor'⟩
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
                        (targs ++ [av']), ?_, ?_⟩
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
                  | clos _ _ => simp [Ixon.Eval.majorCtor.eq_def] at hmc
                  | litStr => simp [Ixon.Eval.majorCtor.eq_def] at hmc
                  | papCtor _ _ _ _ _ _ _ _ =>
                    simp [Ixon.Eval.majorCtor.eq_def] at hmc
                  | papRec _ _ _ _ _ _ _ _ _ =>
                    simp [Ixon.Eval.majorCtor.eq_def] at hmc
                  | papRecI _ _ _ _ _ _ _ _ =>
                    simp [Ixon.Eval.majorCtor.eq_def] at hmc
                  | neu => simp [Ixon.Eval.majorCtor.eq_def] at hmc
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
                    exact fireSim ih (by omega) hresolve hFrefs hFmuts hFsa
                      hmem (indexArgs := []) hlen2 hslen hcursor hmcS htmc
                      hfargs hfire0 hfv' hav'
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
                        exact fireSim ih (by omega) hresolve hFrefs hFmuts
                          hFsa hmem (indexArgs := []) hlen2 hslen hcursor
                          hmcS htmc
                          (by simpa [hp0] using
                            (ValsRel.nil : ValsRel ectx ictx [] []))
                          hfire0 hfv' hav'
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
                        exact fireSim ih (by omega) hresolve hFrefs hFmuts
                          hFsa hmem (indexArgs := []) hlen2 hslen hcursor
                          hmcS htmc
                          (by simpa [hp0] using
                            (ValsRel.cons ValRel.litNat ValsRel.nil))
                          hfire0 hfv' hav'
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
                | clos _ _ => simp [Ixon.Eval.majorCtor.eq_def] at hmc
                | litStr => simp [Ixon.Eval.majorCtor.eq_def] at hmc
                | papCtor _ _ _ _ _ _ _ _ =>
                  simp [Ixon.Eval.majorCtor.eq_def] at hmc
                | papRec _ _ _ _ _ _ _ _ _ =>
                  simp [Ixon.Eval.majorCtor.eq_def] at hmc
                | papRecI _ _ _ _ _ _ _ _ =>
                  simp [Ixon.Eval.majorCtor.eq_def] at hmc
                | neu => simp [Ixon.Eval.majorCtor.eq_def] at hmc
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
                  exact fireSim ih (by omega) hresolve hFrefs hFmuts hFsa
                    hmem (indexArgs := indexArgs) hlen2 hslen hcursor hmcS
                    htmc hfargs hfireI hfv' hav'
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
                      exact fireSim ih (by omega) hresolve hFrefs hFmuts
                        hFsa hmem (indexArgs := indexArgs) hlen2 hslen
                        hcursor hmcS htmc
                        (by simpa [hp0] using
                          (ValsRel.nil : ValsRel ectx ictx [] []))
                        hfireI hfv' hav'
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
                      exact fireSim ih (by omega) hresolve hFrefs hFmuts
                        hFsa hmem (indexArgs := indexArgs) hlen2 hslen
                        hcursor hmcS htmc
                        (by simpa [hp0] using
                          (ValsRel.cons ValRel.litNat ValsRel.nil))
                        hfireI hfv' hav'
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
              obtain ⟨n₃, v', hv', hrel⟩ :=
                ih g (by omega) ectx F (av :: env) body v sc (false :: mask)
                  (.erased :: ρ) bodyT ictx hev hpb (.drop henv)
              have hlamT : IxIR0.eval ictx (n₃ + 1) ρ (.lam .many bodyT) =
                  .ok (.clos .many ρ bodyT) := by rw [IxIR0.eval.eq_def]
              have hboxT : IxIR0.eval ictx (n₃ + 1) ρ .erased =
                  .ok .erased := by rw [IxIR0.eval.eq_def]
              refine ⟨n₃ + 2, v', ?_, hrel⟩
              rw [IxIR0.eval.eq_def]
              dsimp only
              rw [hlamT, bindOk, hboxT, bindOk]
              rw [IxIR0.apply.eq_def]
              dsimp only
              exact hv'
            | ctorP _ hspine _ => cases hspine
            | recP hspine => cases hspine

/-- **The erasure simulation (stages 1 + 2a + 2b).** If a source term
terminates with a value under the Ixon reference semantics, its
erasure terminates under the IxIR₀ semantics with a related value. -/
theorem erasure_sim {fuel : Nat} {ectx : Ixon.Eval.EvalCtx}
    {F : Ixon.Eval.Frame} {env : List Ixon.Eval.Value} {e : Ixon.Expr}
    {v : Ixon.Eval.Value} {sc : Option (Ixon.Address × Nat)}
    {mask : List Bool} {ρ : List IxIR0.Value}
    {e' : IxIR0.Expr} {ictx : IxIR0.Ctx}
    (hev : Ixon.Eval.eval ectx fuel F env e = .ok v)
    (hpe : PErase ectx ictx sc F.refs F.selfMuts F.selfAddr mask e e')
    (henv : EnvRel ectx ictx sc F.refs F.selfMuts F.selfAddr mask env ρ) :
    ∃ fuel' v', IxIR0.eval ictx fuel' ρ e' = .ok v' ∧
      ValRel ectx ictx v v' :=
  simAt fuel ectx F env e v sc mask ρ e' ictx hev hpe henv

/-- Closed-term corollary. -/
theorem erasure_sim_closed {fuel : Nat} {ectx : Ixon.Eval.EvalCtx}
    {F : Ixon.Eval.Frame} {e : Ixon.Expr} {v : Ixon.Eval.Value}
    {e' : IxIR0.Expr} {ictx : IxIR0.Ctx}
    (hev : Ixon.Eval.eval ectx fuel F [] e = .ok v)
    (hpe : PErase ectx ictx none F.refs F.selfMuts F.selfAddr [] e e') :
    ∃ fuel' v', IxIR0.eval ictx fuel' [] e' = .ok v' ∧
      ValRel ectx ictx v v' :=
  erasure_sim hev hpe .nil

/-! ## Sharing composition

Sharing is eliminated semantically before entering `PErase`.  The relation
therefore remains share-free: source evaluation is first transported to the
fully inlined context, frame, environment, and expression, then the existing
simulation theorem applies unchanged. -/

/-- A source value relates to an IxIR₀ value after every captured sharing
table and expression root in the source value has been fully inlined. -/
abbrev InlinedValRel (ectx : Ixon.Eval.EvalCtx) (ictx : IxIR0.Ctx)
    (value : Ixon.Eval.Value) (target : IxIR0.Value) : Prop :=
  ValRel ectx.inlineSharing ictx value.inlineSharing target

/-- General sharing composition.  Successful evaluation under a well-formed
sharing frame is transported to the share-free evaluator, after which an
ordinary `PErase` derivation supplies the existing erasure simulation. -/
theorem erasure_sim_inlineSharing {fuel : Nat}
    {ectx : Ixon.Eval.EvalCtx} {F : Ixon.Eval.Frame}
    {env : List Ixon.Eval.Value} {e : Ixon.Expr} {v : Ixon.Eval.Value}
    {sc : Option (Ixon.Address × Nat)} {mask : List Bool}
    {ρ : List IxIR0.Value} {e' : IxIR0.Expr} {ictx : IxIR0.Ctx}
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
  exact erasure_sim hinlined.1 hpe henv

/-- Closed-term sharing composition, the entry point used by executable
certificates.  No `.share` constructor is added to `PErase`. -/
theorem erasure_sim_inlineSharing_closed {fuel : Nat}
    {ectx : Ixon.Eval.EvalCtx} {F : Ixon.Eval.Frame}
    {e : Ixon.Expr} {v : Ixon.Eval.Value} {e' : IxIR0.Expr}
    {ictx : IxIR0.Ctx} (hctx : ectx.SharingWF) (hF : F.SharingWF)
    (he : Ixon.Sharing.sharesBelow F.sharing.size e = true)
    (hev : Ixon.Eval.eval ectx fuel F [] e = .ok v)
    (hpe : PErase ectx.inlineSharing ictx none F.inlineSharing.refs
      F.inlineSharing.selfMuts F.inlineSharing.selfAddr []
      (Ixon.Sharing.inlineExpr F.sharing e) e') :
    ∃ fuel' v', IxIR0.eval ictx fuel' [] e' = .ok v' ∧
      InlinedValRel ectx ictx v v' := by
  apply erasure_sim_inlineSharing hctx hF .nil he hev hpe
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

end Compilatrix.Sim
