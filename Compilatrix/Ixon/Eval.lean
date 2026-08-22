import Compilatrix.Ixon.Const

/-!
# The Ixon reference evaluator

The **source-side** semantics for the erasure simulation: the unerased
twin of `Compilatrix/IxIR0/Eval.lean`, in the same house style
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
  address configuration, not a name check. Recursor firing checks that its
  block is that configured address and rejects literal majors for recursors
  with parameters.
- **Modes are inert**: `lam`/`all` modes ride in closure values and
  are never consulted — the source half of "modes don't change
  semantics".

Deferred, recorded: quotient ι (`Quot.lift/ind` on `Quot.mk`), K-like
reduction (a defeq rule, not a runtime one), `String.rec` peeling, and
cross-checking `prj`'s type ref. Recursor firing does check constructor-block
agreement (and zero parameters for literal majors): besides rejecting malformed
untyped runs, that runtime fact is the layout equality used when erasure drops
constructor parameters and recursor indices.
-/

namespace Compilatrix.Ixon.Eval

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

def selfMutsOf : ConstantInfo → Array MutConst
  | .muts ms => ms
  | _ => #[]

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
  /-- `block` is the recursor's mutual-block address when known —
  literal ι-peeling fires only when it equals the configured
  `natBlock` (the erased `natLit` flag is set by exactly the same
  comparison, so the two semantics peel in lockstep). -/
  | recH (block : Option Address) (recr : Recursor) (F : Frame)
  | neuH (id : NeutralId)

def Head.arity? : Head → Option Nat
  | .ctorH _ _ _ a => some a
  | .recH _ r _ => some (recArity r)
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
        .ok (.papV (.recH F.selfAddr r { F with uinst := uinst' }) [])
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
    | .recH blk r F =>
      match args.getLast? with
      | none => .error (.stuck "recursor fired with no arguments")
      | some major => do
        guardRecMajor blk r.params.toNat major
        let (cidx, cargs) ← majorCtor (blk.isSome && ctx.natBlock == blk) major
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

/-! ## Fuel monotonicity

Successful evaluation is stable under raising fuel for all six mutually
recursive evaluator functions. This is the composition principle used by
sharing/inlining coherence and source-to-erased simulation proofs.
-/

private theorem bindOk {α β : Type} (a : α) (f : α → Except Err β) :
    (Except.ok a >>= f) = f a := rfl

private theorem bindErr {α β : Type} (e : Err) (f : α → Except Err β) :
    ((Except.error e : Except Err α) >>= f) = Except.error e := rfl

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
                  exact h
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
              exact h
            | true =>
              rw [hu] at h
              simp only [if_true] at h ⊢
              exact ihE _ _ _ _ _ h
        | axio a => rw [hi] at h; simpa using h
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
                  exact h
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
      | recH block r F =>
        rw [fire.eq_def] at h ⊢; dsimp only at h ⊢
        cases hl : args.getLast? with
        | none => rw [hl] at h; simp only at h ⊢; exact h
        | some major =>
          rw [hl] at h
          simp only at h ⊢
          cases hg : guardRecMajor block r.params.toNat major with
          | error err => rw [hg, bindErr] at h; contradiction
          | ok checked =>
            rw [hg, bindOk] at h
            rw [bindOk]
            cases hm : majorCtor (block.isSome && ctx.natBlock == block) major with
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
                cases heq : cargs.length != r.params.toNat + rule.fields.toNat with
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
  induction hle with
  | refl => exact h
  | step _ ih => exact (monoAt _).1 _ _ _ _ _ ih

theorem evalRef_mono {ctx : EvalCtx} {fuel fuel' : Nat} {a : Address}
    {uinst : List Nat} {v : Value} (hle : fuel ≤ fuel')
    (h : evalRef ctx fuel a uinst = .ok v) :
    evalRef ctx fuel' a uinst = .ok v := by
  induction hle with
  | refl => exact h
  | step _ ih => exact (monoAt _).2.1 _ _ _ _ ih

theorem apply_mono {ctx : EvalCtx} {fuel fuel' : Nat} {f a v : Value}
    (hle : fuel ≤ fuel') (h : apply ctx fuel f a = .ok v) :
    apply ctx fuel' f a = .ok v := by
  induction hle with
  | refl => exact h
  | step _ ih => exact (monoAt _).2.2.1 _ _ _ _ ih

theorem applyMany_mono {ctx : EvalCtx} {fuel fuel' : Nat} {f : Value}
    {args : List Value} {v : Value} (hle : fuel ≤ fuel')
    (h : applyMany ctx fuel f args = .ok v) :
    applyMany ctx fuel' f args = .ok v := by
  induction hle with
  | refl => exact h
  | step _ ih => exact (monoAt _).2.2.2.1 _ _ _ _ ih

theorem saturate_mono {ctx : EvalCtx} {fuel fuel' : Nat} {h : Head}
    {args : List Value} {v : Value} (hle : fuel ≤ fuel')
    (hs : saturate ctx fuel h args = .ok v) :
    saturate ctx fuel' h args = .ok v := by
  induction hle with
  | refl => exact hs
  | step _ ih => exact (monoAt _).2.2.2.2.1 _ _ _ _ ih

theorem fire_mono {ctx : EvalCtx} {fuel fuel' : Nat} {h : Head}
    {args : List Value} {v : Value} (hle : fuel ≤ fuel')
    (hs : fire ctx fuel h args = .ok v) :
    fire ctx fuel' h args = .ok v := by
  induction hle with
  | refl => exact hs
  | step _ ih => exact (monoAt _).2.2.2.2.2 _ _ _ _ ih

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
private def aPairBlock := addrOf 0x20
private def aMk := addrOf 0x21
private def aSortAt := addrOf 0x22
private def aDefBlock := addrOf 0x23
private def aDPrj := addrOf 0x24
private def aQuotMk := addrOf 0x25
private def aQuotLift := addrOf 0x26
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

/-- A mutual block with one definition member (`succ zero`), reached
only through a `dPrj`; block refs: 0 = zero, 1 = succ. -/
private def cDefBlock : Constant :=
  { info := .muts #[
      .defn { kind := .defn, safety := .safe, lvls := 0
              typ := .ref 0 #[]
              value := .app (.ref 1 #[]) (.ref 0 #[]) }]
    sharing := #[], refs := #[aZero, aSucc], univs := #[] }

private def cDPrj := prjConst (.dPrj { idx := 0, block := aDefBlock })

/-- Quotient constants (`Quot.mk`/`Quot.lift` stand-ins) — non-unfolding
neutrals under the current evaluator. -/
private def cQuotMk : Constant :=
  { info := .quot { kind := .ctor, lvls := 0, typ := .sort 0 }
    sharing := #[], refs := #[], univs := #[] }

private def cQuotLift : Constant :=
  { info := .quot { kind := .lift, lvls := 0, typ := .sort 0 }
    sharing := #[], refs := #[], univs := #[] }

private def resolver : Address → Option Constant := fun a =>
  (([(aNatBlock, cNatBlock), (aNat, cNat), (aZero, cZero), (aSucc, cSucc),
     (aNatRec, cNatRec), (aAdd, cAdd), (aAx, cAx), (aThm, cThm),
     (aOpq, cOpq), (aPairBlock, cPairBlock), (aMk, cMk),
     (aSortAt, cSortAt), (aDefBlock, cDefBlock), (aDPrj, cDPrj),
     (aQuotMk, cQuotMk), (aQuotLift, cQuotLift)] :
      List (Address × Constant)).find?
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
10 = "hello" blob, 11 = Nat, 12 = unresolvable, 13 = dPrj,
14 = Quot.mk, 15 = Quot.lift. -/
private def testF : Frame :=
  { refs := #[aAdd, aZero, aSucc, aTwo, aThree, aMk, aAx, aThm, aOpq,
              aSortAt, aHello, aNat, aMissing, aDPrj, aQuotMk, aQuotLift]
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

-- dPrj unfolds its definition member through the block frame
#guard runNat? (.ref 13 #[]) == some 1

-- quotient neutrality: source-level quotient ι is deliberately absent,
-- so a `Quot.lift f (Quot.mk x)`-shaped application stays an inert
-- neutral pap. This pin makes a future quotient-ι change visible.
#guard (match run (.app (.app (.ref 15 #[]) (.lam .many (.sort 0) (.var 0)))
    (.app (.ref 14 #[]) (natE 1))) with
  | .ok (.papV (.neuH (.const l)) [_, .papV (.neuH (.const m)) [_]]) =>
    l == aQuotLift && m == aQuotMk
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
#guard (match run (.prj 0 0 (natE 0)) with
  | .error (.stuck _) => true | _ => false)

-- fuel: Ω diverges; a starved success is `.fuel`, not `.stuck`
private def delta : Expr := .lam .many (.sort 0) (.app (.var 0) (.var 0))
#guard (match run (.app delta delta) with
  | .error .fuel => true | _ => false)
#guard (match evalClosed ctx testF
    (.app (.app (.ref 0 #[]) (natE 2)) (natE 3)) (fuel := 10) with
  | .error .fuel => true | _ => false)

end Compilatrix.Ixon.Eval
