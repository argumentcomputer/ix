import Ix.Compiler.Ixon.Const

/-!
# Usage checker v0

Whole-value mode checking over Ixon v2 constants — the checked
pipeline's gate and the executable hypothesis supplier for erasure
non-interference. Erasure drops explicit 0-mode binders and also ordinary
binders whose domains are syntactically sort-like; the checker uses that
same classification and certifies that their runtime demand is zero.

One bottom-up walk per constant computes, for every subterm:

- a **usage vector**: what each context variable experiences —
  computed usages are `erased` (0), `linear` (1), or `many` (ω);
  `affine` is a declared *permission*, never a computed count — plus a
  `moved` flag (consumed at a unique-demand site);
- a **result ownership** (`Owned`): whether the value may be treated
  as unique.

Composition is CBV-additive (`Uses.add`); `Uses.mul` appears only as
the erasure boundary, realized as **ghost mode**: types (all `lam`/
`all`/`letE` annotations, `all` codomains) and arguments in
eraser-dropped parameter positions are walked with all recording and
enforcement off — QTT's 0-fragment. Checks:

- **binders** (`lam`): declared `covers` computed; no dereliction is
  built into `covers` (`many` never satisfies a `linear`/`affine`
  demand). A binder the eraser classifies as dropped is additionally
  rejected if its computed head use is nonzero;
- **applications**: parameter and argument worlds must agree — a
  `linear`/`affine` parameter demands a `unique` argument, while a
  `many` parameter demands a shared argument. Both dereliction and
  the implicit-freeze direction are rejected in v0;
- **moves**: a bare variable passed at unique demand is `moved`; a
  moved variable's total usage must be exactly `linear`
  (`useAfterMove` otherwise — this is what catches double-moves of
  `let`-bound uniques, which have no declared mode to `covers`-check);
- **definitions**: value `lam` modes must equal the type telescope's
  `all` modes (the kernel-infer/beta-stability direction), and a type
  promising a `unique` result must get a body that synthesizes one.

Parameter demands come from **syntactic telescopes**: `collectAll`-
style walks over referenced constants' types (through their sharing
tables, through `muts` blocks for projections and `recur`). Each demand
carries the eraser-aligned drop decision as well as its mode and result
ownership, so normal `many` polymorphic parameters over `Sort` are
zero-scaled exactly when erasure ghosts them.

This module proves zero usage for every successful ghost walk and exposes
the accepted-lambda head-zero bridge. `Ix.Compiler.UsageSound` aligns the
checker classification with the eraser and derives successful-run semantic
non-interference through their common erased observation.

## v0 limitations (recorded, deliberate)

- **Whole-value modes** (gate B): no field-level mixing; modal
  inductives arrive later.
- **Branch-blind counting**: recursor minors are ordinary arguments,
  so a variable used in two minors counts `many` even though one
  branch runs. Conservative; the typed checker (lean4ix extension)
  will max over minors.
- **Higher-order hole**: positions with unresolvable telescopes
  (variable-headed applications, arguments beyond a known telescope)
  are counted non-erased but NOT dereliction-checked — closing this
  needs types. Sound for counting, incomplete for ownership.
- **Unique-capturing closures are rejected**: captured usages are not
  yet scaled by how often the resulting closure may be called, so v0
  takes the sound conservative route already required by the IxIR₁
  lowerer. A nested closure may capture shared values, but any runtime
  use of a unique outer value is an error. QTT-style capture scaling
  can later admit one-shot/non-freezable closures precisely.
- **Flow collapsed**: `moved ⟹ single use`. True use-after-move
  ordering (move at the last use, freeze-points) needs flow
  sensitivity; with exactly one use the flow is trivial.
- **Projections are shared** (`prj`, and any projection constant's
  result): moving fields out of unique structures is the borrow
  axis's job, later.
- **Strict lets always count**: an inferred-erased `let` still
  evaluates (CBV gate); erasure may drop it only under the
  kernel-totality condition (gate A) — that is erasure's decision,
  not this checker's.
- **No type-level reduction**: telescopes hidden behind redexes
  resolve as unknown.
- **Exact `lam`/`all` mode agreement** for definitions (subsumption
  deferred).
-/

namespace Ix.Compiler.Ixon.UsageCheck

/-! ## Computed usages -/

/-- What checking computes per context variable. -/
structure VarUse where
  uses : Uses := .erased
  moved : Bool := false
  deriving BEq, Repr, Inhabited

/-- Usage vector, aligned with the binder context (index 0 =
innermost). Always use qualified `UseVec.*` calls: dot notation on a
`List` abbrev resolves into `List.*`. -/
abbrev UseVec := List VarUse

namespace UseVec

def zeros (n : Nat) : UseVec := List.replicate n {}

def single (n i : Nat) : UseVec := (zeros n).set i { uses := .linear }

def singleMoved (n i : Nat) : UseVec :=
  (zeros n).set i { uses := .linear, moved := true }

def add (a b : UseVec) : UseVec :=
  List.zipWith (fun x y => { uses := x.uses.add y.uses, moved := x.moved || y.moved }) a b

/-- The one executable use of multiplicative grading: erase every recorded
runtime demand at a source-only boundary. Nonzero modes are deliberately not
scaled; they compose through `add` plus the flow-sensitive ownership rules. -/
def zeroScale : UseVec → UseVec
  | [] => []
  | use :: rest =>
    { uses := Uses.mul .erased use.uses, moved := false } :: zeroScale rest

@[simp] theorem zeros_zero : zeros 0 = [] := rfl

@[simp] theorem zeros_succ (n : Nat) :
    zeros (n + 1) = {} :: zeros n := by
  rw [zeros, List.replicate_succ]
  rfl

@[simp] theorem add_zeros (n : Nat) :
    add (zeros n) (zeros n) = zeros n := by
  simp [add, zeros]

@[simp] theorem zeroScale_eq_zeros (uses : UseVec) :
    zeroScale uses = zeros uses.length := by
  induction uses with
  | nil => rfl
  | cons use rest ih =>
    simp [zeroScale, zeros, List.replicate_succ, ih]

end UseVec

#guard UseVec.zeroScale
    [{ uses := .many, moved := true }, { uses := .linear, moved := true }] ==
  UseVec.zeros 2

/-- The world a binder's value lives in, derived from its declared
usage: `linear`/`affine` are the unique world, `many` the shared one.
(`erased` binders get `shared`; their runtime use already fails the
`covers` check, so the world is never load-bearing.) -/
def worldOf : Uses → Owned
  | .linear | .affine => .unique
  | _ => .shared

/-- A fresh closure with only reusable runtime parameters and a shared
result uses the existing shared-PAP representation. Successful lambda
checking separately rules out unique captures. Erased parameters disappear
before that representation is selected. Other callable modes retain the
unique classification and the existing downstream restrictions. -/
def closureWorld (uses : Uses) (result : Owned) : Owned :=
  if (uses == .many || uses == .erased) && result == .shared then .shared else .unique

theorem closureWorld_shared_iff {uses : Uses} {result : Owned} :
    closureWorld uses result = .shared ↔
      (uses = .many ∨ uses = .erased) ∧ result = .shared := by
  cases uses <;> cases result <;> simp [closureWorld]

/-! ## Errors -/

inductive UsageErr where
  /-- Declared binder usage does not cover the computed usage. -/
  | binderCovers (declared computed : Uses)
  /-- A moved (unique-demand-consumed) variable was used more than
  once in total. -/
  | useAfterMove (computed : Uses)
  /-- The eraser classifies a sort-like binder as compile-time-only,
  but checking found a runtime use of its value. -/
  | typeBinderRuntimeUse (computed : Uses)
  /-- A shared value was supplied where a `linear`/`affine` parameter
  demands a unique one. -/
  | dereliction (demanded : Uses)
  /-- A unique value reached a non-unique sink. The v0 checker and
  lowering deliberately reject this implicit coercion until a deep
  freeze operation has a representation and cost model. -/
  | freezeNeeded
  /-- A definition value's `lam` mode differs from its type's `all`
  mode at the same telescope position. -/
  | lamAllMismatch (lamUses allUses : Uses)
  /-- The definition's type promises a `unique` result but the body
  synthesizes a shared one. -/
  | resultNotUnique (got : Owned)
  /-- A nested closure uses a unique value from its outer context.
  Such captures need multiplicity scaling/one-shot closure support. -/
  | uniqueCapture (idx : Nat)
  /-- A nonempty type telescope was implemented without the matching
  leading lambda telescope. -/
  | definitionExpectedLambda (remaining : Nat)
  | unboundVar (idx : Nat)
  | badShareIdx (idx : Nat)
  | badRefIdx (idx : Nat)
  | badRecurIdx (idx : Nat)
  | fuel
  | internal (msg : String)
  deriving BEq, Repr

/-- Stable user-facing diagnostic for the v0 freeze restriction. -/
def UsageErr.message : UsageErr → String
  | .freezeNeeded =>
      "freeze not in v0: unique value at non-unique sink " ++
      "(see docs/compiler/lowering-restrictions.md)"
  | e => reprStr e

/-! ## Telescopes from mode-annotated types -/

/-- Syntactic sort-valued telescope test, deliberately identical to the
eraser's `sortLike`.  It lives here as well because UsageCheck is the
upstream gate and does not import the erasure layer. -/
def erasureSortLike (sharing : Array Expr) : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, e =>
    match e with
    | .sort _ => true
    | .all _ _ _ codomain => erasureSortLike sharing fuel codomain
    | .share index =>
      match sharing[index.toNat]? with
      | some target => erasureSortLike sharing fuel target
      | none => false
    | _ => false

/-- Binder classification shared extensionally with erasure: an explicit
zero-mode binder or a syntactically sort-valued telescope is dropped. -/
def erasureDropsBinder (sharing : Array Expr) (fuel : Nat)
    (uses : Uses) (domain : Expr) : Bool :=
  uses == .erased || erasureSortLike sharing fuel domain

/-- Per-argument demand: the declared mode, the application's result world
at that point, and the eraser-aligned zero-scaling decision.  The third field
matters for ordinary Lean-style type parameters whose declared mode is
`many` but whose domain is sort-like. -/
structure Demand where
  uses : Uses
  owned : Owned
  dropped : Bool

abbrev Telescope := List Demand

/-- Syntactic telescope of a type expression, expanding shares against
the owning constant's table. Malformed foreign types degrade to a
shorter (conservative) telescope, never to an error — checking stays
modular. -/
def telescopeOf (sharing : Array Expr) (fuel : Nat) (e : Expr) : Telescope :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    match e with
    | .all uses owned domain codomain =>
      { uses, owned
        dropped := erasureDropsBinder sharing fuel uses domain } ::
        telescopeOf sharing fuel codomain
    | .share index =>
      match sharing[index.toNat]? with
      | some target => telescopeOf sharing fuel target
      | none => []
    | _ => []

def mutTyp : MutConst → Expr
  | .defn d => d.typ
  | .indc i => i.typ
  | .recr r => r.typ

/-- A constant's type together with the sharing table it must be read
against — chasing projection constants into their `muts` blocks. -/
def constTypeSharing (resolve : Address → Option Constant) (c : Constant) :
    Option (Expr × Array Expr) :=
  match c.info with
  | .defn d => some (d.typ, c.sharing)
  | .recr r => some (r.typ, c.sharing)
  | .axio a => some (a.typ, c.sharing)
  | .quot q => some (q.typ, c.sharing)
  | .muts _ => none
  | .iPrj p => do
    let blk ← resolve p.block
    match blk.info with
    | .muts ms =>
      match ms[p.idx.toNat]? with
      | some (.indc i) => some (i.typ, blk.sharing)
      | _ => none
    | _ => none
  | .cPrj p => do
    let blk ← resolve p.block
    match blk.info with
    | .muts ms =>
      match ms[p.idx.toNat]? with
      | some (.indc i) => do
        let ct ← i.ctors[p.cidx.toNat]?
        some (ct.typ, blk.sharing)
      | _ => none
    | _ => none
  | .rPrj p => do
    let blk ← resolve p.block
    match blk.info with
    | .muts ms =>
      match ms[p.idx.toNat]? with
      | some (.recr r) => some (r.typ, blk.sharing)
      | _ => none
    | _ => none
  | .dPrj p => do
    let blk ← resolve p.block
    match blk.info with
    | .muts ms =>
      match ms[p.idx.toNat]? with
      | some (.defn d) => some (d.typ, blk.sharing)
      | _ => none
    | _ => none

/-! ## The checker -/

/-- Checking context: how to resolve foreign constants, plus the
current constant's tables (and block members, for `recur`). -/
structure CheckCtx where
  resolve : Address → Option Constant
  sharing : Array Expr := #[]
  refs : Array Address := #[]
  selfMuts : Array MutConst := #[]

def defaultFuel : Nat := 100000

/-- Expand top-level shares (for head/argument shape analysis). -/
def expandShareE (ctx : CheckCtx) (fuel : Nat) (e : Expr) :
    Except UsageErr Expr :=
  match fuel with
  | 0 => .error .fuel
  | fuel + 1 =>
    match e with
    | .share i =>
      match ctx.sharing[i.toNat]? with
      | none => .error (.badShareIdx i.toNat)
      | some e' => expandShareE ctx fuel e'
    | e => .ok e

/-- Demand telescope of an application head. Unresolvable heads yield
`[]` (conservative: count, don't ownership-check); a `lam` head
supplies its binder usages with unknown (shared) results. -/
def telescopeOfHead (ctx : CheckCtx) (fuel : Nat) : Expr → Except UsageErr Telescope
  | .ref idx _ =>
    match ctx.refs[idx.toNat]? with
    | none => .error (.badRefIdx idx.toNat)
    | some a =>
      match ctx.resolve a with
      | none => .ok []
      | some c =>
        match constTypeSharing ctx.resolve c with
        | none => .ok []
        | some (typ, sh) => .ok (telescopeOf sh fuel typ)
  | .recur idx _ =>
    match ctx.selfMuts[idx.toNat]? with
    | none => .error (.badRecurIdx idx.toNat)
    | some m => .ok (telescopeOf ctx.sharing fuel (mutTyp m))
  | e@(.lam ..) => .ok ((Expr.collectLam e).1.map fun (uses, domain) =>
      { uses, owned := .shared
        dropped := erasureDropsBinder ctx.sharing fuel uses domain })
  | _ => .ok []

private def headEntry : UseVec → Except UsageErr (VarUse × UseVec)
  | e :: rest => .ok (e, rest)
  | [] => .error (.internal "empty usage vector at binder")

/-- v0 closure rule: shared captures may be duplicated with RC, but a
runtime use of a unique outer value would require a one-shot closure
or QTT scaling that this checker/lowerer pair does not yet model. -/
private def rejectUniqueCaptures : Nat → UseVec → List Owned →
    Except UsageErr Unit
  | _, [], [] => .ok ()
  | i, use :: uses, world :: worlds =>
    if use.uses != .erased && world == .unique then
      .error (.uniqueCapture i)
    else
      rejectUniqueCaptures (i + 1) uses worlds
  | _, _, _ => .error (.internal "capture vector/world length mismatch")

mutual

/-- Compute the usage vector and result ownership of `e` under binder
worlds `ws`. `ghost` is the 0-fragment: walk for well-formedness, but
record nothing and enforce no usage checks. -/
def check (ctx : CheckCtx) (fuel : Nat) (ghost : Bool) (ws : List Owned)
    (e : Expr) : Except UsageErr (UseVec × Owned) :=
  match fuel with
  | 0 => .error .fuel
  | fuel + 1 =>
    match e with
    | .var i =>
      match ws[i.toNat]? with
      | none => .error (.unboundVar i.toNat)
      | some w =>
        if ghost then .ok (UseVec.zeros ws.length, .shared)
        else .ok (UseVec.single ws.length i.toNat, w)
    | .sort _ => .ok (UseVec.zeros ws.length, .shared)
    | .str _ => .ok (UseVec.zeros ws.length, .unique)
    | .nat _ => .ok (UseVec.zeros ws.length, .unique)
    | .ref idx _ =>
      if ctx.refs[idx.toNat]?.isNone then .error (.badRefIdx idx.toNat)
      else .ok (UseVec.zeros ws.length, .shared)
    | .recur idx _ =>
      if ctx.selfMuts[idx.toNat]?.isNone then
        .error (.badRecurIdx idx.toNat)
      else
        .ok (UseVec.zeros ws.length, .shared)
    | .prj _ _ val => do
      let (uv, _) ← check ctx fuel ghost ws val
      return (uv, .shared)
    | .lam u ty body => do
      discard <| check ctx fuel true ws ty
      let (uvB, ownB) ← check ctx fuel ghost (worldOf u :: ws) body
      let (entry, rest) ← headEntry uvB
      unless ghost do
        unless u.covers entry.uses do throw (.binderCovers u entry.uses)
        if erasureDropsBinder ctx.sharing fuel u ty &&
            entry.uses != .erased then
          throw (.typeBinderRuntimeUse entry.uses)
        if entry.moved && entry.uses != .linear then
          throw (.useAfterMove entry.uses)
        rejectUniqueCaptures 0 rest ws
      return (rest, closureWorld u ownB)
    | .all _ _ ty cod => do
      discard <| check ctx fuel true ws ty
      discard <| check ctx fuel true (.shared :: ws) cod
      return (UseVec.zeros ws.length, .shared)
    | .letE _ ty val body => do
      discard <| check ctx fuel true ws ty
      let (uvV, ownV) ← check ctx fuel ghost ws val
      if !ghost && ownV == .unique then
        throw .freezeNeeded
      let (uvB, ownB) ← check ctx fuel ghost (ownV :: ws) body
      let (entry, rest) ← headEntry uvB
      unless ghost do
        if entry.moved && entry.uses != .linear then
          throw (.useAfterMove entry.uses)
      return (UseVec.add uvV rest, ownB)
    | .app f a => do
      let (args, base₀) := Expr.collectApp (.app f a)
      let base ← expandShareE ctx fuel base₀
      let tel ← telescopeOfHead ctx fuel base
      let (uvBase, _) ← check ctx fuel ghost ws base
      let uv ← checkArgs ctx fuel ghost ws tel 0 args uvBase
      let own := if ghost then Owned.shared
        else ((tel[args.length - 1]?).map (·.owned)).getD .shared
      return (uv, own)
    | .share i =>
      match ctx.sharing[i.toNat]? with
      | none => .error (.badShareIdx i.toNat)
      | some e' => check ctx fuel ghost ws e'
  termination_by fuel

/-- Fold an application spine's arguments (position `i` against the
telescope) into the accumulated usage vector. -/
def checkArgs (ctx : CheckCtx) (fuel : Nat) (ghost : Bool)
    (ws : List Owned) (tel : Telescope) (i : Nat) (args : List Expr)
    (acc : UseVec) : Except UsageErr UseVec :=
  match fuel with
  | 0 => .error .fuel
  | fuel + 1 =>
    match args with
    | [] => .ok acc
    | arg :: rest => do
      let contrib ← match tel[i]? with
        | some demand =>
          if demand.dropped then
            do
              -- 0-scaling: the argument is compile-time only.
              let (uvA, _) ← check ctx fuel true ws arg
              pure (UseVec.zeroScale uvA)
          else
            do
              let argX ← expandShareE ctx fuel arg
              let (uvA, ownA) ← check ctx fuel ghost ws argX
              let uniqueDemand := demand.uses == Uses.linear ||
                demand.uses == Uses.affine
              if !ghost && uniqueDemand && ownA != .unique then
                throw (.dereliction demand.uses)
              if !ghost && !uniqueDemand && ownA == .unique then
                throw .freezeNeeded
              pure <| if !ghost && uniqueDemand then
                  match argX with
                  | .var j => UseVec.singleMoved ws.length j.toNat
                  | _ => uvA
                else uvA
        | none => do
          -- Unknown demand: count (non-erased), no ownership check.
          let (uvA, _) ← check ctx fuel ghost ws arg
          pure uvA
      checkArgs ctx fuel ghost ws tel (i + 1) rest (UseVec.add acc contrib)
  termination_by fuel

end

/-! ## Executable-checker metatheory

The first invariant makes the QTT zero fragment mechanical: a successful
ghost walk contributes exactly the all-zero vector.  It is proved against the
real mutually recursive checker, including application-spine collection and
sharing expansion, rather than against a parallel declarative approximation.
-/

private def GhostZeroAt (fuel : Nat) : Prop :=
  (∀ ctx ws e uv own,
      check ctx fuel true ws e = .ok (uv, own) →
      uv = UseVec.zeros ws.length) ∧
  (∀ ctx ws tel i args uv,
      checkArgs ctx fuel true ws tel i args (UseVec.zeros ws.length) =
          .ok uv →
      uv = UseVec.zeros ws.length)

@[simp] private theorem exceptBindOk {α β : Type} (a : α)
    (f : α → Except UsageErr β) :
    (Except.ok a >>= f) = f a := rfl

@[simp] private theorem exceptBindErr {α β : Type} (err : UsageErr)
    (f : α → Except UsageErr β) :
    (Except.error err >>= f) = Except.error err := rfl

@[simp] private theorem exceptBindPure {α β : Type} (a : α)
    (f : α → Except UsageErr β) :
    (do let x ← (pure a : Except UsageErr α); f x) = f a := rfl

@[simp] private theorem exceptDiscardOk {α : Type} (a : α) :
    discard (Except.ok a : Except UsageErr α) = .ok () := rfl

@[simp] private theorem exceptDiscardErr {α : Type} (err : UsageErr) :
    discard (Except.error err : Except UsageErr α) = .error err := rfl

@[simp] private theorem exceptThrow {α : Type} (err : UsageErr) :
    (throw err : Except UsageErr α) = .error err := rfl

private theorem exceptOkPairFst {α β : Type} {a b : α} {x y : β}
    (h : (Except.ok (a, x) : Except UsageErr (α × β)) = .ok (b, y)) :
    a = b :=
  congrArg Prod.fst (Except.ok.inj h)

private theorem ghostZeroAt : ∀ fuel, GhostZeroAt fuel := by
  intro fuel
  induction fuel with
  | zero =>
    constructor
    · intro ctx ws e uv own h
      simp [check] at h
    · intro ctx ws tel i args uv h
      simp [checkArgs] at h
  | succ fuel ih =>
    obtain ⟨ihCheck, ihArgs⟩ := ih
    constructor
    · intro ctx ws e uv own h
      cases e with
      | var idx =>
        rw [check.eq_def] at h
        dsimp only at h
        split at h <;> simp_all
      | sort idx =>
        rw [check.eq_def] at h
        exact (exceptOkPairFst h).symm
      | str idx =>
        rw [check.eq_def] at h
        exact (exceptOkPairFst h).symm
      | nat idx =>
        rw [check.eq_def] at h
        exact (exceptOkPairFst h).symm
      | ref idx univs =>
        rw [check.eq_def] at h
        dsimp only at h
        split at h <;> simp_all
      | recur idx univs =>
        rw [check.eq_def] at h
        dsimp only at h
        split at h <;> simp_all
      | prj typeIdx fieldIdx value =>
        rw [check.eq_def] at h
        dsimp only at h
        cases hv : check ctx fuel true ws value with
        | error err =>
          rw [hv] at h
          simp only [exceptBindErr] at h
          contradiction
        | ok result =>
          rcases result with ⟨valueUses, valueOwn⟩
          have hzero := ihCheck _ _ _ _ _ hv
          rw [hv] at h
          simp only [exceptBindOk] at h
          exact (exceptOkPairFst h).symm.trans hzero
      | lam uses domain body =>
        rw [check.eq_def] at h
        dsimp only at h
        cases hd : check ctx fuel true ws domain with
        | error err =>
          rw [hd] at h
          contradiction
        | ok domainResult =>
          rw [hd] at h
          cases hb : check ctx fuel true (worldOf uses :: ws) body with
          | error err =>
            rw [hb] at h
            simp only [exceptBindErr] at h
            contradiction
          | ok bodyResult =>
            rcases bodyResult with ⟨bodyUses, bodyOwn⟩
            rw [hb] at h
            simp only [exceptBindOk] at h
            cases he : headEntry bodyUses with
            | error err =>
              rw [he] at h
              simp only [exceptBindErr] at h
              contradiction
            | ok entryRest =>
              rcases entryRest with ⟨entry, rest⟩
              have hzero := ihCheck _ _ _ _ _ hb
              have heShape := he
              rw [hzero] at heShape
              simp [headEntry] at heShape
              rw [he] at h
              simp only [exceptBindOk, if_true] at h
              exact (exceptOkPairFst h).symm.trans heShape.2.symm
      | all uses owned domain codomain =>
        rw [check.eq_def] at h
        dsimp only at h
        cases hd : check ctx fuel true ws domain with
        | error err =>
          rw [hd] at h
          contradiction
        | ok domainResult =>
          rw [hd] at h
          cases hc : check ctx fuel true (.shared :: ws) codomain with
          | error err =>
            rw [hc] at h
            contradiction
          | ok codomainResult =>
            rw [hc] at h
            exact (exceptOkPairFst h).symm
      | letE nondep type value body =>
        rw [check.eq_def] at h
        dsimp only at h
        cases ht : check ctx fuel true ws type with
        | error err =>
          rw [ht] at h
          simp only at h
          contradiction
        | ok typeResult =>
          rw [ht] at h
          simp only at h
          cases hv : check ctx fuel true ws value with
          | error err =>
            rw [hv] at h
            simp only [exceptBindErr] at h
            contradiction
          | ok valueResult =>
            rcases valueResult with ⟨valueUses, valueOwn⟩
            rw [hv] at h
            simp only [exceptBindOk, Bool.not_true, Bool.false_and] at h
            cases hb : check ctx fuel true (valueOwn :: ws) body with
            | error err =>
              rw [hb] at h
              simp only [exceptBindErr] at h
              contradiction
            | ok bodyResult =>
              rcases bodyResult with ⟨bodyUses, bodyOwn⟩
              rw [hb] at h
              simp only [exceptBindOk] at h
              cases he : headEntry bodyUses with
              | error err =>
                rw [he] at h
                simp only [exceptBindErr] at h
                contradiction
              | ok entryRest =>
                rcases entryRest with ⟨entry, rest⟩
                have hvzero := ihCheck _ _ _ _ _ hv
                have hbzero := ihCheck _ _ _ _ _ hb
                have heShape := he
                rw [hbzero] at heShape
                simp [headEntry] at heShape
                rw [he] at h
                simp only [exceptBindOk, if_true] at h
                rw [← exceptOkPairFst h, hvzero, ← heShape.2]
                exact UseVec.add_zeros ws.length
      | app function argument =>
        rw [check.eq_def] at h
        dsimp only at h
        let collected := Expr.collectApp (.app function argument)
        cases hx : expandShareE ctx fuel collected.2 with
        | error err =>
          rw [show Expr.collectApp (.app function argument) = collected from rfl,
            hx] at h
          simp only [exceptBindErr] at h
          contradiction
        | ok base =>
          rw [show Expr.collectApp (.app function argument) = collected from rfl,
            hx] at h
          simp only [exceptBindOk] at h
          cases ht : telescopeOfHead ctx fuel base with
          | error err =>
            rw [ht] at h
            simp only [exceptBindErr] at h
            contradiction
          | ok telescope =>
            rw [ht] at h
            simp only [exceptBindOk] at h
            cases hb : check ctx fuel true ws base with
            | error err =>
              rw [hb] at h
              simp only [exceptBindErr] at h
              contradiction
            | ok baseResult =>
              rcases baseResult with ⟨baseUses, baseOwn⟩
              rw [hb] at h
              simp only [exceptBindOk] at h
              cases ha : checkArgs ctx fuel true ws telescope 0 collected.1
                  baseUses with
              | error err =>
                rw [ha] at h
                simp only [exceptBindErr] at h
                contradiction
              | ok argsUses =>
                have hzero := ihCheck _ _ _ _ _ hb
                have haZero := ha
                rw [hzero] at haZero
                have hazero := ihArgs _ _ _ _ _ _ haZero
                rw [ha] at h
                simp only [exceptBindOk, if_true] at h
                exact (exceptOkPairFst h).symm.trans hazero
      | share idx =>
        rw [check.eq_def] at h
        dsimp only at h
        cases hs : ctx.sharing[idx.toNat]? with
        | none =>
          rw [hs] at h
          contradiction
        | some shared =>
          rw [hs] at h
          exact ihCheck _ _ _ _ _ h
    · intro ctx ws tel i args uv h
      cases args with
      | nil =>
        rw [checkArgs.eq_def] at h
        exact (Except.ok.inj h).symm
      | cons argument rest =>
        rw [checkArgs.eq_def] at h
        dsimp only at h
        cases hp : tel[i]? with
        | none =>
          rw [hp] at h
          simp only at h
          cases ha : check ctx fuel true ws argument with
          | error err =>
            rw [ha] at h
            simp only [exceptBindErr] at h
            contradiction
          | ok argResult =>
            rcases argResult with ⟨argUses, argOwn⟩
            have hzero := ihCheck _ _ _ _ _ ha
            rw [ha] at h
            simp only [exceptBindOk] at h
            simp only [exceptBindPure] at h
            rw [hzero, UseVec.add_zeros] at h
            exact ihArgs _ _ _ _ _ _ h
        | some policy =>
          rcases policy with ⟨demandUses, resultOwn, dropped⟩
          cases dropped with
          | true =>
            rw [hp] at h
            simp only [if_true] at h
            cases ha : check ctx fuel true ws argument with
            | error err =>
              rw [ha] at h
              contradiction
            | ok argResult =>
              rcases argResult with ⟨argUses, argOwn⟩
              have hzero := ihCheck _ _ _ _ _ ha
              rw [ha] at h
              simp only [exceptBindOk, exceptBindPure] at h
              rw [hzero, UseVec.zeroScale_eq_zeros] at h
              have hlength : (UseVec.zeros ws.length).length = ws.length := by
                simp [UseVec.zeros]
              rw [hlength, UseVec.add_zeros] at h
              exact ihArgs _ _ _ _ _ _ h
          | false =>
            rw [hp] at h
            simp only [Bool.false_eq_true, if_false] at h
            cases hx : expandShareE ctx fuel argument with
            | error err =>
              rw [hx] at h
              simp only [exceptBindErr] at h
              contradiction
            | ok expanded =>
              rw [hx] at h
              simp only [exceptBindOk] at h
              cases ha : check ctx fuel true ws expanded with
              | error err =>
                rw [ha] at h
                simp only [exceptBindErr] at h
                contradiction
              | ok argResult =>
                rcases argResult with ⟨argUses, argOwn⟩
                have hzero := ihCheck _ _ _ _ _ ha
                rw [ha] at h
                simp only [exceptBindOk] at h
                simp only [Bool.not_true, Bool.false_and,
                  Bool.false_eq_true, if_false,
                  exceptBindPure] at h
                rw [hzero, UseVec.add_zeros] at h
                exact ihArgs _ _ _ _ _ _ h

/-- Successful ghost checking records no runtime use of any binder. -/
theorem check_ghost_zeros {ctx : CheckCtx} {fuel : Nat}
    {ws : List Owned} {e : Expr} {uv : UseVec} {own : Owned}
    (h : check ctx fuel true ws e = .ok (uv, own)) :
    uv = UseVec.zeros ws.length :=
  (ghostZeroAt fuel).1 _ _ _ _ _ h

/-- Public elimination rule for the checker's private binder-vector splitter.
Clients can consume checker certificates without depending on its helper's
implementation name. -/
theorem headEntry_ok_iff {uses : UseVec} {entry : VarUse} {rest : UseVec} :
    headEntry uses = .ok (entry, rest) ↔ uses = entry :: rest := by
  cases uses <;> simp [headEntry]

/-- Every captured unique context entry has zero runtime demand. The relation
also records that the usage vector and context have the same length. -/
inductive SharedCaptures : UseVec → List Owned → Prop where
  | nil : SharedCaptures [] []
  | cons {use : VarUse} {world : Owned} {uses : UseVec} {worlds : List Owned}
      (head : world = .unique → use.uses = .erased)
      (tail : SharedCaptures uses worlds) :
      SharedCaptures (use :: uses) (world :: worlds)

private theorem rejectUniqueCaptures_shared {start : Nat} {uses : UseVec}
    {worlds : List Owned} (h : rejectUniqueCaptures start uses worlds = .ok ()) :
    SharedCaptures uses worlds := by
  induction uses generalizing start worlds with
  | nil =>
    cases worlds with
    | nil => exact .nil
    | cons world worlds => simp [rejectUniqueCaptures] at h
  | cons use uses ih =>
    cases worlds with
    | nil => simp [rejectUniqueCaptures] at h
    | cons world worlds =>
      simp only [rejectUniqueCaptures] at h
      split at h
      · contradiction
      · rename_i safe
        exact .cons (by intro unique; simpa [unique] using safe) (ih h)

/-- Inversion of the actual runtime checker: a lambda classified as shared
has a reusable or erased parameter, a body that synthesizes shared, and no
runtime capture of a unique value. No conversion of an existing unique value
is hidden in the fresh-closure classification. -/
theorem check_lam_shared {ctx : CheckCtx} {fuel : Nat} {worlds : List Owned}
    {uses : Uses} {domain body : Expr} {outerUses : UseVec}
    (hcheck : check ctx (fuel + 1) false worlds (.lam uses domain body) =
      .ok (outerUses, .shared)) :
    (uses = .many ∨ uses = .erased) ∧ SharedCaptures outerUses worlds ∧
      ∃ entry, check ctx fuel false (worldOf uses :: worlds) body =
        .ok (entry :: outerUses, .shared) := by
  rw [check.eq_def] at hcheck
  dsimp only at hcheck
  cases hd : check ctx fuel true worlds domain with
  | error err => rw [hd] at hcheck; contradiction
  | ok domainResult =>
    rw [hd] at hcheck
    cases hb : check ctx fuel false (worldOf uses :: worlds) body with
    | error err =>
      rw [hb] at hcheck
      simp only [exceptBindErr] at hcheck
      contradiction
    | ok bodyResult =>
      rcases bodyResult with ⟨bodyUses, bodyOwn⟩
      rw [hb] at hcheck
      simp only [exceptBindOk] at hcheck
      cases he : headEntry bodyUses with
      | error err =>
        rw [he] at hcheck
        simp only [exceptBindErr] at hcheck
        contradiction
      | ok entryRest =>
        rcases entryRest with ⟨entry, rest⟩
        rw [he] at hcheck
        by_cases hcovers : uses.covers entry.uses = true
        · by_cases hdrop : erasureDropsBinder ctx.sharing fuel uses domain = true ∧
              entry.uses ≠ .erased
          · simp [hcovers, hdrop, exceptThrow, exceptBindErr] at hcheck
          · by_cases hmove : entry.moved = true ∧ entry.uses ≠ .linear
            · simp [hcovers, hdrop, hmove, exceptThrow, exceptBindErr] at hcheck
            · cases hc : rejectUniqueCaptures 0 rest worlds with
              | error err =>
                simp [hcovers, hdrop, hmove, hc, Functor.map, Except.map] at hcheck
              | ok done =>
                cases done
                have result : rest = outerUses ∧ closureWorld uses bodyOwn = .shared := by
                  simpa [hcovers, hdrop, hmove, hc, Functor.map, Except.map] using hcheck
                have classification := closureWorld_shared_iff.mp result.2
                rcases result with ⟨rfl, _⟩
                refine ⟨classification.1, rejectUniqueCaptures_shared hc, entry, ?_⟩
                rw [headEntry_ok_iff.mp he, classification.2]
        · simp [hcovers, exceptThrow, exceptBindErr] at hcheck

/-- If the executable checker accepts a lambda whose binder the executable
eraser classifies as dropped, the body's computed usage for that binder is
exactly zero.  This covers both explicit `Uses.erased` and sort-like type
binders; the latter is the gate condition that was previously implicit. -/
theorem check_lam_dropped_entry_erased {ctx : CheckCtx} {fuel : Nat}
    {ws : List Owned} {uses : Uses} {domain body : Expr}
    {outerUses : UseVec} {own : Owned}
    (hdrop : erasureDropsBinder ctx.sharing fuel uses domain = true)
    (hcheck : check ctx (fuel + 1) false ws (.lam uses domain body) =
      .ok (outerUses, own)) :
    ∃ bodyUses bodyOwn entry rest,
      check ctx fuel false (worldOf uses :: ws) body =
        .ok (bodyUses, bodyOwn) ∧
      headEntry bodyUses = .ok (entry, rest) ∧
      entry.uses = .erased := by
  rw [check.eq_def] at hcheck
  dsimp only at hcheck
  cases hd : check ctx fuel true ws domain with
  | error err =>
    rw [hd] at hcheck
    contradiction
  | ok domainResult =>
    rw [hd] at hcheck
    cases hb : check ctx fuel false (worldOf uses :: ws) body with
    | error err =>
      rw [hb] at hcheck
      simp only [exceptBindErr] at hcheck
      contradiction
    | ok bodyResult =>
      rcases bodyResult with ⟨bodyUses, bodyOwn⟩
      rw [hb] at hcheck
      simp only [exceptBindOk] at hcheck
      cases he : headEntry bodyUses with
      | error err =>
        rw [he] at hcheck
        simp only [exceptBindErr] at hcheck
        contradiction
      | ok entryRest =>
        rcases entryRest with ⟨entry, rest⟩
        have hentry : entry.uses = .erased := by
          by_cases hzero : entry.uses = .erased
          · exact hzero
          · by_cases hcovers : uses.covers entry.uses = true
            · simp [he, hcovers, hdrop, hzero, exceptThrow,
                exceptBindErr] at hcheck
            · simp [he, hcovers, exceptThrow, exceptBindErr] at hcheck
        exact ⟨bodyUses, bodyOwn, entry, rest, rfl, he, hentry⟩

/-! ## Constant-level entry points -/

private def validateBinders : List (Uses × Bool) → UseVec →
    Except UsageErr Unit
  | [], _ => .ok ()
  | (u, dropped) :: us, entry :: uv => do
    unless u.covers entry.uses do throw (.binderCovers u entry.uses)
    if dropped && entry.uses != .erased then
      throw (.typeBinderRuntimeUse entry.uses)
    if entry.moved && entry.uses != .linear then
      throw (.useAfterMove entry.uses)
    validateBinders us uv
  | _ :: _, [] => .error (.internal "usage vector shorter than binders")

/-- Peel a definition value's `lam` telescope against its type's `all`
telescope (exact mode agreement), then check the body under the
accumulated binders. `lastOwned` tracks the promised result ownership
of the innermost peeled arrow. -/
def peelDefn (ctx : CheckCtx) (fuel : Nat) (tel : Telescope)
    (lastOwned : Owned) (ws : List Owned)
    (declared : List (Uses × Bool))
    (e : Expr) : Except UsageErr Unit :=
  match fuel with
  | 0 => .error .fuel
  | fuel + 1 =>
    match tel, e with
    | demand :: telRest, .lam u ty body => do
      discard <| check ctx fuel true ws ty
      unless u == demand.uses do throw (.lamAllMismatch u demand.uses)
      peelDefn ctx fuel telRest demand.owned (worldOf u :: ws)
        ((u, erasureDropsBinder ctx.sharing fuel u ty) :: declared) body
    | tel', .share i =>
      match ctx.sharing[i.toNat]? with
      | none => .error (.badShareIdx i.toNat)
      | some e' => peelDefn ctx fuel tel' lastOwned ws declared e'
    | [], body => do
      let (uv, own) ← check ctx fuel false ws body
      if lastOwned == .unique && own != .unique then
        throw (.resultNotUnique own)
      if lastOwned != .unique && own == .unique then
        throw .freezeNeeded
      validateBinders declared uv
    | remaining, _ => throw (.definitionExpectedLambda remaining.length)
  termination_by fuel

def checkDefinition (resolve : Address → Option Constant) (c : Constant)
    (d : Definition) (fuel : Nat := defaultFuel) : Except UsageErr Unit := do
  let ctx : CheckCtx :=
    { resolve, sharing := c.sharing, refs := c.refs
      selfMuts := selfMutsOf c.info }
  discard <| check ctx fuel true [] d.typ
  peelDefn ctx fuel (telescopeOf c.sharing fuel d.typ) .shared [] [] d.value

def checkRecursor (ctx : CheckCtx) (fuel : Nat) (r : Recursor) :
    Except UsageErr Unit := do
  discard <| check ctx fuel true [] r.typ
  for rule in r.rules do
    -- Rule right-hand sides are closed runtime terms.
    discard <| check ctx fuel false [] rule.rhs

/-- Check one constant, resolving references through `resolve`.
Modular: unresolvable (but well-indexed) references degrade to
conservative unknowns, never errors. -/
def checkConstant (resolve : Address → Option Constant) (c : Constant)
    (fuel : Nat := defaultFuel) : Except UsageErr Unit := do
  let ctx : CheckCtx :=
    { resolve, sharing := c.sharing, refs := c.refs
      selfMuts := selfMutsOf c.info }
  match c.info with
  | .defn d => checkDefinition resolve c d fuel
  | .recr r => checkRecursor ctx fuel r
  | .axio a => discard <| check ctx fuel true [] a.typ
  | .quot q => discard <| check ctx fuel true [] q.typ
  | .cPrj _ | .rPrj _ | .iPrj _ | .dPrj _ => pure ()
  | .muts ms =>
    for m in ms do
      match m with
      | .defn d => checkDefinition resolve c d fuel
      | .indc i => do
        discard <| check ctx fuel true [] i.typ
        for ct in i.ctors do
          discard <| check ctx fuel true [] ct.typ
      | .recr r => checkRecursor ctx fuel r

/-! ## Elaboration-time tests

A hand-written mini-environment: `X : Sort`, functions over it with
every demand shape, and definitions exercising each rule. Reference
convention for test definitions: refs = `#[X, g, h, fresh, f, c0, e]`.
-/

private def addrOf (n : UInt8) : Address :=
  Address.replicate n

private def aX := addrOf 1
private def aG := addrOf 2      -- g : X ⊸ X (linear param, unique result)
private def aH := addrOf 3      -- h : X →ω X (shared)
private def aFresh := addrOf 4  -- fresh : X →ω X^unique
private def aF := addrOf 5      -- f : X →ω X →ω X
private def aC0 := addrOf 6     -- c0 : X
private def aE := addrOf 7      -- e : ∀^0 (A : Sort), X ⊸ X
private def aApply := addrOf 8  -- apply : (X →ω X) →ω X

private def X : Expr := .ref 0 #[]
private def gRef : Expr := .ref 1 #[]
private def hRef : Expr := .ref 2 #[]
private def freshRef : Expr := .ref 3 #[]
private def fRef : Expr := .ref 4 #[]
private def c0Ref : Expr := .ref 5 #[]
private def eRef : Expr := .ref 6 #[]
private def applyRef : Expr := .ref 7 #[]

private def axConst (refs : Array Address) (typ : Expr) : Constant :=
  { info := .axio { isUnsafe := false, lvls := 0, typ }
    sharing := #[], refs, univs := #[.zero] }

private def cX := axConst #[] (.sort 0)
private def cG := axConst #[aX] (.all .linear .unique X X)
private def cH := axConst #[aX] (.all .many .shared X X)
private def cFresh := axConst #[aX] (.all .many .unique X X)
private def cF := axConst #[aX] (.all .many .shared X (.all .many .shared X X))
private def cC0 := axConst #[aX] X
private def cE := axConst #[aX]
  (.all .erased .shared (.sort 0) (.all .linear .unique X X))
private def cApply := axConst #[aX]
  (.all .many .shared (.all .many .shared X X) X)

private def resolver : Address → Option Constant := fun a =>
  (([(aX, cX), (aG, cG), (aH, cH), (aFresh, cFresh), (aF, cF),
     (aC0, cC0), (aE, cE), (aApply, cApply)] : List (Address × Constant)).find?
    (fun p => p.1 == a)).map (·.2)

private def stdRefs : Array Address := #[aX, aG, aH, aFresh, aF, aC0, aE, aApply]

private def defnConst (typ value : Expr) (sharing : Array Expr := #[]) :
    Constant :=
  { info := .defn { kind := .defn, safety := .safe, lvls := 0, typ, value }
    sharing, refs := stdRefs, univs := #[.zero] }

private def ok? (c : Constant) : Bool :=
  match checkConstant resolver c with
  | .ok _ => true
  | .error _ => false

private def failsWith (c : Constant) (p : UsageErr → Bool) : Bool :=
  match checkConstant resolver c with
  | .error e => p e
  | .ok _ => false

-- The axioms themselves check (ghost type walks).
#guard ok? cX
#guard ok? cG
#guard ok? cE

-- Lean fragment: the ω identity, and an ω term that duplicates.
#guard ok? (defnConst (.all .many .shared X X) (.lam .many X (.var 0)))
#guard ok? (defnConst (.all .many .shared X X)
  (.lam .many X (.app (.app fRef (.app hRef (.var 0))) (.var 0))))
-- ... and the leanFragment predicate agrees it is vanilla Lean.
#guard (Expr.leanFragment (.lam .many X (.app (.app fRef (.var 0)) (.var 0))))

-- The linear identity: unique in, unique out.
#guard ok? (defnConst (.all .linear .unique X X) (.lam .linear X (.var 0)))

-- Fresh reusable closures use the shared PAP ABI, including let binding,
-- shared capture, and an erased parameter ahead of the runtime telescope.
#guard ok? (defnConst X (.app applyRef (.lam .many X (.var 0))))
#guard ok? (defnConst X
  (.letE true (.all .many .shared X X) (.lam .many X (.var 0))
    (.app applyRef (.var 0))))
#guard ok? (defnConst (.all .many .shared X X)
  (.lam .many X (.app applyRef (.lam .many X (.var 1)))))
#guard match check { resolve := resolver, refs := stdRefs } 100 false []
    (.lam .erased (.sort 0) (.lam .many X (.var 0))) with
  | .ok ([], .shared) => true
  | _ => false

-- Neighboring callable modes/results still cannot enter shared storage.
#guard failsWith (defnConst X (.app applyRef (.lam .affine X c0Ref)))
  (fun | .freezeNeeded => true | _ => false)
#guard failsWith (defnConst X (.app applyRef (.lam .linear X (.var 0))))
  (fun | .freezeNeeded => true | _ => false)
#guard failsWith (defnConst X
  (.app applyRef (.lam .many X (.app freshRef (.var 0)))))
  (fun | .freezeNeeded => true | _ => false)
#guard failsWith (defnConst (.all .linear .shared X X)
  (.lam .linear X (.app applyRef (.lam .many X (.app gRef (.var 1))))))
  (fun | .uniqueCapture 0 => true | _ => false)

-- Affine weakening: an affine argument may be unused.
#guard ok? (defnConst (.all .affine .shared X X) (.lam .affine X c0Ref))

-- Erased type parameter: ghost in types, one real use of `a`.
#guard ok? (defnConst
  (.all .erased .shared (.sort 0) (.all .many .shared (.var 0) (.var 1)))
  (.lam .erased (.sort 0) (.lam .many (.var 0) (.var 0))))

-- 0-scaling: the same variable in an erased argument position (killed)
-- and a real one (counted once) — linear is satisfied.
#guard ok? (defnConst (.all .linear .unique X X)
  (.lam .linear X (.app (.app eRef (.var 0)) (.var 0))))

-- Moves: a linear binder moved into g (bare-var unique demand).
#guard ok? (defnConst (.all .linear .unique X X)
  (.lam .linear X (.app gRef (.var 0))))

-- Ixon lets have no ownership mode and erasure pins them to `.many`,
-- so a unique initializer is rejected before the old implicit freeze.
#guard failsWith (defnConst (.all .many .shared X X)
  (.lam .many X
    (.letE true X (.app freshRef (.var 0)) (.app gRef (.var 0)))))
  (fun | .freezeNeeded => true | _ => false)

-- Shares resolve through the sharing table (x duplicated via share).
#guard ok? (defnConst (.all .many .shared X X)
  (.lam .many X (.app (.app fRef (.share 0)) (.share 0)))
  (sharing := #[.var 0]))

-- A nested freely-copyable closure may not capture a unique outer
-- value until one-shot closures / capture multiplicity are modeled.
#guard failsWith
  (defnConst
    (.all .linear .unique X X)
    (.lam .linear X (.lam .many X (.var 1))))
  (fun | .uniqueCapture 0 => true | _ => false)

-- Erased binder used at runtime.
#guard failsWith
  (defnConst (.all .erased .shared X X) (.lam .erased X (.var 0)))
  (fun | .binderCovers .erased .linear => true | _ => false)

-- A sort-like binder is erased even when its declared mode is `many`; the
-- checker must therefore reject a computed runtime read before erasure.
#guard failsWith
  (defnConst (.all .many .shared (.sort 0) (.sort 0))
    (.lam .many (.sort 0) (.var 0)))
  (fun | .typeBinderRuntimeUse .linear => true | _ => false)

-- Type-only use of that same binder stays in the zero fragment and passes.
#guard ok? (defnConst
  (.all .many .shared (.sort 0)
    (.all .many .shared (.var 0) (.var 1)))
  (.lam .many (.sort 0) (.lam .many (.var 0) (.var 0))))

-- Unused linear binder (no silent leaks).
#guard failsWith
  (defnConst (.all .linear .shared X X) (.lam .linear X c0Ref))
  (fun | .binderCovers .linear .erased => true | _ => false)

-- Linear binder used twice.
#guard failsWith
  (defnConst (.all .linear .shared X X)
    (.lam .linear X (.app (.var 0) (.var 0))))
  (fun | .binderCovers .linear .many => true | _ => false)

-- Affine binder used twice (dup needs `many`).
#guard failsWith
  (defnConst (.all .affine .shared X X)
    (.lam .affine X (.app (.var 0) (.var 0))))
  (fun | .binderCovers .affine .many => true | _ => false)

-- Freeze: a linear (unique-world) binder at h's `many` sink. This is
-- the minimal checker-accepted/lowering-rejected witness closed by
-- the v0 freeze contract.
#guard failsWith
  (defnConst (.all .linear .shared X X)
    (.lam .linear X (.app hRef (.var 0))))
  (fun | .freezeNeeded => true | _ => false)

-- Dereliction: a shared (ω-bound) variable where g demands linear.
#guard failsWith
  (defnConst (.all .many .shared X X) (.lam .many X (.app gRef (.var 0))))
  (fun | .dereliction .linear => true | _ => false)

-- Dereliction via let: h's result is shared, g demands unique.
#guard failsWith
  (defnConst (.all .many .shared X X)
    (.lam .many X
      (.letE true X (.app hRef (.var 0)) (.app gRef (.var 0)))))
  (fun | .dereliction .linear => true | _ => false)

-- A unique let is now rejected at its shared-pinned installation
-- boundary, before move-flow validation can inspect its body.
#guard failsWith
  (defnConst (.all .many .shared X X)
    (.lam .many X
      (.letE true X (.app freshRef (.var 0))
        (.app (.app fRef (.app gRef (.var 0))) (.app gRef (.var 0))))))
  (fun | .freezeNeeded => true | _ => false)

-- Value/type mode mismatch (beta stability).
#guard failsWith
  (defnConst (.all .linear .shared X X) (.lam .many X (.var 0)))
  (fun | .lamAllMismatch .many .linear => true | _ => false)

-- Eta-contracted values cannot bypass the declared function
-- telescope; v0 requires an explicit matching lambda chain.
#guard failsWith
  (defnConst (.all .many .shared X X) hRef)
  (fun | .definitionExpectedLambda 1 => true | _ => false)

-- Promised unique result, shared body (an ω-bound variable).
#guard failsWith
  (defnConst (.all .many .unique X X) (.lam .many X (.var 0)))
  (fun | .resultNotUnique .shared => true | _ => false)

-- The converse result mismatch would require an implicit freeze.
#guard failsWith
  (defnConst (.all .many .shared X X)
    (.lam .many X (.app freshRef (.var 0))))
  (fun | .freezeNeeded => true | _ => false)

#guard UsageErr.freezeNeeded.message ==
  "freeze not in v0: unique value at non-unique sink " ++
  "(see docs/compiler/lowering-restrictions.md)"

-- ... whereas returning fresh's result keeps the promise.
#guard ok? (defnConst (.all .many .unique X X)
  (.lam .many X (.app freshRef (.var 0))))

-- Structural errors: bad indices are malformedness, not conservatism.
#guard failsWith (defnConst X (.share 5))
  (fun | .badShareIdx 5 => true | _ => false)
#guard failsWith (defnConst X (.ref 99 #[]))
  (fun | .badRefIdx 99 => true | _ => false)
#guard failsWith (defnConst X (.var 5))
  (fun | .unboundVar 5 => true | _ => false)
#guard ok? (defnConst X (.recur 0 #[]))
#guard failsWith (defnConst X (.recur 1 #[]))
  (fun | .badRecurIdx 1 => true | _ => false)

-- Stored definition types are ghost-walked rather than used only as
-- an unchecked telescope hint.
#guard failsWith (defnConst (.ref 99 #[]) c0Ref)
  (fun | .badRefIdx 99 => true | _ => false)

-- `recur` resolves both singleton-collapsed standalones and explicit muts.
#guard ok?
  { info := .muts #[.defn
      { kind := .defn, safety := .safe, lvls := 0
        typ := .all .many .shared X X
        value := .lam .many X (.app (.recur 0 #[]) (.var 0)) }]
    sharing := #[], refs := #[aX], univs := #[.zero] }

-- The dedicated recursor entry point checks both the stored type and
-- closed rule bodies (including their binder usage).
#guard ok?
  { info := .recr
      { k := false, isUnsafe := false, lvls := 0
        params := 0, indices := 0, motives := 0, minors := 0
        typ := .sort 0
        rules := #[{ fields := 1, rhs := .lam .many X (.var 0) }] }
    sharing := #[], refs := #[aX], univs := #[.zero] }

end Ix.Compiler.Ixon.UsageCheck
