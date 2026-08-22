import Compilatrix.Ixon.Const

/-!
# Usage checker v0

Whole-value mode checking over Ixon v2 constants — the checked
pipeline's gate and the future hypothesis supplier for the erasure
simulation (erasure drops 0-mode binders and arguments, which is sound
only when the checker has certified they have no runtime occurrences).

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
erased-mode parameter positions are walked with all recording and
enforcement off — QTT's 0-fragment. Checks:

- **binders** (`lam`): declared `covers` computed; no dereliction is
  built into `covers` (`many` never satisfies a `linear`/`affine`
  demand);
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
tables, through `muts` blocks for projections and `recur`) — readable
without evaluation precisely because modes are data on the binders.

## v0 limitations (recorded, deliberate)

- **Whole-value modes** (gate B): no field-level mixing; modal
  inductives arrive later.
- **Branch-blind counting**: recursor minors are ordinary arguments,
  so a variable used in two minors counts `many` even though one
  branch runs. Conservative; the typed checker (ix4lean extension)
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

namespace Compilatrix.Ixon.UsageCheck

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

end UseVec

/-- The world a binder's value lives in, derived from its declared
usage: `linear`/`affine` are the unique world, `many` the shared one.
(`erased` binders get `shared`; their runtime use already fails the
`covers` check, so the world is never load-bearing.) -/
def worldOf : Uses → Owned
  | .linear | .affine => .unique
  | _ => .shared

/-! ## Errors -/

inductive UsageErr where
  /-- Declared binder usage does not cover the computed usage. -/
  | binderCovers (declared computed : Uses)
  /-- A moved (unique-demand-consumed) variable was used more than
  once in total. -/
  | useAfterMove (computed : Uses)
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
      "(see plans/freeze-contract-2026-08-19.md)"
  | e => reprStr e

/-! ## Telescopes from mode-annotated types -/

/-- Per-argument demand: the parameter's `Uses`, and the `Owned` of
the application's result at that point. -/
abbrev Telescope := List (Uses × Owned)

/-- Syntactic telescope of a type expression, expanding shares against
the owning constant's table. Malformed foreign types degrade to a
shorter (conservative) telescope, never to an error — checking stays
modular. -/
def telescopeOf (sharing : Array Expr) (fuel : Nat) (e : Expr) : Telescope :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    match e with
    | .all u o _ cod => (u, o) :: telescopeOf sharing fuel cod
    | .share i =>
      match sharing[i.toNat]? with
      | some e' => telescopeOf sharing fuel e'
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

def selfMutsOf : ConstantInfo → Array MutConst
  | .muts ms => ms
  | _ => #[]

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
  | e@(.lam ..) => .ok ((Expr.collectLam e).1.map fun (u, _) => (u, .shared))
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
      let (uvB, _) ← check ctx fuel ghost (worldOf u :: ws) body
      let (entry, rest) ← headEntry uvB
      unless ghost do
        unless u.covers entry.uses do throw (.binderCovers u entry.uses)
        if entry.moved && entry.uses != .linear then
          throw (.useAfterMove entry.uses)
        rejectUniqueCaptures 0 rest ws
      return (rest, .unique)
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
        else ((tel[args.length - 1]?).map (·.2)).getD .shared
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
        | some (.erased, _) => do
          -- 0-scaling: the argument is compile-time only.
          discard <| check ctx fuel true ws arg
          pure (UseVec.zeros ws.length)
        | some (q, _) => do
          let argX ← expandShareE ctx fuel arg
          let (uvA, ownA) ← check ctx fuel ghost ws argX
          let uniqueDemand := q == Uses.linear || q == Uses.affine
          if !ghost && uniqueDemand && ownA != .unique then
            throw (.dereliction q)
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

/-! ## Constant-level entry points -/

private def validateBinders : List Uses → UseVec → Except UsageErr Unit
  | [], _ => .ok ()
  | u :: us, entry :: uv => do
    unless u.covers entry.uses do throw (.binderCovers u entry.uses)
    if entry.moved && entry.uses != .linear then
      throw (.useAfterMove entry.uses)
    validateBinders us uv
  | _ :: _, [] => .error (.internal "usage vector shorter than binders")

/-- Peel a definition value's `lam` telescope against its type's `all`
telescope (exact mode agreement), then check the body under the
accumulated binders. `lastOwned` tracks the promised result ownership
of the innermost peeled arrow. -/
def peelDefn (ctx : CheckCtx) (fuel : Nat) (tel : Telescope)
    (lastOwned : Owned) (ws : List Owned) (declared : List Uses)
    (e : Expr) : Except UsageErr Unit :=
  match fuel with
  | 0 => .error .fuel
  | fuel + 1 =>
    match tel, e with
    | (u', o') :: telRest, .lam u ty body => do
      discard <| check ctx fuel true ws ty
      unless u == u' do throw (.lamAllMismatch u u')
      peelDefn ctx fuel telRest o' (worldOf u :: ws) (u :: declared) body
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

private def X : Expr := .ref 0 #[]
private def gRef : Expr := .ref 1 #[]
private def hRef : Expr := .ref 2 #[]
private def freshRef : Expr := .ref 3 #[]
private def fRef : Expr := .ref 4 #[]
private def c0Ref : Expr := .ref 5 #[]
private def eRef : Expr := .ref 6 #[]

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

private def resolver : Address → Option Constant := fun a =>
  (([(aX, cX), (aG, cG), (aH, cH), (aFresh, cFresh), (aF, cF),
     (aC0, cC0), (aE, cE)] : List (Address × Constant)).find?
    (fun p => p.1 == a)).map (·.2)

private def stdRefs : Array Address := #[aX, aG, aH, aFresh, aF, aC0, aE]

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
  "(see plans/freeze-contract-2026-08-19.md)"

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
#guard failsWith (defnConst X (.recur 0 #[]))
  (fun | .badRecurIdx 0 => true | _ => false)

-- Stored definition types are ghost-walked rather than used only as
-- an unchecked telescope hint.
#guard failsWith (defnConst (.ref 99 #[]) c0Ref)
  (fun | .badRefIdx 99 => true | _ => false)

-- `recur` resolves demands through the enclosing muts block.
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

end Compilatrix.Ixon.UsageCheck
