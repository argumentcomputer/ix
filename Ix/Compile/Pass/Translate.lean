/- # Pass 3b: the call-site rewrite (Def 3.5, Def 3.6)

## Contract
Input: a constant `c` of the input environment, and the expansion of every
image-kind auxiliary `a` of every changed Lean block (`a ↦ img(a)`: a λ over
Lean's telescope, its universe parameters and its arity, the number of
leading λs). For a Lean recursor the expansion is the generated image
(`Ix.Compile.Pass.ImageView`); for `casesOn`, `recOn` and the Type-level
`below`/`brecOn` family it is Lean's own value (Lean's auxiliaries over
images, no regeneration), itself rewritten.

Output: `base(c)`, the same constant with every occurrence of such an `a`
replaced:
* **full application** (`a us args`, at least the arity in arguments):
  inline, `img(a)`'s body at `args` developed by hereditary substitution
  (`Ix.Compile.Image.instantiateWith`: β, projection of a constructor and η
  at the substituted positions, never ι); arguments beyond the arity stay
  applied;
* **bare or partial occurrence**: left as written, `a` applied to the
  (rewritten) arguments. The Lean name `a` of an image-kind auxiliary of a
  changed block denotes its stored image, a λ over Lean's telescope with
  Lean's type, so it is the eta adapter.

Every outermost rewritten occurrence is wrapped in the placeholder
`[(_ix.inline, n)]`, and the source occurrence is returned as source `n`
(`BlockRewrite.sources`): the compiler stores it in `metaSharing` and turns
the placeholder into the decompile record. Occurrences inside the arguments
of a rewritten occurrence, and inside expansions, carry no record: the outer
record restores them.

At a full application the optimisation passes are tried first
(`RwConfig.opt?`, a parameter: the engines of batch 5 enter here, and none
is linked by this module). A definitional pass's term replaces the inline
form. A proof-justified pass's term never replaces it under a Lean name: the
Lean name keeps the baseline and the definition's canonical form `c._ix`
(Lean's constant renamed) is returned in `BlockRewrite.canon`, to be
rewritten in place (`RwConfig.inPlace`) by the driver.

## Shape (for the statements)
`rw` and `expansionOf` are total: they recurse structurally on an explicit
bound (`rewriteFuel`), and running out of it is an error that names the
bound, never a partial result; the development's own bound is
`Ix.Compile.Image.developFuel`. The configuration (`RwConfig`: the
callbacks, the flags, the first placeholder index and the definition site)
is a reader, so no step of the rewrite can change it; the state
(`RwState`) holds only outputs and caches. Every cache is keyed exactly
(`RwKey`, `LevelsKey`, `ExactName`): a hit is a term, a level list and a
name equal to the request, never one that only shares a stored hash.

## Faithfulness
Definitional. Inlining is δ of `img(a)` followed by β (hereditary), and the
projection-of-constructor and η steps at substituted positions, so the
rewritten term is definitionally equal to `c` with `a` replaced by `img(a)`.
No ι-step is taken, so a user's `T.rec … (c fs)` stays a redex of the user's.

## Side condition and fallback
None: every occurrence is rewritten. An exhausted bound is a compile error
naming the bound (no silent result).
-/
module
public import Ix.Environment
public import Ix.Compile.Canon.Expr
public import Ix.Compile.ExactKey
public import Ix.Compile.Image.Develop
public import Ix.Compile.Pass.Names
public section

namespace Ix.Compile.Pass

open Ix (Name Level Expr ConstantInfo)
open Ix.Compile.Canon (getAppFnArgs mkAppN substLevels)
open Ix.Compile.ExactKey (ExactName exprEq exprEq_eq nameEq nameEq_iff)

/-- The expansion of an image-kind auxiliary: `img(a)`. -/
structure Expansion where
  levelParams : Array Name
  /-- A λ over Lean's telescope. -/
  value : Expr
  /-- The number of leading λs: a full application has at least this many
  arguments. -/
  arity : Nat
  /-- The value is Lean's own (Def 3.5) and must itself be rewritten before
  use; `false` for a generated image (no auxiliary of a changed block in it). -/
  needsRewrite : Bool
  deriving Inhabited, DecidableEq

/-- The number of leading λs. -/
def lamArity : Expr → Nat
  | .lam _ _ b _ _ => lamArity b + 1
  | _ => 0

/-! ## Exact cache keys -/

/-- Two definition sites, compared exactly. -/
def siteEq : Option Name → Option Name → Bool
  | some x, some y => nameEq x y
  | none, none => true
  | _, _ => false

theorem siteEq_iff (a b : Option Name) : siteEq a b = true ↔ a = b := by
  cases a <;> cases b <;> simp [siteEq, nameEq_iff]

/-- The memo key of `rw`: the term, its record mode and the definition
site, compared exactly (the stored hashes only select a bucket). -/
structure RwKey where
  expr : Expr
  record : Bool
  site : Option Name
  deriving DecidableEq

instance : BEq RwKey :=
  ⟨fun a b => exprEq a.expr b.expr && a.record == b.record && siteEq a.site b.site⟩

instance : Hashable RwKey := ⟨fun k => hash (k.expr, k.record, k.site)⟩

instance : LawfulBEq RwKey where
  eq_of_beq {a b} equal := by
    cases a with
    | mk e r s =>
      cases b with
      | mk e' r' s' =>
        change (exprEq e e' && r == r' && siteEq s s') = true at equal
        simp only [Bool.and_eq_true, exprEq_eq, decide_eq_true_eq, beq_iff_eq,
          siteEq_iff] at equal
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := equal
        rfl
  rfl {a} := by
    change (exprEq a.expr a.expr && a.record == a.record && siteEq a.site a.site) = true
    simp only [Bool.and_eq_true, exprEq_eq, decide_eq_true_eq, beq_self_eq_true,
      siteEq_iff, and_self]

instance : LawfulHashable RwKey where
  hash_eq a b same := by
    have equal : a = b := eq_of_beq same
    subst equal
    rfl

/-- The key of an expansion at an occurrence's universe levels: the head and
the levels, compared exactly. -/
structure LevelsKey where
  head : Name
  levels : Array Level
  deriving DecidableEq

instance : BEq LevelsKey :=
  ⟨fun a b => nameEq a.head b.head && decide (a.levels = b.levels)⟩

instance : Hashable LevelsKey := ⟨fun k => hash (k.head, k.levels)⟩

instance : LawfulBEq LevelsKey where
  eq_of_beq {a b} equal := by
    cases a with
    | mk h ls =>
      cases b with
      | mk h' ls' =>
        change (nameEq h h' && decide (ls = ls')) = true at equal
        simp only [Bool.and_eq_true, nameEq_iff, decide_eq_true_eq] at equal
        obtain ⟨rfl, rfl⟩ := equal
        rfl
  rfl {a} := by
    change (nameEq a.head a.head && decide (a.levels = a.levels)) = true
    simp only [Bool.and_eq_true, nameEq_iff, decide_eq_true_eq, and_self]

instance : LawfulHashable LevelsKey where
  hash_eq a b same := by
    have equal : a = b := eq_of_beq same
    subst equal
    rfl

/-! ## Configuration and state -/

/-- Distinct causes, retaining first occurrence order. Effects are sets: a
shared DAG must not turn one diagnostic into exponentially many copies. -/
def mergeDeclines (left right : Array String) : Array String :=
  right.foldl (fun out cause => if out.contains cause then out else out.push cause) left

/-- What a rewrite run reads and never changes. -/
structure RwConfig where
  /-- Placeholder index of the first source of this run. -/
  base : Nat := 0
  /-- The optimisation passes, tried at every full application before the
  image is inlined; `none` keeps the baseline. The first argument is the
  definition site; the result carries the canonical constants the rewrite
  references and, when the pass is proof-justified, its name (`none` for a
  definitional pass). -/
  opt? : Option Name → Name → Array Level → Array Expr →
      Option (Expr × Array ConstantInfo × Option String × Array String) :=
    fun _ _ _ _ => none
  /-- The production engine tries all site-independent definitional passes
  before any proof-justified one, so after a proof-justified hit its no-site
  retry is known to be empty. Generic callbacks keep the retry. -/
  skipPjRetry : Bool := false
  /-- The recorded declines: tried at every full application next to `opt?`;
  a cause means O11a's side condition failed, including an input reference
  its canonical form needs but cannot find. -/
  decline? : Name → Array Level → Array Expr → Option String := fun _ _ _ => none
  /-- `false` for a Lean constant, whose name keeps the faithful form (at a
  proof-justified rewrite the baseline is kept and the canonical form `c._ix`
  is emitted); `true` for a canonical constant (an `_ix` name), which takes
  the proof-justified rewrites in place. -/
  inPlace : Bool := false
  /-- The definition whose value is being rewritten, where the
  proof-justified passes may fire: only in the value of a definition, never
  in a type, in a theorem's proof or in a shared expansion. -/
  site : Option Name := none

/-- A memo entry: the rewritten term, whether it differs from the key's
term (`false`: it **is** the key's term, returned as given), and the
declines recorded while rewriting it (a cached subterm records them again
for the constant being rewritten now). -/
structure RwEntry where
  term : Expr
  changed : Bool
  declines : Array String
  deriving Inhabited

/-- The outputs and caches of a rewrite run. -/
structure RwState where
  /-- The source occurrences, placeholder `base + i` for entry `i`. -/
  sources : Array Expr := #[]
  /-- Rewritten expansions. -/
  exps : Std.HashMap ExactName Expansion := {}
  /-- The rewrite memo: results reaching `rw`'s final insertion, keyed by
  term, record mode and definition site. A bare or partial occurrence of an
  image head returns early and is not inserted. -/
  memo : Std.HashMap RwKey RwEntry := {}
  /-- Canonical constants to compile with the block (reserved `_ix` names):
  the canonical form `c._ix` of a definition where a proof-justified pass
  fires, and the helpers the passes' rewrites reference. -/
  canon : Array ConstantInfo := #[]
  /-- Distinct causes in the current term/expansion/member scope, in first
  occurrence order. Each memo entry retains its own complete scope. -/
  declines : Array String := #[]
  /-- A proof-justified pass fired in the value being rewritten. -/
  pjFired : Bool := false
  /-- The proof-justified passes that fired in the value being rewritten,
  each once, in firing order (a record only). -/
  pjPasses : Array String := #[]
  /-- The Lean definitions whose canonical form a proof-justified pass wrote,
  with the passes (a record only). -/
  pjForms : Array (Name × Array String) := #[]
  /-- An expansion's value at an occurrence's universe levels (independent
  of the site, the record mode and `inPlace`: the expansion is rewritten
  once, with no site). -/
  levelCache : Std.HashMap LevelsKey Expr := {}
  /-- The fuel-free tables of the developments so far
  (`Ix.Compile.Image.instantiateWith`). -/
  dev : Ix.Compile.Image.DevState := {}

abbrev RwM := ReaderT RwConfig (StateT RwState (Except String))

/-- The rewrite's recursion bound: the term's depth plus every expansion's,
far below this. -/
def rewriteFuel : Nat := 1 <<< 20

/-- The error of an exhausted rewrite bound. -/
def rewriteExhausted : String :=
  s!"Pass 3 rewrite: recursion bound rewriteFuel = {rewriteFuel} exhausted"

section
variable (expansion? : Name → Except String (Option Expansion))

mutual
/-- The expansion of `n` (rewritten when it is Lean's value), or `none` when
`n` is not an image-kind auxiliary of a changed block. -/
def expansionOf : Nat → Name → RwM (Option Expansion)
  | 0, _ => throw rewriteExhausted
  | fuel + 1, n => do
    if let some x := (← get).exps.get? n then return some x
    match ← liftM (expansion? n) with
    | none => return none
    | some x =>
      let outer := (← get).declines
      modify fun st => { st with declines := #[] }
      let before ← (fun st : RwState => (st.canon.size, st.pjForms.size)) <$> get
      let x ← if x.needsRewrite then do
          -- an expansion is shared by every site: no proof-justified pass
          let (v, _) ← withReader (fun cfg => { cfg with site := none }) (rw fuel false x.value)
          pure { x with value := v, needsRewrite := false }
        else pure x
      -- An expansion is shared across members: caching a result that made
      -- a decline would lose that member's report on the next hit. The term
      -- memo retains/replays declines, so an effectful expansion is cheap to
      -- revisit without storing a record-free head entry.
      modify fun st =>
        let cacheable := st.declines.isEmpty && (st.canon.size, st.pjForms.size) == before
        { st with declines := mergeDeclines outer st.declines
                  exps := if cacheable then st.exps.insert n x else st.exps }
      return some x

/-- `base(e)`: every occurrence of an image-kind auxiliary rewritten, and
whether anything was (when not, the result is `e` itself). `record` is false
inside the arguments of a rewritten occurrence and inside expansions. -/
def rw : Nat → Bool → Expr → RwM (Expr × Bool)
  | 0, _, _ => throw rewriteExhausted
  | fuel + 1, record, e => do
    let cfg ← read
    let key : RwKey := { expr := e, record, site := cfg.site }
    if let some hit := (← get).memo.get? key then
      -- a cached subterm records its declines again (they belong to the
      -- constant being rewritten now)
      unless hit.declines.isEmpty do
        modify fun st => { st with declines := mergeDeclines st.declines hit.declines }
      return (hit.term, hit.changed)
    -- A fresh scope captures all effects, including causes already seen by
    -- a parent or earlier member. Taking a suffix of a global set loses them.
    let outer := (← get).declines
    modify fun st => { st with declines := #[] }
    let r : Expr × Bool ← match e with
      | .app .. | .const .. => do
        let (h, args) := getAppFnArgs e
        match h with
        | .const n us _ =>
          match ← expansionOf fuel n with
          | some x =>
            let mut args' : Array Expr := #[]
            let mut argsChanged := false
            for a in args do
              let (a', c) ← rw fuel false a
              args' := args'.push a'
              argsChanged := argsChanged || c
            if args.size < x.arity then
              -- bare or partial: the Lean name denotes the stored image, so
              -- the occurrence stays as written (not memoized)
              return (if argsChanged then mkAppN (Expr.mkConst n us) args' else e, argsChanged)
            let res ← match cfg.opt? cfg.site n us args' with
              | some (e, cs, none, reports) => pure (some (e, cs, reports))
              | some (e, cs, some pass, reports) =>
                if cfg.inPlace then pure (some (e, cs, reports))
                else do
                  -- a Lean name keeps the faithful form: the baseline here,
                  -- the rewrite in the canonical form `c._ix`
                  modify fun st => { st with
                    pjFired := true
                    pjPasses := if st.pjPasses.contains pass then st.pjPasses
                      else st.pjPasses.push pass }
                  pure (if cfg.skipPjRetry then none else
                    (cfg.opt? none n us args').map fun (e, cs, _, reports) => (e, cs, reports))
              | none => pure none
            let body ← match res with
              | some (e, cs, reports) =>
                unless reports.isEmpty do modify fun st => { st with declines := mergeDeclines st.declines reports }
                unless cs.isEmpty do
                  let canon := cs.foldl (init := (← get).canon) fun acc c =>
                    if acc.any (fun d => nameEq d.getCnst.name c.getCnst.name) then acc
                    else acc.push c
                  modify fun st => { st with canon }
                pure e
              | none => do
                let lkey : LevelsKey := { head := n, levels := us }
                let f ← match (← get).levelCache.get? lkey with
                  | some f => pure f
                  | none => do
                    let f := substLevels x.levelParams us x.value
                    modify fun st => { st with levelCache := st.levelCache.insert lkey f }
                    pure f
                -- take the tables out of the state, so they are updated in place
                let dev0 := (← get).dev
                modify fun st => { st with dev := {} }
                let (body, dev) ← liftM (Ix.Compile.Image.instantiateWith dev0 f args')
                modify fun st => { st with dev }
                pure body
            if let some cause := cfg.decline? n us args' then
              modify fun st => { st with declines := mergeDeclines st.declines #[cause] }
            if record then
              let st ← get
              let k := cfg.base + st.sources.size
              set { st with sources := st.sources.push e }
              pure (Expr.mkMData #[(inlineKey, .ofNat k)] body, true)
            else pure (body, true)
          | none =>
            let mut args' : Array Expr := #[]
            let mut changed := false
            for a in args do
              let (a', c) ← rw fuel record a
              args' := args'.push a'
              changed := changed || c
            pure (if changed then mkAppN h args' else e, changed)
        | _ =>
          let (h', ch) ← rw fuel record h
          let mut args' : Array Expr := #[]
          let mut changed := ch
          for a in args do
            let (a', c) ← rw fuel record a
            args' := args'.push a'
            changed := changed || c
          pure (if changed then mkAppN h' args' else e, changed)
      | .lam n t b bi _ => do
        let (t', ct) ← rw fuel record t
        let (b', cb) ← rw fuel record b
        pure (if ct || cb then Expr.mkLam n t' b' bi else e, ct || cb)
      | .forallE n t b bi _ => do
        let (t', ct) ← rw fuel record t
        let (b', cb) ← rw fuel record b
        pure (if ct || cb then Expr.mkForallE n t' b' bi else e, ct || cb)
      | .letE n t v b nd _ => do
        let (t', ct) ← rw fuel record t
        let (v', cv) ← rw fuel record v
        let (b', cb) ← rw fuel record b
        pure (if ct || cv || cb then Expr.mkLetE n t' v' b' nd else e, ct || cv || cb)
      | .proj s i x _ => do
        let (x', c) ← rw fuel record x
        pure (if c then Expr.mkProj s i x' else e, c)
      | .mdata md x _ => do
        let (x', c) ← rw fuel record x
        pure (if c then Expr.mkMData md x' else e, c)
      | e => pure (e, false)
    modify fun st => { st with
      declines := mergeDeclines outer st.declines
      memo := st.memo.insert key
        { term := r.1, changed := r.2, declines := st.declines } }
    return r
end

/-- Rewrite every expression of a constant, and whether any changed. -/
def rewriteConstM (ci : ConstantInfo) : RwM (ConstantInfo × Bool) := do
  let go := rw expansion? rewriteFuel true
  let cnst (c : Ix.ConstantVal) : RwM (Ix.ConstantVal × Bool) := do
    let (t, ch) ← go c.type
    pure ({ c with type := t }, ch)
  match ci with
  | .axiomInfo v => do
    let (c, ch) ← cnst v.cnst
    pure (.axiomInfo { v with cnst := c }, ch)
  | .defnInfo v => do
    let (cnst', ct) ← cnst v.cnst
    -- the value of a definition is the one place a proof-justified pass may
    -- fire (`RwConfig.site`)
    modify fun st => { st with pjFired := false, pjPasses := #[] }
    let (value, cv) ← withReader (fun cfg => { cfg with site := some v.cnst.name }) (go v.value)
    let fired := (← get).pjFired
    let passes := (← get).pjPasses
    modify fun st => { st with pjFired := false, pjPasses := #[] }
    if fired && !(← read).inPlace then
      modify fun st => { st with pjForms := st.pjForms.push (v.cnst.name, passes) }
      -- the canonical form under `c._ix`, Lean's constant renamed, rewritten
      -- in place when the block's canonical constants compile
      let c := ixFormName v.cnst.name
      let canonForm : Ix.DefinitionVal := { v with cnst := { v.cnst with name := c }, all := #[c] }
      let present := (← get).canon.any fun x => nameEq x.getCnst.name c
      if !present then
        modify fun st => { st with canon := st.canon.push (.defnInfo canonForm) }
    pure (.defnInfo { v with cnst := cnst', value }, ct || cv)
  | .thmInfo v => do
    let (c, ct) ← cnst v.cnst
    let (value, cv) ← go v.value
    pure (.thmInfo { v with cnst := c, value }, ct || cv)
  | .opaqueInfo v => do
    let (c, ct) ← cnst v.cnst
    let (value, cv) ← go v.value
    pure (.opaqueInfo { v with cnst := c, value }, ct || cv)
  | .quotInfo v => do
    let (c, ch) ← cnst v.cnst
    pure (.quotInfo { v with cnst := c }, ch)
  | .inductInfo v => do
    let (c, ch) ← cnst v.cnst
    pure (.inductInfo { v with cnst := c }, ch)
  | .ctorInfo v => do
    let (c, ch) ← cnst v.cnst
    pure (.ctorInfo { v with cnst := c }, ch)
  | .recInfo v => do
    let (c, ct) ← cnst v.cnst
    let mut rules := #[]
    let mut changed := ct
    for r in v.rules do
      let (rhs, cr) ← go r.rhs
      rules := rules.push { r with rhs }
      changed := changed || cr
    pure (.recInfo { v with cnst := c, rules }, changed)

end

/-- The result of rewriting one block. -/
structure BlockRewrite where
  /-- The rewritten members that changed. -/
  overlay : Array (Name × ConstantInfo) := #[]
  /-- The source occurrences, placeholder `base + i` for entry `i`. -/
  sources : Array Expr := #[]
  /-- The recorded declines, each with the member whose term had the
  occurrence (`RwConfig.decline?`). -/
  declines : Array (Name × String) := #[]
  /-- Canonical constants the passes' rewrites reference. -/
  canon : Array ConstantInfo := #[]
  /-- The members whose canonical form a proof-justified pass wrote, with the
  passes. -/
  pjForms : Array (Name × Array String) := #[]
  deriving Inhabited

/-- Reports do not affect the overlay; retain every distinct cause in a
deterministic order, including recursive O2 causes. -/
def appendMemberDeclines (rows : Array (Name × String)) (n : Name) (reports : Array String) :
    Array (Name × String) :=
  let causes := reports.foldl
    (fun acc c => if acc.contains c then acc else acc.push c) (#[] : Array String)
  if causes.isEmpty then rows
  else rows.push (n, String.intercalate "; " (causes.qsort (· < ·)).toList)

/-- Rewrite the members of one block (`base(c)` for each); placeholder
indices start at `cfg.base` and are block-unique. A member is in the overlay
exactly when the rewrite changed one of its terms. Everything the run
produces is returned; nothing outlives it. -/
def rewriteBlock (expansion? : Name → Except String (Option Expansion))
    (members : Array (Name × ConstantInfo)) (cfg : RwConfig := {}) :
    Except String BlockRewrite := do
  let mut st : RwState := {}
  let mut overlay : Array (Name × ConstantInfo) := #[]
  let mut declines : Array (Name × String) := #[]
  for (n, ci) in members do
    st := { st with declines := #[] }
    let ((ci', changed), st') ← ((rewriteConstM expansion? ci).run cfg).run st
    st := st'
    declines := appendMemberDeclines declines n st.declines
    if changed then overlay := overlay.push (n, ci')
  return { overlay, sources := st.sources, declines, canon := st.canon,
           pjForms := st.pjForms }

end Ix.Compile.Pass

end
