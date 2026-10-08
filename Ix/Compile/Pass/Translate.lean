/- # Pass 3b: the call-site rewrite (design document §4.5, Def 3.5, Def 3.6)

## Contract
Input: a constant `c` of the input environment, and the expansion of every
image-kind auxiliary `a` of every changed Lean block (`a ↦ img(a)`: a λ over
Lean's telescope, its universe parameters and its arity, the number of
leading λs). For a Lean recursor the expansion is the generated image
(Def 3.4, `Ix.Compile.Pass.ImageView`); for `casesOn`, `recOn` and the
Type-level `below`/`brecOn` family it is Lean's own value (Def 3.5: Lean's
auxiliaries over images, no regeneration), itself rewritten.

Output: `base(c)` (Def 3.6), the same constant with every occurrence of such
an `a` replaced:
* **full application** (`a us args`, at least the arity in arguments):
  inline, `img(a)`'s body at `args` developed by hereditary substitution
  (`Ix.Compile.Image.instantiate`, Q10: β, projection of a constructor and η
  at the substituted positions, never ι); arguments beyond the arity stay
  applied;
* **bare or partial occurrence**: left as written, `a` applied to the
  (rewritten) arguments. The Lean name `a` of an image-kind auxiliary of a
  changed block denotes its stored image (decision 3, design document §4.5),
  a λ over Lean's telescope with Lean's type, so it is the eta adapter (Q11).
  No separate image constant (`a._ix`) exists, and `needed` stays empty (the
  field is kept for the record of a bare occurrence, `BARE`).

Every outermost rewritten occurrence is wrapped in the placeholder
`[(_ix.inline, n)]`, and the source occurrence is returned as source `n`:
the compiler stores it in `metaSharing` and turns the placeholder into the
decompile record (`Ix.CompileM.compileKVMap`). Occurrences inside the
arguments of a rewritten occurrence, and inside expansions, carry no record:
the outer record restores them.

At a full application the optimisation passes are tried first
(`RwState.opt?`). A definitional pass's term replaces the inline form. A
proof-justified pass's term (O7–O12) never replaces it under a Lean name
(decision 5, D1): the Lean name keeps the baseline and the definition's
canonical form `c._ix` (Lean's constant renamed) is returned in
`BlockRewrite.canon`, to be rewritten in place (`RwState.inPlace`) by the
driver (`Driver.compileCanon`).

## Faithfulness
Definitional. Inlining is δ of `img(a)` followed by β (hereditary), and the
projection-of-constructor and η steps at substituted positions, so the
rewritten term is definitionally equal to `c` with `a` replaced by `img(a)`;
`img(a)` computes as `a` (its computation rules hold by `rfl`, `pass3`
suite; Def 3.5 values are Lean's values over images). No ι-step is taken, so
a user's `T.rec … (c fs)` stays a redex of the user's. Arguments of members
outside the major's component vanish only when the image does not use them
(nothing *used* is dropped, A3I §4 item 4).

## Canonicity
Faithful only: the baseline is Lean's term over images. A4's definitional
passes (O1-O6) rewrite the inline forms back onto the Ix auxiliaries.

## Side condition and fallback
None: every occurrence is rewritten. The development fails loudly when its
recursion bound (`Ix.Compile.Image.defaultFuel`) or the rewrite's own bound
is exhausted (a compile error naming the constant, never a silent result).

## Non-canonical set and evidence
`BARE` (a bare or partial occurrence: the image constant has Lean's type).
Evidence: the `pass3` suite (fixtures through the kernels, decompile round
trip, the library comparisons).
-/
module
public import Ix.Environment
public import Ix.Compile.Canon.Expr
public import Ix.Compile.Image.Develop
public import Ix.Compile.Pass.Names
public section

namespace Ix.Compile.Pass

open Ix (Name Level Expr ConstantInfo)
open Ix.Compile.Canon (getAppFnArgs mkAppN substLevels)

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
  deriving Inhabited

/-- The number of leading λs. -/
def lamArity : Expr → Nat
  | .lam _ _ b _ _ => lamArity b + 1
  | _ => 0

structure RwState where
  /-- Placeholder index of the first source of this run. -/
  base : Nat
  /-- The source occurrences, placeholder `base + i` for entry `i`. -/
  sources : Array Expr := #[]
  /-- Heads with a bare or partial occurrence (their image constants are
  needed). -/
  needed : Array Name := #[]
  /-- Rewritten expansions. -/
  exps : Std.HashMap Name Expansion := {}
  /-- Results reaching `rw`'s final insertion, keyed by term, record mode
  and definition site. The bare/partial image-head early return is not
  inserted here; do not infer that every visited subterm is memoized.
  See `docs/compiler-passes.md` §6.3. -/
  cache : Std.HashMap (Expr × Bool × Option Name) Expr := {}
  /-- The optimisation passes (`Ix.Compile.Pass.Opt.engineFull`), tried at
  every full application before the image is inlined; `none` keeps the
  baseline. The first argument is `site`; the result carries the canonical
  constants the rewrite references and, when the pass is proof-justified
  (O7–O12, `Opt.isProofJustified`), its name (`none` for a definitional
  pass). -/
  opt? : Option Name → Name → Array Level → Array Expr → Option (Expr × Array ConstantInfo × Option String) :=
    fun _ _ _ _ => none
  /-- The production engine tries all site-independent definitional passes
  before any proof-justified one. After a proof-justified hit its no-site
  retry is therefore known to be empty. Generic callbacks keep the retry. -/
  skipPjRetry : Bool := false
  /-- Canonical constants to compile with the block (reserved `_ix` names):
  the canonical form `c._ix` of a definition `c` where a proof-justified pass
  fires (Lean's constant renamed, rewritten in place by `Driver.compileCanon`),
  and the helpers the passes' rewrites reference (O9/O10: re-typed
  structural handlers, O12: the shared pair-valued helper). -/
  canon : Array ConstantInfo := #[]
  /-- The recorded declines (design document §6.3, obligation 4): tried at
  every full application next to `opt?`; a cause means a pass declined
  because a reference it needs is absent from the input
  (`Ix.Compile.Pass.Opt.O11a.declineCause?`). -/
  decline? : Name → Array Level → Array Expr → Option String := fun _ _ _ => none
  /-- The causes recorded so far, in rewrite order. -/
  declines : Array String := #[]
  /-- The declines recorded while rewriting a cached subterm (same key as
  `cache`). -/
  declineCache : Std.HashMap (Expr × Bool × Option Name) (Array String) := {}
  /-- The definition whose value is being rewritten, where the proof-justified
  passes (O7–O12) may fire: only in the value of a definition, never in a
  type, in a theorem's proof or in a shared expansion, where a rewrite that
  is not a conversion would change a statement or the type a proof is
  checked against. -/
  site : Option Name := none
  /-- Decision 5 (D1): `false` for a Lean constant, whose name keeps the
  faithful form: at a proof-justified rewrite the baseline is kept and
  `pjFired` is set, so that the definition's canonical form `c._ix` is
  emitted; `true` for a canonical constant (an `_ix` name), which takes the
  proof-justified rewrites in place. -/
  inPlace : Bool := false
  /-- A proof-justified pass fired in the value being rewritten (`site`). -/
  pjFired : Bool := false
  /-- The proof-justified passes that fired in the value being rewritten,
  each once, in firing order (a record only: no byte depends on it). -/
  pjPasses : Array String := #[]
  /-- The Lean definitions whose canonical form `c._ix` a proof-justified
  pass wrote (decision 5, D1), with the passes (`pjPasses`): the compile's
  `PJ-FORM-<pass>` record (`CompileEnv.p3PjForms`). A record only. -/
  pjForms : Array (Name × Array String) := #[]
  /-- An expansion's value at the universe levels of an occurrence
  (`substLevels`), per head and levels: the same value at every full
  application with those levels (independent of `site`, `record` and
  `inPlace`: the expansion is rewritten once, with no site). -/
  levelCache : Std.HashMap (Name × Array Level) Expr := {}
  /-- The fuel-free tables of the developments so far
  (`Ix.Compile.Image.instantiateWith`). -/
  dev : Ix.Compile.Image.DevState := {}

abbrev RwM := StateT RwState (Except String)

/-- A recursion bound for one rewrite: the term's depth plus every
expansion's, far below this. -/
def rewriteFuel : Nat := 1 <<< 20

section
variable (expansion? : Name → Except String (Option Expansion))

mutual
/-- The expansion of `n` (rewritten when it is Lean's value), or `none` when
`n` is not an image-kind auxiliary of a changed block. -/
def expansionOf : Nat → Name → RwM (Option Expansion)
  | 0, _ => throw "Pass 3 rewrite: recursion bound exhausted"
  | fuel + 1, n => do
    if let some x := (← get).exps.get? n then return some x
    match ← liftM (expansion? n) with
    | none => return none
    | some x =>
      let x ← if x.needsRewrite then do
          -- an expansion is shared by every site: no proof-justified pass
          let site := (← get).site
          modify fun st => { st with site := none }
          let v ← rw fuel false x.value
          modify fun st => { st with site }
          pure { x with value := v, needsRewrite := false }
        else pure x
      modify fun st => { st with exps := st.exps.insert n x }
      return some x

/-- `base(e)`: every occurrence of an image-kind auxiliary rewritten.
`record` is false inside the arguments of a rewritten occurrence and inside
expansions. -/
def rw : Nat → Bool → Expr → RwM Expr
  | 0, _, _ => throw "Pass 3 rewrite: recursion bound exhausted"
  | fuel + 1, record, e => do
    let site := (← get).site
    if let some r := (← get).cache.get? (e, record, site) then
      -- a cached subterm records its declines again (they belong to the
      -- constant being rewritten now)
      if let some ds := (← get).declineCache.get? (e, record, site) then
        modify fun st => { st with declines := st.declines ++ ds }
      return r
    let before := (← get).declines.size
    let r ← match e with
      | .app .. | .const .. => do
        let (h, args) := getAppFnArgs e
        match h with
        | .const n us _ =>
          match ← expansionOf fuel n with
          | some x =>
            let mut args' : Array Expr := #[]
            for a in args do args' := args'.push (← rw fuel false a)
            if args.size < x.arity then
              -- bare or partial: the Lean name denotes the stored image
              -- constant (Q11), so the occurrence stays as written
              return mkAppN (Expr.mkConst n us) args'
            let st ← get
            let res ← match st.opt? site n us args' with
              | some (e, cs, none) => pure (some (e, cs))
              | some (e, cs, some pass) =>
                if st.inPlace then pure (some (e, cs))
                else do
                  -- a Lean name keeps the faithful form (D1): the baseline
                  -- here, the rewrite in the canonical form `c._ix`
                  modify fun st => { st with
                    pjFired := true
                    pjPasses := if st.pjPasses.contains pass then st.pjPasses else st.pjPasses.push pass }
                  pure (if st.skipPjRetry then none else
                    (st.opt? none n us args').map fun (e, cs, _) => (e, cs))
              | none => pure none
            let body ← match res with
              | some (e, cs) =>
                if !cs.isEmpty then
                  modify fun st => { st with canon := cs.foldl (fun acc c =>
                    if acc.any (·.getCnst.name == c.getCnst.name) then acc else acc.push c) st.canon }
                pure e
              | none => do
                let f ← match (← get).levelCache.get? (n, us) with
                  | some f => pure f
                  | none => do
                    let f := substLevels x.levelParams us x.value
                    modify fun st => { st with levelCache := st.levelCache.insert (n, us) f }
                    pure f
                -- take the tables out of the state, so they are updated in place
                let dev0 := (← get).dev
                modify fun st => { st with dev := {} }
                let (body, dev) ← liftM (Ix.Compile.Image.instantiateWith dev0 f args')
                modify fun st => { st with dev }
                pure body
            if let some cause := (← get).decline? n us args' then
              modify fun st => { st with declines := st.declines.push cause }
            if record then
              let st ← get
              let k := st.base + st.sources.size
              set { st with sources := st.sources.push e }
              pure (Expr.mkMData #[(inlineKey, .ofNat k)] body)
            else pure body
          | none =>
            let mut args' : Array Expr := #[]
            for a in args do args' := args'.push (← rw fuel record a)
            pure (mkAppN h args')
        | _ =>
          let h' ← rw fuel record h
          let mut args' : Array Expr := #[]
          for a in args do args' := args'.push (← rw fuel record a)
          pure (mkAppN h' args')
      | .lam n t b bi _ => do
        pure (Expr.mkLam n (← rw fuel record t) (← rw fuel record b) bi)
      | .forallE n t b bi _ => do
        pure (Expr.mkForallE n (← rw fuel record t) (← rw fuel record b) bi)
      | .letE n t v b nd _ => do
        pure (Expr.mkLetE n (← rw fuel record t) (← rw fuel record v) (← rw fuel record b) nd)
      | .proj s i x _ => do pure (Expr.mkProj s i (← rw fuel record x))
      | .mdata md x _ => do pure (Expr.mkMData md (← rw fuel record x))
      | e => pure e
    modify fun st => { st with
      cache := st.cache.insert (e, record, site) r
      declineCache := if st.declines.size == before then st.declineCache
        else st.declineCache.insert (e, record, site) (st.declines.extract before st.declines.size) }
    return r
end

/-- Rewrite every expression of a constant. -/
def rewriteConstM (ci : ConstantInfo) : RwM ConstantInfo := do
  let go := rw expansion? rewriteFuel true
  let cnst (c : Ix.ConstantVal) : RwM Ix.ConstantVal := do
    pure { c with type := ← go c.type }
  match ci with
  | .axiomInfo v => pure (.axiomInfo { v with cnst := ← cnst v.cnst })
  | .defnInfo v => do
    let cnst' ← cnst v.cnst
    -- the value of a definition is the one place a proof-justified pass may
    -- fire (`RwState.site`)
    modify fun st => { st with site := some v.cnst.name, pjFired := false, pjPasses := #[] }
    let value ← go v.value
    let fired := (← get).pjFired
    let passes := (← get).pjPasses
    let inPlace := (← get).inPlace
    modify fun st => { st with site := none, pjFired := false, pjPasses := #[] }
    if fired && !inPlace then
      modify fun st => { st with pjForms := st.pjForms.push (v.cnst.name, passes) }
      -- decision 5 (D1): the canonical form under `c._ix`, Lean's constant
      -- renamed, rewritten in place when the block's canonical constants
      -- compile (`Driver.compileCanon`)
      let c := ixFormName v.cnst.name
      let cv : Ix.DefinitionVal := { v with cnst := { v.cnst with name := c }, all := #[c] }
      let present := (← get).canon.any fun x => x.getCnst.name == c
      if !present then
        modify fun st => { st with canon := st.canon.push (.defnInfo cv) }
    pure (.defnInfo { v with cnst := cnst', value })
  | .thmInfo v => pure (.thmInfo { v with cnst := ← cnst v.cnst, value := ← go v.value })
  | .opaqueInfo v => pure (.opaqueInfo { v with cnst := ← cnst v.cnst, value := ← go v.value })
  | .quotInfo v => pure (.quotInfo { v with cnst := ← cnst v.cnst })
  | .inductInfo v => pure (.inductInfo { v with cnst := ← cnst v.cnst })
  | .ctorInfo v => pure (.ctorInfo { v with cnst := ← cnst v.cnst })
  | .recInfo v => do
    let mut rules := #[]
    for r in v.rules do rules := rules.push { r with rhs := ← go r.rhs }
    pure (.recInfo { v with cnst := ← cnst v.cnst, rules })

/-- The value of a needed image constant whose expansion is `x`, rewritten. -/
def rewriteExpansionM (n : Name) : RwM (Option Expansion) :=
  expansionOf expansion? rewriteFuel n

end

/-- The result of rewriting one block. -/
structure BlockRewrite where
  /-- The rewritten members that changed. -/
  overlay : Array (Name × ConstantInfo) := #[]
  /-- The source occurrences, placeholder `i` for entry `i`. -/
  sources : Array Expr := #[]
  /-- Heads whose image constants are needed (bare or partial occurrences). -/
  needed : Array Name := #[]
  /-- The recorded declines, each with the member whose term had the
  occurrence (`RwState.decline?`). -/
  declines : Array (Name × String) := #[]
  /-- Canonical constants the passes' rewrites reference (`RwState.canon`). -/
  canon : Array ConstantInfo := #[]
  /-- The members whose canonical form a proof-justified pass wrote, with the
  passes (`RwState.pjForms`). -/
  pjForms : Array (Name × Array String) := #[]
  deriving Inhabited

/-- Rewrite the members of one block (`base(c)` for each); placeholder
indices are block-unique. `inPlace` (D1): the members are canonical constants
(`_ix` names), which take the proof-justified rewrites in place; otherwise
they are Lean constants, which keep the faithful form, and the canonical form
of each one a proof-justified pass fires in is returned in `canon`. -/
def rewriteBlock (expansion? : Name → Except String (Option Expansion))
    (members : Array (Name × ConstantInfo))
    (opt? : Option Name → Name → Array Level → Array Expr → Option (Expr × Array ConstantInfo × Option String) :=
      fun _ _ _ _ => none)
    (decline? : Name → Array Level → Array Expr → Option String := fun _ _ _ => none)
    (inPlace : Bool := false) (skipPjRetry : Bool := false) :
    Except String BlockRewrite := do
  let mut st : RwState := { base := 0, opt?, decline?, inPlace, skipPjRetry }
  let mut overlay : Array (Name × ConstantInfo) := #[]
  let mut declines : Array (Name × String) := #[]
  for (n, ci) in members do
    let before := st.declines.size
    let (ci', st') ← (rewriteConstM expansion? ci).run st
    st := st'
    for c in st.declines.extract before st.declines.size do
      unless declines.contains (n, c) do declines := declines.push (n, c)
    if ci' != ci then overlay := overlay.push (n, ci')
  return { overlay, sources := st.sources, needed := st.needed, declines, canon := st.canon,
           pjForms := st.pjForms }

end Ix.Compile.Pass

end

