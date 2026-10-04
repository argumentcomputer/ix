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
* **bare or partial occurrence**: the image constant `a._ix` applied to the
  arguments (Q11: the image constant is the eta adapter); `a` is recorded as
  needed, and the driver compiles `a._ix` as an ordinary constant.

Every outermost rewritten occurrence is wrapped in the placeholder
`[(_ix.inline, n)]`, and the source occurrence is returned as source `n`:
the compiler stores it in `metaSharing` and turns the placeholder into the
decompile record (`Ix.CompileM.compileKVMap`). Occurrences inside the
arguments of a rewritten occurrence, and inside expansions, carry no record:
the outer record restores them.

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
  cache : Std.HashMap (Expr × Bool × Option Name) Expr := {}
  /-- The optimisation passes (`Ix.Compile.Pass.Opt.engine`), tried at every
  full application before the image is inlined; `none` keeps the baseline.
  The first argument is `site`. -/
  opt? : Option Name → Name → Array Level → Array Expr → Option (Expr × Array ConstantInfo) :=
    fun _ _ _ _ => none
  /-- Canonical constants the passes' rewrites reference (reserved `_ix`
  names, O9: the re-typed structural handler), to be compiled with the block. -/
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
  passes (O7, O8) may fire: only in the value of a definition, never in a
  type, in a theorem's proof or in a shared expansion, where a rewrite that
  is not a conversion would change a statement or the type a proof is
  checked against. -/
  site : Option Name := none

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
            let body ← match (← get).opt? site n us args' with
              | some (e, cs) =>
                if !cs.isEmpty then
                  modify fun st => { st with canon := cs.foldl (fun acc c =>
                    if acc.any (·.getCnst.name == c.getCnst.name) then acc else acc.push c) st.canon }
                pure e
              | none => liftM (Ix.Compile.Image.instantiate (substLevels x.levelParams us x.value) args')
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
    modify fun st => { st with site := some v.cnst.name }
    let value ← go v.value
    modify fun st => { st with site := none }
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
  deriving Inhabited

/-- Rewrite the members of one block (`base(c)` for each); placeholder
indices are block-unique. -/
def rewriteBlock (expansion? : Name → Except String (Option Expansion))
    (members : Array (Name × ConstantInfo))
    (opt? : Option Name → Name → Array Level → Array Expr → Option (Expr × Array ConstantInfo) :=
      fun _ _ _ _ => none)
    (decline? : Name → Array Level → Array Expr → Option String := fun _ _ _ => none) :
    Except String BlockRewrite := do
  let mut st : RwState := { base := 0, opt?, decline? }
  let mut overlay : Array (Name × ConstantInfo) := #[]
  let mut declines : Array (Name × String) := #[]
  for (n, ci) in members do
    let before := st.declines.size
    let (ci', st') ← (rewriteConstM expansion? ci).run st
    st := st'
    for c in st.declines.extract before st.declines.size do
      unless declines.contains (n, c) do declines := declines.push (n, c)
    if ci' != ci then overlay := overlay.push (n, ci')
  return { overlay, sources := st.sources, needed := st.needed, declines, canon := st.canon }

end Ix.Compile.Pass

end
