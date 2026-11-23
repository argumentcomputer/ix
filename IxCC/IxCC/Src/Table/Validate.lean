import IxCC.Src.Table.Word

/-! # Revalidating the unfolding table

The table checks on the recheck path (style V): given a
program and its table, re-run the entry check that justifies every entry.
`Table.build` (the producer) proposes, checks and prioritises entries; this
validator only asks that each entry present be justified, which is what the
stage-S reading of the table needs:

* `prim op`: `checkPrim` (the configured set, the pinned address, the type);
* `word w op thm`: `checkWord` (enabled, a primitive operation, the pinned address, the
  theorem's statement);
* `csimp g us thm`: `checkCsimp` gives exactly this entry, its target has a
  δ body or an entry, and the redirect chain is acyclic;
* `eqn thm body`: `checkEqn` gives exactly this body;
* `case r`: `checkCase` gives exactly this recursor;
* `recKind`: every entry is the derived kind (`deriveRecKind`);
* `lazy`: `checkLazy` (a pinned row, or a sparse casesOn at its binder
  count, without a `resolve` entry: `lazyResolveOk`); `inline`: `checkInline`;
* `opaqueByValue`: a safe opaque at a pinned allowlist address (D12);
* `known`: every constant it names is the pinned one (`Pinned.knownOk`).

It accepts every table `Table.build` produces (the load pipeline runs it after
the build) and is kernel-evaluable (D17): each column is walked as a list of
its `NatMap`'s entries by structural recursion. -/

namespace IxCC.Src.Table

/-- Check one `resolve` entry of constant `f`. -/
def validateResolve (cfg : Config) (p : Program) (f : CId) : Resolve → Except String Unit
  | .prim op => checkPrim p f op cfg.prims
  | .word w op thm => checkWord cfg p f w op thm
  | .csimp g us thm => do
    let e ← checkCsimp p f g thm
    unless e == .csimp g us thm do throw "csimp: not the checked entry"
    unless (safeDefn? p g).isSome || (p.table.resolveOf g).isSome do
      throw "csimp: target not admissible"
    unless csimpAcyclic p.table.resolve p.size f do throw "csimp: redirect cycle"
  | .eqn thm body => do
    let e ← checkEqn p f thm
    unless e == .eqn thm body do throw "eqn: not the checked body"
    unless eqnAcyclic p p.table.resolve f do throw "eqn: cyclic unconditional unfolding"
  | .case r => do
    let e ← checkCase p f
    unless e == .case r do throw "case: not the checked recursor"

/-- Check each entry of a column (structural on the list); an error names
the constant. -/
def validateEach {α : Type} (check : CId → α → Except String Unit) :
    List (CId × α) → Except String Unit
  | [] => pure ()
  | (c, x) :: rest =>
    match check c x with
    | .ok () => validateEach check rest
    | .error msg => .error s!"table entry of constant {c}: {msg}"

/-- A `recKind` entry is the derived kind. -/
def validateRecKind (p : Program) (r : CId) (k : RecKind) : Except String Unit :=
  if deriveRecKind p r == some k then pure () else throw "recKind: not the derived kind"

/-- An `opaqueByValue` entry is a safe opaque at an allowlisted address (D12 or DR4). -/
def validateOpaque (p : Program) (c : CId) (_ : Unit) : Except String Unit :=
  match p.decl? c with
  | some (.defn _ .safe ..) =>
    let n := Pinned.addrNat (p.addr c)
    if p.known.pins.opaqueByValue.contains n || Pinned.dr4OpaqueByValuePins.contains n then pure ()
    else throw "opaque-by-value: not an allowlisted address"
  | _ => throw "opaque-by-value: not a safe definition"

/-- A `lazy` row that is not a pinned row (so a sparse casesOn's, `checkLazy`)
stands only where the definition's value is what runs: no `resolve` entry for
its constant, since every kind replaces that value, and `checkSparseCases`
established "each by-name binder used at most once" for the value (structural
on the rows). `Table.build` never writes the pairing; pinned rows are not
affected. -/
def lazyResolveOk (p : Program) (resolve : NatMap Resolve) :
    List (CId × Nat) → Except String Unit
  | [] => pure ()
  | (f, a) :: rest =>
    if !pinnedLazy p f a && (resolve.get? f).isSome then
      .error s!"table entry of constant {f}: lazy: a sparse casesOn's row beside a resolve entry, \
        which replaces the value the row was checked on"
    else lazyResolveOk p resolve rest

/-- Every `.eqn` entry in `resolve` has no unconditional unfolding cycle through
`.eqn`/`.csimp` entries (`FE-3`). Structural on the entry list (`D17`). -/
def eqnTargetsAcyclic (p : Program) (resolve : NatMap Resolve) :
    List (CId × Resolve) → Except String Unit
  | [] => pure ()
  | (f, .eqn ..) :: rest =>
    if !eqnAcyclic p resolve f then
      .error s!"table entry of constant {f}: eqn: cyclic unconditional unfolding"
    else eqnTargetsAcyclic p resolve rest
  | _ :: rest => eqnTargetsAcyclic p resolve rest

/-- Every safe definition in `p` whose address is a pinned `lazy` row
(`Pinned.lazyPins`, including `ite`, `dite`, `Bool.and`, `Bool.or`,
`Decidable.byCases`) and passes `checkLazy` must be present in `lazy` at its
pinned arity (`FE-6`). Structural on the countdown (`D17`). -/
def pinnedLazyRequiredLoop (p : Program) (lazy : NatMap Nat) : Nat → Except String Unit
  | 0 => pure ()
  | k + 1 =>
    match p.decl? k with
    | some (.defn .defn .safe _ _ _) =>
      let a := Pinned.addrNat (p.addr k)
      match Pinned.lazyPins.find? (·.1 == a) with
      | some (_, arity) =>
        if lazy.get? k == some arity then
          pinnedLazyRequiredLoop p lazy k
        else
          match checkLazy p k arity with
          | .ok () =>
            .error s!"table entry of constant {k}: lazy: required pinned lazy row (arity {arity}) is missing"
          | .error _ =>
            pinnedLazyRequiredLoop p lazy k
      | none => pinnedLazyRequiredLoop p lazy k
    | _ => pinnedLazyRequiredLoop p lazy k

def pinnedLazyRequired (p : Program) (lazy : NatMap Nat) : Except String Unit :=
  pinnedLazyRequiredLoop p lazy p.size

/-- Revalidate the whole table of `p` (and its pinned identities). -/
def validate (cfg : Config) (p : Program) : Except String Unit := do
  unless Pinned.knownOk p do throw "known: a pinned constant is misidentified"
  validateEach (validateResolve cfg p) p.table.resolve.toList
  validateEach (validateRecKind p) p.table.recKind.toList
  validateEach (checkLazy p) p.table.lazy.toList
  lazyResolveOk p p.table.resolve p.table.lazy.toList
  pinnedLazyRequired p p.table.lazy
  validateEach (fun c (_ : Unit) => checkInline p c cfg.inlineCap) p.table.inline.toList
  validateEach (validateOpaque p) p.table.opaqueByValue.toList

end IxCC.Src.Table
