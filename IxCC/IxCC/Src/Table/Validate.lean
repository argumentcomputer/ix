import IxCC.Src.Table.Check

/-! # Revalidating the unfolding table

The table checks on the recheck path (style V): given a
program and its table, re-run the entry check that justifies every entry.
`Table.build` (the producer) proposes, checks and prioritises entries; this
validator only asks that each entry present be justified, which is what the
stage-S reading of the table needs:

* `prim op`: `checkPrim` (the configured set, the pinned address, the type);
* `csimp g us thm`: `checkCsimp` gives exactly this entry, its target has a
  δ body or an entry, and the redirect chain is acyclic;
* `eqn thm body`: `checkEqn` gives exactly this body;
* `case r`: `checkCase` gives exactly this recursor;
* `recKind`: every entry is the derived kind (`deriveRecKind`);
* `lazy`, `inline`: `checkLazy`, `checkInline`;
* `opaqueByValue`: a safe opaque at a pinned allowlist address (D12);
* `known`: every constant it names is the pinned one (`Pinned.knownOk`).

It accepts every table `Table.build` produces (the load pipeline runs it after
the build) and is kernel-evaluable (D17): each column is walked as a list of
its `NatMap`'s entries by structural recursion. -/

namespace IxCC.Src.Table

/-- Check one `resolve` entry of constant `f`. -/
def validateResolve (cfg : Config) (p : Program) (f : CId) : Resolve → Except String Unit
  | .prim op => checkPrim p f op cfg.prims
  | .csimp g us thm => do
    let e ← checkCsimp p f g thm
    unless e == .csimp g us thm do throw "csimp: not the checked entry"
    unless (safeDefn? p g).isSome || (p.table.resolveOf g).isSome do
      throw "csimp: target not admissible"
    unless csimpAcyclic p.table.resolve p.size f do throw "csimp: redirect cycle"
  | .eqn thm body => do
    let e ← checkEqn p f thm
    unless e == .eqn thm body do throw "eqn: not the checked body"
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

/-- An `opaqueByValue` entry is a safe opaque at an allowlisted address. -/
def validateOpaque (p : Program) (c : CId) (_ : Unit) : Except String Unit :=
  match p.decl? c with
  | some (.defn _ .safe ..) =>
    if Pinned.opaqueByValuePins.contains (Pinned.addrNat (p.addr c)) then pure ()
    else throw "opaque-by-value: not an allowlisted address"
  | _ => throw "opaque-by-value: not a safe definition"

/-- Revalidate the whole table of `p` (and its pinned identities). -/
def validate (cfg : Config) (p : Program) : Except String Unit := do
  unless Pinned.knownOk p do throw "known: a pinned constant is misidentified"
  Resource.selected p p.table
  validateEach (validateResolve cfg p) p.table.resolve.toList
  validateEach (validateRecKind p) p.table.recKind.toList
  validateEach (checkLazy p) p.table.lazy.toList
  validateEach (fun c (_ : Unit) => checkInline p c cfg.inlineCap) p.table.inline.toList
  validateEach (validateOpaque p) p.table.opaqueByValue.toList

end IxCC.Src.Table
