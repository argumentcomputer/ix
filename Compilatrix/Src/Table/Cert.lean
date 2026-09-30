import Compilatrix.Src.Table.Validate

/-! # The unfolding table as certificate data

The table part of the compiler's certificate (design note 00 "Produce and
recheck", `Cert.table`; 01 §1.2): the entries `Table.build` accepted, in the
form of the proposals they came from, without anything a check re-derives.
An `eqn` entry names its theorem but not its body, a `csimp` entry its
target and theorem but not the target's levels, a `case` entry nothing but
its key, and a recursor kind only the recursor.

`Table.ofCert` rebuilds the table from such a certificate on the recheck path
(style V): every entry is produced by the §4.1 check that justifies it
(`checkPrim`, `checkCsimp`, `checkEqn`, `checkCase`, `deriveRecKind`,
`checkLazy`, `checkInline`, the opaque-by-value allowlist), and the global
conditions of `Table.validate` are checked on the result (pinned identities,
`csimp` targets admissible and redirects acyclic). So it accepts exactly the
tables `Table.validate` accepts, up to the entries a check derives, and
never evaluates a check twice. A missing entry only degrades to the kernel
body; a wrong one is rejected with the constant it concerns.

Kernel style (D17): lists, `NatMap`s and structural recursion. -/

namespace Compilatrix.Src.Table

/-- A `resolve` entry as the certificate states it. -/
inductive Entry where
  | prim (op : PrimOp)
  | csimp (g thm : CId)
  | eqn (thm : CId)
  | case
  deriving BEq, DecidableEq, Repr, Inhabited

/-- The table as certificate data, column by column. -/
structure TableCert where
  resolve : List (CId × Entry) := []
  /-- Recursors whose kind is derived. -/
  recKind : List CId := []
  lazy : List (CId × Nat) := []
  inline : List CId := []
  opaqueByValue : List CId := []
  deriving BEq, DecidableEq, Repr, Inhabited

/-- The certificate form of a `resolve` entry. -/
def Entry.ofResolve : Resolve → Entry
  | .prim op => .prim op
  | .csimp g _ thm => .csimp g thm
  | .eqn thm _ => .eqn thm
  | .case _ => .case

/-- The certificate of a table (the producer's side). -/
def TableCert.ofTable (t : Table) : TableCert :=
  { resolve := t.resolve.toList.map fun (c, r) => (c, Entry.ofResolve r)
    recKind := t.recKind.toList.map (·.1)
    lazy := t.lazy.toList
    inline := t.inline.toList.map (·.1)
    opaqueByValue := t.opaqueByValue.toList.map (·.1) }

/-- The entry a certificate line names, produced by its check. -/
def entryOf (cfg : Config) (p : Program) (f : CId) : Entry → Except String Resolve
  | .prim op => do checkPrim p f op cfg.prims; pure (.prim op)
  | .csimp g thm => checkCsimp p f g thm
  | .eqn thm => checkEqn p f thm
  | .case => checkCase p f

/-- The `resolve` column (structural on the certificate's list). -/
def resolveOfCert (cfg : Config) (p : Program) :
    List (CId × Entry) → NatMap Resolve → Except String (NatMap Resolve)
  | [], m => pure m
  | (f, e) :: rest, m =>
    match entryOf cfg p f e with
    | .ok r => resolveOfCert cfg p rest (m.insert f r)
    | .error msg => .error s!"table entry of constant {f}: {msg}"

/-- The `recKind` column: each listed recursor's derived kind. -/
def recKindOfCert (p : Program) : List CId → NatMap RecKind → Except String (NatMap RecKind)
  | [], m => pure m
  | r :: rest, m =>
    match deriveRecKind p r with
    | some k => recKindOfCert p rest (m.insert r k)
    | none => .error s!"table entry of constant {r}: recKind: not a recursor"

/-- Check each listed constant and insert it (structural on the list). -/
def columnOfCert {α β : Type} (check : CId → α → Except String Unit) (val : α → β) :
    List (CId × α) → NatMap β → Except String (NatMap β)
  | [], m => pure m
  | (c, x) :: rest, m =>
    match check c x with
    | .ok () => columnOfCert check val rest (m.insert c (val x))
    | .error msg => .error s!"table entry of constant {c}: {msg}"

/-- Every `csimp` target of the rebuilt column is admissible and its
redirect chain acyclic (as `Table.validate` asks). -/
def csimpTargetsOk (p : Program) (resolve : NatMap Resolve) :
    List (CId × Resolve) → Except String Unit
  | [] => pure ()
  | (f, .csimp g _ _) :: rest =>
    if !((safeDefn? p g).isSome || (resolve.get? g).isSome) then
      .error s!"table entry of constant {f}: csimp: target not admissible"
    else if !csimpAcyclic resolve p.size f then
      .error s!"table entry of constant {f}: csimp: redirect cycle"
    else csimpTargetsOk p resolve rest
  | _ :: rest => csimpTargetsOk p resolve rest

/-- Rebuild the checked table of `p` from its certificate (the recheck
path, style V). -/
def ofCert (cfg : Config) (p : Program) (c : TableCert) : Except String Table := do
  unless Pinned.knownOk p do throw "known: a pinned constant is misidentified"
  let resolve ← resolveOfCert cfg p c.resolve .leaf
  csimpTargetsOk p resolve resolve.toList
  let recKind ← recKindOfCert p c.recKind .leaf
  let lazy ← columnOfCert (checkLazy p) id c.lazy .leaf
  let inline ← columnOfCert (fun f (_ : Unit) => checkInline p f cfg.inlineCap) id
    (c.inline.map (·, ())) .leaf
  let opaqueByValue ← columnOfCert (validateOpaque p) id (c.opaqueByValue.map (·, ())) .leaf
  pure { resolve, recKind, lazy, inline, opaqueByValue }

end Compilatrix.Src.Table
