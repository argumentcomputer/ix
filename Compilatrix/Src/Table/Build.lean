import Compilatrix.Src.Table.Check
import Compilatrix.Src.Hints

/-! # Building the unfolding table

Collects proposals (pinned primitives, `lazy` and opaque-by-value rows;
sidecar `eqn`/`csimp`/`inline` hints; `case` candidates found by scanning
for recursor-headed definitions), checks each one, and resolves by priority
`prim > csimp > eqn > case > body` (design note 01 §4). Every refused explicit
proposal leaves a `hint` diagnostic. Recursor kinds are derived for every
recursor. -/

namespace Compilatrix.Src.Table

open Compilatrix.Ixon

structure Config where
  /-- The primitive operations with native lowering (§3.4); others resolve
  through their `eqn` entry or kernel body. -/
  prims : List PrimOp := PrimOp.all
  /-- Node cap for `inline` entries. -/
  inlineCap : Nat := 256
  deriving Inhabited

/-- What the build accepted, for tests and the census. -/
structure Stats where
  primAccepted : Array CId := #[]
  eqnAccepted : Array CId := #[]
  eqnRefused : Array (CId × String) := #[]
  csimpAccepted : Array CId := #[]
  caseAccepted : Array CId := #[]
  lazyAccepted : Array CId := #[]
  opaqueByValue : Array CId := #[]
  deriving Inhabited

private def resolveHint (p : Program) (a : Address) (what : String) :
    Except String CId :=
  match p.lookup a with
  | some c => .ok c
  | none => .error s!"{what} {((toString a).take 8).toString} is not in the closure"

def csimpProposal (p : Program) (prop : Proposal) : Except String (CId × Resolve) := do
  let f ← resolveHint p prop.subject "subject"
  let some ga := prop.target? | throw "csimp: missing target"
  let some ta := prop.theorem? | throw "csimp: missing theorem"
  let g ← resolveHint p ga "target"
  let thm ← resolveHint p ta "theorem"
  return (f, ← checkCsimp p f g thm)

def eqnProposal (p : Program) (prop : Proposal) : Except String (CId × Resolve) := do
  let f ← resolveHint p prop.subject "subject"
  let some ta := prop.theorem? | throw "eqn: missing theorem"
  let thm ← resolveHint p ta "theorem"
  return (f, ← checkEqn p f thm)

/-- Candidate `case` keys: safe definitions whose body, under its λs, is a
spine headed by a single-motive recursor. -/
def caseCandidates (p : Program) : Array CId := Id.run do
  let mut out := #[]
  for c in [0:p.consts.size] do
    if let some (.defn .defn .safe _ _ value) := p.decl? c then
      if let (.const r _, _) := value.lams.2.spine then
        if let some (.recr _ _ _ _ 1 _ _ _ _ _) := p.decl? r then out := out.push c
  return out

/-- Follow `csimp` redirects; `false` if a chain revisits a constant. -/
def csimpAcyclic (resolve : Array (Option Resolve)) (start : CId) : Bool := Id.run do
  let mut cur := start
  for _ in [0:resolve.size + 1] do
    match (resolve[cur]?).join with
    | some (.csimp g _ _) =>
      if g == start then return false
      cur := g
    | _ => return true
  return false

def build (cfg : Config) (p : Program) (hints : Array Proposal) :
    Table × Array Diag × Stats := Id.run do
  let n := p.size
  let mut resolve : Array (Option Resolve) := .replicate n none
  let mut diags : Array Diag := #[]
  let mut stats : Stats := {}
  let hintDiag := fun (prop : Proposal) (msg : String) =>
    ({ code := "hint", addr := some prop.subject, name := prop.name?, message := msg } : Diag)
  -- prim: every pinned primitive present in the closure.
  for c in [0:n] do
    if let some op := Pinned.primAt? (p.addr c) then
      match checkPrim p c op cfg.prims with
      | .ok () =>
        resolve := resolve.set! c (some (.prim op))
        stats := { stats with primAccepted := stats.primAccepted.push c }
      | .error msg =>
        if cfg.prims.contains op then
          diags := diags.push { code := "hint", addr := some (p.addr c), message := msg }
  -- csimp hints.
  for prop in hints do
    if prop.kind != .csimp then continue
    match csimpProposal p prop with
    | .ok (f, entry) =>
      if (resolve[f]?).join.isNone then
        resolve := resolve.set! f (some entry)
        stats := { stats with csimpAccepted := stats.csimpAccepted.push f }
    | .error msg => diags := diags.push (hintDiag prop msg)
  -- A csimp target must be a safe definition or carry its own entry; the
  -- redirect graph must be acyclic.
  for f in [0:n] do
    if let some (.csimp g _ _) := (resolve[f]?).join then
      let targetOk := (safeDefn? p g).isSome || ((resolve[g]?).join).isSome
      unless targetOk && csimpAcyclic resolve f do
        resolve := resolve.set! f none
        let d : Diag := { code := "hint", addr := some (p.addr f)
                          message := "csimp: target not admissible or redirect cycle" }
        diags := diags.push d
  -- eqn hints (checked even when a higher-priority entry already resolves f).
  for prop in hints do
    if prop.kind != .eqn then continue
    match eqnProposal p prop with
    | .ok (f, entry) =>
      stats := { stats with eqnAccepted := stats.eqnAccepted.push f }
      if (resolve[f]?).join.isNone then resolve := resolve.set! f (some entry)
    | .error msg =>
      if let some f := p.lookup prop.subject then
        stats := { stats with eqnRefused := stats.eqnRefused.push (f, msg) }
      diags := diags.push (hintDiag prop msg)
  -- case: scanned candidates and explicit hints.
  let explicitCases := hints.filterMap fun prop =>
    if prop.kind == .case then p.lookup prop.subject else none
  for c in caseCandidates p ++ explicitCases do
    if (resolve[c]?).join.isSome then continue
    match checkCase p c with
    | .ok entry =>
      resolve := resolve.set! c (some entry)
      stats := { stats with caseAccepted := stats.caseAccepted.push c }
    | .error msg =>
      if explicitCases.contains c then
        diags := diags.push { code := "hint", addr := some (p.addr c), message := msg }
  -- lazy: pinned rows and hints.
  let mut lazy : Array (Option Nat) := .replicate n none
  let pinnedLazy := Pinned.lazyRows.filterMap fun (name, hex, arity) =>
    (p.lookup (Pinned.addr hex)).map (·, arity, name)
  let hintedLazy := hints.toList.filterMap fun prop =>
    if prop.kind == .lazy then
      match p.lookup prop.subject, prop.arity? with
      | some c, some a => some (c, a, prop.name?.getD "")
      | _, _ => none
    else none
  for (c, arity, name) in pinnedLazy ++ hintedLazy do
    if (lazy[c]?).join.isSome then continue
    match checkLazy p c arity with
    | .ok () =>
      lazy := lazy.set! c (some arity)
      stats := { stats with lazyAccepted := stats.lazyAccepted.push c }
    | .error msg =>
      let d : Diag := { code := "hint", addr := some (p.addr c), name := some name
                        message := msg }
      diags := diags.push d
  -- opaque-by-value allowlist.
  let mut opaqueByValue : Array Bool := .replicate n false
  for (_, hex) in Pinned.opaqueByValueRows do
    if let some c := p.lookup (Pinned.addr hex) then
      if let some (.defn _ .safe _ _ _) := p.decl? c then
        opaqueByValue := opaqueByValue.set! c true
        stats := { stats with opaqueByValue := stats.opaqueByValue.push c }
  -- inline hints.
  let mut inline : Array Bool := .replicate n false
  for prop in hints do
    if prop.kind != .inline then continue
    match p.lookup prop.subject with
    | some c =>
      match checkInline p c cfg.inlineCap with
      | .ok () => inline := inline.set! c true
      | .error msg => diags := diags.push (hintDiag prop msg)
    | none => diags := diags.push (hintDiag prop "inline: subject is not in the closure")
  -- Derived recursor kinds.
  let recKind := (Array.range n).map (deriveRecKind p)
  return ({ resolve, recKind, lazy, inline, opaqueByValue }, diags, stats)

end Compilatrix.Src.Table
