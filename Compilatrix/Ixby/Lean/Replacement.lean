import Lean

/-! Optional closed source replacements for the typed frontend. Each request
names a kernel theorem of exactly `source = target`, between closed safe
definitions with the same monomorphic calling arity. This checks a source
equality, not Lean erasure or LCNF-to-Ixby refinement. -/

namespace Compilatrix.Ixby.LeanFrontend

open Lean Lean.Compiler

structure SourceReplacement where
  source : Name
  target : Name
  equality : Name
  deriving BEq, Repr

/-- Admit only an actual closed theorem, and retain the exact declarations
from its equality type. No caller-supplied name pair is trusted. -/
def checkSourceReplacement (equality : Name) : CoreM (Except String SourceReplacement) := do
  let env ← getEnv
  let some (.thmInfo info) := env.find? equality |
    return .error s!"source replacement is not a theorem: {equality}"
  unless info.levelParams.isEmpty do
    return .error s!"source replacement is not closed: {equality}"
  let some (_, .const source [], .const target []) := info.type.eq? |
    return .error s!"source replacement must prove a constant equality: {equality}"
  unless source != target do
    return .error s!"source replacement does not change its source: {equality}"
  for name in #[source, target] do
    let some (.defnInfo definition) := env.find? name |
      return .error s!"source replacement requires definitions: {name}"
    unless definition.safety == .safe && definition.levelParams.isEmpty do
      return .error s!"source replacement requires closed safe definitions: {name}"
  for axiomName in ← collectAxioms equality do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      return .error s!"source replacement has an unsupported axiom: {axiomName}"
  let some original ← LCNF.getMonoDecl? source |
    return .error s!"source replacement has no original LCNF: {source}"
  let some replacement ← LCNF.getMonoDecl? target |
    return .error s!"source replacement has no target LCNF: {target}"
  unless original.params.size == replacement.params.size do
    return .error s!"source replacement changes monomorphic arity: {equality}"
  match original.value, replacement.value with
  | .code .., .code .. => return .ok ⟨source, target, equality⟩
  | _, _ => return .error s!"source replacement cannot replace externs: {equality}"

/-- Selection is bounded and simultaneous: no chains, cycles, duplicate
sources, or overrides of installed runtime bodies. Any rejection discards the
entire optional request; the caller keeps the original compiler behavior. -/
def selectSourceReplacements (equalities : Array Name) (protectedNames : Array Name) :
    CoreM (Except String (Array SourceReplacement)) := do
  if equalities.size > 32 then return .error "source replacement request limit"
  let mut selected := #[]
  for equality in equalities do
    let .ok replacement ← checkSourceReplacement equality | return .error s!"invalid source replacement: {equality}"
    if protectedNames.contains replacement.source || protectedNames.contains replacement.target then
      return .error s!"source replacement touches an installed runtime body: {equality}"
    for previous in selected do
      if previous.source == replacement.source || previous.target == replacement.source ||
          previous.source == replacement.target then
        return .error s!"source replacement overlaps another replacement: {equality}"
    selected := selected.push replacement
  return .ok selected

end Compilatrix.Ixby.LeanFrontend
