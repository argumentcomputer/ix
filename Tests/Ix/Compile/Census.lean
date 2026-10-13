import Tests.Ix.Compile.Pass3

/-! The driver of the census runners (`l2a-syn`, `dev-census`, `opt-census`).

Each census compiles the `pass3` fixture units under Pass 3 and measures each
compile environment. The driver owns the unit list, the `*_ONLY` filter and the
refusal policy: a unit the compile refuses is a problem, so a run passes only
when it measured every unit it selected. -/

open Lean (Environment)

namespace Tests.Ix.Compile.Census

open Tests.Ix.Compile.Pass3 (CUnit unitOfFile compileUnit leanRejects auxCertFiles protoFiles
  passFiles pjPassFiles twinsUnit corpusUnit)

/-- A census unit: its name and the compile environment it produces. -/
abbrev CensusUnit := String × IO _root_.Ix.CompileM.CompileEnv

def compiled (u : IO CUnit) : IO _root_.Ix.CompileM.CompileEnv := do
  return (← compileUnit (← u)).cenv

/-- Every `pass3` fixture file Lean accepts, then, with `whole`, the twins and
the aux corpus. -/
def fixtureUnits (env : Environment) (whole : Bool) : Array CensusUnit := Id.run do
  let mut out : Array CensusUnit := #[]
  for p in auxCertFiles ++ protoFiles ++ passFiles ++ pjPassFiles do
    let stem := (System.FilePath.mk p).fileStem.getD p
    unless leanRejects.contains stem do out := out.push (stem, compiled (unitOfFile p))
  if whole then
    out := out.push ("twins", compiled (twinsUnit env))
    out := out.push ("corpus", compiled (corpusUnit env))
  return out

/-- The outcome of a census run. -/
structure Outcome (α : Type) where
  all : α
  selected : Nat
  measured : Nat
  refused : Array String

/-- Whether every selected unit was measured, and at least one. -/
def Outcome.complete {α} (o : Outcome α) : Bool :=
  o.refused.isEmpty && o.measured == o.selected && o.measured > 0

/-- Measure every unit selected by the filter variable `var`, printing each
unit's `summary` lines and the merged `TOTAL` lines under `[tag]`. -/
def run {α} (tag var : String) (units : Array CensusUnit) (measure : _root_.Ix.CompileM.CompileEnv → α)
    (summary : String → α → Array String) (merge : α → String → α → α) (init : α) :
    IO (Outcome α) := do
  let want ← Tests.Ix.Compile.Only.select tag var (units.map (·.1)).toList
  let mut all := init
  let mut selected := 0
  let mut measured := 0
  let mut refused : Array String := #[]
  for (name, mk) in units do
    unless want name do continue
    selected := selected + 1
    try
      let r := measure (← mk)
      measured := measured + 1
      for l in summary name r do IO.println s!"[{tag}] {l}"
      all := merge all name r
    catch e =>
      IO.println s!"[{tag}] FAIL {name}: compile refused ({(toString e).take 160})"
      refused := refused.push name
  for l in summary "TOTAL" all do IO.println s!"[{tag}] {l}"
  return { all, selected, measured, refused }

end Tests.Ix.Compile.Census
