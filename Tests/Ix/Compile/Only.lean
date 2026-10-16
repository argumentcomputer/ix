/-! The `*_ONLY` unit filters of the compiler test runners.

A filter that selects nothing must fail: otherwise a typo, or a unit the runner
skips, gives a passing run that checked nothing. A set filter is reported, so a
filtered run is labelled as one. -/

namespace Tests.Ix.Compile.Only

/-- The units selected by the environment variable `var`, a comma-separated list
of unit names among `known`; every unit when it is unset. Throws when it is set
and names no unit, or a name that is not one of `known`. `tag` labels the run. -/
def select (tag var : String) (known : List String) : IO (String → Bool) := do
  let some value ← IO.getEnv var | return fun _ => true
  let names := (value.splitOn ",").filter (!·.isEmpty)
  let unknown := names.filter (!known.contains ·)
  unless unknown.isEmpty do
    throw <| IO.userError s!"{var}={value} names {unknown}, which are not {tag} units"
  if names.isEmpty then
    throw <| IO.userError s!"{var}={value} selects no {tag} unit"
  IO.println s!"[{tag}] filtered run: {var}={value} selects {names.eraseDups.length} of {known.length} units"
  return (names.contains ·)

/-- As `select`, for a filter that selects every unit whose name contains its
value. Throws when it selects none of `known`. -/
def selectContaining (tag var : String) (known : List String) : IO (String → Bool) := do
  let some value ← IO.getEnv var | return fun _ => true
  let hit := fun (name : String) => (name.splitOn value).length > 1
  let selected := (known.filter hit).length
  if selected == 0 then
    throw <| IO.userError s!"{var}={value} selects no {tag} unit"
  IO.println s!"[{tag}] filtered run: {var}={value} selects {selected} of {known.length} units"
  return hit

end Tests.Ix.Compile.Only
