/-
  Comprehensive validation of the aux_gen compile pipeline.

  Six phases:
    1. Compilation succeeds (every input constant gets an address)
    2. No ephemeral leaks (original constants don't pollute the Ixon env)
    3. Alpha-equivalence group canonicity (same-class names share addresses)
    4. Decompilation with debug info succeeds
    5. Aux congruence (aux_gen constants match originals)
    6. Decompilation without debug info succeeds

  Invoked via `lake test -- --ignored validate-aux`.
-/
import Ix.Common
import Ix.Meta
import Tests.Ix.Compile.Mutual

/-- Collect the transitive closure of constants referenced by a set of seed names. -/
partial def collectDeps (env : Lean.Environment) (seeds : List Lean.Name)
    : List (Lean.Name × Lean.ConstantInfo) := Id.run do
  let mut needed : Std.HashSet Lean.Name := {}
  let mut worklist := seeds
  while !worklist.isEmpty do
    match worklist with
    | [] => break
    | n :: rest =>
      worklist := rest
      if needed.contains n then continue
      needed := needed.insert n
      if let some ci := env.constants.find? n then
        let mut refs : Lean.NameSet := ci.type.getUsedConstantsAsSet
        match ci with
        | .defnInfo v =>
          for r in v.value.getUsedConstantsAsSet do refs := refs.insert r
        | .thmInfo v =>
          for r in v.value.getUsedConstantsAsSet do refs := refs.insert r
        | .opaqueInfo v =>
          for r in v.value.getUsedConstantsAsSet do refs := refs.insert r
        | .inductInfo v =>
          for ctorName in v.ctors do
            refs := refs.insert ctorName
            if let some ctorCi := env.constants.find? ctorName then
              for r in ctorCi.type.getUsedConstantsAsSet do refs := refs.insert r
          for mutName in v.all do
            refs := refs.insert mutName
        | .ctorInfo v =>
          refs := refs.insert v.induct
        | .recInfo v =>
          for mutName in v.all do
            refs := refs.insert mutName
          for rule in v.rules do
            for r in rule.rhs.getUsedConstantsAsSet do refs := refs.insert r
        | _ => pure ()
        for r in refs do
          if !needed.contains r then
            worklist := r :: worklist
  env.constants.toList.filter fun (n, _) => needed.contains n

@[extern "rs_compile_validate_aux"]
opaque compileValidateAux : @& List (Lean.Name × Lean.ConstantInfo) → USize

def runCompileValidateAux (env : Lean.Environment) : IO UInt32 := do
  IO.println "[validate-aux] finding seeds..."
  let prefixes := [
    `Tests.Ix.Compile.Mutual,
  ]
  let mut seeds := env.constants.toList.filterMap fun (n, _) =>
    if prefixes.any (·.isPrefixOf n) then some n else none
  -- Add prereqs that aux_gen references but test fixtures don't directly use.
  seeds := seeds ++ [`True]
  IO.println s!"[validate-aux] {seeds.length} seeds"

  IO.println "[validate-aux] collecting transitive deps..."
  let filtered := collectDeps env seeds
  IO.println s!"[validate-aux] {filtered.length} constants (from {seeds.length} seeds)"

  IO.println "[validate-aux] calling Rust FFI..."
  let failures := compileValidateAux filtered
  IO.println s!"[validate-aux] total failures: {failures}"
  return if failures == 0 then 0 else 1
