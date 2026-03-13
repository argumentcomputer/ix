/-
  Negative tests: verify the kernel rejects malformed declarations.
-/
import Ix.Kernel
import Tests.Ix.Kernel.Helpers
import LSpec

open LSpec

namespace Tests.Ix.Kernel.Negative

/-- Verify Kernel rejects malformed declarations. -/
def negativeTests : TestSeq :=
  .individualIO "kernel negative tests" (do
    let testAddr := Address.blake3 (ByteArray.mk #[1, 0, 42])
    let badAddr := Address.blake3 (ByteArray.mk #[99, 0, 42])
    let prims := Ix.Kernel.buildPrimitives .anon
    let mut passed := 0
    let mut failures : Array String := #[]

    -- Test 1: Theorem not in Prop
    do
      let cv : Ix.Kernel.ConstantVal .anon :=
        { numLevels := 0, type := .sort (.succ .zero), name := (), levelParams := () }
      let ci : Ix.Kernel.ConstantInfo .anon := .thmInfo { toConstantVal := cv, value := .sort .zero, all := #[] }
      let env := (default : Ix.Kernel.Env .anon).insert testAddr ci
      match Ix.Kernel.typecheckConst env prims testAddr with
      | .error _ => passed := passed + 1
      | .ok () => failures := failures.push "theorem-not-prop: expected error"

    -- Test 2: Type mismatch
    do
      let cv : Ix.Kernel.ConstantVal .anon :=
        { numLevels := 0, type := .sort .zero, name := (), levelParams := () }
      let ci : Ix.Kernel.ConstantInfo .anon := .defnInfo { toConstantVal := cv, value := .sort (.succ .zero), hints := .opaque, safety := .safe, all := #[] }
      let env := (default : Ix.Kernel.Env .anon).insert testAddr ci
      match Ix.Kernel.typecheckConst env prims testAddr with
      | .error _ => passed := passed + 1
      | .ok () => failures := failures.push "type-mismatch: expected error"

    -- Test 3: Unknown constant reference
    do
      let cv : Ix.Kernel.ConstantVal .anon :=
        { numLevels := 0, type := .const badAddr #[], name := (), levelParams := () }
      let ci : Ix.Kernel.ConstantInfo .anon := .defnInfo { toConstantVal := cv, value := .sort .zero, hints := .opaque, safety := .safe, all := #[] }
      let env := (default : Ix.Kernel.Env .anon).insert testAddr ci
      match Ix.Kernel.typecheckConst env prims testAddr with
      | .error _ => passed := passed + 1
      | .ok () => failures := failures.push "unknown-const: expected error"

    -- Test 4: Variable out of range
    do
      let cv : Ix.Kernel.ConstantVal .anon :=
        { numLevels := 0, type := .bvar 0 (), name := (), levelParams := () }
      let ci : Ix.Kernel.ConstantInfo .anon := .defnInfo { toConstantVal := cv, value := .sort .zero, hints := .opaque, safety := .safe, all := #[] }
      let env := (default : Ix.Kernel.Env .anon).insert testAddr ci
      match Ix.Kernel.typecheckConst env prims testAddr with
      | .error _ => passed := passed + 1
      | .ok () => failures := failures.push "var-out-of-range: expected error"

    -- Test 5: Application of non-function
    do
      let cv : Ix.Kernel.ConstantVal .anon :=
        { numLevels := 0, type := .sort (.succ (.succ .zero)), name := (), levelParams := () }
      let ci : Ix.Kernel.ConstantInfo .anon := .defnInfo
        { toConstantVal := cv, value := .app (.sort .zero) (.sort .zero), hints := .opaque, safety := .safe, all := #[] }
      let env := (default : Ix.Kernel.Env .anon).insert testAddr ci
      match Ix.Kernel.typecheckConst env prims testAddr with
      | .error _ => passed := passed + 1
      | .ok () => failures := failures.push "app-non-function: expected error"

    -- Test 6: Let value type doesn't match annotation
    do
      let cv : Ix.Kernel.ConstantVal .anon :=
        { numLevels := 0, type := .sort (.succ (.succ (.succ .zero))), name := (), levelParams := () }
      let letVal : Ix.Kernel.Expr .anon := .letE (.sort .zero) (.sort (.succ .zero)) (.bvar 0 ()) ()
      let ci : Ix.Kernel.ConstantInfo .anon := .defnInfo
        { toConstantVal := cv, value := letVal, hints := .opaque, safety := .safe, all := #[] }
      let env := (default : Ix.Kernel.Env .anon).insert testAddr ci
      match Ix.Kernel.typecheckConst env prims testAddr with
      | .error _ => passed := passed + 1
      | .ok () => failures := failures.push "let-type-mismatch: expected error"

    -- Test 7: Lambda applied to wrong type
    do
      let cv : Ix.Kernel.ConstantVal .anon :=
        { numLevels := 0, type := .sort (.succ (.succ .zero)), name := (), levelParams := () }
      let lam : Ix.Kernel.Expr .anon := .lam (.sort .zero) (.bvar 0 ()) () ()
      let ci : Ix.Kernel.ConstantInfo .anon := .defnInfo
        { toConstantVal := cv, value := .app lam (.sort (.succ .zero)), hints := .opaque, safety := .safe, all := #[] }
      let env := (default : Ix.Kernel.Env .anon).insert testAddr ci
      match Ix.Kernel.typecheckConst env prims testAddr with
      | .error _ => passed := passed + 1
      | .ok () => failures := failures.push "app-wrong-type: expected error"

    -- Test 8: Axiom with non-sort type
    do
      let cv : Ix.Kernel.ConstantVal .anon :=
        { numLevels := 0, type := .app (.sort .zero) (.sort .zero), name := (), levelParams := () }
      let ci : Ix.Kernel.ConstantInfo .anon := .axiomInfo { toConstantVal := cv, isUnsafe := false }
      let env := (default : Ix.Kernel.Env .anon).insert testAddr ci
      match Ix.Kernel.typecheckConst env prims testAddr with
      | .error _ => passed := passed + 1
      | .ok () => failures := failures.push "axiom-non-sort-type: expected error"

    IO.println s!"[kernel-negative] {passed}/8 passed"
    if failures.isEmpty then
      return (true, none)
    else
      for f in failures do IO.println s!"  [fail] {f}"
      return (false, some s!"{failures.size} failure(s)")
  ) .done

def suite : List TestSeq := [negativeTests]

end Tests.Ix.Kernel.Negative
