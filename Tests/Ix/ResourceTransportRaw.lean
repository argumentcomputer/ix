import Ix.Resource.Validate
import Tests.Ix.ResourceAddressed

namespace Tests.ResourceTransportRaw
open Ixon Ix.Resource Tests.ResourceAddressed

def familyEnv (block : Constant) : Ixon.Env := Id.run do
  let (env, address) := store {} block
  let (env, type) := store env (Addressed.wrapper (.iPrj ⟨0, address⟩))
  let (env, _) := store env (Addressed.constructorWrapper address 0 0)
  return (store env (identity type)).1

def run : IO Unit := do
  let (base, unit) := unitEnv
  let (env, id) := store base (identity unit)
  check "combined identity" (validate env {}) true
  check "literal type pin" (validate env { natType := some unit }) false
  let bad : Constant := {
    info := .defn ⟨.defn, .safe, 0, .sort 0, .var 0⟩
    sharing := #[], refs := #[], univs := #[.zero] }
  let (malformed, address) := store env bad
  check "resource-only diagnostic boundary" (Addressed.checkResources malformed {}) true
  check "combined ordinary typing" (validate malformed {}) false
  let forged := { LazyConstant.ofConstant bad with cache := some (identity unit) }
  check "forged cache cannot hide malformed bytes"
    (validate { malformed with consts := malformed.consts.insert address forged } {}) false
  let forged := { LazyConstant.ofConstant (identity unit) with cache := some bad }
  check "valid committed bytes ignore malformed cache"
    (validate { env with consts := env.consts.insert id forged } {}) true
  let .muts members := unitBlock.info | throw (IO.userError "unit block")
  let .indc ind := members[0]! | throw (IO.userError "unit inductive")
  for (name, changed) in #[
      ("forged index count", { ind with indices := 1 }),
      ("forged constructor result", { ind with ctors := ind.ctors.set! 0 { ind.ctors[0]! with typ := .sort 0 } }),
      ("unsafe selected primitive", { ind with isUnsafe := true }),
      ("consistently unsafe selected family", { ind with isUnsafe := true, ctors := ind.ctors.set! 0 { ind.ctors[0]! with isUnsafe := true } }),
      ("unsafe selected constructor", { ind with ctors := ind.ctors.set! 0 { ind.ctors[0]! with isUnsafe := true } })] do
    let raw := familyEnv { unitBlock with info := .muts #[.indc changed] }
    let result := validate raw {}
    check name result false
    match result with
    | .error message => IO.println s!"PASS {name}: {message}"
    | .ok _ => throw (IO.userError "unexpected acceptance")
  IO.println "Raw combined boundary: eleven controls passed"
end Tests.ResourceTransportRaw
