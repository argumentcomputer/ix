module

public import Ix.Resource.Validate
public import Tests.Ix.ResourceAddressed

public section

namespace Tests.ResourceValidate

open Ixon Ix.Resource Tests.ResourceAddressed

def run : IO Unit := do
  let (base, unit) := unitEnv
  let (env, id) := store base (identity unit)
  check "combined identity" (validate env {}) true
  check "literal type pin" (validate env { natType := some unit }) false
  let bad : Constant := {
    info := .defn ⟨.defn, .safe, 0, .sort 0, .var 0⟩
    sharing := #[], refs := #[], univs := #[.zero] }
  let (malformed, address) := store env bad
  check "ordinary component skips resource analysis" (Addressed.checkResources malformed {}) true
  check "ordinary component still needs typing" (validate malformed {}) false
  let forged := { LazyConstant.ofConstant bad with cache := some (identity unit) }
  check "typing also ignores materialized cache"
    (validate { malformed with consts := malformed.consts.insert address forged } {}) false
  let forged := { LazyConstant.ofConstant (identity unit) with cache := some bad }
  check "both validators consume the committed bytes"
    (validate { env with consts := env.consts.insert id forged } {}) true
  IO.println "Combined resources: typing, literal identities, and raw-byte validation passed"

end Tests.ResourceValidate

end
