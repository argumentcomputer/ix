module

public import Ix.Resource.Validate
public import Tests.Ix.ResourceAddressed

public section

namespace Tests.ResourceValidate

open Ixon Ix.Resource Tests.ResourceAddressed

/-- A definition record under another safety. -/
def withSafety (c : Constant) (safety : Ix.DefinitionSafety) : Constant :=
  match c.info with
  | .defn d => { c with info := .defn { d with safety } }
  | _ => c

/-- `unitEnv` with the inductive, its constructor and its recursor unsafe. -/
def unsafeUnitEnv : Ixon.Env × Address := Id.run do
  let block : Constant := { unitBlock with
    info := .muts #[.indc ⟨true, 0, 0, 0, .sort 0, #[⟨true, 0, 0, 0, 0, .recur 0 #[]⟩]⟩] }
  let (env, block) := store {} block
  let (env, type) := store env (Addressed.wrapper (.iPrj ⟨0, block⟩))
  let (env, ctor) := store env (Addressed.constructorWrapper block 0 0)
  let r := unitRec type ctor
  let r := match r.info with
    | .recr rr => { r with info := .recr { rr with isUnsafe := true } }
    | _ => r
  let (env, _) := store env r
  return (env, type)

/-- The validator declines, with `needle` in its message. -/
def declines (label : String) (result : Except String α) (needle : String) : IO Unit := do
  match result with
  | .ok _ => throw <| IO.userError s!"resource validator {label}: expected a decline, got an accept"
  | .error e =>
    unless (e.splitOn needle).length > 1 do
      throw <| IO.userError s!"resource validator {label}: expected '{needle}' in: {e}"

/-- The typing half is IxC's tiered entry: `partial` and `unsafe`
definitions are typed by the tier, ill-typed ones decline on either side,
and an unsafe inductive declines (Q2) until step 10d. -/
def runTier : IO Unit := do
  let (base, unit) := unitEnv
  let plain := identity unit {} {}
  check "safe definition" (validate (store base plain).1 {}) true
  check "partial definition typed by the tier" (validate (store base (withSafety plain .part)).1 {}) true
  check "unsafe definition typed by the tier" (validate (store base (withSafety plain .unsaf)).1 {}) true
  -- `Sort 0 : unit`, ill-typed
  let illTyped : Constant := {
    info := .defn ⟨.defn, .safe, 0, .ref 0 #[], .sort 0⟩
    sharing := #[], refs := #[unit], univs := #[.zero] }
  declines "ill-typed definition (logical check)" (validate (store base illTyped).1 {}) "erased typing failed"
  declines "ill-typed partial definition (tier)" (validate (store base (withSafety illTyped .part)).1 {})
    "tier at"
  let (unsafeEnv, _) := unsafeUnitEnv
  declines "unsafe inductive (Q2, until 10d)" (validate unsafeEnv {}) "erased typing failed"
  IO.println "Combined resources: the typing tier (partial and unsafe definitions; unsafe inductives \
    decline until 10d) passed"

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
  runTier

end Tests.ResourceValidate

end
