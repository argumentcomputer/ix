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

/-- An unsafe block of one type with one constructor of type `ctorType` and
`fields` fields, its type's sort `univs[0]`, with its projection and
constructor records and an unsafe recursor of `unitRec`'s shape. -/
def unsafeBlockEnv (ctorType : Expr := .recur 0 #[]) (fields : UInt64 := 0)
    (univs : Array Univ := #[.zero]) : Ixon.Env × Address := Id.run do
  let block : Constant := { unitBlock with
    info := .muts #[.indc ⟨true, 0, 0, 0, .sort 0, #[⟨true, 0, 0, 0, fields, ctorType⟩]⟩], univs }
  let (env, block) := store {} block
  let (env, type) := store env (Addressed.wrapper (.iPrj ⟨0, block⟩))
  let (env, ctor) := store env (Addressed.constructorWrapper block 0 0)
  let r := unitRec type ctor
  let r := match r.info with
    | .recr rr => { r with info := .recr { rr with isUnsafe := true } }
    | _ => r
  let (env, _) := store env r
  return (env, type)

/-- `unitEnv` with the inductive, its constructor and its recursor unsafe. -/
def unsafeUnitEnv : Ixon.Env × Address := unsafeBlockEnv

/-- The validator declines, with `needle` in its message. -/
def declines (label : String) (result : Except String α) (needle : String) : IO Unit := do
  match result with
  | .ok _ => throw <| IO.userError s!"resource validator {label}: expected a decline, got an accept"
  | .error e =>
    unless (e.splitOn needle).length > 1 do
      throw <| IO.userError s!"resource validator {label}: expected '{needle}' in: {e}"

/-- Assert the actual typing result independently of resource validation. -/
def expectTyping (label : String) (env : Ixon.Env) (accept : Bool) : IO Unit := do
  let result := typeCheck env
  unless result.toOption.isSome == accept do
    let why := match result with | .error e => e | .ok _ => "accepted"
    throw <| IO.userError s!"resource validator {label}: expected typing {accept}, got {why}"

/-- The typing half: `partial` and `unsafe` definitions typed by the batch
tier, ill-typed ones declined; unsafe inductives and
assumption axioms typed uncertified (step 10d), and ill-typed ones declined;
every actual typing result is checked explicitly. -/
def runTier : IO Unit := do
  let (base, unit) := unitEnv
  let ctor := Addressed.commit (Addressed.constructorWrapper (Addressed.commit unitBlock) 0 0)
  let plain := identity unit {} {}
  let mut cases : Array (String × Ixon.Env × Bool) := #[]
  cases := cases.push ("safe definition", (store base plain).1, true)
  cases := cases.push ("partial definition typed by the tier", (store base (withSafety plain .part)).1, true)
  cases := cases.push ("unsafe definition typed by the tier", (store base (withSafety plain .unsaf)).1, true)
  -- δ on tier definitions (transparent, as Lean): `alias : Prop := U`, then
  -- `good : alias := U.mk` types only by unfolding `alias`; `bad : alias :=
  -- fun x : U => x` is ill-typed even after unfolding
  let aliasC : Constant := {
    info := .defn ⟨.defn, .unsaf, 0, .sort 0, .ref 0 #[]⟩
    sharing := #[], refs := #[unit], univs := #[.zero] }
  let (aliasEnv, alias) := store base aliasC
  let good : Constant := {
    info := .defn ⟨.defn, .unsaf, 0, .ref 0 #[], .ref 1 #[]⟩
    sharing := #[], refs := #[alias, ctor], univs := #[] }
  cases := cases.push ("unsafe definition typed by unfolding another (δ)", (store aliasEnv good).1, true)
  let bad : Constant := {
    info := .defn ⟨.defn, .unsaf, 0, .ref 0 #[], .leanLam (.ref 1 #[]) (.var 0)⟩
    sharing := #[], refs := #[alias, unit], univs := #[] }
  cases := cases.push ("unsafe definition ill-typed even after unfolding (δ)", (store aliasEnv bad).1, false)
  -- `Sort 0 : unit`, ill-typed
  let illTyped : Constant := {
    info := .defn ⟨.defn, .safe, 0, .ref 0 #[], .sort 0⟩
    sharing := #[], refs := #[unit], univs := #[.zero] }
  cases := cases.push ("ill-typed definition (logical check)", (store base illTyped).1, false)
  cases := cases.push ("ill-typed partial definition (tier)", (store base (withSafety illTyped .part)).1, false)
  -- unsafe inductives (uncertified, `Tier.indC`)
  cases := cases.push ("unsafe inductive", unsafeUnitEnv.1, true)
  let (unsafeEnv, unsafeType) := unsafeUnitEnv
  let useUnsafe : Constant := {
    info := .defn ⟨.defn, .unsaf, 0, .leanAll (.ref 0 #[]) (.ref 0 #[]), .leanLam (.ref 0 #[]) (.var 0)⟩
    sharing := #[], refs := #[unsafeType], univs := #[] }
  cases := cases.push ("unsafe definition over an unsafe inductive", (store unsafeEnv useUnsafe).1, true)
  cases := cases.push ("safe definition over an unsafe inductive",
    (store unsafeEnv (withSafety useUnsafe .safe)).1, false)
  cases := cases.push ("unsafe constructor whose result is not its type",
    (unsafeBlockEnv (ctorType := .sort 0)).1, false)
  -- `T : Type` with `mk : Type → T`: the field's universe is too large
  cases := cases.push ("unsafe constructor with a field universe too large",
    (unsafeBlockEnv (ctorType := .leanAll (.sort 0) (.recur 0 #[])) (fields := 1)
      (univs := #[.succ .zero])).1, false)
  -- assumption axioms (uncertified: header, then the fold's steps)
  let axiomOf (typ : Expr) (refs : Array Address) : Constant :=
    { info := .axio ⟨false, 0, typ⟩, sharing := #[], refs, univs := #[] }
  let (axEnv, ax) := store base (axiomOf (.ref 0 #[]) #[unit])
  cases := cases.push ("assumption axiom", axEnv, true)
  let useAx : Constant := {
    info := .defn ⟨.defn, .safe, 0, .ref 0 #[], .ref 1 #[]⟩
    sharing := #[], refs := #[unit, ax], univs := #[] }
  cases := cases.push ("definition over an assumption axiom", (store axEnv useAx).1, true)
  cases := cases.push ("assumption axiom whose header is not a type",
    (store base (axiomOf (.ref 0 #[]) #[ctor])).1, false)
  let (fEnv, f) := store base (axiomOf (.leanAll (.ref 0 #[]) (.ref 0 #[])) #[unit])
  let misuse : Constant := {
    info := .defn ⟨.defn, .safe, 0, .ref 0 #[], .ref 1 #[]⟩
    sharing := #[], refs := #[unit, f], univs := #[] }
  cases := cases.push ("definition that misuses an assumption axiom", (store fEnv misuse).1, false)
  unless cases.size == 16 do throw (IO.userError "resource typing corpus lost a case")
  for (label, env, accept) in cases do
    check label (validate env {}) accept
    expectTyping label env accept
  IO.println s!"Combined resources: the typing half (the batch tier; unsafe inductives and assumption \
    axioms uncertified) on {cases.size} explicit outcomes passed"

def run : IO Unit := do
  let (base, unit) := unitEnv
  let (env, id) := store base (identity unit)
  check "combined identity" (validate env {}) true
  expectTyping "combined identity" env true
  -- the handoff's and the VM tests' escaping identity: typed, resource-invalid
  expectTyping "escaping identity" (store base (identity unit linearLocal .shared)).1 true
  check "literal type pin" (validate env { natType := some unit }) false
  let bad : Constant := {
    info := .defn ⟨.defn, .safe, 0, .sort 0, .var 0⟩
    sharing := #[], refs := #[], univs := #[.zero] }
  let (malformed, address) := store env bad
  check "ordinary component skips resource analysis" (Addressed.checkResources malformed {}) true
  check "ordinary component still needs typing" (validate malformed {}) false
  expectTyping "ordinary component still needs typing" malformed false
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
