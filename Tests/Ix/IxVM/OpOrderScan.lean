import Tests.Ix.IxVM.Harness
import IxVM
import Aiur.Artifact

/-! # Operation order in the well-founded block

Inside the well-founded block every group is validated at one limit, and the operation-order
scan (`KernelRoles::op_order_scan`) stands in for the per-reference order check: from an
operation's record and its certificates' references it follows the used references and refuses
an operation that is neither in force nor among the needs of the group being validated. It
stops at a role-bound record in force that is no operation, except at an anchor no validation
walks, where it goes on into the record's references.

Binding claims over the default table, each with one certificate of a well-founded operation
given one more, unused, reference. Must be accepted: the unchanged default table; a record bound
to `True` with no further reference; a reference to an operation in force; a reference to an
operation among the group's needs; a reference to a later role that is no operation. Must be
refused at the scan: a reference to a later operation, directly, through an unbound record,
through a record bound to `True`, and through a record bound to `Lean.reduceBool`.

With `IX_OP_ORDER_DEFAULT_ONLY` set, only the unchanged default table's claim runs.
-/

namespace Tests.Ix.IxVM.OpOrderScan
open IxVM.ClaimHarness

private def scanMessage := "an operation reaches an operation its group does not need"

private def put (env : Ixon.Env) (c : Ixon.Constant) : Ixon.Env × Address :=
  let a := Address.blake3 (Ixon.serConstant c)
  let env := env.storeConst a c
  let env := match c.info with
    | .defn _ | .dPrj _ => { env with anonHints := env.anonHints.insert a .opaque }
    | _ => env
  (env, a)

private def base : Except String Ixon.Env := do
  withRoleTable {} (← Ix.Kernel.Reader.defaultTableBytes)

private def bindingCase (label : String) (env : Ixon.Env) (accept : Bool)
    (reject : Option String := none) : Except String Case := do
  let some binding := env.roleBinding | throw "missing role binding"
  Case.ofClaim label env (.binding (← Ix.SpecDigest.specDigest) binding.address) {} accept reject

/-- `def X : Prop := ∀ p : Prop, p → p`, with an unused sharing reference to `target` if given. -/
private def propDef (target : Option Address) : Ixon.Constant :=
  ⟨.defn ⟨.defn, .safe, {}, 0, .sort 0, .all (.sort 0) (.all (.var 0) (.var 1))⟩,
    (match target with | some _ => #[.ref 0 #[]] | none => #[]),
    (match target with | some t => #[t] | none => #[]), #[.zero, .succ .zero], #[]⟩

/-- `theorem XI : X := fun p h => h`. -/
private def propProof (x : Address) : Ixon.Constant :=
  ⟨.defn ⟨.thm, .safe, {}, 0, .ref 0 #[], .lam (.sort 0) (.lam (.var 0) (.var 0))⟩,
    #[], #[x], #[.zero, .succ .zero], #[]⟩

/-- `def Y : Bool → Bool := fun b => b`, with an unused sharing reference to `target`. -/
private def boolFun (bool target : Address) : Ixon.Constant :=
  ⟨.defn ⟨.defn, .safe, {}, 0, .all (.ref 0 #[]) (.ref 0 #[]), .lam (.ref 0 #[]) (.var 0)⟩,
    #[.ref 1 #[]], #[bool, target], #[.zero], #[]⟩

/-- The first proof certificate of an operation: its index among the role's evidence and its
address. -/
private def proofOf (table : Ix.Kernel.RoleTable) (r : Ix.Kernel.Role) :
    Option (Nat × Address) := Id.run do
  for (r', entries) in table.evidence do
    if r' == r then
      for (e, i) in entries.zipIdx do
        if let .proof a := e then return some (i, a)
  return none

/-- The table with the certificate at `index` of `r`'s evidence replaced. -/
private def withCertificate (table : Ix.Kernel.RoleTable) (r : Ix.Kernel.Role) (index : Nat)
    (cert : Address) : Ix.Kernel.RoleTable :=
  { table with evidence := table.evidence.map fun (role, es) =>
      (role, if role == r then
        (es : Array (Ix.Kernel.Evidence Address)).set! index (.proof cert) else es) }

/-- The table with the roles `rs` rebound. -/
private def rebind (table : Ix.Kernel.RoleTable) (rs : List (Ix.Kernel.Role × Address)) :
    Ix.Kernel.RoleTable :=
  { table with bound := table.bound.map fun (r, b) =>
      (r, match rs.find? (·.1 == r) with | some (_, a) => a | none => b) }

/-- The certificate `cert` with one more reference, `extra`, held by an unused sharing entry. -/
private def withExtra (env : Ixon.Env) (cert extra : Address) : Except String (Ixon.Env × Address) := do
  let some c := env.getConst? cert | throw "missing certificate"
  return put env { c with
    sharing := c.sharing.push (.ref c.refs.size.toUInt64 #[])
    refs := c.refs.push extra }

/-- The operations of the well-founded block with a proof certificate, in table order: the
first (its certificate is the one given the extra reference) and the last (the later operation
the refused cases reach). -/
private def firstAndLast (table : Ix.Kernel.RoleTable) :
    Except String (Ix.Kernel.Role × Nat × Address × Ix.Kernel.Role) := do
  let mut first : Option (Ix.Kernel.Role × Nat × Address) := none
  let mut last : Option Ix.Kernel.Role := none
  for (r, entries) in table.evidence do
    if let .ops := (r.spec (md := .anon)).kind then
      for (e, i) in entries.zipIdx do
        if let .proof a := e then
          if first.isNone then first := some (r, i, a)
          last := some r
  let some (rA, index, cert) := first | throw "no operation proof certificate"
  let some rD := last | throw "no operation proof certificate"
  if rA == rD then throw "one well-founded operation only"
  return (rA, index, cert, rD)

/-- The unchanged default table. -/
private def defaultCase : Except String Case := do
  bindingCase "binding: unchanged full default table" (← base) true

/-- A reference to the later operation from the first operation's certificate: directly
(`direct`), through an unbound record that references it (`unbound`), through a record bound
to `True` that references it (`true`), or a record bound to `True` with no further reference
(`trueOnly`). `True.intro` is rebound to a proof of the record and `Lean.trustCompiler` to an
axiom of it, as the type comparison of those roles then requires. -/
private def trueCase (mode : String) : Except String Case := do
  let env ← base
  let table ← Ix.Kernel.Reader.defaultTable
  let (rA, index, cert, rD) ← firstAndLast table
  let some d := table.addressOf? rD | throw "the later operation is unbound"
  let (env, x) := put env (propDef (if mode == "trueOnly" then none else some d))
  let (env, xi) := put env (propProof x)
  let (env, tc) := put env ⟨.axio ⟨false, 0, .ref 0 #[]⟩, #[], #[x], #[.zero], #[]⟩
  let (env, replacement) ← withExtra env cert (if mode == "direct" then d else x)
  let rebound := mode == "true" || mode == "trueOnly"
  let table := withCertificate table rA index replacement
  let table := if rebound then
      rebind table [(.true, x), (.trueIntro, xi), (.trustCompiler, tc)] else table
  table.check
  let env ← withRoleTable env table.toBytes
  let (label, accept) := match mode with
    | "direct" => (s!"a certificate of {repr rA} references {repr rD} directly", false)
    | "unbound" =>
      (s!"a certificate of {repr rA} references an unbound record that references {repr rD}", false)
    | "true" =>
      (s!"a certificate of {repr rA} references a record bound to True that references {repr rD}",
        false)
    | _ => (s!"a certificate of {repr rA} references a record bound to True", true)
  bindingCase s!"binding: {label}" env accept (if accept then none else some scanMessage)

/-- A reference to the later operation through a record bound to `Lean.reduceBool` (an anchor
no validation walks): `Y : Bool → Bool` referencing the later operation, `Lean.ofReduceBool`
rebound to an axiom of its pinned type at `Y`. -/
private def reduceBoolCase : Except String Case := do
  let env ← base
  let table ← Ix.Kernel.Reader.defaultTable
  let (rA, index, cert, rD) ← firstAndLast table
  let some d := table.addressOf? rD | throw "the later operation is unbound"
  let some bool := table.addressOf? .bool | throw "Bool is unbound"
  let some rb := table.addressOf? .reduceBool | throw "Lean.reduceBool is unbound"
  let some orb := table.addressOf? .ofReduceBool | throw "Lean.ofReduceBool is unbound"
  let some orbC := env.getConst? orb | throw "no record for Lean.ofReduceBool"
  unless orbC.refs.contains rb do throw "Lean.ofReduceBool's record does not name Lean.reduceBool"
  let (env, y) := put env (boolFun bool d)
  let (env, orbY) := put env { orbC with refs := orbC.refs.map fun r => if r == rb then y else r }
  let (env, replacement) ← withExtra env cert y
  let table := rebind (withCertificate table rA index replacement)
    [(.reduceBool, y), (.ofReduceBool, orbY)]
  table.check
  let env ← withRoleTable env table.toBytes
  bindingCase s!"binding: a certificate of {repr rA} references a record bound to \
    Lean.reduceBool that references {repr rD}" env false (some scanMessage)

/-- A certificate of `r` given an unused reference to the record bound to `target`. -/
private def extraCase (label : String) (r target : Ix.Kernel.Role) : Except String Case := do
  let env ← base
  let table ← Ix.Kernel.Reader.defaultTable
  let some (index, cert) := proofOf table r | throw s!"{repr r} has no proof certificate"
  let some t := table.addressOf? target | throw s!"{repr target} is unbound"
  let (env, replacement) ← withExtra env cert t
  let table := withCertificate table r index replacement
  table.check
  let env ← withRoleTable env table.toBytes
  bindingCase s!"binding: a certificate of {repr r} references {repr target}, {label}" env true

def run : IO UInt32 := do
  if (← IO.getEnv "IX_OP_ORDER_DEFAULT_ONLY").isSome then
    return (← runCases "ixvm-op-order-scan" #[fun _ => defaultCase] (jobs := 1)
      (circuit := some true))
  let cases : Array Builder := #[
    fun _ => defaultCase,
    fun _ => trueCase "trueOnly",
    -- `Nat.add` (group 8) is in force in the well-founded block
    fun _ => extraCase "an operation in force" .natDiv .natAdd,
    -- `Nat.mod` (group 34) is among the needs of `Nat.gcd`'s group (35)
    fun _ => extraCase "an operation among its group's needs" .natGcd .natMod,
    -- `List` (group 43) is a later role and no operation
    fun _ => extraCase "a later role that is no operation" .natDiv .list,
    fun _ => trueCase "direct",
    fun _ => trueCase "unbound",
    fun _ => trueCase "true",
    fun _ => reduceBoolCase]
  runCases "ixvm-op-order-scan" cases (jobs := 4) (circuit := some true)

end Tests.Ix.IxVM.OpOrderScan
