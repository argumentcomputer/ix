import IxCCTests.Src.Resource

/-! Discriminating resource/csimp boundary controls. These synthetic table
tests establish structural rejection, not authentication or theorem typing. -/
set_option autoImplicit false
namespace IxCCTests.Src.ResourceCsimp
open IxCC IxCC.Src IxCCTests.Src

def run (a : Assert) : IO Unit := do
  let loaded ← loadK1
  let (add, _) ← Table.eqnNamed loaded "Nat.add"
  let base := { loaded.program with table := {}, resource := none }
  let some eq := base.known.eq | throw (IO.userError "csimp control: Eq missing")
  let some (.defn .defn .safe 0 addTy addVal) := base.decl? add |
    throw (IO.userError "csimp control: unannotated Nat.add missing")
  let (p, target) := Table.withConst base (.defn .defn .safe 0 addTy addVal)
  let theoremTy := Term.mkApps (.const eq [.succ .zero])
    [(addTy, .strict, .rel), (.const add [], .strict, .rel), (.const target [], .strict, .rel)]
  let (p, theoremId) := Table.withConst p (.defn .thm .safe 0 theoremTy (.natLit 0))
  -- The replacement subject is an unannotated callee of a separate root.
  let (p, caller) := Table.withConst p (.defn .defn .safe 0 addTy (.const add []))
  let p := { p with roots := [(p.addr caller, caller)] }
  expect a (addTy.leanFragment && addVal.leanFragment && caller != add &&
    p.roots.all (fun (_, root) => root != add)) "resource csimp: subject is an unannotated non-root callee"
  let entry : Resolve := .csimp target [] theoremId
  let table : Src.Table := { resolve := NatMap.ofList [(add, entry)] }
  let cert : Src.Table.TableCert := { resolve := [(add, .csimp target theoremId)] }
  expect a (match Src.Table.checkCsimp p add target theoremId with
    | .ok actual => actual == entry
    | .error _ => false)
    "resource csimp: same valid redirect accepted without context"
  expect a ((Src.Table.ofCert {} p cert).toOption.any (fun accepted => accepted.resolveOf add == some entry))
    "resource csimp: same valid redirect certificate accepted without context"
  expect a (Src.Table.validate {} { p with table } |>.isOk)
    "resource csimp: same valid redirect table accepted without context"
  let profile : Src.Resource.Profile := {}
  let bytes := profile.bytes
  let context : Src.Resource.Context := {
    address := Ixon.Address.blake3Pure bytes
    bytes
    pairs := [] }
  let bound := { p with resource := some context }
  expect a (Src.Resource.validate bound |>.isOk)
    "resource csimp: independently well-formed resource context with no checked subject pair"
  expect a (match Src.Table.checkCsimp bound add target theoremId with
    | .error message => message == "csimp: resource-bound replacement is unsupported"
    | .ok _ => false)
    "resource csimp: otherwise-valid unannotated callee redirect refused"
  expect a (match Src.Table.ofCert {} bound cert with
    | .error message => message == s!"table entry of constant {add}: csimp: resource-bound replacement is unsupported"
    | .ok _ => false)
    "resource csimp: otherwise-valid certificate refused at replacement restriction"
  expect a (match Src.Resource.selected bound table with
    | .error message => message == "resource binding: csimp replacement is unsupported"
    | .ok _ => false)
    "resource csimp: global selected table refuses unannotated callee redirect"
  expect a (match Src.Table.validate {} { bound with table } with
    | .error message => message == "resource binding: csimp replacement is unsupported"
    | .ok _ => false)
    "resource csimp: otherwise-valid table refused at global resource restriction"

end IxCCTests.Src.ResourceCsimp
