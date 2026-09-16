import Compilatrix.Ixon.V3.Tc.Ingress
import Compilatrix.Ixon.V3.Tc.Check

/-! Anonymous erased typechecking over raw v3 constants. The checker is the
pinned ix algorithm; this driver accounts for every source key, including
projection wrappers, and fails at the first error. -/

namespace Compilatrix.Ixon.V3.Tc

/-- Resolve a mutual block to a member that drives coordinated checking of
the entire block. Every other source key is checked directly, so an orphan
projection cannot evade the checking loop. -/
def checkTarget (address : Address) (c : Constant) : Except String Address := do
  match c.info with
  | .muts members =>
    match members[0]? with
    | none => throw "typing: empty mutual block"
    | some (.defn _) => return defnProjAddr address 0
    | some (.indc _) => return indcProjAddr address 0
    | some (.recr _) => return recrProjAddr address 0
  | _ => return address

/-- All materializations verify hashes and decode the original bytes. The
consumer uses a finite recursive budget per declaration/block. -/
def initialState (env : Compilatrix.Ixon.V3.Env) : TcState .anon := {
  env := {}
  prims := .ofAnonAddrs
  recFuel := 100000
  fuelBudget := 100000
  lazyFault := some fun address => ingressAnonAddrShallow env address true }

def checkEnv (env : Compilatrix.Ixon.V3.Env) : Except String Unit := do
  if env.consts.size > 16384 || env.blobs.size > 16384 then
    throw "typing: environment entry budget exceeded"
  let addresses := env.consts.keys.toArray.qsort (fun a b => a.cmpBytes b == .lt)
  let mut state := initialState env
  let mut sinceClear := 0
  for address in addresses do
    let some constant ← getConstVerified env address
      | throw s!"typing: missing constant {address}"
    let target ← checkTarget address constant
    let fresh := { state with recFuel := state.fuelBudget }
    match (TcM.checkConst (⟨target, ()⟩ : KId .anon)).run fresh with
    | .error error _ => throw s!"typing: {address}: {error}"
    | .ok () next =>
      state := next
      sinceClear := sinceClear + 1
      if sinceClear == 50 then
        state := { state with env := state.env.clearReductionCaches }
        sinceClear := 0

end Compilatrix.Ixon.V3.Tc
