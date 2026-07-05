module

public import Ix.Tc.Ingress

/-!
Mirror: crates/kernel/src/anon_work.rs (work enumeration) plus the driver
skeleton (the check loop itself lands with `Ix.Tc.Check`).

`buildAnonWork` identifies the kernel-checkable target set from `env.consts`
without consulting metadata sections. For each entry:
- projections (IPrj/CPrj/RPrj/DPrj) are skipped — covered by their parent
  Muts block;
- standalones (Defn/Recr/Axio/Quot) emit one `standalone` item;
- Muts blocks materialize to enumerate members, emitting one `block` item
  whose `primary` is the first member's projection address and whose
  `targets` list every member projection plus one CPrj per constructor.

Dispatch is on the leading Tag4 byte (`LazyConstant.peekTag`), avoiding body
parses for the ~95% of constants that are standalones or projections. Keys
are visited in ascending byte-lexicographic address order (Rust
`keys.sort_unstable()` parity).
-/

public section
@[expose] section

namespace Ix.Tc

/-- A single anon-mode work item — one `checkConst primary` per item
    suffices to typecheck every address in `targets`. -/
inductive AnonWorkItem where
  /-- A standalone (Defn/Recr/Axio/Quot) constant. -/
  | standalone (addr : Address)
  /-- A Muts block: checking `primary` (the first member's projection
      address) drives block coordination over all `targets`
      (`targets[0] == primary`). `blockAddr` is the block's own `consts`
      key — the address other constants' refs use. -/
  | block (blockAddr primary : Address) (targets : Array Address)
  deriving Repr, Inhabited

namespace AnonWorkItem

/-- The address to pass to `checkConst`. -/
def primary : AnonWorkItem → Address
  | .standalone addr => addr
  | .block _ p _ => p

/-- Every kernel-checked target this item covers. -/
def targets : AnonWorkItem → Array Address
  | .standalone addr => #[addr]
  | .block _ _ ts => ts

/-- Every `env.consts` key this item certifies well-typed when its primary
    checks: a standalone is its own address; a block adds the block's own
    `consts` key to the projection targets. The union over a full
    `buildAnonWork` is exactly `env.consts` keys. -/
def provenTargets : AnonWorkItem → Array Address
  | .standalone addr => #[addr]
  | .block blockAddr _ ts => #[blockAddr] ++ ts

end AnonWorkItem

/-- Enumerate the anon-mode kernel work set from `env.consts` (see module
    doc). Errors only on a corrupted env. -/
def buildAnonWork (env : Ixon.Env) : Except IngressErr (Array AnonWorkItem) := do
  let mut work : Array AnonWorkItem := #[]
  -- Ascending address order for deterministic run order.
  let keys := env.consts.keys.toArray.qsort fun a b => a.cmpBytes b == .lt
  for addr in keys do
    let some lc := env.consts[addr]?
      | throw s!"buildAnonWork: missing const at {addr}"
    let tag ← match lc.peekTag with
      | .ok t => pure t
      | .error e => throw s!"buildAnonWork: peekTag {addr}: {e}"
    match tag with
    | .iPrj | .cPrj | .rPrj | .dPrj =>
      -- Skip — covered by parent block.
      pure ()
    | .defn | .recr | .axio | .quot =>
      work := work.push (.standalone addr)
    | .muts =>
      let constant ← match lc.get with
        | .ok c => pure c
        | .error e => throw s!"buildAnonWork: materialize Muts {addr}: {e}"
      let .muts members := constant.info
        | throw s!"buildAnonWork: Tag muts but ConstantInfo differs at {addr}"
      let mut targets : Array Address := #[]
      for h : i in [0:members.size] do
        let idx := i.toUInt64
        match members[i] with
        | .defn _ => targets := targets.push (defnProjAddr addr idx)
        | .recr _ => targets := targets.push (recrProjAddr addr idx)
        | .indc ind =>
          targets := targets.push (indcProjAddr addr idx)
          for cidx in [0:ind.ctors.size] do
            targets := targets.push (ctorProjAddr addr idx cidx.toUInt64)
      if targets.isEmpty then
        continue
      work := work.push (.block addr targets[0]! targets)
  return work

/-- The ingress-block address that owns `addr`: a projection maps to its Muts
    block; anything else is its own block. -/
def blockOfAddr (env : Ixon.Env) (addr : Address) : Address :=
  match env.getConst? addr with
  | some c =>
    match c.info with
    | .iPrj p => p.block
    | .cPrj p => p.block
    | .rPrj p => p.block
    | .dPrj p => p.block
    | _ => addr
  | none => addr

/-- Eagerly ingress every work item into the kernel env (unit-test path; the
    production driver faults lazily). Returns the work list for the caller's
    check loop. -/
def ingressAll (ixonEnv : Ixon.Env) (verify : Bool := true) :
    IngressM (Array AnonWorkItem) := do
  let work ← IngressM.liftExcept (buildAnonWork ixonEnv)
  for item in work do
    match item with
    | .standalone addr =>
      let some c ← IngressM.liftExcept (getConstVerified ixonEnv addr verify)
        | throw s!"ingressAll: missing standalone {addr}"
      let _ ← ingressAnonStandalone ixonEnv addr c
    | .block blockAddr _ _ =>
      let some c ← IngressM.liftExcept
          (getConstVerified ixonEnv blockAddr verify)
        | throw s!"ingressAll: missing block {blockAddr}"
      let _ ← ingressAnonBlock ixonEnv c blockAddr
  return work

end Ix.Tc

end
end
