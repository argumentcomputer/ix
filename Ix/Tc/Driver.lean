module

public import Ix.Tc.Ingress
public import Ix.Tc.Check

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

/-! ### The anon check driver -/

/-- Driver configuration. -/
structure CheckCfg where
  /-- Verify `blake3(bytes) == addr` at every constant materialization
      (the soundness-critical integrity check; see `Ix.Tc.Ingress`). -/
  verifyHashes : Bool := true
  /-- Clear the reduction-memo caches every N work items (structural caches,
      constants, and the faulted set are preserved). `0` disables. -/
  clearEvery : Nat := 50
  deriving Repr, Inhabited

/-- One work item's verdict, fanned out per covered target address. -/
structure CheckResult where
  addr : Address
  err? : Option String
  deriving Repr, Inhabited

/-- Fresh anon checker state over `ixonEnv` with the lazy fault hook
    installed (constants ingress on demand as typechecking discovers them).
    Mirrors Rust `TypeChecker::new_with_lazy_anon`. -/
def TcState.newLazyAnon (ixonEnv : Ixon.Env) (verify : Bool := true) :
    TcState .anon :=
  { env := {}
    prims := .ofAnonAddrs
    lazyFault := some fun addr => ingressAnonAddrShallow ixonEnv addr verify }

/-- Check every anon work item of `ixonEnv` with one persistent kernel env
    (lazy faulting makes the cross-item constant reuse pay off) and a fresh
    checker state per item. Verdicts are fanned to every target the item
    covers. Never throws: per-item errors land in the results. -/
def checkEnvAnon (ixonEnv : Ixon.Env) (cfg : CheckCfg := {}) :
    Except IngressErr (Array CheckResult) := do
  let work ← buildAnonWork ixonEnv
  let mut results : Array CheckResult := #[]
  let mut st := TcState.newLazyAnon ixonEnv cfg.verifyHashes
  let mut sinceClear := 0
  for item in work do
    let primary : KId .anon := ⟨item.primary, ()⟩
    let err? ← match (TcM.checkConst primary).run st with
      | .ok () st' =>
        st := st'
        pure none
      | .error e st' =>
        st := st'
        pure (some (toString e))
    for target in item.targets do
      results := results.push ⟨target, err?⟩
    sinceClear := sinceClear + 1
    if cfg.clearEvery != 0 && sinceClear ≥ cfg.clearEvery then
      st := { st with env := st.env.clearReductionCaches }
      sinceClear := 0
  return results

/-- Read a serialized env (anon sections) and check it. -/
def checkIxeBytesAnon (bytes : ByteArray) (cfg : CheckCfg := {}) :
    Except IngressErr (Array CheckResult) := do
  match Ixon.deEnvAnon bytes with
  | .ok env => checkEnvAnon env cfg
  | .error e => throw s!"checkIxeBytesAnon: deserialize failed: {e}"

/-- Check a `.ixe` file from disk. -/
def checkIxeAnon (path : System.FilePath) (cfg : CheckCfg := {}) :
    IO (Except IngressErr (Array CheckResult)) := do
  let bytes ← IO.FS.readBinFile path
  return checkIxeBytesAnon bytes cfg

end Ix.Tc

end
end
