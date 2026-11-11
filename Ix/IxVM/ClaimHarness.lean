module
public import Ix.Aiur.Protocol
public import Ix.Ixon
public import Ix.Claim
public import Ix.AssumptionTree
public import Ix.CompileCertified
public import Ix.Common
public import Ix.PrimAddrs
public import Ix.ClaimContext
public import Ix.IxVM.PwHints
public import Ix.IxVM.Model

public section

/-!
# IxVM Claim harness

Lean-side glue between `Ix.Claim` and the IxVM `verify_claim` /
`verify_const` entrypoints.
-/
namespace IxVM.ClaimHarness

/-- Resolve a Lean name to its `Ixon.Env` `Address`, or fail with a
    descriptive `IO` error. Used by every claim/witness builder that
    starts from a Lean name. -/
def lookupAddr (ixonEnv : Ixon.Env) (name : Lean.Name) : IO Address :=
  match ixonEnv.getAddr? (Ix.Name.fromLeanName name) with
  | some addr => pure addr
  | none => throw <| IO.userError s!"{name} not found in Ixon environment"

/-- Nat / Bool constants the kernel's primitive dispatch synthesizes at
    reduction time (nat literal → succ chain, nat_beq/ble → Bool.true/
    false). Bytes for these MUST live in ch 2 for the kernel's `get_ci` to
    load them — but they may not be dependencies of the target's proof
    body. Seed them into the compile list. -/
def synthesizedPrimNames : Array Lean.Name :=
  #[`Bool.true, `Bool.false, `Nat.zero, `Nat.succ, `Bool,
    -- String-literal ctor expansion (str_lit_to_ctor): the def_eq
    -- Tier 1c / proj-head expansion fabricates Consts of these.
    `String, `String.ofList, `Char, `Char.ofNat, `List.nil, `List.cons]

/-- The Lean names of the roles' constants (`Ix.Kernel.Role.leanName`). Test
    environments compile them with their closures, so a claim finds the record
    of every role the default table binds when it validates the role's group. -/
def roleNames : Array Lean.Name :=
  Ix.Kernel.Role.all.toArray.map fun r => r.leanName.toString.toName

/-- The records, blobs and hints the default role table's roles and evidence
    are validated against (`IxC/Kernel/Ixon/RoleData.lean`): the prelude's
    basis records, the evidence theorems and the well-founded operations'
    dependency closure in the compiled `Init`. -/
def defaultTableSupport : Except String (Array (Address × Ixon.Constant) ×
    Array (Address × ByteArray) × Array (Address × Lean.ReducibilityHints)) := do
  let closure := Ix.Kernel.Reader.RoleData.closure
  let records := (← Ix.Kernel.Reader.preludeRecords) ++ (← Ix.Kernel.Reader.evidenceRecords)
    ++ (← Ix.Kernel.Reader.decodeCommitted "closure" closure)
  let blobs ← (Ix.Kernel.Reader.RoleData.blobs ++ Ix.Kernel.Reader.RoleData.closureBlobs).mapM
    fun (hex, bytes) => do
      let some a := Ix.Kernel.Reader.addressOfHex hex
        | throw s!"default table blob: bad address {hex}"
      let some b := bytesOfHex bytes | throw s!"default table blob: bad bytes at {hex}"
      pure (a, b)
  let hints ← Ix.Kernel.Reader.RoleData.closureHints.mapM fun (hex, h) => do
    let some a := Ix.Kernel.Reader.addressOfHex hex
      | throw s!"default table hint: bad address {hex}"
    let hint : Lean.ReducibilityHints ← match h with
      | "opaque" => pure .opaque
      | "abbrev" => pure .abbrev
      | n => match n.toNat? with
        | some k => pure (.regular k.toUInt32)
        | none => throw s!"default table hint: bad hint {n} at {hex}"
    pure (a, hint)
  pure (records, blobs, hints)

/-- `env` bound to the role table `bytes` (its binding section), together with
    the records the default table's roles and evidence are validated against
    (`defaultTableSupport`, each with the projection records of its blocks)
    wherever `env` lacks them. A table that rebinds roles among those
    constants needs no other support. -/
def withRoleTable (env : Ixon.Env) (bytes : ByteArray) : Except String Ixon.Env := do
  let (records, blobs, hints) ← defaultTableSupport
  let table? := Ix.Kernel.RoleTable.ofBytes bytes
  let mut env := { env with roleBinding := some { address := Address.blake3 bytes, bytes } }
  let wrapper (info : Ixon.ConstantInfo) : Address × Ixon.Constant :=
    let c : Ixon.Constant := ⟨info, #[], #[], #[]⟩
    (Address.blake3 (Ixon.ser c), c)
  for (a, c) in records do
    if let .axio _ := c.info then
      if let some table := table? then
        if !table.bound.any (·.2 == a) then continue
    let mut entries : Array (Address × Ixon.Constant) := #[(a, c)]
    if let .muts members := c.info then
      for (m, i) in members.zipIdx do
        let i := i.toUInt64
        match m with
        | .defn _ => entries := entries.push (wrapper (.dPrj ⟨i, a⟩))
        | .recr _ => entries := entries.push (wrapper (.rPrj ⟨i, a⟩))
        | .indc ind =>
          entries := entries.push (wrapper (.iPrj ⟨i, a⟩))
          for (_, cidx) in ind.ctors.zipIdx do
            entries := entries.push (wrapper (.cPrj ⟨i, cidx.toUInt64, a⟩))
    for (addr, record) in entries do
      unless env.consts.contains addr do
        env := env.storeConst addr record
  for (a, b) in blobs do
    unless env.blobs.contains a do
      env := { env with blobs := env.blobs.insert a b }
  for (a, h) in hints do
    unless env.anonHints.contains a do
      env := { env with anonHints := env.anonHints.insert a h }
  return env

/-- `env` with the default role table (`Ix.Kernel.Reader.defaultTable`) as its
    role binding when it carries none (`withRoleTable`). -/
def withDefaultRoleBinding (env : Ixon.Env) : Except String Ixon.Env := do
  let env ← if env.roleBinding.isSome then pure env
    else withRoleTable env (← Ix.Kernel.Reader.defaultTableBytes)
  -- the prover-side models of the mutual and nested blocks (witness only:
  -- `IxVM.Model`; neither `consts` nor any claim changes)
  IxVM.Model.attach env

/-- Close `roots` under `Lean.collectDependenciesMany` and every collected
    inductive's recursors (`<ind>.rec` and nested `<all0>.rec_N`) so
    `Ix.Cert.compileReport`'s `unownedRecursor` check sees every inductive
    family's recursors when two families share an anonymous Ixon block
    (e.g., `Lean.Doc.MathMode` and `Bool`). -/
private def dedupConstList (entries : List (Lean.Name × Lean.ConstantInfo)) :
    List (Lean.Name × Lean.ConstantInfo) := Id.run do
  let mut seen : Lean.NameSet := {}
  let mut out : Array (Lean.Name × Lean.ConstantInfo) := #[]
  for entry in entries do
    if !seen.contains entry.1 then
      seen := seen.insert entry.1
      out := out.push entry
  return out.toList

private def collectCertifiedClosure (roots : Array Lean.Name)
    (leanEnv : Lean.Environment) : List (Lean.Name × Lean.ConstantInfo) := Id.run do
  let mut seeds := roots.filter leanEnv.constants.contains
  let mut deps := dedupConstList (Lean.collectDependenciesMany seeds leanEnv.constants)
  for _ in [0:4] do
    let mut seen : Lean.NameSet := {}
    for (n, _) in deps do seen := seen.insert n
    let recs := deps.foldl (init := #[]) fun acc (_, ci) =>
      match ci with
      | .inductInfo v =>
        let names := (Lean.mkRecName v.name) ::
          (List.range v.numNested).map fun i =>
            Lean.Name.mkStr (v.all.headD v.name) s!"rec_{i + 1}"
        acc ++ (names.filter fun r =>
          leanEnv.constants.contains r && !seen.contains r && !acc.contains r).toArray
      | _ => acc
    if recs.isEmpty then break
    seeds := seeds ++ recs
    deps := dedupConstList (Lean.collectDependenciesMany seeds leanEnv.constants)
  return deps

/-- `roots` with the recursors of every mutual or nested inductive family in
    their dependency closure and, when there is one, the recursors of every
    inductive in that closure (a nested block's containers among them): IxVM's
    modeled route validates such a block together with its whole recursor
    family (`KernelModeled::check_family`), and the model advice is generated
    from it, using the containers' recursors (`IxVM.Model`). -/
def withModeledRecursors (roots : Array Lean.Name) (leanEnv : Lean.Environment) :
    Array Lean.Name := Id.run do
  let mut roots := roots
  for _ in [0:6] do
    let deps := Lean.collectDependenciesMany roots leanEnv.constants
    let modeled := deps.any fun (_, ci) => match ci with
      | .inductInfo v => v.all.length > 1 || v.numNested > 0
      | _ => false
    unless modeled do break
    let mut more : Array Lean.Name := #[]
    for (_, ci) in deps do
      if let .inductInfo v := ci then
        let names := v.all.map Lean.mkRecName ++
          (List.range v.numNested).map fun i => Lean.Name.mkStr (v.all.headD v.name) s!"rec_{i + 1}"
        for r in names do
          if leanEnv.constants.contains r && !roots.contains r && !more.contains r then
            more := more.push r
    if more.isEmpty then break
    roots := roots ++ more
  return roots

/-- Variant of loadIxonEnv: also seeds the constants the kernel
    fabricates during reduction (Bool.true/false + Nat.zero/succ), so
    their bytes are always in ch 2 even when the target's proof body
    doesn't textually reference them. -/
def loadIxonEnv (name : Lean.Name) (leanEnv : Lean.Environment) :
    IO Ixon.Env := do
  let roots := withModeledRecursors
    ((#[name] ++ synthesizedPrimNames ++ roleNames).filter leanEnv.constants.contains) leanEnv
  let initial := dedupConstList (Lean.collectDependenciesMany roots leanEnv.constants)
  let res ← match ← Ix.CompileM.compileCertified leanEnv initial 32 with
    | .ok out => pure (.ok out)
    | .error _ => Ix.CompileM.compileCertified leanEnv (collectCertifiedClosure roots leanEnv) 32
  match res with
  | .error e => throw (IO.userError s!"the certified Lean compile of {name}'s closure failed: {e}")
  | .ok out =>
    unless out.failures.isEmpty do
      let fMap := out.failures.toMap
      throw (IO.userError s!"the certified Lean compile of {name}'s closure: \
        {fMap.size} constant(s) failed to compile: \
        {Ix.CompileM.recordedFailures fMap}")
    IO.ofExcept (withDefaultRoleBinding out.env)

/-- Compile the union of `names`'s transitive closures into one shared
    Ixon env. -/
def loadSharedIxonEnv (names : Array Lean.Name) (leanEnv : Lean.Environment) :
    IO Ixon.Env := do
  let roots := withModeledRecursors
    ((names ++ synthesizedPrimNames ++ roleNames).filter leanEnv.constants.contains) leanEnv
  let initial := dedupConstList (Lean.collectDependenciesMany roots leanEnv.constants)
  let res ← match ← Ix.CompileM.compileCertified leanEnv initial 32 with
    | .ok out => pure (.ok out)
    | .error _ => Ix.CompileM.compileCertified leanEnv (collectCertifiedClosure roots leanEnv) 32
  match res with
  | .error e => throw (IO.userError s!"the certified Lean compile of shared closure failed: {e}")
  | .ok out =>
    unless out.failures.isEmpty do
      let fMap := out.failures.toMap
      throw (IO.userError s!"the certified Lean compile of shared closure: \
        {fMap.size} constant(s) failed to compile: \
        {Ix.CompileM.recordedFailures fMap}")
    IO.ofExcept (withDefaultRoleBinding out.env)

/-- The `refs` indices `e` uses as a CONSTANT: `Ref i` and the type index
    of `Prj i`. -/
partial def constIdxsExpr : Ixon.Expr → Std.HashSet UInt64
  | .ref i _ => {i}
  | .prj i _ inner => (constIdxsExpr inner).insert i
  | .app a b | .lam _ a b | .all _ _ a b =>
    (constIdxsExpr a).union (constIdxsExpr b)
  | .letE _ t v b =>
    ((constIdxsExpr t).union (constIdxsExpr v)).union (constIdxsExpr b)
  | _ => {}

/-- The `refs` indices `c` uses as constants, over its `sharing` table and
    every Expr its `ConstantInfo` carries. -/
def constIdxsOf (c : Ixon.Constant) : Std.HashSet UInt64 := Id.run do
  let mut out : Std.HashSet UInt64 := {}
  for e in c.sharing do
    out := out.union (constIdxsExpr e)
  let ofDefn (d : Ixon.Definition) := (constIdxsExpr d.typ).union (constIdxsExpr d.value)
  let ofRecr (r : Ixon.Recursor) := r.rules.foldl
    (fun acc rule => acc.union (constIdxsExpr rule.rhs)) (constIdxsExpr r.typ)
  let ofIndc (i : Ixon.Inductive) := i.ctors.foldl
    (fun acc ctor => acc.union (constIdxsExpr ctor.typ)) (constIdxsExpr i.typ)
  match c.info with
  | .defn d => out := out.union (ofDefn d)
  | .recr r => out := out.union (ofRecr r)
  | .axio a => out := out.union (constIdxsExpr a.typ)
  | .quot q => out := out.union (constIdxsExpr q.typ)
  | .muts members =>
    for m in members do
      out := out.union <| match m with
        | .defn d => ofDefn d
        | .indc i => ofIndc i
        | .recr r => ofRecr r
  | _ => pure ()
  return out

/-- Content address of a synthesized projection wrapper. -/
def projWrapperAddr (info : Ixon.ConstantInfo) : Address :=
  Address.blake3 (Ixon.ser (⟨info, #[], #[], #[]⟩ : Ixon.Constant))

/-- Walk the Constant ref-graph from `roots` to compute the set of
    addresses needed to type-check them. -/
partial def closureFromRoots (env : Ixon.Env) (roots : Array Address) :
    Std.HashSet Address := Id.run do
  let mut visited : Std.HashSet Address := {}
  let mut worklist : Array Address := roots
  while !worklist.isEmpty do
    let addr := worklist.back!
    worklist := worklist.pop
    if visited.contains addr then continue
    visited := visited.insert addr
    -- a modeled block brings its model records, its recursor family and the
    -- container recursors its payload names (witness)
    if let some deps := env.modelDeps[addr]? then
      for d in deps do worklist := worklist.push d
    let some c := env.getConst? addr <|> env.modelRecords[addr]? | continue
    for r in c.refs do worklist := worklist.push r
    match c.info with
    | .iPrj p | .cPrj p => worklist := worklist.push p.block
    | _ => pure ()
    match c.info with
    | .rPrj p | .dPrj p => worklist := worklist.push p.block
    | _ => pure ()
    if let .muts members := c.info then
      let mut i : UInt64 := 0
      for m in members do
        let info : Ixon.ConstantInfo := match m with
          | .defn _ => .dPrj ⟨i, addr⟩
          | .indc _ => .iPrj ⟨i, addr⟩
          | .recr _ => .rPrj ⟨i, addr⟩
        worklist := worklist.push (projWrapperAddr info)
        if let .indc ind := m then
          let mut cidx : UInt64 := 0
          for _ in ind.ctors do
            worklist := worklist.push (projWrapperAddr (.cPrj ⟨i, cidx, addr⟩))
            cidx := cidx + 1
        i := i + 1
  return visited

/-- Build the `ixon_serde_test` / `ixon_serde_blake3_bench` IOBuffer. -/
def buildSerdeIOBuffer (ixonEnv : Ixon.Env) : Aiur.IOBuffer × Nat :=
  ixonEnv.consts.valuesIter.fold (init := (default, 0)) fun (ioBuffer, i) lc =>
    let bytes := lc.rawBytes
    (ioBuffer.extend 0 #[.ofNat i] (bytes.data.map .ofUInt8), i + 1)

/-- Encode a `Lean.ReducibilityHints` as a single `G` per the convention
    `load_constant_hint` decodes (opaque → 0, abbrev → 0xFFFFFFFF,
    regular n → clamp(1 + n, 0xFFFFFFFE)). -/
private def hintToG : Lean.ReducibilityHints → Aiur.G
  | .opaque => .ofNat 0
  | .abbrev => .ofNat 0xFFFFFFFF
  | .regular n => .ofNat (min (1 + n.toNat) 0xFFFFFFFE)

/-- Insert all per-address entries for `addr`s satisfying `keep` into
    `ioBuffer`. -/
def addEntries (ixonEnv : Ixon.Env) (keep : Address → Bool)
    (ioBuffer : Aiur.IOBuffer) : Aiur.IOBuffer := Id.run do
  let mut ioBuffer := ioBuffer
  for (addr, lc) in ixonEnv.consts do
    if !keep addr then continue
    let bytes := lc.rawBytes
    let key : Array Aiur.G := addr.hash.data.map .ofUInt8
    ioBuffer := ioBuffer.extend 2 key (bytes.data.map .ofUInt8)
  for (addr, rawBytes) in ixonEnv.blobs do
    if !keep addr then continue
    let key : Array Aiur.G := addr.hash.data.map .ofUInt8
    ioBuffer := ioBuffer.extend 4 key (rawBytes.data.map fun b => .ofNat b.toNat)
  for (addr, hints) in ixonEnv.anonHints do
    if !keep addr then continue
    let key : Array Aiur.G := addr.hash.data.map .ofUInt8
    ioBuffer := ioBuffer.extend 3 key #[hintToG hints]
  -- the model records (witness, `IxVM.Model`): served like any record on
  -- channels 2 and 3, and the unbound advice that finds them on channel 7
  for (addr, c) in ixonEnv.modelRecords do
    if !keep addr || ixonEnv.consts.contains addr then continue
    let key : Array Aiur.G := addr.hash.data.map .ofUInt8
    ioBuffer := ioBuffer.extend 2 key ((Ixon.ser c).data.map .ofUInt8)
  for (addr, hints) in ixonEnv.modelHints do
    if !keep addr || ixonEnv.anonHints.contains addr then continue
    let key : Array Aiur.G := addr.hash.data.map .ofUInt8
    ioBuffer := ioBuffer.extend 3 key #[hintToG hints]
  for (addr, rawBytes) in ixonEnv.modelBlobs do
    if !keep addr || ixonEnv.blobs.contains addr then continue
    let key : Array Aiur.G := addr.hash.data.map .ofUInt8
    ioBuffer := ioBuffer.extend 4 key (rawBytes.data.map fun b => .ofNat b.toNat)
  -- the payloads, keyed by the modeled block (`KernelModeled::read_payload`)
  for (addr, payload) in ixonEnv.models do
    if !keep addr then continue
    let key : Array Aiur.G := addr.hash.data.map .ofUInt8
    ioBuffer := ioBuffer.extend 7 key (payload.data.map .ofUInt8)
  return ioBuffer

/-- A ready-to-run Aiur invocation: function name to dispatch, public
    input (`Array G`), and the IOBuffer pre-populated with every
    blake3-keyed witness payload the entrypoint will demand. -/
structure ClaimWitness where
  funcName      : Lean.Name
  input         : Array Aiur.G
  inputIOBuffer : Aiur.IOBuffer
  deriving Inhabited

/-- Convert an `Address` to its `Array G` IOBuffer-key form. -/
@[inline] private def addrKey (a : Address) : Array Aiur.G :=
  a.hash.data.map .ofUInt8

/-- An `Address` as 8 packed-4-LE-byte field elements: the `verify_claim`
    public-input (and ch-0 key) form. Must match the in-circuit `b3_pack`. -/
@[inline] def packedDigestKey (a : Address) : Array Aiur.G :=
  let h := a.hash.data
  (Array.range 8).map fun i =>
    .ofNat (h[4*i]!.toNat + 256 * h[4*i+1]!.toNat
      + 65536 * h[4*i+2]!.toNat + 16777216 * h[4*i+3]!.toNat)

/-- Look up the `AssumptionTree` at `root` in the caller-supplied
    `trees` map and seed its serialized bytes at key=`root` in
    `ioBuffer`. -/
private def seedTreeAt (root : Address)
    (trees : Std.HashMap Address Ix.AssumptionTree)
    (ioBuffer : Aiur.IOBuffer) : Except String Aiur.IOBuffer :=
  match trees.get? root with
  | some tree =>
    let bytes := Ix.AssumptionTree.ser tree
    .ok (ioBuffer.extend 1 (addrKey tree.root) (bytes.data.map .ofUInt8))
  | none => .error s!"no assumption tree supplied for root {root}"

/-- The constants the role binding names: every bound role and (when
    `!assumeBinding`) every proof evidence theorem the environment carries. -/
def bindingRoots (env : Ixon.Env) (assumeBinding : Bool := false) : Array Address := Id.run do
  let some binding := env.roleBinding | return #[]
  let some table := Ix.Kernel.RoleTable.ofBytes binding.bytes | return #[]
  let mut roots := table.bound.map (·.2)
  unless assumeBinding do
    for (_, entries) in table.evidence do
      for e in entries do
        if let .proof a := e then roots := roots.push a
  return roots.filter env.consts.contains

/-- Seed the environment's role binding on channel 6, keyed by its hash: the
    circuit reads a claim's roles there. -/
def seedBinding (env : Ixon.Env) (ioBuffer : Aiur.IOBuffer) : Aiur.IOBuffer :=
  match env.roleBinding with
  | some binding =>
    ioBuffer.extend 6 (addrKey binding.address) (binding.bytes.data.map .ofUInt8)
  | none => ioBuffer

/-- The full witness byte scope for `target`: the closure of `target`
    together with every primitive address present in `env`, the role
    binding's constants (`bindingRoots`) and user axioms, all as walk ROOTS. -/
def closureFrom (env : Ixon.Env) (target : Address)
    (assumeBinding : Bool := false) : Std.HashSet Address :=
  closureFromRoots env
    (#[target] ++ Ix.primAddrSet.toArray.filter env.consts.contains
      ++ bindingRoots env assumeBinding ++ Ix.ClaimContext.userAxioms env)

/-- Serializes `claim`, seeds its bytes at `key = blake3(claim)`, and
    populates the IOBuffer with the `closureFrom` byte scope of every
    address the claim variant names (plus any caller-supplied
    `AssumptionTree`s under their merkle roots). -/
def buildClaimWitness (env : Ixon.Env) (claim : Ix.Claim)
    (trees : Std.HashMap Address Ix.AssumptionTree := {})
    (profiles : Std.HashMap Address ByteArray := {}) :
    Except String ClaimWitness := do
  let env ← withDefaultRoleBinding env
  let claimBytes := Ix.Claim.ser claim
  let digestKey := packedDigestKey (Address.blake3 claimBytes)
  let mut ioBuffer : Aiur.IOBuffer := seedBinding env default
  ioBuffer := ioBuffer.extend 0 digestKey (claimBytes.data.map .ofUInt8)
  let seedAsm asm buf := match asm with
    | some r => seedTreeAt r trees buf
    | none => .ok buf
  let seedAxioms (ctx : Ix.ClaimContext) (buf : Aiur.IOBuffer) : Except String Aiur.IOBuffer :=
    match ctx.axioms with
    | none => .ok buf
    | some axRoot =>
      if trees.contains axRoot then
        seedTreeAt axRoot trees buf
      else match Ix.ClaimContext.userAxiomTree env with
      | some axTree =>
        if axTree.root == axRoot then
          let bytes := Ix.AssumptionTree.ser axTree
          .ok (buf.extend 1 (addrKey axTree.root) (bytes.data.map .ofUInt8))
        else .error s!"no assumption tree supplied for axioms root {axRoot}"
      | none => .error s!"no assumption tree supplied for axioms root {axRoot}"
  match claim with
  | .check ctx addr asm =>
    ioBuffer := addEntries env (closureFrom env addr ctx.bindingAssumed).contains ioBuffer
    ioBuffer ← seedAxioms ctx ioBuffer
    ioBuffer ← seedAsm asm ioBuffer
  | .eval ctx input output asm =>
    let inputClosure := closureFrom env input
    let outputClosure := closureFrom env output
    ioBuffer := addEntries env
      (fun a => inputClosure.contains a || outputClosure.contains a) ioBuffer
    ioBuffer ← seedAxioms ctx ioBuffer
    ioBuffer ← seedAsm asm ioBuffer
  | .checkEnv ctx root asm =>
    ioBuffer := addEntries env (fun _ => true) ioBuffer
    ioBuffer ← seedTreeAt root trees ioBuffer
    ioBuffer ← seedAxioms ctx ioBuffer
    ioBuffer ← seedAsm asm ioBuffer
  | .resource root profile =>
    ioBuffer := addEntries env (fun _ => true) ioBuffer
    ioBuffer ← seedTreeAt root trees ioBuffer
    let some bytes := profiles[profile]? <|> env.blobs[profile]?
      | throw s!"no resource profile supplied for {profile}"
    unless Address.blake3 bytes == profile do throw "resource profile hash mismatch"
    ioBuffer := ioBuffer.extend 5 (addrKey profile) (bytes.data.map .ofUInt8)
  | .reveal comm _info =>
    ioBuffer := addEntries env (closureFrom env comm).contains ioBuffer
  | .contains tree _target =>
    ioBuffer ← seedTreeAt tree trees ioBuffer
  | .binding _ bound =>
    unless env.roleBinding.map (·.address) == some bound do
      throw s!"the environment's role binding is not {bound}"
    let roots := Ix.primAddrSet.toArray.filter env.consts.contains ++ bindingRoots env
    ioBuffer := addEntries env (closureFromRoots env roots).contains ioBuffer
  | .catalog .. =>
    throw "catalog claims have no single-run witness; they are formed by \
aggregating their members' check-env claims"
  -- the binder data the conversion reads (D2, `IxVM.PwHints`)
  ioBuffer ← IxVM.PwHints.withHints claim ioBuffer env
  return { funcName := `verify_claim
           input := digestKey, inputIOBuffer := ioBuffer }

/-- The owned constants a shard claim may name: `owned` without those outside
    Lean's logic (unsafe or partial, or projected from such a block;
    `Ixon.Env.outsideLogicAt`), which IxVM refuses as seeds
    (`KernelClaim::assert_claimable`). The rest stays closed under the claim
    walk: a safe constant references no unsafe one (`KernelCheck::assert_safety`),
    so no walk from it reaches what is left out. -/
def claimableOwned (env : Ixon.Env) (owned : Array Address) : Except String (Array Address) := do
  if owned.isEmpty then throw "shardCheckEnvClaim: empty owned set"
  let kept := env.dropOutsideLogic owned
  if kept.isEmpty then
    throw s!"shardCheckEnvClaim: all {owned.size} owned constant(s) are unsafe or partial, \
      outside Lean's logic; IxVM certifies none of them"
  pure kept

/-- The shard claim over `owned`, already `claimableOwned`, under the bound
    `env`. -/
def shardCheckEnvClaimTreesOf (env : Ixon.Env) (owned : Array Address)
    (assumeBinding : Bool) :
    Except String (Ix.Claim × Std.HashMap Address Ix.AssumptionTree) := do
  let ownedSet : Std.HashSet Address := owned.foldl (·.insert ·) {}
  let frontier : Array Address := Id.run do
    let mut fs : Std.HashSet Address := {}
    for o in owned do
      match env.getConst? o with
      | none => pure ()
      | some c =>
        let used := constIdxsOf c
        for (r, i) in c.refs.zipIdx do
          if used.contains i.toUInt64 && !ownedSet.contains r
              && env.consts.contains r then
            fs := fs.insert r
        let blockOpt : Option Address := match c.info with
          | .iPrj p => some p.block
          | .cPrj p => some p.block
          | .rPrj p => some p.block
          | .dPrj p => some p.block
          | _ => none
        match blockOpt with
        | some b =>
          if !ownedSet.contains b && env.consts.contains b then
            fs := fs.insert b
        | none => pure ()
    return fs.toArray
  let some ownedTree := Ix.AssumptionTree.canonical owned
    | .error "shardCheckEnvClaim: empty owned set"
  let asmTree? := Ix.AssumptionTree.canonical frontier
  let ctx ← ({ · with bindingAssumed := assumeBinding }) <$> Ix.ClaimContext.ofEnv env
  let claim := Ix.Claim.checkEnv ctx ownedTree.root (asmTree?.map (·.root))
  let mut trees : Std.HashMap Address Ix.AssumptionTree :=
    ({} : Std.HashMap Address Ix.AssumptionTree).insert ownedTree.root ownedTree
  if let some axTree := Ix.ClaimContext.userAxiomTree env then
    trees := trees.insert axTree.root axTree
  match asmTree? with
  | some asmTree => trees := trees.insert asmTree.root asmTree
  | none => pure ()
  pure (claim, trees)

/-- The kernel shard claim and its canonical subject/assumption trees, without
    constructing the witness byte closure. Its owned tree holds the
    `claimableOwned` constants of `owned`. -/
def shardCheckEnvClaimTrees (env : Ixon.Env) (owned : Array Address)
    (assumeBinding : Bool := false) :
    Except String (Ix.Claim × Std.HashMap Address Ix.AssumptionTree) := do
  let env ← withDefaultRoleBinding env
  shardCheckEnvClaimTreesOf env (← claimableOwned env owned) assumeBinding

/-- Claim/tree construction plus the byte closure needed by a Lean-built shard
    witness. -/
def shardCheckEnvClaim (env : Ixon.Env) (owned : Array Address)
    (assumeBinding : Bool := false) :
    Except String (Ix.Claim × Std.HashSet Address × Std.HashMap Address Ix.AssumptionTree) := do
  let env ← withDefaultRoleBinding env
  let owned ← claimableOwned env owned
  let (claim, trees) ← shardCheckEnvClaimTreesOf env owned assumeBinding
  let primitiveRoots := Ix.primAddrSet.toArray.filter env.consts.contains
  let closure := closureFromRoots env
    (owned ++ primitiveRoots ++ bindingRoots env assumeBinding ++ Ix.ClaimContext.userAxioms env)
  pure (claim, closure, trees)

/-- Variant of `buildShardCheckEnvWitness`: THIN frontier asm (see
    `shardCheckEnvClaimTrees`) with the `closureFrom` byte scope. -/
def buildShardCheckEnvWitness (env : Ixon.Env) (owned : Array Address)
    (assumeBinding : Bool := false) :
    Except String (Ix.Claim × ClaimWitness) := do
  let env ← withDefaultRoleBinding env
  let (claim, closure, trees) ← shardCheckEnvClaim env owned assumeBinding
  let claimBytes := Ix.Claim.ser claim
  let digestKey := packedDigestKey (Address.blake3 claimBytes)
  let mut ioBuffer : Aiur.IOBuffer := seedBinding env default
  ioBuffer := ioBuffer.extend 0 digestKey (claimBytes.data.map .ofUInt8)
  ioBuffer := addEntries env closure.contains ioBuffer
  for (root, _) in trees do
    ioBuffer ← seedTreeAt root trees ioBuffer
  ioBuffer ← IxVM.PwHints.withHints claim ioBuffer env
  return (claim, { funcName := `verify_claim
                   input := digestKey, inputIOBuffer := ioBuffer })

/-- Canonical merkle tree over every const address in `env` in Lean's logic
    (`Ixon.Env.inLogicConsts`): the owned tree of a `checkEnv` claim on the
    whole of `env`, which leaves out the unsafe and partial constants IxVM
    refuses as seeds. -/
def envCanonicalTree (env : Ixon.Env) : Option Ix.AssumptionTree :=
  Ix.AssumptionTree.canonical env.inLogicConsts

/-- Subject-only `verify_const` witness. -/
def buildVerifyConst (env : Ixon.Env) (target : Address) : Except String ClaimWitness := do
  let env ← withDefaultRoleBinding env
  let some binding := env.roleBinding
    | throw "verify_const: the environment carries no role binding"
  let closure := closureFrom env target
  let ioBuffer := addEntries env closure.contains (seedBinding env default)
  let ioBuffer ← (·.1) <$> IxVM.PwHints.annotate ioBuffer env
  return { funcName := `verify_const
           input := addrKey binding.address ++ addrKey target, inputIOBuffer := ioBuffer }

end IxVM.ClaimHarness

end
