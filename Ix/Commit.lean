/-
  Ix.Commit: Commitment pipeline for ZK voting and claim construction.

  Provides utilities for:
  - Building a CompileEnv from rsCompilePhases output
  - Incrementally compiling and committing definitions
  - Building evaluation, check, and reveal claims
  - Opening committed constants for selective field revelation
-/
module
public import Ix.Claim
public import Ix.CompileM
public import Ix.CanonM

public section

namespace Ix.Commit

open Ixon (PutM runPut putConstant putExpr Comm)

-- ============================================================================
-- mkCompileEnv: Build a compilation cache from rsCompilePhases output
-- ============================================================================

/-- Create a CompileEnv from the output of rsCompilePhases.
    This allows incremental compilation of new definitions against
    the already-compiled base environment. -/
def mkCompileEnv (phases : Ix.CompileM.CompilePhases) : Ix.CompileM.CompileEnv :=
  { env := phases.rawEnv
  , nameToNamed := phases.compileEnv.named
  , constants := phases.compileEnv.consts
  , blobs := phases.compileEnv.blobs
  , totalBytes := 0 }

-- ============================================================================
-- Secret generation and commitment creation
-- ============================================================================

/-- Generate a random 32-byte secret for blinding a commitment. -/
def generateSecret : IO Address := do
  return ⟨← IO.getRandomBytes 32⟩

/-- Create a commitment from a payload address.
    Returns the Comm structure and the commitment address. -/
def commitConst (payload : Address) : IO (Comm × Address) := do
  let secret ← generateSecret
  let comm : Comm := ⟨secret, payload⟩
  return (comm, Comm.commit comm)

-- ============================================================================
-- Single-definition compilation
-- ============================================================================

/-- Canonicalize and compile a single definition, returning its content address.
    Uses CanonM to canonicalize the Lean expressions, then CompileM to compile.
    By default the definition is compiled under `Lean.Name.anonymous`; pass a
    different `name` to test alpha-invariance. -/
def compileDef (compileEnv : CompileM.CompileEnv)
    (lvls : List Lean.Name) (type value : Lean.Expr)
    (name : Lean.Name := .anonymous)
    : Except String (Address × CompileM.CompileEnv) := do
  -- 1. Create Lean ConstantInfo
  let defnVal : Lean.DefinitionVal := {
    name := name
    levelParams := lvls
    type := type
    value := value
    hints := .regular 0
    safety := .safe
  }
  let leanConst := Lean.ConstantInfo.defnInfo defnVal

  -- 2. Canonicalize via CanonM (pure, runs in Id)
  let (ixName, canonState) := (CanonM.canonName name).run {}
  let (ixConst, _) := (CanonM.canonConst leanConst).run canonState

  -- 3. Add to canonical environment
  let env' := { compileEnv.env with consts := compileEnv.env.consts.insert ixName ixConst }
  let compileEnv' := { compileEnv with env := env' }

  -- 4. Compile via CompileM (pure, runs in Except)
  let all : Ix.Set Ix.Name := ({} : Ix.Set Ix.Name).insert ixName
  match CompileM.compileBlockPure compileEnv' all ixName with
  | .error e => .error s!"compileDef: {e}"
  | .ok (result, blockState) =>
    -- 5. Serialize and hash to get content address
    let blockBytes := runPut (putConstant result.block)
    let addr := Address.blake3 blockBytes

    -- 6. Update CompileEnv with new constant
    let compileEnv'' := { compileEnv' with
      constants := compileEnv'.constants.insert addr result.block
      nameToNamed := compileEnv'.nameToNamed.insert ixName ⟨addr, result.blockMeta⟩
      blobs := blockState.blockBlobs.fold (fun m k v => m.insert k v) compileEnv'.blobs
      totalBytes := compileEnv'.totalBytes + blockBytes.size
    }
    .ok (addr, compileEnv'')

-- ============================================================================
-- Commit a definition: compile + create commitment + register
-- ============================================================================

/-- Full commitment pipeline: canonicalize, compile, commit, and register.
    Returns the commitment address, updated Lean environment, and updated CompileEnv.
    The committed constant is added to the Lean environment under
    `Address.toUniqueName commitAddr` so it can be referenced in later expressions. -/
def commitDef (compileEnv : CompileM.CompileEnv) (leanEnv : Lean.Environment)
    (lvls : List Lean.Name) (type value : Lean.Expr)
    : IO (Address × Lean.Environment × CompileM.CompileEnv) := do
  -- 1. Compile under anonymous to get payload address
  let (payloadAddr, compileEnv') ← IO.ofExcept (compileDef compileEnv lvls type value)

  -- 2. Create commitment
  let (_comm, commitAddr) ← commitConst payloadAddr

  -- 3. Alpha-invariance check: recompile under the commit name and verify
  --    the address is identical. If the compiler leaks names into the
  --    serialized block, this will catch it immediately rather than letting
  --    a broken commitment silently propagate.
  let commitName := Address.toUniqueName commitAddr
  let namedAddr ← IO.ofExcept do
    let (addr, _) ← compileDef compileEnv lvls type value (name := commitName)
    return addr
  if payloadAddr != namedAddr then
    throw $ IO.userError s!"commitDef: alpha-invariance failure: anonymous \
      compiled to {payloadAddr} but {commitName} compiled to {namedAddr}"

  -- 4. Add to Lean environment under the commitment address name
  let defnVal : Lean.DefinitionVal := {
    name := commitName
    levelParams := lvls
    type := type
    value := value
    hints := .regular 0
    safety := .safe
  }
  let decl := Lean.Declaration.defnDecl defnVal
  let leanEnv' ← match Lean.Environment.addDeclCore leanEnv 0 decl .none with
    | .ok env => pure env
    | .error _e => throw $ IO.userError "commitDef: addDeclCore failed"

  -- 4. Also register the committed name in CompileEnv so later compilations can reference it
  let (ixCommitName, _) := (CanonM.canonName commitName).run {}
  let compileEnv'' := { compileEnv' with
    nameToNamed := compileEnv'.nameToNamed.insert ixCommitName
      ⟨payloadAddr, .empty⟩
  }

  return (commitAddr, leanEnv', compileEnv'')

-- ============================================================================
-- Build claims
-- ============================================================================

/-- Build an evaluation claim from input and output expressions.
    Compiles both expressions to get their content addresses. -/
def evalClaim (compileEnv : CompileM.CompileEnv)
    (lvls : List Lean.Name) (input output type : Lean.Expr)
    : Except String Claim := do
  let (inputAddr, compileEnv') ← compileDef compileEnv lvls type input
  let (outputAddr, _) ← compileDef compileEnv' lvls type output
  return .eval inputAddr outputAddr

/-- Build a check claim: asserts that the compiled definition is well-typed. -/
def checkClaim (compileEnv : CompileM.CompileEnv)
    (lvls : List Lean.Name) (type value : Lean.Expr)
    : Except String Claim := do
  let (addr, _) ← compileDef compileEnv lvls type value
  return .check addr

/-- Build a reveal claim from a commitment address and revealed field info. -/
def revealClaim (comm : Address) (info : RevealConstantInfo) : Claim :=
  .reveal comm info

-- ============================================================================
-- Opening committed constants for reveal claims
-- ============================================================================

/-- Content address of a serialized expression: `blake3(putExpr e)`. -/
def exprAddr (e : Ixon.Expr) : Address :=
  Address.blake3 (runPut (putExpr e))

/-- Open all fields of a compiled Constructor. -/
def openConstructor (c : Ixon.Constructor) : RevealConstructorInfo :=
  { isUnsafe := some c.isUnsafe
  , lvls := some c.lvls
  , cidx := some c.cidx
  , params := some c.params
  , fields := some c.fields
  , typ := some (exprAddr c.typ) }

/-- Open a compiled RecursorRule at a given array index. -/
def openRecursorRule (idx : UInt64) (r : Ixon.RecursorRule) : RevealRecursorRule :=
  ⟨idx, r.fields, exprAddr r.rhs⟩

/-- Open all fields of a compiled MutConst component. -/
def openMutConst (mc : Ixon.MutConst) : RevealMutConstInfo :=
  match mc with
  | .defn d => .defn (some d.kind) (some d.safety) (some d.lvls)
      (some (exprAddr d.typ)) (some (exprAddr d.value))
  | .indc i =>
    let ctors := Id.run do
      let mut arr := #[]
      for j in [:i.ctors.size] do
        arr := arr.push (j.toUInt64, openConstructor i.ctors[j]!)
      return arr
    .indc (some i.recr) (some i.refl) (some i.isUnsafe)
      (some i.lvls) (some i.params) (some i.indices) (some i.nested)
      (some (exprAddr i.typ)) (some ctors)
  | .recr r =>
    let rules := Id.run do
      let mut arr := #[]
      for j in [:r.rules.size] do
        arr := arr.push (openRecursorRule j.toUInt64 r.rules[j]!)
      return arr
    .recr (some r.k) (some r.isUnsafe) (some r.lvls)
      (some r.params) (some r.indices) (some r.motives) (some r.minors)
      (some (exprAddr r.typ)) (some rules)

/-- Build a fully-revealed RevealConstantInfo from a compiled ConstantInfo.
    All fields are set to `some`. To build a partial reveal, set unwanted
    fields to `none` afterward, then pass to `revealClaim`. -/
def openConstantInfo (ci : Ixon.ConstantInfo) : RevealConstantInfo :=
  match ci with
  | .defn d => .defn (some d.kind) (some d.safety) (some d.lvls)
      (some (exprAddr d.typ)) (some (exprAddr d.value))
  | .recr r =>
    let rules := Id.run do
      let mut arr := #[]
      for j in [:r.rules.size] do
        arr := arr.push (openRecursorRule j.toUInt64 r.rules[j]!)
      return arr
    .recr (some r.k) (some r.isUnsafe) (some r.lvls)
      (some r.params) (some r.indices) (some r.motives) (some r.minors)
      (some (exprAddr r.typ)) (some rules)
  | .axio a => .axio (some a.isUnsafe) (some a.lvls) (some (exprAddr a.typ))
  | .quot q => .quot (some q.kind) (some q.lvls) (some (exprAddr q.typ))
  | .cPrj p => .cPrj (some p.idx) (some p.cidx) (some p.block)
  | .rPrj p => .rPrj (some p.idx) (some p.block)
  | .iPrj p => .iPrj (some p.idx) (some p.block)
  | .dPrj p => .dPrj (some p.idx) (some p.block)
  | .muts ms =>
    let components := Id.run do
      let mut arr := #[]
      for j in [:ms.size] do
        arr := arr.push (j.toUInt64, openMutConst ms[j]!)
      return arr
    .muts components

/-- Look up a committed constant and build a fully-revealed RevealConstantInfo.
    The caller should set unwanted fields to `none` for a partial reveal,
    then pass the result to `revealClaim`. -/
def openCommitment (compileEnv : CompileM.CompileEnv) (commitAddr : Address)
    : Except String RevealConstantInfo := do
  let commitName := Address.toUniqueName commitAddr
  let (ixCommitName, _) := (CanonM.canonName commitName).run {}
  let named ← match compileEnv.nameToNamed.get? ixCommitName with
    | some n => pure n
    | none => .error s!"openCommitment: unknown commitment {commitAddr}"
  let constant ← match compileEnv.constants.get? named.addr with
    | some c => pure c
    | none => .error s!"openCommitment: payload {named.addr} not found"
  return openConstantInfo constant.info

end Ix.Commit

end
