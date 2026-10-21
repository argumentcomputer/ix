/-
  pass3-rust-parity: the Rust Pass 3 core against the Lean one, on the images
  (part 1) and on the callers the compilers rewrite through them (part 2).

  The Rust core (`crates/compile/src/compile/pass3`) is the compiler's Pass 3
  since the flip; part 1 holds it to `Ix.Compile.Image` on what it computes,
  the image of a Lean recursor. Per case of image-gen's fixtures
  (`Tests.Ix.Compile.Image.files`, without the two ablations, whose options
  are Lean-only test switches), in the fixture's environment grown with
  `addDecl`:

  1. Pass 1's canonical form of the source block (`canonBlock
     Rules.compiler`) and its image specification under `Naming.default`:
     the canonical inductive of a class is `rep._ix`, as in the Rust
     specification (`pass3::spec::ind_name`);
  2. the canonical declarations through Lean's kernel, whose recursors are
     the generator's input;
  3. per Lean recursor of the block (`blockRecursors`): `imageOf {}` against
     the Rust `image_of` through the test-only FFI (`rs_pass3_images`,
     `crates/ffi/src/pass3.rs`). The Rust side receives the canonical classes
     and the block's closure: every constant the seeds' types mention,
     transitively, with each inductive's block, constructors and recursors
     (the nested auxiliaries included) and the generator's `imageSupport`.
     A constant the Rust side reads outside the closure fails its image, so
     a short closure shows up as a difference, never as agreement.

  Verdicts: `SAME` (universe parameters, arity, type and value raw-exact
  equal), `ALPHA` (type and value equal up to binder names and binder info
  only), `DIFF`, `LEAN-ERR`, `RUST-ERR`, `BOTH-ERR`, `ERROR` (the case did not
  run).

  Part 2, the callers (the flip's lockstep): per case, the source namespace
  `Ck.Src` (the changed block, its users, their auxiliaries) with the aux-gen
  seeds, closed under dependencies, compiled by the Lean pipeline
  (`compileLeanInput`, one worker) and by the Rust compiler (`rs_compile_env`,
  the bytes `ix compile` writes), partial output allowed: the two outputs must
  be byte-identical (`compile-lean --rust-check`'s ALIGNED, in process), which
  covers every caller's rewrite and its `_ix.inline` decompile records. A
  difference names the first `Named` entries that differ. Where the input is
  refused (`C4b`'s evaporation), the two must refuse exactly the same
  constants (`REFUSED`); their grounded subsets are not in the contract
  (`ix compile` is fail-closed) and differ before Pass 3 already. (Q1's part
  1 never compiled a caller; the Rust rewrite's memo once ignored the
  definition site, so a `T.below …` occurrence in a structural recursion
  functional's type and value shared one record in Rust and had two in Lean.)

  Part 3, the clique-ownership units (`co-*`, CQ5.2 (b)): each case of
  `Tests.Ix.Compile.Clique.Ownership` compiled whole as a unit (its clique's
  members with their closure and the rows' prerequisites; `WF8` with its
  caller and neighbour), by the Lean pipeline and the Rust compiler, with
  part 2's verdicts: the clique step, the plans, the rows and `_ix.src`
  copies of a transported well-founded clique, and a caller's refusal, in
  both compilers.

  The run passes iff every image is `SAME`, there are image-gen's 38, and
  every case's callers and every `co-*` unit are `ALIGNED` or `REFUSED`
  alike.

  Invoked as `lake test -- pass3-rust-parity` (tier `ci:compile-pipeline`).
-/
import Lean
import Ix.Compile.Canon
import Ix.Compile.Image
import Ix.Meta
import Tests.Ix.Compile.Image
import Tests.Ix.Compile.ImageProto
import Ix.CompileDriver
import Ix.EnvScope
import Tests.Ix.Compile.Harness.Units
import Ix.AuxGen.LiteralSupport
import Tests.Ix.Compile.Clique.Ownership

open Lean

namespace Tests.Ix.Compile.Pass3RustParity

open _root_.Ix.Compile.Image (ImageSpec Naming Image imageOf blockRecursors indOf imageSupport
  alphaEq)
open Tests.Ix.Compile.Image (Case files toLeanName ixName toIx toLeanExpr ixLookup)

/-- The Rust image of one recursor (`pass3::build::Image`). -/
structure RsImage where
  levelParams : Array _root_.Ix.Name
  type : _root_.Ix.Expr
  value : _root_.Ix.Expr
  arity : Nat
  deriving Inhabited

/-- The Rust Pass 3 (`test-ffi`): `image_spec_of_block` on the block given by
its components' classes, then `image_of` per recursor, over the given
constants only. The outer error is the specification's. -/
@[extern "rs_pass3_images"]
opaque rsPass3Images : @& Array _root_.Ix.ConstantInfo →
  @& Array (Array (Array _root_.Ix.Name)) → @& Array _root_.Ix.Name →
  Except String (Array (Except String RsImage))

/-! ## The block's closure -/

/-- A constant of `env`, the nested auxiliary recursors of a raw `addDecl`
included (they are in the kernel environment only, as for `ixLookup`). -/
def lookup (env : Environment) (n : Lean.Name) : Option ConstantInfo :=
  (env.find? n).orElse fun _ => env.toKernelEnv.find? n

/-- The names a constant brings into the closure: what its type mentions,
and an inductive's block, constructors and recursors. -/
def neighbours : ConstantInfo → List Lean.Name
  | .inductInfo iv =>
    -- every member of the block has its own `.rec`; the nested auxiliaries'
    -- `rec_k` are named after the block's head
    let recs : List Lean.Name := iv.all.map (Lean.Name.str · "rec") ++ match iv.all with
      | r :: _ => (List.range iv.numNested).map fun k => Lean.Name.str r s!"rec_{k + 1}"
      | [] => []
    iv.type.getUsedConstants.toList ++ iv.all ++ iv.ctors ++ recs
  | .ctorInfo cv => cv.type.getUsedConstants.toList ++ [cv.induct]
  | .recInfo rv => rv.type.getUsedConstants.toList ++ rv.all ++ rv.rules.map (·.ctor)
  | ci => ci.type.getUsedConstants.toList

partial def closureGo (env : Environment) :
    List Lean.Name → NameSet → Array Lean.Name → Array Lean.Name
  | [], _, out => out
  | n :: todo, seen, out =>
    if seen.contains n then closureGo env todo seen out
    else
      let seen := seen.insert n
      match lookup env n with
      | some ci => closureGo env (neighbours ci ++ todo) seen (out.push n)
      | none => closureGo env todo seen out

/-- `seeds` and everything their `neighbours` reach in `env`. -/
def closure (env : Environment) (seeds : Array Lean.Name) : Array Lean.Name :=
  closureGo env seeds.toList {} #[]

/-! ## Verdicts -/

structure Row where
  case : String
  recName : String
  verdict : String
  msg : String := ""

def namesEq (a b : Array _root_.Ix.Name) : Bool :=
  a.size == b.size && (a.zip b).all fun (x, y) => _root_.Ix.Compile.Image.RawExact.nameEq x y

/-- The verdict on one recursor's Lean and Rust images. -/
def compare (lean : Except String Image) (rust : Except String RsImage) : String × String :=
  match lean, rust with
  | .error a, .error b => ("BOTH-ERR", s!"lean: {a}; rust: {b}")
  | .error a, .ok _ => ("LEAN-ERR", a)
  | .ok _, .error b => ("RUST-ERR", b)
  | .ok l, .ok r =>
    let exact := _root_.Ix.Compile.Image.RawExact.exprEq
    if !namesEq l.levelParams r.levelParams then ("DIFF", "universe parameters")
    else if l.arity != r.arity then ("DIFF", s!"arity {l.arity} vs {r.arity}")
    else if exact l.type r.type && exact l.value r.value then ("SAME", "")
    else if alphaEq l.type r.type && alphaEq l.value r.value then
      ("ALPHA", "binder names or binder info")
    else ("DIFF", if exact l.type r.type then "value" else "type")

/-! ## One case -/

def runCase (c : Case) : CoreM (Array Row) := do
  let some (first, _) := c.hand[0]? | throwError "case without members"
  let all := (← getConstInfoInduct first).all
  -- Pass 1, externals compared by stand-in addresses (as image-gen)
  let cenv : _root_.Ix.Compile.Canon.Env := {
    const? := ixLookup (← getEnv)
    addr? := fun n => some (Address.blake3 n.pretty.toUTF8) }
  let block ← match _root_.Ix.Compile.Canon.canonBlock _root_.Ix.Compile.Canon.Rules.compiler cenv
      (all.toArray.map ixName) with
    | .ok b => pure b
    | .error e => throwError "canonBlock: {e}"
  let spec ← match ImageSpec.ofBlock Naming.default (ixLookup (← getEnv)) block with
    | .ok s => pure s
    | .error e => throwError "ImageSpec.ofBlock: {e}"
  -- the canonical declarations, for their recursors
  for d in spec.decls do
    let types := d.types.toList.map fun ty =>
      { name := toLeanName ty.name, type := toLeanExpr ty.type
        ctors := ty.ctors.toList.map fun k =>
          { name := toLeanName k.name, type := toLeanExpr k.type : Constructor } : InductiveType }
    let decl := Declaration.inductDecl (d.levelParams.toList.map toLeanName) d.numParams types
      d.isUnsafe
    if let some msg ← Tests.Ix.Compile.ImageProto.kernelAdd decl then
      throwError "canonical block {types.map (·.name)}: {msg}"
  let env ← getEnv
  let const? := ixLookup env
  let iv ← match indOf const? (ixName first) with
    | .ok v => pure v
    | .error e => throwError "indOf: {e}"
  let recs := blockRecursors const? iv
  let seeds := all.toArray ++ (spec.canonInds ++ recs ++ imageSupport).map toLeanName
  let consts := (closure env seeds).filterMap fun n => (lookup env n).map toIx
  match rsPass3Images consts (block.components.map (·.classes)) recs with
  | .error e => return #[{ case := c.name, recName := "spec", verdict := "RUST-ERR", msg := e }]
  | .ok rs =>
    unless rs.size == recs.size do
      throwError "rs_pass3_images: {rs.size} results for {recs.size} recursors"
    return (recs.zip rs).map fun (r, ri) =>
      let (verdict, msg) := compare (imageOf {} const? spec r) ri
      { case := c.name, recName := r.pretty, verdict, msg }

/-! ## Part 2: the callers, both compilers -/

/-- The case's constants: those of `Ck.Src` and the aux-gen seeds
(`Ix.CompileM.auxGenSeedNames`), closed under dependencies. -/
def callerClosure (env : Environment) (c : Case) : List (Name × ConstantInfo) :=
  let src := c.ns ++ `Src
  let own := env.constants.toList.filterMap fun (n, _) =>
    if src.isPrefixOf n then some n else none
  let seeds := (_root_.Ix.CompileM.auxGenSeedNames.map toLeanName).toList
  _root_.Ix.EnvScope.collectDeps env (own ++ seeds)

/-- The case's compile input (`callerClosure`). -/
def callerInput (env : Environment) (c : Case) :
    Except String _root_.Ix.Compile.CompileInput :=
  (_root_.Ix.Compile.CompileInput.fromAnnotations (callerClosure env c)).mapError toString

/-- The verdict of one case's callers: `ALIGNED` (byte-identical outputs),
`REFUSED` (both compilers refuse exactly the same constants), else the
difference. -/
inductive CallerVerdict where
  | aligned
  | refused (count : Nat)
  | diverged (why : String)

/-- The Lean pipeline (`workers` workers) and the Rust compiler on one
compile input. The Lean pipeline's Source service gets `support`, the
literal support the input lacks (`Ix.AuxGen.literalSupportFor`), as
`ix compile-lean` gives it: since AuxGen M5c (production `failClosed`) a
block whose generated auxiliaries the service cannot check is refused, and
without the support a `.brecOn` ask about a generated `.below` fails (C2's
callers, push 117). A refused input writes nothing by default (`ix compile` is
fail-closed), so for one the two compilers must refuse the same constants;
their grounded subsets are not compared (they differ before Pass 3 already:
Rust keeps a failed block's stored constants, e.g. on `C4b`). -/
def inputParity (input : _root_.Ix.Compile.CompileInput)
    (support : List (Name × ConstantInfo) := []) (workers : Nat := 1) : IO CallerVerdict := do
  let opts : _root_.Ix.CompileM.DriverOptions := { serviceSupport := support }
  let lean ← match ← _root_.Ix.CompileM.compileLeanInput input (numWorkers := workers) (opts := opts) with
    | .ok out => pure out
    | .error e => return .diverged s!"lean pipeline: {e}"
  let constants ← match input.prepare with
    | .ok cs => pure cs
    | .error e => return .diverged s!"prepare: {e}"
  let dir ← IO.FS.createTempDir
  let path := dir / "rust.ixe"
  let status ← _root_.Ix.CompileM.rsCompileEnvBytesFFI constants path.toString true
  let rustBytes ← IO.FS.readBinFile path
  IO.FS.removeDirAll dir
  let leanRefused := (lean.cenv.ungrounded.toArray.map (·.1.pretty)).qsort (· < ·)
  let rustRefused := (status.ungrounded.map (·.1)).qsort (· < ·)
  if !leanRefused.isEmpty || !rustRefused.isEmpty then
    if leanRefused == rustRefused then return .refused leanRefused.size
    let leanOnly := leanRefused.filter (!rustRefused.contains ·)
    let rustOnly := rustRefused.filter (!leanRefused.contains ·)
    return .diverged s!"refusals differ: lean {leanRefused.size}, rust {rustRefused.size}; \
lean only {leanOnly.toList.take 5}, rust only {rustOnly.toList.take 5}"
  if rustBytes == lean.bytes then return .aligned
  let differing : Array String := match _root_.Ixon.rsDeEnv rustBytes with
    | .error e => #[s!"(the Rust output does not decode: {e})"]
    | .ok rust => (lean.env.named.toArray.filterMap fun (n, l) =>
        match rust.named.get? n with
        | some r => if r == l then none else some n.pretty
        | none => some s!"{n.pretty} (not in the Rust output)").qsort (· < ·)
  return .diverged s!"bytes differ: lean {lean.bytes.size} B, rust {rustBytes.size} B; named \
entries that differ: {differing.toList.take 5}"

/-- The Lean pipeline (one worker) and the Rust compiler on one case's
callers (`inputParity`). -/
def callerParity (env : Environment) (c : Case) : IO CallerVerdict := do
  match callerInput env c with
  | .ok input => inputParity input (_root_.Ix.AuxGen.literalSupportFor env (callerClosure env c))
  | .error e => return .diverged s!"input: {e}"

/-! ## Part 3: the clique-ownership units, both compilers

The `co-*` units (CQ5.2 (b), from the donor's `pass3-rust-parity`): each
clique-ownership case (`Tests.Ix.Compile.Clique.Ownership.cases`, without an
alteration, once per name) compiled whole, as a unit: its members' closure
with the rows' prerequisites (`Twins.rowPrereqNames`, so a well-founded clique
can be transported and its rows emitted), and for `WF8` its caller and
neighbour (the caller refused by name on both sides when the clique is
transported). Both compilers must give the same bytes (`ALIGNED`), or refuse
the same constants (`REFUSED`). -/

/-- The `co-*` units: label, compile input and the literal support the input
lacks (`inputParity`). -/
def ownershipUnits (env : Environment) :
    Array (String × Except String _root_.Ix.Compile.CompileInput × List (Name × ConstantInfo)) :=
    Id.run do
  let eqn := Tests.Ix.Compile.Clique.Transport.eqnCliques env
  let prereqs := Tests.Ix.Compile.Twins.rowPrereqNames env
  let mut seen : Std.HashSet String := {}
  let mut out := #[]
  for c in Tests.Ix.Compile.Clique.Ownership.cases do
    if c.alter.isSome || seen.contains c.name then continue
    seen := seen.insert c.name
    let ns := Tests.Ix.Compile.Clique.Ownership.srcNs ++ c.name.toName
    let label := s!"co-{c.name}"
    let some (_, ms) := eqn.get? (ns ++ `first) | out := out.push (label, .error "no clique recorded", []); continue
    let extra := if c.name.startsWith "WF8" then #[ns ++ `caller, ns ++ `neighbour] else #[]
    let closure := Tests.Ix.Compile.Harness.closureOf env ((ms ++ extra).toList ++ prereqs)
    out := out.push (label, (_root_.Ix.Compile.compileInputFromEnv env closure).mapError toString,
      _root_.Ix.AuxGen.literalSupportFor env closure)
  return out

/-! ## The suite -/

def run : IO UInt32 := do
  let mut rows : Array Row := #[]
  let mut failures : Array String := #[]
  let mut aligned := 0
  let mut refusedAlike := 0
  let mut callerCases := 0
  for (path, cases) in files do
    try
      let env ← getFileEnv path
      -- part 2 on the file's own environment (part 1 grows a copy)
      for c in cases.filter (·.ablationOf.isNone) do
        callerCases := callerCases + 1
        match ← callerParity env c with
        | .aligned => aligned := aligned + 1
        | .refused _ => refusedAlike := refusedAlike + 1
        | .diverged why => failures := failures.push s!"{c.name} callers: DIVERGED: {why}"
      let ctx : Core.Context := { fileName := path, fileMap := default, maxHeartbeats := 0 }
      let (rs, _) ← (do
          let mut acc : Array Row := #[]
          for c in cases.filter (·.ablationOf.isNone) do
            try acc := acc ++ (← runCase c)
            catch e =>
              let msg ← e.toMessageData.toString
              acc := acc.push { case := c.name, recName := "case", verdict := "ERROR", msg }
          return acc
        : CoreM (Array Row)).toIO ctx { env }
      rows := rows ++ rs
    catch e => failures := failures.push s!"{path}: {e}"
  let count := fun (v : String) => (rows.filter (·.verdict == v)).size
  IO.println s!"[pass3-rust-parity] images {rows.size}: SAME {count "SAME"}, ALPHA \
    {count "ALPHA"}, DIFF {count "DIFF"}, LEAN-ERR {count "LEAN-ERR"}, RUST-ERR \
    {count "RUST-ERR"}, BOTH-ERR {count "BOTH-ERR"}, ERROR {count "ERROR"}"
  for r in rows do
    if r.verdict != "SAME" then
      failures := failures.push s!"{r.case} {r.recName}: {r.verdict} {(r.msg.take 400).toString}"
  unless rows.size == 38 do
    failures := failures.push s!"{rows.size} images, want image-gen's 38"
  IO.println s!"[pass3-rust-parity] callers: {callerCases} cases, {aligned} ALIGNED, \
{refusedAlike} REFUSED alike"
  -- part 3: the clique-ownership units (`co-*`)
  let mut unitsAligned := 0
  let mut unitsRefused := 0
  let units := ownershipUnits (← Tests.Ix.Compile.Twins.fixturesEnv)
  for (label, input?, support) in units do
    match input? with
    | .error e => failures := failures.push s!"{label}: input: {e}"
    | .ok input =>
      try
        match ← inputParity input support (workers := 8) with
        | .aligned => unitsAligned := unitsAligned + 1
        | .refused _ => unitsRefused := unitsRefused + 1
        | .diverged why => failures := failures.push s!"{label}: DIVERGED: {why}"
      catch e => failures := failures.push s!"{label}: {e}"
  IO.println s!"[pass3-rust-parity] clique-ownership units: {units.size}, {unitsAligned} ALIGNED, \
{unitsRefused} REFUSED alike"
  for f in failures do IO.println s!"[pass3-rust-parity] FAIL {f}"
  IO.println s!"[pass3-rust-parity] {failures.size} failures"
  return if failures.isEmpty then 0 else 1

end Tests.Ix.Compile.Pass3RustParity
