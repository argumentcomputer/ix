/-
  pass3-rust-parity: the Rust Pass 3 core against the Lean one, on the images.

  The Rust core (`crates/compile/src/compile/pass3`) is not called by the
  compiler yet; this suite holds it to `Ix.Compile.Image` on what it computes,
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
  run). The run passes iff every image is `SAME` and there are image-gen's 38.

  Invoked as `lake test -- pass3-rust-parity` (tier `ci:compile-pipeline`).
-/
import Lean
import Ix.Compile.Canon
import Ix.Compile.Image
import Ix.Meta
import Tests.Ix.Compile.Image
import Tests.Ix.Compile.ImageProto

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

/-! ## The suite -/

def run : IO UInt32 := do
  let mut rows : Array Row := #[]
  let mut failures : Array String := #[]
  for (path, cases) in files do
    try
      let env ← getFileEnv path
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
  for f in failures do IO.println s!"[pass3-rust-parity] FAIL {f}"
  IO.println s!"[pass3-rust-parity] {failures.size} failures"
  return if failures.isEmpty then 0 else 1

end Tests.Ix.Compile.Pass3RustParity
