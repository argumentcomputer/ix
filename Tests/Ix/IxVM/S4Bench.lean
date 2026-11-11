import Std
import Lean
import Ix.Meta
import Ix.KernelFidelity.Reader
import Ix.LeanIngress
import Ix.SemanticContract
import Tests.Ix.IxVM.Harness
import Tests.Ix.IxVMFixtures
import Tests.Ix.Kernel.SourceIngressStep

/-! # IxVM inductive-declaration measurements (manual tier, not a gate)

Measurements behind the choice of how IxVM checks inductive declarations: the
costs of checking inductive declarations in the deployed IxVM program, a
sizeable `Std` shard for the performance baseline, and a census of the
environment's mutual and nested inductive blocks with the certified kernel's
in-process modeller (`IxC/Kernel/Frontend/InModel`) run on chosen blocks.

* `ixvm-s4-bench` runs claims through `ixvm-proof test` with statistics and
  prints `FFT <label>: <cost> (expected none)` lines in the harness's format.
  It needs `IX_TEST_OUTPUT_DIR`, keeps every case file and sidecar there
  (`s4/`), and sets `IXVM_FUNCTION_STATS` so the host also writes per-function
  rows (`<sidecar>.functions.json`).
* `ixvm-s4-census` lists the inductive blocks of the test binary's
  environment by kind and module root, and runs the Source-mode ingress
  (`Ix.LeanIngress.leanIngress`, which calls the modeller for every mutual or
  nested block) on the closures of the chosen blocks, printing each generated
  record with its size. -/

namespace Tests.Ix.IxVM.S4Bench

open IxVM.ClaimHarness Tests.Ix.IxVM

private def nameOfString (str : String) : Lean.Name :=
  str.splitOn "." |>.foldl (init := .anonymous) fun acc s =>
    match s.toNat? with
    | some n => .mkNum acc n
    | none => .mkStr acc s

/-! ## Running claims with statistics -/

/-- One case per file, `jobs` host processes at a time. Every case runs; the
result is 0 when every case was built and got its verdict. -/
def runStats (suite : String) (cases : Array (Unit → Except String Case)) (jobs : Nat := 4) :
    IO UInt32 := do
  let artifact ← programArtifact
  let host ← programHost
  let some out ← IO.getEnv "IX_TEST_OUTPUT_DIR"
    | throw (IO.userError s!"[{suite}] set IX_TEST_OUTPUT_DIR")
  let dir := System.FilePath.mk out / "s4"
  IO.FS.createDirAll dir
  let mut tasks : Array (String × System.FilePath × Task (Except IO.Error IO.Process.Output)) := #[]
  let mut failed := 0
  let mut i := 0
  for build in cases do
    match build () with
    | .error e =>
      IO.eprintln s!"[{suite}] a case could not be built: {e}"
      failed := failed + 1
    | .ok c =>
      -- the binder data, and with `$IX_PW_CHECK` their host-side check
      let c ← IO.ofExcept c.withPwHints
      if let some mode ← IO.getEnv "IX_PW_CHECK" then
        if let some e ← pwCheckCase suite c then
          IO.eprintln s!"[{suite}] {e}"
          failed := failed + 1
        if mode == "only" then continue
      let path := dir / s!"{suite}-{i}.ixt"
      i := i + 1
      IO.FS.writeBinFile path (Ix.AiurInvocation.casesHeader ++ c.encode ++ Ix.AiurInvocation.casesTrailer)
      if tasks.size ≥ jobs then
        let _ ← IO.wait tasks[tasks.size - jobs]!.2.2
      let task ← IO.asTask (prio := .dedicated) (IO.Process.output {
        cmd := host
        args := #["test", artifact, path.toString, "--stats-out", (path.withExtension "stats.json").toString]
        env := #[("IXVM_FUNCTION_STATS", some "1")] })
      IO.println s!"[{suite}] {c.label}: {c.size} stream elements, {path}"
      tasks := tasks.push (c.label, path, task)
  for (label, path, task) in tasks do
    let r ← IO.wait task
    match r with
    | .error e =>
      IO.eprintln s!"[{suite}] {label}: host failed to run: {e}"
      failed := failed + 1
    | .ok o =>
      IO.print o.stdout
      unless o.exitCode == 0 do
        IO.eprintln s!"[{suite}] {label}: {o.stderr.trimAscii}"
        failed := failed + 1
      try
        let raw ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (path.withExtension "stats.json")))
        let m ← IO.ofExcept (raw.getObjVal? label >>= Aiur.ExecutionMeasurements.fromJson)
        let stats := Aiur.computeStats m
        let rows := stats.circuits.foldl (· + ·.height) 0
        IO.println s!"FFT {label}: {stats.roundedFftCost} (expected none)"
        IO.println s!"ROWS {label}: {rows}"
      catch e =>
        IO.eprintln s!"[{suite}] {label}: no statistics: {e}"
  IO.println s!"[{suite}] {i} cases, {failed} failures"
  return if failed == 0 then 0 else 1

/-! ## The cases -/

/-- The string components of an Ixon name, outermost first. -/
private def ixComps (n : Ix.Name) : List String :=
  (Ix.SemanticContract.toLeanName n).components.map toString

/-- Shard group of a constant: projections group with their block. -/
private def groupOf (a : Address) (ci : Ixon.ConstantInfo) : Address :=
  match ci with
  | .iPrj p | .cPrj p | .rPrj p | .dPrj p => p.block
  | _ => a

/-- Every constant of `env` in the shard groups of `names`: the inductive
blocks and recursor blocks the names live in, with their projections. -/
def declOwned (env : Ixon.Env) (names : List Lean.Name) : Except String (Array Address) := do
  let mut keys : Std.HashSet Address := {}
  for n in names do
    let some a := env.getAddr? (Ix.Name.fromLeanName n) | throw s!"{n} is not in the Ixon environment"
    let some c := env.getConst? a | throw s!"{n} has no constant"
    keys := keys.insert (groupOf a c.info)
  let mut owned : Array Address := #[]
  for (a, lc) in env.consts do
    if let some c := lc.get? then
      if keys.contains (groupOf a c.info) then owned := owned.push a
  return owned

/-- A recursor's name: last component `rec` or `rec_<k>`. -/
def isRecName : Lean.Name → Bool
  | .str _ s => s == "rec" || s.startsWith "rec_"
  | _ => false

/-- The inductive blocks measured, by kind: a label, the constants whose shard
groups make up the declarations, and the recursor whose whole closure a
`check` claim walks. -/
def targets : List (String × List String × String) := [
  ("floor id", ["id"], "id"),
  ("plain Option", ["Option", "Option.rec"], "Option.rec"),
  ("plain List", ["List", "List.rec"], "List.rec"),
  ("mutual IxVMInd.Even", ["IxVMInd.Even", "IxVMInd.Even.rec", "IxVMInd.Odd.rec"], "IxVMInd.Even.rec"),
  ("mutual Lean.Meta.Grind.Arith.Linear.RingIneqCnstr",
    ["Lean.Meta.Grind.Arith.Linear.RingIneqCnstr", "Lean.Meta.Grind.Arith.Linear.RingIneqCnstr.rec",
     "Lean.Meta.Grind.Arith.Linear.RingIneqCnstrProof.rec"],
    "Lean.Meta.Grind.Arith.Linear.RingIneqCnstrProof.rec"),
  ("nested IxVMInd.Tree", ["IxVMInd.Tree", "IxVMInd.Tree.rec", "IxVMInd.Tree.rec_1"], "IxVMInd.Tree.rec"),
  ("nested Lean.Syntax", ["Lean.Syntax", "Lean.Syntax.rec", "Lean.Syntax.rec_1", "Lean.Syntax.rec_2"],
    "Lean.Syntax.rec")]

/-- A `Std` shard: the constants of `base`'s closure whose name begins with
`pre`, by shard group, checked with the frontier assumed, validating the
binding (as the `ixvm-kernel-checks` shard case does). -/
def stdShard (env : Lean.Environment) (base : Lean.Name) (pre : List String) :
    IO (Unit → Except String Case) := do
  unless env.constants.contains base do
    throw (IO.userError s!"{base} is not in the environment")
  let ixonEnv ← loadIxonEnv base env
  let mut groups : Std.HashMap Address (Array Address) := {}
  let mut ownedGroups : Std.HashSet Address := {}
  for (a, lc) in ixonEnv.consts do
    if let some c := lc.get? then
      let k := groupOf a c.info
      groups := groups.insert k ((groups.getD k #[]).push a)
      if let some n := ixonEnv.addrToName[a]? then
        if pre.isPrefixOf (ixComps n) then
          ownedGroups := ownedGroups.insert k
  let mut owned : Array Address := #[]
  for k in ownedGroups.toArray do owned := owned ++ groups.getD k #[]
  IO.println s!"[ixvm-s4-bench] Std shard {".".intercalate pre} of {base}: {owned.size} owned of \
    {ixonEnv.consts.size} in the closure"
  return fun _ => do
    if owned.isEmpty then throw s!"the Std shard {pre} selected nothing"
    let (_, witness) ← buildShardCheckEnvWitness ixonEnv owned
    return { label := s!"s4 std shard {".".intercalate pre} of {base} ({owned.size} owned)",
             accept := true, witness, env := ixonEnv }

/-- A module shard: every constant declared in a module whose name begins
with `pre` (and, when `only` is given, whose own name begins with it too),
grouped by shard group, checked with the frontier assumed and the binding
validated. The production pipeline's shards are of this size (hundreds to
thousands of owned constants). -/
def moduleShard (env : Lean.Environment) (pre : Lean.Name) : IO (Unit → Except String Case) := do
  let mut names : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if let some i := env.getModuleIdxFor? n then
      if pre.isPrefixOf env.header.moduleNames[i.toNat]! then names := names.push n
  let sorted := names.qsort Lean.Name.lt
  let ixonEnv ← loadSharedIxonEnv sorted env
  let mut keys : Std.HashSet Address := {}
  for n in sorted do
    if let some a := ixonEnv.getAddr? (Ix.Name.fromLeanName n) then
      if let some c := ixonEnv.getConst? a then keys := keys.insert (groupOf a c.info)
  let mut owned : Array Address := #[]
  for (a, lc) in ixonEnv.consts do
    if let some c := lc.get? then
      if keys.contains (groupOf a c.info) then owned := owned.push a
  IO.println s!"[ixvm-s4-bench] module shard {pre}: {sorted.size} declarations, {owned.size} owned of \
    {ixonEnv.consts.size} in the closure"
  return fun _ => do
    if owned.isEmpty then throw s!"the module shard {pre} selected nothing"
    let (_, witness) ← buildShardCheckEnvWitness ixonEnv owned
    return { label := s!"s4 std module shard {pre} ({owned.size} owned)", accept := true, witness,
             env := ixonEnv }

def bench (env : Lean.Environment) : IO UInt32 := do
  let present := targets.filter fun (label, ns, r) =>
    let missing := (r :: ns).map nameOfString |>.filter (!env.constants.contains ·)
    if missing.isEmpty then true else
      dbgTrace s!"[ixvm-s4-bench] skipped {label}: not in the environment: {missing}" fun _ => false
  let names := present.flatMap (fun (_, ns, r) => r :: ns) |>.map nameOfString
  let ixonEnv ← loadSharedIxonEnv names.toArray env
  let mut cases : Array (Unit → Except String Case) := #[]
  for (label, ns, r) in present do
    let ns := ns.map nameOfString
    cases := cases.push fun _ => do
      let owned ← declOwned ixonEnv ns
      let (_, witness) ← buildShardCheckEnvWitness ixonEnv owned (assumeBinding := true)
      return { label := s!"s4 decl {label} ({owned.size} owned)", accept := true, witness,
               env := ixonEnv }
    -- the same declarations split: the inductive block alone, then the
    -- recursor block alone (the other assumed)
    let (recs, inds) := ns.partition isRecName
    unless recs.isEmpty || inds.isEmpty do
      for (part, sel) in [("ind", inds), ("rec", recs)] do
        cases := cases.push fun _ => do
          let owned ← declOwned ixonEnv sel
          let (_, witness) ← buildShardCheckEnvWitness ixonEnv owned (assumeBinding := true)
          return { label := s!"s4 decl-{part} {label} ({owned.size} owned)", accept := true, witness,
                   env := ixonEnv }
    cases := cases.push fun _ => do
      let some target := ixonEnv.getAddr? (Ix.Name.fromLeanName (nameOfString r))
        | throw s!"{r} is not in the Ixon environment"
      let ctx ← Ix.ClaimContext.ofEnv ixonEnv true
      Case.ofClaim s!"s4 check {r} (closure)" ixonEnv (.check ctx target none)
  let base := nameOfString "Std.HashMap.getElem?_insert_self"
  for pre in [["Std", "DHashMap", "Internal", "AssocList"], ["Std"]] do
    try cases := cases.push (← stdShard env base pre)
    catch e => IO.eprintln s!"[ixvm-s4-bench] Std shard {pre}: {e}"
  for pre in [`Std.Data.HashMap, `Std.Data.DHashMap] do
    try cases := cases.push (← moduleShard env pre)
    catch e => IO.eprintln s!"[ixvm-s4-bench] module shard {pre}: {e}"
  runStats "ixvm-s4-bench" cases

/-! ## The census -/

/-- The top-level component of the module that declares `n`. -/
def moduleOf (env : Lean.Environment) (n : Lean.Name) : Lean.Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => .anonymous

def kindOf (v : Lean.InductiveVal) : String :=
  if v.all.length > 1 && v.numNested > 0 then "mutual+nested"
  else if v.all.length > 1 then "mutual"
  else if v.numNested > 0 then "nested"
  else "plain"

/-- Tree size of a kernel expression, capped. -/
partial def exprSize : Ix.Kernel.Expr md → Nat
  | .app f a => 1 + exprSize f + exprSize a
  | .lam t b _ | .forallE t b _ => 1 + exprSize t + exprSize b
  | .letE t v b _ => 1 + exprSize t + exprSize v + exprSize b
  | .proj _ _ e => 1 + exprSize e
  | .fvar _ t => 1 + exprSize t
  | _ => 1

def declLine : Ix.Kernel.Declaration .source → String
  | .axiomDecl cv => s!"axiom {cv.name} ty={exprSize cv.type}"
  | .defnDecl cv v _ => s!"defn {cv.name} ty={exprSize cv.type} val={exprSize v}"
  | .thmDecl cv v => s!"thm {cv.name} ty={exprSize cv.type} val={exprSize v}"
  | .opaqueDecl cv v => s!"opaque {cv.name} ty={exprSize cv.type} val={exprSize v}"
  | .basisDecl _ => "basis"
  | .indDecl block nP =>
    let tys := block.filterMap fun ci => match ci with
      | .indInfo cv _ => some s!"{cv.name}" | _ => none
    let ctors := block.filter fun ci => match ci with | .ctorInfo .. => true | _ => false
    let recs := block.filter fun ci => match ci with | .recInfo .. => true | _ => false
    let size := block.foldl (fun n ci => n + exprSize ci.toConstantVal.type +
      match ci with | .recInfo _ _ _ rs => rs.foldl (· + exprSize ·.rhs) 0 | _ => 0) 0
    s!"ind {tys} params={nP} ctors={ctors.length} recs={recs.length} size={size}"
  | .quotDecl _ cv => s!"quot {cv.name}"

def modelled : List String := ["Option", "List", "IxVMInd.Even", "IxVMInd.Tree", "Lean.Syntax",
  "Lean.Meta.Grind.Arith.Linear.RingIneqCnstr"]

/-- Is `d` an inductive declaration that declares `seed`? -/
def declaresInductive (seed : Lean.Name) (d : Ix.Kernel.Declaration .source) : Bool :=
  match d with
  | .indDecl .. => d.names.any (Ix.RoleEvidence.toLeanName · == seed)
  | _ => false

/-- The Source-mode declarations of the block of `seed` (the modeller's
generated records followed by the block's own `indDecl`), from the ingress of
its closure: the block's `InductiveVal`, the closure's size, the number of
declarations, and the block's. -/
def blockDecls (env : Lean.Environment) (seed : Lean.Name) :
    IO (Lean.InductiveVal × Nat × Nat × Array (Ix.Kernel.Declaration .source)) := do
  let some (.inductInfo v) := env.find? seed | throw (IO.userError s!"{seed} is not an inductive")
  let closed ← IO.ofExcept (Tests.Ix.Kernel.ReaderFidelity.closure env (v.all.toArray.push seed))
  let ienv := Tests.Ix.Kernel.SourceIngressStep.canon closed.toArray 8
  let blocks := Tests.Ix.Kernel.SourceIngressStep.condense ienv true
  let decls ← match Ix.LeanIngress.leanIngress ienv blocks with
    | .ok ds => pure ds
    | .error e => throw (IO.userError s!"ingress: {e}")
  -- the block's own declaration names its types, constructors and recursors;
  -- the modeller's records are keyed by derivations of those names (a
  -- recursor's `R._model` and `R._model.iota_j`, a constructor's `C._model`)
  let some blockDecl := decls.find? (declaresInductive seed)
    | throw (IO.userError s!"{seed}: no inductive declaration in the ingress")
  let blockNames := blockDecl.names.map Ix.RoleEvidence.toLeanName
  let ours := decls.filter fun d => d.names.any fun k =>
    blockNames.contains (Ix.RoleEvidence.toLeanName k.base)
  return (v, closed.length, decls.size, ours)

def census (env : Lean.Environment) : IO UInt32 := do
  let mut counts : Std.HashMap (String × String) Nat := {}
  let mut lines : Array String := #[]
  for (n, ci) in env.constants.toList do
    if let .inductInfo v := ci then
      if v.all.head? == some n then
        let root := (moduleOf env n).getRoot.toString
        let k := kindOf v
        counts := counts.insert (root, k) (counts.getD (root, k) 0 + 1)
        if k != "plain" then
          let nctors := v.all.foldl (fun acc t => match env.find? t with
            | some (.inductInfo w) => acc + w.ctors.length | _ => acc) 0
          lines := lines.push s!"BLOCK {k} {root} {n} module={moduleOf env n} types={v.all.length} \
            nested={v.numNested} ctors={nctors} indices={v.numIndices} params={v.numParams} \
            rec={v.isRec} reflexive={v.isReflexive} unsafe={v.isUnsafe}"
  for ((root, k), c) in counts.toList.toArray.qsort (fun a b => toString a.1 < toString b.1) do
    IO.println s!"COUNT {root} {k} {c}"
  for l in lines.qsort (· < ·) do IO.println l
  -- the modeller's records for the chosen blocks, through the Source-mode ingress
  let mut failed := 0
  for t in modelled do
    try
      let (v, closure, total, ours) ← blockDecls env (nameOfString t)
      IO.println s!"MODEL {t}: {closure} constants in the closure, {total} declarations, \
        {ours.size} for the block ({v.all.length} types)"
      for d in ours do IO.println s!"MODEL {t}: {declLine d}"
    catch e =>
      failed := failed + 1
      IO.eprintln s!"[ixvm-s4-census] {t}: {e}"
  return if failed == 0 then 0 else 1

/-! ## Prototype: IxVM checks the modeller's records

The records the in-process modeller generates for a block (Source mode, keys
are Lean names) are converted to Lean declarations, added through Lean's
kernel (`Environment.addDeclCore`, which also generates the tag's and the
auxiliary family's recursors), compiled to Ixon by the certified compiler,
and checked by the deployed IxVM program as one shard that owns them all,
with everything else assumed. That is the cost IxVM pays per block when it checks
the modeller's records instead of checking the block natively; the modeled
install's own pins (`Inductives/Modeled.lean`)
are not part of it. -/

/-- A Source-mode level parameter's Lean name. -/
def lpName (i : Nat) : Lean.Name := .mkSimple s!"u_{i}"

def convLevel : Ix.Kernel.Level → Lean.Level
  | .zero => .zero
  | .succ u => .succ (convLevel u)
  | .max u v => .max (convLevel u) (convLevel v)
  | .imax u v => .imax (convLevel u) (convLevel v)
  | .param i => .param (lpName i)

partial def convExpr : Ix.Kernel.Expr .source → Except String Lean.Expr
  | .bvar i => pure (.bvar i)
  | .fvar .. => throw "free variable in a generated record"
  | .sort u => pure (.sort (convLevel u))
  | .const k us => pure (.const (Ix.RoleEvidence.toLeanName k) (us.map convLevel))
  | .app f a => return .app (← convExpr f) (← convExpr a)
  | .lam t b _ => return .lam `x (← convExpr t) (← convExpr b) .default
  | .forallE t b _ => return .forallE `x (← convExpr t) (← convExpr b) .default
  | .letE t v b _ => return .letE `x (← convExpr t) (← convExpr v) (← convExpr b) false
  | .lit (.natVal n) => pure (.lit (.natVal n))
  | .lit (.strVal s) => pure (.lit (.strVal s))
  | .proj s i e => return .proj (Ix.RoleEvidence.toLeanName s) i (← convExpr e)

def convHint : Ix.Kernel.ReducibilityHint → Lean.ReducibilityHints
  | .opaque => .opaque
  | .abbrev => .abbrev
  | .regular h => .regular h.toUInt32

/-- A generated record as a Lean declaration. An inductive record is given to
Lean as its types and constructors; Lean's kernel generates its recursor. -/
def convDecl : Ix.Kernel.Declaration .source → Except String Lean.Declaration
  | .defnDecl cv v h => do
    let n := Ix.RoleEvidence.toLeanName cv.name
    let ty ← convExpr cv.type
    let val ← convExpr v
    let dv : Lean.DefinitionVal := {
      name := n, levelParams := cv.levelParams.map lpName, type := ty, value := val,
      hints := convHint h, safety := .safe, all := [n] }
    return .defnDecl dv
  | .thmDecl cv v => do
    let n := Ix.RoleEvidence.toLeanName cv.name
    let ty ← convExpr cv.type
    let val ← convExpr v
    let tv : Lean.TheoremVal := {
      name := n, levelParams := cv.levelParams.map lpName, type := ty, value := val, all := [n] }
    return .thmDecl tv
  | .indDecl block nP => do
    let tys := block.filterMap fun ci => match ci with | .indInfo cv _ => some cv | _ => none
    let cvs := block.filterMap fun ci => match ci with | .ctorInfo cv _ _ => some cv | _ => none
    let [t] := tys | throw s!"generated block with {tys.length} types"
    let mut ctors : List Lean.Constructor := []
    for c in cvs do
      let cty ← convExpr c.type
      ctors := ctors ++ [{ name := Ix.RoleEvidence.toLeanName c.name, type := cty }]
    let tty ← convExpr t.type
    let it : Lean.InductiveType := { name := Ix.RoleEvidence.toLeanName t.name, type := tty, ctors := ctors }
    return .inductDecl (t.levelParams.map lpName) nP [it] false
  | _ => throw "unexpected generated record kind"

def isAuxKey : Ix.Kernel.Key .source → Bool
  | .aux .. => true
  | _ => false

/-- The Lean names a converted declaration adds, recursors included. -/
def addedNames : Lean.Declaration → List Lean.Name
  | .defnDecl v => [v.name]
  | .thmDecl v => [v.name]
  | .inductDecl _ _ tys _ => tys.flatMap fun t => t.name :: (t.name ++ `rec) :: t.ctors.map (·.name)
  | _ => []

def modelTargets : List String := ["IxVMInd.Even", "Lean.Meta.Grind.Arith.Linear.RingIneqCnstr",
  "IxVMInd.Tree", "Lean.Syntax"]

def modelProbe (env : Lean.Environment) : IO UInt32 := do
  let mut lenv := env
  let mut groups : Array (String × List Lean.Name) := #[]
  let mut failed := 0
  for t in modelTargets do
    try
      let (_, _, _, ours) ← blockDecls env (nameOfString t)
      let gen := ours.filter fun d => d.names.all isAuxKey
      let mut names : List Lean.Name := []
      let mut e := lenv
      for d in gen do
        let ld ← IO.ofExcept ((convDecl d).mapError fun s => s!"{declLine d}: {s}")
        match e.addDeclCore 0 4096 ld none with
        | .ok e' =>
          e := e'
          names := names ++ addedNames ld
        | .error ex =>
          throw (IO.userError s!"Lean's kernel refused {declLine d}: {← (ex.toMessageData {}).toString}")
      lenv := e
      IO.println s!"MODELCHECK {t}: Lean's kernel accepted {gen.size} generated records ({names.length} constants)"
      groups := groups.push (t, names)
    catch ex =>
      failed := failed + 1
      IO.eprintln s!"[ixvm-s4-model] {t}: {ex}"
  if groups.isEmpty then return 1
  let all := groups.toList.flatMap (·.2)
  let ixonEnv ← loadSharedIxonEnv all.toArray lenv
  let mut cases : Array (Unit → Except String Case) := #[]
  for (t, names) in groups do
    cases := cases.push fun _ => do
      let owned ← declOwned ixonEnv names
      let (_, witness) ← buildShardCheckEnvWitness ixonEnv owned (assumeBinding := true)
      return { label := s!"s4 model {t} ({owned.size} owned)", accept := true, witness }
  let rc ← runStats "ixvm-s4-model" cases
  return if failed == 0 then rc else 1

end Tests.Ix.IxVM.S4Bench
