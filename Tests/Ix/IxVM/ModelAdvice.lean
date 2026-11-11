module

public import Ix.Meta
public import Ix.IxVM.Model
public import Tests.Ix.IxVM.Harness
public import Tests.Ix.IxVMFixtures

/-! # Model advice for the modeled route

IxVM checks a mutual or nested inductive block against a model the prover
supplies (`IxVM/IxVM/Source/KernelModeled.lean`, `Ix/IxVM/Model.lean`). The
model is witness data. Two properties are tested here:

* **The claim does not change** (`ixvm-model-advice`, first part): for an
  environment with mutual and nested blocks, the claim, its digest, its context
  and the public input of its witness are the same whether or not the models are
  attached, and `consts` is untouched.
* **A different valid model is accepted** (second part): the modeller's records
  with every `iota_j` proof rewritten (`let _ : Nat := 0; p`), so that every
  theorem record, and with it the advice set, has another address. The circuit
  must accept the same claims with it.
* **No advice under user axioms** (third part): a claim whose axioms tree is
  not empty gets no model advice ("model advice: a claim with user axioms").
  The environments above declare Lean's compiler-trust axioms, which the
  default table binds as inert roles, so their claims name no user axiom and
  are accepted.
* **Verdicts at nested blocks the modeller models** (`nestedVerdicts`: an index
  domain that mentions a parameter, a reflexive field into a member): ι
  reductions through their recursors are accepted, and false ι and constructor
  equations, installed in Lean unchecked, are refused.

The must-reject cases for advice (wrong member models, wrong iota statements,
axioms, self-reference, another block's payload, missing payloads, oversized
counts) are fixtures of the local-only branch `jcb/ixvmc-dc-mustreject`.

`ixvm-model-report` (manual) prints, for an `.ixe` file (`IX_MODEL_IXE`), what
the modeller and the encoder produce per mutual or nested block: the advice's
record count and its outside references by witness kind, or why the block has
no model.
-/

public section

namespace Tests.Ix.IxVM.ModelAdvice

open IxVM.ClaimHarness

/-- Mutual (`Even`/`Odd`, `SoloA`/`SoloB`) and nested (`Tree`, `DedupM`,
`AuxTie`) fixtures, types and recursors. -/
def modeledNames : List String := [
  "IxVMInd.Even", "IxVMInd.Odd", "IxVMInd.Even.rec", "IxVMInd.Odd.rec",
  "IxVMInd.SoloA.rec", "IxVMInd.Tree", "IxVMInd.Tree.rec", "IxVMInd.Tree.rec_1",
  "IxVMInd.DedupM", "IxVMInd.DedupM.rec", "IxVMInd.AuxTie.rec"]

/-- Claims on nested blocks the modeller models, with the verdict the circuit
must give: `Tests.Ix.Kernel.EntryCaseDefs.NB4` (an index domain that mentions
a parameter), `RA1` and `RA3` (a reflexive field into a member), `BD1` and `BD2`
(a member behind a definition) and `EA` (a member only where whnf erases it). For
each, ι
reductions through the recursors are accepted, and false ι or constructor
equations installed in Lean unchecked are refused (`bad_thm` declares their
names at the root). -/
def nestedVerdicts : List (Lean.Name × Bool) := [
  (`Tests.Ix.Kernel.EntryCaseDefs.nb4Iota, true),
  (`nb4IotaFalse, false),
  (`nb4CtorFalse, false),
  (`Tests.Ix.Kernel.EntryCaseDefs.ra1Iota, true),
  (`ra1IotaFalse, false),
  (`Tests.Ix.Kernel.EntryCaseDefs.ra3Iota, true),
  (`ra3IotaFalse, false),
  (`ra3CtorFalse, false),
  (`bd1Iota, true),
  (`bd1IotaFalse, false),
  (`bd2Iota, true),
  (`bd2CtorFalse, false),
  (`Tests.Ix.Kernel.EntryCaseDefs.eaIota, true),
  (`eaIotaFalse, false)]

private def nameOfString (str : String) : Lean.Name :=
  str.splitOn "." |>.foldl (init := .anonymous) fun acc s =>
    match s.toNat? with
    | some n => .mkNum acc n
    | none => .mkStr acc s

/-- The environment a claim builder sees without the models. -/
def withoutModels (env : Ixon.Env) : Ixon.Env :=
  { env with models := {}, modelRecords := {}, modelHints := {}, modelBlobs := {},
             modelDeps := {}, modelsAttached := true }

/-- The claims over `env` and over `env` without its models agree, byte for byte. -/
def digestUnchanged (env : Ixon.Env) (names : List Lean.Name) : IO Bool := do
  let bare := withoutModels env
  let mut ok := true
  let payloads := (env.models.toList.filter fun (_, p) => p.size > 0).length
  if payloads < 2 then
    IO.eprintln s!"[ixvm-model-advice] only {payloads} modeled blocks got a payload"
    ok := false
  unless env.consts.size == bare.consts.size &&
      env.consts.keys.all bare.consts.contains do
    IO.eprintln "[ixvm-model-advice] attaching the models changed `consts`"
    ok := false
  let ctx ← IO.ofExcept (Ix.ClaimContext.ofEnv env true)
  let ctx0 ← IO.ofExcept (Ix.ClaimContext.ofEnv bare true)
  let mut owned : Array Address := #[]
  for n in names do
    let addr ← lookupAddr env n
    owned := owned.push addr
    let claim := Ix.Claim.check ctx addr none
    let claim0 := Ix.Claim.check ctx0 addr none
    unless Ix.Claim.ser claim == Ix.Claim.ser claim0 do
      IO.eprintln s!"[ixvm-model-advice] the check claim on {n} differs"
      ok := false
    let w ← IO.ofExcept (buildClaimWitness env claim)
    let w0 ← IO.ofExcept (buildClaimWitness bare claim0)
    unless w.input == w0.input && w.funcName == w0.funcName do
      IO.eprintln s!"[ixvm-model-advice] the public input of the claim on {n} differs"
      ok := false
  let (c, _) ← IO.ofExcept (shardCheckEnvClaimTrees env owned true)
  let (c0, _) ← IO.ofExcept (shardCheckEnvClaimTrees bare owned true)
  unless Ix.Claim.ser c == Ix.Claim.ser c0 do
    IO.eprintln "[ixvm-model-advice] the shard claim differs"
    ok := false
  let digest := Address.blake3 (Ix.Claim.ser c)
  IO.println s!"[ixvm-model-advice] {payloads} payloads; {names.length} check claims and \
    the shard claim over them agree with and without models (shard digest {digest})"
  return ok

/-- Every theorem's value under `let _ : Nat := 0`: a different proof of the
same statement, so a different record. -/
def tweakProofs : Ix.Kernel.Declaration .anon → Ix.Kernel.Declaration .anon
  | .thmDecl cv v => .thmDecl cv (.letE (.const (.role .nat) []) (.lit (.natVal 0)) v default)
  | d => d

def run (lenv : Lean.Environment) : IO UInt32 := do
  let names := modeledNames.map nameOfString
  let missing := names.filter (!lenv.constants.contains ·)
  unless missing.isEmpty do
    IO.eprintln s!"[ixvm-model-advice] not in the environment: {missing}"
    return 1
  let env ← loadSharedIxonEnv names.toArray lenv
  let digestOk ← digestUnchanged env names
  -- why a modeled block has no model, if one has none
  let (_, rep0) ← IO.ofExcept (IxVM.Model.generateReport { withoutModels env with modelsAttached := false })
  for (b, r) in rep0.blocks do
    match r with
    | .error e => IO.eprintln s!"[ixvm-model-advice] block {b} has no model: {e}"
    | .ok (n, outside) => IO.println s!"[ixvm-model-advice] block {b}: {n} advice records, {outside.size} outside references"
  -- the control: the same environment with the tweaked models
  let (tweaked, _) ← IO.ofExcept (IxVM.Model.generateReport { withoutModels env with modelsAttached := false } tweakProofs)
  let differ := tweaked.models.toList.any fun (b, p) => (env.models[b]?.map (·.data)) != some p.data
  unless differ do IO.eprintln "[ixvm-model-advice] the tweaked models have the same payloads"
  let mkCase (e : Ixon.Env) (tag : String) (n : Lean.Name) : Builder := fun _ => do
    let some target := e.getAddr? (Ix.Name.fromLeanName n)
      | throw s!"{n} is not in the Ixon environment"
    let ctx ← Ix.ClaimContext.ofEnv e true
    Case.ofClaim s!"check {n} ({tag})" e (.check ctx target none)
  -- no advice under user axioms: `Even` with an unused, well-typed `axiom ax : Prop`
  let underAxiom : Builder := fun _ => do
    let ax : Ixon.Constant := ⟨.axio ⟨false, 0, .sort 0⟩, #[], #[], #[.zero], #[]⟩
    let a := Address.blake3 (Ixon.ser ax)
    let e := env.storeConst a ax
    let some axioms := Ix.AssumptionTree.canonical #[a] | throw "no tree for the axiom"
    let some target := e.getAddr? (Ix.Name.fromLeanName (nameOfString "IxVMInd.Even"))
      | throw "IxVMInd.Even is not in the Ixon environment"
    let ctx ← Ix.ClaimContext.ofEnv e true
    Case.ofClaim "check IxVMInd.Even under a user axiom (no model advice)" e
      (.check { ctx with axioms := some axioms.root } target none)
      (({} : Std.HashMap _ _).insert axioms.root axioms) (accept := false)
      (rejectsWith := some "model advice: a claim with user axioms")
  let cases := (names.map (mkCase env "modeller's model")) ++
    (names.map (mkCase tweaked "a different valid model")) ++ [underAxiom]
  -- the verdicts on `NB4`'s claims, from the entry's host cases (loaded at run time)
  let fenv ← getCompileEnv #[`Tests.Ix.Kernel.EntryCaseDefs]
  let fixEnv ← loadSharedIxonEnv (nestedVerdicts.map (·.1)).toArray fenv
  let verdictCase (n : Lean.Name) (accept : Bool) : Builder := fun _ => do
    let some target := fixEnv.getAddr? (Ix.Name.fromLeanName n)
      | throw s!"{n} is not in the Ixon environment"
    let ctx ← Ix.ClaimContext.ofEnv fixEnv true
    Case.ofClaim s!"{if accept then "accept" else "refuse"} {n}" fixEnv (.check ctx target none) {} accept
  let cases := cases ++ nestedVerdicts.map fun (n, accept) => verdictCase n accept
  let rc ← runCases "ixvm-model-advice" cases.toArray
  return if digestOk && differ && rc == 0 then 0 else 1

/-- The environment of an `.ixe` file under the default role table, without models. -/
def loadIxe (path : String) : IO Ixon.Env := do
  let env ← IO.ofExcept (Ixon.deEnvAnon (← IO.FS.readBinFile path))
  IO.ofExcept (withRoleTable env (← IO.ofExcept Ix.Kernel.Reader.defaultTableBytes))

private def groupOf (a : Address) (ci : Ixon.ConstantInfo) : Address :=
  match ci with
  | .iPrj p | .cPrj p | .rPrj p | .dPrj p => p.block
  | _ => a

/-- `ixvm-model-coverage`: every modeled block of an `.ixe` file (`IX_MODEL_IXE`)
checked through the modeled route, one `CheckEnv` claim per block owning the
block, its recursor family record and their projections, the frontier and the
binding assumed. A block without a payload is a failure. -/
def coverage (_ : Lean.Environment) : IO UInt32 := do
  let some path ← IO.getEnv "IX_MODEL_IXE"
    | IO.eprintln "[ixvm-model-coverage] set IX_MODEL_IXE to an .ixe file"; return 1
  let env ← loadIxe path
  let (env, rep) ← IO.ofExcept (IxVM.Model.generateReport { env with modelsAttached := false })
  let mut none := 0
  for (b, r) in rep.blocks do
    if let .error e := r then
      none := none + 1
      IO.eprintln s!"[ixvm-model-coverage] block {b} has no model: {e}"
  let mut groups : Std.HashMap Address (Array Address) := {}
  for (a, lc) in env.consts do
    if let some c := lc.get? then
      let g := groupOf a c.info
      groups := groups.insert g ((groups.getD g #[]).push a)
  let cases : Array Builder := rep.advice.map fun (b, adv) => fun _ => do
    let owned := groups.getD b #[] ++ groups.getD adv.layout.recBlock #[]
    let (_, witness) ← buildShardCheckEnvWitness env owned (assumeBinding := true)
    return { label := s!"model coverage: block {b} ({owned.size} owned, {adv.records.size} advice records)",
             accept := true, witness }
  IO.println s!"[ixvm-model-coverage] {rep.blocks.size} modeled blocks, {rep.advice.size} with a payload"
  let rc ← runCases "ixvm-model-coverage" cases (jobs := 6)
  return if rc == 0 && none == 0 then 0 else 1

/-- The `refs` indices a record projects at (`.prj`). -/
private partial def prjIdxsExpr : Ixon.Expr → Std.HashSet Nat
  | .prj i _ inner => (prjIdxsExpr inner).insert i.toNat
  | .app a b | .lam _ a b | .all _ _ a b => (prjIdxsExpr a).union (prjIdxsExpr b)
  | .letE _ t v b => ((prjIdxsExpr t).union (prjIdxsExpr v)).union (prjIdxsExpr b)
  | _ => {}

private def prjIdxs (c : Ixon.Constant) : Std.HashSet Nat := Id.run do
  let mut out : Std.HashSet Nat := {}
  for e in c.sharing do out := out.union (prjIdxsExpr e)
  let ofDefn (d : Ixon.Definition) := (prjIdxsExpr d.typ).union (prjIdxsExpr d.value)
  let ofRecr (r : Ixon.Recursor) := r.rules.foldl
    (fun acc rule => acc.union (prjIdxsExpr rule.rhs)) (prjIdxsExpr r.typ)
  let ofIndc (i : Ixon.Inductive) := i.ctors.foldl
    (fun acc ctor => acc.union (prjIdxsExpr ctor.typ)) (prjIdxsExpr i.typ)
  match c.info with
  | .defn d => out := out.union (ofDefn d)
  | .recr r => out := out.union (ofRecr r)
  | .axio a => out := out.union (prjIdxsExpr a.typ)
  | .quot q => out := out.union (prjIdxsExpr q.typ)
  | .muts members =>
    for m in members do
      out := out.union <| match m with
        | .defn d => ofDefn d
        | .indc i => ofIndc i
        | .recr r => ofRecr r
  | _ => pure ()
  return out

/-- `ixvm-model-proj`: what refusing `.proj` at modeled blocks costs an `.ixe`
file (`IX_MODEL_IXE`): the records that project at a type of a mutual or nested
block, and every record whose dependency closure reaches one of them. -/
def projUse (_ : Lean.Environment) : IO UInt32 := do
  let some path ← IO.getEnv "IX_MODEL_IXE"
    | IO.eprintln "[ixvm-model-proj] set IX_MODEL_IXE to an .ixe file"; return 1
  let env ← loadIxe path
  let (_, rep) ← IO.ofExcept (IxVM.Model.generateReport { env with modelsAttached := false })
  let modeled : Std.HashSet Address := rep.blocks.foldl (fun s (b, _) => s.insert b) {}
  let mut store : Std.HashMap Address Ixon.Constant := {}
  for (a, lc) in env.consts do
    if let some c := lc.get? then store := store.insert a c
  let modeledType (r : Address) : Bool := match store[r]? with
    | some c => match c.info with
      | .iPrj p => modeled.contains p.block
      | _ => false
    | none => false
  -- direct users, and the reverse edges of the claim walk (used references, projection to block)
  let mut direct : Array Address := #[]
  let mut rev : Std.HashMap Address (Array Address) := {}
  for (a, c) in store.toList do
    if (prjIdxs c).toList.any fun i => (c.refs[i]?.map modeledType).getD false then
      direct := direct.push a
    let used := IxVM.Model.usedIdxs c
    let mut srcs : Array Address := #[]
    if let some b := IxVM.Model.projectionBlock? c then srcs := srcs.push b
    for (r, j) in c.refs.zipIdx do
      if used.contains j then srcs := srcs.push r
    for s in srcs do rev := rev.insert s ((rev.getD s #[]).push a)
  let mut seen : Std.HashSet Address := direct.foldl (·.insert ·) {}
  let mut queue := direct
  let mut head := 0
  while head < queue.size do
    let a := queue[head]!
    head := head + 1
    for d in rev.getD a #[] do
      unless seen.contains d do
        seen := seen.insert d
        queue := queue.push d
  let named (xs : Array Address) : Array String :=
    xs.filterMap fun x => env.addrToName[x]?.map toString
  let directNames := named direct
  let allNames := named queue
  IO.println s!"[ixvm-model-proj] {modeled.size} modeled blocks; {direct.size} records project at \
    one of their types ({directNames.size} named constants); {queue.size} records reach one \
    ({allNames.size} named constants) of {store.size} records ({env.addrToName.size} named)"
  for n in directNames.qsort (· < ·) do IO.println s!"DIRECT {n}"
  for n in (allNames.qsort (· < ·)).toList.take 200 do IO.println s!"REACH {n}"
  return 0

/-- `ixvm-model-report`: the advice per modeled block of an `.ixe` file. -/
def report (_ : Lean.Environment) : IO UInt32 := do
  let some path ← IO.getEnv "IX_MODEL_IXE"
    | IO.eprintln "[ixvm-model-report] set IX_MODEL_IXE to an .ixe file"; return 1
  let env ← IO.ofExcept (Ixon.deEnvAnon (← IO.FS.readBinFile path))
  let env ← IO.ofExcept (withRoleTable env (← IO.ofExcept Ix.Kernel.Reader.defaultTableBytes))
  let (_, rep) ← IO.ofExcept (IxVM.Model.generateReport { env with modelsAttached := false })
  let mut ok := 0
  let mut kinds : Std.HashMap Nat Nat := {}
  let mut outsideAll : Std.HashMap Address Nat := {}
  for (b, r) in rep.blocks do
    match r with
    | .ok (n, outside) =>
      ok := ok + 1
      for (x, k) in outside do
        kinds := kinds.insert k (kinds.getD k 0 + 1)
        outsideAll := outsideAll.insert x k
      IO.println s!"BLOCK {b} ok records={n} outside={outside.size} \
        basis={(outside.filter (·.2 == 0)).size} closure={(outside.filter (·.2 == 1)).size} \
        container-rec={(outside.filter (·.2 == 2)).size} projection={(outside.filter (·.2 == 3)).size}"
    | .error e => IO.println s!"BLOCK {b} none: {e}"
  IO.println s!"[ixvm-model-report] {rep.blocks.size} modeled blocks, {ok} with a payload; outside \
    references by kind: basis {kinds.getD 0 0}, closure {kinds.getD 1 0}, container recursor {kinds.getD 2 0}, \
    projection of a closure block {kinds.getD 3 0}; \
    {outsideAll.size} distinct"
  for (x, k) in outsideAll.toList do
    if k != 1 then
      let n := (env.addrToName[x]?.map toString).getD "?"
      IO.println s!"OUTSIDE kind={k} {x} {n}"
  return if ok == rep.blocks.size then 0 else 1

end Tests.Ix.IxVM.ModelAdvice

end
