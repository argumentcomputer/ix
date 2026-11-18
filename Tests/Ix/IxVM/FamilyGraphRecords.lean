import Tests.Ix.IxVM.Harness
import Tests.Ix.IxVM.FamilyGraphDefs
import Tests.Ix.IxVM.FamilyRecordsDefs
import Ix.IxVM.Model

/-! # The compiled records of two nested families, for the family graph

`ixvm-family-graph-records` compiles a tree nested through a user container and a `List`-nested
tree with Ix's compiler, generates the model advice of their blocks
(`IxVM.Model.generateReport`), and checks that each block got a payload with a model per member
and a theorem per rule.

With `IX_FAMILY_GRAPH_OUT` set to a file, it writes what it compiled there, one item a line in
hexadecimal: the role table's bytes (`table`), every record with its address (`rec`: the
environment's, then the advice's), and for each family its block's address, its recursor family
record's address and the addresses of its advice records (`fam`). The statements about the
family graph are evaluated on this file. -/

namespace Tests.Ix.IxVM.FamilyGraphRecords

open IxVM.ClaimHarness Tests.Ix.IxVM

private def graphDefs (s : String) : Lean.Name :=
  (`Tests.Ix.IxVM.FamilyGraphDefs).str s

private def recordDefs (s : String) : Lean.Name :=
  (`Tests.Ix.IxVM.FamilyRecordsDefs).str s

/-- The families: a label, the first type, the names compiled, and the expected numbers of member
models and of rule theorems. -/
private def families : List (String × Lean.Name × Array Lean.Name × Nat × Nat) :=
  [("BoxTree", graphDefs "BT",
     #[graphDefs "BT", (graphDefs "BT").str "rec", (graphDefs "BT").str "rec_1"], 4, 2),
   ("NestedTree", recordDefs "T",
     #[recordDefs "T", (recordDefs "T").str "rec", (recordDefs "T").str "rec_1"], 4, 3)]

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

private def hex (b : ByteArray) : String :=
  String.ofList (b.data.toList.flatMap fun x => [hexDigit (x.toNat / 16), hexDigit (x.toNat % 16)])

private def hexList (as : Array Address) : String :=
  ",".intercalate (as.toList.map fun a => hex a.hash)


/-! ## A second recursor record that keeps the wrappers its constructors declare

Lean's kernel removes the type-annotation wrappers (`autoParam` among them) at the head of the
field types it copies into a recursor's minor premises and rules. `wrapRecursor` puts each
`autoParam` back: at the field binders of a minor premise, where the constructor's field has
one, and at the same binders of the constructor's rule. The result is a second recursor record
for the same block. -/

/-- For each field of a constructor, the level and tactic argument of its `autoParam`. -/
private def ctorAutoParams (cv : Lean.ConstructorVal) :
    Array (Option (Lean.Level × Lean.Expr)) := Id.run do
  let mut ty := cv.type
  for _ in [0:cv.numParams] do
    if let .forallE _ _ b _ := ty then ty := b
  let mut out : Array (Option (Lean.Level × Lean.Expr)) := #[]
  for _ in [0:cv.numFields] do
    match ty with
    | .forallE _ d b _ =>
      let entry : Option (Lean.Level × Lean.Expr) :=
        if d.isAppOfArity ``autoParam 2 then
          match d.getAppFn with
          | .const _ [l] =>
            if d.appArg!.hasLooseBVars || l.hasParam then none else some (l, d.appArg!)
          | _ => none
        else none
      out := out.push entry
      ty := b
    | _ => out := out.push none
  return out

private def wrapDom (aps : Array (Option (Lean.Level × Lean.Expr))) (j : Nat)
    (d : Lean.Expr) : Lean.Expr :=
  match aps[j]? with
  | some (some (l, tac)) => Lean.mkApp2 (Lean.mkConst ``autoParam [l]) d tac
  | _ => d

/-- Wrap the domains of the first binders of a telescope, one per field. -/
private partial def wrapTele (aps : Array (Option (Lean.Level × Lean.Expr))) :
    Nat → Lean.Expr → Lean.Expr
  | j, .forallE n d b bi =>
    if j < aps.size then .forallE n (wrapDom aps j d) (wrapTele aps (j + 1) b) bi
    else .forallE n d b bi
  | j, .lam n d b bi =>
    if j < aps.size then .lam n (wrapDom aps j d) (wrapTele aps (j + 1) b) bi
    else .lam n d b bi
  | _, e => e

/-- The constructor a minor premise is for: the head of its conclusion's last argument. -/
private partial def resultCtor : Lean.Expr → Option Lean.Name
  | .forallE _ _ b _ => resultCtor b
  | e => e.getAppArgs.back?.bind fun major => major.getAppFn.constName?

private def wrapMinor (leanEnv : Lean.Environment) (d : Lean.Expr) : Lean.Expr :=
  match (resultCtor d).bind leanEnv.find? with
  | some (.ctorInfo cv) => wrapTele (ctorAutoParams cv) 0 d
  | _ => d

private partial def wrapTypeGo (leanEnv : Lean.Environment) (lo hi : Nat) :
    Nat → Lean.Expr → Lean.Expr
  | i, .forallE n d b bi =>
    .forallE n (if lo ≤ i && i < hi then wrapMinor leanEnv d else d)
      (wrapTypeGo leanEnv lo hi (i + 1) b) bi
  | _, e => e

private partial def wrapRuleGo (leanEnv : Lean.Environment) (lo hi : Nat)
    (aps : Array (Option (Lean.Level × Lean.Expr))) : Nat → Lean.Expr → Lean.Expr
  | i, .lam n d b bi =>
    if i < hi then
      .lam n (if lo ≤ i then wrapMinor leanEnv d else d) (wrapRuleGo leanEnv lo hi aps (i + 1) b) bi
    else wrapTele aps 0 (.lam n d b bi)
  | _, e => e

/-- A recursor with the `autoParam`s of its constructors' fields kept. -/
private def wrapRecursor (leanEnv : Lean.Environment) (rv : Lean.RecursorVal) :
    Lean.RecursorVal :=
  let lo := rv.numParams + rv.numMotives
  let hi := lo + rv.numMinors
  { rv with
    type := wrapTypeGo leanEnv lo hi 0 rv.type
    rules := rv.rules.map fun r =>
      let aps := match leanEnv.find? r.ctor with
        | some (.ctorInfo cv) => ctorAutoParams cv
        | _ => #[]
      { r with rhs := wrapRuleGo leanEnv lo hi aps 0 r.rhs } }

/-- The certified compile of the closure of `names`, each constant passed through `edit`. -/
private def compileWith (leanEnv : Lean.Environment) (names : Array Lean.Name)
    (edit : Lean.Name × Lean.ConstantInfo → Lean.Name × Lean.ConstantInfo) : IO Ixon.Env := do
  let roots := withModeledRecursors
    ((names ++ synthesizedPrimNames ++ roleNames).filter leanEnv.constants.contains) leanEnv
  let constants := (collectCertifiedClosure roots leanEnv).map edit
  match ← Ix.CompileM.compileCertified leanEnv constants 32 with
  | .error e => throw (IO.userError s!"the certified compile failed: {e}")
  | .ok out =>
    unless out.failures.isEmpty do
      let fMap := out.failures.toMap
      throw (IO.userError s!"the certified compile: {fMap.size} constants failed: \
        {Ix.CompileM.recordedFailures fMap}")
    IO.ofExcept (withDefaultRoleBinding out.env)

/-- The block of `first`, its recursor family record as the modeller names it, and the block's
own addresses (the block and its projections), in `env` with its model advice. -/
private def familyOf (env0 : Ixon.Env) (first : Lean.Name) :
    IO (Ixon.Env × Address × Address × Array Address × Nat) := do
  let (env, rep) ← IO.ofExcept (IxVM.Model.generateReport
    { env0 with models := {}, modelRecords := {}, modelHints := {}, modelBlobs := {},
                modelDeps := {}, modelsAttached := false })
  let ty ← lookupAddr env first
  let some block := (env.getConst? ty).bind IxVM.Model.projectionBlock?
    | throw (IO.userError s!"{first} is not a member of a block")
  let some (_, adv) := rep.advice.find? (·.1 == block)
    | throw (IO.userError s!"the block of {first} has no model advice")
  let mut owned : Array Address := #[block]
  for (a, lc) in env.consts do
    if let some c := lc.get? then
      if IxVM.Model.projectionBlock? c == some block then owned := owned.push a
  return (env, block, adv.layout.recBlock, owned, adv.records.size)

/-- The second record of `Lean.Compiler.LCNF.Alt`'s family: compile the family as Lean has it
and with the `autoParam`s kept, and submit each block claim with its own advice. -/
def runTwin (leanEnv : Lean.Environment) : IO UInt32 := do
  let first : Lean.Name := `Lean.Compiler.LCNF.Alt
  let some (.inductInfo iv) := leanEnv.find? first
    | do IO.eprintln s!"[ixvm-family-graph-records] {first} is not an inductive"; return 1
  let recNames : List Lean.Name := iv.all.map Lean.mkRecName ++
    (List.range iv.numNested).map fun i => Lean.Name.mkStr (iv.all.headD first) s!"rec_{i + 1}"
  let wrapped := iv.all.foldl (init := 0) fun acc t =>
    match leanEnv.find? t with
    | some (.inductInfo tv) => tv.ctors.foldl (init := acc) fun acc c =>
        match leanEnv.find? c with
        | some (.ctorInfo cv) => acc + ((ctorAutoParams cv).filter (·.isSome)).size
        | _ => acc
    | _ => acc
  IO.println s!"[ixvm-family-graph-records] twin: types {iv.all}, recursors {recNames}, \
    {wrapped} constructor fields with autoParam"
  let names := #[first] ++ recNames.toArray
  let edit : Lean.Name × Lean.ConstantInfo → Lean.Name × Lean.ConstantInfo := fun (n, ci) =>
    match ci with
    | .recInfo rv => if recNames.contains n then (n, .recInfo (wrapRecursor leanEnv rv)) else (n, ci)
    | _ => (n, ci)
  let changed := recNames.filter fun n =>
    match leanEnv.find? n with
    | some (.recInfo rv) => (wrapRecursor leanEnv rv).type != rv.type
    | _ => false
  IO.println s!"[ixvm-family-graph-records] twin: recursors whose type changes: {changed.length} \
    of {recNames.length}"
  let envC0 ← compileWith leanEnv names id
  let envW0 ← compileWith leanEnv names edit
  let (envC, blockC, rbC, ownedC, nAdvC) ← familyOf envC0 first
  let (envW, blockW, rbW, ownedW, nAdvW) ← familyOf envW0 first
  IO.println s!"[ixvm-family-graph-records] twin: as Lean has it: block {blockC}, recursor \
    family {rbC}, {nAdvC} advice records"
  IO.println s!"[ixvm-family-graph-records] twin: autoParams kept: block {blockW}, recursor \
    family {rbW}, {nAdvW} advice records"
  let sameBlock := blockC == blockW
  let secondRecord := rbC != rbW
  IO.println s!"[ixvm-family-graph-records] twin: one block {sameBlock}, two recursor records \
    {secondRecord}"
  let exercise := (← IO.getEnv "IX_FAMILY_TWIN_EXERCISE").getD "KernelModeled::check_family"
  let cases : Array Builder :=
    #[("the record as Lean has it", envC, ownedC), ("the record with the autoParams kept", envW, ownedW)].map
      fun (label, env, owned) => fun _ => do
        let (_, witness) ← buildShardCheckEnvWitness env owned (assumeBinding := true)
        return { label := s!"family of {first}, {label}: {owned.size} owned",
                 accept := true, exercises := some exercise, witness }
  let rc ← runCases "ixvm-family-graph-records" cases (jobs := 2)
  if let some path ← IO.getEnv "IX_FAMILY_TWIN_OUT" then
    IO.FS.writeFile path s!"twin {hex blockC.hash} {hex rbC.hash} {hex rbW.hash}\n"
  return if rc == 0 && sameBlock && secondRecord then 0 else 1

/-- The two nested families, and, with `IX_FAMILY_TWIN` set, the second recursor record. -/
def run (leanEnv : Lean.Environment) : IO UInt32 := do
  if (← IO.getEnv "IX_FAMILY_TWIN").isSome then return (← runTwin leanEnv)
  let names := families.foldl (fun acc f => acc ++ f.2.2.1) #[]
  let missing := names.filter (!leanEnv.constants.contains ·)
  unless missing.isEmpty do
    IO.eprintln s!"[ixvm-family-graph-records] not in the environment: {missing}"
    return 1
  let env0 ← loadSharedIxonEnv names leanEnv
  let (env, rep) ← IO.ofExcept (IxVM.Model.generateReport
    { env0 with models := {}, modelRecords := {}, modelHints := {}, modelBlobs := {},
                modelDeps := {}, modelsAttached := false })
  let mut ok := true
  let mut lines : Array String := #[]
  match env.roleBinding with
  | some b => lines := lines.push s!"table {hex b.bytes}"
  | none =>
    IO.eprintln "[ixvm-family-graph-records] the environment has no role binding"
    ok := false
  for (a, lc) in env.consts do
    lines := lines.push s!"rec {hex a.hash} {hex lc.rawBytes}"
  for (a, c) in env.modelRecords do
    lines := lines.push s!"rec {hex a.hash} {hex (Ixon.serConstant c)}"
  for (label, first, _, nModels, nIotas) in families do
    let ty ← lookupAddr env first
    let some block := (env.getConst? ty).bind IxVM.Model.projectionBlock?
      | do
        IO.eprintln s!"[ixvm-family-graph-records] {label}: {first} is not a member of a block"
        return 1
    let some (_, adv) := rep.advice.find? (·.1 == block)
      | do
        IO.eprintln s!"[ixvm-family-graph-records] {label}: the block has no model advice"
        return 1
    let p := adv.layout
    let models := p.typeModels.size + p.ctorModels.size + p.recModels.size
    IO.println s!"[ixvm-family-graph-records] {label}: block {block}, recursor family \
      {p.recBlock}, {adv.records.size} advice records, {models} member models, \
      {p.iotas.size} rule theorems"
    unless models == nModels && p.iotas.size == nIotas do
      IO.eprintln s!"[ixvm-family-graph-records] {label}: expected {nModels} member models and \
        {nIotas} rule theorems"
      ok := false
    lines := lines.push s!"fam {label} {hex block.hash} {hex p.recBlock.hash} \
      {hexList (adv.records.map (·.1))}"
  if let some path ← IO.getEnv "IX_FAMILY_GRAPH_OUT" then
    IO.FS.writeFile path ("\n".intercalate lines.toList ++ "\n")
    IO.println s!"[ixvm-family-graph-records] wrote {lines.size} lines to {path}"
  return if ok then 0 else 1

end Tests.Ix.IxVM.FamilyGraphRecords
