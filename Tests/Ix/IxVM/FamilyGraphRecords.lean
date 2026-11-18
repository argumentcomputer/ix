import Tests.Ix.IxVM.Harness
import Tests.Ix.IxVM.FamilyGraphDefs
import Tests.Ix.IxVM.FamilyRecordsDefs
import Ix.IxVM.Model
import Ix.Compile.KernelAnnotate
import IxC.Kernel.Inductives.TwinInstall

/-! # The compiled records of two nested families and of a second recursor record

`ixvm-family-graph-records` compiles a tree nested through a user container and a `List`-nested
tree with Ix's compiler, generates the model advice of their blocks
(`IxVM.Model.generateReport`), and checks that each block got a payload with a model per member
and a theorem per rule.

With `IX_FAMILY_GRAPH_OUT` set to a file, it writes what it compiled there, one item a line in
hexadecimal: the role table's bytes (`table`), every record with its address (`rec`: the
environment's, then the advice's), and for each family its block's address, its recursor family
record's address and the addresses of its advice records (`fam`). The statements about the
family graph are evaluated on this file.

With `IX_FAMILY_TWIN` set, the suite instead builds a second recursor record for the block of
`Lean.Compiler.LCNF.Alt` (its recursors with the `autoParam`s of the constructors' fields kept,
compiled by the same pipeline), checks that the block's record is the same and the recursor
record another, and submits the block's claim once with each record's advice; both must be
accepted. With `IX_FAMILY_TWIN_JUDGE` it also evaluates, in source mode and with IxC's
executable functions, the conjuncts of IxC's twin record for the second record. -/

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


/-! ## IxC's twin record for the second recursor record, evaluated in source mode

IxC's in-process install (`Ix.Compile.KernelAnnotate`, the one the certified compile runs for
the binder data) gives the environment that stores the family as compiled. The recursors of the
other variant, taken as IxC stores them and renamed to fresh keys, are a second recursor block
for it. `secondRecordConjuncts` evaluates, with IxC's executable functions, each conjunct of
IxC's twin record (`Ix.Kernel.Semantics.DeclRecTwinRunJ` at the package of runs) for that block:
the generated type is the second record's own checked type, and a rule's generated right-hand
side is the second record's rule with the canonical peers. -/

section Judgement

open Ix.Kernel

private abbrev SRec := ConstantVal .source × Nat × Nat × List (RecRule .source)

/-- IxC's in-process install of all of `constants` (the certified compile installs only what
its binder data needs; here every declaration of the input is installed). -/
private def installOf (leanEnv : Lean.Environment)
    (constants : List (Lean.Name × Lean.ConstantInfo)) :
    IO Ix.Compile.KernelAnnotate.Installed := do
  let (prepared, _) ← IO.ofExcept (Ix.CompileM.prepareCertified leanEnv constants)
  let ienv := Ix.CompileM.canonInput prepared.toArray 32
  let pre ← IO.ofExcept Ix.Compile.KernelAnnotate.prelude?
  let refs := ienv.consts.toList.toArray.map fun (nc : Ix.Name × Ix.ConstantInfo) =>
    (nc.1, (Ix.GraphM.run ienv .init (Ix.graphConst nc.2)).1)
  let graph : Ix.Map Ix.Name (Ix.Set Ix.Name) :=
    refs.foldl (fun out (n, rs) => out.insert n rs) {}
  let blocks ← IO.lazyPure fun _ => Ix.CondenseM.run graph
  IO.ofExcept (← Ix.Compile.KernelAnnotate.install ienv blocks pre 32)

/-- The stored recursors with the given spellings, in their order. -/
private def storedRecs (env : Env .source) (names : List String) : List SRec :=
  names.filterMap fun s => env.consts.findSome? fun ci =>
    match ci with
    | .recInfo cv mI rP rules => if toString cv.name == s then some (cv, mI, rP, rules) else none
    | _ => none

private def secondKey (k : Key .source) : Key .source :=
  match k with
  | .id nm => .id (.str nm "second")
  | k => .aux k .implRec

/-- The recursors as a block at fresh keys, their peers renamed with them. -/
private def secondBlock (recs : List SRec) : List (ConstantInfo .source) :=
  let names := recs.map (·.1.name)
  let f : Key .source → Key .source := fun k => if names.contains k then secondKey k else k
  recs.map fun (cv, mI, rP, rules) =>
    .recInfo { cv with name := f cv.name } mI rP
      (rules.map fun r => { r with rhs := r.rhs.renameConsts f })

private def okOf {α : Type} (x : CheckM .source α) : Bool :=
  match x with
  | .ok _ => true
  | .error _ => false

/-- Each conjunct of IxC's twin record for `block` as a second record of the stored recursors
`canon` of `env`, evaluated at fuel `fuel`. -/
private def secondRecordConjuncts (fuel : Nat) (env : Env .source) (canon : List SRec)
    (block : List (ConstantInfo .source)) : Except String (List (String × Bool) × Nat) := do
  let ops : CheckerOps .source (CheckM .source) := fueledOps .verified fuel
  let mut parts : List (NativeTwin.Part .source) := []
  let mut lf := true
  let mut counts := true
  let mut lps := true
  let mut model := true
  let mut tyAbove := true
  let mut tyTyped := true
  for (ci, (cvC, mIC, rPC, rulesC)) in block.zip canon do
    let .recInfo cvW mI rP rulesW := ci | throw "the block holds a constant that is no recursor"
    match checkConstantVal ops env cvW with
    | .error e => throw s!"the front door refuses {cvW.name}: {e}"
    | .ok cvW' =>
      lf := lf && Semantics.letFree cvW'.type
      counts := counts && mI == mIC && rP == rPC && rulesW.length == rulesC.length
      lps := lps && cvW.levelParams == cvC.levelParams
      let model? := match env.find? (auxKey cvC.name .model) with
        | some (.defnInfo cv value hint) => some (cv, value, hint)
        | _ => none
      model := model && model?.isSome
      tyAbove := tyAbove && Semantics.wrapRelOk env.find? cvW'.type cvC.type
      tyTyped := tyTyped && !cvW'.type.hasFvar &&
        cvW'.type.allLevelParamsDefined cvC.levelParams && cvW'.type.constsResolve env &&
        cvW'.type.looseBVarsBounded 0 && okOf (inferTypeCore .verified env fuel 0 cvW'.type)
      parts := parts ++ [{
        raw := cvW, annotated := cvW', canonical := cvC, canonicalKey := cvC.name,
        majorIndex := mI, rulePrefix := rP, rawRules := rulesW, canonicalRules := rulesC,
        model? := model? }]
  let added := NativeTwin.provision parts ++ NativeTwin.models parts
  let nodup := decide ((added.map (·.name)).Nodup)
  let fresh := added.all fun ci => (env.find? ci.name).isNone
  let envSelf := NativeTwin.selfEnv env parts
  let checked ← match NativeTwin.checkPartsRules ops env envSelf parts with
    | .ok c => pure c
    | .error e => throw s!"a rule's stage fails: {e}"
  let f := NativeTwin.peerRename parts
  let back : Key .source → Key .source := fun k =>
    match parts.find? (fun p => p.raw.name == k) with
    | some p => p.canonicalKey
    | none => k
  let mut ruleAbove := true
  let mut ruleRenamed := true
  let mut ruleTyped := true
  let mut nrules := 0
  for p in checked do
    for (rW', rC) in p.checkedRules.zip p.canonicalRules do
      nrules := nrules + 1
      let g := rW'.rhs.renameConsts back
      ruleAbove := ruleAbove && Semantics.wrapRelOk env.find? g rC.rhs
      ruleRenamed := ruleRenamed && Semantics.wrapRelOk env.find? (g.renameConsts f) rW'.rhs
      ruleTyped := ruleTyped && !g.hasFvar && g.allLevelParamsDefined p.canonical.levelParams &&
        g.constsResolve env && g.looseBVarsBounded 0 &&
        okOf (inferTypeCore .verified env fuel 0 g)
  return ([("the block is not empty and each member is a recursor", !block.isEmpty),
    ("each front door accepts (checkConstantVal)", true),
    ("each checked type has no let", lf),
    ("each canonical recursor is stored with the member's counts and rule count", counts),
    ("the level parameters are the canonical recursor's", lps),
    ("each canonical recursor has its model companion", model),
    ("the new names are distinct", nodup), ("the new names are fresh", fresh),
    ("generated type := the member's checked type: WrapRel to the canonical type", tyAbove),
    ("generated type: closed, level-closed, resolved, bounded, inferred", tyTyped),
    ("each rule's stage (constructor, counts, annotation, scoping, no let, shape)", true),
    ("generated rule := the member's rule at the canonical peers: WrapRel to the canonical rule",
      ruleAbove),
    ("generated rule, renamed to the member's peers: WrapRel to the member's rule", ruleRenamed),
    ("generated rule: closed, level-closed, resolved, bounded, inferred", ruleTyped)], nrules)

end Judgement

/-- The certified compile of the closure of `names`, each constant passed through `edit`. -/
private def compileWith (leanEnv : Lean.Environment) (names : Array Lean.Name)
    (edit : Lean.Name × Lean.ConstantInfo → Lean.Name × Lean.ConstantInfo) :
    IO (Ixon.Env × List (Lean.Name × Lean.ConstantInfo)) := do
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
    return (← IO.ofExcept (withDefaultRoleBinding out.env), constants)

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
  let (envC0, constantsC) ← compileWith leanEnv names id
  let (envW0, constantsW) ← compileWith leanEnv names edit
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
  let mut judged := true
  if (← IO.getEnv "IX_FAMILY_TWIN_JUDGE").isSome then
    let instC ← installOf leanEnv constantsC
    let instW ← installOf leanEnv constantsW
    IO.println s!"[ixvm-family-graph-records] twin: IxC's install, as Lean has it: \
      {instC.installed} declarations, {instC.failures.size} refused, {instC.lenient} entered \
      without their checks; autoParams kept: {instW.installed}, {instW.failures.size}, \
      {instW.lenient}"
    let spellings := recNames.map toString
    let recsC := storedRecs instC.fe.env spellings
    let recsW := storedRecs instW.fe.env spellings
    IO.println s!"[ixvm-family-graph-records] twin: stored recursors found: {recsC.length} and \
      {recsW.length} of {recNames.length}"
    let fuel := 1000000
    let ops : Ix.Kernel.CheckerOps .source (Ix.Kernel.CheckM .source) :=
      Ix.Kernel.fueledOps .verified fuel
    -- IxC's own executable twin check, in both directions
    let verdict (env : Ix.Kernel.Env .source) (block : List (Ix.Kernel.ConstantInfo .source)) :
        String :=
      match Ix.Kernel.NativeTwin.check ops env block with
      | .ok _ => "accepted"
      | .error e => s!"declined: {((toString e).replace "\n" " ").take 160}"
    let keptOverLean := verdict instC.fe.env (secondBlock recsW)
    let leanOverKept := verdict instW.fe.env (secondBlock recsC)
    IO.println s!"[ixvm-family-graph-records] twin: IxC's executable twin check, the record with \
      the autoParams kept as a second record of Lean's: {keptOverLean}"
    IO.println s!"[ixvm-family-graph-records] twin: IxC's executable twin check, Lean's record as \
      a second record of the one with the autoParams kept: {leanOverKept}"
    match secondRecordConjuncts fuel instC.fe.env recsC (secondBlock recsW) with
    | .error e =>
      IO.eprintln s!"[ixvm-family-graph-records] twin: the twin record's conjuncts: {e}"
      judged := false
    | .ok (cs, nrules) =>
      for (name, b) in cs do
        IO.println s!"[ixvm-family-graph-records] twin record, {name}: {b}"
        judged := judged && b
      IO.println s!"[ixvm-family-graph-records] twin record: {recsW.length} recursors, {nrules} \
        rules, every conjunct {judged}"
    judged := judged && recsC.length == recNames.length && recsW.length == recNames.length &&
      leanOverKept == "accepted"
  if let some path ← IO.getEnv "IX_FAMILY_TWIN_OUT" then
    IO.FS.writeFile path s!"twin {hex blockC.hash} {hex rbC.hash} {hex rbW.hash}\n"
  return if rc == 0 && sameBlock && secondRecord && judged then 0 else 1

/-- A census of a block's payload: its advice records by the arm of the advice check that reads
them, and its witnessed references by kind. -/
private def payloadCensus (adv : IxVM.Model.BlockAdvice) : String :=
  let count (p : Ixon.Constant → Bool) : Nat := (adv.records.filter fun (_, c) => p c).size
  let defs := count fun c => match c.info with
    | .defn d => (match d.kind with | .defn => true | _ => false)
    | _ => false
  let thms := count fun c => match c.info with
    | .defn d => (match d.kind with | .thm => true | _ => false)
    | _ => false
  let recs := count fun c => match c.info with | .recr _ => true | _ => false
  let blocks := count fun c => match c.info with | .muts _ => true | _ => false
  let members := adv.records.foldl (init := 0) fun n (_, c) =>
    match c.info with | .muts ms => n + ms.size | _ => n
  let projs := count fun c => match c.info with | .iPrj _ | .cPrj _ => true | _ => false
  let w (k : Nat) : Nat := (adv.layout.witnesses.filter fun (_, kind, _, _) => kind == k).size
  s!"{adv.records.size} advice records ({defs} definitions, {thms} theorems, {recs} recursors, \
    {blocks} blocks with {members} members, {projs} projections), \
    {adv.layout.witnesses.size} witnessed references ({w 0} basis roles, {w 1} closure members, \
    {w 2} container recursors, {w 3} projections)"

/-- The checks two family checks run on their advice: the block claim of a `List`-nested tree
and of a mutual pair, each under an assumed and under a validated binding, with the census of
each payload. Every claim must be accepted and must have called the advice-record check. The
case file is kept under `IX_TEST_OUTPUT_DIR`, so that it can be rerun with the host's function
statistics. -/
def runInner (leanEnv : Lean.Environment) : IO UInt32 := do
  let fams : List (String × Lean.Name × Array Lean.Name) :=
    [("NestedTree", recordDefs "T",
       #[recordDefs "T", (recordDefs "T").str "rec", (recordDefs "T").str "rec_1"]),
     ("IndexedPair", recordDefs "EvT",
       #[recordDefs "EvT", recordDefs "OdT", (recordDefs "EvT").str "rec",
         (recordDefs "OdT").str "rec"])]
  IO.println s!"[ixvm-family-graph-records] inner: artifact {← programArtifact}"
  IO.println s!"[ixvm-family-graph-records] inner: host {← programHost}"
  let mut cases : Array Builder := #[]
  for (label, first, names) in fams do
    let env0 ← loadSharedIxonEnv names leanEnv
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
    IO.println s!"[ixvm-family-graph-records] inner {label}: block {block}, {owned.size} owned, \
      {payloadCensus adv}"
    let ownedAll := owned
    for assume in [true, false] do
      let mode := if assume then "assumed" else "validated"
      cases := cases.push fun _ => do
        let (_, witness) ← buildShardCheckEnvWitness env ownedAll (assumeBinding := assume)
        return { label := s!"inner-{label}-{mode}", accept := true,
                 exercises := some "KernelModeled::check_advice_record", witness }
  runCases "ixvm-family-graph-records" cases (jobs := 2)

/-- A binder-free safe `.defn` record (type and value are refs/apps, no `∀`/`λ`), so it needs no
binder section: `typ` and `value` are expressions over `refs` (`.ref i #[..]`) and `univs`. -/
private def bareDefn (safety : Ix.DefinitionSafety) (typ value : Ixon.Expr)
    (refs : Array Address) (univs : Array Ixon.Univ) : Address × Ixon.Constant :=
  let c : Ixon.Constant :=
    { info := .defn { kind := .defn, safety, lvls := 0, typ, value },
      sharing := #[], refs, univs, binders := #[] }
  (IxVM.Model.addressOf c, c)

/-- One family check's advice path, probed by execution. For each fixture (the `List`-nested tree
`T`, the mutual pair `EvT`/`OdT`) and each binding (assumed, validated), the clean payload is the
accepted control; each candidate differs from it by one advice or witness record, served through
`modelRecords`/`modelDeps` with the payload's `advice`/`witnesses` edited. Candidates that use an
inert axiom, an unsafe record or a block address must be rejected, and the function and message
are read from the circuit's error; a kind-1 dependency path ending at a block record is the one
benign accepted case (an unused witness). `IX_FAMILY_PROBE_SCOPE=quick` runs only `T`/assumed. -/
def runProbe (leanEnv : Lean.Environment) : IO UInt32 := do
  let fixtures : List (String × Lean.Name × Array Lean.Name) :=
    [("NestedTree", recordDefs "T",
       #[recordDefs "T", (recordDefs "T").str "rec", (recordDefs "T").str "rec_1"]),
     ("IndexedPair", recordDefs "EvT",
       #[recordDefs "EvT", recordDefs "OdT", (recordDefs "EvT").str "rec",
         (recordDefs "OdT").str "rec"])]
  let scope := (← IO.getEnv "IX_FAMILY_PROBE_SCOPE").getD "all"
  let fixtures := if scope == "quick" then fixtures.take 1 else fixtures
  let modes := if scope == "quick" then [true] else [true, false]
  IO.println s!"[ixvm-family-graph-records] probe: artifact {← programArtifact}, host {← programHost}"
  let mut cases : Array Builder := #[]
  for (label, first, names) in fixtures do
    let env0 ← loadSharedIxonEnv names leanEnv
    let (env, rep) ← IO.ofExcept (IxVM.Model.generateReport
      { env0 with models := {}, modelRecords := {}, modelHints := {}, modelBlobs := {},
                  modelDeps := {}, modelsAttached := false })
    let ty ← lookupAddr env first
    let some block := (env.getConst? ty).bind IxVM.Model.projectionBlock?
      | throw (IO.userError s!"{first} is not a member of a block")
    let some (_, adv) := rep.advice.find? (·.1 == block)
      | throw (IO.userError s!"the block of {first} has no model advice")
    let p := adv.layout
    let some blockRec := env.getConst? block | throw (IO.userError "no block record")
    -- the inert axioms (`sorryAx` always; `trustCompiler`/`ofReduceBool` when the env has them)
    let sorryA ← lookupAddr env `sorryAx
    let inertAddrs : Array (String × Address) :=
      (#[("sorryAx", some sorryA),
         ("trustCompiler", env.getAddr? (Ix.Name.fromLeanName `Lean.trustCompiler)),
         ("ofReduceBool", env.getAddr? (Ix.Name.fromLeanName `Lean.ofReduceBool))]).filterMap
        fun (n, a?) => a?.map (n, ·)
    -- the hand-built harmful records
    let natA ← lookupAddr env `Nat
    let bfA ← lookupAddr env `Bool.false
    let nzA ← lookupAddr env `Nat.zero
    let listA ← lookupAddr env `List
    let some listB := (env.getConst? listA).bind IxVM.Model.projectionBlock?
      | throw (IO.userError "List is not a member of a block")
    let rNat : Ixon.Expr := .ref 0 #[]
    -- `dSorry : Nat := @sorryAx.{1} Nat Bool.false` (a safe def that uses the inert axiom)
    let (dSorryA, dSorry) := bareDefn .safe (.ref 1 #[])
      (.app (.app (.ref 0 #[0]) (.ref 1 #[])) (.ref 2 #[]))
      #[sorryA, natA, bfA] #[.succ .zero]
    -- `dUnsafe : Nat := Nat.zero` flagged unsafe; `dRefsUnsafe : Nat := dUnsafe` (safe -> unsafe)
    let (dUnsafeA, dUnsafe) := bareDefn .unsaf rNat (.ref 1 #[]) #[natA, nzA] #[]
    let (dRefsUnsafeA, dRefsUnsafe) := bareDefn .safe rNat (.ref 1 #[]) #[natA, dUnsafeA] #[]
    -- `dBlock : Nat := <List's block record>` (a term naming a block (Muts) address)
    let (dBlockA, dBlock) := bareDefn .safe rNat (.ref 1 #[]) #[natA, listB] #[]
    -- a used reference of the block, for a one-step dependency path that cannot reach an axiom
    let usedSet := IxVM.Model.usedIdxs blockRec
    let jAny? := (blockRec.refs.zipIdx.find? fun (_, k) => usedSet.contains k).map (·.2)
    let jList? := blockRec.refs.findIdx? (· == listA)
    IO.println s!"[ixvm-family-graph-records] probe {label}: block {block}, {p.advice.size} advice, \
      {p.witnesses.size} witnesses; inert {inertAddrs.map (·.1)}; List's block {listB}; \
      block-ref-used {jAny?}, List-ref {jList?}"
    for assume in modes do
      let mode := if assume then "assumed" else "validated"
      let ctx ← IO.ofExcept (Ix.ClaimContext.ofEnv env assume)
      let mkEnv (extra : Array (Address × Ixon.Constant)) (pl : IxVM.Model.Payload) : Ixon.Env :=
        { env with models := env.models.insert block pl.ser,
                   modelRecords := extra.foldl (fun m (a, c) => m.insert a c) env.modelRecords,
                   modelDeps := env.modelDeps.insert block
                     ((env.modelDeps.getD block #[]) ++ extra.map (·.1)) }
      let probe (name : String) (extra : Array (Address × Ixon.Constant)) (pl : IxVM.Model.Payload)
          (accept : Bool) (why : Option String) : Builder := fun _ =>
        Case.ofClaim s!"probe-{label}-{mode}-{name}" (mkEnv extra pl) (.check ctx ty none)
          (accept := accept) (rejectsWith := why)
      cases := cases.push (probe "control" #[] p true none)
      -- (i) the inert axiom: as a basis-role witness, and the referencing safe def as advice
      for (n, a) in inertAddrs do
        cases := cases.push (probe s!"{n}-as-basis-witness" #[]
          { p with witnesses := p.witnesses.push (a, 0, [], []) } false
          (some "a reference to a role outside the basis"))
        if let some jAny := jAny? then
          cases := cases.push (probe s!"{n}-as-path-witness" #[]
            { p with witnesses := p.witnesses.push (a, 1, [jAny + 1], []) } false
            (some "a dependency path ends elsewhere"))
      cases := cases.push (probe "inert-axiom-record-as-advice" #[]
        { p with advice := p.advice.push sorryA } false none)
      cases := cases.push (probe "def-using-inert-axiom-as-advice" #[(dSorryA, dSorry)]
        { p with advice := p.advice.push dSorryA } false (some "an unwitnessed outside reference"))
      -- (ii) an unsafe record: directly as advice, and referenced by a safe advice record
      cases := cases.push (probe "unsafe-record-as-advice" #[(dUnsafeA, dUnsafe)]
        { p with advice := p.advice.push dUnsafeA } false
        (some "an opaque, unsafe or partial definition"))
      cases := cases.push (probe "safe-record-referencing-unsafe"
        #[(dUnsafeA, dUnsafe), (dRefsUnsafeA, dRefsUnsafe)]
        { p with advice := p.advice.push dRefsUnsafeA } false
        (some "safe constant references an unsafe constant"))
      -- (iii) an advice term naming a block (Muts) record's address
      cases := cases.push (probe "advice-term-names-a-block" #[(dBlockA, dBlock)]
        { p with advice := p.advice.push dBlockA } false none)
      -- the known benign case: a kind-1 path ending at a block record (an unused witness)
      if let some jList := jList? then
        cases := cases.push (probe "path-witness-ending-at-a-block" #[]
          { p with witnesses := p.witnesses.push (listB, 1, [jList + 1, 0], []) } true none)
  runCases "ixvm-family-graph-records" cases (jobs := 2)

/-- The two nested families; with `IX_FAMILY_TWIN` set, the second recursor record; with
`IX_FAMILY_INNER` set, the checks two family checks run on their advice. -/
def run (leanEnv : Lean.Environment) : IO UInt32 := do
  if (← IO.getEnv "IX_FAMILY_TWIN").isSome then return (← runTwin leanEnv)
  if (← IO.getEnv "IX_FAMILY_INNER").isSome then return (← runInner leanEnv)
  if (← IO.getEnv "IX_FAMILY_PROBE").isSome then return (← runProbe leanEnv)
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
