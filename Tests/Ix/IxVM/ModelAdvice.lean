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
  must accept the same claims with it. Likewise a model whose proofs use the
  quotient (`Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`, `Quot.sound`, the roles
  function extensionality comes from), which advice may reference.
* **No advice under user axioms** (third part): a claim whose axioms tree is
  not empty gets no model advice ("model advice: a claim with user axioms").
  The environments above declare Lean's compiler-trust axioms, which the
  default table binds as inert roles, so their claims name no user axiom and
  are accepted.
* **Verdicts at nested blocks the modeller models** (`nestedVerdicts`: an index
  domain that mentions a parameter, a reflexive field into a member): ι
  reductions through their recursors are accepted, and false ι and constructor
  equations, installed in Lean unchecked, are refused.
* **A tag enumeration is the compiled enumeration of its size** (`tagsCoincide`):
  the model of a block of `n` types holds a tag enumeration of `n` constructors
  and its recursor, encoded with the compiler's refs order and sharing
  (`IxVM.Model.sharedRecord`), so they are, by address, the records the compiler
  makes for a Lean enumeration of `n` constructors: `IxVMInd.Tri` for the block
  `TriA`/`TriB`/`TriC`, of types in `Type`. `Tri.rec` names `Tri` and its three
  constructors, so in the encoder's order of references the generated recursor
  would equal the compiled one for one order in 24. Checks of `TriA` and of
  `Tri.rec`, with the generated and the compiled records one, are accepted.
* **A model record is the compiled record** (`univTables`): every definition of
  a compiled environment, read by the kernel's reader and encoded again by the
  model's encoder, is the compiled record (tables, sharing, binder and let
  contracts), including `IxVMInd.univOrder`, whose two levels the encoder meets
  in the other order. The default table's evidence theorems are not compiler
  records (`kernel-pin-gen` closes and writes them, tables in first-use order),
  and no model record is one: they are counted, not compared.

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
(a member behind a definition), `EA` (a member only where whnf erases it), and `GA`, `GI`
and `GE` (formers declared at a definition). For each, ι reductions through the recursors are accepted, and false ι or constructor
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
  (`eaIotaFalse, false),
  (`gaIota, true),
  (`giIota, true),
  (`geIota, true)]

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

/-- The Lean enumerations, each with a member of a block whose tag enumeration
has its number of constructors. -/
def tagEnums : List (Lean.Name × Lean.Name) :=
  [(`IxVMInd.Tri, `IxVMInd.TriA)]

/-- The names `tagsCoincide` compiles: the enumerations and the blocks, with
their recursors. -/
def tagNames : Array Lean.Name :=
  #[`IxVMInd.Tri, `IxVMInd.Tri.rec, `IxVMInd.TriA, `IxVMInd.TriA.rec,
    `IxVMInd.Even, `IxVMInd.Even.rec]

/-- The definitions `univTables` compiles besides `tagNames`: `IxVMInd.univOrder`,
whose two levels the encoder meets in the order the compiler's table reverses, and
universe-polymorphic definitions whose closures hold many more. -/
def univNames : Array Lean.Name :=
  #[`IxVMInd.univOrder, `Function.comp, `List.map, `Prod.map, `List.foldl]

/-- The levels of a definition in the order the model's encoder meets them. -/
def levelsMet (nm : IxVM.Model.Names) (cv : Ix.Kernel.ConstantVal .anon)
    (v : Ix.Kernel.Expr .anon) : Array Ixon.Univ :=
  let run : IxVM.Model.EncM Unit := do
    let _ ← IxVM.Model.encExpr nm cv.levelParams (fun _ => none) cv.type
    let _ ← IxVM.Model.encExpr nm cv.levelParams (fun _ => none) v
  match run.run {} with
  | .ok (_, s) => s.univs
  | .error _ => #[]

/-- Each safe definition and theorem of `env` that the kernel's reader reads as one
declaration: its address, its compiled record without the binder-data section (the
model's encoder writes none), the record `IxVM.Model.encDecl` makes of the
declaration read, and the levels in the order the encoder met them. -/
def reencoded (env : Ixon.Env) :
    Except String (Array (Address × Ixon.Constant × Ixon.Constant × Array Ixon.Univ)) := do
  let some b := env.roleBinding | throw "no role binding"
  let some table := Ix.Kernel.RoleTable.ofBytes b.bytes | throw "the role table does not decode"
  let pre : Ix.Kernel.Reader.Prelude .anon ← Ix.Kernel.Reader.preludeFor table
  let mut records : Array (Address × Ixon.Constant) := #[]
  for (a, lc) in env.consts do
    if let some c := lc.get? then records := records.push (a, c)
  let cx : Ix.Kernel.Reader.Ctx .anon :=
    Ix.Kernel.Reader.contextOf table records env.blobs.toList (pre.records ++ pre.evidence) pre.blobs
      (fun _ => none) (Ix.Kernel.Admission.projectionAddress Address.blake3)
  let store : Std.HashMap Address Ixon.Constant := records.foldl (fun m (a, c) => m.insert a c) {}
  let nm : IxVM.Model.Names := { roles := table.bound.foldl (fun m (r, a) => m.insert r a) {} }
  let mut st := pre.state
  let mut out := #[]
  for a in Ixon.CheckOrder.wholeEnv table pre records do
    let some c := store[a]? | continue
    let .ok r := Ix.Kernel.Reader.readRecord cx st a c | continue
    st := st.commit r
    let .defn d := c.info | continue
    unless d.safety == .safe && d.kind != .opaq do continue
    let #[decl] := r.decls | continue
    let met := match decl with
      | .defnDecl cv v _ => levelsMet nm cv v
      | .thmDecl cv v => levelsMet nm cv v
      | _ => #[]
    let .ok e := IxVM.Model.encDecl nm decl | continue
    let some (_, c') := e.records[0]? | continue
    out := out.push (a, { c with binders := #[] }, c', met)
  return out

/-- The default table's evidence theorems (`Ix.Kernel.Reader.evidenceRecords`):
`kernel-pin-gen` closes each over its operation's dependency closure and writes its
record with the tables in first-use order, not in the compiler's form. No model
record is an evidence theorem. -/
def evidenceAddresses : Std.HashSet Address :=
  match Ix.Kernel.Reader.evidenceRecords with
  | .ok rs => rs.foldl (fun s (a, _) => s.insert a) {}
  | .error _ => {}

/-- **A model record is the compiled record.** `IxVMInd.univOrder`, whose levels the
encoder meets out of the table's order, re-encoded by the model's encoder, is the
compiled record, and so is every other definition of `env` the kernel's reader reads as
one declaration, except the default table's evidence theorems (`evidenceAddresses`),
which no compiler wrote: they are counted, with how many are the encoder's record once
put in the compiler's form (`IxVM.Model.renormalize`). Any other difference is a
failure, reported. -/
def univTables (env : Ixon.Env) : IO Bool := do
  let rows ← IO.ofExcept (reencoded env)
  let mut same := 0
  let mut multi := 0
  let mut reordered := 0
  let mut evidence := 0
  let mut evidenceForm := 0
  let mut univsDiffer : Array Address := #[]
  let mut otherDiffer : Array String := #[]
  for (a, c, c', met) in rows do
    if IxVM.Model.addressOf c == IxVM.Model.addressOf c' then
      same := same + 1
      if c.univs.size ≥ 2 then multi := multi + 1
      if met != c.univs then reordered := reordered + 1
    else if evidenceAddresses.contains a then
      evidence := evidence + 1
      if (match IxVM.Model.renormalize id c with
          | .ok r => IxVM.Model.addressOf r == IxVM.Model.addressOf c'
          | .error _ => false) then
        evidenceForm := evidenceForm + 1
    else if c.univs != c'.univs then
      univsDiffer := univsDiffer.push a
    else
      let parts := [("info", c.info == c'.info), ("sharing", c.sharing == c'.sharing),
        ("refs", c.refs == c'.refs)]
      otherDiffer := otherDiffer.push s!"{a} ({(parts.filter (!·.2)).map (·.1)})"
  let target := env.getAddr? (Ix.Name.fromLeanName `IxVMInd.univOrder)
  let targetOk := match rows.find? (some ·.1 == target) with
    | some (_, c, c', met) =>
      IxVM.Model.addressOf c == IxVM.Model.addressOf c' && c.univs.size == 2 && met != c.univs
    | none => false
  IO.println s!"[ixvm-model-advice] {rows.size} definitions re-encoded by the model's encoder: \
    {same} are the compiled record ({multi} with two levels or more, {reordered} met in another \
    order than the table's); {evidence} are evidence theorems ({evidenceForm} of them the encoder's record \
    in the compiler's form); \
    {univsDiffer.size} have another univs table, {otherDiffer.size} differ elsewhere"
  for a in univsDiffer.toList.take 10 do
    IO.eprintln s!"[ixvm-model-advice] another univs table than the compiled record's: {a}"
  for s in otherDiffer.toList.take 10 do
    IO.eprintln s!"[ixvm-model-advice] differs from the compiled record outside the univs table: {s}"
  unless targetOk do
    IO.eprintln "[ixvm-model-advice] IxVMInd.univOrder: the re-encoded record is not the compiled \
      one, or its levels are not met out of the table's order"
  return targetOk && univsDiffer.isEmpty && otherDiffer.isEmpty

/-- Each enumeration's compiled block and recursor are model records of `env`
(the generated tag enumeration and its recursor, by address). -/
def tagsCoincide (env : Ixon.Env) : IO Bool := do
  let mut ok := true
  for (enum, member) in tagEnums do
    let ty ← lookupAddr env enum
    let recA ← lookupAddr env (enum.str "rec")
    let block : Option Address := (env.getConst? ty).bind IxVM.Model.projectionBlock?
    let blockOk := block.any env.modelRecords.contains
    let recOk := env.modelRecords.contains recA
    unless blockOk && recOk do
      IO.eprintln s!"[ixvm-model-advice] the tag enumeration of {member}'s block is not \
        {enum}: block {if blockOk then "equal" else "different"}, recursor \
        {if recOk then "equal" else "different"}"
      ok := false
  if ok then
    IO.println s!"[ixvm-model-advice] the tag enumerations of the blocks of \
      {tagEnums.map (·.2)} are {tagEnums.map (·.1)}, block and recursor"
  return ok

/-- **Every advice record is the compiler's record for its declaration.** Each model
record of `env` holds the compiler's table invariant (`IxVM.Model.tablesCanonical`),
is unchanged by being put in the compiler's form again (`IxVM.Model.renormalize`), and
carries the section IxC's pass computes for it as it stands. At least one cites
another advice record that re-addressing moved (one with a section), so its refs table
is sorted by addresses it was given after encoding. -/
def adviceCanonical (env : Ixon.Env) (label : String) : IO Bool := do
  let advice := env.modelRecords.toArray
  let aset : Std.HashSet Address := advice.foldl (fun s (a, _) => s.insert a) {}
  let moved : Std.HashSet Address :=
    advice.foldl (fun s (a, c) => if c.binders.isEmpty then s else s.insert a) {}
  let mut bad : Array String := #[]
  let mut citers := 0
  for (a, c) in advice do
    unless IxVM.Model.tablesCanonical c do bad := bad.push s!"{a}: tables out of the compiler's order"
    match IxVM.Model.renormalize id c with
    | .ok c' => unless { c' with binders := c.binders } == c do
        bad := bad.push s!"{a}: not in the compiler's form"
    | .error e => bad := bad.push s!"{a}: {e}"
    if c.refs.any moved.contains then citers := citers + 1
  let support : Array (Address × Ixon.Constant) := env.consts.fold (init := #[]) fun out a lc =>
    if aset.contains a then out else match lc.get? with
      | some c => out.push (a, c)
      | none => out
  let blobs := env.modelBlobs.fold (init := env.blobs) fun m a b => m.insert a b
  let hints := env.modelHints.fold (init := env.anonHints) fun m a h => m.insert a h
  let chosen ← IO.ofExcept (IxVM.RecordSections.chosenOf env)
  let sections ← IO.ofExcept
    (IxVM.RecordSections.sectionsOf advice support blobs hints chosen (models := aset))
  for (a, c) in advice do
    unless sections.getD a #[] == c.binders do bad := bad.push s!"{a}: another section than IxC's"
  for b in bad.toList.take 10 do IO.eprintln s!"[ixvm-model-advice] {label}: advice record {b}"
  IO.println s!"[ixvm-model-advice] {label}: {advice.size} advice records, {bad.size} not the \
    compiler's; {citers} cite an advice record re-addressing moved"
  return bad.isEmpty && citers > 0

/-- Every theorem's value under `let _ : Nat := 0`: a different proof of the
same statement, so a different record. -/
def tweakProofs : Ix.Kernel.Declaration .anon → Ix.Kernel.Declaration .anon
  | .thmDecl cv v => .thmDecl cv (.letE (.const (.role .nat) []) (.lit (.natVal 0)) v default)
  | d => d

namespace QuotModel

def roleC (r : Ix.Kernel.Role) (us : List Ix.Kernel.Level) : Ix.Kernel.Expr .anon := .const (.role r) us
def one : Ix.Kernel.Level := .succ .zero
def natE : Ix.Kernel.Expr .anon := roleC .nat []
def zeroE : Ix.Kernel.Expr .anon := .lit (.natVal 0)
/-- `@Eq.{1} Nat`, the relation. -/
def eqNat : Ix.Kernel.Expr .anon := .app (roleC .eq [one]) natE
/-- `@Quot.{1} Nat (@Eq Nat)`. -/
def quotE : Ix.Kernel.Expr .anon := Ix.Kernel.Expr.mkAppN (roleC .quot [one]) [natE, eqNat]
/-- `@Quot.mk.{1} Nat (@Eq Nat) x`. -/
def mkQ (x : Ix.Kernel.Expr .anon) : Ix.Kernel.Expr .anon :=
  Ix.Kernel.Expr.mkAppN (roleC .quotMk [one]) [natE, eqNat, x]
/-- `@Eq.{1} (Quot (@Eq Nat)) a b`. -/
def eqQ (a b : Ix.Kernel.Expr .anon) : Ix.Kernel.Expr .anon :=
  Ix.Kernel.Expr.mkAppN (roleC .eq [one]) [quotE, a, b]

/-- `v` under three `let`s whose values use the whole quotient package at `Nat`
and `Eq`: `Quot.sound (Eq.refl 0) : Quot.mk _ 0 = Quot.mk _ 0`,
`Quot.lift id (λ a b h, h) (Quot.mk _ 0) : Nat` and
`Quot.ind (β := λ q, q = q) (λ a, Eq.refl _) (Quot.mk _ 0) : Quot.mk _ 0 = Quot.mk _ 0`.
Every term is closed, so `v` needs no lifting. -/
def lets (v : Ix.Kernel.Expr .anon) : Ix.Kernel.Expr .anon :=
  let sound := Ix.Kernel.Expr.mkAppN (roleC .quotSound [one])
    [natE, eqNat, zeroE, zeroE, Ix.Kernel.Expr.mkAppN (roleC .eqRefl [one]) [natE, zeroE]]
  let respects : Ix.Kernel.Expr .anon :=
    .lam natE (.lam natE (.lam (Ix.Kernel.Expr.mkAppN (roleC .eq [one]) [natE, .bvar 1, .bvar 0])
      (.bvar 0) default) default) default
  let lift := Ix.Kernel.Expr.mkAppN (roleC .quotLift [one, one])
    [natE, eqNat, natE, .lam natE (.bvar 0) default, respects, mkQ zeroE]
  let ind := Ix.Kernel.Expr.mkAppN (roleC .quotInd [one])
    [natE, eqNat, .lam quotE (eqQ (.bvar 0) (.bvar 0)) default,
     .lam natE (Ix.Kernel.Expr.mkAppN (roleC .eqRefl [one]) [quotE, mkQ (.bvar 0)]) default, mkQ zeroE]
  .letE (eqQ (mkQ zeroE) (mkQ zeroE)) sound
    (.letE natE lift (.letE (eqQ (mkQ zeroE) (mkQ zeroE)) ind v default) default) default

/-- The quotient roles. -/
def roles : List Ix.Kernel.Role := [.quot, .quotMk, .quotLift, .quotInd, .quotSound]

end QuotModel

/-- Every theorem's value under `QuotModel.lets`: a different proof of the same
statement whose record names the five quotient roles, which advice may reference
(function extensionality is a theorem from them). -/
def quotProofs : Ix.Kernel.Declaration .anon → Ix.Kernel.Declaration .anon
  | .thmDecl cv v => .thmDecl cv (QuotModel.lets v)
  | d => d

/-- The claims run with the quotient-using model: a mutual and a nested block. -/
def quotNames : List String := ["IxVMInd.Even.rec", "IxVMInd.Tree.rec"]

def run (lenv : Lean.Environment) : IO UInt32 := do
  let names := modeledNames.map nameOfString
  let missing := (names ++ tagNames.toList ++ univNames.toList).filter (!lenv.constants.contains ·)
  unless missing.isEmpty do
    IO.eprintln s!"[ixvm-model-advice] not in the environment: {missing}"
    return 1
  let env ← loadSharedIxonEnv names.toArray lenv
  let digestOk ← digestUnchanged env names
  let tagEnv ← loadSharedIxonEnv (tagNames ++ univNames) lenv
  let tagsOk ← tagsCoincide tagEnv
  let univsOk ← univTables tagEnv
  let adviceOk := (← adviceCanonical env "modeled blocks") && (← adviceCanonical tagEnv "tag blocks")
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
  -- a model whose proofs name the quotient roles: every block gets a payload, and
  -- the quotient roles are among the outside references, as basis references
  let (quotEnv, repQ) ← IO.ofExcept
    (IxVM.Model.generateReport { withoutModels env with modelsAttached := false } quotProofs)
  let quotAddrs : List Address := match Ix.Kernel.Reader.defaultTable with
    | .ok t => t.bound.toList.filterMap fun (r, a) => if QuotModel.roles.contains r then some a else none
    | .error _ => []
  let mut quotOk := quotAddrs.length == QuotModel.roles.length
  let mut quotBlocks := 0
  for (b, r) in repQ.blocks do
    match r with
    | .error e =>
      IO.eprintln s!"[ixvm-model-advice] block {b} has no quotient-using model: {e}"
      quotOk := false
    | .ok (_, outside) =>
      if quotAddrs.all (fun q => outside.any (· == (q, 0))) then quotBlocks := quotBlocks + 1
  IO.println s!"[ixvm-model-advice] {quotBlocks} of {repQ.blocks.size} quotient-using models name \
    the five quotient roles as basis references"
  unless quotBlocks > 0 do quotOk := false
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
    (names.map (mkCase tweaked "a different valid model")) ++
    (quotNames.map fun n => mkCase quotEnv "a model whose proofs use the quotient" (nameOfString n)) ++
    [underAxiom] ++
    [mkCase tagEnv "its tag enumeration is Tri" `IxVMInd.TriA,
     mkCase tagEnv "the recursor of TriA's tag enumeration" `IxVMInd.Tri.rec]
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
  return if digestOk && differ && quotOk && tagsOk && univsOk && adviceOk && rc == 0 then 0 else 1

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
  | .app a b | .lam a b | .all a b => (prjIdxsExpr a).union (prjIdxsExpr b)
  | .letE _ _ t v b => ((prjIdxsExpr t).union (prjIdxsExpr v)).union (prjIdxsExpr b)
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
