import Ix.Meta
import Ix.Check
import Ix.KernelCheck
import Ix.Compile.BinderData
import Ix.Shard.Environment
import Ix.IxVM.Model
import Ix.IxVM.ClaimHarness
import Ix.ClaimContext
import Ix.AssumptionTree
import Tests.Ix.IxVM.Harness
import Tests.Ix.Kernel.SourceIngressCompare
import Tests.Ix.IxVM.SyntheticRegressionsDefs

/-! # Corpus-driven and synthetic 3-way IxVM / IxCK regressions

End-to-end regressions covering:
1. **`ix shard extract` modeled-family closure (`extractCases`)**: extracting a leaf that
   references a modeled inductive (`autoParam` → `Lean.Syntax`, 8-member mutual+nested
   `AstExpr`, and nested-in-nested `NestedInNested`) without naming its recursors carries
   the recursor families and container recursors needed by `IxVM.Model` and `ix check`.
2. **Lean 4.34 `native_decide` inert compiler-trust classification (`nativeDecideCases`)**:
   per-theorem `_native.native_decide.ax_*` axioms are classified as inert compiler-trust
   axioms rather than custom user axioms, so `native_decide` theorems and their dependents
   are set aside by `inertUsers` and shards touching modeled blocks check under
   `ctx.axioms = none`, while explicit custom user axioms stay in `ClaimContext.userAxioms`.
3. **Dead-`let` out-of-range universe parameters (`deadLetUnivCases`)**: `lvls = 0`
   definitions, theorems, opaques, types, and inductive constructors carrying an undeclared
   universe parameter inside an unused `let` are rejected by BOTH IxCK and IxVM.
4. **Large multi-container & mutual AST and synthetic positive 3-way regressions
   (`positiveCases`)**: 5-container `MultiContDoc`, 8-member 19-motive mutual+nested
   `AstMod`..`AstType`, `NestedInMut`, `NestedInNested`, `TriM1`..`TriM3`, `KS1Clean`/
   `KS2Clean`/`kitchenSinkCleanThm`, `AliasParamDep`, `Nat.pow` at `2^24`, and 4-byte
   UTF-8 `String.ofList` — all verified accepted by BOTH IxCK and IxVM.
5. **Semantic `imax` universe algebra (`imaxCases`)**: 5 valid `imax` identities accepted
   by BOTH IxCK and IxVM, paired with 2 false negative controls rejected by BOTH.
6. **Adversarial boundary controls (`adversarialCases`)**: forged large eliminator on a
   2-constructor `Prop` inductive (UTF-8, non-canonical `Nat` literal blobs, unused-sharing
   unsafe refs, and the retired `resource-v1` claim are covered by `Exploits`, `Eval`,
   `SafeReferences`, and `Codec`).
-/

namespace Tests.Ix.IxVM.SyntheticRegressions

open IxVM.ClaimHarness
open Tests.Ix.IxVM

abbrev E := Ixon.Expr

private def storeNamed (env : Ixon.Env) (nm : Lean.Name) (c : Ixon.Constant)
    (hint : Lean.ReducibilityHints := .regular 0) : Ixon.Env × Address :=
  let a := Address.blake3 (Ixon.ser c)
  let isIndOrRec := match c.info with
    | .recr _ | .iPrj _ | .cPrj _ | .rPrj _ => true
    | .muts ms => ms.any fun
      | .indc _ | .recr _ => true
      | .defn _ => false
    | _ => false
  let env := if isIndOrRec then env.storeConst a c else env.storeConstKeepModels a c
  let env := match c.info with
    | .defn _ | .dPrj _ => { env with anonHints := env.anonHints.insert a hint }
    | _ => env
  let env := env.registerName (Ix.Name.fromLeanName nm)
    { addr := a, constMeta := .empty, hints := hint }
  (env, a)

private def storeNamedAnnot (env : Ixon.Env) (nm : Lean.Name) (c : Ixon.Constant)
    (hint : Lean.ReducibilityHints := .regular 0) : IO (Ixon.Env × Address) := do
  let sup ← IO.ofExcept (Ix.Compile.BinderData.recordsOf env)
  let (env0, a0) := storeNamed env nm c hint
  let view : IxVM.PwHints.View := {
    records := #[(a0, c)], support := sup, blobs := env0.blobs, hints := env0.anonHints,
    table := env0.roleBinding.map (·.bytes) }
  let k ← IO.ofExcept (IxVM.PwHints.KernelEnv.ofView view)
  let (tables, _) := IxVM.PwHints.annotateKernel k (taint := false)
  let blocks := (tables.find? (·.1 == a0)).map (·.2) |>.getD #[]
  let sec ← IO.ofExcept (Ix.Compile.BinderData.sectionOf c blocks)
  pure (storeNamed env nm { c with binders := sec } hint)

private def checkIxcOutcome (verdicts : Std.HashMap (Ix.Kernel.Key .source) (String × String))
    (nm : Lean.Name) (expectAccept : Bool) (expectReasonSubstr : Option String := none) :
    IO Unit := do
  let key := Ix.LeanIngress.ingressKey (Ix.Name.fromLeanName nm)
  match verdicts[key]? with
  | none =>
    throw (IO.userError s!"[ixvm-synthetic-regressions] IxCK produced no verdict for {nm}")
  | some (outcome, reason) =>
    if expectAccept then
      unless outcome == "accept" do
        throw (IO.userError s!"[ixvm-synthetic-regressions] IxCK unexpectedly did not accept {nm}: \
          {outcome} ({reason})")
    else
      if outcome == "accept" then
        throw (IO.userError s!"[ixvm-synthetic-regressions] IxCK unexpectedly ACCEPTED {nm}!")
      if let some needle := expectReasonSubstr then
        unless (reason.splitOn needle).length > 1 do
          throw (IO.userError s!"[ixvm-synthetic-regressions] IxCK rejected {nm} with '{reason}', \
            expected substring '{needle}'")

/-! ## 1. `ix shard extract` modeled-family & container-recursor closure -/

private def extractCases (leanEnv : Lean.Environment) : IO (Array Builder) := do
  let env ← loadSharedIxonEnv
    #[`SynReg.autoParamLeaf, `SynReg.usesAstType, `SynReg.AstExpr.rec,
      `SynReg.NestedInNested, `SynReg.NestedInNested.rec, `SynReg.MultiContDoc.rec]
    leanEnv
  let fullBytes ← IO.ofExcept (Ixon.serEnv env)
  IO.FS.withTempDir fun dir => do
    let fullPath := (dir / "full.ixe").toString
    let autoPath := (dir / "auto.ixe").toString
    let modeledPath := (dir / "modeled.ixe").toString
    IO.FS.writeBinFile fullPath fullBytes
    -- Extract ONLY `SynReg.autoParamLeaf` (touches `Lean.Syntax` via `autoParam`, naming no rec).
    Ix.KernelCheck.rsEnvExtractFFI fullPath #["SynReg.autoParamLeaf"] autoPath true
    let autoRaw ← IO.ofExcept (Ixon.deEnvAnon (← IO.FS.readBinFile autoPath))
    let (autoEnv, autoRep) ← IO.ofExcept
      (IxVM.Model.generateReport (← IO.ofExcept (withDefaultRoleBinding autoRaw)))
    if autoRep.blocks.isEmpty then
      throw (IO.userError "[ixvm-synthetic-regressions] extract(autoParamLeaf): expected modeled \
        Lean.Syntax block in extracted env")
    for (b, r) in autoRep.blocks do
      match r with
      | .ok _ => pure ()
      | .error e =>
        throw (IO.userError s!"[ixvm-synthetic-regressions] extract(autoParamLeaf): model advice \
          failed for block {b}: {e}")
    let autoLeafA ← lookupAddr autoEnv `SynReg.autoParamLeaf
    let autoCtx ← IO.ofExcept (Ix.ClaimContext.ofEnv autoEnv true)
    let autoClaimable := claimableConsts autoEnv

    -- Extract ONLY `SynReg.usesAstType` and `SynReg.NestedInNested` (neither names any `.rec`).
    Ix.KernelCheck.rsEnvExtractFFI fullPath
      #["SynReg.usesAstType", "SynReg.NestedInNested"] modeledPath true
    let modRaw ← IO.ofExcept (Ixon.deEnvAnon (← IO.FS.readBinFile modeledPath))
    let (modEnv, modRep) ← IO.ofExcept
      (IxVM.Model.generateReport (← IO.ofExcept (withDefaultRoleBinding modRaw)))
    if modRep.blocks.size < 3 then
      throw (IO.userError s!"[ixvm-synthetic-regressions] extract(usesAstType,NestedInNested): \
        expected >= 3 modeled blocks (AstMod, NestedInNested, RoseCont), got {modRep.blocks.size}")
    for (b, r) in modRep.blocks do
      match r with
      | .ok _ => pure ()
      | .error e =>
        throw (IO.userError s!"[ixvm-synthetic-regressions] extract(usesAstType,NestedInNested): \
          model advice failed for block {b}: {e}")
    let usesAstA ← lookupAddr modEnv `SynReg.usesAstType
    let nestNestA ← lookupAddr modEnv `SynReg.NestedInNested
    let modCtx ← IO.ofExcept (Ix.ClaimContext.ofEnv modEnv true)
    IO.println s!"[ixvm-synthetic-regressions] extract checks passed \
      (autoParamLeaf: {autoRep.blocks.size} modeled block(s), \
      usesAstType+NestedInNested: {modRep.blocks.size} modeled block(s))"
    return #[
      fun _ => Case.ofClaim "extract-autoparam-leaf-check" autoEnv
        (.check autoCtx autoLeafA none) {} true,
      fun _ => do
        let (_, witness) ← buildShardCheckEnvWitness autoEnv autoClaimable (assumeBinding := true)
        return { label := "extract-autoparam-leaf-shard-checkEnv", accept := true, witness },
      fun _ => Case.ofClaim "extract-ast-type-without-recs" modEnv
        (.check modCtx usesAstA none) {} true,
      fun _ => Case.ofClaim "extract-nested-in-nested-without-recs" modEnv
        (.check modCtx nestNestA none) {} true]

/-! ## 2. Lean 4.34 `native_decide` inert compiler-trust classification -/

private def nativeDecideCases (leanEnv : Lean.Environment) : IO (Array Builder) := do
  -- Environment mixing `native_decide` with `autoParam` (modeled `Lean.Syntax`), no user axioms.
  let env ← loadSharedIxonEnv #[`SynReg.nativeDecideDownstream, `SynReg.autoParamLeaf] leanEnv
  let autoA ← lookupAddr env `SynReg.autoParamLeaf
  let ndProofA ← lookupAddr env `SynReg.nativeDecideProof
  let ndDownA ← lookupAddr env `SynReg.nativeDecideDownstream
  let uax := Ix.ClaimContext.userAxioms env
  unless uax.isEmpty do
    throw (IO.userError s!"[ixvm-synthetic-regressions] native_decide env reported {uax.size} \
      user axiom(s); expected 0")
  let ctx ← IO.ofExcept (Ix.ClaimContext.ofEnv env true)
  unless ctx.axioms.isNone do
    throw (IO.userError "[ixvm-synthetic-regressions] native_decide env context unexpectedly has \
      non-empty axioms tree")
  let inert := inertUsers env
  unless inert.contains ndProofA && inert.contains ndDownA do
    throw (IO.userError "[ixvm-synthetic-regressions] inertUsers missed nativeDecideProof or \
      nativeDecideDownstream")
  if inert.contains autoA then
    throw (IO.userError "[ixvm-synthetic-regressions] inertUsers spuriously marked autoParamLeaf")
  unless (Ix.Check.seedError? env inert "SynReg.nativeDecideDownstream" ndDownA).isSome do
    throw (IO.userError "[ixvm-synthetic-regressions] seedError? failed to refuse \
      nativeDecideDownstream")
  let allBlocks : Array Address := env.consts.fold (init := #[]) fun acc a lc =>
    match lc.get? with
    | some c =>
      let blk := c.ownerAt a
      if acc.contains blk then acc else acc.push blk
    | none => acc
  let owned := Ix.Shard.ownedConstsForBlocks env allBlocks
  unless owned.contains autoA && !owned.contains ndProofA && !owned.contains ndDownA do
    throw (IO.userError "[ixvm-synthetic-regressions] ownedConstsForBlocks did not set aside \
      native_decide constants while keeping autoParamLeaf")

  -- Control: environment with BOTH `native_decide` and an explicit custom user axiom.
  let envMixed ← loadSharedIxonEnv
    #[`SynReg.nativeDecideDownstream, `SynReg.usesCustomUserAx] leanEnv
  let customAxA ← lookupAddr envMixed `SynReg.customUserAx
  let ndMixedProofA ← lookupAddr envMixed `SynReg.nativeDecideProof
  let ndMixedDownA ← lookupAddr envMixed `SynReg.nativeDecideDownstream
  let uaxMixed := Ix.ClaimContext.userAxioms envMixed
  unless uaxMixed == #[customAxA] do
    throw (IO.userError s!"[ixvm-synthetic-regressions] mixed env userAxioms = {uaxMixed}, \
      expected #[customUserAx]")
  let inertMixed := inertUsers envMixed
  unless !inertMixed.contains customAxA &&
      inertMixed.contains ndMixedProofA && inertMixed.contains ndMixedDownA do
    throw (IO.userError "[ixvm-synthetic-regressions] mixed env inertUsers misclassified \
      customUserAx or native_decide")

  IO.println "[ixvm-synthetic-regressions] native_decide inert-classification host checks passed"
  return #[
    -- Shard over `autoParamLeaf` + `native_decide` sets aside `native_decide` and checks modeled
    -- `Lean.Syntax` cleanly under `ctx.axioms = none`.
    fun _ => do
      let (claim, witness) ← buildShardCheckEnvWitness env #[autoA, ndProofA, ndDownA]
        (assumeBinding := true)
      match claim with
      | .checkEnv c _ _ =>
        if c.axioms.isSome then throw "shard claim unexpectedly carried user axioms"
      | _ => throw "expected checkEnv claim"
      return { label := "native-decide-shard-with-modeled-syntax", accept := true, witness },
    -- Direct claim targeting the `native_decide` theorem under `ctx.axioms = none` is still
    -- rejected in-circuit.
    fun _ => Case.ofClaim "native-decide-direct-check-rejected" env
      (.check ctx ndDownA none) {} false
      (some "an axiom that is not one of Lean's standard axioms")]

/-! ## 3. Dead-`let` out-of-range universe parameters (IxCK + IxVM) -/

private def deadLetUnivCases (leanEnv : Lean.Environment) : IO (Array Builder) := do
  let env ← loadSharedIxonEnv #[``Nat, ``Nat.zero, ``True, ``True.intro] leanEnv
  let natA ← lookupAddr env ``Nat
  let zeroA ← lookupAddr env ``Nat.zero
  let trueA ← lookupAddr env ``True
  let introA ← lookupAddr env ``True.intro
  let deadVal (r : UInt64) : E := .leanLet false (.sort 1) (.sort 0) (.ref r #[])
  let univsOob : Array Ixon.Univ := #[.var 99, .succ (.var 99)]
  let univsOobInd : Array Ixon.Univ := #[.var 99, .succ (.var 99), .succ .zero]

  -- `lvls = 0` definition value with dead `let` mentioning `Param 99`
  let (env, deadLetDefnValA) := storeNamed env `SynReg.Raw.deadLetDefnVal
    ⟨.defn ⟨.defn, .safe, {}, 0, .ref 0 #[], deadVal 1⟩, #[], #[natA, zeroA], univsOob, #[]⟩
  -- `lvls = 0` theorem value with dead `let` mentioning `Param 99`
  let (env, deadLetThmValA) := storeNamed env `SynReg.Raw.deadLetThmVal
    ⟨.defn ⟨.thm, .safe, {}, 0, .ref 0 #[], deadVal 1⟩, #[], #[trueA, introA], univsOob, #[]⟩
  -- `lvls = 0` definition type with dead `let` mentioning `Param 99`
  let (env, deadLetDefnTypeA) := storeNamed env `SynReg.Raw.deadLetDefnType
    ⟨.defn ⟨.defn, .safe, {}, 0, deadVal 0, .ref 1 #[]⟩, #[], #[natA, zeroA], univsOob, #[]⟩
  -- `lvls = 0` opaque value with dead `let` mentioning `Param 99`
  let (env, deadLetOpaqueValA) := storeNamed env `SynReg.Raw.deadLetOpaqueVal
    ⟨.defn ⟨.opaq, .safe, {}, 0, .ref 0 #[], deadVal 1⟩, #[], #[natA, zeroA], univsOob, #[]⟩
  -- `lvls = 0` inductive constructor with dead `let` mentioning `Param 99`
  let ctorOob : E := .leanLet false (.sort 1) (.sort 0) (.recur 0 #[])
  let (env, deadLetIndBlockA) := storeNamed env `SynReg.Raw.deadLetIndBlock
    ⟨.muts #[.indc ⟨false, 0, 0, 0, .sort 2,
      #[⟨false, 0, 0, 0, 0, .inherited, ctorOob⟩]⟩], #[], #[], univsOobInd, #[]⟩
  let (env, deadLetIndA) := storeNamed env `SynReg.Raw.deadLetInd
    ⟨.iPrj ⟨0, deadLetIndBlockA⟩, #[], #[], #[], #[]⟩
  let (env, _) := storeNamed env `SynReg.Raw.deadLetInd.mk
    ⟨.cPrj ⟨0, 0, deadLetIndBlockA⟩, #[], #[], #[], #[]⟩

  -- Verify IxCK rejects ALL 5!
  let verdicts ← Tests.Ix.Kernel.SourceIngressCompare.ixonVerdicts env
  checkIxcOutcome verdicts `SynReg.Raw.deadLetDefnVal false (some "undeclared universe parameter")
  checkIxcOutcome verdicts `SynReg.Raw.deadLetThmVal false (some "undeclared universe parameter")
  checkIxcOutcome verdicts `SynReg.Raw.deadLetDefnType false (some "undeclared universe parameter")
  checkIxcOutcome verdicts `SynReg.Raw.deadLetOpaqueVal false (some "undeclared universe parameter")
  checkIxcOutcome verdicts `SynReg.Raw.deadLetInd false
  IO.println "[ixvm-synthetic-regressions] IxCK rejected all 5 dead-let OOB universe param probes"

  let ctx ← IO.ofExcept (Ix.ClaimContext.ofEnv env true)
  let msg := some "universe param index out of range"
  return #[
    fun _ => Case.ofClaim "dead-let-oob-lvl-defn-val" env (.check ctx deadLetDefnValA none) {} false msg,
    fun _ => Case.ofClaim "dead-let-oob-lvl-ind-ctor" env (.check ctx deadLetIndA none) {} false msg,
    fun _ => Case.ofClaim "dead-let-oob-lvl-thm-val" env (.check ctx deadLetThmValA none) {} false msg,
    fun _ => Case.ofClaim "dead-let-oob-lvl-defn-type" env (.check ctx deadLetDefnTypeA none) {} false msg,
    fun _ => Case.ofClaim "dead-let-oob-lvl-opaque-val" env (.check ctx deadLetOpaqueValA none) {} false msg]

/-! ## 4. Large multi-container/mutual AST & synthetic positive 3-way regressions -/

private def positiveNames : Array Lean.Name := #[
  `SynReg.MultiContDoc.rec,
  `SynReg.multiContDocIota,
  `SynReg.AstExpr.rec,
  `SynReg.astExprIota,
  `SynReg.NestedInMut.rec,
  `SynReg.nestedInMutIota,
  `SynReg.NestedInNested.rec,
  `SynReg.nestedInNestedIota,
  `SynReg.TriM1.rec,
  `SynReg.triM1Iota,
  `SynReg.KS1Clean.rec,
  `SynReg.kitchenSinkCleanThm,
  `SynReg.AliasParamDep.rec,
  `SynReg.aliasParamDepThm,
  `SynReg.natPowAtCap,
  `SynReg.strUtf8LitEqOfList]

private def positiveCases (leanEnv : Lean.Environment) : IO (Array Builder) := do
  let env ← loadSharedIxonEnv positiveNames leanEnv
  -- Confirm `IxVM.Model.generateReport` models the multi-container and 8-member AST blocks cleanly.
  let (env, rep) ← IO.ofExcept (IxVM.Model.generateReport { env with modelsAttached := false })
  let mut maxContainerRecs := 0
  let mut maxAdviceRecs := 0
  for (b, r) in rep.blocks do
    match r with
    | .ok (nRecs, outside) =>
      let cRecs := (outside.filter (·.2 == 2)).size
      maxContainerRecs := max maxContainerRecs cRecs
      maxAdviceRecs := max maxAdviceRecs nRecs
    | .error e =>
      throw (IO.userError s!"[ixvm-synthetic-regressions] positive modeled block {b} failed: {e}")
  -- `MultiContDoc` nests through `List` (role-bound), `Array`, `Option`, `Prod`, and `Sum`
  -- (4 non-role kind-2 container recursors alongside `List.rec`).
  unless maxContainerRecs ≥ 4 do
    throw (IO.userError s!"[ixvm-synthetic-regressions] expected >= 4 non-role container recursors \
      on MultiContDoc, observed max {maxContainerRecs}")
  -- Verify IxCK accepts every single positive regression!
  let verdicts ← Tests.Ix.Kernel.SourceIngressCompare.ixonVerdicts env
  for nm in positiveNames do
    checkIxcOutcome verdicts nm true
  IO.println s!"[ixvm-synthetic-regressions] IxCK accepted all {positiveNames.size} positive \
    regressions (max {maxContainerRecs} container recs, max {maxAdviceRecs} advice records)"

  let ctx ← IO.ofExcept (Ix.ClaimContext.ofEnv env true)
  let mut cases : Array Builder := #[]
  for nm in positiveNames do
    let a ← lookupAddr env nm
    cases := cases.push fun _ => Case.ofClaim s!"pos-{nm}" env (.check ctx a none) {} true
  return cases

/-! ## 5. Semantic `imax` universe algebra (IxCK + IxVM) -/

private def imaxThm (eqA eqReflA : Address) (lvls : UInt64) (l1 l2 : Ixon.Univ) : Ixon.Constant :=
  let univs : Array Ixon.Univ := #[l1, l2, .succ l1, .succ (.succ l1)]
  let ty : E := .app (.app (.app (.ref 0 #[3]) (.sort 2)) (.sort 0)) (.sort 1)
  let val : E := .app (.app (.ref 1 #[3]) (.sort 2)) (.sort 0)
  ⟨.defn ⟨.thm, .safe, {}, lvls, ty, val⟩, #[], #[eqA, eqReflA], univs, #[]⟩

private def imaxCases (leanEnv : Lean.Environment) : IO (Array Builder) := do
  let env ← loadSharedIxonEnv #[``Eq, ``Eq.refl] leanEnv
  let eqA ← lookupAddr env ``Eq
  let eqReflA ← lookupAddr env ``Eq.refl
  let u : Ixon.Univ := .var 0
  let v : Ixon.Univ := .var 1
  let w : Ixon.Univ := .var 2
  let specs : Array (String × Lean.Name × UInt64 × Ixon.Univ × Ixon.Univ × Bool) := #[
    ("imax-distL", `SynReg.Raw.imaxDistL, 3,
      .imax (.max u v) w, .max (.imax u w) (.imax v w), true),
    ("imax-distR", `SynReg.Raw.imaxDistR, 3,
      .imax u (.max v w), .max (.imax u v) (.imax u w), true),
    ("imax-chain", `SynReg.Raw.imaxChain, 3,
      .imax u (.imax v w), .max (.imax u w) (.imax v w), true),
    ("max-imax-sym", `SynReg.Raw.maxImaxSym, 2,
      .max (.imax u v) (.imax v u), .max u v, true),
    ("imax-absorb", `SynReg.Raw.imaxAbsorb, 1,
      .imax u (.imax (.succ u) u), .imax (.succ u) u, true),
    ("bad-imax-succ", `SynReg.Raw.badImaxSucc, 1,
      .imax (.succ u) u, .succ u, false),
    ("bad-imax-max", `SynReg.Raw.badImaxMax, 2,
      .imax u v, .max u v, false)]
  let mut env := env
  let mut addrs : Array (String × Lean.Name × Address × Bool) := #[]
  for (label, nm, lvls, l1, l2, ok) in specs do
    let (env', a) := storeNamed env nm (imaxThm eqA eqReflA lvls l1 l2)
    env := env'
    addrs := addrs.push (label, nm, a, ok)
  let verdicts ← Tests.Ix.Kernel.SourceIngressCompare.ixonVerdicts env
  for (_, nm, _, ok) in addrs do
    checkIxcOutcome verdicts nm ok
  IO.println "[ixvm-synthetic-regressions] IxCK agreed on all 7 semantic imax cases (5 accept, 2 reject)"
  let ctx ← IO.ofExcept (Ix.ClaimContext.ofEnv env true)
  return addrs.map fun (label, _, a, ok) => fun _ =>
    Case.ofClaim label env (.check ctx a none) {} ok
      (if ok then none else some "inferred type is not def-eq")

/-! ## 6. High-value adversarial boundary controls -/

private def adversarialCases (leanEnv : Lean.Environment) : IO (Array Builder) := do
  let env ← loadSharedIxonEnv
    #[`SynReg.TwoProp, `SynReg.TwoProp.left, `SynReg.TwoProp.right] leanEnv
  let twoA ← lookupAddr env `SynReg.TwoProp
  let twoLA ← lookupAddr env `SynReg.TwoProp.left
  let twoRA ← lookupAddr env `SynReg.TwoProp.right

  -- Forged large eliminator (`lvls = 1`, `Sort u` motive) on 2-ctor `Prop` inductive `TwoProp`.
  let motiveDom : E := .leanAll (.ref 0 #[]) (.sort 0)
  let minorLDom : E := .app (.var 0) (.ref 1 #[])
  let minorRDom : E := .app (.var 1) (.ref 2 #[])
  let recTy : E := .leanAll motiveDom (.leanAll minorLDom (.leanAll minorRDom
    (.leanAll (.ref 0 #[]) (.app (.var 3) (.var 0)))))
  let mkRule (i : UInt64) : Ixon.RecursorRule :=
    { fields := 0, rhs := .leanLam motiveDom (.leanLam minorLDom (.leanLam minorRDom (.var i))) }
  let forgedLargeRec : Ixon.Constant :=
    ⟨.recr ⟨false, false, 1, 0, 0, 1, 2, recTy, #[mkRule 1, mkRule 0]⟩,
      #[], #[twoA, twoLA, twoRA], #[.var 0], #[]⟩
  let (env, forgedLargeRecA) ← storeNamedAnnot env `SynReg.Raw.forgedLargeRec forgedLargeRec
  -- Verify IxCK also rejects the forged large eliminator.
  let forgedLargeVerdicts ← Tests.Ix.Kernel.SourceIngressCompare.ixonVerdicts env
  checkIxcOutcome forgedLargeVerdicts `SynReg.Raw.forgedLargeRec false

  let ctx ← IO.ofExcept (Ix.ClaimContext.ofEnv env true)
  return #[
    fun _ => Case.ofClaim "forged-large-elim-on-2ctor-prop" env (.check ctx forgedLargeRecA none) {} false
      (some "recursor universe-parameter count is not its block's plus the elimination parameter")]

def run (leanEnv : Lean.Environment) : IO UInt32 := do
  let cases :=
    (← extractCases leanEnv) ++
    (← nativeDecideCases leanEnv) ++
    (← deadLetUnivCases leanEnv) ++
    (← positiveCases leanEnv) ++
    (← imaxCases leanEnv) ++
    (← adversarialCases leanEnv)
  runCases "ixvm-synthetic-regressions" cases

end Tests.Ix.IxVM.SyntheticRegressions
