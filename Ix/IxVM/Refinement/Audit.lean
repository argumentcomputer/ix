import Ix.IxVM.Refinement.Statement
import Ix.IxVM.Refinement.TagNWide
import Ix.IxVM.Refinement.Deserialize
import IxC.Kernel.Audit.Axioms

/-! # The IxVM ↔ IxC refinement statement, frozen

`#print` freezes every statement (`def … : Prop`) of
`Ix.IxVM.Refinement.Statement`, every definition they read from
`Ix.IxVM.Refinement.Claim`, the observed semantics' records
(`Aiur.Generic.Observe`) and the policy forms of IxC's acceptance
(`Ix.Cert.IxonAcceptsRefUnder`, `Ix.Kernel.Cached.AcceptsRefUnder`) and IxC's
reference normalizer (`Ix.Kernel.nfRef`, frozen by its equations); the
structurally recursive tree functions are frozen by their equations.
`#check` freezes the proved theorems, and `#guard_kernel_axioms` and
`#guard_module_axioms` freeze the axioms of the statements, the theorems and
the modules (the standard three: `propext`, `Classical.choice`, `Quot.sound`). A
change to any of them fails the build, so the statement cannot drift
silently. The module is outside any namespace, so every name prints in full.

Three guards keep the statement about the deployed object:

* it names the prepared source `IxVM.source` and the entry
  `IxVM::verify_claim`, and it does not substitute the bare
  `IxVM.program` or invoke module preparation (the `run_meta` check, beside the frozen
  text): the object is the compiled, transparent source;
* the prepared source is the deployed preparation's: that is the native test
  suite `ixvm-source` (`IxVM.Check`), which prepares
  the imported DSL declarations for `verify_claim` and compares the result with
  `IxVM.source`, and `lake exe ixvm/ixvm-proof-gen --check`, which
  compares the derived proof scripts with their rendering. These are checks, not proofs;
* it is not vacuous, and its escape names a real function: in the checked
  source, `verify_claim` is an entry, its world prepares a call on a digest
  argument, and the program has the function `Blake3::hash` the escape
  observes, whose one parameter is a pointer to the byte-stream enum `Hashed`
  reads (`#guard`, evaluated when this module builds; an evaluation, not a
  proof). -/

example : IxVM.Refinement.verifyClaim = "IxVM::verify_claim" := rfl
example : IxVM.Refinement.blake3Hash = "Blake3::hash" := rfl
example : IxVM.Refinement.byteStreamEnum = "${\"name\":\"Lists::Node\",\"types\":[\"field\"]}" := rfl
example : IxVM.entry = IxVM.Refinement.verifyClaim := rfl

open Lean in
run_meta do
  let names : List (Name × List Name) := [
    (``IxVM.Refinement.SourceSound, [``IxVM.source, ``IxVM.Refinement.verifyClaim,
      ``Aiur.Generic.SourceSemantics.ObsFn, ``IxVM.Refinement.digestValue]),
    (``IxVM.Refinement.CircuitSound, [``IxVM.source, ``IxVM.Refinement.verifyClaim,
      ``Aiur.Generic.Specialized, ``Aiur.Optimized.Depth.Certified, ``Aiur.Optimized.Depth.system,
      ``Aiur.Optimized.Grouping.Plan.checkMemo, ``IxVM.Refinement.digestValue,
      ``Aiur.Generic.SourceSemantics.CallsInROM]),
    (``IxVM.Refinement.CircuitSoundAssuming, [``IxVM.source, ``IxVM.Refinement.verifyClaim,
      ``Aiur.Generic.Specialized, ``IxVM.Refinement.AcyclicDerivation,
      ``IxVM.Refinement.digestValue, ``Aiur.Generic.SourceSemantics.CallsInROM]),
    (``IxVM.Refinement.AxiomScopeIn, [``IxVM.Refinement.UserAxiomLeavesIn]),
    (``IxVM.Refinement.BindingIn, [``IxVM.Refinement.BindingSpecs]),
    (``IxVM.Refinement.BindingSeeds, [``IxVM.Refinement.compilerTrust]),
    (``IxVM.Refinement.BindingSpecs, [``Ix.Kernel.Declaration.anchorMismatch?,
      ``IxVM.Refinement.AnchorsTyped, ``Ix.Kernel.eqnsCheck]),
    (``IxVM.Refinement.TypingIn, [``IxVM.Refinement.AxiomScopeIn, ``IxVM.Refinement.LeavesInstalled,
      ``IxVM.Refinement.AssumedIn]),
    (``IxVM.Refinement.IxVMClaimSpecIn, [``IxVM.Refinement.packDigest, ``Address.blake3Pure,
      ``Ix.Claim.de, ``Ix.Claim.HoldsIn, ``IxVM.Refinement.View.HashedCollision]),
    (``IxVM.Refinement.Hashed, [``IxVM.Refinement.blake3Hash, ``IxVM.Refinement.byteStreamEnum]),
    (``IxVM.Refinement.EvalValues, [``Ix.Kernel.annotateCore, ``Ix.Kernel.isDefEqCore,
      ``Ix.Kernel.Expr.eraseMeta])]
  for (statement, needed) in names do
    let some info := (← getEnv).find? statement | throwError "{statement} is missing"
    let used := info.value!.getUsedConstants
    for n in needed do
      unless used.contains n do throwError "{statement} no longer names {n}"
  for statement in [``IxVM.Refinement.SourceSound, ``IxVM.Refinement.CircuitSound,
      ``IxVM.Refinement.CircuitSoundAssuming] do
    let some info := (← getEnv).find? statement | throwError "{statement} is missing"
    let used := info.value!.getUsedConstants
    for n in [``IxVM.program, ``Aiur.Modules.prepare] do
      if used.contains n then throwError "{statement} names {n}: state it over the prepared source"

#guard IxVM.source.checkEntry IxVM.Refinement.verifyClaim matches .ok () &&
  (IxVM.source.world.prepare IxVM.Refinement.verifyClaim
      [IxVM.Refinement.digestValue 0]).toBool &&
  (match IxVM.source.program.sourceFunction? IxVM.Refinement.blake3Hash with
    | some f => f.params.map Prod.snd == [.ptr (.enum IxVM.Refinement.byteStreamEnum)]
    | none => false)

/-! ## The statements -/

/--
info: def IxVM.Refinement.VerifyClaimSoundIn : Prop :=
IxVM.Refinement.SourceSound IxVM.Refinement.IxVMClaimSpecIn
-/
#guard_msgs in
#print IxVM.Refinement.VerifyClaimSoundIn

/--
info: def IxVM.Refinement.VerifyClaimCircuitSoundIn : Prop :=
IxVM.Refinement.CircuitSound IxVM.Refinement.IxVMClaimSpecIn
-/
#guard_msgs in
#print IxVM.Refinement.VerifyClaimCircuitSoundIn

/--
info: def IxVM.Refinement.VerifyClaimCircuitSoundInAssuming : Prop :=
IxVM.Refinement.CircuitSoundAssuming IxVM.Refinement.IxVMClaimSpecIn
-/
#guard_msgs in
#print IxVM.Refinement.VerifyClaimCircuitSoundInAssuming

/--
info: def IxVM.Refinement.SourceSound : (List (Aiur.Generic.SourceSemantics.Call IxVM.F) → IxVM.Refinement.Digest → Prop) →
  Prop :=
fun P =>
  ∀ (d : IxVM.Refinement.Digest) (value : Aiur.SourceValue IxVM.F) (heap : Aiur.Heap IxVM.F)
    (calls : List (Aiur.Generic.SourceSemantics.Call IxVM.F)),
    Aiur.Generic.SourceSemantics.ObsFn IxVM.source.world IxVM.Refinement.verifyClaim [IxVM.Refinement.digestValue d] []
        value heap calls →
      P calls d
-/
#guard_msgs in
#print IxVM.Refinement.SourceSound

/--
info: def IxVM.Refinement.CircuitSound : (List (Aiur.Generic.SourceSemantics.Call IxVM.F) → IxVM.Refinement.Digest → Prop) →
  Prop :=
fun P =>
  ∀ {id : String → Except String ℕ} {specialized : Aiur.Generic.Specialized IxVM.source [IxVM.Refinement.verifyClaim]}
    (compiled : Aiur.Optimized.GenericArtifact specialized)
    (physical : Aiur.Optimized.Physical.Prepared compiled.artifact) {cfg : Aiur.Optimized.Depth.Config},
    Aiur.Optimized.Depth.Certified cfg physical.system →
      cfg.bits ≤ 24 →
        ∀ (plan : Aiur.Optimized.Grouping.Plan (Aiur.Optimized.Depth.system cfg physical.system) id),
          plan.WellFormedActivation →
            ∀ {rom : Aiur.WidthROM IxVM.F},
              rom.Valid →
                ∀ (d : IxVM.Refinement.Digest) {wires : List (Aiur.WireValue IxVM.F)} {output : Aiur.WireValue IxVM.F}
                  {result : Aiur.Value IxVM.F},
                  Aiur.Circuit.Erasure.Signed compiled.system
                      { channel := IxVM.Refinement.verifyClaim, args := wires, result := output } →
                    ∀ {root : Aiur.Circuit.Message IxVM.F},
                      Aiur.Optimized.Depth.erase cfg root =
                          Aiur.Circuit.Erasure.message compiled.system
                            { channel := IxVM.Refinement.verifyClaim, args := wires, result := output } →
                        root.channel ∉ cfg.names →
                          ∀ {rows : List (Aiur.Circuit.WeightedRow IxVM.F)},
                            rows.length ≤ 2 ^ 39 →
                              plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = Except.ok () →
                                Aiur.DecodesValues specialized.program.enums wires
                                    (Aiur.entryValues [IxVM.Refinement.digestValue d]) →
                                  Aiur.WireValue.decode specialized.program.enums output = some result →
                                    ∃ value heap calls,
                                      Aiur.Generic.SourceSemantics.ObsFn IxVM.source.world IxVM.Refinement.verifyClaim
                                          [IxVM.Refinement.digestValue d] [] value heap calls ∧
                                        Aiur.Generic.SourceSemantics.CallsInROM (compiled.traceROM rom) calls ∧
                                          P calls d
-/
#guard_msgs in
#print IxVM.Refinement.CircuitSound

/--
info: def IxVM.Refinement.CircuitSoundAssuming : (List (Aiur.Generic.SourceSemantics.Call IxVM.F) →
    IxVM.Refinement.Digest → Prop) →
  Prop :=
fun P =>
  ∀ {id : String → Except String ℕ} {specialized : Aiur.Generic.Specialized IxVM.source [IxVM.Refinement.verifyClaim]}
    (compiled : Aiur.Optimized.GenericArtifact specialized)
    (physical : Aiur.Optimized.Physical.Prepared compiled.artifact)
    (plan : Aiur.Optimized.Grouping.Plan physical.system id),
    plan.WellFormedActivation →
      ∀ {rom : Aiur.WidthROM IxVM.F},
        rom.Valid →
          ∀ (d : IxVM.Refinement.Digest) {wires : List (Aiur.WireValue IxVM.F)} {output : Aiur.WireValue IxVM.F}
            {result : Aiur.Value IxVM.F},
            Aiur.Circuit.Erasure.Signed compiled.system
                { channel := IxVM.Refinement.verifyClaim, args := wires, result := output } →
              IxVM.Refinement.AcyclicDerivation compiled plan rom
                  { channel := IxVM.Refinement.verifyClaim, args := wires, result := output } →
                Aiur.DecodesValues specialized.program.enums wires (Aiur.entryValues [IxVM.Refinement.digestValue d]) →
                  Aiur.WireValue.decode specialized.program.enums output = some result →
                    ∃ value heap calls,
                      Aiur.Generic.SourceSemantics.ObsFn IxVM.source.world IxVM.Refinement.verifyClaim
                          [IxVM.Refinement.digestValue d] [] value heap calls ∧
                        Aiur.Generic.SourceSemantics.CallsInROM (compiled.traceROM rom) calls ∧ P calls d
-/
#guard_msgs in
#print IxVM.Refinement.CircuitSoundAssuming

/--
info: def IxVM.Refinement.ObservedHeadline : Prop :=
∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {id : String → Except String ℕ} {s : Aiur.Generic.Source F}
  {entries : List String} {specialized : Aiur.Generic.Specialized s entries}
  (compiled : Aiur.Optimized.GenericArtifact specialized)
  (physical : Aiur.Optimized.Physical.Prepared compiled.artifact)
  (plan : Aiur.Optimized.Grouping.Plan physical.system id),
  plan.WellFormedActivation →
    ∀ {name : String},
      name ∈ entries →
        ∀ {rom : Aiur.WidthROM F},
          rom.Valid →
            ∀ {args : List (Aiur.SourceValue F)} {result : Aiur.Value F} {wires : List (Aiur.WireValue F)}
              {output : Aiur.WireValue F},
              Aiur.Circuit.Erasure.Signed compiled.system { channel := name, args := wires, result := output } →
                IxVM.Refinement.AcyclicDerivation compiled plan rom
                    { channel := name, args := wires, result := output } →
                  Aiur.DecodesValues specialized.program.enums wires (Aiur.entryValues args) →
                    Aiur.WireValue.decode specialized.program.enums output = some result →
                      ∃ value heap calls,
                        Aiur.Generic.SourceSemantics.ObsFn s.world name args [] value heap calls ∧
                          Aiur.Represents (compiled.traceROM rom) heap value result ∧
                            Aiur.Generic.SourceSemantics.CallsInROM (compiled.traceROM rom) calls
-/
#guard_msgs in
#print IxVM.Refinement.ObservedHeadline

/--
info: def IxVM.Refinement.AcyclicDerivation : {F : Type} →
  [inst : Field F] →
    [inst_1 : DecidableEq F] →
      {s : Aiur.Generic.Source F} →
        {entries : List String} →
          {specialized : Aiur.Generic.Specialized s entries} →
            (compiled : Aiur.Optimized.GenericArtifact specialized) →
              {physical : Aiur.Optimized.Physical.Prepared compiled.artifact} →
                {id : String → Except String ℕ} →
                  Aiur.Optimized.Grouping.Plan physical.system id → Aiur.WidthROM F → Aiur.Circuit.Message F → Prop :=
fun {F} [Field F] [DecidableEq F] {s} {entries} {specialized} compiled {physical} {id} plan rom root =>
  plan.ActivatedDerives (Aiur.Circuit.Erasure.rawROM rom) (Aiur.Circuit.Erasure.message compiled.system root)
-/
#guard_msgs in
#print IxVM.Refinement.AcyclicDerivation

/--
info: @[reducible] def Aiur.Optimized.GenericArtifact.traceROM : {F : Type} →
  [inst : Field F] →
    [inst_1 : DecidableEq F] →
      {source : Aiur.Generic.Source F} →
        {entries : List String} →
          {specialized : Aiur.Generic.Specialized source entries} →
            Aiur.Optimized.GenericArtifact specialized → Aiur.WidthROM F → Aiur.ROM F :=
fun {F} [Field F] [DecidableEq F] {source} {entries} {specialized} compiled rom =>
  Aiur.WireROM.decode specialized.program.enums (Aiur.Circuit.Erasure.typedROM compiled.system rom)
-/
#guard_msgs in
#print Aiur.Optimized.GenericArtifact.traceROM

/--
info: def Aiur.Generic.SourceSemantics.CallsInROM : {F : Type} →
  Aiur.ROM F → List (Aiur.Generic.SourceSemantics.Call F) → Prop :=
fun {F} rom calls => ∀ c ∈ calls, ∀ v ∈ c.args, ∃ w, Aiur.Represents rom c.heap v w
-/
#guard_msgs in
#print Aiur.Generic.SourceSemantics.CallsInROM

/--
info: def IxVM.Refinement.IxVMClaimSpecIn : List (Aiur.Generic.SourceSemantics.Call IxVM.F) → IxVM.Refinement.Digest → Prop :=
fun calls d =>
  ∀ (bytes : ByteArray) (c : Ix.Claim) (V : IxVM.Refinement.View),
    Ix.Claim.de bytes = Except.ok c →
      IxVM.Refinement.packDigest (Address.blake3Pure bytes) = d →
        V.Authentic → Ix.Claim.Covers V c → Ix.Claim.HoldsIn V c ∨ V.HashedCollision [bytes] calls
-/
#guard_msgs in
#print IxVM.Refinement.IxVMClaimSpecIn

/--
info: def IxVM.Refinement.View.HashedCollision : IxVM.Refinement.View →
  List ByteArray → List (Aiur.Generic.SourceSemantics.Call IxVM.F) → Prop :=
fun V extra calls =>
  (∃ x held bytes,
      (V.Preimage x held ∨
          held ∈ extra ∧ Address.blake3Pure held = x ∨
            IxVM.Refinement.Hashed calls held ∧ Address.blake3Pure held = x) ∧
        IxVM.Refinement.Hashed calls bytes ∧ bytes ≠ held ∧ Address.blake3Pure bytes = x) ∨
    ∃ bytes,
      (V.Preimage Ix.HostAdmission.Merkle.padding bytes ∨ IxVM.Refinement.Hashed calls bytes) ∧
        Address.blake3Pure bytes = Ix.HostAdmission.Merkle.padding
-/
#guard_msgs in
#print IxVM.Refinement.View.HashedCollision

/--
info: def IxVM.Refinement.Hashed : List (Aiur.Generic.SourceSemantics.Call IxVM.F) → ByteArray → Prop :=
fun calls bytes =>
  ∃ c ∈ calls,
    c.name = IxVM.Refinement.blake3Hash ∧
      ∃ input,
        c.args = [input] ∧
          Aiur.Library.Bytes.RepByteStream IxVM.Refinement.byteStreamEnum c.heap bytes.data.toList input
-/
#guard_msgs in
#print IxVM.Refinement.Hashed

/--
info: def IxVM.Refinement.blake3Hash : String :=
"Blake3::hash"
-/
#guard_msgs in
#print IxVM.Refinement.blake3Hash

/--
info: def IxVM.Refinement.byteStreamEnum : String :=
"${\"name\":\"Lists::Node\",\"types\":[\"field\"]}"
-/
#guard_msgs in
#print IxVM.Refinement.byteStreamEnum

/--
info: @[reducible] def IxVM.Refinement.Digest : Type :=
Fin 8 → IxVM.F
-/
#guard_msgs in
#print IxVM.Refinement.Digest

/--
info: def IxVM.Refinement.packDigest : Address → IxVM.Refinement.Digest :=
fun a i =>
  have byte := fun k => (a.hash.data.getD k 0).toNat;
  ↑(byte (4 * ↑i) + 256 * byte (4 * ↑i + 1) + 65536 * byte (4 * ↑i + 2) + 16777216 * byte (4 * ↑i + 3))
-/
#guard_msgs in
#print IxVM.Refinement.packDigest

/--
info: def IxVM.Refinement.digestValue : IxVM.Refinement.Digest → Aiur.SourceValue IxVM.F :=
fun d => Aiur.Value.tuple (List.ofFn fun i => Aiur.Value.field (d i))
-/
#guard_msgs in
#print IxVM.Refinement.digestValue

/--
info: def IxVM.Refinement.verifyClaim : String :=
"IxVM::verify_claim"
-/
#guard_msgs in
#print IxVM.Refinement.verifyClaim

/--
info: @[reducible] def IxVM.Refinement.source : Aiur.Generic.Source IxVM.F :=
IxVM.source
-/
#guard_msgs in
#print IxVM.Refinement.source

/--
info: def IxVM.source : Aiur.Generic.Source IxVM.F :=
{ program := IxVM.program, tables := IxVM.coreTables, tablesChecked := IxVM.tablesChecked }
-/
#guard_msgs in
#print IxVM.source

/--
info: def IxVM.entry : String :=
"IxVM::verify_claim"
-/
#guard_msgs in
#print IxVM.entry

/--
info: IxVM.tablesChecked : Aiur.typecheck IxVM.coreTables = Except.ok ()
-/
#guard_msgs in
#check @IxVM.tablesChecked

/--
info: def Aiur.Modules.Prepared.ObsFn : {F : Type} →
  [Field F] →
    [inst : DecidableEq F] →
      {program : Aiur.Modules.Program F} →
        Aiur.Modules.Prepared program →
          String →
            List (Aiur.SourceValue F) →
              Aiur.SourceValue F → Aiur.Heap F → List (Aiur.Generic.SourceSemantics.Call F) → Prop :=
fun {F} [Field F] [DecidableEq F] {program} p name args value heap calls =>
  ∃ entry,
    p.find? name = some entry ∧
      Aiur.Generic.SourceSemantics.ObsFn p.environment.source.world entry.resolved.name args [] value heap calls
-/
#guard_msgs in
#print Aiur.Modules.Prepared.ObsFn

/--
info: structure Aiur.Generic.SourceSemantics.Call (F : Type) : Type
number of parameters: 1
fields:
  Aiur.Generic.SourceSemantics.Call.name : String
  Aiur.Generic.SourceSemantics.Call.args : List (Aiur.SourceValue F)
  Aiur.Generic.SourceSemantics.Call.heap : Aiur.Heap F
constructor:
  Aiur.Generic.SourceSemantics.Call.mk {F : Type} (name : String) (args : List (Aiur.SourceValue F))
    (heap : Aiur.Heap F) : Aiur.Generic.SourceSemantics.Call F
-/
#guard_msgs in
#print Aiur.Generic.SourceSemantics.Call

/-! ## What a claim means -/

/--
info: def Ix.Claim.HoldsIn : IxVM.Refinement.View → Ix.Claim → Prop :=
fun V x =>
  match x with
  | Ix.Claim.eval ctx input output asm =>
    IxVM.Refinement.TypingIn V ctx (fun a => a = input ∨ a = output) asm (IxVM.Refinement.EvalValues input output) ∧
      IxVM.Refinement.EvalOutputIn V output
  | Ix.Claim.check ctx a asm => IxVM.Refinement.TypingIn V ctx (fun x => x = a) asm
  | Ix.Claim.checkEnv ctx root asm =>
    V.HoldsTree root ∧
      ∀ (leaves : List Address),
        V.LeavesAt root leaves → leaves ≠ [] ∧ IxVM.Refinement.TypingIn V ctx (fun x => x ∈ leaves) asm
  | Ix.Claim.reveal comm info => ∃ c, Ix.Cert.recordAt V.env comm = some c ∧ IxVM.Refinement.RevealLE info c.info
  | Ix.Claim.contains tree a => V.HoldsTree tree ∧ ∀ (leaves : List Address), V.LeavesAt tree leaves → a ∈ leaves
  | Ix.Claim.catalog members => False
  | Ix.Claim.resource root profile => False
  | Ix.Claim.binding spec b => IxVM.Refinement.BindingIn V spec b
-/
#guard_msgs in
#print Ix.Claim.HoldsIn

/--
info: def Ix.Claim.Covers : IxVM.Refinement.View → Ix.Claim → Prop :=
fun V x =>
  match x with
  | Ix.Claim.eval ctx input output asm =>
    V.TypingCovers ctx asm ∧
      V.Stores input ∧
        V.Stores output ∧
          ∀ (c : Ixon.Constant) (d : Ixon.Definition),
            Ix.Cert.recordAt V.env output = some c →
              c.info = Ixon.ConstantInfo.defn d → ∀ (n : ℕ), ¬IxVM.Refinement.IsProjFnAt c n d.value
  | Ix.Claim.check ctx a asm => V.TypingCovers ctx asm ∧ V.Stores a
  | Ix.Claim.checkEnv ctx root asm =>
    V.TypingCovers ctx asm ∧
      V.HoldsTree root ∧ ∀ (leaves : List Address), V.LeavesAt root leaves → ∀ a ∈ leaves, V.Stores a
  | Ix.Claim.reveal comm info => V.Stores comm
  | Ix.Claim.contains tree const => V.HoldsTree tree
  | Ix.Claim.binding spec b => V.Closed ∧ (V.binding? b).isSome = true
  | Ix.Claim.catalog members => True
  | Ix.Claim.resource root profile => True
-/
#guard_msgs in
#print Ix.Claim.Covers

/--
info: def IxVM.Refinement.TypingIn : IxVM.Refinement.View →
  Ix.ClaimContext →
    (Address → Prop) →
      Option Address →
        (optParam
            (Ix.Kernel.Admission.Binding →
              Ix.Kernel.Env Ix.Kernel.Mode.anon → List (Ix.Kernel.Declaration Ix.Kernel.Mode.anon) → Prop)
            fun x x_1 x_2 => True) →
          Prop :=
fun V ctx S asm Q =>
  Ix.SpecDigest.specDigest = Except.ok ctx.spec ∧
    ctx.literalClass = false ∧
      ∃ b,
        V.binding? ctx.binding = some b ∧
          IxVM.Refinement.AxiomScopeIn V b ctx.axioms fun policy leaves =>
            (ctx.bindingAssumed = true → IxVM.Refinement.BindingIn V ctx.spec ctx.binding) →
              IxVM.Refinement.AssumingIn V { binding := b, policy := policy, axioms := fun x => x ∈ leaves }
                (fun a => S a ∨ a ∈ leaves ∧ ¬IxVM.Refinement.AssumedIn V asm a)
                (fun bnd envA ds =>
                  IxVM.Refinement.LeavesInstalled leaves (IxVM.Refinement.AssumedIn V asm) ds ∧ Q bnd envA ds)
                asm
-/
#guard_msgs in
#print IxVM.Refinement.TypingIn

/--
info: def IxVM.Refinement.AxiomScopeIn : IxVM.Refinement.View →
  Ix.Kernel.Admission.Binding → Option Address → (Ix.Kernel.Cached.AxiomPolicy → List Address → Prop) → Prop :=
fun V b x x_1 =>
  match x, x_1 with
  | none, k => k Ix.Kernel.Cached.AxiomPolicy.strict []
  | some r, k =>
    V.HoldsTree r ∧
      ∀ (leaves : List Address),
        V.LeavesAt r leaves →
          IxVM.Refinement.UserAxiomLeavesIn V b leaves ∧ k Ix.Kernel.Cached.AxiomPolicy.allowUser leaves
-/
#guard_msgs in
#print IxVM.Refinement.AxiomScopeIn

/--
info: def IxVM.Refinement.UserAxiomLeavesIn : IxVM.Refinement.View → Ix.Kernel.Admission.Binding → List Address → Prop :=
fun V b leaves =>
  ∀ a ∈ leaves,
    (∃ c ax, Ix.Cert.recordAt V.env a = some c ∧ c.info = Ixon.ConstantInfo.axio ax ∧ ax.isUnsafe = false) ∧
      ∀ (t : Ix.Kernel.RoleTable),
        Ix.Kernel.RoleTable.ofBytes b.bytes = some t → ∀ (r : Ix.Kernel.Role), t.addressOf? r ≠ some a
-/
#guard_msgs in
#print IxVM.Refinement.UserAxiomLeavesIn

/--
info: def IxVM.Refinement.LeavesInstalled : List Address →
  (Address → Prop) → List (Ix.Kernel.Declaration Ix.Kernel.Mode.anon) → Prop :=
fun leaves assumed ds => ∀ a ∈ leaves, ¬assumed a → ∃ cv ∈ Ix.Kernel.userAxiomsOfDecls ds, cv.name = Ix.Kernel.Key.id a
-/
#guard_msgs in
#print IxVM.Refinement.LeavesInstalled

/--
info: def IxVM.Refinement.AssumedIn : IxVM.Refinement.View → Option Address → Address → Prop :=
fun V asm a => ∃ r leaves, asm = some r ∧ V.LeavesAt r leaves ∧ a ∈ leaves
-/
#guard_msgs in
#print IxVM.Refinement.AssumedIn

/--
info: def IxVM.Refinement.AssumingIn : IxVM.Refinement.View →
  IxVM.Refinement.Scope →
    (Address → Prop) →
      (Ix.Kernel.Admission.Binding →
          Ix.Kernel.Env Ix.Kernel.Mode.anon → List (Ix.Kernel.Declaration Ix.Kernel.Mode.anon) → Prop) →
        Option Address → Prop :=
fun V σ S Q x =>
  match x with
  | none => IxVM.Refinement.AcceptsIn V σ S Q
  | some r =>
    V.HoldsTree r ∧
      ∀ (leaves : List Address),
        V.LeavesAt r leaves →
          (∀ a ∈ leaves, IxVM.Refinement.AcceptsIn V σ fun x => x = a) → IxVM.Refinement.AcceptsIn V σ S Q
-/
#guard_msgs in
#print IxVM.Refinement.AssumingIn

/--
info: def IxVM.Refinement.AcceptsIn : IxVM.Refinement.View →
  IxVM.Refinement.Scope →
    (Address → Prop) →
      (optParam
          (Ix.Kernel.Admission.Binding →
            Ix.Kernel.Env Ix.Kernel.Mode.anon → List (Ix.Kernel.Declaration Ix.Kernel.Mode.anon) → Prop)
          fun x x_1 x_2 => True) →
        Prop :=
fun V σ S Q =>
  ∃ E limits order envA,
    IxVM.Refinement.Draws E V.env ∧
      (∀ (a : Address), S a → E.consts.contains a = true) ∧
        ∃ t pre ev ds,
          Ix.Kernel.Admission.admitBinding Address.admissionHash σ.binding = Except.ok t ∧
            Ix.Cert.ClosureOrderAt t E S order ∧
              Ix.Kernel.Admission.admitAxiomPolicy σ.policy t = Except.ok () ∧
                Ix.Kernel.Reader.preludeFor t = Except.ok pre ∧
                  Ix.Kernel.Admission.prepareWith Address.admissionHash σ.binding pre limits (Ix.Cert.recordsOf E order)
                        (Ix.Cert.blobsOf E order) (Ix.Cert.hintsOf E) =
                      Except.ok (ev, ds) ∧
                    Ix.Kernel.Cached.AcceptsRefUnder σ.policy Ix.Kernel.CheckMode.verified ev
                        (List.map IxVM.Refinement.thmToOpaqueDefn ds.toList) envA ∧
                      IxVM.Refinement.TheoremsInProp envA ds.toList ∧
                        IxVM.Refinement.UserAxiomsWithin σ.axioms ds.toList ∧ Q σ.binding envA ds.toList
-/
#guard_msgs in
#print IxVM.Refinement.AcceptsIn

/--
info: def IxVM.Refinement.thmToOpaqueDefn : {md : Ix.Kernel.Mode} → Ix.Kernel.Declaration md → Ix.Kernel.Declaration md :=
fun {md} x =>
  match x with
  | Ix.Kernel.Declaration.thmDecl cv value =>
    match cv.name with
    | base.aux d => Ix.Kernel.Declaration.thmDecl cv value
    | x => Ix.Kernel.Declaration.defnDecl cv value Ix.Kernel.ReducibilityHint.opaque
  | d => d
-/
#guard_msgs in
#print IxVM.Refinement.thmToOpaqueDefn

/--
info: def IxVM.Refinement.TheoremsInProp : {md : Ix.Kernel.Mode} →
  Ix.Kernel.Env md → List (Ix.Kernel.Declaration md) → Prop :=
fun {md} envA ds =>
  ∀ (cv : Ix.Kernel.ConstantVal md) (value : Ix.Kernel.Expr md),
    Ix.Kernel.Declaration.thmDecl cv value ∈ ds →
      ∃ F tA stype u,
        (Ix.Kernel.fueledOps Ix.Kernel.CheckMode.verified F).annotate envA 0 cv.type = Except.ok tA ∧
          (Ix.Kernel.fueledOps Ix.Kernel.CheckMode.verified F).inferType envA 0 tA = Except.ok stype ∧
            (Ix.Kernel.fueledOps Ix.Kernel.CheckMode.verified F).ensureSort envA 0 stype = Except.ok u ∧ u.isZero = true
-/
#guard_msgs in
#print IxVM.Refinement.TheoremsInProp

/--
info: structure IxVM.Refinement.Scope : Type
number of parameters: 0
fields:
  IxVM.Refinement.Scope.binding : Ix.Kernel.Admission.Binding
  IxVM.Refinement.Scope.policy : Ix.Kernel.Cached.AxiomPolicy
  IxVM.Refinement.Scope.axioms : Address → Prop
constructor:
  IxVM.Refinement.Scope.mk (binding : Ix.Kernel.Admission.Binding) (policy : Ix.Kernel.Cached.AxiomPolicy)
    (axioms : Address → Prop) : IxVM.Refinement.Scope
-/
#guard_msgs in
#print IxVM.Refinement.Scope

/--
info: def IxVM.Refinement.Scope.strict : Ix.Kernel.Admission.Binding → IxVM.Refinement.Scope :=
fun binding => { binding := binding, policy := Ix.Kernel.Cached.AxiomPolicy.strict, axioms := fun x => False }
-/
#guard_msgs in
#print IxVM.Refinement.Scope.strict

/--
info: def IxVM.Refinement.UserAxiomsWithin : (Address → Prop) → List (Ix.Kernel.Declaration Ix.Kernel.Mode.anon) → Prop :=
fun allowed ds => ∀ cv ∈ Ix.Kernel.userAxiomsOfDecls ds, ∃ a, allowed a ∧ cv.name = Ix.Kernel.Key.id a
-/
#guard_msgs in
#print IxVM.Refinement.UserAxiomsWithin

/--
info: def IxVM.Refinement.Draws : Ixon.Env → Ixon.Env → Prop :=
fun E E₀ =>
  (∀ (a : Address) (lc : Ixon.LazyConstant),
      E.consts.get? a = some lc →
        (∃ lc₀, E₀.consts.get? a = some lc₀ ∧ lc₀.rawBytes = lc.rawBytes) ∨
          E₀.consts.contains a = false ∧ ∃ c, lc.get? = some c ∧ IxVM.Refinement.IsRecursorRecord c) ∧
    ∀ (a : Address) (bytes : ByteArray), E.blobs.get? a = some bytes → E₀.blobs.get? a = some bytes
-/
#guard_msgs in
#print IxVM.Refinement.Draws

/--
info: def IxVM.Refinement.IsRecursorRecord : Ixon.Constant → Prop :=
fun c =>
  match c.info with
  | Ixon.ConstantInfo.recr a => True
  | Ixon.ConstantInfo.muts ms => ∀ m ∈ ms.toList, ∃ r, m = Ixon.MutConst.recr r
  | x => False
-/
#guard_msgs in
#print IxVM.Refinement.IsRecursorRecord

/--
info: def IxVM.Refinement.BindingSpecs : Ix.Kernel.RoleTable →
  Ix.Kernel.Admission.Binding →
    Ix.Kernel.Env Ix.Kernel.Mode.anon → List (Ix.Kernel.Declaration Ix.Kernel.Mode.anon) → Prop :=
fun t x envA ds =>
  (∀ d ∈ ds, d.anchorMismatch? = none) ∧
    IxVM.Refinement.AnchorsTyped ds ∧
      ∃ ev,
        ∀ (r : Ix.Kernel.Role),
          t.addressOf? r ≠ none →
            r.spec.kind = Ix.Kernel.SpecKind.eqns →
              ∃ F, Ix.Kernel.eqnsCheck (Ix.Kernel.fueledOps Ix.Kernel.CheckMode.verified F) envA r ev = Except.ok ()
-/
#guard_msgs in
#print IxVM.Refinement.BindingSpecs

/--
info: def IxVM.Refinement.BindingIn : IxVM.Refinement.View → Address → Address → Prop :=
fun V spec b =>
  Ix.SpecDigest.specDigest = Except.ok spec ∧
    ∃ bnd t,
      V.binding? b = some bnd ∧
        Ix.Kernel.Admission.admitBinding Address.admissionHash bnd = Except.ok t ∧
          (∀ r ∈ Ix.Kernel.Role.all, (t.addressOf? r).isSome = true) ∧
            IxVM.Refinement.AcceptsIn V (IxVM.Refinement.Scope.strict bnd) (IxVM.Refinement.BindingSeeds t)
              (IxVM.Refinement.BindingSpecs t)
-/
#guard_msgs in
#print IxVM.Refinement.BindingIn

/--
info: def IxVM.Refinement.BindingSeeds : Ix.Kernel.RoleTable → Address → Prop :=
fun t a =>
  (∃ r, IxVM.Refinement.compilerTrust r = false ∧ t.addressOf? r = some a) ∨
    ∃ e ∈ t.evidence.toList, Ix.Kernel.Evidence.proof a ∈ e.2.toList
-/
#guard_msgs in
#print IxVM.Refinement.BindingSeeds

/--
info: def IxVM.Refinement.AnchorsTyped : List (Ix.Kernel.Declaration Ix.Kernel.Mode.anon) → Prop :=
fun ds =>
  ∀ d ∈ ds,
    ∀ cv ∈ IxVM.Refinement.declaredVals d,
      ∀ (pin : Ix.Kernel.ConstantVal Ix.Kernel.Mode.anon),
        IxVM.Refinement.anchorPin? cv.name = some pin → cv.matchesPin pin = true
-/
#guard_msgs in
#print IxVM.Refinement.AnchorsTyped

/--
info: def IxVM.Refinement.anchorPin? : Ix.Kernel.Key Ix.Kernel.Mode.anon →
  Option (Ix.Kernel.ConstantVal Ix.Kernel.Mode.anon) :=
fun x =>
  match x with
  | Ix.Kernel.Key.role r =>
    match r.spec with
    | Ix.Kernel.Spec.anchor n ty => some { name := Ix.Kernel.Key.role r, levelParams := List.range n, type := ty }
    | x => none
  | x => none
-/
#guard_msgs in
#print IxVM.Refinement.anchorPin?

/--
info: def IxVM.Refinement.declaredVals : Ix.Kernel.Declaration Ix.Kernel.Mode.anon →
  List (Ix.Kernel.ConstantVal Ix.Kernel.Mode.anon) :=
fun x =>
  match x with
  | Ix.Kernel.Declaration.axiomDecl cv => [cv]
  | Ix.Kernel.Declaration.defnDecl cv value hint => [cv]
  | Ix.Kernel.Declaration.thmDecl cv value => [cv]
  | Ix.Kernel.Declaration.opaqueDecl cv value => [cv]
  | Ix.Kernel.Declaration.quotDecl kind cv => [cv]
  | Ix.Kernel.Declaration.indDecl block numParams => List.map (fun x => x.toConstantVal) block
  | Ix.Kernel.Declaration.basisDecl kind => []
-/
#guard_msgs in
#print IxVM.Refinement.declaredVals

/--
info: def IxVM.Refinement.compilerTrust : Ix.Kernel.Role → Bool :=
fun x =>
  match x with
  | Ix.Kernel.Role.trustCompiler => true
  | Ix.Kernel.Role.reduceBool => true
  | Ix.Kernel.Role.reduceNat => true
  | Ix.Kernel.Role.ofReduceBool => true
  | Ix.Kernel.Role.ofReduceNat => true
  | x => false
-/
#guard_msgs in
#print IxVM.Refinement.compilerTrust

/--
info: def IxVM.Refinement.EvalValues : Address →
  Address →
    Ix.Kernel.Admission.Binding →
      Ix.Kernel.Env Ix.Kernel.Mode.anon → List (Ix.Kernel.Declaration Ix.Kernel.Mode.anon) → Prop :=
fun input output b envA ds =>
  ∃ cvIn cvOut vIn vOut hint,
    (∃ d ∈ ds, IxVM.Refinement.declValue? d = some (cvIn, vIn)) ∧
      IxVM.Refinement.AddressKey b input cvIn.name ∧
        Ix.Kernel.Declaration.defnDecl cvOut vOut hint ∈ ds ∧
          IxVM.Refinement.AddressKey b output cvOut.name ∧
            cvOut.levelParams.length = cvIn.levelParams.length ∧
              cvOut.type.eraseMeta = cvIn.type.eraseMeta ∧
                ∃ fuel vInA vOutA,
                  Ix.Kernel.annotateCore Ix.Kernel.CheckMode.verified envA fuel 0 vIn = Except.ok vInA ∧
                    Ix.Kernel.annotateCore Ix.Kernel.CheckMode.verified envA fuel 0 vOut = Except.ok vOutA ∧
                      Ix.Kernel.isDefEqCore Ix.Kernel.CheckMode.verified envA fuel 0 vInA vOutA = Except.ok true
-/
#guard_msgs in
#print IxVM.Refinement.EvalValues

/--
info: def IxVM.Refinement.declValue? : Ix.Kernel.Declaration Ix.Kernel.Mode.anon →
  Option (Ix.Kernel.ConstantVal Ix.Kernel.Mode.anon × Ix.Kernel.Expr Ix.Kernel.Mode.anon) :=
fun x =>
  match x with
  | Ix.Kernel.Declaration.defnDecl cv value hint => some (cv, value)
  | Ix.Kernel.Declaration.thmDecl cv value => some (cv, value)
  | Ix.Kernel.Declaration.opaqueDecl cv value => some (cv, value)
  | x => none
-/
#guard_msgs in
#print IxVM.Refinement.declValue?

/--
info: def IxVM.Refinement.AddressKey : Ix.Kernel.Admission.Binding → Address → Ix.Kernel.Key Ix.Kernel.Mode.anon → Prop :=
fun b a k =>
  k = Ix.Kernel.Key.id a ∨
    ∃ t r, Ix.Kernel.RoleTable.ofBytes b.bytes = some t ∧ t.addressOf? r = some a ∧ k = Ix.Kernel.Key.role r
-/
#guard_msgs in
#print IxVM.Refinement.AddressKey

/--
info: def IxVM.Refinement.EvalOutputIn : IxVM.Refinement.View → Address → Prop :=
fun V output =>
  ∃ c d,
    Ix.Cert.recordAt V.env output = some c ∧
      c.info = Ixon.ConstantInfo.defn d ∧ d.kind = Ix.DefKind.defn ∧ d.safety = Ix.DefinitionSafety.safe
-/
#guard_msgs in
#print IxVM.Refinement.EvalOutputIn

/--
info: def IxVM.Refinement.RevealLE : Ix.RevealConstantInfo → Ixon.ConstantInfo → Prop :=
fun x x_1 =>
  match x, x_1 with
  | Ix.RevealConstantInfo.defn k s l t v, Ixon.ConstantInfo.defn d => IxVM.Refinement.RevealDefnLE k s l t v d
  | Ix.RevealConstantInfo.recr k u l p ix mo mi t rs, Ixon.ConstantInfo.recr r =>
    IxVM.Refinement.RevealRecrLE k u l p ix mo mi t rs r
  | Ix.RevealConstantInfo.axio u l t, Ixon.ConstantInfo.axio a =>
    IxVM.Refinement.OptEq u a.isUnsafe ∧
      IxVM.Refinement.OptEq l a.lvls ∧ IxVM.Refinement.OptEq t (IxVM.Refinement.exprAddr a.typ)
  | Ix.RevealConstantInfo.quot k l t, Ixon.ConstantInfo.quot q =>
    IxVM.Refinement.OptEq k q.kind ∧
      IxVM.Refinement.OptEq l q.lvls ∧ IxVM.Refinement.OptEq t (IxVM.Refinement.exprAddr q.typ)
  | Ix.RevealConstantInfo.cPrj i c b, Ixon.ConstantInfo.cPrj p =>
    IxVM.Refinement.OptEq i p.idx ∧ IxVM.Refinement.OptEq c p.cidx ∧ IxVM.Refinement.OptEq b p.block
  | Ix.RevealConstantInfo.rPrj i b, Ixon.ConstantInfo.rPrj p =>
    IxVM.Refinement.OptEq i p.idx ∧ IxVM.Refinement.OptEq b p.block
  | Ix.RevealConstantInfo.iPrj i b, Ixon.ConstantInfo.iPrj p =>
    IxVM.Refinement.OptEq i p.idx ∧ IxVM.Refinement.OptEq b p.block
  | Ix.RevealConstantInfo.dPrj i b, Ixon.ConstantInfo.dPrj p =>
    IxVM.Refinement.OptEq i p.idx ∧ IxVM.Refinement.OptEq b p.block
  | Ix.RevealConstantInfo.muts cs, Ixon.ConstantInfo.muts ms =>
    ∀ e ∈ cs.toList, ∃ m, ms[e.1.toNat]? = some m ∧ IxVM.Refinement.RevealMutLE e.2 m
  | x, x_2 => False
-/
#guard_msgs in
#print IxVM.Refinement.RevealLE

/--
info: def IxVM.Refinement.RevealMutLE : Ix.RevealMutConstInfo → Ixon.MutConst → Prop :=
fun x x_1 =>
  match x, x_1 with
  | Ix.RevealMutConstInfo.defn k s l t v, Ixon.MutConst.defn d => IxVM.Refinement.RevealDefnLE k s l t v d
  | Ix.RevealMutConstInfo.indc u l p ix t cs, Ixon.MutConst.indc i => IxVM.Refinement.RevealIndcLE u l p ix t cs i
  | Ix.RevealMutConstInfo.recr k u l p ix mo mi t rs, Ixon.MutConst.recr r =>
    IxVM.Refinement.RevealRecrLE k u l p ix mo mi t rs r
  | x, x_2 => False
-/
#guard_msgs in
#print IxVM.Refinement.RevealMutLE

/--
info: def IxVM.Refinement.RevealDefnLE : Option Ix.DefKind →
  Option Ix.DefinitionSafety → Option UInt64 → Option Address → Option Address → Ixon.Definition → Prop :=
fun kind safety lvls typ value d =>
  IxVM.Refinement.OptEq kind d.kind ∧
    IxVM.Refinement.OptEq safety d.safety ∧
      IxVM.Refinement.OptEq lvls d.lvls ∧
        IxVM.Refinement.OptEq typ (IxVM.Refinement.exprAddr d.typ) ∧
          IxVM.Refinement.OptEq value (IxVM.Refinement.exprAddr d.value)
-/
#guard_msgs in
#print IxVM.Refinement.RevealDefnLE

/--
info: def IxVM.Refinement.RevealRecrLE : Option Bool →
  Option Bool →
    Option UInt64 →
      Option UInt64 →
        Option UInt64 →
          Option UInt64 →
            Option UInt64 → Option Address → Option (Array Ix.RevealRecursorRule) → Ixon.Recursor → Prop :=
fun k isUnsafe lvls params indices motives minors typ rules r =>
  IxVM.Refinement.OptEq k r.k ∧
    IxVM.Refinement.OptEq isUnsafe r.isUnsafe ∧
      IxVM.Refinement.OptEq lvls r.lvls ∧
        IxVM.Refinement.OptEq params r.params ∧
          IxVM.Refinement.OptEq indices r.indices ∧
            IxVM.Refinement.OptEq motives r.motives ∧
              IxVM.Refinement.OptEq minors r.minors ∧
                IxVM.Refinement.OptEq typ (IxVM.Refinement.exprAddr r.typ) ∧
                  IxVM.Refinement.OptEq (Option.map Array.toList rules) (IxVM.Refinement.revealRules r.rules)
-/
#guard_msgs in
#print IxVM.Refinement.RevealRecrLE

/--
info: def IxVM.Refinement.RevealIndcLE : Option Bool →
  Option UInt64 →
    Option UInt64 →
      Option UInt64 → Option Address → Option (Array (UInt64 × Ix.RevealConstructorInfo)) → Ixon.Inductive → Prop :=
fun isUnsafe lvls params indices typ ctors i =>
  IxVM.Refinement.OptEq isUnsafe i.isUnsafe ∧
    IxVM.Refinement.OptEq lvls i.lvls ∧
      IxVM.Refinement.OptEq params i.params ∧
        IxVM.Refinement.OptEq indices i.indices ∧
          IxVM.Refinement.OptEq typ (IxVM.Refinement.exprAddr i.typ) ∧
            ∀ (cs : Array (UInt64 × Ix.RevealConstructorInfo)),
              ctors = some cs →
                ∀ e ∈ cs.toList, ∃ c, i.ctors[e.1.toNat]? = some c ∧ IxVM.Refinement.RevealConstructorLE e.2 c
-/
#guard_msgs in
#print IxVM.Refinement.RevealIndcLE

/--
info: def IxVM.Refinement.RevealConstructorLE : Ix.RevealConstructorInfo → Ixon.Constructor → Prop :=
fun info c =>
  IxVM.Refinement.OptEq info.isUnsafe c.isUnsafe ∧
    IxVM.Refinement.OptEq info.lvls c.lvls ∧
      IxVM.Refinement.OptEq info.cidx c.cidx ∧
        IxVM.Refinement.OptEq info.params c.params ∧
          IxVM.Refinement.OptEq info.fields c.fields ∧ IxVM.Refinement.OptEq info.typ (IxVM.Refinement.exprAddr c.typ)
-/
#guard_msgs in
#print IxVM.Refinement.RevealConstructorLE

/--
info: def IxVM.Refinement.revealRules : Array Ixon.RecursorRule → List Ix.RevealRecursorRule :=
fun rules =>
  List.map
    (fun x =>
      match x with
      | (r, j) => { ruleIdx := j.toUInt64, fields := r.fields, rhs := IxVM.Refinement.exprAddr r.rhs })
    rules.toList.zipIdx
-/
#guard_msgs in
#print IxVM.Refinement.revealRules

/--
info: def IxVM.Refinement.exprAddr : Ixon.Expr → Address :=
fun e => Address.blake3Pure (Ixon.runPut (Ixon.putExpr e))
-/
#guard_msgs in
#print IxVM.Refinement.exprAddr

/--
info: def IxVM.Refinement.OptEq : {α : Type} → Option α → α → Prop :=
fun {α} claimed real => ∀ (x : α), claimed = some x → x = real
-/
#guard_msgs in
#print IxVM.Refinement.OptEq

/-! ## IxC acceptance under an axiom policy -/

/--
info: def Ix.Cert.IxonAcceptsRefUnder : Ix.Kernel.Cached.AxiomPolicy →
  Ix.Kernel.Admission.Binding →
    Ix.Kernel.Admission.Limits →
      Ixon.Env → (Address → Prop) → List Address → Ix.Kernel.Env Ix.Kernel.Mode.anon → Prop :=
fun policy binding limits ixe S order envA =>
  Ix.Cert.ClosureOrder ixe S order ∧
    ∃ t pre ev ds,
      Ix.Kernel.Admission.admitBinding Address.admissionHash binding = Except.ok t ∧
        Ix.Kernel.Admission.admitAxiomPolicy policy t = Except.ok () ∧
          Ix.Kernel.Reader.preludeFor t = Except.ok pre ∧
            Ix.Kernel.Admission.prepareWith Address.admissionHash binding pre limits (Ix.Cert.recordsOf ixe order)
                  (Ix.Cert.blobsOf ixe order) (Ix.Cert.hintsOf ixe) =
                Except.ok (ev, ds) ∧
              Ix.Kernel.Cached.AcceptsRefUnder policy Ix.Kernel.CheckMode.verified ev ds.toList envA
-/
#guard_msgs in
#print Ix.Cert.IxonAcceptsRefUnder

/--
info: def Ix.Kernel.Cached.AcceptsRefUnder : {md : Ix.Kernel.Mode} →
  Ix.Kernel.Cached.AxiomPolicy →
    Ix.Kernel.CheckMode → Ix.Kernel.Evidences md → List (Ix.Kernel.Declaration md) → Ix.Kernel.Env md → Prop :=
fun {md} policy μ ev ds env =>
  ∃ F, Ix.Kernel.checkDeclsPureUnder μ policy (Ix.Kernel.fueledOps μ F) ev ds = Except.ok env
-/
#guard_msgs in
#print Ix.Kernel.Cached.AcceptsRefUnder

/--
info: def Ix.Kernel.checkDeclsPureUnder : {md : Ix.Kernel.Mode} →
  {m : Type → Type} →
    [Monad m] →
      [MonadExcept (Ix.Kernel.CheckError md) m] →
        Ix.Kernel.CheckMode →
          Ix.Kernel.Cached.AxiomPolicy →
            Ix.Kernel.CheckerOps md m →
              Ix.Kernel.Evidences md → List (Ix.Kernel.Declaration md) → m (Ix.Kernel.Env md) :=
fun {md} {m} [Monad m] [MonadExcept (Ix.Kernel.CheckError md) m] mode policy ops ev ds =>
  List.foldlM (Ix.Kernel.checkDeclUnder mode policy ops ev) Ix.Kernel.Env.empty ds
-/
#guard_msgs in
#print Ix.Kernel.checkDeclsPureUnder

/--
info: def Ix.Kernel.checkDeclUnder : {md : Ix.Kernel.Mode} →
  {m : Type → Type} →
    [Monad m] →
      [MonadExcept (Ix.Kernel.CheckError md) m] →
        Ix.Kernel.CheckMode →
          Ix.Kernel.Cached.AxiomPolicy →
            Ix.Kernel.CheckerOps md m →
              Ix.Kernel.Evidences md → Ix.Kernel.Env md → Ix.Kernel.Declaration md → m (Ix.Kernel.Env md) :=
fun {md} {m} [Monad m] [MonadExcept (Ix.Kernel.CheckError md) m] mode policy ops ev env d =>
  match d with
  | Ix.Kernel.Declaration.axiomDecl cv =>
    if policy.admits cv.name = true then Ix.Kernel.checkUserAxiomDecl ops env cv
    else Ix.Kernel.checkDecl mode ops ev env d
  | x => Ix.Kernel.checkDecl mode ops ev env d
-/
#guard_msgs in
#print Ix.Kernel.checkDeclUnder

/--
info: def Ix.Kernel.checkUserAxiomDecl : {md : Ix.Kernel.Mode} →
  {m : Type → Type} →
    [Monad m] →
      [MonadExcept (Ix.Kernel.CheckError md) m] →
        Ix.Kernel.CheckerOps md m → Ix.Kernel.Env md → Ix.Kernel.ConstantVal md → m (Ix.Kernel.Env md) :=
fun {md} {m} [Monad m] [MonadExcept (Ix.Kernel.CheckError md) m] ops env cv => do
  let cvA ← Ix.Kernel.checkConstantVal ops env cv
  pure { consts := Ix.Kernel.ConstantInfo.axiomInfo cvA :: env.consts }
-/
#guard_msgs in
#print Ix.Kernel.checkUserAxiomDecl

/-! ## IxC's reference normalizer -/

/--
info: def Ix.Kernel.nfRef : {md : Ix.Kernel.Mode} →
  Ix.Kernel.CheckMode → Ix.Kernel.Env md → ℕ → ℕ → Ix.Kernel.Expr md → Ix.Kernel.CheckM md (Ix.Kernel.Expr md) :=
fun {md} mode env fuel depth e => do
  let __do_lift ← Ix.Kernel.annotateCore mode env fuel depth e
  Ix.Kernel.nfGo mode env fuel fuel depth __do_lift
-/
#guard_msgs in
#print Ix.Kernel.nfRef

/--
info: @Ix.Kernel.nfGo.eq_def : ∀ {md : Ix.Kernel.Mode} (mode : Ix.Kernel.CheckMode) (env : Ix.Kernel.Env md) (fuel x x_1 : ℕ)
  (x_2 : Ix.Kernel.Expr md),
  Ix.Kernel.nfGo mode env fuel x x_1 x_2 =
    match x, x_1, x_2 with
    | 0, x, x_3 => throw (Ix.Kernel.CheckError.notImplemented [Ix.Kernel.MsgPart.text "normalization budget exhausted"])
    | budget.succ, depth, e => do
      let __do_lift ← Ix.Kernel.whnf mode env fuel depth e
      match __do_lift with
        | ty.lam body mb => do
          let ty' ← Ix.Kernel.nfGo mode env fuel budget depth ty
          let body' ← Ix.Kernel.nfGo mode env fuel budget (depth + 1) (body.instantiate1 (Ix.Kernel.Expr.fvar depth ty))
          pure (ty'.lam (body'.abstract1 depth) mb)
        | ty.forallE body mb => do
          let ty' ← Ix.Kernel.nfGo mode env fuel budget depth ty
          let body' ← Ix.Kernel.nfGo mode env fuel budget (depth + 1) (body.instantiate1 (Ix.Kernel.Expr.fvar depth ty))
          pure (ty'.forallE (body'.abstract1 depth) mb)
        | w => Ix.Kernel.nfSpine mode env fuel budget depth w
-/
#guard_msgs in
#check @Ix.Kernel.nfGo.eq_def

/--
info: @Ix.Kernel.nfSpine.eq_def : ∀ {md : Ix.Kernel.Mode} (mode : Ix.Kernel.CheckMode) (env : Ix.Kernel.Env md)
  (fuel x x_1 : ℕ) (x_2 : Ix.Kernel.Expr md),
  Ix.Kernel.nfSpine mode env fuel x x_1 x_2 =
    match x, x_1, x_2 with
    | 0, x, x_3 => throw (Ix.Kernel.CheckError.notImplemented [Ix.Kernel.MsgPart.text "normalization budget exhausted"])
    | budget.succ, depth, f.app a => do
      let __do_lift ← Ix.Kernel.nfSpine mode env fuel budget depth f
      let __do_lift_1 ← Ix.Kernel.nfGo mode env fuel budget depth a
      pure (__do_lift.app __do_lift_1)
    | budget.succ, depth, Ix.Kernel.Expr.proj s i e => do
      let __do_lift ← Ix.Kernel.nfGo mode env fuel budget depth e
      pure (Ix.Kernel.Expr.proj s i __do_lift)
    | n.succ, x, e => pure e
-/
#guard_msgs in
#check @Ix.Kernel.nfSpine.eq_def

/--
info: @Ix.Kernel.Expr.eraseMeta.eq_def : ∀ {md : Ix.Kernel.Mode} (x : Ix.Kernel.Expr md),
  x.eraseMeta =
    match x with
    | Ix.Kernel.Expr.fvar idx ty => Ix.Kernel.Expr.fvar idx ty.eraseMeta
    | f.app a => f.eraseMeta.app a.eraseMeta
    | ty.lam body m => ty.eraseMeta.lam body.eraseMeta default
    | ty.forallE body m => ty.eraseMeta.forallE body.eraseMeta default
    | ty.letE value body l => ty.eraseMeta.letE value.eraseMeta body.eraseMeta default
    | Ix.Kernel.Expr.proj s i e => Ix.Kernel.Expr.proj s i e.eraseMeta
    | e => e
-/
#guard_msgs in
#check @Ix.Kernel.Expr.eraseMeta.eq_def

/-! ## Views -/

/--
info: structure IxVM.Refinement.View : Type
number of parameters: 0
fields:
  IxVM.Refinement.View.env : Ixon.Env
  IxVM.Refinement.View.trees : List Ix.AssumptionTree :=
    []
constructor:
  IxVM.Refinement.View.mk (env : Ixon.Env) (trees : List Ix.AssumptionTree) : IxVM.Refinement.View
-/
#guard_msgs in
#print IxVM.Refinement.View

/--
info: def IxVM.Refinement.View.LeavesAt : IxVM.Refinement.View → Address → List Address → Prop :=
fun V root leaves => ∃ t ∈ V.trees, IxVM.Refinement.treeRoot t = root ∧ IxVM.Refinement.treeLeaves t = leaves
-/
#guard_msgs in
#print IxVM.Refinement.View.LeavesAt

/--
info: def IxVM.Refinement.View.HoldsTree : IxVM.Refinement.View → Address → Prop :=
fun V root => ∃ leaves, V.LeavesAt root leaves
-/
#guard_msgs in
#print IxVM.Refinement.View.HoldsTree

/--
info: def IxVM.Refinement.View.binding? : IxVM.Refinement.View → Address → Option Ix.Kernel.Admission.Binding :=
fun V address =>
  match V.env.roleBinding with
  | some rb => if rb.address = address then some { address := rb.address, bytes := rb.bytes } else none
  | none => none
-/
#guard_msgs in
#print IxVM.Refinement.View.binding?

/--
info: def IxVM.Refinement.View.Stores : IxVM.Refinement.View → Address → Prop :=
fun V a => V.env.consts.contains a = true
-/
#guard_msgs in
#print IxVM.Refinement.View.Stores

/--
info: def IxVM.Refinement.View.Authentic : IxVM.Refinement.View → Prop :=
fun V =>
  (∀ (a : Address) (lc : Ixon.LazyConstant),
      V.env.consts.get? a = some lc →
        Address.blake3Pure lc.rawBytes = a ∧ ∃ c, lc.get? = some c ∧ c.wireWF ∧ Ixon.serConstant c = lc.rawBytes) ∧
    (∀ (a : Address) (bytes : ByteArray), V.env.blobs.get? a = some bytes → Address.blake3Pure bytes = a) ∧
      ∀ (rb : Ixon.RoleBinding), V.env.roleBinding = some rb → Address.blake3Pure rb.bytes = rb.address
-/
#guard_msgs in
#print IxVM.Refinement.View.Authentic

/--
info: def IxVM.Refinement.View.Preimage : IxVM.Refinement.View → Address → ByteArray → Prop :=
fun V x bytes =>
  (∃ lc, V.env.consts.get? x = some lc ∧ lc.rawBytes = bytes) ∨
    V.env.blobs.get? x = some bytes ∨
      (∃ rb, V.env.roleBinding = some rb ∧ rb.address = x ∧ rb.bytes = bytes) ∨
        ∃ t ∈ V.trees, bytes ∈ IxVM.Refinement.treeImages t ∧ Address.blake3Pure bytes = x
-/
#guard_msgs in
#print IxVM.Refinement.View.Preimage

/--
info: def IxVM.Refinement.AnchorPinned : Ix.Kernel.Env Ix.Kernel.Mode.anon → Ix.Kernel.Role → Prop :=
fun envA r =>
  ∀ (n : ℕ) (ty : Ix.Kernel.Expr Ix.Kernel.Mode.anon),
    r.spec = Ix.Kernel.Spec.anchor n ty →
      ∃ ci,
        envA.find? (Ix.Kernel.Key.role r) = some ci ∧
          ci.toConstantVal.levelParams = List.range n ∧ ci.toConstantVal.type.eraseMeta = ty.eraseMeta
-/
#guard_msgs in
#print IxVM.Refinement.AnchorPinned

/--
info: def IxVM.Refinement.View.Closed : IxVM.Refinement.View → Prop :=
fun V =>
  (∀ (a : Address) (c : Ixon.Constant),
      Ix.Cert.recordAt V.env a = some c →
        IxVM.Refinement.SafeConstant c ∧
          IxVM.Refinement.ConstantExprsClosed V.env c ∧
            (∀ r ∈ c.refs.toList, V.env.consts.contains r = true ∨ V.env.blobs.contains r = true) ∧
              V.env.consts.contains (Ix.Cert.ownerOf a c) = true) ∧
    ∀ (rb : Ixon.RoleBinding),
      V.env.roleBinding = some rb →
        ∃ t,
          Ix.Kernel.RoleTable.ofBytes rb.bytes = some t ∧
            t.check = Except.ok () ∧
              (∃ pre, Ix.Kernel.Reader.preludeFor t = Except.ok pre) ∧
                (∀ (a : Address), IxVM.Refinement.BindingSeeds t a → V.env.consts.contains a = true) ∧
                  ∀ (r : Ix.Kernel.Role),
                    r.spec.kind = Ix.Kernel.SpecKind.anchor →
                      IxVM.Refinement.compilerTrust r = false →
                        ∀ (a : Address),
                          t.addressOf? r = some a →
                            IxVM.Refinement.AcceptsIn V
                              (IxVM.Refinement.Scope.strict { address := rb.address, bytes := rb.bytes }) (fun x => x = a)
                              fun x envA x_1 => IxVM.Refinement.AnchorPinned envA r
-/
#guard_msgs in
#print IxVM.Refinement.View.Closed

/--
info: def IxVM.Refinement.ConstantExprsClosed : Ixon.Env → Ixon.Constant → Prop :=
fun ixe c =>
  (∀ e ∈ c.info.exprs ++ c.sharing.toList, e.leanFragment = true ∧ IxVM.Refinement.ExprRefsClosed ixe c false e) ∧
    ∀ e ∈ c.info.exprs,
      (¬∃ d n, c.info = Ixon.ConstantInfo.defn d ∧ e = d.value ∧ IxVM.Refinement.IsProjFnAt c n d.value) →
        IxVM.Refinement.ExprRefsClosed ixe c true (Ix.Kernel.Reader.unshare c e)
-/
#guard_msgs in
#print IxVM.Refinement.ConstantExprsClosed

/--
info: def IxVM.Refinement.DirectProjTarget : Ixon.Env → Ixon.Constant → UInt64 → Prop :=
fun ixe c idx =>
  ∃ r cr cb ind ctor,
    c.refs[idx.toNat]? = some r ∧
      Ix.Cert.recordAt ixe r = some cr ∧
        Ix.Cert.recordAt ixe (Ix.Cert.ownerOf r cr) = some cb ∧
          cb.info = Ixon.ConstantInfo.muts #[Ixon.MutConst.indc ind] ∧
            ind.indices = 0 ∧
              ind.ctors = #[ctor] ∧ IxVM.Refinement.noArgRecur false (Ix.Kernel.Reader.unshare cb ctor.typ) = true
-/
#guard_msgs in
#print IxVM.Refinement.DirectProjTarget

/--
info: def IxVM.Refinement.View.TypingCovers : IxVM.Refinement.View → Ix.ClaimContext → Option Address → Prop :=
fun V ctx asm =>
  V.Closed ∧
    (V.binding? ctx.binding).isSome = true ∧
      (∀ (r : Address), asm = some r → V.HoldsTree r) ∧
        ∀ (r : Address),
          ctx.axioms = some r →
            V.HoldsTree r ∧
              (∀ (rb : Ixon.RoleBinding) (t : Ix.Kernel.RoleTable),
                  V.env.roleBinding = some rb →
                    Ix.Kernel.RoleTable.ofBytes rb.bytes = some t →
                      Ix.Kernel.Admission.admitAxiomPolicy Ix.Kernel.Cached.AxiomPolicy.allowUser t = Except.ok ()) ∧
                ∀ (leaves : List Address), V.LeavesAt r leaves → ∀ a ∈ leaves, V.Stores a
-/
#guard_msgs in
#print IxVM.Refinement.View.TypingCovers

/--
info: def IxVM.Refinement.SafeConstant : Ixon.Constant → Prop :=
fun c =>
  match c.info with
  | Ixon.ConstantInfo.defn d => d.safety = Ix.DefinitionSafety.safe
  | Ixon.ConstantInfo.recr r => r.isUnsafe = false
  | Ixon.ConstantInfo.axio a => a.isUnsafe = false
  | Ixon.ConstantInfo.muts ms => ∀ m ∈ ms.toList, IxVM.Refinement.SafeMutConst m
  | x => True
-/
#guard_msgs in
#print IxVM.Refinement.SafeConstant

/--
info: def IxVM.Refinement.SafeMutConst : Ixon.MutConst → Prop :=
fun x =>
  match x with
  | Ixon.MutConst.defn d => d.safety = Ix.DefinitionSafety.safe
  | Ixon.MutConst.indc i => i.isUnsafe = false ∧ ∀ ctor ∈ i.ctors.toList, ctor.isUnsafe = false
  | Ixon.MutConst.recr r => r.isUnsafe = false
-/
#guard_msgs in
#print IxVM.Refinement.SafeMutConst

example (c : Ixon.Constant) (e : Ixon.Expr) : IxVM.Refinement.IsProjFnAt c 0 e =
    (∃ i f v, Ix.Kernel.Reader.unshare c e = .prj i f v ∧ Ix.Kernel.Reader.unshare c v = .var 0) := rfl
example (c : Ixon.Constant) (n : Nat) (e : Ixon.Expr) : IxVM.Refinement.IsProjFnAt c (n + 1) e =
    (∃ ct t b, Ix.Kernel.Reader.unshare c e = .lam ct t b ∧ IxVM.Refinement.IsProjFnAt c n b) := rfl

example (a : Address) : IxVM.Refinement.treeRoot (.leaf a) = Ix.HostAdmission.Merkle.leaf a := rfl
example : IxVM.Refinement.treeRoot .padding = Ix.HostAdmission.Merkle.padding := rfl
example (l r : Ix.AssumptionTree) : IxVM.Refinement.treeRoot (.node l r) =
    Ix.HostAdmission.Merkle.node (IxVM.Refinement.treeRoot l) (IxVM.Refinement.treeRoot r) := rfl
example (a : Address) : IxVM.Refinement.treeLeaves (.leaf a) = [a] := rfl
example : IxVM.Refinement.treeLeaves .padding = [] := rfl
example (l r : Ix.AssumptionTree) : IxVM.Refinement.treeLeaves (.node l r) =
    IxVM.Refinement.treeLeaves l ++ IxVM.Refinement.treeLeaves r := rfl
example (a : Address) : IxVM.Refinement.treeImages (.leaf a) = [ByteArray.mk #[0] ++ a.hash] := rfl
example : IxVM.Refinement.treeImages .padding = [] := rfl
example (l r : Ix.AssumptionTree) : IxVM.Refinement.treeImages (.node l r) =
    (ByteArray.mk #[1] ++ (IxVM.Refinement.treeRoot l).hash ++ (IxVM.Refinement.treeRoot r).hash) ::
      (IxVM.Refinement.treeImages l ++ IxVM.Refinement.treeImages r) := rfl

/-! ## Phase 3: the TagN slice

The first refinement: every derivation of `IxonDeserialize::get_tagn0` agrees
with IxC's `Ixon.getTagN 0` on the same bytes, on every header
(`getTagN0_refines`; `getTagN2_refines` and `getTagN4_refines` for the two- and
four-bit flags), proved from the prepared source through its generated lookup
facts (`IxVM.Lookup`), the generated mirrors and their lemmas
(`Ix.IxVM.Refinement.Mirrors.TagN`, over the helper library
`Ix.IxVM.Refinement.Mirror`) and the hand-written creative layer
(`Ix.IxVM.Refinement.TagN`, `Ix.IxVM.Refinement.TagNWide`). Deterministic runs and their
completeness for worlds without control syntax: `EvalFn.exec`. -/

/--
info: @IxVM.Refinement.TagN.getTagN0_refines : ∀ {stream r : Aiur.SourceValue IxVM.F} {heap h' : Aiur.Heap IxVM.F}
  {bytes : List UInt8},
  Aiur.Library.Bytes.RepByteStream IxVM.Refinement.byteStreamEnum heap bytes stream →
    Aiur.Generic.SourceSemantics.EvalFn IxVM.Refinement.TagN.W "IxonDeserialize::get_tagn0" [stream] heap r h' →
      h' = heap ∧
        ∃ t n restPtr,
          Ixon.getTagN 0 (IxVM.Refinement.TagN.start bytes) =
              EStateM.Result.ok t { idx := n, bytes := { data := bytes.toArray } } ∧
            t.flag = 0 ∧
              Aiur.Library.Bytes.RepByteStream IxVM.Refinement.byteStreamEnum heap (List.drop n bytes) restPtr ∧
                r = Aiur.Value.tuple [IxVM.Refinement.TagN.u64Value t.value.toNat, restPtr]
-/
#guard_msgs in
#check @IxVM.Refinement.TagN.getTagN0_refines

/--
info: def IxVM.Refinement.TagN.u64Value : ℕ → Aiur.SourceValue IxVM.F :=
fun n =>
  Aiur.Value.tuple
    [Aiur.Value.field ↑(n % 256), Aiur.Value.field ↑(n / 256 % 256), Aiur.Value.field ↑(n / 65536 % 256),
      Aiur.Value.field ↑(n / 16777216 % 256), Aiur.Value.field ↑(n / 4294967296 % 256),
      Aiur.Value.field ↑(n / 1099511627776 % 256), Aiur.Value.field ↑(n / 281474976710656 % 256),
      Aiur.Value.field ↑(n / 72057594037927936 % 256)]
-/
#guard_msgs in
#print IxVM.Refinement.TagN.u64Value

/--
info: def IxVM.Refinement.TagN.start : List UInt8 → Ixon.GetState :=
fun bytes => { bytes := { data := bytes.toArray } }
-/
#guard_msgs in
#print IxVM.Refinement.TagN.start

/--
info: @Aiur.Generic.SourceSemantics.EvalFn.exec : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {world : Aiur.Generic.SourceSemantics.World F},
  Aiur.Generic.SourceSemantics.ControlFree world →
    ∀ {name : String} {args : List (Aiur.SourceValue F)} {before after : Aiur.Heap F} {result : Aiur.SourceValue F},
      Aiur.Generic.SourceSemantics.EvalFn world name args before result after →
        ∃ hs k0,
          ∀ k ≥ k0,
            ∀ (rest : Aiur.Generic.SourceSemantics.HintStream F),
              Aiur.Generic.SourceSemantics.execFn world k name args before (hs ++ rest) = some (result, after, rest)
-/
#guard_msgs in
#check @Aiur.Generic.SourceSemantics.EvalFn.exec

/-! ## Theorems and axioms -/

/--
info: @Aiur.Generic.SourceSemantics.EvalFn.observe : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {world : Aiur.Generic.SourceSemantics.World F} {name : String} {args : List (Aiur.SourceValue F)}
  {before after : Aiur.Heap F} {result : Aiur.SourceValue F},
  Aiur.Generic.SourceSemantics.EvalFn world name args before result after →
    ∃ calls, Aiur.Generic.SourceSemantics.ObsFn world name args before result after calls
-/
#guard_msgs in
#check @Aiur.Generic.SourceSemantics.EvalFn.observe

/--
info: @Aiur.Generic.SourceSemantics.ObsFn.erase : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {world : Aiur.Generic.SourceSemantics.World F} {name : String} {args : List (Aiur.SourceValue F)}
  {before after : Aiur.Heap F} {result : Aiur.SourceValue F} {calls : List (Aiur.Generic.SourceSemantics.Call F)},
  Aiur.Generic.SourceSemantics.ObsFn world name args before result after calls →
    Aiur.Generic.SourceSemantics.EvalFn world name args before result after
-/
#guard_msgs in
#check @Aiur.Generic.SourceSemantics.ObsFn.erase

/--
info: @Aiur.Modules.Prepared.EvalFn.observe : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {program : Aiur.Modules.Program F} {p : Aiur.Modules.Prepared program} {name : String}
  {args : List (Aiur.SourceValue F)} {value : Aiur.SourceValue F} {heap : Aiur.Heap F},
  p.EvalFn name args value heap → ∃ calls, p.ObsFn name args value heap calls
-/
#guard_msgs in
#check @Aiur.Modules.Prepared.EvalFn.observe

/--
info: @Aiur.Modules.Prepared.ObsFn.erase : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {program : Aiur.Modules.Program F} {p : Aiur.Modules.Prepared program} {name : String}
  {args : List (Aiur.SourceValue F)} {value : Aiur.SourceValue F} {heap : Aiur.Heap F}
  {calls : List (Aiur.Generic.SourceSemantics.Call F)},
  p.ObsFn name args value heap calls → p.EvalFn name args value heap
-/
#guard_msgs in
#check @Aiur.Modules.Prepared.ObsFn.erase

/--
info: @IxVM.Refinement.SourceSound.eval : ∀
  {P : List (Aiur.Generic.SourceSemantics.Call IxVM.F) → IxVM.Refinement.Digest → Prop},
  IxVM.Refinement.SourceSound P →
    ∀ {d : IxVM.Refinement.Digest} {value : Aiur.SourceValue IxVM.F} {heap : Aiur.Heap IxVM.F},
      Aiur.Generic.SourceSemantics.EvalFn IxVM.source.world IxVM.Refinement.verifyClaim [IxVM.Refinement.digestValue d]
          [] value heap →
        ∃ calls,
          Aiur.Generic.SourceSemantics.ObsFn IxVM.source.world IxVM.Refinement.verifyClaim
              [IxVM.Refinement.digestValue d] [] value heap calls ∧
            P calls d
-/
#guard_msgs in
#check @IxVM.Refinement.SourceSound.eval

/--
info: @IxVM.Refinement.SourceSound.run : ∀
  {P : List (Aiur.Generic.SourceSemantics.Call IxVM.F) → IxVM.Refinement.Digest → Prop},
  IxVM.Refinement.SourceSound P →
    ∀ {d : IxVM.Refinement.Digest} {fuel : ℕ} {hints : IxVM.source.HintProvider} {value : Aiur.SourceValue IxVM.F}
      {heap : Aiur.Heap IxVM.F},
      IxVM.source.run IxVM.Refinement.verifyClaim [IxVM.Refinement.digestValue d] fuel hints = Except.ok (value, heap) →
        ∃ calls,
          Aiur.Generic.SourceSemantics.ObsFn IxVM.source.world IxVM.Refinement.verifyClaim
              [IxVM.Refinement.digestValue d] [] value heap calls ∧
            P calls d
-/
#guard_msgs in
#check @IxVM.Refinement.SourceSound.run

/--
info: @IxVM.Refinement.circuitSoundAssuming_of_sourceSound : ∀
  {P : List (Aiur.Generic.SourceSemantics.Call IxVM.F) → IxVM.Refinement.Digest → Prop},
  IxVM.Refinement.SourceSound P → IxVM.Refinement.CircuitSoundAssuming P
-/
#guard_msgs in
#check @IxVM.Refinement.circuitSoundAssuming_of_sourceSound

/--
info: @IxVM.Refinement.observedHeadline : IxVM.Refinement.ObservedHeadline
-/
#guard_msgs in
#check @IxVM.Refinement.observedHeadline

/--
info: @IxVM.Refinement.circuitSound_of_sourceSound : ∀
  {P : List (Aiur.Generic.SourceSemantics.Call IxVM.F) → IxVM.Refinement.Digest → Prop},
  IxVM.Refinement.SourceSound P → IxVM.Refinement.CircuitSound P
-/
#guard_msgs in
#check @IxVM.Refinement.circuitSound_of_sourceSound

/--
info: @IxVM.Refinement.AcceptsIn.acceptsRefUnder : ∀ {V : IxVM.Refinement.View} {σ : IxVM.Refinement.Scope}
  {S : Address → Prop}
  {Q :
    Ix.Kernel.Admission.Binding →
      Ix.Kernel.Env Ix.Kernel.Mode.anon → List (Ix.Kernel.Declaration Ix.Kernel.Mode.anon) → Prop},
  IxVM.Refinement.AcceptsIn V σ S Q →
    ∃ ev ds envA,
      Ix.Kernel.Cached.AcceptsRefUnder σ.policy Ix.Kernel.CheckMode.verified ev
          (List.map IxVM.Refinement.thmToOpaqueDefn ds) envA ∧
        IxVM.Refinement.TheoremsInProp envA ds ∧ IxVM.Refinement.UserAxiomsWithin σ.axioms ds ∧ Q σ.binding envA ds
-/
#guard_msgs in
#check @IxVM.Refinement.AcceptsIn.acceptsRefUnder

/--
info: @IxVM.Refinement.AcceptsIn.acceptsRef : ∀ {V : IxVM.Refinement.View} {b : Ix.Kernel.Admission.Binding}
  {S : Address → Prop}
  {Q :
    Ix.Kernel.Admission.Binding →
      Ix.Kernel.Env Ix.Kernel.Mode.anon → List (Ix.Kernel.Declaration Ix.Kernel.Mode.anon) → Prop},
  IxVM.Refinement.AcceptsIn V (IxVM.Refinement.Scope.strict b) S Q →
    ∃ ev ds envA,
      Ix.Kernel.Cached.AcceptsRef Ix.Kernel.CheckMode.verified ev (List.map IxVM.Refinement.thmToOpaqueDefn ds) envA ∧
        IxVM.Refinement.TheoremsInProp envA ds ∧ Q b envA ds
-/
#guard_msgs in
#check @IxVM.Refinement.AcceptsIn.acceptsRef

/--
info: @Ix.Cert.ixonAcceptsRefUnder_strict : ∀ {binding : Ix.Kernel.Admission.Binding} {limits : Ix.Kernel.Admission.Limits}
  {ixe : Ixon.Env} {S : Address → Prop} {order : List Address} {envA : Ix.Kernel.Env Ix.Kernel.Mode.anon},
  Ix.Cert.IxonAcceptsRefUnder Ix.Kernel.Cached.AxiomPolicy.strict binding limits ixe S order envA ↔
    Ix.Cert.IxonAcceptsRef binding limits ixe S order envA
-/
#guard_msgs in
#check @Ix.Cert.ixonAcceptsRefUnder_strict

/--
info: @Ix.Kernel.Cached.acceptsRefUnder_strict : ∀ {md : Ix.Kernel.Mode} {μ : Ix.Kernel.CheckMode}
  {ev : Ix.Kernel.Evidences md} {ds : List (Ix.Kernel.Declaration md)} {env : Ix.Kernel.Env md},
  Ix.Kernel.Cached.AcceptsRefUnder Ix.Kernel.Cached.AxiomPolicy.strict μ ev ds env ↔
    Ix.Kernel.Cached.AcceptsRef μ ev ds env
-/
#guard_msgs in
#check @Ix.Kernel.Cached.acceptsRefUnder_strict

/--
info: @Ix.Kernel.Cached.acceptsRefUnder_iff_of_nil : ∀ {md : Ix.Kernel.Mode} {policy : Ix.Kernel.Cached.AxiomPolicy}
  {μ : Ix.Kernel.CheckMode} {ev : Ix.Kernel.Evidences md} {ds : List (Ix.Kernel.Declaration md)}
  {env : Ix.Kernel.Env md},
  Ix.Kernel.userAxiomsOfDecls ds = [] →
    (Ix.Kernel.Cached.AcceptsRefUnder policy μ ev ds env ↔ Ix.Kernel.Cached.AcceptsRef μ ev ds env)
-/
#guard_msgs in
#check @Ix.Kernel.Cached.acceptsRefUnder_iff_of_nil

/--
info: @Ix.Kernel.nfGo_zero : ∀ {md : Ix.Kernel.Mode} (mode : Ix.Kernel.CheckMode) (env : Ix.Kernel.Env md) (fuel depth : ℕ)
  (e : Ix.Kernel.Expr md),
  Ix.Kernel.nfGo mode env fuel 0 depth e =
    throw (Ix.Kernel.CheckError.notImplemented [Ix.Kernel.MsgPart.text "normalization budget exhausted"])
-/
#guard_msgs in
#check @Ix.Kernel.nfGo_zero

/--
info: @Ix.Kernel.nfGo_of_whnf_sort : ∀ {md : Ix.Kernel.Mode} {mode : Ix.Kernel.CheckMode} {env : Ix.Kernel.Env md}
  {fuel budget depth : ℕ} {e : Ix.Kernel.Expr md} {u : Ix.Kernel.Level},
  Ix.Kernel.whnf mode env fuel depth e = Except.ok (Ix.Kernel.Expr.sort u) →
    Ix.Kernel.nfGo mode env fuel (budget + 2) depth e = Except.ok (Ix.Kernel.Expr.sort u)
-/
#guard_msgs in
#check @Ix.Kernel.nfGo_of_whnf_sort

#guard_kernel_axioms Aiur.Generic.SourceSemantics.EvalFn.observe [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Aiur.Generic.SourceSemantics.ObsFn.erase [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.SourceSound.eval [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.SourceSound.run [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.circuitSoundAssuming_of_sourceSound [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.circuitSound_of_sourceSound [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.VerifyClaimSoundIn [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.VerifyClaimCircuitSoundIn [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.VerifyClaimCircuitSoundInAssuming [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.ObservedHeadline [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.observedHeadline [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.verifyClaimCircuitSoundIn_of_soundIn [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.verifyClaimCircuitSoundInAssuming_of_soundIn [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.TypingIn [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Cert.ixonAcceptsRefUnder_strict [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Cached.acceptsRefUnder_strict [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Cached.acceptsRefUnder_iff_of_nil [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.nfGo_of_whnf_sort [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.tablesChecked [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.source [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.TagN.getTagN0_refines [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.TagN.getTagN2_refines [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.TagN.getTagN4_refines [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.TagN.getTagN0_refines_at [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.TagN.getTagN2_refines_at [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.TagN.getTagN4_refines_at [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.TagN.getU64le_complete [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Mirrors.«IxonDeserialize::get_tagn0».of_eval [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Mirrors.«UInt64::add».of_eval [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Aiur.Generic.SourceSemantics.EvalFn.exec [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Aiur.Generic.Source.controlFree [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Aiur.Generic.SourceSemantics.execFn_unique_of_runs [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.TagN.controlFree [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Cached.AcceptsRefUnder.unique [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.checkDeclsFromUnder_append [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.nfRef_deterministic [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Kernel.Expr.eraseMeta_idem [propext]
#guard_kernel_axioms Ix.Cert.ixonAcceptsRef_of_under_nil [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.functionNames_nodup [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.IxonDeserialize.get_tagn0.lookup [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Deserialize.u64BytesMeasure_dec [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Deserialize.buildSuccChain_complete [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Deserialize.getU64List_complete [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Deserialize.u64IsZero_run [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Deserialize.u64Eq_run [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Deserialize.u64ToField_run [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Deserialize.u64SaturatingPred_run [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Deserialize.u64WrappingSucc_run [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Deserialize.getQuotKind_run [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Deserialize.unpackDefKindSafety_run [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Deserialize.getLamMode_run [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Deserialize.getAllMode_run [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Deserialize.buildSuccChain_run [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Deserialize.readByte_refines [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Deserialize.assertWireBool_refines [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Deserialize.getQuotKind_refines [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Deserialize.unpackDefKindSafety_refines [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Deserialize.getLamMode_refines [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Deserialize.getAllMode_refines [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Deserialize.buildSuccChain_refines [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Mirrors.«IxonDeserialize::get_all_mode».of_eval [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.Mirrors.«IxonDeserialize::get_lam_mode».of_eval [propext, Classical.choice, Quot.sound]

#guard_module_axioms Aiur.Generic.Observe Ix.IxVM.Refinement.Claim Ix.IxVM.Refinement.Statement
  Ix.Cert.AcceptsUnder IxC.Kernel.Verify.Cached.ReferenceUnder IxC.Kernel.Verify.Cached.NormalizeRef
  IxVM.Source IxVM.Static IxVM.Program IxVM.Tables IxVM.Lookup
  Aiur.Generic.LookupFacts Ix.IxVM.Refinement.Exec Ix.IxVM.Refinement.Mirror Ix.IxVM.Refinement.Mirrors.TagN
  Ix.IxVM.Refinement.Mirrors.Deserialize Ix.IxVM.Refinement.TagN Ix.IxVM.Refinement.TagNWide
  Ix.IxVM.Refinement.Deserialize
