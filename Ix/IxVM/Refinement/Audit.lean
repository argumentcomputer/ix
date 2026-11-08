import Ix.IxVM.Refinement.Statement
import IxC.Kernel.Audit.Axioms

/-! # The IxVM ↔ IxC refinement statement, frozen

`#print` freezes every statement (`def … : Prop`) of
`Ix.IxVM.Refinement.Statement` and every definition they read from
`Ix.IxVM.Refinement.Claim`; the structurally recursive tree functions are
frozen by their equations. `#check` freezes the proved composition theorems,
and `#guard_kernel_axioms` and `#guard_module_axioms` freeze the axioms of
the statements, the theorems and both modules (decision D5: `propext`,
`Classical.choice`, `Quot.sound`). A change to any of them fails the build,
so the statement cannot drift silently. The module is outside any namespace,
so every name prints in full.

Two guards keep the statement about the deployed object:

* it names `IxVM.program` and the entry `IxVM::verify_claim` (the `run_meta`
  check, beside the frozen text);
* it is not vacuous for want of a preparation: preparing `IxVM.program` for
  `verify_claim` succeeds, selects the entry, and the entry's world prepares
  a call on a digest argument (`#guard`, evaluated when this module builds;
  an evaluation, not a proof). -/

example : IxVM.Refinement.verifyClaim = "IxVM::verify_claim" := rfl

open Lean in
run_meta do
  let names : List (Name × List Name) := [
    (``IxVM.Refinement.SourceSound, [``IxVM.program, ``IxVM.Refinement.verifyClaim,
      ``Aiur.Modules.prepare, ``Aiur.Modules.Prepared.EvalFn, ``IxVM.Refinement.digestValue]),
    (``IxVM.Refinement.CircuitSound, [``IxVM.program, ``IxVM.Refinement.verifyClaim,
      ``Aiur.Modules.prepare, ``IxVM.Refinement.AcyclicDerivation, ``IxVM.Refinement.digestValue]),
    (``IxVM.Refinement.IxVMClaimSpec, [``IxVM.Refinement.packDigest, ``Address.blake3Pure,
      ``Ix.Claim.de, ``Ix.Claim.Holds]),
    (``IxVM.Refinement.IxVMClaimSpecIn, [``IxVM.Refinement.packDigest, ``Address.blake3Pure,
      ``Ix.Claim.de, ``Ix.Claim.HoldsIn, ``IxVM.Refinement.View.Collision])]
  for (statement, needed) in names do
    let some info := (← getEnv).find? statement | throwError "{statement} is missing"
    let used := info.value!.getUsedConstants
    for n in needed do
      unless used.contains n do throwError "{statement} no longer names {n}"

#guard match Aiur.Modules.prepare IxVM.program [IxVM.Refinement.verifyClaim] with
  | .ok prepared => match prepared.find? IxVM.Refinement.verifyClaim with
    | some entry =>
      (prepared.environment.source.world.prepare entry.resolved.name
        [IxVM.Refinement.digestValue 0]).toBool
    | none => false
  | .error _ => false

/-! ## The statements -/

/--
info: def IxVM.Refinement.VerifyClaimSound : Prop :=
IxVM.Refinement.SourceSound IxVM.Refinement.IxVMClaimSpec
-/
#guard_msgs in
#print IxVM.Refinement.VerifyClaimSound

/--
info: def IxVM.Refinement.VerifyClaimSoundIn : Prop :=
IxVM.Refinement.SourceSound IxVM.Refinement.IxVMClaimSpecIn
-/
#guard_msgs in
#print IxVM.Refinement.VerifyClaimSoundIn

/--
info: def IxVM.Refinement.VerifyClaimCircuitSound : Prop :=
IxVM.Refinement.CircuitSound IxVM.Refinement.IxVMClaimSpec
-/
#guard_msgs in
#print IxVM.Refinement.VerifyClaimCircuitSound

/--
info: def IxVM.Refinement.VerifyClaimCircuitSoundIn : Prop :=
IxVM.Refinement.CircuitSound IxVM.Refinement.IxVMClaimSpecIn
-/
#guard_msgs in
#print IxVM.Refinement.VerifyClaimCircuitSoundIn

/--
info: def IxVM.Refinement.SourceSound : (IxVM.Refinement.Digest → Prop) → Prop :=
fun P =>
  ∀ (prepared : Aiur.Modules.Prepared IxVM.program),
    Aiur.Modules.prepare IxVM.program [IxVM.Refinement.verifyClaim] = Except.ok prepared →
      ∀ (d : IxVM.Refinement.Digest) (value : Aiur.SourceValue IxVM.F) (heap : Aiur.Heap IxVM.F),
        prepared.EvalFn IxVM.Refinement.verifyClaim [IxVM.Refinement.digestValue d] value heap → P d
-/
#guard_msgs in
#print IxVM.Refinement.SourceSound

/--
info: def IxVM.Refinement.CircuitSound : (IxVM.Refinement.Digest → Prop) → Prop :=
fun P =>
  ∀ (prepared : Aiur.Modules.Prepared IxVM.program),
    Aiur.Modules.prepare IxVM.program [IxVM.Refinement.verifyClaim] = Except.ok prepared →
      ∀ {id : String → Except String ℕ} (compiled : Aiur.Optimized.ModulesArtifact prepared)
        (physical : Aiur.Optimized.Physical.Prepared compiled.circuit.artifact)
        (plan : Aiur.Optimized.Grouping.Plan physical.system id),
        plan.WellFormedActivation →
          ∀ {entry : Aiur.Modules.Selection IxVM.program prepared.environment.assembly.instances},
            prepared.find? IxVM.Refinement.verifyClaim = some entry →
              ∀ {rom : Aiur.WidthROM IxVM.F},
                rom.Valid →
                  ∀ (d : IxVM.Refinement.Digest) {wires : List (Aiur.WireValue IxVM.F)} {output : Aiur.WireValue IxVM.F}
                    {result : Aiur.Value IxVM.F},
                    Aiur.Circuit.Erasure.Signed compiled.circuit.system
                        { channel := entry.resolved.name, args := wires, result := output } →
                      IxVM.Refinement.AcyclicDerivation compiled plan rom
                          { channel := entry.resolved.name, args := wires, result := output } →
                        Aiur.DecodesValues compiled.specialized.program.enums wires
                            (Aiur.entryValues [IxVM.Refinement.digestValue d]) →
                          Aiur.WireValue.decode compiled.specialized.program.enums output = some result → P d
-/
#guard_msgs in
#print IxVM.Refinement.CircuitSound

/--
info: def IxVM.Refinement.AcyclicDerivation : {F : Type} →
  [inst : Field F] →
    [inst_1 : DecidableEq F] →
      {program : Aiur.Modules.Program F} →
        {prepared : Aiur.Modules.Prepared program} →
          (compiled : Aiur.Optimized.ModulesArtifact prepared) →
            {physical : Aiur.Optimized.Physical.Prepared compiled.circuit.artifact} →
              {id : String → Except String ℕ} →
                Aiur.Optimized.Grouping.Plan physical.system id → Aiur.WidthROM F → Aiur.Circuit.Message F → Prop :=
fun {F} [Field F] [DecidableEq F] {program} {prepared} compiled {physical} {id} plan rom root =>
  plan.ActivatedDerives (Aiur.Circuit.Erasure.rawROM rom) (Aiur.Circuit.Erasure.message compiled.circuit.system root)
-/
#guard_msgs in
#print IxVM.Refinement.AcyclicDerivation

/--
info: def IxVM.Refinement.IxVMClaimSpec : IxVM.Refinement.Digest → Prop :=
fun d =>
  ∃ bytes c, IxVM.Refinement.packDigest (Address.blake3Pure bytes) = d ∧ Ix.Claim.de bytes = Except.ok c ∧ c.Holds
-/
#guard_msgs in
#print IxVM.Refinement.IxVMClaimSpec

/--
info: def IxVM.Refinement.IxVMClaimSpecIn : IxVM.Refinement.Digest → Prop :=
fun d =>
  ∀ (bytes : ByteArray) (c : Ix.Claim) (V : IxVM.Refinement.View),
    Ix.Claim.de bytes = Except.ok c →
      IxVM.Refinement.packDigest (Address.blake3Pure bytes) = d →
        V.Authentic → Ix.Claim.Covers V c → Ix.Claim.HoldsIn V c ∨ V.Collision [bytes]
-/
#guard_msgs in
#print IxVM.Refinement.IxVMClaimSpecIn

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

/-! ## What a claim means -/

/--
info: def Ix.Claim.Holds : Ix.Claim → Prop :=
fun c => ∃ V, V.Authentic ∧ Ix.Claim.HoldsIn V c
-/
#guard_msgs in
#print Ix.Claim.Holds

/--
info: def Ix.Claim.HoldsIn : IxVM.Refinement.View → Ix.Claim → Prop :=
fun V x =>
  match x with
  | Ix.Claim.eval ctx input output asm =>
    IxVM.Refinement.TypingIn V ctx (fun x => x = input) asm ∧ IxVM.Refinement.EvalOutputIn V output
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
  | Ix.Claim.eval ctx input output asm => V.TypingCovers ctx asm ∧ V.Stores input ∧ V.Stores output
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
info: def IxVM.Refinement.TypingIn : IxVM.Refinement.View → Ix.ClaimContext → (Address → Prop) → Option Address → Prop :=
fun V ctx S asm =>
  Ix.SpecDigest.specDigest = Except.ok ctx.spec ∧
    ctx.literalClass = false ∧
      (ctx.axioms = none →
        (ctx.bindingAssumed = true → IxVM.Refinement.BindingIn V ctx.spec ctx.binding) →
          ∃ b, V.binding? ctx.binding = some b ∧ IxVM.Refinement.AssumingIn V b S asm)
-/
#guard_msgs in
#print IxVM.Refinement.TypingIn

/--
info: def IxVM.Refinement.AssumingIn : IxVM.Refinement.View →
  Ix.Kernel.Admission.Binding → (Address → Prop) → Option Address → Prop :=
fun V b S x =>
  match x with
  | none => IxVM.Refinement.AcceptsIn V b S
  | some r =>
    V.HoldsTree r ∧
      ∀ (leaves : List Address),
        V.LeavesAt r leaves →
          (∀ a ∈ leaves, IxVM.Refinement.AcceptsIn V b fun x => x = a) → IxVM.Refinement.AcceptsIn V b S
-/
#guard_msgs in
#print IxVM.Refinement.AssumingIn

/--
info: def IxVM.Refinement.AcceptsIn : IxVM.Refinement.View → Ix.Kernel.Admission.Binding → (Address → Prop) → Prop :=
fun V b S =>
  ∃ E limits order envA,
    IxVM.Refinement.Draws E V.env ∧
      (∀ (a : Address), S a → E.consts.contains a = true) ∧ Ix.Cert.IxonAcceptsRef b limits E S order envA
-/
#guard_msgs in
#print IxVM.Refinement.AcceptsIn

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
info: def IxVM.Refinement.BindingIn : IxVM.Refinement.View → Address → Address → Prop :=
fun V spec b =>
  Ix.SpecDigest.specDigest = Except.ok spec ∧
    ∃ bnd t,
      V.binding? b = some bnd ∧
        Ix.Kernel.Admission.admitBinding Address.admissionHash bnd = Except.ok t ∧
          (∀ r ∈ Ix.Kernel.Role.all, (t.addressOf? r).isSome = true) ∧
            IxVM.Refinement.AcceptsIn V bnd (IxVM.Refinement.BindingSeeds t)
-/
#guard_msgs in
#print IxVM.Refinement.BindingIn

/--
info: def IxVM.Refinement.BindingSeeds : Ix.Kernel.RoleTable → Address → Prop :=
fun t a => (∃ r, t.addressOf? r = some a) ∨ ∃ e ∈ t.evidence.toList, Ix.Kernel.Evidence.proof a ∈ e.2.toList
-/
#guard_msgs in
#print IxVM.Refinement.BindingSeeds

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
  (∀ (a : Address) (lc : Ixon.LazyConstant), V.env.consts.get? a = some lc → Address.blake3Pure lc.rawBytes = a) ∧
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
info: def IxVM.Refinement.View.Collision : IxVM.Refinement.View → List ByteArray → Prop :=
fun V extra =>
  ∃ x held other,
    (V.Preimage x held ∨ held ∈ extra ∧ Address.blake3Pure held = x) ∧ other ≠ held ∧ Address.blake3Pure other = x
-/
#guard_msgs in
#print IxVM.Refinement.View.Collision

/--
info: def IxVM.Refinement.View.Closed : IxVM.Refinement.View → Prop :=
fun V =>
  (∀ (a : Address) (c : Ixon.Constant),
      Ix.Cert.recordAt V.env a = some c →
        (∀ r ∈ c.refs.toList, V.env.consts.contains r = true ∨ V.env.blobs.contains r = true) ∧
          V.env.consts.contains (Ix.Cert.ownerOf a c) = true) ∧
    ∀ (rb : Ixon.RoleBinding) (t : Ix.Kernel.RoleTable),
      V.env.roleBinding = some rb →
        Ix.Kernel.RoleTable.ofBytes rb.bytes = some t →
          ∀ (a : Address), IxVM.Refinement.BindingSeeds t a → V.env.consts.contains a = true
-/
#guard_msgs in
#print IxVM.Refinement.View.Closed

/--
info: def IxVM.Refinement.View.TypingCovers : IxVM.Refinement.View → Ix.ClaimContext → Option Address → Prop :=
fun V ctx asm => V.Closed ∧ (V.binding? ctx.binding).isSome = true ∧ ∀ (r : Address), asm = some r → V.HoldsTree r
-/
#guard_msgs in
#print IxVM.Refinement.View.TypingCovers

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

/-! ## Theorems and axioms -/

/--
info: @IxVM.Refinement.circuitSound_of_sourceSound : ∀ {P : IxVM.Refinement.Digest → Prop},
  IxVM.Refinement.SourceSound P → IxVM.Refinement.CircuitSound P
-/
#guard_msgs in
#check @IxVM.Refinement.circuitSound_of_sourceSound

/--
info: @IxVM.Refinement.SourceSound.run : ∀ {P : IxVM.Refinement.Digest → Prop},
  IxVM.Refinement.SourceSound P →
    ∀ {prepared : Aiur.Modules.Prepared IxVM.program},
      Aiur.Modules.prepare IxVM.program [IxVM.Refinement.verifyClaim] = Except.ok prepared →
        ∀ {d : IxVM.Refinement.Digest} {fuel : ℕ} {hints : prepared.environment.source.HintProvider}
          {value : Aiur.SourceValue IxVM.F} {heap : Aiur.Heap IxVM.F},
          prepared.run IxVM.Refinement.verifyClaim [IxVM.Refinement.digestValue d] fuel hints =
              Except.ok (value, heap) →
            P d
-/
#guard_msgs in
#check @IxVM.Refinement.SourceSound.run

#guard_kernel_axioms IxVM.Refinement.circuitSound_of_sourceSound [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.SourceSound.run [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.VerifyClaimSound [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.VerifyClaimSoundIn [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.VerifyClaimCircuitSound [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms IxVM.Refinement.VerifyClaimCircuitSoundIn [propext, Classical.choice, Quot.sound]

#guard_module_axioms Ix.IxVM.Refinement.Claim Ix.IxVM.Refinement.Statement
