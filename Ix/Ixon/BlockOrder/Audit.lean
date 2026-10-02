import Ix.Ixon.BlockOrder.Theorems
import Ix.Ixon.Projection.Audit

namespace Ix.Ixon.BlockOrder.Audit

/-- The certified entry with canonical block order. -/
def operations : Array Lean.Name := #[``checkBytes, ``canonicalClasses, ``compareExpr]

def allowedData (name : Lean.Name) : Bool :=
  Projection.Audit.allowedData name || name == `Ix.Ixon.ReduceUniverse || name == `Ix.Ixon.BlockOrder

def allowedProof (name : Lean.Name) : Bool :=
  allowedData name || Projection.Audit.allowedProof name || name == `Ix.Ixon.BlockOrder.Theorems

end Ix.Ixon.BlockOrder.Audit

#guard_msgs (drop info) in
run_cmd Ix.Ixon.Projection.Audit.checkImports #[`Ix.Ixon.BlockOrder] Ix.Ixon.BlockOrder.Audit.allowedData

#guard_msgs (drop info) in
run_cmd Ix.Ixon.Projection.Audit.checkImports #[`Ix.Ixon.BlockOrder.Theorems] Ix.Ixon.BlockOrder.Audit.allowedProof

#guard !Ix.Ixon.BlockOrder.Audit.allowedData `Ix.Ixon.BlockOrder.Theorems
#guard !Ix.Ixon.BlockOrder.Audit.allowedData `Ix.Tc.CanonicalCheck
#guard !Ix.Ixon.BlockOrder.Audit.allowedData `Blake3.Rust
#guard !Ix.Ixon.BlockOrder.Audit.allowedData `Blake3.C
#guard !Ix.Ixon.BlockOrder.Audit.allowedData `Ix.IxonUniv
#guard !Ix.Ixon.Projection.Audit.allowedData `Ix.Ixon.BlockOrder
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Ix.Ixon.BlockOrder Ix.Kernel.Audit.importDenylist
#guard !Ix.Kernel.Audit.allowed Ix.Ixon.Audit.dataImports `Ix.Ixon.BlockOrder
#guard !Ix.Kernel.Audit.allowed Ix.Ixon.Admission.Audit.dataImports `Ix.Ixon.BlockOrder Ix.Kernel.Audit.importDenylist
#guard !Ix.Ixon.BlockOrder.Audit.allowedData `Ix.Ixon.BlockOrder.Audit

/- Measured before freezing: the certified entry adds the order check to the
certified projection entry (`Ix.Ixon.Projection.Audit`), with the same ruled
constructs. A block of recursors is checked in motive order (`checkRecord`,
`isRecursor`, `checkMotives`, `recursorMotive`), which reuses the reader's
`stripAll` and `appHead` (`IxonReader.analyseRecursor`); every other block
is checked in canonical structural order. -/
/-- info: runtime closure of [Ix.Ixon.BlockOrder.checkBytes,
 Ix.Ixon.BlockOrder.canonicalClasses,
 Ix.Ixon.BlockOrder.compareExpr]: 5563 compiled functions; inherited externs 132, implemented_by 0,
unsafe 23, csimp 4; ruled computed_field 18, csimp 21, partial 10 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith Ix.Ixon.BlockOrder.Audit.operations #[`Init, `Std] Ix.Kernel.Audit.runtimeRulings

#guard_kernel_axioms Ix.Ixon.BlockOrder.Refinement.positive [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.Refinement.fixedPoint [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.refine_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.refine_fixedPoint [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.refine_mono [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.canonicalClasses_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.checkBlock_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.recursorMotive_of_analyse [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.motivesFrom_cons [propext, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.checkMotives_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.checkMotiveOrder_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.checkRecord_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.checkConstants_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.checkBytes [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.checkBytes_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.checkBytes_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.checkBytes_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.checkBytes_no_proof_of_False [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ix.Ixon.BlockOrder.checkBytes_of_ordered [propext, Classical.choice, Quot.sound]

/-- info: Ix.Ixon.BlockOrder.refine_ok_iff : ∀ (block : Ix.Ixon.BlockOrder.Block) (comparison fuel : Nat)
  (initial result : Ix.Ixon.BlockOrder.Classes),
  Ix.Ixon.BlockOrder.refine block comparison fuel initial = Except.ok result ↔
    ∃ rounds, rounds ≤ fuel ∧ Ix.Ixon.BlockOrder.Refinement block comparison rounds initial result -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.BlockOrder.refine_ok_iff

/-- info: @Ix.Ixon.BlockOrder.refine_fixedPoint : ∀ {block : Ix.Ixon.BlockOrder.Block} {comparison fuel : Nat}
  {initial result : Ix.Ixon.BlockOrder.Classes},
  Ix.Ixon.BlockOrder.refine block comparison fuel initial = Except.ok result →
    Ix.Ixon.BlockOrder.refineStep block comparison result = Except.ok result -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.BlockOrder.refine_fixedPoint

/-- info: Ix.Ixon.BlockOrder.checkBlock_ok_iff : ∀ (limits : Ix.Ixon.BlockOrder.Limits) (owner : Address) (source : Ixon.Constant)
  (blobs : Ix.Kernel.Ingress.Blobs),
  Ix.Ixon.BlockOrder.checkBlock limits owner source blobs = Except.ok () ↔
    Ix.Ixon.BlockOrder.Canonical limits owner source blobs -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.BlockOrder.checkBlock_ok_iff

/- Recursor blocks in motive order. `Ordered`, which every entry theorem
below states, is `OrderedRecord` at each record: a block of recursors must
be `MotiveOrdered` (member `j` eliminates motive `j`, read off its type as
the reader reads it, `recursorMotive_of_analyse`, and declares one motive
per member); every other `muts` block must be `Canonical`. These freeze
what `Ordered` means. -/
/-- info: def Ix.Ixon.BlockOrder.OrderedRecord : Ix.Ixon.BlockOrder.Limits →
  Ix.Kernel.Ingress.Blobs → Address × Ixon.Constant → Prop :=
fun limits blobs pair =>
  match pair.snd.info with
  | Ixon.ConstantInfo.muts members =>
    if members.all Ix.Ixon.BlockOrder.isRecursor = true then Ix.Ixon.BlockOrder.MotiveOrdered pair.snd members
    else Ix.Ixon.BlockOrder.Canonical limits pair.fst pair.snd blobs
  | x => True -/
#guard_msgs (whitespace := lax) in
#print Ix.Ixon.BlockOrder.OrderedRecord

/-- info: def Ix.Ixon.BlockOrder.MotivesFrom : Ixon.Constant → Nat → Nat → List Ixon.MutConst → Prop :=
fun source size start members =>
  ∀ (j : Nat) (h : j < members.length),
    ∃ r,
      members[j] = Ixon.MutConst.recr r ∧
        r.motives.toNat = size ∧ Ix.Ixon.BlockOrder.recursorMotive source r = some (start + j) -/
#guard_msgs (whitespace := lax) in
#print Ix.Ixon.BlockOrder.MotivesFrom

/-- info: Ix.Ixon.BlockOrder.checkRecord_ok_iff : ∀ (limits : Ix.Ixon.BlockOrder.Limits) (blobs : Ix.Kernel.Ingress.Blobs)
  (owner : Address) (source : Ixon.Constant),
  Ix.Ixon.BlockOrder.checkRecord limits blobs owner source = Except.ok () ↔
    Ix.Ixon.BlockOrder.OrderedRecord limits blobs (owner, source) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.BlockOrder.checkRecord_ok_iff

/-! ### The certified entry's theorems -/

/-- info: Ix.Ixon.BlockOrder.checkBytes_ok_iff : ∀ (maxProjections : Nat) (limits : Ix.Ixon.Admission.Limits)
  (orderLimits : Ix.Ixon.BlockOrder.Limits) (records : Ix.Ixon.Admission.Records) (blobs : Ix.Kernel.Ingress.Blobs)
  (hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint) (env : Ix.Kernel.Env),
  Ix.Ixon.BlockOrder.checkBytes maxProjections limits orderLimits records blobs hint = Except.ok env ↔
    Ix.Ixon.Verify.Admission.WithinBatch limits records blobs ∧
      Ix.Ixon.Verify.Admission.UniqueKeys records blobs ∧
        ∃ input output,
          Ix.Ixon.Verify.Admission.RecordsRead limits records input ∧
            Ix.Ixon.Projection.Expanded maxProjections input output ∧
              Ix.Ixon.BlockOrder.Ordered orderLimits blobs input ∧
                Ix.Ixon.Admission.checkConstants output blobs hint = Except.ok env -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.BlockOrder.checkBytes_ok_iff

/-- info: @Ix.Ixon.BlockOrder.checkBytes_reading : ∀ {maxProjections : Nat} {limits : Ix.Ixon.Admission.Limits}
  {orderLimits : Ix.Ixon.BlockOrder.Limits} {records : Ix.Ixon.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ix.Ixon.BlockOrder.checkBytes maxProjections limits orderLimits records blobs hint = Except.ok env →
    Ix.Ixon.Verify.Admission.UniqueKeys records blobs ∧
      ∃ input output,
        Ix.Ixon.Verify.Admission.RecordsRead limits records input ∧
          Ix.Ixon.Projection.Expanded maxProjections input output ∧
            Ix.Ixon.BlockOrder.Ordered orderLimits blobs input ∧
              ∃ pins pre natPins,
                Ix.Kernel.IxonReader.defaultPins = Except.ok pins ∧
                  Ix.Kernel.IxonReader.builtinPrelude = Except.ok pre ∧
                    Ix.Kernel.IxonReader.builtinNatOpPins = Except.ok natPins ∧
                      Ix.Ixon.Admission.Installed pins pre natPins output blobs hint env -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.BlockOrder.checkBytes_reading

/-- info: Ix.Ixon.BlockOrder.checkBytes_has_model : ∀ (V : Type u_1) [inst : Ix.Kernel.SetTheory V] {maxProjections : Nat}
  {limits : Ix.Ixon.Admission.Limits} {orderLimits : Ix.Ixon.BlockOrder.Limits} {records : Ix.Ixon.Admission.Records}
  {blobs : Ix.Kernel.Ingress.Blobs} {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint}
  {env : Ix.Kernel.Env},
  Ix.Ixon.BlockOrder.checkBytes maxProjections limits orderLimits records blobs hint = Except.ok env →
    Nonempty (Ix.Kernel.Model V env) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.BlockOrder.checkBytes_has_model

/-- info: Ix.Ixon.BlockOrder.checkBytes_no_proof_of_False : ∀ (V : Type u_1) [Ix.Kernel.SetTheory V] {maxProjections : Nat}
  {limits : Ix.Ixon.Admission.Limits} {orderLimits : Ix.Ixon.BlockOrder.Limits} {records : Ix.Ixon.Admission.Records}
  {blobs : Ix.Kernel.Ingress.Blobs} {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint}
  {env : Ix.Kernel.Env},
  Ix.Ixon.BlockOrder.checkBytes maxProjections limits orderLimits records blobs hint = Except.ok env →
    ∀ (ci : Ix.Kernel.ConstantInfo),
      ci ∈ env.consts → ci.toConstantVal.type = Ix.Kernel.Expr.const Ix.Kernel.falseName [] → False -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.BlockOrder.checkBytes_no_proof_of_False

/-- info: @Ix.Ixon.BlockOrder.checkBytes_of_ordered : ∀ {maxProjections : Nat} {limits : Ix.Ixon.Admission.Limits}
  {orderLimits : Ix.Ixon.BlockOrder.Limits} {records : Ix.Ixon.Admission.Records}
  {input output : Ix.Kernel.Ingress.Constants} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint},
  Ix.Ixon.Verify.Admission.WithinBatch limits records blobs →
    Ix.Ixon.Verify.Admission.UniqueKeys records blobs →
      Ix.Ixon.Verify.Admission.RecordsRead limits records input →
        Ix.Ixon.Projection.Expanded maxProjections input output →
          Ix.Ixon.BlockOrder.Ordered orderLimits blobs input →
            Ix.Ixon.BlockOrder.checkBytes maxProjections limits orderLimits records blobs hint =
              Except.mapError Ix.Ixon.BlockOrder.CheckError.checker
                (Ix.Ixon.Admission.checkConstants output blobs hint) -/
#guard_msgs (whitespace := lax) in
#check @Ix.Ixon.BlockOrder.checkBytes_of_ordered

/- The certified entry's order check reaches no extern or unsafe primitive
beyond the certified projection entry's (the fold's closure already uses
`String.compare`, the `UInt64` operations and `Array.uget`). -/
/-- info: Additional certified block-order externs: []
---
info: Additional certified block-order unsafe: [] -/
#guard_msgs (whitespace := lax) in
run_cmd do
  let env ← Lean.getEnv
  let before := Ix.Kernel.Audit.runtimeClosure env Ix.Ixon.Projection.Audit.operations
  let after := Ix.Kernel.Audit.runtimeClosure env Ix.Ixon.BlockOrder.Audit.operations
  Lean.logInfo m!"Additional certified block-order externs: {after.externs.filter (!before.externs.contains ·)}"
  Lean.logInfo m!"Additional certified block-order unsafe: {after.unsafes.filter (!before.unsafes.contains ·)}"
