import Ix.Ixon.BlockOrder.Theorems
import Ix.Ixon.Projection.Audit

namespace Ixon.BlockOrder.Audit

/-- The certified entry with canonical block order. -/
def operations : Array Lean.Name := #[``checkBytes, ``canonicalClasses, ``compareExpr]

def allowedData (name : Lean.Name) : Bool :=
  Projection.Audit.allowedData name || name == `Ix.Ixon.ReduceUniverse || name == `Ix.Ixon.BlockOrder

def allowedProof (name : Lean.Name) : Bool :=
  allowedData name || Projection.Audit.allowedProof name || name == `Ix.Ixon.BlockOrder.Theorems

end Ixon.BlockOrder.Audit

#guard_msgs (drop info) in
run_cmd Ixon.Projection.Audit.checkImports #[`Ix.Ixon.BlockOrder] Ixon.BlockOrder.Audit.allowedData

#guard_msgs (drop info) in
run_cmd Ixon.Projection.Audit.checkImports #[`Ix.Ixon.BlockOrder.Theorems] Ixon.BlockOrder.Audit.allowedProof

#guard !Ixon.BlockOrder.Audit.allowedData `Ix.Ixon.BlockOrder.Theorems
#guard !Ixon.BlockOrder.Audit.allowedData `Ix.Tc.CanonicalCheck
#guard !Ixon.BlockOrder.Audit.allowedData `Blake3.Rust
#guard !Ixon.BlockOrder.Audit.allowedData `Blake3.C
#guard !Ixon.BlockOrder.Audit.allowedData `Ix.IxonUniv
#guard !Ixon.Projection.Audit.allowedData `Ix.Ixon.BlockOrder
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Audit.importAllowlist `Ix.Ixon.BlockOrder Ix.Kernel.Audit.importDenylist
#guard !Ix.Kernel.Audit.allowed Ixon.Audit.dataImports `Ix.Ixon.BlockOrder
#guard !Ix.Kernel.Audit.allowed Ix.Kernel.Admission.Audit.dataImports `Ix.Ixon.BlockOrder Ix.Kernel.Audit.importDenylist
#guard !Ixon.BlockOrder.Audit.allowedData `Ix.Ixon.BlockOrder.Audit

/- Measured before freezing: the certified entry adds the order check to the
certified projection entry (`Ixon.Projection.Audit`), with the same ruled
constructs. A block of recursors is checked in motive order (`checkRecord`,
`isRecursor`, `checkMotives`, `recursorMotive`), which reuses the reader's
`stripAll` and `appHead` (`Reader.analyseRecursor`); every other block
is checked in canonical structural order. Its codec is the projection
entry's: Ixon v4's TagN reader and writer (`Ixon.getTagN`, `putTagN`). -/
/-- info: runtime closure of [Ixon.BlockOrder.checkBytes,
 Ixon.BlockOrder.canonicalClasses,
 Ixon.BlockOrder.compareExpr]: 5549 compiled functions; inherited externs 130, implemented_by 0,
unsafe 23, csimp 4; ruled computed_field 18, csimp 21, partial 10 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith Ixon.BlockOrder.Audit.operations #[`Init, `Std] Ix.Kernel.Audit.runtimeRulings

#guard_kernel_axioms Ixon.BlockOrder.Refinement.positive [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.BlockOrder.Refinement.fixedPoint [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.BlockOrder.refine_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.BlockOrder.refine_fixedPoint [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.BlockOrder.refine_mono [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.BlockOrder.canonicalClasses_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.BlockOrder.checkBlock_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.BlockOrder.recursorMotive_of_analyse [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.BlockOrder.motivesFrom_cons [propext, Quot.sound]
#guard_kernel_axioms Ixon.BlockOrder.checkMotives_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.BlockOrder.checkMotiveOrder_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.BlockOrder.checkRecord_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.BlockOrder.checkConstants_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.BlockOrder.checkBytes [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.BlockOrder.checkBytes_ok_iff [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.BlockOrder.checkBytes_reading [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.BlockOrder.checkBytes_has_model [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.BlockOrder.checkBytes_no_proof_of_False [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.BlockOrder.checkBytes_of_ordered [propext, Classical.choice, Quot.sound]

/-- info: Ixon.BlockOrder.refine_ok_iff : ∀ (block : Ixon.BlockOrder.Block) (comparison fuel : Nat)
  (initial result : Ixon.BlockOrder.Classes),
  Ixon.BlockOrder.refine block comparison fuel initial = Except.ok result ↔
    ∃ rounds, rounds ≤ fuel ∧ Ixon.BlockOrder.Refinement block comparison rounds initial result -/
#guard_msgs (whitespace := lax) in
#check @Ixon.BlockOrder.refine_ok_iff

/-- info: @Ixon.BlockOrder.refine_fixedPoint : ∀ {block : Ixon.BlockOrder.Block} {comparison fuel : Nat}
  {initial result : Ixon.BlockOrder.Classes},
  Ixon.BlockOrder.refine block comparison fuel initial = Except.ok result →
    Ixon.BlockOrder.refineStep block comparison result = Except.ok result -/
#guard_msgs (whitespace := lax) in
#check @Ixon.BlockOrder.refine_fixedPoint

/-- info: Ixon.BlockOrder.checkBlock_ok_iff : ∀ (limits : Ixon.BlockOrder.Limits) (owner : Address) (source : Ixon.Constant)
  (blobs : Ix.Kernel.Ingress.Blobs),
  Ixon.BlockOrder.checkBlock limits owner source blobs = Except.ok () ↔
    Ixon.BlockOrder.Canonical limits owner source blobs -/
#guard_msgs (whitespace := lax) in
#check @Ixon.BlockOrder.checkBlock_ok_iff

/- Recursor blocks in motive order. `Ordered`, which every entry theorem
below states, is `OrderedRecord` at each record: a block of recursors must
be `MotiveOrdered` (member `j` eliminates motive `j`, read off its type as
the reader reads it, `recursorMotive_of_analyse`, and declares one motive
per member); every other `muts` block must be `Canonical`. These freeze
what `Ordered` means. -/
/-- info: def Ixon.BlockOrder.OrderedRecord : Ixon.BlockOrder.Limits →
  Ix.Kernel.Ingress.Blobs → Address × Ixon.Constant → Prop :=
fun limits blobs pair =>
  match pair.snd.info with
  | Ixon.ConstantInfo.muts members =>
    if members.all Ixon.BlockOrder.isRecursor = true then Ixon.BlockOrder.MotiveOrdered pair.snd members
    else Ixon.BlockOrder.Canonical limits pair.fst pair.snd blobs
  | x => True -/
#guard_msgs (whitespace := lax) in
#print Ixon.BlockOrder.OrderedRecord

/-- info: def Ixon.BlockOrder.MotivesFrom : Ixon.Constant → Nat → Nat → List Ixon.MutConst → Prop :=
fun source size start members =>
  ∀ (j : Nat) (h : j < members.length),
    ∃ r,
      members[j] = Ixon.MutConst.recr r ∧
        r.motives.toNat = size ∧ Ixon.BlockOrder.recursorMotive source r = some (start + j) -/
#guard_msgs (whitespace := lax) in
#print Ixon.BlockOrder.MotivesFrom

/-- info: Ixon.BlockOrder.checkRecord_ok_iff : ∀ (limits : Ixon.BlockOrder.Limits) (blobs : Ix.Kernel.Ingress.Blobs)
  (owner : Address) (source : Ixon.Constant),
  Ixon.BlockOrder.checkRecord limits blobs owner source = Except.ok () ↔
    Ixon.BlockOrder.OrderedRecord limits blobs (owner, source) -/
#guard_msgs (whitespace := lax) in
#check @Ixon.BlockOrder.checkRecord_ok_iff

/-! ### The certified entry's theorems -/

/-- info: Ixon.BlockOrder.checkBytes_ok_iff : ∀ (maxProjections : Nat) (limits : Ix.Kernel.Admission.Limits)
  (orderLimits : Ixon.BlockOrder.Limits) (records : Ix.Kernel.Admission.Records) (blobs : Ix.Kernel.Ingress.Blobs)
  (hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint) (env : Ix.Kernel.Env),
  Ixon.BlockOrder.checkBytes maxProjections limits orderLimits records blobs hint = Except.ok env ↔
    Ix.Kernel.Admission.WithinBatch limits records blobs ∧
      Ix.Kernel.Admission.UniqueKeys records blobs ∧
        ∃ input output,
          Ix.Kernel.Admission.RecordsRead limits records input ∧
            Ixon.Projection.Expanded maxProjections input output ∧
              Ixon.BlockOrder.Ordered orderLimits blobs input ∧
                Ix.Kernel.Admission.checkConstants output blobs hint = Except.ok env -/
#guard_msgs (whitespace := lax) in
#check @Ixon.BlockOrder.checkBytes_ok_iff

/-- info: @Ixon.BlockOrder.checkBytes_reading : ∀ {maxProjections : Nat} {limits : Ix.Kernel.Admission.Limits}
  {orderLimits : Ixon.BlockOrder.Limits} {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env},
  Ixon.BlockOrder.checkBytes maxProjections limits orderLimits records blobs hint = Except.ok env →
    Ix.Kernel.Admission.UniqueKeys records blobs ∧
      ∃ input output,
        Ix.Kernel.Admission.RecordsRead limits records input ∧
          Ixon.Projection.Expanded maxProjections input output ∧
            Ixon.BlockOrder.Ordered orderLimits blobs input ∧
              ∃ pins pre natPins,
                Ix.Kernel.Reader.defaultPins = Except.ok pins ∧
                  Ix.Kernel.Reader.builtinPrelude = Except.ok pre ∧
                    Ix.Kernel.Reader.builtinNatOpPins = Except.ok natPins ∧
                      Ix.Kernel.Admission.Installed pins pre natPins output blobs hint env -/
#guard_msgs (whitespace := lax) in
#check @Ixon.BlockOrder.checkBytes_reading

/-- info: Ixon.BlockOrder.checkBytes_has_model : ∀ (V : Type u_1) [inst : Ix.Kernel.SetTheory V] {maxProjections : Nat}
  {limits : Ix.Kernel.Admission.Limits} {orderLimits : Ixon.BlockOrder.Limits} {records : Ix.Kernel.Admission.Records}
  {blobs : Ix.Kernel.Ingress.Blobs} {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint}
  {env : Ix.Kernel.Env},
  Ixon.BlockOrder.checkBytes maxProjections limits orderLimits records blobs hint = Except.ok env →
    Nonempty (Ix.Kernel.Model V env) -/
#guard_msgs (whitespace := lax) in
#check @Ixon.BlockOrder.checkBytes_has_model

/-- info: Ixon.BlockOrder.checkBytes_no_proof_of_False : ∀ (V : Type u_1) [Ix.Kernel.SetTheory V] {maxProjections : Nat}
  {limits : Ix.Kernel.Admission.Limits} {orderLimits : Ixon.BlockOrder.Limits} {records : Ix.Kernel.Admission.Records}
  {blobs : Ix.Kernel.Ingress.Blobs} {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint}
  {env : Ix.Kernel.Env},
  Ixon.BlockOrder.checkBytes maxProjections limits orderLimits records blobs hint = Except.ok env →
    ∀ (ci : Ix.Kernel.ConstantInfo),
      ci ∈ env.consts → ci.toConstantVal.type = Ix.Kernel.Expr.const Ix.Kernel.falseName [] → False -/
#guard_msgs (whitespace := lax) in
#check @Ixon.BlockOrder.checkBytes_no_proof_of_False

/-- info: @Ixon.BlockOrder.checkBytes_of_ordered : ∀ {maxProjections : Nat} {limits : Ix.Kernel.Admission.Limits}
  {orderLimits : Ixon.BlockOrder.Limits} {records : Ix.Kernel.Admission.Records}
  {input output : Ix.Kernel.Ingress.Constants} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint},
  Ix.Kernel.Admission.WithinBatch limits records blobs →
    Ix.Kernel.Admission.UniqueKeys records blobs →
      Ix.Kernel.Admission.RecordsRead limits records input →
        Ixon.Projection.Expanded maxProjections input output →
          Ixon.BlockOrder.Ordered orderLimits blobs input →
            Ixon.BlockOrder.checkBytes maxProjections limits orderLimits records blobs hint =
              Except.mapError Ixon.BlockOrder.CheckError.checker
                (Ix.Kernel.Admission.checkConstants output blobs hint) -/
#guard_msgs (whitespace := lax) in
#check @Ixon.BlockOrder.checkBytes_of_ordered

/- The certified entry's order check reaches no extern or unsafe primitive
beyond the certified projection entry's (the fold's closure already uses
`String.compare`, the `UInt64` operations and `Array.uget`). -/
/-- info: Additional certified block-order externs: []
---
info: Additional certified block-order unsafe: [] -/
#guard_msgs (whitespace := lax) in
run_cmd do
  let env ← Lean.getEnv
  let before := Ix.Kernel.Audit.runtimeClosure env Ixon.Projection.Audit.operations
  let after := Ix.Kernel.Audit.runtimeClosure env Ixon.BlockOrder.Audit.operations
  Lean.logInfo m!"Additional certified block-order externs: {after.externs.filter (!before.externs.contains ·)}"
  Lean.logInfo m!"Additional certified block-order unsafe: {after.unsafes.filter (!before.unsafes.contains ·)}"
