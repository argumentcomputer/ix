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
entry's: Ixon v4's TagN reader and writer (`Ixon.getTagN`, `putTagN`). Step 5a
(typed keys) moved the count from 5820 by the entry's change
(`IxC/Kernel/Audit/Roots.lean`); step 5b's `LetMeta` from 5611, by the let
contract's equality, hash and `Repr`; step 5b's walk change from 5638, by the
sources of the arity-reduced `f._redArg` the walk reaches (no extern, `unsafe`,
`csimp` or `partial` constant among them); step 5b's mode index from 5733, by
the entry's change; its address keys from 5745 and 112 inherited
externs, by the entry's change; the IxC performance series (PERF P16, P14,
P3, P2) from 5708 and 114 inherited externs, by the entry's change
(`IxC/Kernel/Audit/Roots.lean`); step 6's structured errors from 5726 and
116 inherited externs, by the entry's change; the validation of the four
install anchors from 5944, by the entry's change; step 6b's display annotations from
5955, by the entry's change (8 more, one more ruled csimp), and its failure display
from 5963 (30 more, one more ruled csimp); the reader's conversion to Lean `module`s from
5993, by the entry's change (28) and one specialisation more: the entry and
the block-order code shared one specialisation of `Ingress.natural`'s fold,
which the block-order code still reaches, beside the one the module now
compiles for the entry (29 more); a `let`'s nondependency bit became a key
(`compareExpr_letE`) from 6022: the closures differ only in `compareExpr`'s
own compiler-generated lambdas (the new `thenM` continuation after the body and
the renumbering of the existing ones); `Bool.toNat` was already in the closure
(`compareMember`); no extern, unsafe or ruled construct moved; CQX.8's field test
in the in-model generator from 6024, by the entry's change (4 of `genNested`'s
specialisations gone, `IxC/Kernel/Audit/Roots.lean`); (A) (`ALPHA-COLLAPSE.md`
§8.2) from 6020, by the entry's change (122 out: the compiler-trust roles and
their checks, `IxC/Kernel/Audit/Roots.lean`); the `.indDecl` shape guard from 5898, by the
entry's change (44 in: the guard, its memoized walk and their specialisations; one more csimp, ruled, `IxC/Kernel/Audit/Roots.lean`); the mutual modeller's reading of Lean's
recursive fields from 5942, by the entry's change (9 more); the rest-only hoist and the
decided units check (S1) from 5951, by the entry's change (117 in,
`IxC/Kernel/Audit/Roots.lean`); the prelude's shape check (S1, fact
(ii)) from 6068, by the entry's change (12 in); the hoist guard (S1) from 6080, by
the entry's change (4 in); the in-model generator's totality (S1) from
6084, by the entry's change (15 more; its nine ruled `partial` definitions are total,
and the ruling is gone). -/
/-- info: runtime closure of [Ixon.BlockOrder.checkBytes,
 Ixon.BlockOrder.canonicalClasses,
 Ixon.BlockOrder.compareExpr]: 6099 compiled functions; inherited externs 114, implemented_by 0, unsafe 26, csimp 7; ruled computed_field 21, csimp 26 -/
#guard_msgs (whitespace := lax) in
run_cmd Ix.Kernel.Audit.checkRuntimeWith Ixon.BlockOrder.Audit.operations #[`Init, `Std] Ix.Kernel.Audit.runtimeRulings

#guard_kernel_axioms Ixon.BlockOrder.compareExpr_letE [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.BlockOrder.compareExpr_letE_nonDep [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.BlockOrder.compareExpr_letE_sameBit [propext, Classical.choice, Quot.sound]
#guard_kernel_axioms Ixon.BlockOrder.bind_thenM_eq []
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
#guard_kernel_axioms Ixon.BlockOrder.checkBytes_authentic [propext, Classical.choice, Quot.sound]
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

/-- info: Ixon.BlockOrder.checkBlock_ok_iff : ∀ (hash : ByteArray → Address) (limits : Ixon.BlockOrder.Limits) (owner : Address)
  (source : Ixon.Constant) (blobs : Ix.Kernel.Ingress.Blobs),
  Ixon.BlockOrder.checkBlock hash limits owner source blobs = Except.ok () ↔
    Ixon.BlockOrder.Canonical hash limits owner source blobs -/
#guard_msgs (whitespace := lax) in
#check @Ixon.BlockOrder.checkBlock_ok_iff

/- The comparison's `let` arm, frozen: the type, the value, the body, then
the nondependency bit; two `let`s that differ only in the bit are never
equal, and with equal bits the arm is the one before the bit was a key. -/
/-- info: Ixon.BlockOrder.compareExpr_letE : ∀ (block : Ixon.BlockOrder.Block) (ctx : Ixon.BlockOrder.LocalContext)
  (fuel leftLimit rightLimit : Nat) (xc yc : Ixon.LetContract) (xt xv xb yt yv yb : Ixon.Expr),
  Ixon.BlockOrder.compareExpr block ctx (fuel + 1) leftLimit (Ixon.Expr.letE xc xt xv xb) rightLimit
      (Ixon.Expr.letE yc yt yv yb) =
    do
    let __do_lift ← Ixon.BlockOrder.compareExpr block ctx fuel leftLimit xt rightLimit yt
    Ixon.BlockOrder.thenM __do_lift fun x => do
        let __do_lift ← Ixon.BlockOrder.compareExpr block ctx fuel leftLimit xv rightLimit yv
        Ixon.BlockOrder.thenM __do_lift fun x => do
            let __do_lift ← Ixon.BlockOrder.compareExpr block ctx fuel leftLimit xb rightLimit yb
            Ixon.BlockOrder.thenM __do_lift fun x => Except.ok (compare xc.nonDep.toNat yc.nonDep.toNat) -/
#guard_msgs (whitespace := lax) in
#check @Ixon.BlockOrder.compareExpr_letE

/-- info: @Ixon.BlockOrder.compareExpr_letE_nonDep : ∀ {block : Ixon.BlockOrder.Block} {ctx : Ixon.BlockOrder.LocalContext}
  {fuel leftLimit rightLimit : Nat} {xc yc : Ixon.LetContract} {xt xv xb yt yv yb : Ixon.Expr},
  Ixon.BlockOrder.compareExpr block ctx fuel leftLimit xt rightLimit yt = Except.ok Ordering.eq →
    Ixon.BlockOrder.compareExpr block ctx fuel leftLimit xv rightLimit yv = Except.ok Ordering.eq →
      Ixon.BlockOrder.compareExpr block ctx fuel leftLimit xb rightLimit yb = Except.ok Ordering.eq →
        xc.nonDep ≠ yc.nonDep →
          Ixon.BlockOrder.compareExpr block ctx (fuel + 1) leftLimit (Ixon.Expr.letE xc xt xv xb) rightLimit
              (Ixon.Expr.letE yc yt yv yb) =
            Except.ok (if xc.nonDep = true then Ordering.gt else Ordering.lt) -/
#guard_msgs (whitespace := lax) in
#check @Ixon.BlockOrder.compareExpr_letE_nonDep

/-- info: @Ixon.BlockOrder.compareExpr_letE_sameBit : ∀ {block : Ixon.BlockOrder.Block} {ctx : Ixon.BlockOrder.LocalContext}
  {fuel leftLimit rightLimit : Nat} {xc yc : Ixon.LetContract} {xt xv xb yt yv yb : Ixon.Expr},
  xc.nonDep = yc.nonDep →
    Ixon.BlockOrder.compareExpr block ctx (fuel + 1) leftLimit (Ixon.Expr.letE xc xt xv xb) rightLimit
        (Ixon.Expr.letE yc yt yv yb) =
      do
      let __do_lift ← Ixon.BlockOrder.compareExpr block ctx fuel leftLimit xt rightLimit yt
      Ixon.BlockOrder.thenM __do_lift fun x => do
          let __do_lift ← Ixon.BlockOrder.compareExpr block ctx fuel leftLimit xv rightLimit yv
          Ixon.BlockOrder.thenM __do_lift fun x => Ixon.BlockOrder.compareExpr block ctx fuel leftLimit xb rightLimit yb -/
#guard_msgs (whitespace := lax) in
#check @Ixon.BlockOrder.compareExpr_letE_sameBit

/- Recursor blocks in motive order. `Ordered`, which every entry theorem
below states, is `OrderedRecord` at each record: a block of recursors must
be `MotiveOrdered` (member `j` eliminates motive `j`, read off its type as
the reader reads it, `recursorMotive_of_analyse`, and declares one motive
per member); every other `muts` block must be `Canonical`. These freeze
what `Ordered` means. -/
/-- info: def Ixon.BlockOrder.OrderedRecord : (ByteArray → Address) →
  Ixon.BlockOrder.Limits → Ix.Kernel.Ingress.Blobs → Address × Ixon.Constant → Prop :=
fun hash limits blobs pair =>
  match pair.snd.info with
  | Ixon.ConstantInfo.muts members =>
    if members.all Ixon.BlockOrder.isRecursor = true then Ixon.BlockOrder.MotiveOrdered pair.snd members
    else Ixon.BlockOrder.Canonical hash limits pair.fst pair.snd blobs
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

/-- info: Ixon.BlockOrder.checkRecord_ok_iff : ∀ (hash : ByteArray → Address) (limits : Ixon.BlockOrder.Limits)
  (blobs : Ix.Kernel.Ingress.Blobs) (owner : Address) (source : Ixon.Constant),
  Ixon.BlockOrder.checkRecord hash limits blobs owner source = Except.ok () ↔
    Ixon.BlockOrder.OrderedRecord hash limits blobs (owner, source) -/
#guard_msgs (whitespace := lax) in
#check @Ixon.BlockOrder.checkRecord_ok_iff

/-! ### The certified entry's theorems -/

/-- info: Ixon.BlockOrder.checkBytes_ok_iff : ∀ (hash : ByteArray → Address) (binding : Ix.Kernel.Admission.Binding)
  (maxProjections : Nat) (limits : Ix.Kernel.Admission.Limits) (orderLimits : Ixon.BlockOrder.Limits)
  (records : Ix.Kernel.Admission.Records) (blobs : Ix.Kernel.Ingress.Blobs)
  (hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint) (env : Ix.Kernel.Env Ix.Kernel.Mode.anon),
  Ixon.BlockOrder.checkBytes hash binding maxProjections limits orderLimits records blobs hint = Except.ok env ↔
    Ix.Kernel.Admission.WithinBatch limits records blobs ∧
      Ix.Kernel.Admission.UniqueKeys records blobs ∧
        Ix.Kernel.Admission.Authentic hash records blobs ∧
          ∃ input output,
            Ix.Kernel.Admission.RecordsRead limits records input ∧
              Ixon.Projection.Expanded hash maxProjections input output ∧
                Ixon.BlockOrder.Ordered hash orderLimits blobs input ∧
                  Ix.Kernel.Admission.checkConstantsAt hash binding output blobs hint = Except.ok env -/
#guard_msgs (whitespace := lax) in
#check @Ixon.BlockOrder.checkBytes_ok_iff

/-- info: @Ixon.BlockOrder.checkBytes_reading : ∀ {hash : ByteArray → Address} {binding : Ix.Kernel.Admission.Binding}
  {maxProjections : Nat} {limits : Ix.Kernel.Admission.Limits} {orderLimits : Ixon.BlockOrder.Limits}
  {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env Ix.Kernel.Mode.anon},
  Ixon.BlockOrder.checkBytes hash binding maxProjections limits orderLimits records blobs hint = Except.ok env →
    Ix.Kernel.Admission.UniqueKeys records blobs ∧
      Ix.Kernel.Admission.Authentic hash records blobs ∧
        ∃ input output,
          Ix.Kernel.Admission.RecordsRead limits records input ∧
            Ixon.Projection.Expanded hash maxProjections input output ∧
              Ixon.BlockOrder.Ordered hash orderLimits blobs input ∧
                Ix.Kernel.Admission.Hashed hash output ∧
                  ∃ t pre,
                    Ix.Kernel.Admission.BindingAdmitted hash binding t ∧
                      Ix.Kernel.Reader.preludeFor t = Except.ok pre ∧
                        Ix.Kernel.Admission.Installed hash t pre output blobs hint env -/
#guard_msgs (whitespace := lax) in
#check @Ixon.BlockOrder.checkBytes_reading

/-- info: @Ixon.BlockOrder.checkBytes_authentic : ∀ {hash : ByteArray → Address} {binding : Ix.Kernel.Admission.Binding}
  {maxProjections : Nat} {limits : Ix.Kernel.Admission.Limits} {orderLimits : Ixon.BlockOrder.Limits}
  {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env Ix.Kernel.Mode.anon},
  Ixon.BlockOrder.checkBytes hash binding maxProjections limits orderLimits records blobs hint = Except.ok env →
    Ix.Kernel.Admission.Authentic hash records blobs ∧
      ∃ output,
        Ix.Kernel.Admission.Hashed hash output ∧
          Ix.Kernel.Admission.checkConstantsAt hash binding output blobs hint = Except.ok env -/
#guard_msgs (whitespace := lax) in
#check @Ixon.BlockOrder.checkBytes_authentic

/-- info: Ixon.BlockOrder.checkBytes_has_model : ∀ (V : Type u_1) [inst : Ix.Kernel.SetTheory V] {hash : ByteArray → Address}
  {binding : Ix.Kernel.Admission.Binding} {maxProjections : Nat} {limits : Ix.Kernel.Admission.Limits}
  {orderLimits : Ixon.BlockOrder.Limits} {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env Ix.Kernel.Mode.anon},
  Ixon.BlockOrder.checkBytes hash binding maxProjections limits orderLimits records blobs hint = Except.ok env →
    Nonempty (Ix.Kernel.Model V env) -/
#guard_msgs (whitespace := lax) in
#check @Ixon.BlockOrder.checkBytes_has_model

/-- info: Ixon.BlockOrder.checkBytes_no_proof_of_False : ∀ (V : Type u_1) [Ix.Kernel.SetTheory V] {hash : ByteArray → Address}
  {binding : Ix.Kernel.Admission.Binding} {maxProjections : Nat} {limits : Ix.Kernel.Admission.Limits}
  {orderLimits : Ixon.BlockOrder.Limits} {records : Ix.Kernel.Admission.Records} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint} {env : Ix.Kernel.Env Ix.Kernel.Mode.anon},
  Ixon.BlockOrder.checkBytes hash binding maxProjections limits orderLimits records blobs hint = Except.ok env →
    ∀ (ci : Ix.Kernel.ConstantInfo Ix.Kernel.Mode.anon),
      ci ∈ env.consts → ci.toConstantVal.type = Ix.Kernel.Expr.const (Ix.Kernel.roleKey Ix.Kernel.Role.false) [] → False -/
#guard_msgs (whitespace := lax) in
#check @Ixon.BlockOrder.checkBytes_no_proof_of_False

/-- info: @Ixon.BlockOrder.checkBytes_of_ordered : ∀ {hash : ByteArray → Address} {binding : Ix.Kernel.Admission.Binding}
  {maxProjections : Nat} {limits : Ix.Kernel.Admission.Limits} {orderLimits : Ixon.BlockOrder.Limits}
  {records : Ix.Kernel.Admission.Records} {input output : Ix.Kernel.Ingress.Constants} {blobs : Ix.Kernel.Ingress.Blobs}
  {hint : Ix.Kernel.ConstRef Address → Option Ix.Kernel.ReducibilityHint},
  Ix.Kernel.Admission.WithinBatch limits records blobs →
    Ix.Kernel.Admission.UniqueKeys records blobs →
      Ix.Kernel.Admission.Authentic hash records blobs →
        Ix.Kernel.Admission.RecordsRead limits records input →
          Ixon.Projection.Expanded hash maxProjections input output →
            Ixon.BlockOrder.Ordered hash orderLimits blobs input →
              Ixon.BlockOrder.checkBytes hash binding maxProjections limits orderLimits records blobs hint =
                Except.mapError Ixon.BlockOrder.CheckError.checker
                  (Ix.Kernel.Admission.checkConstantsAt hash binding output blobs hint) -/
#guard_msgs (whitespace := lax) in
#check @Ixon.BlockOrder.checkBytes_of_ordered

/- The certified entry's order check reaches one extern beyond the certified
projection entry's, `String.compare`, by which it orders string literals,
and no unsafe primitive (the fold's closure already uses the `UInt64`
operations and `Array.uget`). -/
/-- info: Additional certified block-order externs: [String.compare]
---
info: Additional certified block-order unsafe: [] -/
#guard_msgs (whitespace := lax) in
run_cmd do
  let env ← Lean.getEnv
  let before := Ix.Kernel.Audit.runtimeClosure env Ixon.Projection.Audit.operations
  let after := Ix.Kernel.Audit.runtimeClosure env Ixon.BlockOrder.Audit.operations
  Lean.logInfo m!"Additional certified block-order externs: {after.externs.filter (!before.externs.contains ·)}"
  Lean.logInfo m!"Additional certified block-order unsafe: {after.unsafes.filter (!before.unsafes.contains ·)}"
