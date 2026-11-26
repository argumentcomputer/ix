import IxCCAiur.TypedBackward
import IxCCAiur.Compose
import IxCCAiur.Claim
import IxCCAiur.Progress

/-! # Certified End-to-End Claims for Typed / Unboxed `Fir → Formal Aiur` (`IxCCAiur.TypedClaim`)

Composes `TypedBackward.typed_entry_backward_sound` and
`TypedBackward.typed_circuit_sound_goldilocks` with:
* `Recheck.front_fir` (`IxCCAiur.Compose`) to reach the source evaluator `SrcEval`;
* `TypedWorld.checkTypedWorld` (`TypedBackward.typedLoweredWorld_of_natCore`) to discharge
  `TypedLoweredWorld` purely from executable world checking;
* `TypedRep.inferCheckedShapes` / `Fir.Shape.check` / `Fir.Proof.Shape.checkSound` to connect
  inferred shape certificates to certified soundness;
* `Progress.checkShape` (`SrcShape.neverStuck_checked`) to remove the stuck-source disjunct.

Supports all three public result shapes produced by `TypedLower.lowerProgram`:
1. **Unboxed `Nat` (`.field y`)**: when `lp.exportReps[i]? = some retR` with `retR.isFieldNat = true`
   (`result_fieldNat`, `typed_accepted_nat_backward`, `typed_accepted_nat_sound`, `typed_accepted_nat`);
2. **Dedicated enumeration (`Prog::E<ind>::<ctor>`)**: when `lp.exportReps[i]? = some (.enum ind)`
   (`result_typed_enum`, `typed_accepted_enum_backward`, `typed_accepted_enum_sound`,
   `typed_accepted_enum`);
3. **Fallback boxed `Obj` (`Prog::Obj::N(y)` and `Prog::Obj::<ctor>`)**: when
   `lp.exportReps[i]? = some .obj` (`result_typed_obj_nat`, `result_typed_obj_enum`,
   `typed_accepted_obj_nat`, `typed_accepted_obj_enum`).

Zero `sorry`, zero `admit`, zero `axiom`, zero `native_decide`, zero `bv_decide`. -/

set_option autoImplicit false

namespace IxCC.AiurBackend.TypedClaim

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Library
open IxCC.Lam.Erase.Proof (CheckedProgram)
open IxCC.AiurBackend.Lower
open IxCC.AiurBackend.Schedule (CircuitSchedule)
open IxCC.AiurBackend.TypedRep
open IxCC.AiurBackend.TypedLower
open IxCC.AiurBackend.TypedWorld
open IxCC.AiurBackend.TypedGadgets
open IxCC.AiurBackend.TypedBackward
open IxCC.AiurBackend.Compose
open IxCC.AiurBackend.Claim
open IxCC.AiurBackend.Progress

/-! ## 1. Soundness of `TypedRep.inferCheckedShapes` -/

/-- Whenever `TypedRep.inferCheckedShapes src P` accepts a certificate `(cert, true)`,
the Boolean shape checker `Fir.Shape.check P cert` succeeded. -/
theorem check_of_inferCheckedShapes {src : Src.Program} {P : Fir.Program}
    {cert : Fir.Shape.ShapeCert}
    (h : TypedRep.inferCheckedShapes src P = (cert, true)) :
    Fir.Shape.check P cert = true := by
  unfold TypedRep.inferCheckedShapes Fir.ShapeInfer.run at h
  dsimp only at h
  split at h
  · rename_i hchk
    cases h
    exact hchk
  · cases h

/-- Whenever `TypedRep.inferCheckedShapes src P = (cert, true)`, `cert` satisfies the
semantic `Fir.Shape.Checked P cert` judgment. -/
theorem checked_of_inferCheckedShapes {src : Src.Program} {P : Fir.Program}
    {cert : Fir.Shape.ShapeCert}
    (h : TypedRep.inferCheckedShapes src P = (cert, true)) :
    Fir.Shape.Checked P cert :=
  Fir.Proof.Shape.check_checked (check_of_inferCheckedShapes h)

/-- Whenever `TypedRep.inferCheckedShapes src P = (cert, true)`, every run of `P`
respects `cert` (`Fir.Shape.ShapeSound P cert enc`). -/
theorem shapeSound_of_inferCheckedShapes {enc : Fir.Shape.ArrEnc}
    {src : Src.Program} {P : Fir.Program} {cert : Fir.Shape.ShapeCert}
    (h : TypedRep.inferCheckedShapes src P = (cert, true)) :
    Fir.Shape.ShapeSound P cert enc :=
  Fir.Proof.Shape.checkSound enc P cert (checked_of_inferCheckedShapes h)

/-! ## 2. Reading Typed Public Results -/

section PublicResults

variable {F : Type} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- **An unboxed `Nat` result (`.field y`).** If the export return representation is a
single-field `Nat` (`retR.isFieldNat = true`, i.e., `.nat _`, `.w8`, or `.w16`) and the
public circuit result is `.field y`, then the Fir value is `.lit (.nat n)` with `n < 2^56`
and `(n : F) = y`. -/
theorem result_fieldNat {P : Fir.Program} {cert : Fir.Shape.ShapeCert} {feat : Features}
    {heap : Heap F} {retR : Rep} {w : Fir.Val} {value : SourceValue F}
    {rom : Aiur.ROM F} {y : F}
    (hfn : retR.isFieldNat = true)
    (htvr : TVR P cert feat heap retR w value)
    (hrep : Aiur.Represents rom heap value (.field y)) :
    ∃ n : Nat, n < natLimit ∧ w = .lit (.nat n) ∧ (n : F) = y := by
  obtain ⟨n, _, hn, rfl, rfl⟩ := htvr.fieldNat_inv hfn
  cases hrep
  exact ⟨n, hn, rfl, rfl⟩

omit [DecidableEq F] in
/-- **A dedicated `E<ind>` enumeration result.** If the export return representation is
`.enum ind` and the public circuit result is `Prog::E<ind>::<ctor of row idx>`, then the
Fir value is that nullary constructor. -/
theorem result_typed_enum {P : Fir.Program} {cert : Fir.Shape.ShapeCert} {feat : Features}
    (hnd : (objCtorNames P).Nodup)
    {idx : Nat} {entry : Lam.CtorInfo} (hget : P.ctors[idx]? = some entry)
    {ind : Src.CId} {heap : Heap F} {w : Fir.Val} {value : SourceValue F} {rom : Aiur.ROM F}
    (htvr : TVR P cert feat heap (.enum ind) w value)
    (hrep : Aiur.Represents rom heap value
      (.construct (enumQName ind) (ctorNameOf idx entry.key) [])) :
    ∃ c, w = Fir.Val.ctor c [] ∧ c.key = entry.key := by
  cases hrep with
  | construct items =>
    cases items
    obtain ⟨_, c, idx', entry', _, _, hget', hkey', _, rfl, heq⟩ := TVR_enum_inv htvr
    have hname : ctorNameOf idx' entry'.key = ctorNameOf idx entry.key := by
      rw [hkey']
      exact (Value.construct.inj heq).2.1.symm
    obtain ⟨_, hEntryEq⟩ := ctorNameOf_inj_of_nodup hnd hget' hget hname
    exact ⟨c, rfl, hkey'.symm.trans (congrArg Lam.CtorInfo.key hEntryEq)⟩

omit [DecidableEq F] in
/-- **A fallback boxed `Obj::N(y)` result** under typed lowering when `retR = .obj`. -/
theorem result_typed_obj_nat {P : Fir.Program} {cert : Fir.Shape.ShapeCert} {feat : Features}
    {heap : Heap F} {w : Fir.Val} {value : SourceValue F} {rom : Aiur.ROM F} {y : F}
    (htvr : TVR P cert feat heap .obj w value)
    (hrep : Aiur.Represents rom heap value (.construct objQName "N" [.field y])) :
    ∃ n : Nat, n < natLimit ∧ w = .lit (.nat n) ∧ (n : F) = y :=
  Claim.result_nat (TVR_obj_inv htvr) hrep

omit [DecidableEq F] in
/-- **A fallback boxed `Obj::<ctor>` enumeration result** under typed lowering when `retR = .obj`. -/
theorem result_typed_obj_enum {P : Fir.Program} {cert : Fir.Shape.ShapeCert} {feat : Features}
    (hnd : (objCtorNames P).Nodup)
    {idx : Nat} {entry : Lam.CtorInfo} (hget : P.ctors[idx]? = some entry)
    {heap : Heap F} {w : Fir.Val} {value : SourceValue F} {rom : Aiur.ROM F}
    (htvr : TVR P cert feat heap .obj w value)
    (hrep : Aiur.Represents rom heap value
      (.construct objQName (ctorNameOf idx entry.key) [])) :
    ∃ c, w = Fir.Val.ctor c [] ∧ c.key = entry.key :=
  Claim.result_enum hnd hget (TVR_obj_inv htvr) hrep

end PublicResults

/-! ## 3. Entry-Level Source Soundness (`TypedLower` + `Recheck.runFir`) -/

section TypedEntry

variable {F : Type} [Field F] [DecidableEq F]

/-- **An accepted run of a typed lowered entry, read at the source (with stuck-source disjunct).** -/
theorem typed_entry_source_backward {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {cert : Fir.Shape.ShapeCert} {sched : CircuitSchedule} {lp : LoweredProgram}
    {world : World F}
    (fc : FieldCompatible64 F) (lw : TypedLoweredWorld f.fir cert sched lp world)
    (hnc : natCoreProgram f.fir cert = true)
    {i : Nat} {g : Fir.FunId} (hexp : f.fir.exports[i]? = some g)
    {args : List (SourceValue F)} {h' : Heap F} {r : SourceValue F}
    (ev : EvalFn world (qualified (entryName i)) args [] r h') :
    ∃ (ns : List Nat) (w : Fir.Val),
      (∀ n ∈ ns, n < natLimit) ∧
      args = ns.map (fun n => .field (n : F)) ∧
      lp.exportReps[i]? = some (repOf f.fir cert (scanFeatures f.fir) (cert.fn g).ret) ∧
      TVR f.fir cert (scanFeatures f.fir) h'
        (repOf f.fir cert (scanFeatures f.fir) (cert.fn g).ret) w r ∧
      (f.Covered c (i, ns) →
        (∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, ns) k = .ok v ∧
            Sem.Lang.ObsEq (S := CheckedProgram) (T := Fir.Program) v w) ∨
          ∃ k, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, ns) k = .stuck) := by
  obtain ⟨ns, k, w, hns, hargs, hrun, hrepGet, htvr⟩ :=
    typed_entry_backward_sound fc lw hnc hexp ev
  exact ⟨ns, w, hns, hargs, hrepGet, htvr, fun hcov => source_of_fir_run hf hexp hrun hcov⟩

/-- **An accepted run of a typed lowered entry, read at the source, under `NeverStuck`.** -/
theorem typed_entry_source_sound {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {cert : Fir.Shape.ShapeCert} {sched : CircuitSchedule} {lp : LoweredProgram}
    {world : World F}
    (fc : FieldCompatible64 F) (lw : TypedLoweredWorld f.fir cert sched lp world)
    (hnc : natCoreProgram f.fir cert = true)
    {i : Nat} {g : Fir.FunId} (hexp : f.fir.exports[i]? = some g)
    {args : List (SourceValue F)} {h' : Heap F} {r : SourceValue F}
    (ev : EvalFn world (qualified (entryName i)) args [] r h')
    (hp : ∀ ns : List Nat, args = ns.map (fun n => .field (n : F)) →
      NeverStuck ⟨f.src, f.checked⟩ (i, ns)) :
    ∃ (ns : List Nat) (w : Fir.Val),
      (∀ n ∈ ns, n < natLimit) ∧
      args = ns.map (fun n => .field (n : F)) ∧
      lp.exportReps[i]? = some (repOf f.fir cert (scanFeatures f.fir) (cert.fn g).ret) ∧
      TVR f.fir cert (scanFeatures f.fir) h'
        (repOf f.fir cert (scanFeatures f.fir) (cert.fn g).ret) w r ∧
      (f.Covered c (i, ns) →
        ∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, ns) k = .ok v ∧
          Sem.Lang.ObsEq (S := CheckedProgram) (T := Fir.Program) v w) := by
  obtain ⟨ns, k, w, hns, hargs, hrun, hrepGet, htvr⟩ :=
    typed_entry_backward_sound fc lw hnc hexp ev
  exact ⟨ns, w, hns, hargs, hrepGet, htvr, fun hcov =>
    source_of_fir_run_of_neverStuck hf hexp hrun hcov (hp ns hargs)⟩

/-- `typed_entry_source_backward` with `TypedLoweredWorld` discharged by
`TypedWorld.checkTypedWorld`. -/
theorem typed_entry_source_backward_checked {cfg : Recheck.Config} {P : Src.Program}
    {c : Recheck.Cert} {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {cert : Fir.Shape.ShapeCert} {sched : CircuitSchedule} {lp : LoweredProgram}
    (hnc : natCoreProgram f.fir cert = true)
    (hlow : TypedLower.lowerProgram f.fir cert sched = .ok lp)
    (fc : FieldCompatible64 F) {s : Generic.Source F} (hw : checkTypedWorld s lp = true)
    {i : Nat} {g : Fir.FunId} (hexp : f.fir.exports[i]? = some g)
    {args : List (SourceValue F)} {h' : Heap F} {r : SourceValue F}
    (ev : EvalFn s.world (qualified (entryName i)) args [] r h') :
    ∃ (ns : List Nat) (w : Fir.Val),
      (∀ n ∈ ns, n < natLimit) ∧
      args = ns.map (fun n => .field (n : F)) ∧
      lp.exportReps[i]? = some (repOf f.fir cert (scanFeatures f.fir) (cert.fn g).ret) ∧
      TVR f.fir cert (scanFeatures f.fir) h'
        (repOf f.fir cert (scanFeatures f.fir) (cert.fn g).ret) w r ∧
      (f.Covered c (i, ns) →
        (∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, ns) k = .ok v ∧
            Sem.Lang.ObsEq (S := CheckedProgram) (T := Fir.Program) v w) ∨
          ∃ k, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, ns) k = .stuck) :=
  typed_entry_source_backward hf fc (typedLoweredWorld_of_natCore fc hnc hlow s hw) hnc hexp ev

/-- `typed_entry_source_sound` with `TypedLoweredWorld` discharged by
`TypedWorld.checkTypedWorld`. -/
theorem typed_entry_source_sound_checked {cfg : Recheck.Config} {P : Src.Program}
    {c : Recheck.Cert} {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {cert : Fir.Shape.ShapeCert} {sched : CircuitSchedule} {lp : LoweredProgram}
    (hnc : natCoreProgram f.fir cert = true)
    (hlow : TypedLower.lowerProgram f.fir cert sched = .ok lp)
    (fc : FieldCompatible64 F) {s : Generic.Source F} (hw : checkTypedWorld s lp = true)
    {i : Nat} {g : Fir.FunId} (hexp : f.fir.exports[i]? = some g)
    {args : List (SourceValue F)} {h' : Heap F} {r : SourceValue F}
    (ev : EvalFn s.world (qualified (entryName i)) args [] r h')
    (hp : ∀ ns : List Nat, args = ns.map (fun n => .field (n : F)) →
      NeverStuck ⟨f.src, f.checked⟩ (i, ns)) :
    ∃ (ns : List Nat) (w : Fir.Val),
      (∀ n ∈ ns, n < natLimit) ∧
      args = ns.map (fun n => .field (n : F)) ∧
      lp.exportReps[i]? = some (repOf f.fir cert (scanFeatures f.fir) (cert.fn g).ret) ∧
      TVR f.fir cert (scanFeatures f.fir) h'
        (repOf f.fir cert (scanFeatures f.fir) (cert.fn g).ret) w r ∧
      (f.Covered c (i, ns) →
        ∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, ns) k = .ok v ∧
          Sem.Lang.ObsEq (S := CheckedProgram) (T := Fir.Program) v w) :=
  typed_entry_source_sound hf fc (typedLoweredWorld_of_natCore fc hnc hlow s hw) hnc hexp ev hp

end TypedEntry

/-! ## 4. Accepted Goldilocks Circuit Claims (`TypedLower` + `Recheck.runFir` + `Progress`) -/

/-- **Accepted Goldilocks circuit rows for a typed lowered program, read at the source
(with stuck-source disjunct).** -/
theorem typed_circuit_source_backward_goldilocks {cfg : Recheck.Config} {P : Src.Program}
    {c : Recheck.Cert} {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {cert : Fir.Shape.ShapeCert} {sched : CircuitSchedule} {lp : LoweredProgram}
    {moduleProg : Aiur.Modules.Program G}
    {id : String → Except String Nat}
    (prepared : Aiur.Modules.Prepared moduleProg)
    (lw : TypedLoweredWorld f.fir cert sched lp prepared.environment.source.world)
    (hnc : natCoreProgram f.fir cert = true)
    (compiled : Aiur.Optimized.ModulesArtifact prepared)
    (physical : Aiur.Optimized.Physical.Prepared compiled.circuit.artifact)
    {dcfg : Aiur.Optimized.Depth.Config}
    (certified : Aiur.Optimized.Physical.Prepared.DepthCertified compiled.circuit physical dcfg)
    (bits : dcfg.bits ≤ 24)
    (plan : Aiur.Optimized.Grouping.Plan (Aiur.Optimized.Depth.system dcfg physical.system) id)
    (activated : plan.WellFormedActivation)
    {external : String}
    {entry : Aiur.Modules.Selection moduleProg prepared.environment.assembly.instances}
    (selected : prepared.find? external = some entry)
    {i : Nat} {g : Fir.FunId}
    (hname : entry.resolved.name = qualified (entryName i))
    (hexp : f.fir.exports[i]? = some g)
    {rom : Aiur.WidthROM G} (valid : rom.Valid)
    {args : List (SourceValue G)} {result : Aiur.Value G}
    {wires : List (Aiur.WireValue G)} {output : Aiur.WireValue G}
    (signed : Aiur.Circuit.Erasure.Signed compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message G}
    (rooted : Aiur.Optimized.Depth.erase dcfg root =
      Aiur.Circuit.Erasure.message compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ dcfg.names)
    {rows : List (Aiur.Circuit.WeightedRow G)} (bound : rows.length ≤ 2 ^ 39)
    (checked : plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues compiled.specialized.program.enums wires (Aiur.entryValues args))
    (decoded : output.decode compiled.specialized.program.enums = some result) :
    ∃ (value : SourceValue G) (heap : Heap G) (ns : List Nat) (w : Fir.Val),
      (∀ n ∈ ns, n < natLimit) ∧
      args = ns.map (fun n => .field (n : G)) ∧
      lp.exportReps[i]? = some (repOf f.fir cert (scanFeatures f.fir) (cert.fn g).ret) ∧
      TVR f.fir cert (scanFeatures f.fir) heap
        (repOf f.fir cert (scanFeatures f.fir) (cert.fn g).ret) w value ∧
      Aiur.Represents ((Aiur.Circuit.Erasure.typedROM compiled.circuit.system rom).decode
        compiled.specialized.program.enums) heap value result ∧
      (f.Covered c (i, ns) →
        (∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, ns) k = .ok v ∧
            Sem.Lang.ObsEq (S := CheckedProgram) (T := Fir.Program) v w) ∨
          ∃ k, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, ns) k = .stuck) := by
  obtain ⟨value, heap, ns, k, w, hns, hargs, hrun, hrepGet, htvr, hrep⟩ :=
    typed_circuit_sound_goldilocks prepared lw hnc compiled physical certified bits plan activated
      selected hname hexp valid signed rooted outside bound checked arguments decoded
  exact ⟨value, heap, ns, w, hns, hargs, hrepGet, htvr, hrep,
    fun hcov => source_of_fir_run hf hexp hrun hcov⟩

/-- **Accepted Goldilocks circuit rows for a typed lowered program, read at the source,
under `NeverStuck`.** -/
theorem typed_circuit_source_sound_goldilocks {cfg : Recheck.Config} {P : Src.Program}
    {c : Recheck.Cert} {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {cert : Fir.Shape.ShapeCert} {sched : CircuitSchedule} {lp : LoweredProgram}
    {moduleProg : Aiur.Modules.Program G}
    {id : String → Except String Nat}
    (prepared : Aiur.Modules.Prepared moduleProg)
    (lw : TypedLoweredWorld f.fir cert sched lp prepared.environment.source.world)
    (hnc : natCoreProgram f.fir cert = true)
    (compiled : Aiur.Optimized.ModulesArtifact prepared)
    (physical : Aiur.Optimized.Physical.Prepared compiled.circuit.artifact)
    {dcfg : Aiur.Optimized.Depth.Config}
    (certified : Aiur.Optimized.Physical.Prepared.DepthCertified compiled.circuit physical dcfg)
    (bits : dcfg.bits ≤ 24)
    (plan : Aiur.Optimized.Grouping.Plan (Aiur.Optimized.Depth.system dcfg physical.system) id)
    (activated : plan.WellFormedActivation)
    {external : String}
    {entry : Aiur.Modules.Selection moduleProg prepared.environment.assembly.instances}
    (selected : prepared.find? external = some entry)
    {i : Nat} {g : Fir.FunId}
    (hname : entry.resolved.name = qualified (entryName i))
    (hexp : f.fir.exports[i]? = some g)
    {rom : Aiur.WidthROM G} (valid : rom.Valid)
    {args : List (SourceValue G)} {result : Aiur.Value G}
    {wires : List (Aiur.WireValue G)} {output : Aiur.WireValue G}
    (signed : Aiur.Circuit.Erasure.Signed compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message G}
    (rooted : Aiur.Optimized.Depth.erase dcfg root =
      Aiur.Circuit.Erasure.message compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ dcfg.names)
    {rows : List (Aiur.Circuit.WeightedRow G)} (bound : rows.length ≤ 2 ^ 39)
    (checked : plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues compiled.specialized.program.enums wires (Aiur.entryValues args))
    (decoded : output.decode compiled.specialized.program.enums = some result)
    (hp : ∀ ns : List Nat, args = ns.map (fun n => .field (n : G)) →
      NeverStuck ⟨f.src, f.checked⟩ (i, ns)) :
    ∃ (value : SourceValue G) (heap : Heap G) (ns : List Nat) (w : Fir.Val),
      (∀ n ∈ ns, n < natLimit) ∧
      args = ns.map (fun n => .field (n : G)) ∧
      lp.exportReps[i]? = some (repOf f.fir cert (scanFeatures f.fir) (cert.fn g).ret) ∧
      TVR f.fir cert (scanFeatures f.fir) heap
        (repOf f.fir cert (scanFeatures f.fir) (cert.fn g).ret) w value ∧
      Aiur.Represents ((Aiur.Circuit.Erasure.typedROM compiled.circuit.system rom).decode
        compiled.specialized.program.enums) heap value result ∧
      (f.Covered c (i, ns) →
        ∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, ns) k = .ok v ∧
          Sem.Lang.ObsEq (S := CheckedProgram) (T := Fir.Program) v w) := by
  obtain ⟨value, heap, ns, k, w, hns, hargs, hrun, hrepGet, htvr, hrep⟩ :=
    typed_circuit_sound_goldilocks prepared lw hnc compiled physical certified bits plan activated
      selected hname hexp valid signed rooted outside bound checked arguments decoded
  exact ⟨value, heap, ns, w, hns, hargs, hrepGet, htvr, hrep, fun hcov =>
    source_of_fir_run_of_neverStuck hf hexp hrun hcov (hp ns hargs)⟩

/-- **An accepted typed claim, read at the source (with stuck-source disjunct),** with
`TypedLoweredWorld` discharged purely from `TypedWorld.checkTypedWorld`. -/
theorem typed_accepted_source_backward {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {cert : Fir.Shape.ShapeCert} {sched : CircuitSchedule} {lp : LoweredProgram}
    (hnc : natCoreProgram f.fir cert = true)
    (hlow : TypedLower.lowerProgram f.fir cert sched = .ok lp)
    {moduleProg : Aiur.Modules.Program G} (prepared : Aiur.Modules.Prepared moduleProg)
    (hw : checkTypedWorld prepared.environment.source lp = true)
    {i : Nat} {g : Fir.FunId} (hexp : f.fir.exports[i]? = some g)
    {args : List (SourceValue G)} {result : Aiur.Value G}
    (acc : Accepted prepared i args result) :
    ∃ (value : SourceValue G) (heap : Heap G) (rom : Aiur.ROM G) (ns : List Nat) (w : Fir.Val),
      (∀ n ∈ ns, n < natLimit) ∧
      args = ns.map (fun n => .field (n : G)) ∧
      lp.exportReps[i]? = some (repOf f.fir cert (scanFeatures f.fir) (cert.fn g).ret) ∧
      TVR f.fir cert (scanFeatures f.fir) heap
        (repOf f.fir cert (scanFeatures f.fir) (cert.fn g).ret) w value ∧
      Aiur.Represents rom heap value result ∧
      (f.Covered c (i, ns) →
        (∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, ns) k = .ok v ∧
            Sem.Lang.ObsEq (S := CheckedProgram) (T := Fir.Program) v w) ∨
          ∃ k, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, ns) k = .stuck) := by
  obtain ⟨id, compiled, physical, dcfg, plan, external, entry, rom, wires, output, root, rows,
    certified, bits, activated, selected, hname, valid, signed, rooted, outside, bound, checked,
    arguments, decoded⟩ := acc
  obtain ⟨value, heap, ns, w, hns, hargs, hrepGet, htvr, hrep, hsrc⟩ :=
    typed_circuit_source_backward_goldilocks hf prepared
      (typedLoweredWorld_of_natCore fieldCompatible64_goldilocks hnc hlow _ hw) hnc
      compiled physical certified bits plan activated selected hname hexp valid signed rooted
      outside bound checked arguments decoded
  exact ⟨value, heap, _, ns, w, hns, hargs, hrepGet, htvr, hrep, hsrc⟩

/-! ### Unboxed `Nat` Claims (Public Output = Raw `.field y`) -/

/-- **An accepted unboxed `Nat` claim (`.field y`), read at the source (with stuck-source disjunct).**
Applies whenever `lp.exportReps[i]? = some retR` with `retR.isFieldNat = true` (every
unboxed `Nat`/`UInt8`/`UInt16`-returning benchmark). -/
theorem typed_accepted_nat_backward {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {cert : Fir.Shape.ShapeCert} {sched : CircuitSchedule} {lp : LoweredProgram}
    (hnc : natCoreProgram f.fir cert = true)
    (hlow : TypedLower.lowerProgram f.fir cert sched = .ok lp)
    {moduleProg : Aiur.Modules.Program G} (prepared : Aiur.Modules.Prepared moduleProg)
    (hw : checkTypedWorld prepared.environment.source lp = true)
    {i : Nat} {g : Fir.FunId} (hexp : f.fir.exports[i]? = some g)
    {retR : Rep} (hret : lp.exportReps[i]? = some retR) (hfn : retR.isFieldNat = true)
    {as : List G} {y : G}
    (acc : Accepted prepared i (as.map Value.field) (.field y))
    (hcov : f.Covered c (i, as.map ZMod.val)) :
    (∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .ok v ∧
        Sem.Lang.obs (S := CheckedProgram) v = some (.nat y.val)) ∨
      ∃ k, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .stuck := by
  obtain ⟨value, heap, rom, ns, w, hns, hargs, hrepGet, htvr, hrep, hsrc⟩ :=
    typed_accepted_source_backward hf hnc hlow prepared hw hexp acc
  have hretEq : repOf f.fir cert (scanFeatures f.fir) (cert.fn g).ret = retR := by
    rw [hrepGet, Option.some.injEq] at hret
    exact hret
  rw [hretEq] at htvr
  have hvals : as.map ZMod.val = ns := vals_of_fields hns hargs
  rw [hvals] at hcov ⊢
  obtain ⟨n, hn, rfl, hy⟩ := result_fieldNat hfn htvr hrep
  have hval : y.val = n := by rw [← hy]; exact val_natCast_lt hn
  rcases hsrc hcov with ⟨k, v, hrun, hobs⟩ | ⟨k, hstuck⟩
  · exact Or.inl ⟨k, v, hrun, by rw [hval]; exact Eq.trans hobs (obs_nat n)⟩
  · exact Or.inr ⟨k, hstuck⟩

/-- **An accepted unboxed `Nat` claim (`.field y`), read at the source, under `NeverStuck`.** -/
theorem typed_accepted_nat_sound {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {cert : Fir.Shape.ShapeCert} {sched : CircuitSchedule} {lp : LoweredProgram}
    (hnc : natCoreProgram f.fir cert = true)
    (hlow : TypedLower.lowerProgram f.fir cert sched = .ok lp)
    {moduleProg : Aiur.Modules.Program G} (prepared : Aiur.Modules.Prepared moduleProg)
    (hw : checkTypedWorld prepared.environment.source lp = true)
    {i : Nat} {g : Fir.FunId} (hexp : f.fir.exports[i]? = some g)
    {retR : Rep} (hret : lp.exportReps[i]? = some retR) (hfn : retR.isFieldNat = true)
    {as : List G} {y : G}
    (acc : Accepted prepared i (as.map Value.field) (.field y))
    (hcov : f.Covered c (i, as.map ZMod.val))
    (hp : NeverStuck ⟨f.src, f.checked⟩ (i, as.map ZMod.val)) :
    ∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .ok v ∧
      Sem.Lang.obs (S := CheckedProgram) v = some (.nat y.val) := by
  rcases typed_accepted_nat_backward hf hnc hlow prepared hw hexp hret hfn acc hcov with h | ⟨k, hk⟩
  · exact h
  · exact absurd hk (hp k)

/-- **An accepted unboxed `Nat` claim (`.field y`), read at the source, with NO escape disjunct**
(discharging `NeverStuck` from `Progress.checkShape` / `SrcShape.neverStuck_checked`). -/
theorem typed_accepted_nat {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {cert : Fir.Shape.ShapeCert} {sched : CircuitSchedule} {lp : LoweredProgram}
    (hnc : natCoreProgram f.fir cert = true)
    (hlow : TypedLower.lowerProgram f.fir cert sched = .ok lp)
    {moduleProg : Aiur.Modules.Program G} (prepared : Aiur.Modules.Prepared moduleProg)
    (hw : checkTypedWorld prepared.environment.source lp = true)
    {i : Nat} {g : Fir.FunId} (hexp : f.fir.exports[i]? = some g)
    {retR : Rep} (hret : lp.exportReps[i]? = some retR) (hfn : retR.isFieldNat = true)
    {as : List G} {y : G}
    (acc : Accepted prepared i (as.map Value.field) (.field y))
    (hcov : f.Covered c (i, as.map ZMod.val))
    {shapes : SrcShape.Cert} (hshape : checkShape f.src shapes i as.length = true) :
    ∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .ok v ∧
      Sem.Lang.obs (S := CheckedProgram) v = some (.nat y.val) :=
  typed_accepted_nat_sound hf hnc hlow prepared hw hexp hret hfn acc hcov
    (neverStuck_of_checkShape (ns := as.map ZMod.val) (by rw [List.length_map]; exact hshape))

/-! ### Dedicated `E<ind>` Enumeration Claims -/

/-- **An accepted dedicated-enum claim (`Prog::E<ind>::<ctor>`), read at the source
(with stuck-source disjunct).** -/
theorem typed_accepted_enum_backward {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {cert : Fir.Shape.ShapeCert} {sched : CircuitSchedule} {lp : LoweredProgram}
    (hnc : natCoreProgram f.fir cert = true)
    (hlow : TypedLower.lowerProgram f.fir cert sched = .ok lp)
    {moduleProg : Aiur.Modules.Program G} (prepared : Aiur.Modules.Prepared moduleProg)
    (hw : checkTypedWorld prepared.environment.source lp = true)
    {i : Nat} {g : Fir.FunId} (hexp : f.fir.exports[i]? = some g)
    {ind : Src.CId} (hret : lp.exportReps[i]? = some (.enum ind))
    {as : List G} {idx : Nat} {entry : Lam.CtorInfo} {cid : Src.CId}
    (hget : f.fir.ctors[idx]? = some entry) (hkey : entry.key = .src cid)
    (acc : Accepted prepared i (as.map Value.field)
      (.construct (enumQName ind) (ctorNameOf idx entry.key) []))
    (hcov : f.Covered c (i, as.map ZMod.val)) :
    (∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .ok v ∧
        Sem.Lang.obs (S := CheckedProgram) v = some (.ctor cid [])) ∨
      ∃ k, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .stuck := by
  obtain ⟨value, heap, rom, ns, w, hns, hargs, hrepGet, htvr, hrep, hsrc⟩ :=
    typed_accepted_source_backward hf hnc hlow prepared hw hexp acc
  have hretEq : repOf f.fir cert (scanFeatures f.fir) (cert.fn g).ret = .enum ind := by
    rw [hrepGet, Option.some.injEq] at hret
    exact hret
  rw [hretEq] at htvr
  have hvals : as.map ZMod.val = ns := vals_of_fields hns hargs
  rw [hvals] at hcov ⊢
  obtain ⟨ci, rfl, hci⟩ := result_typed_enum (typedLowerProgram_inv hlow).2.1 hget htvr hrep
  rcases hsrc hcov with ⟨k, v, hrun, hobs⟩ | ⟨k, hstuck⟩
  · exact Or.inl ⟨k, v, hrun, Eq.trans hobs (obs_ctor_nil (hci.trans hkey))⟩
  · exact Or.inr ⟨k, hstuck⟩

/-- **An accepted dedicated-enum claim, read at the source, under `NeverStuck`.** -/
theorem typed_accepted_enum_sound {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {cert : Fir.Shape.ShapeCert} {sched : CircuitSchedule} {lp : LoweredProgram}
    (hnc : natCoreProgram f.fir cert = true)
    (hlow : TypedLower.lowerProgram f.fir cert sched = .ok lp)
    {moduleProg : Aiur.Modules.Program G} (prepared : Aiur.Modules.Prepared moduleProg)
    (hw : checkTypedWorld prepared.environment.source lp = true)
    {i : Nat} {g : Fir.FunId} (hexp : f.fir.exports[i]? = some g)
    {ind : Src.CId} (hret : lp.exportReps[i]? = some (.enum ind))
    {as : List G} {idx : Nat} {entry : Lam.CtorInfo} {cid : Src.CId}
    (hget : f.fir.ctors[idx]? = some entry) (hkey : entry.key = .src cid)
    (acc : Accepted prepared i (as.map Value.field)
      (.construct (enumQName ind) (ctorNameOf idx entry.key) []))
    (hcov : f.Covered c (i, as.map ZMod.val))
    (hp : NeverStuck ⟨f.src, f.checked⟩ (i, as.map ZMod.val)) :
    ∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .ok v ∧
      Sem.Lang.obs (S := CheckedProgram) v = some (.ctor cid []) := by
  rcases typed_accepted_enum_backward hf hnc hlow prepared hw hexp hret hget hkey acc hcov with
    h | ⟨k, hk⟩
  · exact h
  · exact absurd hk (hp k)

/-- **An accepted dedicated-enum claim, read at the source, with NO escape disjunct.** -/
theorem typed_accepted_enum {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {cert : Fir.Shape.ShapeCert} {sched : CircuitSchedule} {lp : LoweredProgram}
    (hnc : natCoreProgram f.fir cert = true)
    (hlow : TypedLower.lowerProgram f.fir cert sched = .ok lp)
    {moduleProg : Aiur.Modules.Program G} (prepared : Aiur.Modules.Prepared moduleProg)
    (hw : checkTypedWorld prepared.environment.source lp = true)
    {i : Nat} {g : Fir.FunId} (hexp : f.fir.exports[i]? = some g)
    {ind : Src.CId} (hret : lp.exportReps[i]? = some (.enum ind))
    {as : List G} {idx : Nat} {entry : Lam.CtorInfo} {cid : Src.CId}
    (hget : f.fir.ctors[idx]? = some entry) (hkey : entry.key = .src cid)
    (acc : Accepted prepared i (as.map Value.field)
      (.construct (enumQName ind) (ctorNameOf idx entry.key) []))
    (hcov : f.Covered c (i, as.map ZMod.val))
    {shapes : SrcShape.Cert} (hshape : checkShape f.src shapes i as.length = true) :
    ∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .ok v ∧
      Sem.Lang.obs (S := CheckedProgram) v = some (.ctor cid []) :=
  typed_accepted_enum_sound hf hnc hlow prepared hw hexp hret hget hkey acc hcov
    (neverStuck_of_checkShape (ns := as.map ZMod.val) (by rw [List.length_map]; exact hshape))

/-! ### Fallback Boxed `Obj` Claims (`lp.exportReps[i]? = some .obj`) -/

/-- **An accepted fallback `Obj::N(y)` claim** under typed lowering (with stuck-source disjunct). -/
theorem typed_accepted_obj_nat_backward {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {cert : Fir.Shape.ShapeCert} {sched : CircuitSchedule} {lp : LoweredProgram}
    (hnc : natCoreProgram f.fir cert = true)
    (hlow : TypedLower.lowerProgram f.fir cert sched = .ok lp)
    {moduleProg : Aiur.Modules.Program G} (prepared : Aiur.Modules.Prepared moduleProg)
    (hw : checkTypedWorld prepared.environment.source lp = true)
    {i : Nat} {g : Fir.FunId} (hexp : f.fir.exports[i]? = some g)
    (hret : lp.exportReps[i]? = some .obj)
    {as : List G} {y : G}
    (acc : Accepted prepared i (as.map Value.field) (.construct objQName "N" [.field y]))
    (hcov : f.Covered c (i, as.map ZMod.val)) :
    (∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .ok v ∧
        Sem.Lang.obs (S := CheckedProgram) v = some (.nat y.val)) ∨
      ∃ k, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .stuck := by
  obtain ⟨value, heap, rom, ns, w, hns, hargs, hrepGet, htvr, hrep, hsrc⟩ :=
    typed_accepted_source_backward hf hnc hlow prepared hw hexp acc
  have hretEq : repOf f.fir cert (scanFeatures f.fir) (cert.fn g).ret = .obj := by
    rw [hrepGet, Option.some.injEq] at hret
    exact hret
  rw [hretEq] at htvr
  have hvals : as.map ZMod.val = ns := vals_of_fields hns hargs
  rw [hvals] at hcov ⊢
  obtain ⟨n, hn, rfl, hy⟩ := result_typed_obj_nat htvr hrep
  have hval : y.val = n := by rw [← hy]; exact val_natCast_lt hn
  rcases hsrc hcov with ⟨k, v, hrun, hobs⟩ | ⟨k, hstuck⟩
  · exact Or.inl ⟨k, v, hrun, by rw [hval]; exact Eq.trans hobs (obs_nat n)⟩
  · exact Or.inr ⟨k, hstuck⟩

/-- **An accepted fallback `Obj::N(y)` claim** under typed lowering, with NO escape disjunct. -/
theorem typed_accepted_obj_nat {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {cert : Fir.Shape.ShapeCert} {sched : CircuitSchedule} {lp : LoweredProgram}
    (hnc : natCoreProgram f.fir cert = true)
    (hlow : TypedLower.lowerProgram f.fir cert sched = .ok lp)
    {moduleProg : Aiur.Modules.Program G} (prepared : Aiur.Modules.Prepared moduleProg)
    (hw : checkTypedWorld prepared.environment.source lp = true)
    {i : Nat} {g : Fir.FunId} (hexp : f.fir.exports[i]? = some g)
    (hret : lp.exportReps[i]? = some .obj)
    {as : List G} {y : G}
    (acc : Accepted prepared i (as.map Value.field) (.construct objQName "N" [.field y]))
    (hcov : f.Covered c (i, as.map ZMod.val))
    {shapes : SrcShape.Cert} (hshape : checkShape f.src shapes i as.length = true) :
    ∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .ok v ∧
      Sem.Lang.obs (S := CheckedProgram) v = some (.nat y.val) := by
  rcases typed_accepted_obj_nat_backward hf hnc hlow prepared hw hexp hret acc hcov with
    h | ⟨k, hk⟩
  · exact h
  · exact absurd hk
      (neverStuck_of_checkShape (ns := as.map ZMod.val) (by rw [List.length_map]; exact hshape) k)

/-- **An accepted fallback `Obj::<ctor>` enumeration claim** under typed lowering
(with stuck-source disjunct). -/
theorem typed_accepted_obj_enum_backward {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {cert : Fir.Shape.ShapeCert} {sched : CircuitSchedule} {lp : LoweredProgram}
    (hnc : natCoreProgram f.fir cert = true)
    (hlow : TypedLower.lowerProgram f.fir cert sched = .ok lp)
    {moduleProg : Aiur.Modules.Program G} (prepared : Aiur.Modules.Prepared moduleProg)
    (hw : checkTypedWorld prepared.environment.source lp = true)
    {i : Nat} {g : Fir.FunId} (hexp : f.fir.exports[i]? = some g)
    (hret : lp.exportReps[i]? = some .obj)
    {as : List G} {idx : Nat} {entry : Lam.CtorInfo} {cid : Src.CId}
    (hget : f.fir.ctors[idx]? = some entry) (hkey : entry.key = .src cid)
    (acc : Accepted prepared i (as.map Value.field)
      (.construct objQName (ctorNameOf idx entry.key) []))
    (hcov : f.Covered c (i, as.map ZMod.val)) :
    (∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .ok v ∧
        Sem.Lang.obs (S := CheckedProgram) v = some (.ctor cid [])) ∨
      ∃ k, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .stuck := by
  obtain ⟨value, heap, rom, ns, w, hns, hargs, hrepGet, htvr, hrep, hsrc⟩ :=
    typed_accepted_source_backward hf hnc hlow prepared hw hexp acc
  have hretEq : repOf f.fir cert (scanFeatures f.fir) (cert.fn g).ret = .obj := by
    rw [hrepGet, Option.some.injEq] at hret
    exact hret
  rw [hretEq] at htvr
  have hvals : as.map ZMod.val = ns := vals_of_fields hns hargs
  rw [hvals] at hcov ⊢
  obtain ⟨ci, rfl, hci⟩ := result_typed_obj_enum (typedLowerProgram_inv hlow).2.1 hget htvr hrep
  rcases hsrc hcov with ⟨k, v, hrun, hobs⟩ | ⟨k, hstuck⟩
  · exact Or.inl ⟨k, v, hrun, Eq.trans hobs (obs_ctor_nil (hci.trans hkey))⟩
  · exact Or.inr ⟨k, hstuck⟩

/-- **An accepted fallback `Obj::<ctor>` enumeration claim** under typed lowering,
with NO escape disjunct. -/
theorem typed_accepted_obj_enum {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {cert : Fir.Shape.ShapeCert} {sched : CircuitSchedule} {lp : LoweredProgram}
    (hnc : natCoreProgram f.fir cert = true)
    (hlow : TypedLower.lowerProgram f.fir cert sched = .ok lp)
    {moduleProg : Aiur.Modules.Program G} (prepared : Aiur.Modules.Prepared moduleProg)
    (hw : checkTypedWorld prepared.environment.source lp = true)
    {i : Nat} {g : Fir.FunId} (hexp : f.fir.exports[i]? = some g)
    (hret : lp.exportReps[i]? = some .obj)
    {as : List G} {idx : Nat} {entry : Lam.CtorInfo} {cid : Src.CId}
    (hget : f.fir.ctors[idx]? = some entry) (hkey : entry.key = .src cid)
    (acc : Accepted prepared i (as.map Value.field)
      (.construct objQName (ctorNameOf idx entry.key) []))
    (hcov : f.Covered c (i, as.map ZMod.val))
    {shapes : SrcShape.Cert} (hshape : checkShape f.src shapes i as.length = true) :
    ∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .ok v ∧
      Sem.Lang.obs (S := CheckedProgram) v = some (.ctor cid []) := by
  rcases typed_accepted_obj_enum_backward hf hnc hlow prepared hw hexp hret hget hkey acc hcov with
    h | ⟨k, hk⟩
  · exact h
  · exact absurd hk
      (neverStuck_of_checkShape (ns := as.map ZMod.val) (by rw [List.length_map]; exact hshape) k)

end IxCC.AiurBackend.TypedClaim
