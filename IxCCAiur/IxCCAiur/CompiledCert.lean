import IxCCAiur.Progress
import IxCCAiur.TypedClaim
import IxCC.Ixon.Address

/-! # Compiled circuit certificate & artifact digest pin (`IxCCAiur.CompiledCert`)

Bundles the verified compiler facts produced alongside an emitted `.ixa`
artifact (whether a reusable `IXAIURP\0` program package or an `IXAIURX\0`
execution package):

* `World.checkWorld` holds on the prepared Aiur source for the lowered program;
* `Physical.Prepared.checkDepthPlan` holds on the deduplicated physical circuits,
  depth configuration, structural measures, and grouping plan (giving
  `DepthCertified`, `cfg.bits ≤ 24`, and `plan.WellFormedActivation` via
  `Physical.Prepared.checkDepthPlan_sound`);
* the selected entry resolves to `Prog::main<i>`;
* `artifactDigest = Ixon.Address.blake3Pure artifactBytes` pins the exact
  serialized `.ixa` bytes.

Any trace rows accepted by `plan.checkMemo` for the certified artifact
immediately discharge `Claim.Accepted`, and compose directly with
`Claim.accepted_nat_backward` and `Progress.accepted_nat` (escape-free SrcEval
soundness). -/

set_option autoImplicit false

namespace IxCC.AiurBackend.CompiledCert

open Aiur Aiur.Generic
open IxCC.Lam.Erase.Proof (CheckedProgram)
open IxCC.AiurBackend.Lower IxCC.AiurBackend.Claim

/-- Envelope format of an emitted `.ixa` artifact. -/
inductive ArtifactKind where
  /-- Reusable compiled program + trace plan (`IXAIURP\0`, `Aiur.Artifact.package`). -/
  | program
  /-- Single-invocation execution package (`IXAIURX\0`, `Aiur.Artifact.execution`). -/
  | execution
  deriving DecidableEq, Repr, Inhabited

def ArtifactKind.label : ArtifactKind → String
  | .program => "program"
  | .execution => "execution"

/-- **Certificate of a compiled `IxCCAiur` artifact**: pins the prepared program,
world check, optimized circuits, physical deduplication, depth-grouped plan
certificate (`checkDepthPlan`), selected entry `Prog::main<i>`, and pure-Lean
BLAKE3 digest of the serialized `.ixa` bytes. -/
structure Cert {P : Fir.Program} {prog : Aiur.Generic.Program Nat}
    {moduleProg : Aiur.Modules.Program G}
    (prepared : Aiur.Modules.Prepared moduleProg) (entryIdx : Nat) where
  lowered : lowerProgram P = .ok prog
  worldOk : World.checkWorld prepared.environment.source prog = true
  id : String → Except String Nat
  compiled : Aiur.Optimized.ModulesArtifact prepared
  physical : Aiur.Optimized.Physical.Prepared compiled.circuit.artifact
  dcfg : Aiur.Optimized.Depth.Config
  measures : Aiur.Optimized.Depth.Structural.Plan
  plan : Aiur.Optimized.Grouping.Plan
    (Aiur.Optimized.Depth.system dcfg physical.system) id
  depthPlanOk : physical.checkDepthPlan compiled.circuit.inlined.program dcfg measures plan = true
  external : String
  entry : Aiur.Modules.Selection moduleProg prepared.environment.assembly.instances
  selected : prepared.find? external = some entry
  entryNameEq : entry.resolved.name = qualified (entryName entryIdx)
  artifactKind : ArtifactKind
  artifactBytes : ByteArray
  artifactDigest : Ixon.Address
  digestEq : artifactDigest = Ixon.Address.blake3Pure artifactBytes

/-- Rows accepted by the certified plan's `checkMemo` yield `Claim.Accepted`. -/
theorem Cert.accepted_of_checkMemo {P : Fir.Program} {prog : Aiur.Generic.Program Nat}
    {moduleProg : Aiur.Modules.Program G} {prepared : Aiur.Modules.Prepared moduleProg}
    {i : Nat} (cert : Cert (P := P) (prog := prog) prepared i)
    {rom : Aiur.WidthROM G} (valid : rom.Valid)
    {args : List (Aiur.SourceValue G)} {result : Aiur.Value G}
    {wires : List (Aiur.WireValue G)} {output : Aiur.WireValue G}
    (signed : Aiur.Circuit.Erasure.Signed cert.compiled.circuit.system
      ⟨cert.entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message G}
    (rooted : Aiur.Optimized.Depth.erase cert.dcfg root =
      Aiur.Circuit.Erasure.message cert.compiled.circuit.system
        ⟨cert.entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cert.dcfg.names)
    {rows : List (Aiur.Circuit.WeightedRow G)} (bound : rows.length ≤ 2 ^ 39)
    (checked : cert.plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues cert.compiled.specialized.program.enums wires
      (Aiur.entryValues args))
    (decoded : output.decode cert.compiled.specialized.program.enums = some result) :
    Claim.Accepted prepared i args result := by
  obtain ⟨certified, bits, activated⟩ :=
    Aiur.Optimized.Physical.Prepared.checkDepthPlan_sound cert.depthPlanOk
  exact ⟨cert.id, cert.compiled, cert.physical, cert.dcfg, cert.plan, cert.external, cert.entry,
    rom, wires, output, root, rows, certified, bits, activated, cert.selected, cert.entryNameEq,
    valid, signed, rooted, outside, bound, checked, arguments, decoded⟩

/-- **Certified artifact `Nat` claim, read at the source (with stuck-source disjunct).** -/
theorem Cert.accepted_nat_backward {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {prog : Aiur.Generic.Program Nat} {moduleProg : Aiur.Modules.Program G}
    {prepared : Aiur.Modules.Prepared moduleProg} {i : Nat} {g : Fir.FunId}
    (cert : Cert (P := f.fir) (prog := prog) prepared i)
    (hexp : f.fir.exports[i]? = some g)
    {as : List G} {y : G}
    {rom : Aiur.WidthROM G} (valid : rom.Valid)
    {wires : List (Aiur.WireValue G)} {output : Aiur.WireValue G}
    (signed : Aiur.Circuit.Erasure.Signed cert.compiled.circuit.system
      ⟨cert.entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message G}
    (rooted : Aiur.Optimized.Depth.erase cert.dcfg root =
      Aiur.Circuit.Erasure.message cert.compiled.circuit.system
        ⟨cert.entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cert.dcfg.names)
    {rows : List (Aiur.Circuit.WeightedRow G)} (bound : rows.length ≤ 2 ^ 39)
    (checked : cert.plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues cert.compiled.specialized.program.enums wires
      (Aiur.entryValues (as.map Value.field)))
    (decoded : output.decode cert.compiled.specialized.program.enums =
      some (.construct objQName "N" [.field y]))
    (hcov : f.Covered c (i, as.map ZMod.val)) :
    (∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .ok v ∧
        Sem.Lang.obs (S := CheckedProgram) v = some (.nat y.val)) ∨
      ∃ k, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .stuck :=
  Claim.accepted_nat_backward hf cert.lowered prepared cert.worldOk hexp
    (cert.accepted_of_checkMemo valid signed rooted outside bound checked arguments decoded) hcov

/-- **Certified artifact `Nat` claim, read at the source (escape-free via `Progress.checkShape`).** -/
theorem Cert.accepted_nat {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {prog : Aiur.Generic.Program Nat} {moduleProg : Aiur.Modules.Program G}
    {prepared : Aiur.Modules.Prepared moduleProg} {i : Nat} {g : Fir.FunId}
    (cert : Cert (P := f.fir) (prog := prog) prepared i)
    (hexp : f.fir.exports[i]? = some g)
    {as : List G} {y : G}
    {rom : Aiur.WidthROM G} (valid : rom.Valid)
    {wires : List (Aiur.WireValue G)} {output : Aiur.WireValue G}
    (signed : Aiur.Circuit.Erasure.Signed cert.compiled.circuit.system
      ⟨cert.entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message G}
    (rooted : Aiur.Optimized.Depth.erase cert.dcfg root =
      Aiur.Circuit.Erasure.message cert.compiled.circuit.system
        ⟨cert.entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cert.dcfg.names)
    {rows : List (Aiur.Circuit.WeightedRow G)} (bound : rows.length ≤ 2 ^ 39)
    (checked : cert.plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues cert.compiled.specialized.program.enums wires
      (Aiur.entryValues (as.map Value.field)))
    (decoded : output.decode cert.compiled.specialized.program.enums =
      some (.construct objQName "N" [.field y]))
    (hcov : f.Covered c (i, as.map ZMod.val))
    {shapes : SrcShape.Cert} (hshape : Progress.checkShape f.src shapes i as.length = true) :
    ∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .ok v ∧
      Sem.Lang.obs (S := CheckedProgram) v = some (.nat y.val) :=
  Progress.accepted_nat hf cert.lowered prepared cert.worldOk hexp
    (cert.accepted_of_checkMemo valid signed rooted outside bound checked arguments decoded)
    hcov hshape

/-! ## Typed / Unboxed Artifact Certificate (`TypedCert`) -/

/-- **Certificate of a typed/unboxed `IxCCAiur` artifact**: pins
`TypedLower.lowerProgram`, `TypedBackward.natCoreProgram`, tier-aware
`TypedWorld.checkTypedWorld`, optimized circuits, physical deduplication,
depth-grouped plan certificate (`checkDepthPlan`), selected entry
`Prog::main<i>`, and pure-Lean BLAKE3 digest of the serialized `.ixa` bytes. -/
structure TypedCert {P : Fir.Program} {shapeCert : Fir.Shape.ShapeCert}
    {sched : Schedule.CircuitSchedule} {lp : TypedLower.LoweredProgram}
    {moduleProg : Aiur.Modules.Program G}
    (prepared : Aiur.Modules.Prepared moduleProg) (entryIdx : Nat) where
  lowered : TypedLower.lowerProgram P shapeCert sched = .ok lp
  natCoreOk : TypedBackward.natCoreProgram P shapeCert = true
  worldOk : TypedWorld.checkTypedWorld prepared.environment.source lp = true
  id : String → Except String Nat
  compiled : Aiur.Optimized.ModulesArtifact prepared
  physical : Aiur.Optimized.Physical.Prepared compiled.circuit.artifact
  dcfg : Aiur.Optimized.Depth.Config
  measures : Aiur.Optimized.Depth.Structural.Plan
  plan : Aiur.Optimized.Grouping.Plan
    (Aiur.Optimized.Depth.system dcfg physical.system) id
  depthPlanOk : physical.checkDepthPlan compiled.circuit.inlined.program dcfg measures plan = true
  external : String
  entry : Aiur.Modules.Selection moduleProg prepared.environment.assembly.instances
  selected : prepared.find? external = some entry
  entryNameEq : entry.resolved.name = qualified (entryName entryIdx)
  artifactKind : ArtifactKind
  artifactBytes : ByteArray
  artifactDigest : Ixon.Address
  digestEq : artifactDigest = Ixon.Address.blake3Pure artifactBytes

/-- Rows accepted by a typed certified plan's `checkMemo` yield `Claim.Accepted`. -/
theorem TypedCert.accepted_of_checkMemo {P : Fir.Program} {shapeCert : Fir.Shape.ShapeCert}
    {sched : Schedule.CircuitSchedule} {lp : TypedLower.LoweredProgram}
    {moduleProg : Aiur.Modules.Program G} {prepared : Aiur.Modules.Prepared moduleProg}
    {i : Nat} (cert : TypedCert (P := P) (shapeCert := shapeCert) (sched := sched) (lp := lp) prepared i)
    {rom : Aiur.WidthROM G} (valid : rom.Valid)
    {args : List (Aiur.SourceValue G)} {result : Aiur.Value G}
    {wires : List (Aiur.WireValue G)} {output : Aiur.WireValue G}
    (signed : Aiur.Circuit.Erasure.Signed cert.compiled.circuit.system
      ⟨cert.entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message G}
    (rooted : Aiur.Optimized.Depth.erase cert.dcfg root =
      Aiur.Circuit.Erasure.message cert.compiled.circuit.system
        ⟨cert.entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cert.dcfg.names)
    {rows : List (Aiur.Circuit.WeightedRow G)} (bound : rows.length ≤ 2 ^ 39)
    (checked : cert.plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues cert.compiled.specialized.program.enums wires
      (Aiur.entryValues args))
    (decoded : output.decode cert.compiled.specialized.program.enums = some result) :
    Claim.Accepted prepared i args result := by
  obtain ⟨certified, bits, activated⟩ :=
    Aiur.Optimized.Physical.Prepared.checkDepthPlan_sound cert.depthPlanOk
  exact ⟨cert.id, cert.compiled, cert.physical, cert.dcfg, cert.plan, cert.external, cert.entry,
    rom, wires, output, root, rows, certified, bits, activated, cert.selected, cert.entryNameEq,
    valid, signed, rooted, outside, bound, checked, arguments, decoded⟩

/-- **Certified typed artifact unboxed `Nat` claim (`.field y`), read at the source
(with stuck-source disjunct).** -/
theorem TypedCert.accepted_fieldNat_backward {cfg : Recheck.Config} {P : Src.Program}
    {c : Recheck.Cert} {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {shapeCert : Fir.Shape.ShapeCert} {sched : Schedule.CircuitSchedule}
    {lp : TypedLower.LoweredProgram} {moduleProg : Aiur.Modules.Program G}
    {prepared : Aiur.Modules.Prepared moduleProg} {i : Nat} {g : Fir.FunId}
    (cert : TypedCert (P := f.fir) (shapeCert := shapeCert) (sched := sched) (lp := lp) prepared i)
    (hexp : f.fir.exports[i]? = some g)
    {retR : TypedRep.Rep} (hret : lp.exportReps[i]? = some retR) (hfn : retR.isFieldNat = true)
    {as : List G} {y : G}
    {rom : Aiur.WidthROM G} (valid : rom.Valid)
    {wires : List (Aiur.WireValue G)} {output : Aiur.WireValue G}
    (signed : Aiur.Circuit.Erasure.Signed cert.compiled.circuit.system
      ⟨cert.entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message G}
    (rooted : Aiur.Optimized.Depth.erase cert.dcfg root =
      Aiur.Circuit.Erasure.message cert.compiled.circuit.system
        ⟨cert.entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cert.dcfg.names)
    {rows : List (Aiur.Circuit.WeightedRow G)} (bound : rows.length ≤ 2 ^ 39)
    (checked : cert.plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues cert.compiled.specialized.program.enums wires
      (Aiur.entryValues (as.map Value.field)))
    (decoded : output.decode cert.compiled.specialized.program.enums = some (.field y))
    (hcov : f.Covered c (i, as.map ZMod.val)) :
    (∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .ok v ∧
        Sem.Lang.obs (S := CheckedProgram) v = some (.nat y.val)) ∨
      ∃ k, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .stuck :=
  TypedClaim.typed_accepted_nat_backward hf cert.natCoreOk cert.lowered prepared cert.worldOk
    hexp hret hfn
    (cert.accepted_of_checkMemo valid signed rooted outside bound checked arguments decoded)
    hcov

/-- **Certified typed artifact unboxed field-`Nat` claim (`.field y`), read at the source
(escape-free via `Progress.checkShape`), composing directly with `TypedClaim.typed_accepted_nat`.** -/
theorem TypedCert.accepted_fieldNat {cfg : Recheck.Config} {P : Src.Program}
    {c : Recheck.Cert} {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {shapeCert : Fir.Shape.ShapeCert} {sched : Schedule.CircuitSchedule}
    {lp : TypedLower.LoweredProgram} {moduleProg : Aiur.Modules.Program G}
    {prepared : Aiur.Modules.Prepared moduleProg} {i : Nat} {g : Fir.FunId}
    (cert : TypedCert (P := f.fir) (shapeCert := shapeCert) (sched := sched) (lp := lp) prepared i)
    (hexp : f.fir.exports[i]? = some g)
    {retR : TypedRep.Rep} (hret : lp.exportReps[i]? = some retR) (hfn : retR.isFieldNat = true)
    {as : List G} {y : G}
    {rom : Aiur.WidthROM G} (valid : rom.Valid)
    {wires : List (Aiur.WireValue G)} {output : Aiur.WireValue G}
    (signed : Aiur.Circuit.Erasure.Signed cert.compiled.circuit.system
      ⟨cert.entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message G}
    (rooted : Aiur.Optimized.Depth.erase cert.dcfg root =
      Aiur.Circuit.Erasure.message cert.compiled.circuit.system
        ⟨cert.entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cert.dcfg.names)
    {rows : List (Aiur.Circuit.WeightedRow G)} (bound : rows.length ≤ 2 ^ 39)
    (checked : cert.plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues cert.compiled.specialized.program.enums wires
      (Aiur.entryValues (as.map Value.field)))
    (decoded : output.decode cert.compiled.specialized.program.enums = some (.field y))
    (hcov : f.Covered c (i, as.map ZMod.val))
    {shapes : SrcShape.Cert} (hshape : Progress.checkShape f.src shapes i as.length = true) :
    ∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .ok v ∧
      Sem.Lang.obs (S := CheckedProgram) v = some (.nat y.val) :=
  TypedClaim.typed_accepted_nat hf cert.natCoreOk cert.lowered prepared cert.worldOk
    hexp hret hfn
    (cert.accepted_of_checkMemo valid signed rooted outside bound checked arguments decoded)
    hcov hshape

/-- **Certified typed artifact unboxed `Nat` claim (`.field y`), read at the source
(escape-free via `Progress.checkShape`).** Alias of `TypedCert.accepted_fieldNat`
matching `Cert.accepted_nat` and `TypedClaim.typed_accepted_nat`. -/
theorem TypedCert.accepted_nat {cfg : Recheck.Config} {P : Src.Program}
    {c : Recheck.Cert} {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {shapeCert : Fir.Shape.ShapeCert} {sched : Schedule.CircuitSchedule}
    {lp : TypedLower.LoweredProgram} {moduleProg : Aiur.Modules.Program G}
    {prepared : Aiur.Modules.Prepared moduleProg} {i : Nat} {g : Fir.FunId}
    (cert : TypedCert (P := f.fir) (shapeCert := shapeCert) (sched := sched) (lp := lp) prepared i)
    (hexp : f.fir.exports[i]? = some g)
    {retR : TypedRep.Rep} (hret : lp.exportReps[i]? = some retR) (hfn : retR.isFieldNat = true)
    {as : List G} {y : G}
    {rom : Aiur.WidthROM G} (valid : rom.Valid)
    {wires : List (Aiur.WireValue G)} {output : Aiur.WireValue G}
    (signed : Aiur.Circuit.Erasure.Signed cert.compiled.circuit.system
      ⟨cert.entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message G}
    (rooted : Aiur.Optimized.Depth.erase cert.dcfg root =
      Aiur.Circuit.Erasure.message cert.compiled.circuit.system
        ⟨cert.entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cert.dcfg.names)
    {rows : List (Aiur.Circuit.WeightedRow G)} (bound : rows.length ≤ 2 ^ 39)
    (checked : cert.plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues cert.compiled.specialized.program.enums wires
      (Aiur.entryValues (as.map Value.field)))
    (decoded : output.decode cert.compiled.specialized.program.enums = some (.field y))
    (hcov : f.Covered c (i, as.map ZMod.val))
    {shapes : SrcShape.Cert} (hshape : Progress.checkShape f.src shapes i as.length = true) :
    ∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .ok v ∧
      Sem.Lang.obs (S := CheckedProgram) v = some (.nat y.val) :=
  cert.accepted_fieldNat hf hexp hret hfn valid signed rooted outside bound checked
    arguments decoded hcov hshape

/-- **Certified typed artifact dedicated-enum claim (`Prog::E<ind>::<ctor>`), read at the source
(escape-free via `Progress.checkShape`).** -/
theorem TypedCert.accepted_enum {cfg : Recheck.Config} {P : Src.Program}
    {c : Recheck.Cert} {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {shapeCert : Fir.Shape.ShapeCert} {sched : Schedule.CircuitSchedule}
    {lp : TypedLower.LoweredProgram} {moduleProg : Aiur.Modules.Program G}
    {prepared : Aiur.Modules.Prepared moduleProg} {i : Nat} {g : Fir.FunId}
    (cert : TypedCert (P := f.fir) (shapeCert := shapeCert) (sched := sched) (lp := lp) prepared i)
    (hexp : f.fir.exports[i]? = some g)
    {ind : Src.CId} (hret : lp.exportReps[i]? = some (.enum ind))
    {as : List G} {idx : Nat} {entry : Lam.CtorInfo} {cid : Src.CId}
    (hget : f.fir.ctors[idx]? = some entry) (hkey : entry.key = .src cid)
    {rom : Aiur.WidthROM G} (valid : rom.Valid)
    {wires : List (Aiur.WireValue G)} {output : Aiur.WireValue G}
    (signed : Aiur.Circuit.Erasure.Signed cert.compiled.circuit.system
      ⟨cert.entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message G}
    (rooted : Aiur.Optimized.Depth.erase cert.dcfg root =
      Aiur.Circuit.Erasure.message cert.compiled.circuit.system
        ⟨cert.entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cert.dcfg.names)
    {rows : List (Aiur.Circuit.WeightedRow G)} (bound : rows.length ≤ 2 ^ 39)
    (checked : cert.plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues cert.compiled.specialized.program.enums wires
      (Aiur.entryValues (as.map Value.field)))
    (decoded : output.decode cert.compiled.specialized.program.enums =
      some (.construct (TypedRep.enumQName ind) (ctorNameOf idx entry.key) []))
    (hcov : f.Covered c (i, as.map ZMod.val))
    {shapes : SrcShape.Cert} (hshape : Progress.checkShape f.src shapes i as.length = true) :
    ∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .ok v ∧
      Sem.Lang.obs (S := CheckedProgram) v = some (.ctor cid []) :=
  TypedClaim.typed_accepted_enum hf cert.natCoreOk cert.lowered prepared cert.worldOk
    hexp hret hget hkey
    (cert.accepted_of_checkMemo valid signed rooted outside bound checked arguments decoded)
    hcov hshape

/-- **Certified typed artifact fallback boxed `Obj::N(y)` claim, read at the source
(escape-free via `Progress.checkShape`).** -/
theorem TypedCert.accepted_obj_nat {cfg : Recheck.Config} {P : Src.Program}
    {c : Recheck.Cert} {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {shapeCert : Fir.Shape.ShapeCert} {sched : Schedule.CircuitSchedule}
    {lp : TypedLower.LoweredProgram} {moduleProg : Aiur.Modules.Program G}
    {prepared : Aiur.Modules.Prepared moduleProg} {i : Nat} {g : Fir.FunId}
    (cert : TypedCert (P := f.fir) (shapeCert := shapeCert) (sched := sched) (lp := lp) prepared i)
    (hexp : f.fir.exports[i]? = some g)
    (hret : lp.exportReps[i]? = some .obj)
    {as : List G} {y : G}
    {rom : Aiur.WidthROM G} (valid : rom.Valid)
    {wires : List (Aiur.WireValue G)} {output : Aiur.WireValue G}
    (signed : Aiur.Circuit.Erasure.Signed cert.compiled.circuit.system
      ⟨cert.entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message G}
    (rooted : Aiur.Optimized.Depth.erase cert.dcfg root =
      Aiur.Circuit.Erasure.message cert.compiled.circuit.system
        ⟨cert.entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ cert.dcfg.names)
    {rows : List (Aiur.Circuit.WeightedRow G)} (bound : rows.length ≤ 2 ^ 39)
    (checked : cert.plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues cert.compiled.specialized.program.enums wires
      (Aiur.entryValues (as.map Value.field)))
    (decoded : output.decode cert.compiled.specialized.program.enums =
      some (.construct objQName "N" [.field y]))
    (hcov : f.Covered c (i, as.map ZMod.val))
    {shapes : SrcShape.Cert} (hshape : Progress.checkShape f.src shapes i as.length = true) :
    ∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, as.map ZMod.val) k = .ok v ∧
      Sem.Lang.obs (S := CheckedProgram) v = some (.nat y.val) :=
  TypedClaim.typed_accepted_obj_nat hf cert.natCoreOk cert.lowered prepared cert.worldOk
    hexp hret
    (cert.accepted_of_checkMemo valid signed rooted outside bound checked arguments decoded)
    hcov hshape

/--
info: 'IxCC.AiurBackend.CompiledCert.TypedCert.accepted_of_checkMemo' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms TypedCert.accepted_of_checkMemo

/--
info: 'IxCC.AiurBackend.CompiledCert.TypedCert.accepted_fieldNat_backward' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms TypedCert.accepted_fieldNat_backward

/--
info: 'IxCC.AiurBackend.CompiledCert.TypedCert.accepted_fieldNat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms TypedCert.accepted_fieldNat

/--
info: 'IxCC.AiurBackend.CompiledCert.TypedCert.accepted_nat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms TypedCert.accepted_nat

/--
info: 'IxCC.AiurBackend.CompiledCert.TypedCert.accepted_enum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms TypedCert.accepted_enum

/--
info: 'IxCC.AiurBackend.CompiledCert.TypedCert.accepted_obj_nat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in #print axioms TypedCert.accepted_obj_nat

end IxCC.AiurBackend.CompiledCert
