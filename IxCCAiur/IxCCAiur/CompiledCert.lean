import IxCCAiur.Progress
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

end IxCC.AiurBackend.CompiledCert
