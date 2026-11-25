import IxCCAiur.Backward
import IxCC.Recheck.Proof.RunFir

/-! # From an accepted Aiur run to the source evaluator

The lowering's backward simulation (`Backward.entry_backward_sound`) ends at
`Fir.run` on the Fir program that was lowered. Here that program is the one
the compiler's front half makes (`Recheck.runFir`), and the simulation is
composed with the front half's refinement (`Recheck.front_fir`: erasure, the
middle end with the closures step, `Fir.lower`).

**What the composition says, and what it does not.** Every pass above Fir is
proved as a refinement that asks nothing of a stuck source
(`Sem.Behaviour.Refines.stuck`), and the middle end's proofs use that clause
(a dead projection or primitive is dropped because its value is "stuck or a
value"). So a value the lowered program returns is a value SrcEval returns
with the same observation, **or SrcEval is stuck on that input**
(`entry_source_backward`, `circuit_source_backward_goldilocks`). The second
disjunct is not discharged here. It goes away for an input on which the
source is stuck at no clock (`NeverStuck`, `entry_source_sound`,
`circuit_source_sound_goldilocks`): that is source progress at safety
strength, per input, on the unviewed source. Termination of the source is not
a premise (the accepted run supplies it), and neither is trap-freedom (every
pass keeps a trap, and the lowered trap has no derivation,
`Backward.trap_no_derivation`).

**Hypotheses that are still open.** `Backward.LoweredWorld` (that the prepared
Aiur source holds the lowered functions and the `UInt64` library's contracts)
is taken as a hypothesis, as in `Backward`; nothing constructs it yet.
`FrontFir.Covered` restricts the input to the root's declared parameter count
(or to a program the closures step left unchanged), as every theorem about
the front half does.

**What is related.** The Aiur result `r` on heap `h'` represents a Fir value
`w` (`Backward.VR`), and `w` has the source value's observation
(`Sem.Lang.ObsEq`). No statement here reads `w` off the public output of a
proof. -/

set_option autoImplicit false

namespace IxCC.AiurBackend.Compose

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics Aiur.Library
open IxCC.Lam.Erase.Proof (CheckedProgram)
open IxCC.AiurBackend.Lower IxCC.AiurBackend.Gadgets IxCC.AiurBackend.Backward

/-! ## Fir runs as runs of the language -/

/-- A run of export `i` on exactly its parameters, as `Fir.run` states it, is
the run of the language `Fir.lower`'s refinement is about (`Fir.firRun`). -/
theorem lang_run_of_run {Q : Fir.Program} {i : Nat} {g : Fir.FunId}
    (hexp : Q.exports[i]? = some g) {ns : List Nat} {k : Nat} {w : Fir.Val}
    (hrun : Fir.run Q k g (ns.map fun n => .lit (.nat n)) = .ok w) :
    Sem.Lang.run Q (i, ns) k = .ok w := by
  have hcall := hrun
  rw [Fir.run_eq, Fir.evalCall_eq] at hcall
  cases hfd : Q.fun? g with
  | none => simp [hfd, Sem.Result.ofOption, Sem.Result.bind] at hcall
  | some fd =>
    simp only [hfd, Sem.Result.ofOption, Sem.Result.bind_ok] at hcall
    have hlen : ns.length = fd.params.length := by
      by_cases hl : ns.length = fd.params.length
      · exact hl
      · simp [Fir.callFun, hl] at hcall
    rw [Fir.lang_run]
    unfold Fir.firRun
    simp only [hexp, hfd]
    rw [Sem.entryRun_exact hlen k]
    exact hrun

/-! ## Source progress on one input -/

/-- **The source is stuck at no clock on input `i`.** The shape of the
source-progress lane's `NeverStuck` (`IxCC.Correct.NeverStuck`, safety
strength), stated on the checked source itself rather than on the source
viewed at the native roots' readback types: a viewed run is stuck where this
one is, or where the view rejects its result, so that predicate implies this
one. It is a hypothesis here; no instance is proved in this package. -/
def NeverStuck (s : CheckedProgram) (i : Nat × List Nat) : Prop :=
  ∀ k, Sem.Lang.run s i k ≠ .stuck

/-! ## From a Fir value to the source -/

/-- **A value of the front half's Fir program, read at the source.** On a
covered input, a value `Fir.run` returns for an export is the observation of a
value SrcEval returns for the root, or SrcEval is stuck. -/
theorem source_of_fir_run {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {i : Nat} {g : Fir.FunId} (hexp : f.fir.exports[i]? = some g)
    {ns : List Nat} {k : Nat} {w : Fir.Val}
    (hrun : Fir.run f.fir k g (ns.map fun n => .lit (.nat n)) = .ok w)
    (hcov : f.Covered c (i, ns)) :
    (∃ k' v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, ns) k' = .ok v ∧
        Sem.Lang.ObsEq (S := CheckedProgram) (T := Fir.Program) v w) ∨
      ∃ k', Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, ns) k' = .stuck :=
  (Recheck.front_fir hf).backward hcov (lang_run_of_run hexp hrun)

/-- `source_of_fir_run` where the source is stuck at no clock: the value is
the source's. -/
theorem source_of_fir_run_of_neverStuck {cfg : Recheck.Config} {P : Src.Program}
    {c : Recheck.Cert} {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {i : Nat} {g : Fir.FunId} (hexp : f.fir.exports[i]? = some g)
    {ns : List Nat} {k : Nat} {w : Fir.Val}
    (hrun : Fir.run f.fir k g (ns.map fun n => .lit (.nat n)) = .ok w)
    (hcov : f.Covered c (i, ns)) (hp : NeverStuck ⟨f.src, f.checked⟩ (i, ns)) :
    ∃ k' v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, ns) k' = .ok v ∧
      Sem.Lang.ObsEq (S := CheckedProgram) (T := Fir.Program) v w := by
  rcases source_of_fir_run hf hexp hrun hcov with h | ⟨k', hk'⟩
  · exact h
  · exact absurd hk' (hp k')

section Entry

variable {F : Type} [Field F] [DecidableEq F]

/-- **An accepted run of a lowered entry, read at the source (with the
stuck-source disjunct).** For the Fir program the front half makes
(`Recheck.runFir`), every derivation of the lowered entry `Prog::main<i>` on
field arguments decodes them as `Nat`s below `2^56`, and its result represents
a Fir value `w` that, on a covered input, is the observation of a value
SrcEval returns for root `i` on those `Nat`s, **or SrcEval is stuck on them**. -/
theorem entry_source_backward {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {prog : Aiur.Generic.Program Nat} {world : World F}
    (fc : FieldCompatible F) (lw : LoweredWorld f.fir prog world)
    {i : Nat} {g : Fir.FunId} (hexp : f.fir.exports[i]? = some g)
    {args : List (SourceValue F)} {h' : Heap F} {r : SourceValue F}
    (ev : EvalFn world (qualified (entryName i)) args [] r h') :
    ∃ (ns : List Nat) (w : Fir.Val),
      (∀ n ∈ ns, n < natLimit) ∧
      args = ns.map (fun n => .field (n : F)) ∧
      VR f.fir objQName bytesQName h' w r ∧
      (f.Covered c (i, ns) →
        (∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, ns) k = .ok v ∧
            Sem.Lang.ObsEq (S := CheckedProgram) (T := Fir.Program) v w) ∨
          ∃ k, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, ns) k = .stuck) := by
  obtain ⟨ns, k, w, hns, hargs, hrun, hvr⟩ := entry_backward_sound fc lw hexp ev
  exact ⟨ns, w, hns, hargs, hvr, fun hcov => source_of_fir_run hf hexp hrun hcov⟩

/-- **An accepted run of a lowered entry, read at the source, under source
progress on its input.** As `entry_source_backward`, where the source is stuck
at no clock on the decoded input: the result represents the observation of the
value SrcEval returns. -/
theorem entry_source_sound {cfg : Recheck.Config} {P : Src.Program} {c : Recheck.Cert}
    {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {prog : Aiur.Generic.Program Nat} {world : World F}
    (fc : FieldCompatible F) (lw : LoweredWorld f.fir prog world)
    {i : Nat} {g : Fir.FunId} (hexp : f.fir.exports[i]? = some g)
    {args : List (SourceValue F)} {h' : Heap F} {r : SourceValue F}
    (ev : EvalFn world (qualified (entryName i)) args [] r h')
    (hp : ∀ ns : List Nat, args = ns.map (fun n => .field (n : F)) →
      NeverStuck ⟨f.src, f.checked⟩ (i, ns)) :
    ∃ (ns : List Nat) (w : Fir.Val),
      (∀ n ∈ ns, n < natLimit) ∧
      args = ns.map (fun n => .field (n : F)) ∧
      VR f.fir objQName bytesQName h' w r ∧
      (f.Covered c (i, ns) →
        ∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, ns) k = .ok v ∧
          Sem.Lang.ObsEq (S := CheckedProgram) (T := Fir.Program) v w) := by
  obtain ⟨ns, k, w, hns, hargs, hrun, hvr⟩ := entry_backward_sound fc lw hexp ev
  exact ⟨ns, w, hns, hargs, hvr, fun hcov =>
    source_of_fir_run_of_neverStuck hf hexp hrun hcov (hp ns hargs)⟩

end Entry

/-! ## From accepted circuit rows (Goldilocks) -/

/-- **Accepted circuit rows, read at the source (with the stuck-source
disjunct).** `Backward.lowered_circuit_sound_goldilocks` for the Fir program
the front half makes, composed with `Recheck.front_fir`: rows the grouped,
activated memo checker accepts (at most `2^39`), over the certified depth pass
of the circuits compiled from the lowered module, for the entry `Prog::main<i>`,
decode the arguments as `Nat`s below `2^56` and give a Fir value `w` that the
Aiur result represents and that, on a covered input, is the observation of a
value SrcEval returns for root `i`, **or SrcEval is stuck on that input**. -/
theorem circuit_source_backward_goldilocks {cfg : Recheck.Config} {P : Src.Program}
    {c : Recheck.Cert} {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {prog : Aiur.Generic.Program Nat}
    {moduleProg : Aiur.Modules.Program Aiur.Library.U32.Goldilocks.F}
    {id : String → Except String Nat}
    (prepared : Aiur.Modules.Prepared moduleProg)
    (lw : LoweredWorld f.fir prog prepared.environment.source.world)
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
    {rom : Aiur.WidthROM Aiur.Library.U32.Goldilocks.F} (valid : rom.Valid)
    {args : List (SourceValue Aiur.Library.U32.Goldilocks.F)}
    {result : Aiur.Value Aiur.Library.U32.Goldilocks.F}
    {wires : List (Aiur.WireValue Aiur.Library.U32.Goldilocks.F)}
    {output : Aiur.WireValue Aiur.Library.U32.Goldilocks.F}
    (signed : Aiur.Circuit.Erasure.Signed compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message Aiur.Library.U32.Goldilocks.F}
    (rooted : Aiur.Optimized.Depth.erase dcfg root =
      Aiur.Circuit.Erasure.message compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ dcfg.names)
    {rows : List (Aiur.Circuit.WeightedRow Aiur.Library.U32.Goldilocks.F)}
    (bound : rows.length ≤ 2 ^ 39)
    (checked : plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues compiled.specialized.program.enums wires (Aiur.entryValues args))
    (decoded : output.decode compiled.specialized.program.enums = some result) :
    ∃ (value : SourceValue Aiur.Library.U32.Goldilocks.F) (heap : Heap Aiur.Library.U32.Goldilocks.F)
      (ns : List Nat) (w : Fir.Val),
      (∀ n ∈ ns, n < natLimit) ∧
      args = ns.map (fun n => .field (n : Aiur.Library.U32.Goldilocks.F)) ∧
      VR f.fir objQName bytesQName heap w value ∧
      Aiur.Represents ((Aiur.Circuit.Erasure.typedROM compiled.circuit.system rom).decode
        compiled.specialized.program.enums) heap value result ∧
      (f.Covered c (i, ns) →
        (∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, ns) k = .ok v ∧
            Sem.Lang.ObsEq (S := CheckedProgram) (T := Fir.Program) v w) ∨
          ∃ k, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, ns) k = .stuck) := by
  obtain ⟨value, heap, ns, k, w, hns, hargs, hrun, hvr, hrep⟩ :=
    lowered_circuit_sound_goldilocks prepared lw compiled physical certified bits plan activated
      selected hname hexp valid signed rooted outside bound checked arguments decoded
  exact ⟨value, heap, ns, w, hns, hargs, hvr, hrep,
    fun hcov => source_of_fir_run hf hexp hrun hcov⟩

/-- **Accepted circuit rows, read at the source, under source progress on the
input.** As `circuit_source_backward_goldilocks`, where the source is stuck at
no clock on the decoded input. -/
theorem circuit_source_sound_goldilocks {cfg : Recheck.Config} {P : Src.Program}
    {c : Recheck.Cert} {f : Recheck.FrontFir} (hf : Recheck.runFir cfg P c = .ok f)
    {prog : Aiur.Generic.Program Nat}
    {moduleProg : Aiur.Modules.Program Aiur.Library.U32.Goldilocks.F}
    {id : String → Except String Nat}
    (prepared : Aiur.Modules.Prepared moduleProg)
    (lw : LoweredWorld f.fir prog prepared.environment.source.world)
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
    {rom : Aiur.WidthROM Aiur.Library.U32.Goldilocks.F} (valid : rom.Valid)
    {args : List (SourceValue Aiur.Library.U32.Goldilocks.F)}
    {result : Aiur.Value Aiur.Library.U32.Goldilocks.F}
    {wires : List (Aiur.WireValue Aiur.Library.U32.Goldilocks.F)}
    {output : Aiur.WireValue Aiur.Library.U32.Goldilocks.F}
    (signed : Aiur.Circuit.Erasure.Signed compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    {root : Aiur.Circuit.Message Aiur.Library.U32.Goldilocks.F}
    (rooted : Aiur.Optimized.Depth.erase dcfg root =
      Aiur.Circuit.Erasure.message compiled.circuit.system ⟨entry.resolved.name, wires, output⟩)
    (outside : root.channel ∉ dcfg.names)
    {rows : List (Aiur.Circuit.WeightedRow Aiur.Library.U32.Goldilocks.F)}
    (bound : rows.length ≤ 2 ^ 39)
    (checked : plan.checkMemo (Aiur.Circuit.Erasure.rawROM rom) root rows = .ok ())
    (arguments : Aiur.DecodesValues compiled.specialized.program.enums wires (Aiur.entryValues args))
    (decoded : output.decode compiled.specialized.program.enums = some result)
    (hp : ∀ ns : List Nat,
      args = ns.map (fun n => .field (n : Aiur.Library.U32.Goldilocks.F)) →
      NeverStuck ⟨f.src, f.checked⟩ (i, ns)) :
    ∃ (value : SourceValue Aiur.Library.U32.Goldilocks.F) (heap : Heap Aiur.Library.U32.Goldilocks.F)
      (ns : List Nat) (w : Fir.Val),
      (∀ n ∈ ns, n < natLimit) ∧
      args = ns.map (fun n => .field (n : Aiur.Library.U32.Goldilocks.F)) ∧
      VR f.fir objQName bytesQName heap w value ∧
      Aiur.Represents ((Aiur.Circuit.Erasure.typedROM compiled.circuit.system rom).decode
        compiled.specialized.program.enums) heap value result ∧
      (f.Covered c (i, ns) →
        ∃ k v, Sem.Lang.run (⟨f.src, f.checked⟩ : CheckedProgram) (i, ns) k = .ok v ∧
          Sem.Lang.ObsEq (S := CheckedProgram) (T := Fir.Program) v w) := by
  obtain ⟨value, heap, ns, k, w, hns, hargs, hrun, hvr, hrep⟩ :=
    lowered_circuit_sound_goldilocks prepared lw compiled physical certified bits plan activated
      selected hname hexp valid signed rooted outside bound checked arguments decoded
  exact ⟨value, heap, ns, w, hns, hargs, hvr, hrep, fun hcov =>
    source_of_fir_run_of_neverStuck hf hexp hrun hcov (hp ns hargs)⟩

end IxCC.AiurBackend.Compose
