import Aiur.Correctness
import Aiur.Completeness
import Aiur.MemoCompleteness
import Aiur.MemoSoundness
import Aiur.MemoryCorrectness
import Aiur.CheckerCorrectness
import Aiur.Generic
import Aiur.Modules
import Aiur.Optimized
import Aiur.Optimized.Depth
import Aiur.Optimized.Observed
import Aiur.HeapMono
import Aiur.StepLemmas
import Aiur.Library.Carry
import Aiur.Library.U8Facts
import Aiur.Library.U32.Correctness
import Aiur.Library.U32.Goldilocks
import Aiur.Library.U64.Correctness
import Aiur.Library.U64.Goldilocks
import Aiur.Library.List.Correctness
import Aiur.Library.Bytes.Correctness
import Aiur.Library.RBTreeMap.Correctness
import Aiur.Library.IxVMRep
import Aiur.Library.Blake3.Correctness
import Aiur.Library.Blake3.Goldilocks

/-!
# Frozen Certification Audit for Aiur

This module freezes the type signatures and audits the axiom footprints of all
top-level compiler, checker, physical/grouped/activated backend, depth-pass
(memo-cycle soundness), and standard library (`Carry`, `U8`, `U32`, `U64`,
`Blake3`, `Goldilocks`) correctness theorems in `Aiur`.

Every theorem audited here depends strictly on a subset of the standard Lean
foundational axioms `[propext, Classical.choice, Quot.sound]`, with zero
`sorryAx` and zero custom or `bv_decide` axioms. The `axiom_sweep` executable
(`Examples/AxiomSweep.lean`, run in CI) checks the same of every declaration in
the package.

## What the audited theorems do not cover

The backend theorems (`Modules.Prepared.grouped_activated_heap_sound` and its
relatives in `Aiur.Optimized.EndToEnd`) assume a *finite* derivation over the
compiled circuits (`Grouping.Plan.ActivatedDerives`), plus `rom.Valid`,
`Erasure.Signed` and `Plan.WellFormedActivation`. A STARK proof does not supply
that derivation. It gives at most rows that satisfy their constraints with
balanced LogUp lookups, which `checkMemo_sound` turns into a
`Circuit.MemoDerivation`; that memo graph may be cyclic (a provided row
`loop(0) = 42` balances `fn loop(x) { loop(x) }`). `memo_acyclic_sound` needs
it acyclic, i.e. every proved call terminating. The frozen statements that
assume it are printed with `pp.proofs true`, so they name the memo graph that
must be acyclic (`Classical.choice (… checkMemo_sound checked)`) rather than an
elided `⋯`.

Section 3a closes that gap for circuits compiled with the depth pass
(`Optimized.Depth`, Track A). `Modules.Prepared.depth_grouped_activated_heap_sound`
(and `…_goldilocks`) start from acceptance of `Grouping.Plan.checkMemo`, the memo
checker over the grouped, activated plan the prover commits to, built over the
certified depth pass of the physical circuits (`Depth.Certified`), with at most
`2^39` rows. Acyclicity is proved, not assumed: every memo graph over a certified
depth system with that many rows is acyclic (`Depth.acyclic`), given a field
condition that Goldilocks meets for `k = 24` (`Depth.goldilocks_characteristic`).
Both side conditions are decidable: the exporter already checks
`Plan.WellFormedActivation`, and must check `Depth.Certified` once it emits the
depth pass (Track A3). Until then, deployed artifacts are covered only by the
derivation-assuming theorems.

Section 3b strengthens the headlines to observed derivations
(`Generic.SourceSemantics.ObsFn`: the source semantics with every call recorded,
inline calls included). They add that every argument of every recorded call is
represented in the trace's decoded ROM relative to the heap at the call
(`CallsInROM`), so data a call received, such as a byte stream passed to the
inline `Blake3::hash`, can be read off the memory table.
`ModulesArtifact.grouped_activated_heap_sound_observed` is the assumption-based
form; `Modules.Prepared.depth_grouped_activated_heap_sound_observed` needs no
derivation.

Trusted and unproved: the Rust lowering of the exported artifact into
multi-stark circuits (CALL, ROM and memory-segment channel tags, activation
times multiplicity, trace-shard segment boundaries, fixed tables and claim
encoding), including that an accepting proof yields rows `Plan.checkMemo`
accepts and that the verifiers, in Rust and in circuit, enforce the `2^39` row
bound over the whole batch; multi-stark's STARK and FRI soundness; the
`aiur⟦ … ⟧` and `aiur_library%` elaborators; and the artifact exporter. The library
`Correctness` theorems prove hand-written Lean models of the library functions
(their byte and limb arithmetic) against Lean specifications such as
`Blake3.digest`. No theorem evaluates the library's Aiur source, so they are
not proofs about the Aiur library functions, nor about the IxVM or MultiStark
programs that call them.
-/

namespace Aiur.Audit

/-! ### 1. Core Compiler, Memory Realization, and Checker Theorems -/

/--
info: @derivation_sound : ∀ {F : Type} {rom : WireROM F} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F}
  {system : Circuit.System F},
  Circuit.compile program = Except.ok system →
    ∀ {message : Circuit.Message F} (derivation : Circuit.Derivation system rom message),
      Circuit.Message.Evaluates program rom message
-/
#guard_msgs in
#check @Aiur.derivation_sound
/-- info: 'Aiur.derivation_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.derivation_sound

/--
info: @compiler_sound : ∀ {F : Type} {rom : WireROM F} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F}
  {system : Circuit.System F},
  Circuit.compile program = Except.ok system →
    ∀ {name : String} {args : List (WireValue F)} {result : WireValue F},
      Circuit.CircuitEvaluates system rom name args result →
        ∀ {values : List (Value F)} {value : Value F},
          DecodesValues program.enums args values →
            WireValue.decode program.enums result = some value →
              ROMEvalCall (WireROM.decode program.enums rom) program name values value
-/
#guard_msgs in
#check @Aiur.compiler_sound
/-- info: 'Aiur.compiler_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.compiler_sound

/--
info: @evaluation_complete : ∀ {F : Type} {rom : WireROM F} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F}
  {system : Circuit.System F},
  Circuit.compile program = Except.ok system →
    ∀ {name : String} {args : List (Value F)} {result : Value F},
      ROMEvalCall (WireROM.decode program.enums rom) program name args result →
        Circuit.EncodedEvaluates program.enums system rom name args result
-/
#guard_msgs in
#check @Aiur.evaluation_complete
/-- info: 'Aiur.evaluation_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.evaluation_complete

/--
info: @compiler_correct : ∀ {F : Type} {rom : WireROM F} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F}
  {system : Circuit.System F},
  Circuit.compile program = Except.ok system →
    ∀ {name : String} {args : List (Value F)} {result : Value F},
      ROMEvalCall (WireROM.decode program.enums rom) program name args result ↔
        Circuit.EncodedEvaluates program.enums system rom name args result
-/
#guard_msgs in
#check @Aiur.compiler_correct
/-- info: 'Aiur.compiler_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.compiler_correct

/--
info: @memo_acyclic_sound : ∀ {F : Type} {rom : WireROM F} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F}
  {system : Circuit.System F},
  Circuit.compile program = Except.ok system →
    ∀ {message : Circuit.Message F} (graph : Circuit.MemoDerivation system rom message),
      graph.Acyclic → Circuit.Message.Evaluates program rom message
-/
#guard_msgs in
#check @Aiur.memo_acyclic_sound
/-- info: 'Aiur.memo_acyclic_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.memo_acyclic_sound

/--
info: @compiler_heap_complete : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F}
  {system : Circuit.System F},
  Circuit.compile program = Except.ok system →
    ∀ {name : String} {args : List (SourceValue F)} {value : SourceValue F} {heap : Heap F},
      checkEntry program name = Except.ok () →
        EvalFn program name args [] value heap →
          ∀ (encode : ℕ → F),
            (∀ (i j : ℕ), i < List.length heap → j < List.length heap → encode i = encode j → i = j) →
              Circuit.EncodedEntryDerives system name (entryValues args) (Value.mapAddress encode value)
-/
#guard_msgs in
#check @Aiur.compiler_heap_complete
/-- info: 'Aiur.compiler_heap_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.compiler_heap_complete

/--
info: @compiler_heap_complete_finite : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] [inst_2 : Fintype F]
  {program : Program F} {system : Circuit.System F},
  Circuit.compile program = Except.ok system →
    ∀ {name : String} {args : List (SourceValue F)} {value : SourceValue F} {heap : Heap F},
      checkEntry program name = Except.ok () →
        EvalFn program name args [] value heap →
          List.length heap ≤ Fintype.card F →
            ∃ encode, Circuit.EncodedEntryDerives system name (entryValues args) (Value.mapAddress encode value)
-/
#guard_msgs in
#check @Aiur.compiler_heap_complete_finite
/-- info: 'Aiur.compiler_heap_complete_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.compiler_heap_complete_finite

/--
info: @compiler_run_complete : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] [inst_2 : Fintype F]
  {program : Program F} {system : Circuit.System F},
  Circuit.compile program = Except.ok system →
    ∀ {name : String} {args : List (SourceValue F)} {fuel : ℕ} {value : SourceValue F} {heap : Heap F}
      {hints : HintProvider F program.enums},
      run program name args fuel hints = Except.ok (value, heap) →
        List.length heap ≤ Fintype.card F →
          ∃ encode, Circuit.EncodedEntryDerives system name (entryValues args) (Value.mapAddress encode value)
-/
#guard_msgs in
#check @Aiur.compiler_run_complete
/-- info: 'Aiur.compiler_run_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.compiler_run_complete

/--
info: @memo_run_complete : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] [inst_2 : Fintype F] {program : Program F}
  {system : Circuit.System F},
  Circuit.compile program = Except.ok system →
    ∀ {name : String} {args : List (SourceValue F)} {fuel : ℕ} {value : SourceValue F} {heap : Heap F}
      {hints : HintProvider F program.enums},
      run program name args fuel hints = Except.ok (value, heap) →
        List.length heap ≤ Fintype.card F →
          ∃ encode, Circuit.EncodedMemoEntryDerives system name (entryValues args) (Value.mapAddress encode value)
-/
#guard_msgs in
#check @Aiur.memo_run_complete
/-- info: 'Aiur.memo_run_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.memo_run_complete

/--
info: @compiler_heap_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F}
  {system : Circuit.System F},
  Circuit.compile program = Except.ok system →
    ∀ {rom : WireROM F},
      rom.Valid →
        ∀ {name : String} {args : List (SourceValue F)} {result : Value F},
          checkEntry program name = Except.ok () →
            ∀ {wires : List (WireValue F)} {output : WireValue F},
              Circuit.CircuitEvaluates system rom name wires output →
                DecodesValues program.enums wires (entryValues args) →
                  WireValue.decode program.enums output = some result →
                    ∃ source heap,
                      EvalFn program name args [] source heap ∧
                        Represents (WireROM.decode program.enums rom) heap source result
-/
#guard_msgs in
#check @Aiur.compiler_heap_sound
/-- info: 'Aiur.compiler_heap_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.compiler_heap_sound

/--
info: @compiler_entry_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F}
  {system : Circuit.System F},
  Circuit.compile program = Except.ok system →
    ∀ {name : String} {args : List (SourceValue F)} {result : Value F},
      Circuit.EncodedEntryDerives system name (entryValues args) result →
        result.pointerFree = true → EvalCall program name args (Value.mapAddress (fun x => 0) result)
-/
#guard_msgs in
#check @Aiur.compiler_entry_sound
/-- info: 'Aiur.compiler_entry_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.compiler_entry_sound

/--
info: @memo_acyclic_heap_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F}
  {system : Circuit.System F},
  Circuit.compile program = Except.ok system →
    ∀ {rom : WireROM F},
      rom.Valid →
        ∀ {name : String} {args : List (SourceValue F)} {result : Value F},
          checkEntry program name = Except.ok () →
            ∀ {wires : List (WireValue F)} {output : WireValue F}
              (graph : Circuit.MemoDerivation system rom { channel := name, args := wires, result := output }),
              graph.Acyclic →
                DecodesValues program.enums wires (entryValues args) →
                  WireValue.decode program.enums output = some result →
                    ∃ source heap,
                      EvalFn program name args [] source heap ∧
                        Represents (WireROM.decode program.enums rom) heap source result
-/
#guard_msgs in
#check @Aiur.memo_acyclic_heap_sound
/-- info: 'Aiur.memo_acyclic_heap_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.memo_acyclic_heap_sound

/--
info: @checker_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F}
  {system : Circuit.System F},
  Circuit.compile program = Except.ok system →
    ∀ {rom : WireROM F} {message : Circuit.Message F} {rows : List (Circuit.Row F)},
      system.check rom message rows = Except.ok () → Circuit.Message.Evaluates program rom message
-/
#guard_msgs in
#check @Aiur.checker_sound
/-- info: 'Aiur.checker_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.checker_sound

/--
info: @checker_heap_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F}
  {system : Circuit.System F},
  Circuit.compile program = Except.ok system →
    ∀ {rom : WireROM F} {name : String} {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)}
      {output : WireValue F} {rows : List (Circuit.Row F)},
      system.check rom { channel := name, args := wires, result := output } rows = Except.ok () →
        checkEntry program name = Except.ok () →
          DecodesValues program.enums wires (entryValues args) →
            WireValue.decode program.enums output = some result →
              ∃ source heap,
                EvalFn program name args [] source heap ∧
                  Represents (WireROM.decode program.enums rom) heap source result
-/
#guard_msgs in
#check @Aiur.checker_heap_sound
/-- info: 'Aiur.checker_heap_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.checker_heap_sound

/--
info: @checker_run_complete : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] [inst_2 : Fintype F]
  {program : Program F} {system : Circuit.System F},
  Circuit.compile program = Except.ok system →
    system.WellFormed →
      ∀ {name : String} {args : List (SourceValue F)} {fuel : ℕ} {value : SourceValue F} {heap : Heap F}
        {hints : HintProvider F program.enums},
        run program name args fuel hints = Except.ok (value, heap) →
          List.length heap ≤ Fintype.card F →
            ∃ encode wires output rom rows,
              DecodesValues system.enums wires (entryValues args) ∧
                WireValue.decode system.enums output = some (Value.mapAddress encode value) ∧
                  system.check rom { channel := name, args := wires, result := output } rows = Except.ok ()
-/
#guard_msgs in
#check @Aiur.checker_run_complete
/-- info: 'Aiur.checker_run_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.checker_run_complete

/--
info: @checkerMemo_run_complete : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] [inst_2 : Fintype F]
  {program : Program F} {system : Circuit.System F},
  Circuit.compile program = Except.ok system →
    system.WellFormed →
      ∀ {name : String} {args : List (SourceValue F)} {fuel : ℕ} {value : SourceValue F} {heap : Heap F}
        {hints : HintProvider F program.enums},
        run program name args fuel hints = Except.ok (value, heap) →
          List.length heap ≤ Fintype.card F →
            ∃ encode wires output rom rows,
              DecodesValues system.enums wires (entryValues args) ∧
                WireValue.decode system.enums output = some (Value.mapAddress encode value) ∧
                  system.checkMemo rom { channel := name, args := wires, result := output } rows = Except.ok ()
-/
#guard_msgs in
#check @Aiur.checkerMemo_run_complete
/-- info: 'Aiur.checkerMemo_run_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.checkerMemo_run_complete

/--
info: @checkerMemo_acyclic_heap_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F}
  {system : Circuit.System F},
  Circuit.compile program = Except.ok system →
    ∀ {rom : WireROM F} {name : String} {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)}
      {output : WireValue F} {rows : List (Circuit.WeightedRow F)}
      (checked : system.checkMemo rom { channel := name, args := wires, result := output } rows = Except.ok ()),
      (Classical.choice (Circuit.System.checkMemo_sound checked)).Acyclic →
        checkEntry program name = Except.ok () →
          DecodesValues program.enums wires (entryValues args) →
            WireValue.decode program.enums output = some result →
              ∃ source heap,
                EvalFn program name args [] source heap ∧
                  Represents (WireROM.decode program.enums rom) heap source result
-/
#guard_msgs in
set_option pp.proofs true in
#check @Aiur.checkerMemo_acyclic_heap_sound
/-- info: 'Aiur.checkerMemo_acyclic_heap_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.checkerMemo_acyclic_heap_sound

/-! ### 2. Generic Source Specialization and Inlining Theorems -/

/--
info: @Generic.Specialized.native_entry_iff : ∀ {F : Type} {entries : List String} {name : String}
  {args : List (SourceValue F)} {result : SourceValue F} {heap : Heap F} [inst : Field F] [inst_1 : DecidableEq F]
  {s : Generic.Source F} (q : Generic.Specialized s entries),
  name ∈ entries →
    (Generic.SourceSemantics.EvalFn s.world name args [] result heap ↔ EvalFn q.program name args [] result heap)
-/
#guard_msgs in
#check @Aiur.Generic.Specialized.native_entry_iff
/-- info: 'Aiur.Generic.Specialized.native_entry_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.Specialized.native_entry_iff

/--
info: @Generic.Specialized.native_evalCall_iff : ∀ {F : Type} {entries : List String} {name : String}
  {args : List (SourceValue F)} {result : SourceValue F} [inst : Field F] [inst_1 : DecidableEq F]
  {s : Generic.Source F} (q : Generic.Specialized s entries),
  name ∈ entries → (s.EvalCall name args result ↔ EvalCall q.program name args result)
-/
#guard_msgs in
#check @Aiur.Generic.Specialized.native_evalCall_iff
/-- info: 'Aiur.Generic.Specialized.native_evalCall_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.Specialized.native_evalCall_iff

/--
info: @Generic.Specialized.heap_complete : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {s : Generic.Source F}
  {entries : List String} {name : String} {args : List (SourceValue F)} {value : SourceValue F} {heap : Heap F}
  (q : Generic.Specialized s entries),
  name ∈ entries →
    ∀ {system : Circuit.System F},
      Circuit.compile q.program = Except.ok system →
        Generic.SourceSemantics.EvalFn s.world name args [] value heap →
          ∀ (encode : ℕ → F),
            (∀ (i j : ℕ), i < List.length heap → j < List.length heap → encode i = encode j → i = j) →
              Circuit.EncodedEntryDerives system name (entryValues args) (Value.mapAddress encode value)
-/
#guard_msgs in
#check @Aiur.Generic.Specialized.heap_complete
/-- info: 'Aiur.Generic.Specialized.heap_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.Specialized.heap_complete

/--
info: @Generic.Specialized.heap_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {s : Generic.Source F}
  {entries : List String} {name : String} (q : Generic.Specialized s entries),
  name ∈ entries →
    ∀ {system : Circuit.System F},
      Circuit.compile q.program = Except.ok system →
        ∀ {rom : WireROM F},
          rom.Valid →
            ∀ {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F},
              Circuit.CircuitEvaluates system rom name wires output →
                DecodesValues q.program.enums wires (entryValues args) →
                  WireValue.decode q.program.enums output = some result →
                    ∃ value heap,
                      Generic.SourceSemantics.EvalFn s.world name args [] value heap ∧
                        Represents (WireROM.decode q.program.enums rom) heap value result
-/
#guard_msgs in
#check @Aiur.Generic.Specialized.heap_sound
/-- info: 'Aiur.Generic.Specialized.heap_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.Specialized.heap_sound

/--
info: @Generic.Specialized.memo_acyclic_heap_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {s : Generic.Source F} {entries : List String} {name : String} (q : Generic.Specialized s entries),
  name ∈ entries →
    ∀ {system : Circuit.System F},
      Circuit.compile q.program = Except.ok system →
        ∀ {rom : WireROM F},
          rom.Valid →
            ∀ {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
              (graph : Circuit.MemoDerivation system rom { channel := name, args := wires, result := output }),
              graph.Acyclic →
                DecodesValues q.program.enums wires (entryValues args) →
                  WireValue.decode q.program.enums output = some result →
                    ∃ value heap,
                      Generic.SourceSemantics.EvalFn s.world name args [] value heap ∧
                        Represents (WireROM.decode q.program.enums rom) heap value result
-/
#guard_msgs in
#check @Aiur.Generic.Specialized.memo_acyclic_heap_sound
/-- info: 'Aiur.Generic.Specialized.memo_acyclic_heap_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.Specialized.memo_acyclic_heap_sound

/--
info: @Generic.Specialized.checker_heap_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {s : Generic.Source F}
  {entries : List String} {name : String} (q : Generic.Specialized s entries),
  name ∈ entries →
    ∀ {system : Circuit.System F},
      Circuit.compile q.program = Except.ok system →
        ∀ {rom : WireROM F} {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)}
          {output : WireValue F} {rows : List (Circuit.Row F)},
          system.check rom { channel := name, args := wires, result := output } rows = Except.ok () →
            DecodesValues q.program.enums wires (entryValues args) →
              WireValue.decode q.program.enums output = some result →
                ∃ value heap,
                  Generic.SourceSemantics.EvalFn s.world name args [] value heap ∧
                    Represents (WireROM.decode q.program.enums rom) heap value result
-/
#guard_msgs in
#check @Aiur.Generic.Specialized.checker_heap_sound
/-- info: 'Aiur.Generic.Specialized.checker_heap_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.Specialized.checker_heap_sound

/--
info: @Generic.Specialized.checkerMemo_acyclic_heap_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {s : Generic.Source F} {entries : List String} {name : String} (q : Generic.Specialized s entries),
  name ∈ entries →
    ∀ {system : Circuit.System F},
      Circuit.compile q.program = Except.ok system →
        ∀ {rom : WireROM F} {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)}
          {output : WireValue F} {rows : List (Circuit.WeightedRow F)}
          (checked : system.checkMemo rom { channel := name, args := wires, result := output } rows = Except.ok ()),
          (Classical.choice (Circuit.System.checkMemo_sound checked)).Acyclic →
            DecodesValues q.program.enums wires (entryValues args) →
              WireValue.decode q.program.enums output = some result →
                ∃ value heap,
                  Generic.SourceSemantics.EvalFn s.world name args [] value heap ∧
                    Represents (WireROM.decode q.program.enums rom) heap value result
-/
#guard_msgs in
set_option pp.proofs true in
#check @Aiur.Generic.Specialized.checkerMemo_acyclic_heap_sound
/-- info: 'Aiur.Generic.Specialized.checkerMemo_acyclic_heap_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.Specialized.checkerMemo_acyclic_heap_sound

/--
info: @Generic.Compiled.native_entry_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {s : Generic.Source F}
  {entries : List String} {name : String} {args : List (SourceValue F)} {result : SourceValue F} {heap : Heap F}
  {q : Generic.Specialized s entries} (c : Generic.Compiled q),
  name ∈ entries →
    (Generic.SourceSemantics.EvalFn s.world name args [] result heap ↔ EvalFn c.program name args [] result heap)
-/
#guard_msgs in
#check @Aiur.Generic.Compiled.native_entry_iff
/-- info: 'Aiur.Generic.Compiled.native_entry_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.Compiled.native_entry_iff

/--
info: @Generic.Compiled.heap_complete : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {s : Generic.Source F}
  {entries : List String} {name : String} {args : List (SourceValue F)} {value : SourceValue F} {heap : Heap F}
  {q : Generic.Specialized s entries} (c : Generic.Compiled q),
  name ∈ entries →
    Generic.SourceSemantics.EvalFn s.world name args [] value heap →
      ∀ (encode : ℕ → F),
        (∀ (i j : ℕ), i < List.length heap → j < List.length heap → encode i = encode j → i = j) →
          Circuit.EncodedEntryDerives c.system name (entryValues args) (Value.mapAddress encode value)
-/
#guard_msgs in
#check @Aiur.Generic.Compiled.heap_complete
/-- info: 'Aiur.Generic.Compiled.heap_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.Compiled.heap_complete

/--
info: @Generic.Compiled.heap_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {s : Generic.Source F}
  {entries : List String} {name : String} {q : Generic.Specialized s entries} (c : Generic.Compiled q),
  name ∈ entries →
    ∀ {rom : WireROM F},
      rom.Valid →
        ∀ {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F},
          Circuit.CircuitEvaluates c.system rom name wires output →
            DecodesValues q.program.enums wires (entryValues args) →
              WireValue.decode q.program.enums output = some result →
                ∃ value heap,
                  Generic.SourceSemantics.EvalFn s.world name args [] value heap ∧
                    Represents (WireROM.decode q.program.enums rom) heap value result
-/
#guard_msgs in
#check @Aiur.Generic.Compiled.heap_sound
/-- info: 'Aiur.Generic.Compiled.heap_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.Compiled.heap_sound

/--
info: @Generic.Compiled.checker_heap_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {s : Generic.Source F}
  {entries : List String} {name : String} {q : Generic.Specialized s entries} (c : Generic.Compiled q),
  name ∈ entries →
    ∀ {rom : WireROM F} {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)}
      {output : WireValue F} {rows : List (Circuit.Row F)},
      c.system.check rom { channel := name, args := wires, result := output } rows = Except.ok () →
        DecodesValues q.program.enums wires (entryValues args) →
          WireValue.decode q.program.enums output = some result →
            ∃ value heap,
              Generic.SourceSemantics.EvalFn s.world name args [] value heap ∧
                Represents (WireROM.decode q.program.enums rom) heap value result
-/
#guard_msgs in
#check @Aiur.Generic.Compiled.checker_heap_sound
/-- info: 'Aiur.Generic.Compiled.checker_heap_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.Compiled.checker_heap_sound

/--
info: @Generic.Compiled.checkerMemo_acyclic_heap_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {s : Generic.Source F} {entries : List String} {name : String} {q : Generic.Specialized s entries}
  (c : Generic.Compiled q),
  name ∈ entries →
    ∀ {rom : WireROM F} {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)}
      {output : WireValue F} {rows : List (Circuit.WeightedRow F)}
      (checked : c.system.checkMemo rom { channel := name, args := wires, result := output } rows = Except.ok ()),
      (Classical.choice (Circuit.System.checkMemo_sound checked)).Acyclic →
        DecodesValues q.program.enums wires (entryValues args) →
          WireValue.decode q.program.enums output = some result →
            ∃ value heap,
              Generic.SourceSemantics.EvalFn s.world name args [] value heap ∧
                Represents (WireROM.decode q.program.enums rom) heap value result
-/
#guard_msgs in
set_option pp.proofs true in
#check @Aiur.Generic.Compiled.checkerMemo_acyclic_heap_sound
/-- info: 'Aiur.Generic.Compiled.checkerMemo_acyclic_heap_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.Compiled.checkerMemo_acyclic_heap_sound

/--
info: @Generic.Compiled.check_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {s : Generic.Source F}
  {entries : List String} {name : String} {q : Generic.Specialized s entries} (c : Generic.Compiled q) {rom : WireROM F}
  {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
  {rows : List (Circuit.Row F)},
  c.check rom { channel := name, args := wires, result := output } rows = Except.ok () →
    DecodesValues q.program.enums wires (entryValues args) →
      WireValue.decode q.program.enums output = some result →
        ∃ value heap, s.EvalCall name args value ∧ Represents (WireROM.decode q.program.enums rom) heap value result
-/
#guard_msgs in
#check @Aiur.Generic.Compiled.check_sound
/-- info: 'Aiur.Generic.Compiled.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.Compiled.check_sound

/--
info: @Generic.Compiled.checkMemo_acyclic_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {s : Generic.Source F} {entries : List String} {name : String} {q : Generic.Specialized s entries}
  (c : Generic.Compiled q) {rom : WireROM F} {args : List (SourceValue F)} {result : Value F}
  {wires : List (WireValue F)} {output : WireValue F} {rows : List (Circuit.WeightedRow F)}
  (checked : c.checkMemo rom { channel := name, args := wires, result := output } rows = Except.ok ()),
  (Classical.choice (Circuit.System.checkMemo_sound ((Generic.Compiled.checkMemo_iff c).mp checked).right)).Acyclic →
    DecodesValues q.program.enums wires (entryValues args) →
      WireValue.decode q.program.enums output = some result →
        ∃ value heap, s.EvalCall name args value ∧ Represents (WireROM.decode q.program.enums rom) heap value result
-/
#guard_msgs in
set_option pp.proofs true in
#check @Aiur.Generic.Compiled.checkMemo_acyclic_sound
/-- info: 'Aiur.Generic.Compiled.checkMemo_acyclic_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.Compiled.checkMemo_acyclic_sound

/-! ### 3. Optimized Backend, Physical Type Erasure, Grouping, Activation, and End-to-End Theorems -/

/--
info: @Optimized.GenericArtifact.native_entry_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {source : Generic.Source F} {entries : List String} {args : List (SourceValue F)} {value : SourceValue F}
  {heap : Heap F} {prepared : Generic.Specialized source entries} (compiled : Optimized.GenericArtifact prepared)
  {name : String},
  name ∈ entries →
    (Generic.SourceSemantics.EvalFn source.world name args [] value heap ↔
      EvalFn compiled.inlined.program name args [] value heap)
-/
#guard_msgs in
#check @Aiur.Optimized.GenericArtifact.native_entry_iff
/-- info: 'Aiur.Optimized.GenericArtifact.native_entry_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.GenericArtifact.native_entry_iff

/--
info: @Optimized.GenericArtifact.heap_complete : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {source : Generic.Source F} {entries : List String} {prepared : Generic.Specialized source entries}
  (compiled : Optimized.GenericArtifact prepared) {name : String},
  name ∈ entries →
    ∀ {args : List (SourceValue F)} {value : SourceValue F} {heap : Heap F},
      Generic.SourceSemantics.EvalFn source.world name args [] value heap →
        ∀ (encode : ℕ → F),
          (∀ (i j : ℕ), i < List.length heap → j < List.length heap → encode i = encode j → i = j) →
            Circuit.EncodedEntryDerives compiled.system name (entryValues args) (Value.mapAddress encode value)
-/
#guard_msgs in
#check @Aiur.Optimized.GenericArtifact.heap_complete
/-- info: 'Aiur.Optimized.GenericArtifact.heap_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.GenericArtifact.heap_complete

/--
info: @Optimized.GenericArtifact.heap_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {source : Generic.Source F} {entries : List String} {prepared : Generic.Specialized source entries}
  (compiled : Optimized.GenericArtifact prepared) {name : String},
  name ∈ entries →
    ∀ {rom : WireROM F},
      rom.Valid →
        ∀ {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F},
          Circuit.CircuitEvaluates compiled.system rom name wires output →
            DecodesValues prepared.program.enums wires (entryValues args) →
              WireValue.decode prepared.program.enums output = some result →
                ∃ value heap,
                  Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
                    Represents (WireROM.decode prepared.program.enums rom) heap value result
-/
#guard_msgs in
#check @Aiur.Optimized.GenericArtifact.heap_sound
/-- info: 'Aiur.Optimized.GenericArtifact.heap_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.GenericArtifact.heap_sound

/--
info: @Optimized.GenericArtifact.checker_heap_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {source : Generic.Source F} {entries : List String} {prepared : Generic.Specialized source entries}
  (compiled : Optimized.GenericArtifact prepared) {name : String},
  name ∈ entries →
    ∀ {rom : WireROM F} {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)}
      {output : WireValue F} {rows : List (Circuit.Row F)},
      compiled.system.check rom { channel := name, args := wires, result := output } rows = Except.ok () →
        DecodesValues prepared.program.enums wires (entryValues args) →
          WireValue.decode prepared.program.enums output = some result →
            ∃ value heap,
              Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
                Represents (WireROM.decode prepared.program.enums rom) heap value result
-/
#guard_msgs in
#check @Aiur.Optimized.GenericArtifact.checker_heap_sound
/-- info: 'Aiur.Optimized.GenericArtifact.checker_heap_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.GenericArtifact.checker_heap_sound

/--
info: @Optimized.GenericArtifact.checkerMemo_acyclic_heap_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {source : Generic.Source F} {entries : List String} {prepared : Generic.Specialized source entries}
  (compiled : Optimized.GenericArtifact prepared) {name : String},
  name ∈ entries →
    ∀ {rom : WireROM F} {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)}
      {output : WireValue F} {rows : List (Circuit.WeightedRow F)}
      (checked :
        compiled.system.checkMemo rom { channel := name, args := wires, result := output } rows = Except.ok ()),
      (Classical.choice (Circuit.System.checkMemo_sound checked)).Acyclic →
        DecodesValues prepared.program.enums wires (entryValues args) →
          WireValue.decode prepared.program.enums output = some result →
            ∃ value heap,
              Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
                Represents (WireROM.decode prepared.program.enums rom) heap value result
-/
#guard_msgs in
set_option pp.proofs true in
#check @Aiur.Optimized.GenericArtifact.checkerMemo_acyclic_heap_sound
/--
info: 'Aiur.Optimized.GenericArtifact.checkerMemo_acyclic_heap_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Aiur.Optimized.GenericArtifact.checkerMemo_acyclic_heap_sound

/--
info: @Optimized.GenericArtifact.check_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {source : Generic.Source F} {entries : List String} {prepared : Generic.Specialized source entries}
  (compiled : Optimized.GenericArtifact prepared) {name : String} {rom : WireROM F} {args : List (SourceValue F)}
  {result : Value F} {wires : List (WireValue F)} {output : WireValue F} {rows : List (Circuit.Row F)},
  compiled.artifact.check rom { channel := name, args := wires, result := output } rows = Except.ok () →
    DecodesValues prepared.program.enums wires (entryValues args) →
      WireValue.decode prepared.program.enums output = some result →
        ∃ value heap,
          source.EvalCall name args value ∧ Represents (WireROM.decode prepared.program.enums rom) heap value result
-/
#guard_msgs in
#check @Aiur.Optimized.GenericArtifact.check_sound
/-- info: 'Aiur.Optimized.GenericArtifact.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.GenericArtifact.check_sound

/--
info: @Optimized.ModulesArtifact.check_complete : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {name : String}
  {args : List (SourceValue F)} {value : SourceValue F} {heap : Heap F} [inst_2 : Fintype F]
  {program : Modules.Program F} {prepared : Modules.Prepared program} (compiled : Optimized.ModulesArtifact prepared),
  prepared.EvalFn name args value heap →
    List.length heap ≤ Fintype.card F →
      ∃ encode wires output rom rows,
        DecodesValues compiled.circuit.system.enums wires (entryValues args) ∧
          WireValue.decode compiled.circuit.system.enums output = some (Value.mapAddress encode value) ∧
            compiled.check rom name wires output rows = Except.ok ()
-/
#guard_msgs in
#check @Aiur.Optimized.ModulesArtifact.check_complete
/-- info: 'Aiur.Optimized.ModulesArtifact.check_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.ModulesArtifact.check_complete

/--
info: @Optimized.ModulesArtifact.checkMemo_complete : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {name : String}
  {args : List (SourceValue F)} {value : SourceValue F} {heap : Heap F} [inst_2 : Fintype F]
  {program : Modules.Program F} {prepared : Modules.Prepared program} (compiled : Optimized.ModulesArtifact prepared),
  prepared.EvalFn name args value heap →
    List.length heap ≤ Fintype.card F →
      ∃ encode wires output rom rows,
        DecodesValues compiled.circuit.system.enums wires (entryValues args) ∧
          WireValue.decode compiled.circuit.system.enums output = some (Value.mapAddress encode value) ∧
            compiled.checkMemo rom name wires output rows = Except.ok ()
-/
#guard_msgs in
#check @Aiur.Optimized.ModulesArtifact.checkMemo_complete
/-- info: 'Aiur.Optimized.ModulesArtifact.checkMemo_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.ModulesArtifact.checkMemo_complete

/--
info: @Optimized.ModulesArtifact.check_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {name : String}
  {program : Modules.Program F} {prepared : Modules.Prepared program} (compiled : Optimized.ModulesArtifact prepared)
  {rom : WireROM F} {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F}
  {rows : List (Circuit.Row F)},
  compiled.check rom name wires output rows = Except.ok () →
    DecodesValues compiled.specialized.program.enums wires (entryValues args) →
      WireValue.decode compiled.specialized.program.enums output = some result →
        ∃ value heap,
          prepared.EvalCall name args value ∧
            Represents (WireROM.decode compiled.specialized.program.enums rom) heap value result
-/
#guard_msgs in
#check @Aiur.Optimized.ModulesArtifact.check_sound
/-- info: 'Aiur.Optimized.ModulesArtifact.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.ModulesArtifact.check_sound

/--
info: @Optimized.ModulesArtifact.checkMemo_acyclic_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {name : String} {program : Modules.Program F} {prepared : Modules.Prepared program}
  (compiled : Optimized.ModulesArtifact prepared)
  {entry : Modules.Selection program prepared.environment.assembly.instances}
  (selected : prepared.find? name = some entry) {rom : WireROM F} {args : List (SourceValue F)} {result : Value F}
  {wires : List (WireValue F)} {output : WireValue F} {rows : List (Circuit.WeightedRow F)}
  (checked : compiled.checkMemo rom name wires output rows = Except.ok ()),
  (Classical.choice
        (Circuit.System.checkMemo_sound (Optimized.ModulesArtifact.checkMemo_rows compiled selected checked))).Acyclic →
    DecodesValues compiled.specialized.program.enums wires (entryValues args) →
      WireValue.decode compiled.specialized.program.enums output = some result →
        ∃ value heap,
          prepared.EvalCall name args value ∧
            Represents (WireROM.decode compiled.specialized.program.enums rom) heap value result
-/
#guard_msgs in
set_option pp.proofs true in
#check @Aiur.Optimized.ModulesArtifact.checkMemo_acyclic_sound
/-- info: 'Aiur.Optimized.ModulesArtifact.checkMemo_acyclic_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.ModulesArtifact.checkMemo_acyclic_sound

/--
info: @Optimized.ModulesArtifact.physical_heap_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {program : Modules.Program F} {prepared : Modules.Prepared program} (compiled : Optimized.ModulesArtifact prepared)
  (physical : Optimized.Physical.Prepared compiled.circuit.artifact) {external : String}
  {entry : Modules.Selection program prepared.environment.assembly.instances},
  prepared.find? external = some entry →
    ∀ {rom : WidthROM F},
      rom.Valid →
        ∀ {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F},
          Circuit.Erasure.Signed compiled.circuit.system
              { channel := entry.resolved.name, args := wires, result := output } →
            Circuit.Derives physical.system (Circuit.Erasure.rawROM rom)
                (Circuit.Erasure.message compiled.circuit.system
                  { channel := entry.resolved.name, args := wires, result := output }) →
              DecodesValues compiled.specialized.program.enums wires (entryValues args) →
                WireValue.decode compiled.specialized.program.enums output = some result →
                  ∃ value heap,
                    prepared.EvalFn external args value heap ∧
                      Represents
                        (WireROM.decode compiled.specialized.program.enums
                          (Circuit.Erasure.typedROM compiled.circuit.system rom))
                        heap value result
-/
#guard_msgs in
#check @Aiur.Optimized.ModulesArtifact.physical_heap_sound
/-- info: 'Aiur.Optimized.ModulesArtifact.physical_heap_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.ModulesArtifact.physical_heap_sound

/--
info: @Optimized.ModulesArtifact.grouped_heap_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {id : String → Except String ℕ} {program : Modules.Program F} {prepared : Modules.Prepared program}
  (compiled : Optimized.ModulesArtifact prepared) (physical : Optimized.Physical.Prepared compiled.circuit.artifact)
  (plan : Optimized.Grouping.Plan physical.system id) {external : String}
  {entry : Modules.Selection program prepared.environment.assembly.instances},
  prepared.find? external = some entry →
    ∀ {rom : WidthROM F},
      rom.Valid →
        ∀ {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F},
          Circuit.Erasure.Signed compiled.circuit.system
              { channel := entry.resolved.name, args := wires, result := output } →
            plan.Derives (Circuit.Erasure.rawROM rom)
                (Circuit.Erasure.message compiled.circuit.system
                  { channel := entry.resolved.name, args := wires, result := output }) →
              DecodesValues compiled.specialized.program.enums wires (entryValues args) →
                WireValue.decode compiled.specialized.program.enums output = some result →
                  ∃ value heap,
                    prepared.EvalFn external args value heap ∧
                      Represents
                        (WireROM.decode compiled.specialized.program.enums
                          (Circuit.Erasure.typedROM compiled.circuit.system rom))
                        heap value result
-/
#guard_msgs in
#check @Aiur.Optimized.ModulesArtifact.grouped_heap_sound
/-- info: 'Aiur.Optimized.ModulesArtifact.grouped_heap_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.ModulesArtifact.grouped_heap_sound

/--
info: @Optimized.ModulesArtifact.grouped_activated_heap_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {id : String → Except String ℕ} {program : Modules.Program F} {prepared : Modules.Prepared program}
  (compiled : Optimized.ModulesArtifact prepared) (physical : Optimized.Physical.Prepared compiled.circuit.artifact)
  (plan : Optimized.Grouping.Plan physical.system id),
  plan.WellFormedActivation →
    ∀ {external : String} {entry : Modules.Selection program prepared.environment.assembly.instances},
      prepared.find? external = some entry →
        ∀ {rom : WidthROM F},
          rom.Valid →
            ∀ {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F},
              Circuit.Erasure.Signed compiled.circuit.system
                  { channel := entry.resolved.name, args := wires, result := output } →
                plan.ActivatedDerives (Circuit.Erasure.rawROM rom)
                    (Circuit.Erasure.message compiled.circuit.system
                      { channel := entry.resolved.name, args := wires, result := output }) →
                  DecodesValues compiled.specialized.program.enums wires (entryValues args) →
                    WireValue.decode compiled.specialized.program.enums output = some result →
                      ∃ value heap,
                        prepared.EvalFn external args value heap ∧
                          Represents
                            (WireROM.decode compiled.specialized.program.enums
                              (Circuit.Erasure.typedROM compiled.circuit.system rom))
                            heap value result
-/
#guard_msgs in
#check @Aiur.Optimized.ModulesArtifact.grouped_activated_heap_sound
/-- info: 'Aiur.Optimized.ModulesArtifact.grouped_activated_heap_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.ModulesArtifact.grouped_activated_heap_sound

/--
info: @Optimized.Physical.Prepared.derives_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {artifact : Optimized.Artifact F} (prepared : Optimized.Physical.Prepared artifact) {rom : WidthROM F}
  {root : Circuit.Message F},
  root.channel ∈ artifact.entries →
    Circuit.Erasure.Signed artifact.system root →
      (Circuit.Derives artifact.system (Circuit.Erasure.typedROM artifact.system rom) root ↔
        Circuit.Derives prepared.system (Circuit.Erasure.rawROM rom) (Circuit.Erasure.message artifact.system root))
-/
#guard_msgs in
#check @Aiur.Optimized.Physical.Prepared.derives_iff
/-- info: 'Aiur.Optimized.Physical.Prepared.derives_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.Physical.Prepared.derives_iff

/--
info: @Optimized.Physical.Prepared.entry_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F}
  {entries : List String} {config : Optimized.Config} {artifact : Optimized.Artifact F},
  Optimized.compile program entries config = Except.ok artifact →
    ∀ (prepared : Optimized.Physical.Prepared artifact) {rom : WidthROM F},
      rom.Valid →
        ∀ {root : Circuit.Message F},
          root.channel ∈ entries →
            Circuit.Erasure.Signed artifact.system root →
              Circuit.Message.PublicArguments program.enums root →
                Circuit.Derives prepared.system (Circuit.Erasure.rawROM rom)
                    (Circuit.Erasure.message artifact.system root) →
                  Circuit.Message.Evaluates program (Circuit.Erasure.typedROM artifact.system rom) root
-/
#guard_msgs in
#check @Aiur.Optimized.Physical.Prepared.entry_sound
/-- info: 'Aiur.Optimized.Physical.Prepared.entry_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.Physical.Prepared.entry_sound

/--
info: @Optimized.Physical.Prepared.native_heap_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {source : Generic.Source F} {entries : List String} {specialized : Generic.Specialized source entries}
  (compiled : Optimized.GenericArtifact specialized) (prepared : Optimized.Physical.Prepared compiled.artifact)
  {name : String},
  name ∈ entries →
    ∀ {rom : WidthROM F},
      rom.Valid →
        ∀ {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F},
          Circuit.Erasure.Signed compiled.system { channel := name, args := wires, result := output } →
            Circuit.Derives prepared.system (Circuit.Erasure.rawROM rom)
                (Circuit.Erasure.message compiled.system { channel := name, args := wires, result := output }) →
              DecodesValues specialized.program.enums wires (entryValues args) →
                WireValue.decode specialized.program.enums output = some result →
                  ∃ value heap,
                    Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
                      Represents
                        (WireROM.decode specialized.program.enums (Circuit.Erasure.typedROM compiled.system rom)) heap
                        value result
-/
#guard_msgs in
#check @Aiur.Optimized.Physical.Prepared.native_heap_sound
/-- info: 'Aiur.Optimized.Physical.Prepared.native_heap_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.Physical.Prepared.native_heap_sound

/--
info: @Optimized.Physical.Prepared.grouped_native_heap_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {id : String → Except String ℕ} {source : Generic.Source F} {entries : List String}
  {specialized : Generic.Specialized source entries} (compiled : Optimized.GenericArtifact specialized)
  (prepared : Optimized.Physical.Prepared compiled.artifact) (plan : Optimized.Grouping.Plan prepared.system id)
  {name : String},
  name ∈ entries →
    ∀ {rom : WidthROM F},
      rom.Valid →
        ∀ {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F},
          Circuit.Erasure.Signed compiled.system { channel := name, args := wires, result := output } →
            plan.Derives (Circuit.Erasure.rawROM rom)
                (Circuit.Erasure.message compiled.system { channel := name, args := wires, result := output }) →
              DecodesValues specialized.program.enums wires (entryValues args) →
                WireValue.decode specialized.program.enums output = some result →
                  ∃ value heap,
                    Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
                      Represents
                        (WireROM.decode specialized.program.enums (Circuit.Erasure.typedROM compiled.system rom)) heap
                        value result
-/
#guard_msgs in
#check @Aiur.Optimized.Physical.Prepared.grouped_native_heap_sound
/-- info: 'Aiur.Optimized.Physical.Prepared.grouped_native_heap_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.Physical.Prepared.grouped_native_heap_sound

/--
info: @Optimized.Physical.Prepared.grouped_activated_native_heap_sound : ∀ {F : Type} [inst : Field F]
  [inst_1 : DecidableEq F] {id : String → Except String ℕ} {source : Generic.Source F} {entries : List String}
  {specialized : Generic.Specialized source entries} (compiled : Optimized.GenericArtifact specialized)
  (prepared : Optimized.Physical.Prepared compiled.artifact) (plan : Optimized.Grouping.Plan prepared.system id),
  plan.WellFormedActivation →
    ∀ {name : String},
      name ∈ entries →
        ∀ {rom : WidthROM F},
          rom.Valid →
            ∀ {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F},
              Circuit.Erasure.Signed compiled.system { channel := name, args := wires, result := output } →
                plan.ActivatedDerives (Circuit.Erasure.rawROM rom)
                    (Circuit.Erasure.message compiled.system { channel := name, args := wires, result := output }) →
                  DecodesValues specialized.program.enums wires (entryValues args) →
                    WireValue.decode specialized.program.enums output = some result →
                      ∃ value heap,
                        Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
                          Represents
                            (WireROM.decode specialized.program.enums (Circuit.Erasure.typedROM compiled.system rom))
                            heap value result
-/
#guard_msgs in
#check @Aiur.Optimized.Physical.Prepared.grouped_activated_native_heap_sound
/--
info: 'Aiur.Optimized.Physical.Prepared.grouped_activated_native_heap_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Aiur.Optimized.Physical.Prepared.grouped_activated_native_heap_sound

/--
info: @Optimized.Grouping.Plan.localRule_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {id : String → Except String ℕ} {source : Circuit.System F} (plan : Optimized.Grouping.Plan source id)
  (rom : WireROM F) (root : Circuit.Message F) (premises : List (Circuit.Message F)),
  plan.LocalRule rom root premises ↔ ∃ c, source.findChip? c.name = some c ∧ c.LocalRule rom root premises
-/
#guard_msgs in
#check @Aiur.Optimized.Grouping.Plan.localRule_iff
/-- info: 'Aiur.Optimized.Grouping.Plan.localRule_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.Grouping.Plan.localRule_iff

/--
info: @Optimized.Grouping.Plan.derives_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {id : String → Except String ℕ} {source : Circuit.System F} (plan : Optimized.Grouping.Plan source id)
  {rom : WireROM F} {root : Circuit.Message F}, plan.Derives rom root → Circuit.Derives source rom root
-/
#guard_msgs in
#check @Aiur.Optimized.Grouping.Plan.derives_sound
/-- info: 'Aiur.Optimized.Grouping.Plan.derives_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.Grouping.Plan.derives_sound

/--
info: @Optimized.Grouping.Plan.derives_complete : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {id : String → Except String ℕ} {source : Circuit.System F} (plan : Optimized.Grouping.Plan source id)
  {rom : WireROM F} {root : Circuit.Message F}, Circuit.Derives source rom root → plan.Derives rom root
-/
#guard_msgs in
#check @Aiur.Optimized.Grouping.Plan.derives_complete
/-- info: 'Aiur.Optimized.Grouping.Plan.derives_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.Grouping.Plan.derives_complete

/--
info: @Optimized.Grouping.Plan.derives_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {id : String → Except String ℕ} {source : Circuit.System F} (plan : Optimized.Grouping.Plan source id)
  {rom : WireROM F} {root : Circuit.Message F}, plan.Derives rom root ↔ Circuit.Derives source rom root
-/
#guard_msgs in
#check @Aiur.Optimized.Grouping.Plan.derives_iff
/-- info: 'Aiur.Optimized.Grouping.Plan.derives_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.Grouping.Plan.derives_iff

/--
info: @Optimized.Grouping.Plan.activatedLocalRule_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {source : Circuit.System F} {id : String → Except String ℕ} (plan : Optimized.Grouping.Plan source id),
  plan.WellFormedActivation →
    ∀ (rom : WireROM F) (root : Circuit.Message F) (premises : List (Circuit.Message F)),
      plan.ActivatedLocalRule rom root premises ↔ plan.LocalRule rom root premises
-/
#guard_msgs in
#check @Aiur.Optimized.Grouping.Plan.activatedLocalRule_iff
/-- info: 'Aiur.Optimized.Grouping.Plan.activatedLocalRule_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.Grouping.Plan.activatedLocalRule_iff

/--
info: @Optimized.Grouping.Plan.activatedDerives_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {source : Circuit.System F} {id : String → Except String ℕ} (plan : Optimized.Grouping.Plan source id),
  plan.WellFormedActivation →
    ∀ {rom : WireROM F} {root : Circuit.Message F}, plan.ActivatedDerives rom root → Circuit.Derives source rom root
-/
#guard_msgs in
#check @Aiur.Optimized.Grouping.Plan.activatedDerives_sound
/-- info: 'Aiur.Optimized.Grouping.Plan.activatedDerives_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.Grouping.Plan.activatedDerives_sound

/--
info: @Optimized.Grouping.Plan.activatedDerives_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {source : Circuit.System F} {id : String → Except String ℕ} (plan : Optimized.Grouping.Plan source id),
  plan.WellFormedActivation →
    ∀ {rom : WireROM F} {root : Circuit.Message F}, plan.ActivatedDerives rom root ↔ plan.Derives rom root
-/
#guard_msgs in
#check @Aiur.Optimized.Grouping.Plan.activatedDerives_iff
/-- info: 'Aiur.Optimized.Grouping.Plan.activatedDerives_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.Grouping.Plan.activatedDerives_iff

/--
info: @Optimized.Activation.active_rule_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] (chip : Circuit.Chip F),
  chip.wellFormed = true →
    (Optimized.Activation.compile chip).wellFormed = true →
      ∀ (rom : WireROM F) (root : Circuit.Message F) (premises : List (Circuit.Message F)),
        (∃ row,
            row.chip = chip.name ∧
              (Optimized.Activation.compile chip).ValidRow rom row ∧
                row.assignment chip.numVars = 1 ∧
                  (Optimized.Activation.compile chip).receive row = root ∧
                    (Optimized.Activation.compile chip).premises row = premises) ↔
          chip.LocalRule rom root premises
-/
#guard_msgs in
#check @Aiur.Optimized.Activation.active_rule_iff
/-- info: 'Aiur.Optimized.Activation.active_rule_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.Activation.active_rule_iff

/--
info: @Optimized.Activation.activeRule_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] (chip : Circuit.Chip F),
  chip.wellFormed = true →
    (Optimized.Activation.compile chip).wellFormed = true →
      ∀ (rom : WireROM F) (root : Circuit.Message F) (premises : List (Circuit.Message F)),
        Optimized.Activation.ActiveRule chip rom root premises ↔ chip.LocalRule rom root premises
-/
#guard_msgs in
#check @Aiur.Optimized.Activation.activeRule_iff
/-- info: 'Aiur.Optimized.Activation.activeRule_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.Activation.activeRule_iff

/--
info: @Modules.Prepared.physical_heap_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {program : Modules.Program F} (prepared : Modules.Prepared program) (compiled : Optimized.ModulesArtifact prepared)
  (physical : Optimized.Physical.Prepared compiled.circuit.artifact) {external : String}
  {entry : Modules.Selection program prepared.environment.assembly.instances},
  prepared.find? external = some entry →
    ∀ {rom : WidthROM F},
      rom.Valid →
        ∀ {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F},
          Circuit.Erasure.Signed compiled.circuit.system
              { channel := entry.resolved.name, args := wires, result := output } →
            Circuit.Derives physical.system (Circuit.Erasure.rawROM rom)
                (Circuit.Erasure.message compiled.circuit.system
                  { channel := entry.resolved.name, args := wires, result := output }) →
              DecodesValues compiled.specialized.program.enums wires (entryValues args) →
                WireValue.decode compiled.specialized.program.enums output = some result →
                  ∃ value heap,
                    prepared.EvalFn external args value heap ∧
                      Represents
                        (WireROM.decode compiled.specialized.program.enums
                          (Circuit.Erasure.typedROM compiled.circuit.system rom))
                        heap value result
-/
#guard_msgs in
#check @Aiur.Modules.Prepared.physical_heap_sound
/-- info: 'Aiur.Modules.Prepared.physical_heap_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Modules.Prepared.physical_heap_sound

/--
info: @Modules.Prepared.grouped_heap_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {id : String → Except String ℕ} {program : Modules.Program F} (prepared : Modules.Prepared program)
  (compiled : Optimized.ModulesArtifact prepared) (physical : Optimized.Physical.Prepared compiled.circuit.artifact)
  (plan : Optimized.Grouping.Plan physical.system id) {external : String}
  {entry : Modules.Selection program prepared.environment.assembly.instances},
  prepared.find? external = some entry →
    ∀ {rom : WidthROM F},
      rom.Valid →
        ∀ {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F},
          Circuit.Erasure.Signed compiled.circuit.system
              { channel := entry.resolved.name, args := wires, result := output } →
            plan.Derives (Circuit.Erasure.rawROM rom)
                (Circuit.Erasure.message compiled.circuit.system
                  { channel := entry.resolved.name, args := wires, result := output }) →
              DecodesValues compiled.specialized.program.enums wires (entryValues args) →
                WireValue.decode compiled.specialized.program.enums output = some result →
                  ∃ value heap,
                    prepared.EvalFn external args value heap ∧
                      Represents
                        (WireROM.decode compiled.specialized.program.enums
                          (Circuit.Erasure.typedROM compiled.circuit.system rom))
                        heap value result
-/
#guard_msgs in
#check @Aiur.Modules.Prepared.grouped_heap_sound
/-- info: 'Aiur.Modules.Prepared.grouped_heap_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Modules.Prepared.grouped_heap_sound

/--
info: @Modules.Prepared.grouped_activated_heap_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {id : String → Except String ℕ} {program : Modules.Program F} (prepared : Modules.Prepared program)
  (compiled : Optimized.ModulesArtifact prepared) (physical : Optimized.Physical.Prepared compiled.circuit.artifact)
  (plan : Optimized.Grouping.Plan physical.system id),
  plan.WellFormedActivation →
    ∀ {external : String} {entry : Modules.Selection program prepared.environment.assembly.instances},
      prepared.find? external = some entry →
        ∀ {rom : WidthROM F},
          rom.Valid →
            ∀ {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F},
              Circuit.Erasure.Signed compiled.circuit.system
                  { channel := entry.resolved.name, args := wires, result := output } →
                plan.ActivatedDerives (Circuit.Erasure.rawROM rom)
                    (Circuit.Erasure.message compiled.circuit.system
                      { channel := entry.resolved.name, args := wires, result := output }) →
                  DecodesValues compiled.specialized.program.enums wires (entryValues args) →
                    WireValue.decode compiled.specialized.program.enums output = some result →
                      ∃ value heap,
                        prepared.EvalFn external args value heap ∧
                          Represents
                            (WireROM.decode compiled.specialized.program.enums
                              (Circuit.Erasure.typedROM compiled.circuit.system rom))
                            heap value result
-/
#guard_msgs in
#check @Aiur.Modules.Prepared.grouped_activated_heap_sound
/-- info: 'Aiur.Modules.Prepared.grouped_activated_heap_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Modules.Prepared.grouped_activated_heap_sound

/-! ### 3a. Memo-Cycle Soundness: the Depth Pass and the Grouped, Activated Memo Checker -/

/--
info: @Circuit.CycleLength.no_cycle : ∀ {V F : Type} [inst : Field F] [DecidableEq V] {edge : V → V → Prop} {rows : Finset V}
  {N B : ℕ},
  (∀ (u v : V), edge u v → u ∈ rows) →
    rows.card ≤ N →
      ∀ (rank : V → ℕ) (depth : V → F),
        (∀ (u v : V), edge u v → rank v < rank u ∨ rank v = rank u ∧ ∃ s, 0 < s ∧ s ≤ B ∧ depth v + ↑s = depth u) →
          (∀ (n : ℕ), 0 < n → n ≤ N * B → ↑n ≠ 0) → ∀ (u : V), ¬Relation.TransGen edge u u
-/
#guard_msgs in
#check @Aiur.Circuit.CycleLength.no_cycle
/-- info: 'Aiur.Circuit.CycleLength.no_cycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Circuit.CycleLength.no_cycle

/--
info: @Circuit.MemoDerivation.acyclic_of_steps : ∀ {F : Type} {rom : WireROM F} [inst : Field F] [inst_1 : DecidableEq F]
  {system : Circuit.System F} {message : Circuit.Message F} (graph : Circuit.MemoDerivation system rom message)
  {N B : ℕ},
  graph.rows.card ≤ N →
    ∀ (rank : Fin graph.size → ℕ) (depth : Fin graph.size → F),
      (∀ (i : Fin graph.size) (j : Fin (graph.node i).premises.length),
          rank (graph.target i j) < rank i ∨
            rank (graph.target i j) = rank i ∧ ∃ s, 0 < s ∧ s ≤ B ∧ depth (graph.target i j) + ↑s = depth i) →
        (∀ (n : ℕ), 0 < n → n ≤ N * B → ↑n ≠ 0) → graph.Acyclic
-/
#guard_msgs in
#check @Aiur.Circuit.MemoDerivation.acyclic_of_steps
/-- info: 'Aiur.Circuit.MemoDerivation.acyclic_of_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Circuit.MemoDerivation.acyclic_of_steps

/--
info: @Circuit.MemoDerivation.exists_of_balance : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {rom : WireROM F}
  {system : Circuit.System F} {root : Circuit.Message F} (rules : List (Circuit.RuleInstance system rom × ℤ)),
  (Circuit.Balance.accumulator (fun c => decide (system.MapClaim c)) root
          (List.map (fun rule => (rule.1.claims, rule.2)) rules)).isZero =
      true →
    ∃ graph, graph.rows.card ≤ rules.length
-/
#guard_msgs in
#check @Aiur.Circuit.MemoDerivation.exists_of_balance
/-- info: 'Aiur.Circuit.MemoDerivation.exists_of_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Circuit.MemoDerivation.exists_of_balance

/--
info: @Optimized.Depth.compileChip_localRule : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  (cfg : Optimized.Depth.Config) (chip : Circuit.Chip F),
  chip.wellFormed = true →
    (∀ pair ∈ chip.sends.zip (cfg.plan chip.name).slots,
        pair.2 = Optimized.Depth.SlotKind.plain ↔ cfg.recursive pair.1.channel = false) →
      (cfg.plan chip.name).slots.length = chip.sends.length →
        ∀ {rom : WireROM F} {root : Circuit.Message F} {premises : List (Circuit.Message F)},
          (Optimized.Depth.compileChip cfg.limbs (cfg.plan chip.name) chip).LocalRule rom root premises →
            ∃ main ranges,
              premises = main ++ ranges ∧
                chip.LocalRule rom (Optimized.Depth.erase cfg root) (List.map (Optimized.Depth.erase cfg) main) ∧
                  ∀ check ∈ ranges, ∃ width ∈ cfg.limbs, check.channel = Optimized.Depth.rangeName width
-/
#guard_msgs in
#check @Aiur.Optimized.Depth.compileChip_localRule
/-- info: 'Aiur.Optimized.Depth.compileChip_localRule' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.Depth.compileChip_localRule

/--
info: @Optimized.Depth.compileChip_lift : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  (cfg : Optimized.Depth.Config) (chip : Circuit.Chip F),
  chip.wellFormed = true →
    (∀ pair ∈ chip.sends.zip (cfg.plan chip.name).slots,
        pair.2 = Optimized.Depth.SlotKind.plain ↔ cfg.recursive pair.1.channel = false) →
      (cfg.plan chip.name).slots.length = chip.sends.length →
        ∀ (rom : WireROM F) (a b : Circuit.Var → F),
          (∀ id < chip.numVars, a id = b id) →
            ((Optimized.Depth.compileChip cfg.limbs (cfg.plan chip.name) chip).ValidAssignment rom b ↔
                chip.ValidAssignment rom a) ∧
              Optimized.Depth.erase cfg
                    ((Optimized.Depth.compileChip cfg.limbs (cfg.plan chip.name) chip).conclusion b) =
                  chip.conclusion a ∧
                List.map (Optimized.Depth.erase cfg)
                    (List.filterMap (Optimized.Depth.enabled b)
                      (Optimized.Depth.mainSends cfg.limbs (Circuit.ArithExpr.var chip.numVars)
                        ((cfg.plan chip.name).base chip) (chip.sends.zip (cfg.plan chip.name).slots))) =
                  chip.requirements a
-/
#guard_msgs in
#check @Aiur.Optimized.Depth.compileChip_lift
/-- info: 'Aiur.Optimized.Depth.compileChip_lift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.Depth.compileChip_lift

/--
info: @Optimized.Depth.rangeClaim : ∀ {F : Type} [inst : Field F] [DecidableEq F] {cfg : Optimized.Depth.Config}
  {source : Circuit.System F},
  Optimized.Depth.Facts cfg source →
    ∀ {width : ℕ} {x : F},
      width ∈ cfg.limbs →
        (Optimized.Depth.system cfg source).MapClaim (Optimized.Depth.rangeMessage width x) → ∃ n < 2 ^ width, x = ↑n
-/
#guard_msgs in
#check @Aiur.Optimized.Depth.rangeClaim
/-- info: 'Aiur.Optimized.Depth.rangeClaim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.Depth.rangeClaim

/--
info: @Optimized.Depth.derives_erase : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {cfg : Optimized.Depth.Config}
  {source : Circuit.System F} {rom : WireROM F},
  Optimized.Depth.Facts cfg source →
    ∀ {message : Circuit.Message F},
      Circuit.Derives (Optimized.Depth.system cfg source) rom message →
        message.channel ∉ cfg.names → Circuit.Derives source rom (Optimized.Depth.erase cfg message)
-/
#guard_msgs in
#check @Aiur.Optimized.Depth.derives_erase
/-- info: 'Aiur.Optimized.Depth.derives_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.Depth.derives_erase

/--
info: @Optimized.Depth.acyclic : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {cfg : Optimized.Depth.Config}
  {source : Circuit.System F} {rom : WireROM F},
  Optimized.Depth.Facts cfg source →
    ∀ {root : Circuit.Message F} (graph : Circuit.MemoDerivation (Optimized.Depth.system cfg source) rom root) {N : ℕ},
      graph.rows.card ≤ N → (∀ (n : ℕ), 0 < n → n ≤ N * 2 ^ cfg.bits → ↑n ≠ 0) → graph.Acyclic
-/
#guard_msgs in
#check @Aiur.Optimized.Depth.acyclic
/-- info: 'Aiur.Optimized.Depth.acyclic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.Depth.acyclic

/--
info: @Optimized.Depth.checkMemo_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {cfg : Optimized.Depth.Config}
  {source : Circuit.System F} {rom : WireROM F},
  Optimized.Depth.Certified cfg source →
    ∀ {root : Circuit.Message F} {rows : List (Circuit.WeightedRow F)} {N : ℕ},
      rows.length ≤ N →
        (∀ (n : ℕ), 0 < n → n ≤ N * 2 ^ cfg.bits → ↑n ≠ 0) →
          (Optimized.Depth.system cfg source).checkMemo rom root rows = Except.ok () →
            root.channel ∉ cfg.names → Circuit.Derives source rom (Optimized.Depth.erase cfg root)
-/
#guard_msgs in
#check @Aiur.Optimized.Depth.checkMemo_sound
/-- info: 'Aiur.Optimized.Depth.checkMemo_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.Depth.checkMemo_sound

/--
info: Optimized.Depth.goldilocks_characteristic : ∀ (n : ℕ), 0 < n → n ≤ 2 ^ 39 * 2 ^ 24 → ↑n ≠ 0
-/
#guard_msgs in
#check @Aiur.Optimized.Depth.goldilocks_characteristic
/-- info: 'Aiur.Optimized.Depth.goldilocks_characteristic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.Depth.goldilocks_characteristic

/--
info: @Optimized.Grouping.Plan.checkMemo_rules : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {source : Circuit.System F} {id : String → Except String ℕ} {plan : Optimized.Grouping.Plan source id},
  plan.WellFormedActivation →
    ∀ {rom : WireROM F} {root : Circuit.Message F} {rows : List (Circuit.WeightedRow F)},
      plan.checkMemo rom root rows = Except.ok () →
        ∃ rules,
          rules.length ≤ rows.length ∧
            (Circuit.Balance.accumulator (fun c => decide (source.MapClaim c)) root
                  (List.map (fun rule => (rule.1.claims, rule.2)) rules)).isZero =
              true
-/
#guard_msgs in
#check @Aiur.Optimized.Grouping.Plan.checkMemo_rules
/-- info: 'Aiur.Optimized.Grouping.Plan.checkMemo_rules' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.Grouping.Plan.checkMemo_rules

/--
info: @Optimized.Grouping.Plan.checkMemo_graph : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {source : Circuit.System F} {id : String → Except String ℕ} {plan : Optimized.Grouping.Plan source id},
  plan.WellFormedActivation →
    ∀ {rom : WireROM F} {root : Circuit.Message F} {rows : List (Circuit.WeightedRow F)},
      plan.checkMemo rom root rows = Except.ok () → ∃ graph, graph.rows.card ≤ rows.length
-/
#guard_msgs in
#check @Aiur.Optimized.Grouping.Plan.checkMemo_graph
/-- info: 'Aiur.Optimized.Grouping.Plan.checkMemo_graph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.Grouping.Plan.checkMemo_graph

/--
info: @Optimized.Depth.plan_checkMemo_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {cfg : Optimized.Depth.Config} {source : Circuit.System F} {rom : WireROM F} {id : String → Except String ℕ},
  Optimized.Depth.Certified cfg source →
    ∀ (plan : Optimized.Grouping.Plan (Optimized.Depth.system cfg source) id),
      plan.WellFormedActivation →
        ∀ {root : Circuit.Message F} {rows : List (Circuit.WeightedRow F)} {N : ℕ},
          rows.length ≤ N →
            (∀ (n : ℕ), 0 < n → n ≤ N * 2 ^ cfg.bits → ↑n ≠ 0) →
              plan.checkMemo rom root rows = Except.ok () →
                root.channel ∉ cfg.names → Circuit.Derives source rom (Optimized.Depth.erase cfg root)
-/
#guard_msgs in
#check @Aiur.Optimized.Depth.plan_checkMemo_sound
/-- info: 'Aiur.Optimized.Depth.plan_checkMemo_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.Depth.plan_checkMemo_sound

/--
info: @Optimized.Physical.Prepared.depth_native_heap_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {source : Generic.Source F} {entries : List String} {specialized : Generic.Specialized source entries}
  (compiled : Optimized.GenericArtifact specialized) (prepared : Optimized.Physical.Prepared compiled.artifact)
  {cfg : Optimized.Depth.Config},
  Optimized.Depth.Certified cfg prepared.system →
    ∀ {name : String},
      name ∈ entries →
        ∀ {rom : WidthROM F},
          rom.Valid →
            ∀ {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F},
              Circuit.Erasure.Signed compiled.system { channel := name, args := wires, result := output } →
                ∀ {root : Circuit.Message F},
                  Optimized.Depth.erase cfg root =
                      Circuit.Erasure.message compiled.system { channel := name, args := wires, result := output } →
                    root.channel ∉ cfg.names →
                      ∀ {rows : List (Circuit.WeightedRow F)} {N : ℕ},
                        rows.length ≤ N →
                          (∀ (n : ℕ), 0 < n → n ≤ N * 2 ^ cfg.bits → ↑n ≠ 0) →
                            (Optimized.Depth.system cfg prepared.system).checkMemo (Circuit.Erasure.rawROM rom) root
                                  rows =
                                Except.ok () →
                              DecodesValues specialized.program.enums wires (entryValues args) →
                                WireValue.decode specialized.program.enums output = some result →
                                  ∃ value heap,
                                    Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
                                      Represents
                                        (WireROM.decode specialized.program.enums
                                          (Circuit.Erasure.typedROM compiled.system rom))
                                        heap value result
-/
#guard_msgs in
#check @Aiur.Optimized.Physical.Prepared.depth_native_heap_sound
/-- info: 'Aiur.Optimized.Physical.Prepared.depth_native_heap_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.Physical.Prepared.depth_native_heap_sound

/--
info: @Optimized.Physical.Prepared.depth_grouped_activated_heap_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {id : String → Except String ℕ} {source : Generic.Source F} {entries : List String}
  {specialized : Generic.Specialized source entries} (compiled : Optimized.GenericArtifact specialized)
  (prepared : Optimized.Physical.Prepared compiled.artifact) {cfg : Optimized.Depth.Config},
  Optimized.Depth.Certified cfg prepared.system →
    ∀ (plan : Optimized.Grouping.Plan (Optimized.Depth.system cfg prepared.system) id),
      plan.WellFormedActivation →
        ∀ {name : String},
          name ∈ entries →
            ∀ {rom : WidthROM F},
              rom.Valid →
                ∀ {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F},
                  Circuit.Erasure.Signed compiled.system { channel := name, args := wires, result := output } →
                    ∀ {root : Circuit.Message F},
                      Optimized.Depth.erase cfg root =
                          Circuit.Erasure.message compiled.system { channel := name, args := wires, result := output } →
                        root.channel ∉ cfg.names →
                          ∀ {rows : List (Circuit.WeightedRow F)},
                            rows.length ≤ 2 ^ 39 →
                              (∀ (n : ℕ), 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → ↑n ≠ 0) →
                                plan.checkMemo (Circuit.Erasure.rawROM rom) root rows = Except.ok () →
                                  DecodesValues specialized.program.enums wires (entryValues args) →
                                    WireValue.decode specialized.program.enums output = some result →
                                      ∃ value heap,
                                        Generic.SourceSemantics.EvalFn source.world name args [] value heap ∧
                                          Represents
                                            (WireROM.decode specialized.program.enums
                                              (Circuit.Erasure.typedROM compiled.system rom))
                                            heap value result
-/
#guard_msgs in
#check @Aiur.Optimized.Physical.Prepared.depth_grouped_activated_heap_sound
/--
info: 'Aiur.Optimized.Physical.Prepared.depth_grouped_activated_heap_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Aiur.Optimized.Physical.Prepared.depth_grouped_activated_heap_sound

/--
info: @Modules.Prepared.depth_grouped_activated_heap_sound : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {id : String → Except String ℕ} {program : Modules.Program F} (prepared : Modules.Prepared program)
  (compiled : Optimized.ModulesArtifact prepared) (physical : Optimized.Physical.Prepared compiled.circuit.artifact)
  {cfg : Optimized.Depth.Config},
  Optimized.Depth.Certified cfg physical.system →
    ∀ (plan : Optimized.Grouping.Plan (Optimized.Depth.system cfg physical.system) id),
      plan.WellFormedActivation →
        ∀ {external : String} {entry : Modules.Selection program prepared.environment.assembly.instances},
          prepared.find? external = some entry →
            ∀ {rom : WidthROM F},
              rom.Valid →
                ∀ {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F},
                  Circuit.Erasure.Signed compiled.circuit.system
                      { channel := entry.resolved.name, args := wires, result := output } →
                    ∀ {root : Circuit.Message F},
                      Optimized.Depth.erase cfg root =
                          Circuit.Erasure.message compiled.circuit.system
                            { channel := entry.resolved.name, args := wires, result := output } →
                        root.channel ∉ cfg.names →
                          ∀ {rows : List (Circuit.WeightedRow F)},
                            rows.length ≤ 2 ^ 39 →
                              (∀ (n : ℕ), 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → ↑n ≠ 0) →
                                plan.checkMemo (Circuit.Erasure.rawROM rom) root rows = Except.ok () →
                                  DecodesValues compiled.specialized.program.enums wires (entryValues args) →
                                    WireValue.decode compiled.specialized.program.enums output = some result →
                                      ∃ value heap,
                                        prepared.EvalFn external args value heap ∧
                                          Represents
                                            (WireROM.decode compiled.specialized.program.enums
                                              (Circuit.Erasure.typedROM compiled.circuit.system rom))
                                            heap value result
-/
#guard_msgs in
#check @Aiur.Modules.Prepared.depth_grouped_activated_heap_sound
/-- info: 'Aiur.Modules.Prepared.depth_grouped_activated_heap_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Modules.Prepared.depth_grouped_activated_heap_sound

/--
info: @Modules.Prepared.depth_grouped_activated_heap_sound_goldilocks : ∀ {id : String → Except String ℕ}
  {program : Modules.Program Library.U32.Goldilocks.F} (prepared : Modules.Prepared program)
  (compiled : Optimized.ModulesArtifact prepared) (physical : Optimized.Physical.Prepared compiled.circuit.artifact)
  {cfg : Optimized.Depth.Config},
  Optimized.Depth.Certified cfg physical.system →
    cfg.bits = 24 →
      ∀ (plan : Optimized.Grouping.Plan (Optimized.Depth.system cfg physical.system) id),
        plan.WellFormedActivation →
          ∀ {external : String} {entry : Modules.Selection program prepared.environment.assembly.instances},
            prepared.find? external = some entry →
              ∀ {rom : WidthROM Library.U32.Goldilocks.F},
                rom.Valid →
                  ∀ {args : List (SourceValue Library.U32.Goldilocks.F)} {result : Value Library.U32.Goldilocks.F}
                    {wires : List (WireValue Library.U32.Goldilocks.F)} {output : WireValue Library.U32.Goldilocks.F},
                    Circuit.Erasure.Signed compiled.circuit.system
                        { channel := entry.resolved.name, args := wires, result := output } →
                      ∀ {root : Circuit.Message Library.U32.Goldilocks.F},
                        Optimized.Depth.erase cfg root =
                            Circuit.Erasure.message compiled.circuit.system
                              { channel := entry.resolved.name, args := wires, result := output } →
                          root.channel ∉ cfg.names →
                            ∀ {rows : List (Circuit.WeightedRow Library.U32.Goldilocks.F)},
                              rows.length ≤ 2 ^ 39 →
                                plan.checkMemo (Circuit.Erasure.rawROM rom) root rows = Except.ok () →
                                  DecodesValues compiled.specialized.program.enums wires (entryValues args) →
                                    WireValue.decode compiled.specialized.program.enums output = some result →
                                      ∃ value heap,
                                        prepared.EvalFn external args value heap ∧
                                          Represents
                                            (WireROM.decode compiled.specialized.program.enums
                                              (Circuit.Erasure.typedROM compiled.circuit.system rom))
                                            heap value result
-/
#guard_msgs in
#check @Aiur.Modules.Prepared.depth_grouped_activated_heap_sound_goldilocks
/--
info: 'Aiur.Modules.Prepared.depth_grouped_activated_heap_sound_goldilocks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Aiur.Modules.Prepared.depth_grouped_activated_heap_sound_goldilocks

/-! ### 3b. Observed Headlines: Calls Carried by the Trace's Memory -/

/--
info: @ROMEvalCall.realizeCells : ∀ {F : Type} {rom : ROM F} [inst : Field F] [inst_1 : DecidableEq F],
  rom.Valid →
    ∀ {program : Program F} {name : String} {args : List (Value F)} {result : Value F},
      ROMEvalCall rom program name args result →
        ∀ {heap : Heap F} {sources : List (SourceValue F)},
          RepresentsArgs rom heap sources args →
            ∃ source after,
              EvalFn program name sources heap source after ∧
                heap <+: after ∧ Represents rom after source result ∧ CellsInROM rom (List.length heap) after
-/
#guard_msgs in
#check @Aiur.ROMEvalCall.realizeCells
/-- info: 'Aiur.ROMEvalCall.realizeCells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.ROMEvalCall.realizeCells

/--
info: @Generic.SourceSemantics.ObsFn.erase : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {world : Generic.SourceSemantics.World F} {name : String} {args : List (SourceValue F)} {before after : Heap F}
  {result : SourceValue F} {calls : List (Generic.SourceSemantics.Call F)},
  Generic.SourceSemantics.ObsFn world name args before result after calls →
    Generic.SourceSemantics.EvalFn world name args before result after
-/
#guard_msgs in
#check @Aiur.Generic.SourceSemantics.ObsFn.erase
/-- info: 'Aiur.Generic.SourceSemantics.ObsFn.erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.SourceSemantics.ObsFn.erase

/--
info: @Generic.SourceSemantics.EvalFn.observe : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {world : Generic.SourceSemantics.World F} {name : String} {args : List (SourceValue F)} {before after : Heap F}
  {result : SourceValue F},
  Generic.SourceSemantics.EvalFn world name args before result after →
    ∃ calls, Generic.SourceSemantics.ObsFn world name args before result after calls
-/
#guard_msgs in
#check @Aiur.Generic.SourceSemantics.EvalFn.observe
/-- info: 'Aiur.Generic.SourceSemantics.EvalFn.observe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.SourceSemantics.EvalFn.observe

/--
info: @Generic.SourceSemantics.ObsFn.represented : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {world : Generic.SourceSemantics.World F} {rom : ROM F},
  Generic.SourceSemantics.PreparesFromArgs world →
    ∀ {H : Heap F},
      HeapInROM rom H →
        ∀ {name : String} {args : List (SourceValue F)} {before after : Heap F} {result : SourceValue F}
          {calls : List (Generic.SourceSemantics.Call F)},
          Generic.SourceSemantics.ObsFn world name args before result after calls →
            before <+: after ∧
              (after <+: H →
                (∀ v ∈ args, Generic.SourceSemantics.Represented rom before v) →
                  Generic.SourceSemantics.Represented rom after result ∧ Generic.SourceSemantics.CallsInROM rom calls)
-/
#guard_msgs in
#check @Aiur.Generic.SourceSemantics.ObsFn.represented
/-- info: 'Aiur.Generic.SourceSemantics.ObsFn.represented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.SourceSemantics.ObsFn.represented

/--
info: @Generic.SourceSemantics.ObsFn.callsInROM : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {world : Generic.SourceSemantics.World F} {rom : ROM F},
  Generic.SourceSemantics.PreparesFromArgs world →
    ∀ {H : Heap F},
      HeapInROM rom H →
        ∀ {name : String} {args : List (SourceValue F)} {result : SourceValue F}
          {calls : List (Generic.SourceSemantics.Call F)},
          (∀ v ∈ args, Value.pointerFree v = true) →
            Generic.SourceSemantics.ObsFn world name args [] result H calls →
              Generic.SourceSemantics.CallsInROM rom calls
-/
#guard_msgs in
#check @Aiur.Generic.SourceSemantics.ObsFn.callsInROM
/-- info: 'Aiur.Generic.SourceSemantics.ObsFn.callsInROM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.SourceSemantics.ObsFn.callsInROM

/--
info: @Generic.Source.world_preparesFromArgs : ∀ {F : Type} [Field F] [inst : DecidableEq F] (s : Generic.Source F),
  Generic.SourceSemantics.PreparesFromArgs s.world
-/
#guard_msgs in
#check @Aiur.Generic.Source.world_preparesFromArgs
/-- info: 'Aiur.Generic.Source.world_preparesFromArgs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.Source.world_preparesFromArgs

/--
info: @Optimized.Physical.Prepared.native_heap_sound_observed : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {source : Generic.Source F} {entries : List String} {specialized : Generic.Specialized source entries}
  (compiled : Optimized.GenericArtifact specialized) (prepared : Optimized.Physical.Prepared compiled.artifact)
  {name : String},
  name ∈ entries →
    ∀ {rom : WidthROM F},
      rom.Valid →
        ∀ {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F},
          Circuit.Erasure.Signed compiled.system { channel := name, args := wires, result := output } →
            Circuit.Derives prepared.system (Circuit.Erasure.rawROM rom)
                (Circuit.Erasure.message compiled.system { channel := name, args := wires, result := output }) →
              DecodesValues specialized.program.enums wires (entryValues args) →
                WireValue.decode specialized.program.enums output = some result →
                  ∃ value heap calls,
                    Generic.SourceSemantics.ObsFn source.world name args [] value heap calls ∧
                      Represents
                          (WireROM.decode specialized.program.enums (Circuit.Erasure.typedROM compiled.system rom)) heap
                          value result ∧
                        Generic.SourceSemantics.CallsInROM
                          (WireROM.decode specialized.program.enums (Circuit.Erasure.typedROM compiled.system rom))
                          calls
-/
#guard_msgs in
#check @Aiur.Optimized.Physical.Prepared.native_heap_sound_observed
/-- info: 'Aiur.Optimized.Physical.Prepared.native_heap_sound_observed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Optimized.Physical.Prepared.native_heap_sound_observed

/--
info: @Optimized.ModulesArtifact.grouped_activated_heap_sound_observed : ∀ {F : Type} [inst : Field F]
  [inst_1 : DecidableEq F] {id : String → Except String ℕ} {program : Modules.Program F}
  {prepared : Modules.Prepared program} (compiled : Optimized.ModulesArtifact prepared)
  (physical : Optimized.Physical.Prepared compiled.circuit.artifact)
  (plan : Optimized.Grouping.Plan physical.system id),
  plan.WellFormedActivation →
    ∀ {external : String} {entry : Modules.Selection program prepared.environment.assembly.instances},
      prepared.find? external = some entry →
        ∀ {rom : WidthROM F},
          rom.Valid →
            ∀ {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F},
              Circuit.Erasure.Signed compiled.circuit.system
                  { channel := entry.resolved.name, args := wires, result := output } →
                plan.ActivatedDerives (Circuit.Erasure.rawROM rom)
                    (Circuit.Erasure.message compiled.circuit.system
                      { channel := entry.resolved.name, args := wires, result := output }) →
                  DecodesValues compiled.specialized.program.enums wires (entryValues args) →
                    WireValue.decode compiled.specialized.program.enums output = some result →
                      ∃ value heap calls,
                        prepared.ObsFn external args value heap calls ∧
                          Represents (compiled.traceROM rom) heap value result ∧
                            Generic.SourceSemantics.CallsInROM (compiled.traceROM rom) calls
-/
#guard_msgs in
#check @Aiur.Optimized.ModulesArtifact.grouped_activated_heap_sound_observed
/--
info: 'Aiur.Optimized.ModulesArtifact.grouped_activated_heap_sound_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Aiur.Optimized.ModulesArtifact.grouped_activated_heap_sound_observed

/--
info: @Modules.Prepared.grouped_activated_heap_sound_observed : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {id : String → Except String ℕ} {program : Modules.Program F} (prepared : Modules.Prepared program)
  (compiled : Optimized.ModulesArtifact prepared) (physical : Optimized.Physical.Prepared compiled.circuit.artifact)
  (plan : Optimized.Grouping.Plan physical.system id),
  plan.WellFormedActivation →
    ∀ {external : String} {entry : Modules.Selection program prepared.environment.assembly.instances},
      prepared.find? external = some entry →
        ∀ {rom : WidthROM F},
          rom.Valid →
            ∀ {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F},
              Circuit.Erasure.Signed compiled.circuit.system
                  { channel := entry.resolved.name, args := wires, result := output } →
                plan.ActivatedDerives (Circuit.Erasure.rawROM rom)
                    (Circuit.Erasure.message compiled.circuit.system
                      { channel := entry.resolved.name, args := wires, result := output }) →
                  DecodesValues compiled.specialized.program.enums wires (entryValues args) →
                    WireValue.decode compiled.specialized.program.enums output = some result →
                      ∃ value heap calls,
                        prepared.ObsFn external args value heap calls ∧
                          Represents (compiled.traceROM rom) heap value result ∧
                            Generic.SourceSemantics.CallsInROM (compiled.traceROM rom) calls
-/
#guard_msgs in
#check @Aiur.Modules.Prepared.grouped_activated_heap_sound_observed
/-- info: 'Aiur.Modules.Prepared.grouped_activated_heap_sound_observed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Modules.Prepared.grouped_activated_heap_sound_observed

/--
info: @Modules.Prepared.depth_grouped_activated_heap_sound_observed : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {id : String → Except String ℕ} {program : Modules.Program F} (prepared : Modules.Prepared program)
  (compiled : Optimized.ModulesArtifact prepared) (physical : Optimized.Physical.Prepared compiled.circuit.artifact)
  {cfg : Optimized.Depth.Config},
  Optimized.Depth.Certified cfg physical.system →
    ∀ (plan : Optimized.Grouping.Plan (Optimized.Depth.system cfg physical.system) id),
      plan.WellFormedActivation →
        ∀ {external : String} {entry : Modules.Selection program prepared.environment.assembly.instances},
          prepared.find? external = some entry →
            ∀ {rom : WidthROM F},
              rom.Valid →
                ∀ {args : List (SourceValue F)} {result : Value F} {wires : List (WireValue F)} {output : WireValue F},
                  Circuit.Erasure.Signed compiled.circuit.system
                      { channel := entry.resolved.name, args := wires, result := output } →
                    ∀ {root : Circuit.Message F},
                      Optimized.Depth.erase cfg root =
                          Circuit.Erasure.message compiled.circuit.system
                            { channel := entry.resolved.name, args := wires, result := output } →
                        root.channel ∉ cfg.names →
                          ∀ {rows : List (Circuit.WeightedRow F)},
                            rows.length ≤ 2 ^ 39 →
                              (∀ (n : ℕ), 0 < n → n ≤ 2 ^ 39 * 2 ^ cfg.bits → ↑n ≠ 0) →
                                plan.checkMemo (Circuit.Erasure.rawROM rom) root rows = Except.ok () →
                                  DecodesValues compiled.specialized.program.enums wires (entryValues args) →
                                    WireValue.decode compiled.specialized.program.enums output = some result →
                                      ∃ value heap calls,
                                        prepared.ObsFn external args value heap calls ∧
                                          Represents (compiled.traceROM rom) heap value result ∧
                                            Generic.SourceSemantics.CallsInROM (compiled.traceROM rom) calls
-/
#guard_msgs in
#check @Aiur.Modules.Prepared.depth_grouped_activated_heap_sound_observed
/--
info: 'Aiur.Modules.Prepared.depth_grouped_activated_heap_sound_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Aiur.Modules.Prepared.depth_grouped_activated_heap_sound_observed

/--
info: @Modules.Prepared.depth_grouped_activated_heap_sound_goldilocks_observed : ∀ {id : String → Except String ℕ}
  {program : Modules.Program Library.U32.Goldilocks.F} (prepared : Modules.Prepared program)
  (compiled : Optimized.ModulesArtifact prepared) (physical : Optimized.Physical.Prepared compiled.circuit.artifact)
  {cfg : Optimized.Depth.Config},
  Optimized.Depth.Certified cfg physical.system →
    cfg.bits = 24 →
      ∀ (plan : Optimized.Grouping.Plan (Optimized.Depth.system cfg physical.system) id),
        plan.WellFormedActivation →
          ∀ {external : String} {entry : Modules.Selection program prepared.environment.assembly.instances},
            prepared.find? external = some entry →
              ∀ {rom : WidthROM Library.U32.Goldilocks.F},
                rom.Valid →
                  ∀ {args : List (SourceValue Library.U32.Goldilocks.F)} {result : Value Library.U32.Goldilocks.F}
                    {wires : List (WireValue Library.U32.Goldilocks.F)} {output : WireValue Library.U32.Goldilocks.F},
                    Circuit.Erasure.Signed compiled.circuit.system
                        { channel := entry.resolved.name, args := wires, result := output } →
                      ∀ {root : Circuit.Message Library.U32.Goldilocks.F},
                        Optimized.Depth.erase cfg root =
                            Circuit.Erasure.message compiled.circuit.system
                              { channel := entry.resolved.name, args := wires, result := output } →
                          root.channel ∉ cfg.names →
                            ∀ {rows : List (Circuit.WeightedRow Library.U32.Goldilocks.F)},
                              rows.length ≤ 2 ^ 39 →
                                plan.checkMemo (Circuit.Erasure.rawROM rom) root rows = Except.ok () →
                                  DecodesValues compiled.specialized.program.enums wires (entryValues args) →
                                    WireValue.decode compiled.specialized.program.enums output = some result →
                                      ∃ value heap calls,
                                        prepared.ObsFn external args value heap calls ∧
                                          Represents (compiled.traceROM rom) heap value result ∧
                                            Generic.SourceSemantics.CallsInROM (compiled.traceROM rom) calls
-/
#guard_msgs in
#check @Aiur.Modules.Prepared.depth_grouped_activated_heap_sound_goldilocks_observed
/--
info: 'Aiur.Modules.Prepared.depth_grouped_activated_heap_sound_goldilocks_observed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Aiur.Modules.Prepared.depth_grouped_activated_heap_sound_goldilocks_observed

/-! ### 4. Standard Library: Carry, U8, U32, U64, Blake3, and Goldilocks -/

/--
info: @Library.Carry.recover : ∀ {F : Type} [inst : Field F] (base n : ℕ),
  ↑base ≠ 0 → (↑n - ↑(n % base)) / ↑base = ↑(n / base)
-/
#guard_msgs in
#check @Aiur.Library.Carry.recover
/-- info: 'Aiur.Library.Carry.recover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Carry.recover

/--
info: @Library.Carry.fullRows_iff : ∀ {F : Type} [inst : Field F] (base count : ℕ),
  ↑base ≠ 0 →
    ∀ (input byte carry : F),
      (input, byte, carry) ∈ Library.Carry.fullRows F base count ↔
        (input, byte) ∈ Library.Carry.fieldRows F base count ∧ carry = (input - byte) / ↑base
-/
#guard_msgs in
#check @Aiur.Library.Carry.fullRows_iff
/-- info: 'Aiur.Library.Carry.fullRows_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Carry.fullRows_iff

/--
info: @Library.Carry.mapEntries_iff : ∀ {F : Type} [inst : Field F] (base count : ℕ),
  ↑base ≠ 0 →
    ∀ (input byte carry : F),
      { args := [Value.field input], result := Value.tuple [Value.field byte, Value.field carry] } ∈
          List.map
            (fun x =>
              match x with
              | (x, lo, hi) => { args := [Value.field x], result := Value.tuple [Value.field lo, Value.field hi] })
            (Library.Carry.fullRows F base count) ↔
        { args := [Value.field input], result := Value.field byte } ∈
            List.map
              (fun x =>
                match x with
                | (x, lo) => { args := [Value.field x], result := Value.field lo })
              (Library.Carry.fieldRows F base count) ∧
          carry = (input - byte) / ↑base
-/
#guard_msgs in
#check @Aiur.Library.Carry.mapEntries_iff
/-- info: 'Aiur.Library.Carry.mapEntries_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Carry.mapEntries_iff

/-- info: Library.U8.nat_xor_and_sum : ∀ (n m : ℕ), n + m = n.xor m + 2 * n.land m -/
#guard_msgs in
#check @Aiur.Library.U8.nat_xor_and_sum
/-- info: 'Aiur.Library.U8.nat_xor_and_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.U8.nat_xor_and_sum

/-- info: Library.U8.nat_xor_or_sum : ∀ (n m : ℕ), 2 * n.lor m = n + m + n.xor m -/
#guard_msgs in
#check @Aiur.Library.U8.nat_xor_or_sum
/-- info: 'Aiur.Library.U8.nat_xor_or_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.U8.nat_xor_or_sum

/-- info: Library.U8.xor_and_sum : ∀ (a b : BitVec 8), a.toNat + b.toNat = (a ^^^ b).toNat + 2 * (a &&& b).toNat -/
#guard_msgs in
#check @Aiur.Library.U8.xor_and_sum
/-- info: 'Aiur.Library.U8.xor_and_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.U8.xor_and_sum

/-- info: Library.U8.xor_or_sum : ∀ (a b : BitVec 8), 2 * (a ||| b).toNat = a.toNat + b.toNat + (a ^^^ b).toNat -/
#guard_msgs in
#check @Aiur.Library.U8.xor_or_sum
/-- info: 'Aiur.Library.U8.xor_or_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.U8.xor_or_sum

/--
info: @Library.U8.and_field : ∀ {F : Type u_1} [inst : Field F],
  2 ≠ 0 → ∀ (a b : BitVec 8), (↑a.toNat + ↑b.toNat - ↑(a ^^^ b).toNat) / 2 = ↑(a &&& b).toNat
-/
#guard_msgs in
#check @Aiur.Library.U8.and_field
/-- info: 'Aiur.Library.U8.and_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.U8.and_field

/--
info: @Library.U8.or_field : ∀ {F : Type u_1} [inst : Field F],
  2 ≠ 0 → ∀ (a b : BitVec 8), (↑a.toNat + ↑b.toNat + ↑(a ^^^ b).toNat) / 2 = ↑(a ||| b).toNat
-/
#guard_msgs in
#check @Aiur.Library.U8.or_field
/-- info: 'Aiur.Library.U8.or_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.U8.or_field

/-- info: @Library.U8Facts.xor_lt_256 : ∀ {a b : ℕ}, a < 256 → b < 256 → a.xor b < 256 -/
#guard_msgs in
#check @Aiur.Library.U8Facts.xor_lt_256
/-- info: 'Aiur.Library.U8Facts.xor_lt_256' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.U8Facts.xor_lt_256

/-- info: Library.U8Facts.xor_and_identity : ∀ (a b : ℕ), a + b = a.xor b + 2 * a.land b -/
#guard_msgs in
#check @Aiur.Library.U8Facts.xor_and_identity
/-- info: 'Aiur.Library.U8Facts.xor_and_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.U8Facts.xor_and_identity

/-- info: Library.U8Facts.xor_or_identity : ∀ (a b : ℕ), 2 * a.lor b = a + b + a.xor b -/
#guard_msgs in
#check @Aiur.Library.U8Facts.xor_or_identity
/-- info: 'Aiur.Library.U8Facts.xor_or_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.U8Facts.xor_or_identity

/-- info: @Library.U8Facts.land_128_div : ∀ {a : ℕ}, a < 256 → a.land 128 / 128 = a / 128 -/
#guard_msgs in
#check @Aiur.Library.U8Facts.land_128_div
/-- info: 'Aiur.Library.U8Facts.land_128_div' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.U8Facts.land_128_div

/--
info: @Library.U32.add_check_iff : ∀ {F : Type} [inst : Field F],
  Library.U32.Compatible F →
    ∀ {sum result : ℕ},
      sum < 2 * Library.U32.base →
        result < Library.U32.base →
          have carry := (↑sum - ↑result) / ↑Library.U32.base;
          carry * (carry - 1) = 0 ↔ result = sum % Library.U32.base
-/
#guard_msgs in
#check @Aiur.Library.U32.add_check_iff
/-- info: 'Aiur.Library.U32.add_check_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.U32.add_check_iff

/--
info: @Library.U32.add3_check_iff : ∀ {F : Type} [inst : Field F],
  Library.U32.Compatible F →
    ∀ {sum result : ℕ},
      sum < 3 * Library.U32.base →
        result < Library.U32.base →
          have carry := (↑sum - ↑result) / ↑Library.U32.base;
          carry * (carry - 1) * (carry - 2) = 0 ↔ result = sum % Library.U32.base
-/
#guard_msgs in
#check @Aiur.Library.U32.add3_check_iff
/-- info: 'Aiur.Library.U32.add3_check_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.U32.add3_check_iff

/--
info: @Library.U32.add_words_check_iff : ∀ {F : Type} [inst : Field F],
  Library.U32.Compatible F →
    ∀ {a b result : ℕ},
      a < Library.U32.base →
        b < Library.U32.base →
          result < Library.U32.base →
            have carry := (↑a + ↑b - ↑result) / ↑Library.U32.base;
            carry * (carry - 1) = 0 ↔ result = (a + b) % Library.U32.base
-/
#guard_msgs in
#check @Aiur.Library.U32.add_words_check_iff
/-- info: 'Aiur.Library.U32.add_words_check_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.U32.add_words_check_iff

/--
info: @Library.U32.add3_words_check_iff : ∀ {F : Type} [inst : Field F],
  Library.U32.Compatible F →
    ∀ {a b c result : ℕ},
      a < Library.U32.base →
        b < Library.U32.base →
          c < Library.U32.base →
            result < Library.U32.base →
              have carry := (↑a + ↑b + ↑c - ↑result) / ↑Library.U32.base;
              carry * (carry - 1) * (carry - 2) = 0 ↔ result = (a + b + c) % Library.U32.base
-/
#guard_msgs in
#check @Aiur.Library.U32.add3_words_check_iff
/-- info: 'Aiur.Library.U32.add3_words_check_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.U32.add3_words_check_iff

/--
info: @Library.U32.sub_sound : ∀ {F : Type} [inst : Field F],
  Library.U32.Compatible F →
    ∀ {a b result : ℕ},
      a < Library.U32.base →
        b < Library.U32.base →
          result < Library.U32.base →
            (have borrow := (↑result + ↑b - ↑a) / ↑Library.U32.base;
              borrow * (borrow - 1) = 0) →
              result = (a + Library.U32.base - b) % Library.U32.base ∧
                (↑result + ↑b - ↑a) / ↑Library.U32.base = if a < b then 1 else 0
-/
#guard_msgs in
#check @Aiur.Library.U32.sub_sound
/-- info: 'Aiur.Library.U32.sub_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.U32.sub_sound

/--
info: @Library.U32.compare_fields_sound : ∀ {F : Type} [inst : Field F],
  Library.U32.Compatible F →
    ∀ (a b : F) {leftWord rightWord difference : ℕ},
      leftWord < Library.U32.base →
        rightWord < Library.U32.base →
          difference < Library.U32.base →
            a = ↑leftWord →
              b = ↑rightWord →
                (have borrow := (↑difference + b - a) / ↑Library.U32.base;
                  borrow * (borrow - 1) = 0) →
                  (↑difference + b - a) / ↑Library.U32.base = if leftWord < rightWord then 1 else 0
-/
#guard_msgs in
#check @Aiur.Library.U32.compare_fields_sound
/-- info: 'Aiur.Library.U32.compare_fields_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.U32.compare_fields_sound

/-- info: Library.U32.Goldilocks.modulus_prime : Nat.Prime Library.U32.Goldilocks.modulus -/
#guard_msgs in
#check @Aiur.Library.U32.Goldilocks.modulus_prime
/-- info: 'Aiur.Library.U32.Goldilocks.modulus_prime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.U32.Goldilocks.modulus_prime

/-- info: Library.U32.Goldilocks.compatible : Library.U32.Compatible Library.U32.Goldilocks.F -/
#guard_msgs in
#check @Aiur.Library.U32.Goldilocks.compatible
/-- info: 'Aiur.Library.U32.Goldilocks.compatible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.U32.Goldilocks.compatible

/--
info: @Library.U64.is_zero_sound : ∀ {F : Type} [inst : Field F],
  Library.U64.Compatible F →
    ∀ {b0 b1 b2 b3 b4 b5 b6 b7 : ℕ},
      b0 < 256 →
        b1 < 256 →
          b2 < 256 →
            b3 < 256 →
              b4 < 256 →
                b5 < 256 →
                  b6 < 256 →
                    b7 < 256 →
                      (↑b0 = 0 ∧ ↑b1 = 0 ∧ ↑b2 = 0 ∧ ↑b3 = 0 ∧ ↑b4 = 0 ∧ ↑b5 = 0 ∧ ↑b6 = 0 ∧ ↑b7 = 0 ↔
                        Library.U64.pack b0 b1 b2 b3 b4 b5 b6 b7 = 0)
-/
#guard_msgs in
#check @Aiur.Library.U64.is_zero_sound
/-- info: 'Aiur.Library.U64.is_zero_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.U64.is_zero_sound

/--
info: @Library.U64.eq_sound : ∀ {F : Type} [inst : Field F],
  Library.U64.Compatible F →
    ∀ {a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : ℕ},
      a0 < 256 →
        a1 < 256 →
          a2 < 256 →
            a3 < 256 →
              a4 < 256 →
                a5 < 256 →
                  a6 < 256 →
                    a7 < 256 →
                      b0 < 256 →
                        b1 < 256 →
                          b2 < 256 →
                            b3 < 256 →
                              b4 < 256 →
                                b5 < 256 →
                                  b6 < 256 →
                                    b7 < 256 →
                                      (↑a0 - ↑b0 = 0 ∧
                                          ↑a1 - ↑b1 = 0 ∧
                                            ↑a2 - ↑b2 = 0 ∧
                                              ↑a3 - ↑b3 = 0 ∧
                                                ↑a4 - ↑b4 = 0 ∧ ↑a5 - ↑b5 = 0 ∧ ↑a6 - ↑b6 = 0 ∧ ↑a7 - ↑b7 = 0 ↔
                                        Library.U64.pack a0 a1 a2 a3 a4 a5 a6 a7 =
                                          Library.U64.pack b0 b1 b2 b3 b4 b5 b6 b7)
-/
#guard_msgs in
#check @Aiur.Library.U64.eq_sound
/-- info: 'Aiur.Library.U64.eq_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.U64.eq_sound

/--
info: @Library.U64.add_sound : ∀
  {a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 s0 s1 s2 s3 s4 s5 s6 s7 c1 c2 c3 c4 c5 c6 c7 c8 : ℕ},
  a0 < 256 →
    a1 < 256 →
      a2 < 256 →
        a3 < 256 →
          a4 < 256 →
            a5 < 256 →
              a6 < 256 →
                a7 < 256 →
                  b0 < 256 →
                    b1 < 256 →
                      b2 < 256 →
                        b3 < 256 →
                          b4 < 256 →
                            b5 < 256 →
                              b6 < 256 →
                                b7 < 256 →
                                  s0 < 256 →
                                    s1 < 256 →
                                      s2 < 256 →
                                        s3 < 256 →
                                          s4 < 256 →
                                            s5 < 256 →
                                              s6 < 256 →
                                                s7 < 256 →
                                                  a0 + b0 = s0 + 256 * c1 →
                                                    a1 + b1 + c1 = s1 + 256 * c2 →
                                                      a2 + b2 + c2 = s2 + 256 * c3 →
                                                        a3 + b3 + c3 = s3 + 256 * c4 →
                                                          a4 + b4 + c4 = s4 + 256 * c5 →
                                                            a5 + b5 + c5 = s5 + 256 * c6 →
                                                              a6 + b6 + c6 = s6 + 256 * c7 →
                                                                a7 + b7 + c7 = s7 + 256 * c8 →
                                                                  Library.U64.pack s0 s1 s2 s3 s4 s5 s6 s7 =
                                                                      (Library.U64.pack a0 a1 a2 a3 a4 a5 a6 a7 +
                                                                          Library.U64.pack b0 b1 b2 b3 b4 b5 b6 b7) %
                                                                        Library.U64.base ∧
                                                                    c8 =
                                                                        (Library.U64.pack a0 a1 a2 a3 a4 a5 a6 a7 +
                                                                            Library.U64.pack b0 b1 b2 b3 b4 b5 b6 b7) /
                                                                          Library.U64.base ∧
                                                                      c8 < 2
-/
#guard_msgs in
#check @Aiur.Library.U64.add_sound
/-- info: 'Aiur.Library.U64.add_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.U64.add_sound

/--
info: @Library.U64.wrapping_succ_sound : ∀ {b0 b1 b2 b3 b4 b5 b6 b7 : ℕ},
  b0 < 256 →
    b1 < 256 →
      b2 < 256 →
        b3 < 256 →
          b4 < 256 →
            b5 < 256 →
              b6 < 256 →
                b7 < 256 →
                  match Library.U64.wrappingSuccBytes b0 b1 b2 b3 b4 b5 b6 b7 with
                  | (r0, r1, r2, r3, r4, r5, r6, r7) =>
                    r0 < 256 ∧
                      r1 < 256 ∧
                        r2 < 256 ∧
                          r3 < 256 ∧
                            r4 < 256 ∧
                              r5 < 256 ∧
                                r6 < 256 ∧
                                  r7 < 256 ∧
                                    Library.U64.pack r0 r1 r2 r3 r4 r5 r6 r7 =
                                      (Library.U64.pack b0 b1 b2 b3 b4 b5 b6 b7 + 1) % Library.U64.base
-/
#guard_msgs in
#check @Aiur.Library.U64.wrapping_succ_sound
/-- info: 'Aiur.Library.U64.wrapping_succ_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.U64.wrapping_succ_sound

/--
info: @Library.U64.wrapping_succ_bytes_sound : ∀ {b0 b1 b2 b3 b4 b5 b6 b7 : ℕ},
  b0 < 256 →
    b1 < 256 →
      b2 < 256 →
        b3 < 256 →
          b4 < 256 →
            b5 < 256 →
              b6 < 256 →
                b7 < 256 →
                  match Library.U64.wrappingSuccBytes b0 b1 b2 b3 b4 b5 b6 b7 with
                  | (r0, r1, r2, r3, r4, r5, r6, r7) =>
                    r0 < 256 ∧
                      r1 < 256 ∧
                        r2 < 256 ∧
                          r3 < 256 ∧
                            r4 < 256 ∧
                              r5 < 256 ∧
                                r6 < 256 ∧
                                  r7 < 256 ∧
                                    Library.U64.pack r0 r1 r2 r3 r4 r5 r6 r7 =
                                      (Library.U64.pack b0 b1 b2 b3 b4 b5 b6 b7 + 1) % Library.U64.base
-/
#guard_msgs in
#check @Aiur.Library.U64.wrapping_succ_bytes_sound
/-- info: 'Aiur.Library.U64.wrapping_succ_bytes_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.U64.wrapping_succ_bytes_sound

/--
info: @Library.U64.saturating_pred_sound : ∀ {b0 b1 b2 b3 b4 b5 b6 b7 : ℕ},
  b0 < 256 →
    b1 < 256 →
      b2 < 256 →
        b3 < 256 →
          b4 < 256 →
            b5 < 256 →
              b6 < 256 →
                b7 < 256 →
                  match Library.U64.saturatingPredBytes b0 b1 b2 b3 b4 b5 b6 b7 with
                  | (r0, r1, r2, r3, r4, r5, r6, r7) =>
                    r0 < 256 ∧
                      r1 < 256 ∧
                        r2 < 256 ∧
                          r3 < 256 ∧
                            r4 < 256 ∧
                              r5 < 256 ∧
                                r6 < 256 ∧
                                  r7 < 256 ∧
                                    Library.U64.pack r0 r1 r2 r3 r4 r5 r6 r7 =
                                      Library.U64.pack b0 b1 b2 b3 b4 b5 b6 b7 - 1
-/
#guard_msgs in
#check @Aiur.Library.U64.saturating_pred_sound
/-- info: 'Aiur.Library.U64.saturating_pred_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.U64.saturating_pred_sound

/--
info: @Library.U64.to_field_sound : ∀ {F : Type} [inst : Field F],
  Library.U64.Compatible F →
    ∀ {b0 b1 b2 b3 b4 b5 b6 b7 : ℕ},
      b0 < 256 →
        b1 < 256 →
          b2 < 256 →
            b3 < 256 →
              b4 < 256 →
                b5 < 256 →
                  b6 < 256 →
                    b7 < 256 →
                      ↑b7 = 0 →
                        Library.U64.pack b0 b1 b2 b3 b4 b5 b6 b7 < Library.U64.fieldBound ∧
                          ↑b0 + 256 * ↑b1 + 65536 * ↑b2 + 16777216 * ↑b3 + 4294967296 * ↑b4 + 1099511627776 * ↑b5 +
                              281474976710656 * ↑b6 =
                            ↑(Library.U64.pack b0 b1 b2 b3 b4 b5 b6 b7)
-/
#guard_msgs in
#check @Aiur.Library.U64.to_field_sound
/-- info: 'Aiur.Library.U64.to_field_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.U64.to_field_sound

/--
info: @Library.U64.sub_with_borrow_sound : ∀ {F : Type} [inst : Field F]
  {a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 s0 s1 s2 s3 s4 s5 s6 s7 c1 c2 c3 c4 c5 c6 c7 c8 : ℕ},
  a0 < 256 →
    a1 < 256 →
      a2 < 256 →
        a3 < 256 →
          a4 < 256 →
            a5 < 256 →
              a6 < 256 →
                a7 < 256 →
                  b0 < 256 →
                    b1 < 256 →
                      b2 < 256 →
                        b3 < 256 →
                          b4 < 256 →
                            b5 < 256 →
                              b6 < 256 →
                                b7 < 256 →
                                  s0 < 256 →
                                    s1 < 256 →
                                      s2 < 256 →
                                        s3 < 256 →
                                          s4 < 256 →
                                            s5 < 256 →
                                              s6 < 256 →
                                                s7 < 256 →
                                                  a0 + 256 - b0 = s0 + 256 * c1 →
                                                    a1 + 255 - b1 + c1 = s1 + 256 * c2 →
                                                      a2 + 255 - b2 + c2 = s2 + 256 * c3 →
                                                        a3 + 255 - b3 + c3 = s3 + 256 * c4 →
                                                          a4 + 255 - b4 + c4 = s4 + 256 * c5 →
                                                            a5 + 255 - b5 + c5 = s5 + 256 * c6 →
                                                              a6 + 255 - b6 + c6 = s6 + 256 * c7 →
                                                                a7 + 255 - b7 + c7 = s7 + 256 * c8 →
                                                                  Library.U64.pack s0 s1 s2 s3 s4 s5 s6 s7 =
                                                                      (Library.U64.pack a0 a1 a2 a3 a4 a5 a6 a7 +
                                                                            Library.U64.base -
                                                                          Library.U64.pack b0 b1 b2 b3 b4 b5 b6 b7) %
                                                                        Library.U64.base ∧
                                                                    1 - ↑c8 =
                                                                      if
                                                                          Library.U64.pack a0 a1 a2 a3 a4 a5 a6 a7 <
                                                                            Library.U64.pack b0 b1 b2 b3 b4 b5 b6
                                                                              b7 then
                                                                        1
                                                                      else 0
-/
#guard_msgs in
#check @Aiur.Library.U64.sub_with_borrow_sound
/-- info: 'Aiur.Library.U64.sub_with_borrow_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.U64.sub_with_borrow_sound

/--
info: @Library.U64.mul_column_sound : ∀ {F : Type} [inst : Field F],
  Library.U64.Compatible F →
    ∀ {val r0 r1 c0 c1 c2 : ℕ},
      val < Library.U64.fieldBound →
        r0 < 256 →
          r1 < 256 →
            c0 < 256 →
              c1 < 256 →
                c2 < 256 →
                  ↑val = ↑r0 + 256 * ↑r1 + 65536 * (↑c0 + 256 * ↑c1 + 65536 * ↑c2) →
                    val = Library.U64.limb2 r0 r1 + 65536 * Library.U64.carry3 c0 c1 c2 ∧
                      Library.U64.limb2 r0 r1 = val % 65536 ∧ Library.U64.carry3 c0 c1 c2 = val / 65536
-/
#guard_msgs in
#check @Aiur.Library.U64.mul_column_sound
/-- info: 'Aiur.Library.U64.mul_column_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.U64.mul_column_sound

/--
info: @Library.U64.mul_sound : ∀
  {a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 r00 r01 r10 r11 r20 r21 r30 r31 r40 r41 r50 r51 r60 r61 c00 c01 c02
    c10 c11 c12 c20 c21 c22 c30 c31 c32 c40 c41 c42 c50 c51 c52 c60 c61 c62 : ℕ},
  r00 < 256 →
    r01 < 256 →
      r10 < 256 →
        r11 < 256 →
          r20 < 256 →
            r21 < 256 →
              r30 < 256 →
                r31 < 256 →
                  r40 < 256 →
                    r41 < 256 →
                      r50 < 256 →
                        r51 < 256 →
                          r60 < 256 →
                            r61 < 256 →
                              c60 < 256 →
                                c61 < 256 →
                                  Library.U64.limb2 a0 a1 * Library.U64.limb2 b0 b1 =
                                      Library.U64.limb2 r00 r01 + 65536 * Library.U64.carry3 c00 c01 c02 →
                                    Library.U64.limb2 a0 a1 * Library.U64.limb2 b2 b3 +
                                            Library.U64.limb2 a2 a3 * Library.U64.limb2 b0 b1 +
                                          Library.U64.carry3 c00 c01 c02 =
                                        Library.U64.limb2 r10 r11 + 65536 * Library.U64.carry3 c10 c11 c12 →
                                      Library.U64.limb2 a0 a1 * Library.U64.limb2 b4 b5 +
                                                Library.U64.limb2 a2 a3 * Library.U64.limb2 b2 b3 +
                                              Library.U64.limb2 a4 a5 * Library.U64.limb2 b0 b1 +
                                            Library.U64.carry3 c10 c11 c12 =
                                          Library.U64.limb2 r20 r21 + 65536 * Library.U64.carry3 c20 c21 c22 →
                                        Library.U64.limb2 a0 a1 * Library.U64.limb2 b6 b7 +
                                                    Library.U64.limb2 a2 a3 * Library.U64.limb2 b4 b5 +
                                                  Library.U64.limb2 a4 a5 * Library.U64.limb2 b2 b3 +
                                                Library.U64.limb2 a6 a7 * Library.U64.limb2 b0 b1 +
                                              Library.U64.carry3 c20 c21 c22 =
                                            Library.U64.limb2 r30 r31 + 65536 * Library.U64.carry3 c30 c31 c32 →
                                          Library.U64.limb2 a2 a3 * Library.U64.limb2 b6 b7 +
                                                    Library.U64.limb2 a4 a5 * Library.U64.limb2 b4 b5 +
                                                  Library.U64.limb2 a6 a7 * Library.U64.limb2 b2 b3 +
                                                Library.U64.carry3 c30 c31 c32 =
                                              Library.U64.limb2 r40 r41 + 65536 * Library.U64.carry3 c40 c41 c42 →
                                            Library.U64.limb2 a4 a5 * Library.U64.limb2 b6 b7 +
                                                    Library.U64.limb2 a6 a7 * Library.U64.limb2 b4 b5 +
                                                  Library.U64.carry3 c40 c41 c42 =
                                                Library.U64.limb2 r50 r51 + 65536 * Library.U64.carry3 c50 c51 c52 →
                                              Library.U64.limb2 a6 a7 * Library.U64.limb2 b6 b7 +
                                                    Library.U64.carry3 c50 c51 c52 =
                                                  Library.U64.limb2 r60 r61 + 65536 * Library.U64.carry3 c60 c61 c62 →
                                                c62 = 0 →
                                                  have a := Library.U64.pack a0 a1 a2 a3 a4 a5 a6 a7;
                                                  have b := Library.U64.pack b0 b1 b2 b3 b4 b5 b6 b7;
                                                  have lo := Library.U64.pack r00 r01 r10 r11 r20 r21 r30 r31;
                                                  have hi := Library.U64.pack r40 r41 r50 r51 r60 r61 c60 c61;
                                                  a * b = lo + Library.U64.base * hi ∧
                                                    lo = a * b % Library.U64.base ∧
                                                      hi = a * b / Library.U64.base ∧ hi < Library.U64.base
-/
#guard_msgs in
#check @Aiur.Library.U64.mul_sound
/-- info: 'Aiur.Library.U64.mul_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.U64.mul_sound

/--
info: @Library.U64.and_sound : ∀ {F : Type} [inst : Field F],
  Library.U64.Compatible F →
    ∀ {a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : ℕ},
      a0 < 256 →
        a1 < 256 →
          a2 < 256 →
            a3 < 256 →
              a4 < 256 →
                a5 < 256 →
                  a6 < 256 →
                    a7 < 256 →
                      b0 < 256 →
                        b1 < 256 →
                          b2 < 256 →
                            b3 < 256 →
                              b4 < 256 →
                                b5 < 256 →
                                  b6 < 256 →
                                    b7 < 256 →
                                      (↑a0 + ↑b0 - ↑(a0.xor b0)) / 2 = ↑(a0.land b0) ∧
                                        Library.U64.pack (a0.land b0) (a1.land b1) (a2.land b2) (a3.land b3)
                                            (a4.land b4) (a5.land b5) (a6.land b6) (a7.land b7) =
                                          (Library.U64.pack a0 a1 a2 a3 a4 a5 a6 a7).land
                                            (Library.U64.pack b0 b1 b2 b3 b4 b5 b6 b7)
-/
#guard_msgs in
#check @Aiur.Library.U64.and_sound
/-- info: 'Aiur.Library.U64.and_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.U64.and_sound

/--
info: @Library.U64.or_sound : ∀ {F : Type} [inst : Field F],
  Library.U64.Compatible F →
    ∀ {a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : ℕ},
      a0 < 256 →
        a1 < 256 →
          a2 < 256 →
            a3 < 256 →
              a4 < 256 →
                a5 < 256 →
                  a6 < 256 →
                    a7 < 256 →
                      b0 < 256 →
                        b1 < 256 →
                          b2 < 256 →
                            b3 < 256 →
                              b4 < 256 →
                                b5 < 256 →
                                  b6 < 256 →
                                    b7 < 256 →
                                      (↑a0 + ↑b0 + ↑(a0.xor b0)) / 2 = ↑(a0.lor b0) ∧
                                        Library.U64.pack (a0.lor b0) (a1.lor b1) (a2.lor b2) (a3.lor b3) (a4.lor b4)
                                            (a5.lor b5) (a6.lor b6) (a7.lor b7) =
                                          (Library.U64.pack a0 a1 a2 a3 a4 a5 a6 a7).lor
                                            (Library.U64.pack b0 b1 b2 b3 b4 b5 b6 b7)
-/
#guard_msgs in
#check @Aiur.Library.U64.or_sound
/-- info: 'Aiur.Library.U64.or_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.U64.or_sound

/--
info: @Library.U64.xor_sound : ∀ {a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : ℕ},
  a0 < 256 →
    a1 < 256 →
      a2 < 256 →
        a3 < 256 →
          a4 < 256 →
            a5 < 256 →
              a6 < 256 →
                a7 < 256 →
                  b0 < 256 →
                    b1 < 256 →
                      b2 < 256 →
                        b3 < 256 →
                          b4 < 256 →
                            b5 < 256 →
                              b6 < 256 →
                                b7 < 256 →
                                  Library.U64.pack (a0.xor b0) (a1.xor b1) (a2.xor b2) (a3.xor b3) (a4.xor b4)
                                      (a5.xor b5) (a6.xor b6) (a7.xor b7) =
                                    (Library.U64.pack a0 a1 a2 a3 a4 a5 a6 a7).xor
                                      (Library.U64.pack b0 b1 b2 b3 b4 b5 b6 b7)
-/
#guard_msgs in
#check @Aiur.Library.U64.xor_sound
/-- info: 'Aiur.Library.U64.xor_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.U64.xor_sound

/--
info: @Library.U64.from_field_sound : ∀ {F : Type} [inst : Field F],
  Library.U64.Compatible F →
    ∀ {value : F} {b0 b1 b2 b3 b4 b5 b6 b7 : ℕ},
      b0 < 256 →
        b1 < 256 →
          b2 < 256 →
            b3 < 256 →
              b4 < 256 →
                b5 < 256 →
                  b6 < 256 →
                    b7 < 256 →
                      ↑b7 = 0 →
                        ↑b0 + 256 * ↑b1 + 65536 * ↑b2 + 16777216 * ↑b3 + 4294967296 * ↑b4 + 1099511627776 * ↑b5 +
                              281474976710656 * ↑b6 =
                            value →
                          b7 = 0 ∧
                            Library.U64.pack b0 b1 b2 b3 b4 b5 b6 b7 < Library.U64.fieldBound ∧
                              ↑(Library.U64.pack b0 b1 b2 b3 b4 b5 b6 b7) = value
-/
#guard_msgs in
#check @Aiur.Library.U64.from_field_sound
/-- info: 'Aiur.Library.U64.from_field_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.U64.from_field_sound

/--
info: @Library.U64.from_field_unique : ∀ {F : Type} [inst : Field F],
  Library.U64.Compatible F →
    ∀ {n : ℕ},
      n < Library.U64.fieldBound →
        ∀ {b0 b1 b2 b3 b4 b5 b6 b7 : ℕ},
          b0 < 256 →
            b1 < 256 →
              b2 < 256 →
                b3 < 256 →
                  b4 < 256 →
                    b5 < 256 →
                      b6 < 256 →
                        b7 < 256 →
                          ↑b7 = 0 →
                            ↑b0 + 256 * ↑b1 + 65536 * ↑b2 + 16777216 * ↑b3 + 4294967296 * ↑b4 + 1099511627776 * ↑b5 +
                                  281474976710656 * ↑b6 =
                                ↑n →
                              Library.U64.pack b0 b1 b2 b3 b4 b5 b6 b7 = n
-/
#guard_msgs in
#check @Aiur.Library.U64.from_field_unique
/-- info: 'Aiur.Library.U64.from_field_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.U64.from_field_unique

/-- info: Library.U64.Goldilocks.compatible : Library.U64.Compatible Library.U64.Goldilocks.F -/
#guard_msgs in
#check @Aiur.Library.U64.Goldilocks.compatible
/-- info: 'Aiur.Library.U64.Goldilocks.compatible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.U64.Goldilocks.compatible

/--
info: Library.Blake3.iv_spec : #v[Library.Blake3.wordOfBytes 103 230 9 106, Library.Blake3.wordOfBytes 133 174 103 187,
    Library.Blake3.wordOfBytes 114 243 110 60, Library.Blake3.wordOfBytes 58 245 79 165,
    Library.Blake3.wordOfBytes 127 82 14 81, Library.Blake3.wordOfBytes 140 104 5 155,
    Library.Blake3.wordOfBytes 171 217 131 31, Library.Blake3.wordOfBytes 25 205 224 91] =
  Library.Blake3.iv
-/
#guard_msgs in
#check @Aiur.Library.Blake3.iv_spec
/-- info: 'Aiur.Library.Blake3.iv_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Blake3.iv_spec

/--
info: Library.Blake3.rotr8_spec : ∀ (b0 b1 b2 b3 : UInt8),
  Library.Blake3.rotateRight (Library.Blake3.wordOfBytes b0 b1 b2 b3) 8 = Library.Blake3.wordOfBytes b1 b2 b3 b0
-/
#guard_msgs in
#check @Aiur.Library.Blake3.rotr8_spec
/-- info: 'Aiur.Library.Blake3.rotr8_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Blake3.rotr8_spec

/--
info: Library.Blake3.rotr16_spec : ∀ (b0 b1 b2 b3 : UInt8),
  Library.Blake3.rotateRight (Library.Blake3.wordOfBytes b0 b1 b2 b3) 16 = Library.Blake3.wordOfBytes b2 b3 b0 b1
-/
#guard_msgs in
#check @Aiur.Library.Blake3.rotr16_spec
/-- info: 'Aiur.Library.Blake3.rotr16_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Blake3.rotr16_spec

/--
info: Library.Blake3.xor_spec : ∀ (a0 a1 a2 a3 b0 b1 b2 b3 : UInt8),
  Library.Blake3.wordOfBytes a0 a1 a2 a3 ^^^ Library.Blake3.wordOfBytes b0 b1 b2 b3 =
    Library.Blake3.wordOfBytes (a0 ^^^ b0) (a1 ^^^ b1) (a2 ^^^ b2) (a3 ^^^ b3)
-/
#guard_msgs in
#check @Aiur.Library.Blake3.xor_spec
/-- info: 'Aiur.Library.Blake3.xor_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Blake3.xor_spec

/--
info: Library.Blake3.xor_rotr12_spec : ∀ (a0 a1 a2 a3 b0 b1 b2 b3 : UInt8),
  have x0 := (a0 ^^^ b0).toNat;
  have x1 := (a1 ^^^ b1).toNat;
  have x2 := (a2 ^^^ b2).toNat;
  have x3 := (a3 ^^^ b3).toNat;
  have r0 := UInt8.ofNat (x1 / 16 + x2 % 16 * 16);
  have r1 := UInt8.ofNat (x2 / 16 + x3 % 16 * 16);
  have r2 := UInt8.ofNat (x3 / 16 + x0 % 16 * 16);
  have r3 := UInt8.ofNat (x0 / 16 + x1 % 16 * 16);
  Library.Blake3.rotateRight (Library.Blake3.wordOfBytes a0 a1 a2 a3 ^^^ Library.Blake3.wordOfBytes b0 b1 b2 b3) 12 =
    Library.Blake3.wordOfBytes r0 r1 r2 r3
-/
#guard_msgs in
#check @Aiur.Library.Blake3.xor_rotr12_spec
/-- info: 'Aiur.Library.Blake3.xor_rotr12_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Blake3.xor_rotr12_spec

/--
info: Library.Blake3.xor_rotr7_spec : ∀ (a0 a1 a2 a3 b0 b1 b2 b3 : UInt8),
  have x0 := (a0 ^^^ b0).toNat;
  have x1 := (a1 ^^^ b1).toNat;
  have x2 := (a2 ^^^ b2).toNat;
  have x3 := (a3 ^^^ b3).toNat;
  have r0 := UInt8.ofNat (x0 / 128 + x1 % 128 * 2);
  have r1 := UInt8.ofNat (x1 / 128 + x2 % 128 * 2);
  have r2 := UInt8.ofNat (x2 / 128 + x3 % 128 * 2);
  have r3 := UInt8.ofNat (x3 / 128 + x0 % 128 * 2);
  Library.Blake3.rotateRight (Library.Blake3.wordOfBytes a0 a1 a2 a3 ^^^ Library.Blake3.wordOfBytes b0 b1 b2 b3) 7 =
    Library.Blake3.wordOfBytes r0 r1 r2 r3
-/
#guard_msgs in
#check @Aiur.Library.Blake3.xor_rotr7_spec
/-- info: 'Aiur.Library.Blake3.xor_rotr7_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Blake3.xor_rotr7_spec

/--
info: Library.Blake3.g_function_spec : ∀ (a b c d mx my : UInt32),
  have a1 := a + b + mx;
  have d1 := Library.Blake3.rotateRight (d ^^^ a1) 16;
  have c1 := c + d1;
  have b1 := Library.Blake3.rotateRight (b ^^^ c1) 12;
  have a2 := a1 + b1 + my;
  have d2 := Library.Blake3.rotateRight (d1 ^^^ a2) 8;
  have c2 := c1 + d2;
  have b2 := Library.Blake3.rotateRight (b1 ^^^ c2) 7;
  #v[a2, b2, c2, d2] = Library.Blake3.mix a b c d mx my
-/
#guard_msgs in
#check @Aiur.Library.Blake3.g_function_spec
/-- info: 'Aiur.Library.Blake3.g_function_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Blake3.g_function_spec

/--
info: Library.Blake3.g_spec : ∀ (state : Library.Blake3.Block) (j : Fin 8) (mx my : UInt32),
  (match ↑j with
    | 0 => Library.Blake3.g state 0 4 8 12 mx my
    | 1 => Library.Blake3.g state 1 5 9 13 mx my
    | 2 => Library.Blake3.g state 2 6 10 14 mx my
    | 3 => Library.Blake3.g state 3 7 11 15 mx my
    | 4 => Library.Blake3.g state 0 5 10 15 mx my
    | 5 => Library.Blake3.g state 1 6 11 12 mx my
    | 6 => Library.Blake3.g state 2 7 8 13 mx my
    | x => Library.Blake3.g state 3 4 9 14 mx my) =
    have cols :=
      #v[(0, 4, 8, 12), (1, 5, 9, 13), (2, 6, 10, 14), (3, 7, 11, 15), (0, 5, 10, 15), (1, 6, 11, 12), (2, 7, 8, 13),
        (3, 4, 9, 14)];
    match cols[j] with
    | (a, b, c, d) => Library.Blake3.g state a b c d mx my
-/
#guard_msgs in
#check @Aiur.Library.Blake3.g_spec
/-- info: 'Aiur.Library.Blake3.g_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Blake3.g_spec

/--
info: Library.Blake3.round_spec : ∀ (state m : Library.Blake3.Block),
  Library.Blake3.compressInnerJ state m = Library.Blake3.round state m Library.Blake3.schedules[0]
-/
#guard_msgs in
#check @Aiur.Library.Blake3.round_spec
/-- info: 'Aiur.Library.Blake3.round_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Blake3.round_spec

/--
info: Library.Blake3.permute_spec : ∀ (m : Library.Blake3.Block) (r : Fin 7) (k : Fin 16),
  (Library.Blake3.permute^[↑r] m)[↑k] = m[Library.Blake3.schedules[r][↑k]]
-/
#guard_msgs in
#check @Aiur.Library.Blake3.permute_spec
/-- info: 'Aiur.Library.Blake3.permute_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Blake3.permute_spec

/--
info: Library.Blake3.compress_inner_i_spec : ∀ (state m : Library.Blake3.Block),
  Library.Blake3.compressInnerI state m =
    Vector.foldl (fun s sched => Library.Blake3.round s m sched) state Library.Blake3.schedules
-/
#guard_msgs in
#check @Aiur.Library.Blake3.compress_inner_i_spec
/-- info: 'Aiur.Library.Blake3.compress_inner_i_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Blake3.compress_inner_i_spec

/--
info: Library.Blake3.counter_split_spec : ∀ (c0 c1 c2 c3 c4 c5 c6 c7 : UInt8),
  have counter :=
    UInt64.ofNat (Library.U64.pack c0.toNat c1.toNat c2.toNat c3.toNat c4.toNat c5.toNat c6.toNat c7.toNat);
  counter.toUInt32 = Library.Blake3.wordOfBytes c0 c1 c2 c3 ∧
    (counter >>> 32).toUInt32 = Library.Blake3.wordOfBytes c4 c5 c6 c7
-/
#guard_msgs in
#check @Aiur.Library.Blake3.counter_split_spec
/-- info: 'Aiur.Library.Blake3.counter_split_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Blake3.counter_split_spec

/--
info: Library.Blake3.compress_spec : ∀ (cv : Library.Blake3.CV) (message : Library.Blake3.Block) (counter : UInt64)
  (blockLen flags : UInt32),
  Library.Blake3.finalizeState
      (Library.Blake3.compressInnerI (Library.Blake3.initialWords cv counter blockLen flags) message) =
    Library.Blake3.compress cv message counter blockLen flags
-/
#guard_msgs in
#check @Aiur.Library.Blake3.compress_spec
/-- info: 'Aiur.Library.Blake3.compress_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Blake3.compress_spec

/--
info: Library.Blake3.pad_block_spec : ∀ (acc : List UInt8),
  (Library.Blake3.padBlock acc.reverse acc.length).reverse = acc ++ List.replicate (64 - acc.length) 0
-/
#guard_msgs in
#check @Aiur.Library.Blake3.pad_block_spec
/-- info: 'Aiur.Library.Blake3.pad_block_spec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.Blake3.pad_block_spec

/--
info: Library.Blake3.bytes_to_block_spec : ∀ (acc : List UInt8),
  acc.length ≤ 64 →
    Library.Blake3.blockWords (acc ++ List.replicate (64 - acc.length) 0) = Library.Blake3.blockWords acc
-/
#guard_msgs in
#check @Aiur.Library.Blake3.bytes_to_block_spec
/-- info: 'Aiur.Library.Blake3.bytes_to_block_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Blake3.bytes_to_block_spec

/--
info: Library.Blake3.chunk_single_root_spec : ∀ (input : List UInt8),
  input.length ≤ 1024 → (Library.Blake3.chunkOutput 0 input).rootHash = Library.Blake3.digest input
-/
#guard_msgs in
#check @Aiur.Library.Blake3.chunk_single_root_spec
/-- info: 'Aiur.Library.Blake3.chunk_single_root_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Blake3.chunk_single_root_spec

/--
info: Library.Blake3.next_layer_pair_spec : ∀ (left right : Library.Blake3.CV) (rest : List Library.Blake3.CV),
  Library.Blake3.nextLayer (left :: right :: rest) =
    Library.Blake3.compress Library.Blake3.iv (left ++ right) 0 64 4 :: Library.Blake3.nextLayer rest
-/
#guard_msgs in
#check @Aiur.Library.Blake3.next_layer_pair_spec
/-- info: 'Aiur.Library.Blake3.next_layer_pair_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Blake3.next_layer_pair_spec

/--
info: Library.Blake3.compress_layer_two_spec : ∀ (left right : Library.Blake3.CV),
  Library.Blake3.cvBytes (Library.Blake3.compressLayer [left, right]) =
    (Library.Blake3.parentOutput left right).rootHash
-/
#guard_msgs in
#check @Aiur.Library.Blake3.compress_layer_two_spec
/-- info: 'Aiur.Library.Blake3.compress_layer_two_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Blake3.compress_layer_two_spec

/--
info: Library.Blake3.compress_layer_step_spec : ∀ (left right c : Library.Blake3.CV) (rest : List Library.Blake3.CV),
  Library.Blake3.compressLayer (left :: right :: c :: rest) =
    Library.Blake3.compressLayer (Library.Blake3.nextLayer (left :: right :: c :: rest))
-/
#guard_msgs in
#check @Aiur.Library.Blake3.compress_layer_step_spec
/-- info: 'Aiur.Library.Blake3.compress_layer_step_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Blake3.compress_layer_step_spec

/--
info: Library.Blake3.digest_bytes_spec : ∀ (cv : Library.Blake3.CV) (i : Fin 32),
  (Library.Blake3.cvBytes cv)[i] = (Library.Blake3.wordBytes cv[↑i / 4])[↑i % 4]
-/
#guard_msgs in
#check @Aiur.Library.Blake3.digest_bytes_spec
/-- info: 'Aiur.Library.Blake3.digest_bytes_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Blake3.digest_bytes_spec

/--
info: @Library.Blake3.cvBytes_inj : ∀ {cv1 cv2 : Library.Blake3.CV},
  Library.Blake3.cvBytes cv1 = Library.Blake3.cvBytes cv2 → cv1 = cv2
-/
#guard_msgs in
#check @Aiur.Library.Blake3.cvBytes_inj
/-- info: 'Aiur.Library.Blake3.cvBytes_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Blake3.cvBytes_inj

/--
info: @Library.Blake3.pack_digest_inj : ∀ {F : Type} [inst : Field F],
  Library.U32.Compatible F → Function.Injective (Library.Blake3.packDigest F)
-/
#guard_msgs in
#check @Aiur.Library.Blake3.pack_digest_inj
/-- info: 'Aiur.Library.Blake3.pack_digest_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Blake3.pack_digest_inj

/--
info: @Library.Blake3.address_to_fields_inj : ∀ {F : Type} [inst : Field F],
  Library.U32.Compatible F → Function.Injective (Library.Blake3.addressToFields F)
-/
#guard_msgs in
#check @Aiur.Library.Blake3.address_to_fields_inj
/-- info: 'Aiur.Library.Blake3.address_to_fields_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Blake3.address_to_fields_inj

/--
info: @Library.Blake3.verify_bytes_against_iff : ∀ {F : Type} [inst : Field F],
  Library.U32.Compatible F →
    ∀ (bytes : List UInt8) (expectedAddr : Library.Blake3.Digest),
      Library.Blake3.addressToFields F (Library.Blake3.digest bytes) = Library.Blake3.addressToFields F expectedAddr ↔
        Library.Blake3.digest bytes = expectedAddr
-/
#guard_msgs in
#check @Aiur.Library.Blake3.verify_bytes_against_iff
/-- info: 'Aiur.Library.Blake3.verify_bytes_against_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Blake3.verify_bytes_against_iff

/-- info: Library.Blake3.Goldilocks.u64_compatible : Library.U64.Compatible Library.U32.Goldilocks.F -/
#guard_msgs in
#check @Aiur.Library.Blake3.Goldilocks.u64_compatible
/-- info: 'Aiur.Library.Blake3.Goldilocks.u64_compatible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Blake3.Goldilocks.u64_compatible

/-! ### 5. Heap Monotonicity (`Aiur.HeapMono`) -/

/-- info: @Heap.Extends.refl : ∀ {F : Type} (h : Heap F), h.Extends h -/
#guard_msgs in
#check @Aiur.Heap.Extends.refl
/-- info: 'Aiur.Heap.Extends.refl' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Heap.Extends.refl

/-- info: @Heap.Extends.trans : ∀ {F : Type} {h₁ h₂ h₃ : Heap F}, h₁.Extends h₂ → h₂.Extends h₃ → h₁.Extends h₃ -/
#guard_msgs in
#check @Aiur.Heap.Extends.trans
/-- info: 'Aiur.Heap.Extends.trans' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Heap.Extends.trans

/-- info: @Heap.Extends.length_le : ∀ {F : Type} {h₁ h₂ : Heap F}, h₁.Extends h₂ → List.length h₁ ≤ List.length h₂ -/
#guard_msgs in
#check @Aiur.Heap.Extends.length_le
/-- info: 'Aiur.Heap.Extends.length_le' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Heap.Extends.length_le

/--
info: @Heap.Extends.getElem?_eq : ∀ {F : Type} {h₁ h₂ : Heap F} {i : ℕ} {v : SourceValue F},
  h₁.Extends h₂ → h₁[i]? = some v → h₂[i]? = some v
-/
#guard_msgs in
#check @Aiur.Heap.Extends.getElem?_eq
/-- info: 'Aiur.Heap.Extends.getElem?_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Heap.Extends.getElem?_eq

/--
info: @Heap.Extends.loadValue_eq : ∀ {F : Type} {h₁ h₂ : Heap F} {ptr v : SourceValue F},
  h₁.Extends h₂ → loadValue h₁ ptr = Except.ok v → loadValue h₂ ptr = Except.ok v
-/
#guard_msgs in
#check @Aiur.Heap.Extends.loadValue_eq
/-- info: 'Aiur.Heap.Extends.loadValue_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Heap.Extends.loadValue_eq

/--
info: @EvalExpr.heap_extends : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F}
  {locals : Environment F ℕ} {expr : Expr F} {before after : Heap F} {value : SourceValue F},
  EvalExpr program locals expr before value after → before.Extends after
-/
#guard_msgs in
#check @Aiur.EvalExpr.heap_extends
/-- info: 'Aiur.EvalExpr.heap_extends' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.EvalExpr.heap_extends

/--
info: @EvalArgs.heap_extends : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F}
  {locals : Environment F ℕ} {exprs : List (Expr F)} {before after : Heap F} {values : List (SourceValue F)},
  EvalArgs program locals exprs before values after → before.Extends after
-/
#guard_msgs in
#check @Aiur.EvalArgs.heap_extends
/-- info: 'Aiur.EvalArgs.heap_extends' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.EvalArgs.heap_extends

/--
info: @EvalFn.heap_extends : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F} {name : String}
  {args : List (SourceValue F)} {before after : Heap F} {value : SourceValue F},
  EvalFn program name args before value after → before.Extends after
-/
#guard_msgs in
#check @Aiur.EvalFn.heap_extends
/-- info: 'Aiur.EvalFn.heap_extends' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.EvalFn.heap_extends

/--
info: @Generic.SourceSemantics.EvalExpr.heap_extends : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {world : Generic.SourceSemantics.World F} {types : Generic.SourceSemantics.Types} {locals : Environment F ℕ}
  {expr : Generic.Expr F} {before after : Heap F} {result : SourceValue F},
  Generic.SourceSemantics.EvalExpr world types locals expr before result after → before.Extends after
-/
#guard_msgs in
#check @Aiur.Generic.SourceSemantics.EvalExpr.heap_extends
/-- info: 'Aiur.Generic.SourceSemantics.EvalExpr.heap_extends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.SourceSemantics.EvalExpr.heap_extends

/--
info: @Generic.SourceSemantics.EvalArgs.heap_extends : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {world : Generic.SourceSemantics.World F} {types : Generic.SourceSemantics.Types} {locals : Environment F ℕ}
  {exprs : List (Generic.Expr F)} {before after : Heap F} {values : List (SourceValue F)},
  Generic.SourceSemantics.EvalArgs world types locals exprs before values after → before.Extends after
-/
#guard_msgs in
#check @Aiur.Generic.SourceSemantics.EvalArgs.heap_extends
/-- info: 'Aiur.Generic.SourceSemantics.EvalArgs.heap_extends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.SourceSemantics.EvalArgs.heap_extends

/--
info: @Generic.SourceSemantics.EvalExit.heap_extends : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {world : Generic.SourceSemantics.World F} {types : Generic.SourceSemantics.Types} {locals : Environment F ℕ}
  {expr : Generic.Expr F} {before after : Heap F} {target : Generic.ExitTarget} {result : SourceValue F},
  Generic.SourceSemantics.EvalExit world types locals expr before target result after → before.Extends after
-/
#guard_msgs in
#check @Aiur.Generic.SourceSemantics.EvalExit.heap_extends
/-- info: 'Aiur.Generic.SourceSemantics.EvalExit.heap_extends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.SourceSemantics.EvalExit.heap_extends

/--
info: @Generic.SourceSemantics.EvalFn.heap_extends : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {world : Generic.SourceSemantics.World F} {name : String} {args : List (SourceValue F)} {before after : Heap F}
  {result : SourceValue F}, Generic.SourceSemantics.EvalFn world name args before result after → before.Extends after
-/
#guard_msgs in
#check @Aiur.Generic.SourceSemantics.EvalFn.heap_extends
/-- info: 'Aiur.Generic.SourceSemantics.EvalFn.heap_extends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.SourceSemantics.EvalFn.heap_extends

/--
info: @Generic.SourceSemantics.EvalArgsExit.heap_extends : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {world : Generic.SourceSemantics.World F} {types : Generic.SourceSemantics.Types} {locals : Environment F ℕ}
  {exprs : List (Generic.Expr F)} {before after : Heap F} {target : Generic.ExitTarget} {result : SourceValue F},
  Generic.SourceSemantics.EvalArgsExit world types locals exprs before target result after → before.Extends after
-/
#guard_msgs in
#check @Aiur.Generic.SourceSemantics.EvalArgsExit.heap_extends
/-- info: 'Aiur.Generic.SourceSemantics.EvalArgsExit.heap_extends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.SourceSemantics.EvalArgsExit.heap_extends

/--
info: @Generic.SourceSemantics.EvalList.heap_extends : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {world : Generic.SourceSemantics.World F} {types : Generic.SourceSemantics.Types} {locals : Environment F ℕ}
  {exprs : List (Generic.Expr F)} {before after : Heap F} {values : List (SourceValue F)},
  Generic.SourceSemantics.EvalList world types locals exprs before values after → before.Extends after
-/
#guard_msgs in
#check @Aiur.Generic.SourceSemantics.EvalList.heap_extends
/-- info: 'Aiur.Generic.SourceSemantics.EvalList.heap_extends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.SourceSemantics.EvalList.heap_extends

/--
info: @Generic.SourceSemantics.EvalFields.heap_extends : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {world : Generic.SourceSemantics.World F} {types : Generic.SourceSemantics.Types} {locals : Environment F ℕ}
  {exprs : List (Generic.Expr F)} {before after : Heap F} {values : List (SourceValue F)},
  Generic.SourceSemantics.EvalFields world types locals exprs before values after → before.Extends after
-/
#guard_msgs in
#check @Aiur.Generic.SourceSemantics.EvalFields.heap_extends
/-- info: 'Aiur.Generic.SourceSemantics.EvalFields.heap_extends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.SourceSemantics.EvalFields.heap_extends

/--
info: @Generic.SourceSemantics.EvalPath.heap_extends : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {world : Generic.SourceSemantics.World F} {types : Generic.SourceSemantics.Types} {locals : Environment F ℕ}
  {exprs : List (Generic.Expr F)} {before after : Heap F} {values : List (SourceValue F)},
  Generic.SourceSemantics.EvalPath world types locals exprs before values after → before.Extends after
-/
#guard_msgs in
#check @Aiur.Generic.SourceSemantics.EvalPath.heap_extends
/-- info: 'Aiur.Generic.SourceSemantics.EvalPath.heap_extends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.SourceSemantics.EvalPath.heap_extends

/-- info: @HeapMono.const : ∀ {F : Type} {α : Type u_1} (Q : α → Prop), HeapMono fun x x_1 => Q x_1 -/
#guard_msgs in
#check @Aiur.HeapMono.const
/-- info: 'Aiur.HeapMono.const' does not depend on any axioms -/
#guard_msgs in
#print axioms Aiur.HeapMono.const

/--
info: @HeapMono.and : ∀ {F : Type} {α : Type u_1} {P Q : Heap F → α → Prop},
  HeapMono P → HeapMono Q → HeapMono fun h x => P h x ∧ Q h x
-/
#guard_msgs in
#check @Aiur.HeapMono.and
/-- info: 'Aiur.HeapMono.and' does not depend on any axioms -/
#guard_msgs in
#print axioms Aiur.HeapMono.and

/--
info: @HeapMono.or : ∀ {F : Type} {α : Type u_1} {P Q : Heap F → α → Prop},
  HeapMono P → HeapMono Q → HeapMono fun h x => P h x ∨ Q h x
-/
#guard_msgs in
#check @Aiur.HeapMono.or
/-- info: 'Aiur.HeapMono.or' does not depend on any axioms -/
#guard_msgs in
#print axioms Aiur.HeapMono.or

/--
info: @HeapMono.ex : ∀ {F : Type} {α : Type u_1} {β : Type u_2} {P : β → Heap F → α → Prop},
  (∀ (b : β), HeapMono (P b)) → HeapMono fun h x => ∃ b, P b h x
-/
#guard_msgs in
#check @Aiur.HeapMono.ex
/-- info: 'Aiur.HeapMono.ex' does not depend on any axioms -/
#guard_msgs in
#print axioms Aiur.HeapMono.ex

/--
info: @HeapMono.all : ∀ {F : Type} {α : Type u_1} {β : Type u_2} {P : β → Heap F → α → Prop},
  (∀ (b : β), HeapMono (P b)) → HeapMono fun h x => ∀ (b : β), P b h x
-/
#guard_msgs in
#check @Aiur.HeapMono.all
/-- info: 'Aiur.HeapMono.all' does not depend on any axioms -/
#guard_msgs in
#print axioms Aiur.HeapMono.all

/--
info: @HeapMono.derefTyped : ∀ {F : Type} {ty : Ty} {P : Heap F → SourceValue F → Prop},
  HeapMono P → HeapMono (DerefTyped ty P)
-/
#guard_msgs in
#check @Aiur.HeapMono.derefTyped
/-- info: 'Aiur.HeapMono.derefTyped' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.HeapMono.derefTyped

/-- info: @HeapMono.deref : ∀ {F : Type} {P : Heap F → SourceValue F → Prop}, HeapMono P → HeapMono (Deref P) -/
#guard_msgs in
#check @Aiur.HeapMono.deref
/-- info: 'Aiur.HeapMono.deref' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.HeapMono.deref

/--
info: @Represents.heapMono : ∀ {F : Type} (rom : ROM F) (source : SourceValue F),
  HeapMono fun h target => Represents rom h source target
-/
#guard_msgs in
#check @Aiur.Represents.heapMono
/-- info: 'Aiur.Represents.heapMono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Represents.heapMono

/--
info: @RepLinkedList.mono : ∀ {F : Type} {α : Type u_1} {enumName nilCtor consCtor : String}
  {R : Heap F → α → SourceValue F → Prop},
  HeapMono₂ R →
    ∀ {h₁ h₂ : Heap F} {xs : List α} {ptr : SourceValue F},
      h₁.Extends h₂ →
        RepLinkedList enumName nilCtor consCtor R h₁ xs ptr → RepLinkedList enumName nilCtor consCtor R h₂ xs ptr
-/
#guard_msgs in
#check @Aiur.RepLinkedList.mono
/-- info: 'Aiur.RepLinkedList.mono' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.RepLinkedList.mono

/--
info: @HeapMono.repLinkedList : ∀ {F : Type} {α : Type u_1} (enumName nilCtor consCtor : String)
  {R : Heap F → α → SourceValue F → Prop},
  HeapMono₂ R → ∀ (xs : List α), HeapMono fun h ptr => RepLinkedList enumName nilCtor consCtor R h xs ptr
-/
#guard_msgs in
#check @Aiur.HeapMono.repLinkedList
/-- info: 'Aiur.HeapMono.repLinkedList' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.HeapMono.repLinkedList

/--
info: @RepBinaryTree.mono : ∀ {F : Type} {α : Type u_1} {enumName leafCtor branchCtor : String}
  {R : Heap F → α → SourceValue F → Prop},
  HeapMono₂ R →
    ∀ {h₁ h₂ : Heap F} {t : BinaryTree α} {ptr : SourceValue F},
      h₁.Extends h₂ →
        RepBinaryTree enumName leafCtor branchCtor R h₁ t ptr → RepBinaryTree enumName leafCtor branchCtor R h₂ t ptr
-/
#guard_msgs in
#check @Aiur.RepBinaryTree.mono
/-- info: 'Aiur.RepBinaryTree.mono' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.RepBinaryTree.mono

/--
info: @HeapMono.repBinaryTree : ∀ {F : Type} {α : Type u_1} (enumName leafCtor branchCtor : String)
  {R : Heap F → α → SourceValue F → Prop},
  HeapMono₂ R → ∀ (t : BinaryTree α), HeapMono fun h ptr => RepBinaryTree enumName leafCtor branchCtor R h t ptr
-/
#guard_msgs in
#check @Aiur.HeapMono.repBinaryTree
/-- info: 'Aiur.HeapMono.repBinaryTree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.HeapMono.repBinaryTree

/-! ### 6. Standard Library Representation Predicates, `Lists`, `WordLists`, `Options`, and `Bytes` -/

/-- info: @Library.repU8_heapMono : ∀ {F : Type} [inst : NatCast F] (b : UInt8), HeapMono fun h v => Library.RepU8 h b v -/
#guard_msgs in
#check @Aiur.Library.repU8_heapMono
/-- info: 'Aiur.Library.repU8_heapMono' does not depend on any axioms -/
#guard_msgs in
#print axioms Aiur.Library.repU8_heapMono

/--
info: @Library.repU8_inj : ∀ {F : Type} [inst : Field F],
  Library.U32.Compatible F →
    ∀ {h : Heap F} {a b : UInt8} {v : SourceValue F}, Library.RepU8 h a v → Library.RepU8 h b v → a = b
-/
#guard_msgs in
#check @Aiur.Library.repU8_inj
/-- info: 'Aiur.Library.repU8_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.repU8_inj

/-- info: @Library.repU32_heapMono : ∀ {F : Type} [inst : NatCast F] (w : UInt32), HeapMono fun h v => Library.RepU32 h w v -/
#guard_msgs in
#check @Aiur.Library.repU32_heapMono
/-- info: 'Aiur.Library.repU32_heapMono' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.repU32_heapMono

/-- info: @Library.repU64_heapMono : ∀ {F : Type} [inst : NatCast F] (w : UInt64), HeapMono fun h v => Library.RepU64 h w v -/
#guard_msgs in
#check @Aiur.Library.repU64_heapMono
/-- info: 'Aiur.Library.repU64_heapMono' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.repU64_heapMono

/--
info: @Library.RepOption.mono : ∀ {F : Type} {α : Type u_1} {enumName : String} {R : Heap F → α → SourceValue F → Prop},
  HeapMono₂ R →
    ∀ {h₁ h₂ : Heap F} {opt : Option α} {v : SourceValue F},
      h₁.Extends h₂ → Library.RepOption enumName R h₁ opt v → Library.RepOption enumName R h₂ opt v
-/
#guard_msgs in
#check @Aiur.Library.RepOption.mono
/-- info: 'Aiur.Library.RepOption.mono' does not depend on any axioms -/
#guard_msgs in
#print axioms Aiur.Library.RepOption.mono

/--
info: @Library.repOption_heapMono : ∀ {F : Type} {α : Type u_1} (enumName : String) {R : Heap F → α → SourceValue F → Prop},
  HeapMono₂ R → ∀ (opt : Option α), HeapMono fun h v => Library.RepOption enumName R h opt v
-/
#guard_msgs in
#check @Aiur.Library.repOption_heapMono
/-- info: 'Aiur.Library.repOption_heapMono' does not depend on any axioms -/
#guard_msgs in
#print axioms Aiur.Library.repOption_heapMono

/--
info: @Library.List.repList_heapMono : ∀ {F : Type} {α : Type u_1} (enumName : String)
  {R : Heap F → α → SourceValue F → Prop},
  HeapMono₂ R → ∀ (xs : List α), HeapMono fun h ptr => Library.List.RepList enumName R h xs ptr
-/
#guard_msgs in
#check @Aiur.Library.List.repList_heapMono
/-- info: 'Aiur.Library.List.repList_heapMono' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.List.repList_heapMono

/--
info: @Library.List.repList_inj : ∀ {F : Type} {α : Type u_1} {enumName : String} {R : Heap F → α → SourceValue F → Prop}
  {h : Heap F},
  (∀ {x₁ x₂ : α} {v : SourceValue F}, R h x₁ v → R h x₂ v → x₁ = x₂) →
    ∀ {xs₁ xs₂ : List α} {ptr : SourceValue F},
      Library.List.RepList enumName R h xs₁ ptr → Library.List.RepList enumName R h xs₂ ptr → xs₁ = xs₂
-/
#guard_msgs in
#check @Aiur.Library.List.repList_inj
/-- info: 'Aiur.Library.List.repList_inj' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.List.repList_inj

/--
info: @Library.List.allocNil_extends : ∀ {F : Type} (enumName : String) (h : Heap F),
  h.Extends (Library.List.allocNil enumName h).2
-/
#guard_msgs in
#check @Aiur.Library.List.allocNil_extends
/-- info: 'Aiur.Library.List.allocNil_extends' does not depend on any axioms -/
#guard_msgs in
#print axioms Aiur.Library.List.allocNil_extends

/--
info: @Library.List.allocNil_rep : ∀ {F : Type} {α : Type u_1} (enumName : String) (R : Heap F → α → SourceValue F → Prop)
  (h : Heap F),
  Library.List.RepList enumName R (Library.List.allocNil enumName h).2 [] (Library.List.allocNil enumName h).1
-/
#guard_msgs in
#check @Aiur.Library.List.allocNil_rep
/-- info: 'Aiur.Library.List.allocNil_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.List.allocNil_rep

/--
info: @Library.List.allocCons_extends : ∀ {F : Type} (enumName : String) (headVal tailPtr : SourceValue F) (h : Heap F),
  h.Extends (Library.List.allocCons enumName headVal tailPtr h).2
-/
#guard_msgs in
#check @Aiur.Library.List.allocCons_extends
/-- info: 'Aiur.Library.List.allocCons_extends' does not depend on any axioms -/
#guard_msgs in
#print axioms Aiur.Library.List.allocCons_extends

/--
info: @Library.List.allocCons_rep : ∀ {F : Type} {α : Type u_1} (enumName : String) {R : Heap F → α → SourceValue F → Prop},
  HeapMono₂ R →
    ∀ {h : Heap F} {x : α} {xs : List α} {headVal tailPtr : SourceValue F},
      R h x headVal →
        Library.List.RepList enumName R h xs tailPtr →
          Library.List.RepList enumName R (Library.List.allocCons enumName headVal tailPtr h).2 (x :: xs)
            (Library.List.allocCons enumName headVal tailPtr h).1
-/
#guard_msgs in
#check @Aiur.Library.List.allocCons_rep
/-- info: 'Aiur.Library.List.allocCons_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.List.allocCons_rep

/--
info: @Library.List.allocValues_extends : ∀ {F : Type} (enumName : String) (h : Heap F) (vs : List (SourceValue F)),
  h.Extends (Library.List.allocValues enumName h vs).2
-/
#guard_msgs in
#check @Aiur.Library.List.allocValues_extends
/-- info: 'Aiur.Library.List.allocValues_extends' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.List.allocValues_extends

/--
info: @Library.List.allocValues_rep : ∀ {F : Type} {α : Type u_1} (enumName : String) {R : Heap F → α → SourceValue F → Prop},
  HeapMono₂ R →
    ∀ (h : Heap F) {xs : List α} {vs : List (SourceValue F)},
      List.Forall₂ (R h) xs vs →
        Library.List.RepList enumName R (Library.List.allocValues enumName h vs).2 xs
          (Library.List.allocValues enumName h vs).1
-/
#guard_msgs in
#check @Aiur.Library.List.allocValues_rep
/-- info: 'Aiur.Library.List.allocValues_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.List.allocValues_rep

/--
info: @Library.List.is_empty_spec : ∀ {F : Type} {α : Type u_1} [inst : Field F] (xs : List α),
  Library.List.isEmpty xs = if xs.isEmpty = true then 1 else 0
-/
#guard_msgs in
#check @Aiur.Library.List.is_empty_spec
/-- info: 'Aiur.Library.List.is_empty_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.List.is_empty_spec

/--
info: @Library.List.is_empty_one_iff : ∀ {F : Type} {α : Type u_1} [inst : Field F] (xs : List α),
  Library.List.isEmpty xs = 1 ↔ xs = []
-/
#guard_msgs in
#check @Aiur.Library.List.is_empty_one_iff
/-- info: 'Aiur.Library.List.is_empty_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.List.is_empty_one_iff

/--
info: @Library.List.is_empty_zero_iff : ∀ {F : Type} {α : Type u_1} [inst : Field F] (xs : List α),
  Library.List.isEmpty xs = 0 ↔ xs ≠ []
-/
#guard_msgs in
#check @Aiur.Library.List.is_empty_zero_iff
/-- info: 'Aiur.Library.List.is_empty_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.List.is_empty_zero_iff

/-- info: @Library.List.reverse_acc_spec : ∀ {α : Type u_1} (xs acc : List α), Library.List.reverseAcc xs acc = xs.reverse ++ acc -/
#guard_msgs in
#check @Aiur.Library.List.reverse_acc_spec
/-- info: 'Aiur.Library.List.reverse_acc_spec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.List.reverse_acc_spec

/-- info: @Library.List.reverse_spec : ∀ {α : Type u_1} (xs : List α), Library.List.reverseAcc xs [] = xs.reverse -/
#guard_msgs in
#check @Aiur.Library.List.reverse_spec
/-- info: 'Aiur.Library.List.reverse_spec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.List.reverse_spec

/-- info: @Library.List.snoc_spec : ∀ {α : Type u_1} (xs : List α) (v : α), xs ++ [v] = xs.concat v -/
#guard_msgs in
#check @Aiur.Library.List.snoc_spec
/-- info: 'Aiur.Library.List.snoc_spec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.List.snoc_spec

/--
info: @Library.List.Word.checked_depth_succ_sound : ∀ {F : Type} [inst : Field F],
  Library.U32.Compatible F →
    ∀ {depth difference : ℕ},
      depth < Library.U32.base →
        difference < Library.U32.base →
          (have borrow := (↑difference + ↑4294967295 - ↑depth) / ↑Library.U32.base;
            borrow * (borrow - 1) = 0) →
            (↑difference + ↑4294967295 - ↑depth) / ↑Library.U32.base = 1 →
              depth < 4294967295 ∧ depth + 1 < Library.U32.base ∧ ↑depth + 1 = ↑(depth + 1)
-/
#guard_msgs in
#check @Aiur.Library.List.Word.checked_depth_succ_sound
/-- info: 'Aiur.Library.List.Word.checked_depth_succ_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.List.Word.checked_depth_succ_sound

/--
info: @Library.List.Word.depth_checked_iff : ∀ {α : Type u_1} (xs : List α),
  Library.List.Word.depthChecked xs = if xs.length < Library.U32.base then some xs.length else none
-/
#guard_msgs in
#check @Aiur.Library.List.Word.depth_checked_iff
/-- info: 'Aiur.Library.List.Word.depth_checked_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.List.Word.depth_checked_iff

/--
info: @Library.List.Word.depth_checked_some_iff : ∀ {α : Type u_1} (xs : List α) (n : ℕ),
  Library.List.Word.depthChecked xs = some n ↔ n = xs.length ∧ xs.length < Library.U32.base
-/
#guard_msgs in
#check @Aiur.Library.List.Word.depth_checked_some_iff
/-- info: 'Aiur.Library.List.Word.depth_checked_some_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.List.Word.depth_checked_some_iff

/--
info: @Library.List.Word.length_u64_spec : ∀ {α : Type u_1} (xs : List α),
  Library.List.Word.lengthU64 xs = UInt64.ofNat xs.length
-/
#guard_msgs in
#check @Aiur.Library.List.Word.length_u64_spec
/-- info: 'Aiur.Library.List.Word.length_u64_spec' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.List.Word.length_u64_spec

/--
info: @Library.List.Word.length_u64_toNat_of_lt : ∀ {α : Type u_1} {xs : List α},
  xs.length < Library.U64.base → (Library.List.Word.lengthU64 xs).toNat = xs.length
-/
#guard_msgs in
#check @Aiur.Library.List.Word.length_u64_toNat_of_lt
/-- info: 'Aiur.Library.List.Word.length_u64_toNat_of_lt' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.List.Word.length_u64_toNat_of_lt

/--
info: @Library.List.Word.length_u64_of_depth_checked : ∀ {α : Type u_1} {xs : List α} {n : ℕ},
  Library.List.Word.depthChecked xs = some n → (Library.List.Word.lengthU64 xs).toNat = xs.length ∧ n = xs.length
-/
#guard_msgs in
#check @Aiur.Library.List.Word.length_u64_of_depth_checked
/-- info: 'Aiur.Library.List.Word.length_u64_of_depth_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.List.Word.length_u64_of_depth_checked

/--
info: @Library.List.Word.lookup_u64_spec : ∀ {α : Type u_1} (xs : List α) (idx : UInt64),
  Library.List.Word.lookupU64 xs idx = xs[idx.toNat]?
-/
#guard_msgs in
#check @Aiur.Library.List.Word.lookup_u64_spec
/-- info: 'Aiur.Library.List.Word.lookup_u64_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.List.Word.lookup_u64_spec

/--
info: @Library.List.Word.lookup_u64_rep : ∀ {F : Type} {α : Type u_1} (enumName : String)
  (R : Heap F → α → SourceValue F → Prop) {h : Heap F} {xs : List α} {ptr : SourceValue F},
  Library.List.RepList enumName R h xs ptr →
    ∀ (idx : UInt64) {x : α}, Library.List.Word.lookupU64 xs idx = some x → ∃ v, R h x v
-/
#guard_msgs in
#check @Aiur.Library.List.Word.lookup_u64_rep
/-- info: 'Aiur.Library.List.Word.lookup_u64_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.List.Word.lookup_u64_rep

/--
info: @Library.Bytes.repAddress_heapMono : ∀ {F : Type} [inst : NatCast F] (addr : Library.Bytes.Address),
  HeapMono fun h v => Library.Bytes.RepAddress h addr v
-/
#guard_msgs in
#check @Aiur.Library.Bytes.repAddress_heapMono
/-- info: 'Aiur.Library.Bytes.repAddress_heapMono' does not depend on any axioms -/
#guard_msgs in
#print axioms Aiur.Library.Bytes.repAddress_heapMono

/--
info: @Library.Bytes.repAddressRef_heapMono : ∀ {F : Type} [inst : NatCast F] (ty : Ty) (addr : Library.Bytes.Address),
  HeapMono fun h ptr => Library.Bytes.RepAddressRef ty h addr ptr
-/
#guard_msgs in
#check @Aiur.Library.Bytes.repAddressRef_heapMono
/-- info: 'Aiur.Library.Bytes.repAddressRef_heapMono' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.Bytes.repAddressRef_heapMono

/--
info: @Library.Bytes.repByteStream_heapMono : ∀ {F : Type} [inst : NatCast F] (enumName : String) (bytes : List UInt8),
  HeapMono fun h ptr => Library.Bytes.RepByteStream enumName h bytes ptr
-/
#guard_msgs in
#check @Aiur.Library.Bytes.repByteStream_heapMono
/-- info: 'Aiur.Library.Bytes.repByteStream_heapMono' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.Bytes.repByteStream_heapMono

/--
info: @Library.Bytes.repAddress_inj : ∀ {F : Type} [inst : Field F],
  Library.U32.Compatible F →
    ∀ {h : Heap F} {a₁ a₂ : Library.Bytes.Address} {v : SourceValue F},
      Library.Bytes.RepAddress h a₁ v → Library.Bytes.RepAddress h a₂ v → a₁ = a₂
-/
#guard_msgs in
#check @Aiur.Library.Bytes.repAddress_inj
/-- info: 'Aiur.Library.Bytes.repAddress_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Bytes.repAddress_inj

/--
info: @Library.Bytes.repAddressRef_inj : ∀ {F : Type} [inst : Field F],
  Library.U32.Compatible F →
    ∀ {ty : Ty} {h : Heap F} {a₁ a₂ : Library.Bytes.Address} {ptr : SourceValue F},
      Library.Bytes.RepAddressRef ty h a₁ ptr → Library.Bytes.RepAddressRef ty h a₂ ptr → a₁ = a₂
-/
#guard_msgs in
#check @Aiur.Library.Bytes.repAddressRef_inj
/-- info: 'Aiur.Library.Bytes.repAddressRef_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Bytes.repAddressRef_inj

/--
info: @Library.Bytes.repByteStream_inj : ∀ {F : Type} [inst : Field F],
  Library.U32.Compatible F →
    ∀ {enumName : String} {h : Heap F} {bs₁ bs₂ : List UInt8} {ptr : SourceValue F},
      Library.Bytes.RepByteStream enumName h bs₁ ptr → Library.Bytes.RepByteStream enumName h bs₂ ptr → bs₁ = bs₂
-/
#guard_msgs in
#check @Aiur.Library.Bytes.repByteStream_inj
/-- info: 'Aiur.Library.Bytes.repByteStream_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Bytes.repByteStream_inj

/--
info: @Library.Bytes.address_eq_spec : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F],
  Library.U64.Compatible F → ∀ (a b : Library.Bytes.Address), Library.Bytes.addressEq F a b = if a = b then 1 else 0
-/
#guard_msgs in
#check @Aiur.Library.Bytes.address_eq_spec
/-- info: 'Aiur.Library.Bytes.address_eq_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Bytes.address_eq_spec

/--
info: @Library.Bytes.address_eq_one_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F],
  Library.U64.Compatible F → ∀ (a b : Library.Bytes.Address), Library.Bytes.addressEq F a b = 1 ↔ a = b
-/
#guard_msgs in
#check @Aiur.Library.Bytes.address_eq_one_iff
/-- info: 'Aiur.Library.Bytes.address_eq_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Bytes.address_eq_one_iff

/--
info: @Library.Bytes.address_eq_zero_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F],
  Library.U64.Compatible F → ∀ (a b : Library.Bytes.Address), Library.Bytes.addressEq F a b = 0 ↔ a ≠ b
-/
#guard_msgs in
#check @Aiur.Library.Bytes.address_eq_zero_iff
/-- info: 'Aiur.Library.Bytes.address_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Bytes.address_eq_zero_iff

/--
info: Library.Bytes.read_byte_stream_length : ∀ (stream : ℕ → UInt8) (idx len : ℕ),
  (Library.Bytes.readByteStream stream idx len).length = len
-/
#guard_msgs in
#check @Aiur.Library.Bytes.read_byte_stream_length
/-- info: 'Aiur.Library.Bytes.read_byte_stream_length' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.Bytes.read_byte_stream_length

/--
info: Library.Bytes.read_byte_stream_getElem : ∀ (stream : ℕ → UInt8) (idx len i : ℕ) (hi : i < len),
  (Library.Bytes.readByteStream stream idx len)[i] = stream (idx + i)
-/
#guard_msgs in
#check @Aiur.Library.Bytes.read_byte_stream_getElem
/-- info: 'Aiur.Library.Bytes.read_byte_stream_getElem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Bytes.read_byte_stream_getElem

/--
info: @Library.Bytes.alloc_byte_stream_extends : ∀ {F : Type} [inst : NatCast F] (enumName : String) (h : Heap F)
  (bytes : List UInt8), h.Extends (Library.Bytes.allocByteStream enumName h bytes).2
-/
#guard_msgs in
#check @Aiur.Library.Bytes.alloc_byte_stream_extends
/-- info: 'Aiur.Library.Bytes.alloc_byte_stream_extends' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.Bytes.alloc_byte_stream_extends

/--
info: @Library.Bytes.alloc_byte_stream_rep : ∀ {F : Type} [inst : NatCast F] (enumName : String) (h : Heap F)
  (bytes : List UInt8),
  Library.Bytes.RepByteStream enumName (Library.Bytes.allocByteStream enumName h bytes).2 bytes
    (Library.Bytes.allocByteStream enumName h bytes).1
-/
#guard_msgs in
#check @Aiur.Library.Bytes.alloc_byte_stream_rep
/-- info: 'Aiur.Library.Bytes.alloc_byte_stream_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Bytes.alloc_byte_stream_rep

/--
info: @Library.Bytes.read_byte_stream_spec : ∀ {F : Type} [inst : NatCast F] (enumName : String) (stream : ℕ → UInt8)
  (idx len : ℕ) (h : Heap F),
  have bytes := Library.Bytes.readByteStream stream idx len;
  have allocated := Library.Bytes.allocByteStream enumName h bytes;
  h.Extends allocated.2 ∧ Library.Bytes.RepByteStream enumName allocated.2 bytes allocated.1 ∧ bytes.length = len
-/
#guard_msgs in
#check @Aiur.Library.Bytes.read_byte_stream_spec
/-- info: 'Aiur.Library.Bytes.read_byte_stream_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Bytes.read_byte_stream_spec

/--
info: @Library.Bytes.read_finite_byte_stream_spec : ∀ {F : Type} [inst : NatCast F] (enumName : String) (stream : ℕ → UInt8)
  (idx len : ℕ) (h : Heap F),
  have bytes := Library.Bytes.readByteStream stream idx len;
  have allocated := Library.Bytes.allocByteStream enumName h bytes;
  (Library.List.Word.depthChecked bytes = some len ↔ len < Library.U32.base) ∧
    h.Extends allocated.2 ∧ Library.Bytes.RepByteStream enumName allocated.2 bytes allocated.1 ∧ bytes.length = len
-/
#guard_msgs in
#check @Aiur.Library.Bytes.read_finite_byte_stream_spec
/-- info: 'Aiur.Library.Bytes.read_finite_byte_stream_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.Bytes.read_finite_byte_stream_spec

/-! ## Step & Inversion Lemmas and Hint-Invariance (`Aiur.StepLemmas`) -/

/--
info: @evalExpr_literal_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F}
  {locals : Environment F ℕ} {value : F} {before : Heap F} {result : SourceValue F} {after : Heap F},
  EvalExpr program locals (Expr.literal value) before result after ↔ result = Value.field value ∧ after = before
-/
#guard_msgs in
#check @Aiur.evalExpr_literal_iff
/-- info: 'Aiur.evalExpr_literal_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.evalExpr_literal_iff

/--
info: @evalExpr_var_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F}
  {locals : Environment F ℕ} {name : String} {before : Heap F} {result : SourceValue F} {after : Heap F},
  EvalExpr program locals (Expr.var name) before result after ↔
    List.find? (fun x => x.1 == name) locals = some (name, result) ∧ after = before
-/
#guard_msgs in
#check @Aiur.evalExpr_var_iff
/-- info: 'Aiur.evalExpr_var_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.evalExpr_var_iff

/--
info: @evalExpr_tuple_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F}
  {locals : Environment F ℕ} {exprs : List (Expr F)} {before : Heap F} {result : SourceValue F} {after : Heap F},
  EvalExpr program locals (Expr.tuple exprs) before result after ↔
    ∃ values, EvalArgs program locals exprs before values after ∧ result = Value.tuple values
-/
#guard_msgs in
#check @Aiur.evalExpr_tuple_iff
/-- info: 'Aiur.evalExpr_tuple_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.evalExpr_tuple_iff

/--
info: @evalExpr_construct_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F}
  {locals : Environment F ℕ} {name ctor : String} {exprs : List (Expr F)} {before : Heap F} {result : SourceValue F}
  {after : Heap F},
  EvalExpr program locals (Expr.construct name ctor exprs) before result after ↔
    ∃ values, EvalArgs program locals exprs before values after ∧ result = Value.construct name ctor values
-/
#guard_msgs in
#check @Aiur.evalExpr_construct_iff
/-- info: 'Aiur.evalExpr_construct_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.evalExpr_construct_iff

/--
info: @evalExpr_project_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F}
  {locals : Environment F ℕ} {expr : Expr F} {index : ℕ} {before : Heap F} {result : SourceValue F} {after : Heap F},
  EvalExpr program locals (expr.project index) before result after ↔
    ∃ input, EvalExpr program locals expr before input after ∧ projectValue input index = Except.ok result
-/
#guard_msgs in
#check @Aiur.evalExpr_project_iff
/-- info: 'Aiur.evalExpr_project_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.evalExpr_project_iff

/--
info: @evalExpr_letValue_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F}
  {locals : Environment F ℕ} {pattern : Pattern F} {expr rest : Expr F} {before : Heap F} {result : SourceValue F}
  {after : Heap F},
  EvalExpr program locals (Expr.letValue pattern expr rest) before result after ↔
    ∃ input middle bindings,
      EvalExpr program locals expr before input middle ∧
        pattern.bindings input = some bindings ∧ EvalExpr program (bindings ++ locals) rest middle result after
-/
#guard_msgs in
#check @Aiur.evalExpr_letValue_iff
/-- info: 'Aiur.evalExpr_letValue_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.evalExpr_letValue_iff

/--
info: @evalExpr_store_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F}
  {locals : Environment F ℕ} {expr : Expr F} {before : Heap F} {result : SourceValue F} {after : Heap F},
  EvalExpr program locals expr.store before result after ↔
    ∃ input middle,
      EvalExpr program locals expr before input middle ∧
        result = Value.ptr (Value.type input) (List.length middle) ∧ after = middle ++ [input]
-/
#guard_msgs in
#check @Aiur.evalExpr_store_iff
/-- info: 'Aiur.evalExpr_store_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.evalExpr_store_iff

/--
info: @evalExpr_load_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F}
  {locals : Environment F ℕ} {expr : Expr F} {before : Heap F} {result : SourceValue F} {after : Heap F},
  EvalExpr program locals expr.load before result after ↔
    ∃ input, EvalExpr program locals expr before input after ∧ loadValue after input = Except.ok result
-/
#guard_msgs in
#check @Aiur.evalExpr_load_iff
/-- info: 'Aiur.evalExpr_load_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.evalExpr_load_iff

/--
info: @evalExpr_hint_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F}
  {locals : Environment F ℕ} {type : Ty} {expr : Expr F} {channel : String} {before : Heap F} {result : SourceValue F}
  {after : Heap F},
  EvalExpr program locals (Expr.hint type expr channel) before result after ↔
    ∃ input value,
      EvalExpr program locals expr before input after ∧
        Value.WellTyped program.enums value type ∧ result = value.toValue
-/
#guard_msgs in
#check @Aiur.evalExpr_hint_iff
/-- info: 'Aiur.evalExpr_hint_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.evalExpr_hint_iff

/--
info: @evalExpr_neg_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F}
  {locals : Environment F ℕ} {expr : Expr F} {before : Heap F} {result : SourceValue F} {after : Heap F},
  EvalExpr program locals expr.neg before result after ↔
    ∃ input, EvalExpr program locals expr before input after ∧ evalNeg input = Except.ok result
-/
#guard_msgs in
#check @Aiur.evalExpr_neg_iff
/-- info: 'Aiur.evalExpr_neg_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.evalExpr_neg_iff

/--
info: @evalExpr_assertEq_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F}
  {locals : Environment F ℕ} {op : Assertion} {lhs rhs : Expr F} {before : Heap F} {result : SourceValue F}
  {after : Heap F},
  EvalExpr program locals (Expr.assertEq op lhs rhs) before result after ↔
    ∃ x middle y,
      EvalExpr program locals lhs before x middle ∧
        EvalExpr program locals rhs middle y after ∧ evalAssertEq op x y = Except.ok result
-/
#guard_msgs in
#check @Aiur.evalExpr_assertEq_iff
/-- info: 'Aiur.evalExpr_assertEq_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.evalExpr_assertEq_iff

/--
info: @evalExpr_binary_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F}
  {locals : Environment F ℕ} {op : BinOp} {lhs rhs : Expr F} {before : Heap F} {result : SourceValue F}
  {after : Heap F},
  EvalExpr program locals (Expr.binary op lhs rhs) before result after ↔
    ∃ x middle y,
      EvalExpr program locals lhs before x middle ∧
        EvalExpr program locals rhs middle y after ∧ evalBinOp op x y = Except.ok result
-/
#guard_msgs in
#check @Aiur.evalExpr_binary_iff
/-- info: 'Aiur.evalExpr_binary_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.evalExpr_binary_iff

/--
info: @evalExpr_call_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F}
  {locals : Environment F ℕ} {name : String} {args : List (Expr F)} {before : Heap F} {result : SourceValue F}
  {after : Heap F},
  EvalExpr program locals (Expr.call name args) before result after ↔
    ∃ values middle, EvalArgs program locals args before values middle ∧ EvalFn program name values middle result after
-/
#guard_msgs in
#check @Aiur.evalExpr_call_iff
/-- info: 'Aiur.evalExpr_call_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.evalExpr_call_iff

/--
info: @evalFn_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F} {name : String}
  {args : List (SourceValue F)} {before : Heap F} {result : SourceValue F} {after : Heap F},
  EvalFn program name args before result after ↔
    ∃ locals expr,
      prepareCall program name args = Except.ok (locals, expr) ∧ EvalExpr program locals expr before result after
-/
#guard_msgs in
#check @Aiur.evalFn_iff
/-- info: 'Aiur.evalFn_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.evalFn_iff

/--
info: @evalExpr_call_function_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F}
  {locals : Environment F ℕ} {name : String} {«fn» : Function F} {args : List (Expr F)} {before : Heap F}
  {result : SourceValue F} {after : Heap F},
  program.findFunction? name = some «fn» →
    (EvalExpr program locals (Expr.call name args) before result after ↔
      ∃ values middle,
        EvalArgs program locals args before values middle ∧
          List.map Prod.snd «fn».params = List.map Value.type values ∧
            (∀ arg ∈ values, Value.wellFormed program.enums arg = true) ∧
              EvalExpr program ((List.map Prod.fst «fn».params).zip values) «fn».body middle result after)
-/
#guard_msgs in
#check @Aiur.evalExpr_call_function_iff
/-- info: 'Aiur.evalExpr_call_function_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.evalExpr_call_function_iff

/--
info: @evalExpr_call_table_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F}
  {locals : Environment F ℕ} {name : String} {args : List (Expr F)} {before : Heap F} {result : SourceValue F}
  {after : Heap F},
  program.findFunction? name = none →
    (EvalExpr program locals (Expr.call name args) before result after ↔
      ∃ values value,
        EvalArgs program locals args before values after ∧
          lookupMap program name values = Except.ok value ∧ result = value.toValue)
-/
#guard_msgs in
#check @Aiur.evalExpr_call_table_iff
/-- info: 'Aiur.evalExpr_call_table_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.evalExpr_call_table_iff

/--
info: @evalExpr_matchValue_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F}
  {locals : Environment F ℕ} {expr : Expr F} {arms : List (Pattern F × Expr F)} {before : Heap F}
  {result : SourceValue F} {after : Heap F},
  EvalExpr program locals (expr.matchValue arms) before result after ↔
    ∃ input middle bindings body,
      EvalExpr program locals expr before input middle ∧
        selectArm input arms = some (bindings, body) ∧ EvalExpr program (bindings ++ locals) body middle result after
-/
#guard_msgs in
#check @Aiur.evalExpr_matchValue_iff
/-- info: 'Aiur.evalExpr_matchValue_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.evalExpr_matchValue_iff

/--
info: @evalArgs_nil_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F}
  {locals : Environment F ℕ} {before : Heap F} {values : List (SourceValue F)} {after : Heap F},
  EvalArgs program locals [] before values after ↔ values = [] ∧ after = before
-/
#guard_msgs in
#check @Aiur.evalArgs_nil_iff
/-- info: 'Aiur.evalArgs_nil_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.evalArgs_nil_iff

/--
info: @evalArgs_cons_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F}
  {locals : Environment F ℕ} {expr : Expr F} {exprs : List (Expr F)} {before : Heap F} {results : List (SourceValue F)}
  {after : Heap F},
  EvalArgs program locals (expr :: exprs) before results after ↔
    ∃ value middle values,
      EvalExpr program locals expr before value middle ∧
        EvalArgs program locals exprs middle values after ∧ results = value :: values
-/
#guard_msgs in
#check @Aiur.evalArgs_cons_iff
/-- info: 'Aiur.evalArgs_cons_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.evalArgs_cons_iff

/--
info: @evalExpr_let_hint_invariance : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F}
  {locals : Environment F ℕ} {pattern : Pattern F} {type : Ty} {keyExpr : Expr F} {channel : String} {rest : Expr F}
  {before : Heap F} {result : SourceValue F} {after : Heap F} {P : Constant F → SourceValue F → Heap F → Prop},
  EvalExpr program locals (Expr.letValue pattern (Expr.hint type keyExpr channel) rest) before result after →
    (∀ (c : Constant F) (middle : Heap F) (bindings : Environment F ℕ),
        Value.WellTyped program.enums c type →
          pattern.bindings c.toValue = some bindings →
            EvalExpr program (bindings ++ locals) rest middle result after → P c result after) →
      ∃ c, Value.WellTyped program.enums c type ∧ P c result after
-/
#guard_msgs in
#check @Aiur.evalExpr_let_hint_invariance
/-- info: 'Aiur.evalExpr_let_hint_invariance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.evalExpr_let_hint_invariance

/--
info: @evalFn_hint_invariance : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {program : Program F} {name : String}
  {«fn» : Function F} {args : List (SourceValue F)} {before : Heap F} {result : SourceValue F} {after : Heap F}
  {pattern : Pattern F} {type : Ty} {keyExpr : Expr F} {channel : String} {rest : Expr F}
  {P : Constant F → SourceValue F → Heap F → Prop},
  program.findFunction? name = some «fn» →
    «fn».body = Expr.letValue pattern (Expr.hint type keyExpr channel) rest →
      EvalFn program name args before result after →
        (∀ (c : Constant F) (middle : Heap F) (bindings : Environment F ℕ),
            Value.WellTyped program.enums c type →
              pattern.bindings c.toValue = some bindings →
                EvalExpr program (bindings ++ (List.map Prod.fst «fn».params).zip args) rest middle result after →
                  P c result after) →
          ∃ c, Value.WellTyped program.enums c type ∧ P c result after
-/
#guard_msgs in
#check @Aiur.evalFn_hint_invariance
/-- info: 'Aiur.evalFn_hint_invariance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.evalFn_hint_invariance

/--
info: @Generic.SourceSemantics.evalExpr_literal_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {world : Generic.SourceSemantics.World F} {types : Generic.SourceSemantics.Types} {locals : Environment F ℕ}
  {value : F} {before : Heap F} {result : SourceValue F} {after : Heap F},
  Generic.SourceSemantics.EvalExpr world types locals (Generic.Expr.literal value) before result after ↔
    result = Value.field value ∧ after = before
-/
#guard_msgs in
#check @Aiur.Generic.SourceSemantics.evalExpr_literal_iff
/-- info: 'Aiur.Generic.SourceSemantics.evalExpr_literal_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.SourceSemantics.evalExpr_literal_iff

/--
info: @Generic.SourceSemantics.evalExpr_var_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {world : Generic.SourceSemantics.World F} {types : Generic.SourceSemantics.Types} {locals : Environment F ℕ}
  {name : String} {before : Heap F} {result : SourceValue F} {after : Heap F},
  Generic.SourceSemantics.EvalExpr world types locals (Generic.Expr.var name) before result after ↔
    List.find? (fun x => x.1 == name) locals = some (name, result) ∧ after = before
-/
#guard_msgs in
#check @Aiur.Generic.SourceSemantics.evalExpr_var_iff
/-- info: 'Aiur.Generic.SourceSemantics.evalExpr_var_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.SourceSemantics.evalExpr_var_iff

/--
info: @Generic.SourceSemantics.evalExpr_tuple_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {world : Generic.SourceSemantics.World F} {types : Generic.SourceSemantics.Types} {locals : Environment F ℕ}
  {exprs : List (Generic.Expr F)} {before : Heap F} {result : SourceValue F} {after : Heap F},
  Generic.SourceSemantics.EvalExpr world types locals (Generic.Expr.tuple exprs) before result after ↔
    ∃ values,
      Generic.SourceSemantics.EvalArgs world types locals exprs before values after ∧ result = Value.tuple values
-/
#guard_msgs in
#check @Aiur.Generic.SourceSemantics.evalExpr_tuple_iff
/-- info: 'Aiur.Generic.SourceSemantics.evalExpr_tuple_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.SourceSemantics.evalExpr_tuple_iff

/--
info: @Generic.SourceSemantics.evalExpr_array_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {world : Generic.SourceSemantics.World F} {types : Generic.SourceSemantics.Types} {locals : Environment F ℕ}
  {exprs : List (Generic.Expr F)} {before : Heap F} {result : SourceValue F} {after : Heap F},
  Generic.SourceSemantics.EvalExpr world types locals (Generic.Expr.array exprs) before result after ↔
    ∃ values,
      Generic.SourceSemantics.EvalArgs world types locals exprs before values after ∧ result = Value.tuple values
-/
#guard_msgs in
#check @Aiur.Generic.SourceSemantics.evalExpr_array_iff
/-- info: 'Aiur.Generic.SourceSemantics.evalExpr_array_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.SourceSemantics.evalExpr_array_iff

/--
info: @Generic.SourceSemantics.evalExpr_let_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {world : Generic.SourceSemantics.World F} {types : Generic.SourceSemantics.Types} {locals : Environment F ℕ}
  {pattern : Generic.Pattern F} {expr rest : Generic.Expr F} {before : Heap F} {result : SourceValue F}
  {after : Heap F},
  Generic.SourceSemantics.EvalExpr world types locals (Generic.Expr.letValue pattern expr rest) before result after ↔
    ∃ input middle bindings,
      Generic.SourceSemantics.EvalExpr world types locals expr before input middle ∧
        world.matchPattern types middle pattern input = Except.ok (some bindings) ∧
          Generic.SourceSemantics.EvalExpr world types (bindings ++ locals) rest middle result after
-/
#guard_msgs in
#check @Aiur.Generic.SourceSemantics.evalExpr_let_iff
/-- info: 'Aiur.Generic.SourceSemantics.evalExpr_let_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.SourceSemantics.evalExpr_let_iff

/--
info: @Generic.SourceSemantics.evalExpr_store_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {world : Generic.SourceSemantics.World F} {types : Generic.SourceSemantics.Types} {locals : Environment F ℕ}
  {expr : Generic.Expr F} {before : Heap F} {result : SourceValue F} {after : Heap F},
  Generic.SourceSemantics.EvalExpr world types locals expr.store before result after ↔
    ∃ input middle,
      Generic.SourceSemantics.EvalExpr world types locals expr before input middle ∧
        result = Value.ptr (Value.type input) (List.length middle) ∧ after = middle ++ [input]
-/
#guard_msgs in
#check @Aiur.Generic.SourceSemantics.evalExpr_store_iff
/-- info: 'Aiur.Generic.SourceSemantics.evalExpr_store_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.SourceSemantics.evalExpr_store_iff

/--
info: @Generic.SourceSemantics.evalExpr_load_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {world : Generic.SourceSemantics.World F} {types : Generic.SourceSemantics.Types} {locals : Environment F ℕ}
  {expr : Generic.Expr F} {before : Heap F} {result : SourceValue F} {after : Heap F},
  Generic.SourceSemantics.EvalExpr world types locals expr.load before result after ↔
    ∃ input,
      Generic.SourceSemantics.EvalExpr world types locals expr before input after ∧
        loadValue after input = Except.ok result
-/
#guard_msgs in
#check @Aiur.Generic.SourceSemantics.evalExpr_load_iff
/-- info: 'Aiur.Generic.SourceSemantics.evalExpr_load_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.SourceSemantics.evalExpr_load_iff

/--
info: @Generic.SourceSemantics.evalExpr_hint_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {world : Generic.SourceSemantics.World F} {types : Generic.SourceSemantics.Types} {locals : Environment F ℕ}
  {t : Generic.Ty} {expr : Generic.Expr F} {channel : String} {before : Heap F} {result : SourceValue F}
  {after : Heap F},
  Generic.SourceSemantics.EvalExpr world types locals (Generic.Expr.hint t expr channel) before result after ↔
    ∃ input value,
      Generic.SourceSemantics.EvalExpr world types locals expr before input after ∧
        world.typed (Generic.Ty.subst types t).toCore value = true ∧ result = value.toValue
-/
#guard_msgs in
#check @Aiur.Generic.SourceSemantics.evalExpr_hint_iff
/-- info: 'Aiur.Generic.SourceSemantics.evalExpr_hint_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.SourceSemantics.evalExpr_hint_iff

/--
info: @Generic.SourceSemantics.evalExpr_builtin_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {world : Generic.SourceSemantics.World F} {types : Generic.SourceSemantics.Types} {locals : Environment F ℕ}
  {operation : Generic.Builtin} {exprs : List (Generic.Expr F)} {before : Heap F} {result : SourceValue F}
  {after : Heap F},
  Generic.SourceSemantics.EvalExpr world types locals (Generic.Expr.builtin operation exprs) before result after ↔
    ∃ values,
      Generic.SourceSemantics.EvalArgs world types locals exprs before values after ∧
        operation.apply values = Except.ok result
-/
#guard_msgs in
#check @Aiur.Generic.SourceSemantics.evalExpr_builtin_iff
/-- info: 'Aiur.Generic.SourceSemantics.evalExpr_builtin_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.SourceSemantics.evalExpr_builtin_iff

/--
info: @Generic.SourceSemantics.evalArgs_nil_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {world : Generic.SourceSemantics.World F} {types : Generic.SourceSemantics.Types} {locals : Environment F ℕ}
  {before : Heap F} {values : List (SourceValue F)} {after : Heap F},
  Generic.SourceSemantics.EvalArgs world types locals [] before values after ↔ values = [] ∧ after = before
-/
#guard_msgs in
#check @Aiur.Generic.SourceSemantics.evalArgs_nil_iff
/-- info: 'Aiur.Generic.SourceSemantics.evalArgs_nil_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.SourceSemantics.evalArgs_nil_iff

/--
info: @Generic.SourceSemantics.evalArgs_cons_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {world : Generic.SourceSemantics.World F} {types : Generic.SourceSemantics.Types} {locals : Environment F ℕ}
  {expr : Generic.Expr F} {exprs : List (Generic.Expr F)} {before : Heap F} {results : List (SourceValue F)}
  {after : Heap F},
  Generic.SourceSemantics.EvalArgs world types locals (expr :: exprs) before results after ↔
    ∃ value middle values,
      Generic.SourceSemantics.EvalExpr world types locals expr before value middle ∧
        Generic.SourceSemantics.EvalArgs world types locals exprs middle values after ∧ results = value :: values
-/
#guard_msgs in
#check @Aiur.Generic.SourceSemantics.evalArgs_cons_iff
/-- info: 'Aiur.Generic.SourceSemantics.evalArgs_cons_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.SourceSemantics.evalArgs_cons_iff

/--
info: @Generic.SourceSemantics.evalExpr_assertEq_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {world : Generic.SourceSemantics.World F} {types : Generic.SourceSemantics.Types} {locals : Environment F ℕ}
  {assertion : Assertion} {lhs rhs : Generic.Expr F} {before : Heap F} {result : SourceValue F} {after : Heap F},
  Generic.SourceSemantics.EvalExpr world types locals
      (Generic.Expr.builtin (Generic.Builtin.assertEq assertion) [lhs, rhs]) before result after ↔
    ∃ x middle y,
      Generic.SourceSemantics.EvalExpr world types locals lhs before x middle ∧
        Generic.SourceSemantics.EvalExpr world types locals rhs middle y after ∧
          evalAssertEq assertion x y = Except.ok result
-/
#guard_msgs in
#check @Aiur.Generic.SourceSemantics.evalExpr_assertEq_iff
/-- info: 'Aiur.Generic.SourceSemantics.evalExpr_assertEq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.SourceSemantics.evalExpr_assertEq_iff

/--
info: @Generic.SourceSemantics.evalExpr_binary_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {world : Generic.SourceSemantics.World F} {types : Generic.SourceSemantics.Types} {locals : Environment F ℕ}
  {op : BinOp} {lhs rhs : Generic.Expr F} {before : Heap F} {result : SourceValue F} {after : Heap F},
  Generic.SourceSemantics.EvalExpr world types locals (Generic.Expr.binary op lhs rhs) before result after ↔
    ∃ x middle y,
      Generic.SourceSemantics.EvalExpr world types locals lhs before x middle ∧
        Generic.SourceSemantics.EvalExpr world types locals rhs middle y after ∧ evalBinOp op x y = Except.ok result
-/
#guard_msgs in
#check @Aiur.Generic.SourceSemantics.evalExpr_binary_iff
/-- info: 'Aiur.Generic.SourceSemantics.evalExpr_binary_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.SourceSemantics.evalExpr_binary_iff

/--
info: @Generic.SourceSemantics.evalExpr_neg_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {world : Generic.SourceSemantics.World F} {types : Generic.SourceSemantics.Types} {locals : Environment F ℕ}
  {expr : Generic.Expr F} {before : Heap F} {result : SourceValue F} {after : Heap F},
  Generic.SourceSemantics.EvalExpr world types locals expr.neg before result after ↔
    ∃ input,
      Generic.SourceSemantics.EvalExpr world types locals expr before input after ∧ evalNeg input = Except.ok result
-/
#guard_msgs in
#check @Aiur.Generic.SourceSemantics.evalExpr_neg_iff
/-- info: 'Aiur.Generic.SourceSemantics.evalExpr_neg_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.SourceSemantics.evalExpr_neg_iff

/--
info: @Generic.SourceSemantics.evalExpr_block_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {world : Generic.SourceSemantics.World F} {types : Generic.SourceSemantics.Types} {locals : Environment F ℕ}
  {label : String} {expr : Generic.Expr F} {before : Heap F} {result : SourceValue F} {after : Heap F},
  Generic.SourceSemantics.EvalExpr world types locals (Generic.Expr.control (Generic.Control.block label) expr) before
      result after ↔
    Generic.SourceSemantics.EvalExpr world types locals expr before result after ∨
      Generic.SourceSemantics.EvalExit world types locals expr before (Generic.ExitTarget.block label) result after
-/
#guard_msgs in
#check @Aiur.Generic.SourceSemantics.evalExpr_block_iff
/-- info: 'Aiur.Generic.SourceSemantics.evalExpr_block_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.SourceSemantics.evalExpr_block_iff

/--
info: @Generic.SourceSemantics.evalExpr_call_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {world : Generic.SourceSemantics.World F} {types : Generic.SourceSemantics.Types} {locals : Environment F ℕ}
  {name : String} {typeArgs : Option (List Generic.Ty)} {args : List (Generic.Expr F)} {before : Heap F}
  {result : SourceValue F} {after : Heap F},
  Generic.SourceSemantics.EvalExpr world types locals (Generic.Expr.call name typeArgs args) before result after ↔
    ∃ values middle,
      Generic.SourceSemantics.EvalArgs world types locals args before values middle ∧
        Generic.SourceSemantics.EvalFn world (Generic.SourceSemantics.instanceName types name typeArgs) values middle
          result after
-/
#guard_msgs in
#check @Aiur.Generic.SourceSemantics.evalExpr_call_iff
/-- info: 'Aiur.Generic.SourceSemantics.evalExpr_call_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.SourceSemantics.evalExpr_call_iff

/--
info: @Generic.SourceSemantics.evalExpr_matchValue_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {world : Generic.SourceSemantics.World F} {types : Generic.SourceSemantics.Types} {locals : Environment F ℕ}
  {expr : Generic.Expr F} {arms : List (Generic.Pattern F × Generic.Expr F)} {before : Heap F} {result : SourceValue F}
  {after : Heap F},
  Generic.SourceSemantics.EvalExpr world types locals (expr.matchValue arms) before result after ↔
    ∃ input middle bindings body,
      Generic.SourceSemantics.EvalExpr world types locals expr before input middle ∧
        Generic.SourceSemantics.selectArm world types middle input arms = Except.ok (some (bindings, body)) ∧
          Generic.SourceSemantics.EvalExpr world types (bindings ++ locals) body middle result after
-/
#guard_msgs in
#check @Aiur.Generic.SourceSemantics.evalExpr_matchValue_iff
/-- info: 'Aiur.Generic.SourceSemantics.evalExpr_matchValue_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.SourceSemantics.evalExpr_matchValue_iff

/--
info: @Generic.SourceSemantics.evalFn_step_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {world : Generic.SourceSemantics.World F} {name : String} {args : List (SourceValue F)} {before : Heap F}
  {result : SourceValue F} {after : Heap F},
  Generic.SourceSemantics.EvalFn world name args before result after ↔
    ∃ types locals expr,
      world.prepare name args = Except.ok (types, locals, expr) ∧
        (Generic.SourceSemantics.EvalExpr world types locals expr before result after ∨
          Generic.SourceSemantics.EvalExit world types locals expr before Generic.ExitTarget.function result after)
-/
#guard_msgs in
#check @Aiur.Generic.SourceSemantics.evalFn_step_iff
/-- info: 'Aiur.Generic.SourceSemantics.evalFn_step_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.SourceSemantics.evalFn_step_iff

/--
info: @Generic.SourceSemantics.evalExpr_let_hint_invariance : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F]
  {world : Generic.SourceSemantics.World F} {types : Generic.SourceSemantics.Types} {locals : Environment F ℕ}
  {pattern : Generic.Pattern F} {t : Generic.Ty} {keyExpr : Generic.Expr F} {channel : String} {rest : Generic.Expr F}
  {before : Heap F} {result : SourceValue F} {after : Heap F} {P : Constant F → SourceValue F → Heap F → Prop},
  Generic.SourceSemantics.EvalExpr world types locals
      (Generic.Expr.letValue pattern (Generic.Expr.hint t keyExpr channel) rest) before result after →
    (∀ (c : Constant F) (middle : Heap F) (bindings : Environment F ℕ),
        world.typed (Generic.Ty.subst types t).toCore c = true →
          world.matchPattern types middle pattern c.toValue = Except.ok (some bindings) →
            Generic.SourceSemantics.EvalExpr world types (bindings ++ locals) rest middle result after →
              P c result after) →
      ∃ c, world.typed (Generic.Ty.subst types t).toCore c = true ∧ P c result after
-/
#guard_msgs in
#check @Aiur.Generic.SourceSemantics.evalExpr_let_hint_invariance
/-- info: 'Aiur.Generic.SourceSemantics.evalExpr_let_hint_invariance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Generic.SourceSemantics.evalExpr_let_hint_invariance

/--
info: @Modules.Prepared.evalFn_iff : ∀ {F : Type} [inst : Field F] [inst_1 : DecidableEq F] {program : Modules.Program F}
  {p : Modules.Prepared program} {name : String} {args : List (SourceValue F)} {value : SourceValue F} {heap : Heap F},
  p.EvalFn name args value heap ↔
    ∃ entry,
      p.find? name = some entry ∧
        Generic.SourceSemantics.EvalFn p.environment.source.world entry.resolved.name args [] value heap
-/
#guard_msgs in
#check @Aiur.Modules.Prepared.evalFn_iff
/-- info: 'Aiur.Modules.Prepared.evalFn_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Modules.Prepared.evalFn_iff


/-! ## Red-Black Tree (`RBTreeMap` / `RoleMap`) Correctness (`Aiur.Library.RBTreeMap.Correctness`) -/

/--
info: @Library.RBTreeMap.LawfulCmp.cmp_refl : ∀ {K : Type u_1} {cmp : K → K → Ordering},
  Library.RBTreeMap.LawfulCmp cmp → ∀ (x : K), cmp x x = Ordering.eq
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.LawfulCmp.cmp_refl
/-- info: 'Aiur.Library.RBTreeMap.LawfulCmp.cmp_refl' does not depend on any axioms -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.LawfulCmp.cmp_refl

/--
info: @Library.RBTreeMap.LawfulCmp.lt_irrefl : ∀ {K : Type u_1} {cmp : K → K → Ordering},
  Library.RBTreeMap.LawfulCmp cmp → ∀ (x : K), cmp x x ≠ Ordering.lt
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.LawfulCmp.lt_irrefl
/-- info: 'Aiur.Library.RBTreeMap.LawfulCmp.lt_irrefl' does not depend on any axioms -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.LawfulCmp.lt_irrefl

/--
info: @Library.RBTreeMap.LawfulCmp.gt_irrefl : ∀ {K : Type u_1} {cmp : K → K → Ordering},
  Library.RBTreeMap.LawfulCmp cmp → ∀ (x : K), cmp x x ≠ Ordering.gt
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.LawfulCmp.gt_irrefl
/-- info: 'Aiur.Library.RBTreeMap.LawfulCmp.gt_irrefl' does not depend on any axioms -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.LawfulCmp.gt_irrefl

/--
info: @Library.RBTreeMap.LawfulCmp.lt_asymm : ∀ {K : Type u_1} {cmp : K → K → Ordering},
  Library.RBTreeMap.LawfulCmp cmp → ∀ {x y : K}, cmp x y = Ordering.lt → cmp y x ≠ Ordering.lt
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.LawfulCmp.lt_asymm
/-- info: 'Aiur.Library.RBTreeMap.LawfulCmp.lt_asymm' does not depend on any axioms -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.LawfulCmp.lt_asymm

/--
info: @Library.RBTreeMap.LawfulCmp.lt_ne : ∀ {K : Type u_1} {cmp : K → K → Ordering},
  Library.RBTreeMap.LawfulCmp cmp → ∀ {x y : K}, cmp x y = Ordering.lt → x ≠ y
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.LawfulCmp.lt_ne
/-- info: 'Aiur.Library.RBTreeMap.LawfulCmp.lt_ne' does not depend on any axioms -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.LawfulCmp.lt_ne

/--
info: @Library.RBTreeMap.LawfulCmp.gt_of_lt : ∀ {K : Type u_1} {cmp : K → K → Ordering},
  Library.RBTreeMap.LawfulCmp cmp → ∀ {x y : K}, cmp x y = Ordering.lt → cmp y x = Ordering.gt
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.LawfulCmp.gt_of_lt
/-- info: 'Aiur.Library.RBTreeMap.LawfulCmp.gt_of_lt' does not depend on any axioms -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.LawfulCmp.gt_of_lt

/--
info: @Library.RBTreeMap.LawfulCmp.lt_of_gt : ∀ {K : Type u_1} {cmp : K → K → Ordering},
  Library.RBTreeMap.LawfulCmp cmp → ∀ {x y : K}, cmp x y = Ordering.gt → cmp y x = Ordering.lt
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.LawfulCmp.lt_of_gt
/-- info: 'Aiur.Library.RBTreeMap.LawfulCmp.lt_of_gt' does not depend on any axioms -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.LawfulCmp.lt_of_gt

/--
info: @Library.RBTreeMap.LawfulCmp.trichotomous : ∀ {K : Type u_1} {cmp : K → K → Ordering},
  Library.RBTreeMap.LawfulCmp cmp → ∀ (x y : K), cmp x y = Ordering.lt ∨ x = y ∨ cmp y x = Ordering.lt
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.LawfulCmp.trichotomous
/-- info: 'Aiur.Library.RBTreeMap.LawfulCmp.trichotomous' does not depend on any axioms -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.LawfulCmp.trichotomous

/-- info: Library.RBTreeMap.lawfulCmp_nat : Library.RBTreeMap.LawfulCmp compare -/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.lawfulCmp_nat
/-- info: 'Aiur.Library.RBTreeMap.lawfulCmp_nat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.lawfulCmp_nat

/--
info: Library.RBTreeMap.canonOrdThen_assoc : ∀ (a b c : Ordering),
  Library.RBTreeMap.canonOrdThen (Library.RBTreeMap.canonOrdThen a b) c =
    Library.RBTreeMap.canonOrdThen a (Library.RBTreeMap.canonOrdThen b c)
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.canonOrdThen_assoc
/-- info: 'Aiur.Library.RBTreeMap.canonOrdThen_assoc' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.canonOrdThen_assoc

/--
info: @Library.RBTreeMap.lexCmpNat_append : ∀ {xs₁ ys₁ : List ℕ},
  xs₁.length = ys₁.length →
    ∀ (xs₂ ys₂ : List ℕ),
      Library.RBTreeMap.lexCmpNat (xs₁ ++ xs₂) (ys₁ ++ ys₂) =
        Library.RBTreeMap.canonOrdThen (Library.RBTreeMap.lexCmpNat xs₁ ys₁) (Library.RBTreeMap.lexCmpNat xs₂ ys₂)
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.lexCmpNat_append
/-- info: 'Aiur.Library.RBTreeMap.lexCmpNat_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.lexCmpNat_append

/-- info: Library.RBTreeMap.lawfulCmp_lexCmpNat : Library.RBTreeMap.LawfulCmp Library.RBTreeMap.lexCmpNat -/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.lawfulCmp_lexCmpNat
/-- info: 'Aiur.Library.RBTreeMap.lawfulCmp_lexCmpNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.lawfulCmp_lexCmpNat

/--
info: Library.RBTreeMap.compare_chunkVal_eq_lexCmpNat : ∀ (x0 x1 x2 x3 y0 y1 y2 y3 : UInt8),
  compare (Library.RBTreeMap.chunkVal x0 x1 x2 x3) (Library.RBTreeMap.chunkVal y0 y1 y2 y3) =
    Library.RBTreeMap.lexCmpNat [x0.toNat, x1.toNat, x2.toNat, x3.toNat] [y0.toNat, y1.toNat, y2.toNat, y3.toNat]
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.compare_chunkVal_eq_lexCmpNat
/-- info: 'Aiur.Library.RBTreeMap.compare_chunkVal_eq_lexCmpNat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.compare_chunkVal_eq_lexCmpNat

/-- info: Library.RBTreeMap.lawfulCmp_canonAddrCmp : Library.RBTreeMap.LawfulCmp Library.RBTreeMap.canonAddrCmp -/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.lawfulCmp_canonAddrCmp
/-- info: 'Aiur.Library.RBTreeMap.lawfulCmp_canonAddrCmp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.lawfulCmp_canonAddrCmp

/-- info: Library.RBTreeMap.canon_addr_cmp_refl : ∀ (x : Library.Bytes.Address), Library.RBTreeMap.canonAddrCmp x x = Ordering.eq -/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.canon_addr_cmp_refl
/-- info: 'Aiur.Library.RBTreeMap.canon_addr_cmp_refl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.canon_addr_cmp_refl

/--
info: Library.RBTreeMap.canon_addr_cmp_eq_iff : ∀ (x y : Library.Bytes.Address),
  Library.RBTreeMap.canonAddrCmp x y = Ordering.eq ↔ x = y
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.canon_addr_cmp_eq_iff
/-- info: 'Aiur.Library.RBTreeMap.canon_addr_cmp_eq_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.canon_addr_cmp_eq_iff

/-- info: Library.RBTreeMap.canon_addr_cmp_irrefl : ∀ (x : Library.Bytes.Address), ¬Library.RBTreeMap.canonAddrLt x x -/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.canon_addr_cmp_irrefl
/-- info: 'Aiur.Library.RBTreeMap.canon_addr_cmp_irrefl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.canon_addr_cmp_irrefl

/--
info: @Library.RBTreeMap.canon_addr_cmp_trans : ∀ {x y z : Library.Bytes.Address},
  Library.RBTreeMap.canonAddrLt x y → Library.RBTreeMap.canonAddrLt y z → Library.RBTreeMap.canonAddrLt x z
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.canon_addr_cmp_trans
/-- info: 'Aiur.Library.RBTreeMap.canon_addr_cmp_trans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.canon_addr_cmp_trans

/--
info: @Library.RBTreeMap.canon_addr_cmp_asymm : ∀ {x y : Library.Bytes.Address},
  Library.RBTreeMap.canonAddrLt x y → ¬Library.RBTreeMap.canonAddrLt y x
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.canon_addr_cmp_asymm
/-- info: 'Aiur.Library.RBTreeMap.canon_addr_cmp_asymm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.canon_addr_cmp_asymm

/--
info: Library.RBTreeMap.canon_addr_cmp_trichotomous : ∀ (x y : Library.Bytes.Address),
  Library.RBTreeMap.canonAddrLt x y ∨ x = y ∨ Library.RBTreeMap.canonAddrLt y x
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.canon_addr_cmp_trichotomous
/-- info: 'Aiur.Library.RBTreeMap.canon_addr_cmp_trichotomous' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.canon_addr_cmp_trichotomous

/--
info: Library.RBTreeMap.canon_addr_cmp_gt_iff : ∀ (x y : Library.Bytes.Address),
  Library.RBTreeMap.canonAddrCmp x y = Ordering.gt ↔ Library.RBTreeMap.canonAddrLt y x
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.canon_addr_cmp_gt_iff
/-- info: 'Aiur.Library.RBTreeMap.canon_addr_cmp_gt_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.canon_addr_cmp_gt_iff

/--
info: @Library.RBTreeMap.RBTree.ofBinaryTree_toBinaryTree : ∀ {K : Type u_1} {V : Type u_2}
  (t : Library.RBTreeMap.RBTree K V), Library.RBTreeMap.RBTree.ofBinaryTree t.toBinaryTree = t
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.RBTree.ofBinaryTree_toBinaryTree
/-- info: 'Aiur.Library.RBTreeMap.RBTree.ofBinaryTree_toBinaryTree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.RBTree.ofBinaryTree_toBinaryTree

/--
info: @Library.RBTreeMap.RBTree.toBinaryTree_ofBinaryTree : ∀ {K : Type u_1} {V : Type u_2} (t : BinaryTree (ℕ × K × V)),
  (Library.RBTreeMap.RBTree.ofBinaryTree t).toBinaryTree = t
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.RBTree.toBinaryTree_ofBinaryTree
/-- info: 'Aiur.Library.RBTreeMap.RBTree.toBinaryTree_ofBinaryTree' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.RBTree.toBinaryTree_ofBinaryTree

/--
info: @Library.RBTreeMap.RepRBTreePtr.mono : ∀ {F : Type} {K : Type u_1} {V : Type u_2} {enumName nilCtor nodeCtor : String}
  {RLabel : Heap F → ℕ × K × V → SourceValue F → Prop},
  HeapMono₂ RLabel →
    ∀ {h₁ h₂ : Heap F} {t : Library.RBTreeMap.RBTree K V} {ptr : SourceValue F},
      h₁.Extends h₂ →
        Library.RBTreeMap.RepRBTreePtr enumName nilCtor nodeCtor RLabel h₁ t ptr →
          Library.RBTreeMap.RepRBTreePtr enumName nilCtor nodeCtor RLabel h₂ t ptr
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.RepRBTreePtr.mono
/-- info: 'Aiur.Library.RBTreeMap.RepRBTreePtr.mono' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.RepRBTreePtr.mono

/--
info: @Library.RBTreeMap.HeapMono.repRBTreePtr : ∀ {F : Type} {K : Type u_1} {V : Type u_2}
  (enumName nilCtor nodeCtor : String) {RLabel : Heap F → ℕ × K × V → SourceValue F → Prop},
  HeapMono₂ RLabel →
    ∀ (t : Library.RBTreeMap.RBTree K V),
      HeapMono fun h ptr => Library.RBTreeMap.RepRBTreePtr enumName nilCtor nodeCtor RLabel h t ptr
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.HeapMono.repRBTreePtr
/-- info: 'Aiur.Library.RBTreeMap.HeapMono.repRBTreePtr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.HeapMono.repRBTreePtr

/--
info: @Library.RBTreeMap.balanceFix_cases : ∀ {K : Type u_1} {V : Type u_2} (k : K) (v : V)
  (left right : Library.RBTreeMap.RBTree K V),
  (∃ yk yv xk xv a b c,
      left = Library.RBTreeMap.RBTree.node 0 yk yv (Library.RBTreeMap.RBTree.node 0 xk xv a b) c ∧
        Library.RBTreeMap.balanceFix k v left right =
          Library.RBTreeMap.RBTree.node 0 yk yv (Library.RBTreeMap.RBTree.node 1 xk xv a b)
            (Library.RBTreeMap.RBTree.node 1 k v c right)) ∨
    (∃ xk xv a yk yv b c,
        left = Library.RBTreeMap.RBTree.node 0 xk xv a (Library.RBTreeMap.RBTree.node 0 yk yv b c) ∧
          Library.RBTreeMap.balanceFix k v left right =
            Library.RBTreeMap.RBTree.node 0 yk yv (Library.RBTreeMap.RBTree.node 1 xk xv a b)
              (Library.RBTreeMap.RBTree.node 1 k v c right)) ∨
      (∃ zk zv yk yv b c d,
          right = Library.RBTreeMap.RBTree.node 0 zk zv (Library.RBTreeMap.RBTree.node 0 yk yv b c) d ∧
            Library.RBTreeMap.balanceFix k v left right =
              Library.RBTreeMap.RBTree.node 0 yk yv (Library.RBTreeMap.RBTree.node 1 k v left b)
                (Library.RBTreeMap.RBTree.node 1 zk zv c d)) ∨
        (∃ yk yv b zk zv c d,
            right = Library.RBTreeMap.RBTree.node 0 yk yv b (Library.RBTreeMap.RBTree.node 0 zk zv c d) ∧
              Library.RBTreeMap.balanceFix k v left right =
                Library.RBTreeMap.RBTree.node 0 yk yv (Library.RBTreeMap.RBTree.node 1 k v left b)
                  (Library.RBTreeMap.RBTree.node 1 zk zv c d)) ∨
          Library.RBTreeMap.balanceFix k v left right = Library.RBTreeMap.RBTree.node 1 k v left right
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.balanceFix_cases
/-- info: 'Aiur.Library.RBTreeMap.balanceFix_cases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.balanceFix_cases

/--
info: @Library.RBTreeMap.AllKeys.imp : ∀ {K : Type u_1} {V : Type u_2} {P Q : K → Prop},
  (∀ (x : K), P x → Q x) →
    ∀ {t : Library.RBTreeMap.RBTree K V}, Library.RBTreeMap.AllKeys P t → Library.RBTreeMap.AllKeys Q t
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.AllKeys.imp
/-- info: 'Aiur.Library.RBTreeMap.AllKeys.imp' does not depend on any axioms -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.AllKeys.imp

/--
info: @Library.RBTreeMap.allKeys_balanceFix : ∀ {K : Type u_1} {V : Type u_2} (P : K → Prop) (k : K) (v : V)
  (left right : Library.RBTreeMap.RBTree K V),
  Library.RBTreeMap.AllKeys P (Library.RBTreeMap.balanceFix k v left right) ↔
    P k ∧ Library.RBTreeMap.AllKeys P left ∧ Library.RBTreeMap.AllKeys P right
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.allKeys_balanceFix
/-- info: 'Aiur.Library.RBTreeMap.allKeys_balanceFix' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.allKeys_balanceFix

/--
info: @Library.RBTreeMap.allKeys_balance : ∀ {K : Type u_1} {V : Type u_2} (P : K → Prop) (color : ℕ) (k : K) (v : V)
  (left right : Library.RBTreeMap.RBTree K V),
  Library.RBTreeMap.AllKeys P (Library.RBTreeMap.balance color k v left right) ↔
    P k ∧ Library.RBTreeMap.AllKeys P left ∧ Library.RBTreeMap.AllKeys P right
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.allKeys_balance
/-- info: 'Aiur.Library.RBTreeMap.allKeys_balance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.allKeys_balance

/--
info: @Library.RBTreeMap.allKeys_ins : ∀ {K : Type u_1} {V : Type u_2} {cmp : K → K → Ordering},
  Library.RBTreeMap.LawfulCmp cmp →
    ∀ (P : K → Prop) (k : K) (v : V) (t : Library.RBTreeMap.RBTree K V),
      Library.RBTreeMap.AllKeys P (Library.RBTreeMap.ins cmp k v t) ↔ P k ∧ Library.RBTreeMap.AllKeys P t
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.allKeys_ins
/-- info: 'Aiur.Library.RBTreeMap.allKeys_ins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.allKeys_ins

/--
info: @Library.RBTreeMap.rbtree_bst_balance : ∀ {K : Type u_1} {V : Type u_2} {cmp : K → K → Ordering},
  Library.RBTreeMap.LawfulCmp cmp →
    ∀ (color : ℕ) (k : K) (v : V) (left right : Library.RBTreeMap.RBTree K V),
      Library.RBTreeMap.AllKeys (fun x => cmp x k = Ordering.lt) left →
        Library.RBTreeMap.AllKeys (fun x => cmp k x = Ordering.lt) right →
          Library.RBTreeMap.BST cmp left →
            Library.RBTreeMap.BST cmp right → Library.RBTreeMap.BST cmp (Library.RBTreeMap.balance color k v left right)
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.rbtree_bst_balance
/-- info: 'Aiur.Library.RBTreeMap.rbtree_bst_balance' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.rbtree_bst_balance

/--
info: @Library.RBTreeMap.rbtree_bst_ins : ∀ {K : Type u_1} {V : Type u_2} {cmp : K → K → Ordering},
  Library.RBTreeMap.LawfulCmp cmp →
    ∀ (k : K) (v : V) {t : Library.RBTreeMap.RBTree K V},
      Library.RBTreeMap.BST cmp t → Library.RBTreeMap.BST cmp (Library.RBTreeMap.ins cmp k v t)
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.rbtree_bst_ins
/-- info: 'Aiur.Library.RBTreeMap.rbtree_bst_ins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.rbtree_bst_ins

/--
info: @Library.RBTreeMap.rbtree_bst_insert : ∀ {K : Type u_1} {V : Type u_2} {cmp : K → K → Ordering},
  Library.RBTreeMap.LawfulCmp cmp →
    ∀ (k : K) (v : V) {t : Library.RBTreeMap.RBTree K V},
      Library.RBTreeMap.BST cmp t → Library.RBTreeMap.BST cmp (Library.RBTreeMap.rbtreeInsert cmp k v t)
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.rbtree_bst_insert
/-- info: 'Aiur.Library.RBTreeMap.rbtree_bst_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.rbtree_bst_insert

/--
info: @Library.RBTreeMap.balance_lookup_eq : ∀ {K : Type u_1} {V : Type u_2} {cmp : K → K → Ordering},
  Library.RBTreeMap.LawfulCmp cmp →
    ∀ (color : ℕ) (k : K) (v : V) (left right : Library.RBTreeMap.RBTree K V),
      Library.RBTreeMap.AllKeys (fun x => cmp x k = Ordering.lt) left →
        Library.RBTreeMap.AllKeys (fun x => cmp k x = Ordering.lt) right →
          Library.RBTreeMap.BST cmp left →
            Library.RBTreeMap.BST cmp right →
              ∀ (q : K),
                Library.RBTreeMap.rbtreeGet cmp q (Library.RBTreeMap.balance color k v left right) =
                  Library.RBTreeMap.rbtreeGet cmp q (Library.RBTreeMap.RBTree.node color k v left right)
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.balance_lookup_eq
/-- info: 'Aiur.Library.RBTreeMap.balance_lookup_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.balance_lookup_eq

/--
info: @Library.RBTreeMap.ins_lookup_eq : ∀ {K : Type u_1} {V : Type u_2} [inst : DecidableEq K] {cmp : K → K → Ordering},
  Library.RBTreeMap.LawfulCmp cmp →
    ∀ (k : K) (v : V) {t : Library.RBTreeMap.RBTree K V},
      Library.RBTreeMap.BST cmp t →
        ∀ (q : K),
          Library.RBTreeMap.rbtreeGet cmp q (Library.RBTreeMap.ins cmp k v t) =
            if q = k then some v else Library.RBTreeMap.rbtreeGet cmp q t
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.ins_lookup_eq
/-- info: 'Aiur.Library.RBTreeMap.ins_lookup_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.ins_lookup_eq

/--
info: @Library.RBTreeMap.rbtree_get_insert : ∀ {K : Type u_1} {V : Type u_2} [inst : DecidableEq K] {cmp : K → K → Ordering},
  Library.RBTreeMap.LawfulCmp cmp →
    ∀ (k : K) (v : V) {t : Library.RBTreeMap.RBTree K V},
      Library.RBTreeMap.BST cmp t →
        ∀ (q : K),
          Library.RBTreeMap.rbtreeGet cmp q (Library.RBTreeMap.rbtreeInsert cmp k v t) =
            if q = k then some v else Library.RBTreeMap.rbtreeGet cmp q t
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.rbtree_get_insert
/-- info: 'Aiur.Library.RBTreeMap.rbtree_get_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.rbtree_get_insert

/--
info: @Library.RBTreeMap.rbtree_get_insert_self : ∀ {K : Type u_1} {V : Type u_2} [DecidableEq K] {cmp : K → K → Ordering},
  Library.RBTreeMap.LawfulCmp cmp →
    ∀ (k : K) (v : V) {t : Library.RBTreeMap.RBTree K V},
      Library.RBTreeMap.BST cmp t →
        Library.RBTreeMap.rbtreeGet cmp k (Library.RBTreeMap.rbtreeInsert cmp k v t) = some v
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.rbtree_get_insert_self
/-- info: 'Aiur.Library.RBTreeMap.rbtree_get_insert_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.rbtree_get_insert_self

/--
info: @Library.RBTreeMap.rbtree_get_insert_ne : ∀ {K : Type u_1} {V : Type u_2} [DecidableEq K] {cmp : K → K → Ordering},
  Library.RBTreeMap.LawfulCmp cmp →
    ∀ (k : K) (v : V) {t : Library.RBTreeMap.RBTree K V},
      Library.RBTreeMap.BST cmp t →
        ∀ {q : K},
          q ≠ k →
            Library.RBTreeMap.rbtreeGet cmp q (Library.RBTreeMap.rbtreeInsert cmp k v t) =
              Library.RBTreeMap.rbtreeGet cmp q t
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.rbtree_get_insert_ne
/-- info: 'Aiur.Library.RBTreeMap.rbtree_get_insert_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.rbtree_get_insert_ne

/--
info: @Library.RBTreeMap.mem_toList_imp_allKeys : ∀ {K : Type u_1} {V : Type u_2} {P : K → Prop}
  {t : Library.RBTreeMap.RBTree K V}, Library.RBTreeMap.AllKeys P t → ∀ {p : K × V}, p ∈ t.toList → P p.1
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.mem_toList_imp_allKeys
/-- info: 'Aiur.Library.RBTreeMap.mem_toList_imp_allKeys' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.mem_toList_imp_allKeys

/--
info: @Library.RBTreeMap.allKeys_iff_forall_mem_toList : ∀ {K : Type u_1} {V : Type u_2} (P : K → Prop)
  (t : Library.RBTreeMap.RBTree K V), Library.RBTreeMap.AllKeys P t ↔ ∀ p ∈ t.toList, P p.1
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.allKeys_iff_forall_mem_toList
/-- info: 'Aiur.Library.RBTreeMap.allKeys_iff_forall_mem_toList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.allKeys_iff_forall_mem_toList

/--
info: @Library.RBTreeMap.rbtreeGet_eq_some_iff_mem_toList : ∀ {K : Type u_1} {V : Type u_2} {cmp : K → K → Ordering},
  Library.RBTreeMap.LawfulCmp cmp →
    ∀ {t : Library.RBTreeMap.RBTree K V},
      Library.RBTreeMap.BST cmp t → ∀ (q : K) (v : V), Library.RBTreeMap.rbtreeGet cmp q t = some v ↔ (q, v) ∈ t.toList
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.rbtreeGet_eq_some_iff_mem_toList
/-- info: 'Aiur.Library.RBTreeMap.rbtreeGet_eq_some_iff_mem_toList' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.rbtreeGet_eq_some_iff_mem_toList

/--
info: @Library.RBTreeMap.rbtreeGet_eq_none_iff_forall_ne : ∀ {K : Type u_1} {V : Type u_2} {cmp : K → K → Ordering},
  Library.RBTreeMap.LawfulCmp cmp →
    ∀ {t : Library.RBTreeMap.RBTree K V},
      Library.RBTreeMap.BST cmp t → ∀ (q : K), Library.RBTreeMap.rbtreeGet cmp q t = none ↔ ∀ p ∈ t.toList, p.1 ≠ q
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.rbtreeGet_eq_none_iff_forall_ne
/-- info: 'Aiur.Library.RBTreeMap.rbtreeGet_eq_none_iff_forall_ne' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.rbtreeGet_eq_none_iff_forall_ne

/--
info: @Library.RBTreeMap.toList_buildBalancedTree : ∀ {K : Type u_1} {V : Type u_2} (entries : List (K × V)),
  (Library.RBTreeMap.buildBalancedTree entries).toList = entries
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.toList_buildBalancedTree
/-- info: 'Aiur.Library.RBTreeMap.toList_buildBalancedTree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.toList_buildBalancedTree

/--
info: @Library.RBTreeMap.bst_buildBalancedTree : ∀ {K : Type u_1} {V : Type u_2} {cmp : K → K → Ordering}
  {entries : List (K × V)},
  List.Pairwise (fun a b => cmp a.1 b.1 = Ordering.lt) entries →
    Library.RBTreeMap.BST cmp (Library.RBTreeMap.buildBalancedTree entries)
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.bst_buildBalancedTree
/-- info: 'Aiur.Library.RBTreeMap.bst_buildBalancedTree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.bst_buildBalancedTree

/--
info: @Library.RBTreeMap.role_tree_get_eq_some_iff : ∀ {K : Type u_1} {V : Type u_2} {cmp : K → K → Ordering},
  Library.RBTreeMap.LawfulCmp cmp →
    ∀ {entries : List (K × V)},
      List.Pairwise (fun a b => cmp a.1 b.1 = Ordering.lt) entries →
        ∀ (q : K) (v : V),
          Library.RBTreeMap.rbtreeGet cmp q (Library.RBTreeMap.buildBalancedTree entries) = some v ↔ (q, v) ∈ entries
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.role_tree_get_eq_some_iff
/-- info: 'Aiur.Library.RBTreeMap.role_tree_get_eq_some_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.role_tree_get_eq_some_iff

/--
info: @Library.RBTreeMap.role_tree_get_eq_none_iff : ∀ {K : Type u_1} {V : Type u_2} {cmp : K → K → Ordering},
  Library.RBTreeMap.LawfulCmp cmp →
    ∀ {entries : List (K × V)},
      List.Pairwise (fun a b => cmp a.1 b.1 = Ordering.lt) entries →
        ∀ (q : K),
          Library.RBTreeMap.rbtreeGet cmp q (Library.RBTreeMap.buildBalancedTree entries) = none ↔
            ∀ p ∈ entries, p.1 ≠ q
-/
#guard_msgs in
#check @Aiur.Library.RBTreeMap.role_tree_get_eq_none_iff
/-- info: 'Aiur.Library.RBTreeMap.role_tree_get_eq_none_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.RBTreeMap.role_tree_get_eq_none_iff

/-! ### 9. `IxVM` Representation Predicates, Monotonicity, Determinism, and Deserialization (`IxVMRep`) -/

/--
info: @Library.IxVMRep.nat_lt_256_inj : ∀ {F : Type} [inst : Field F],
  Library.U32.Compatible F → ∀ {a b : ℕ}, a < 256 → b < 256 → ↑a = ↑b → a = b
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.nat_lt_256_inj
/-- info: 'Aiur.Library.IxVMRep.nat_lt_256_inj' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.nat_lt_256_inj

/--
info: @Library.IxVMRep.repU32_det : ∀ {F : Type} [inst : Field F],
  Library.U32.Compatible F →
    ∀ {h : Heap F} {w₁ w₂ : UInt32} {v : SourceValue F}, Library.RepU32 h w₁ v → Library.RepU32 h w₂ v → w₁ = w₂
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.repU32_det
/-- info: 'Aiur.Library.IxVMRep.repU32_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.repU32_det

/--
info: @Library.IxVMRep.repU64_det : ∀ {F : Type} [inst : Field F],
  Library.U32.Compatible F →
    ∀ {h : Heap F} {w₁ w₂ : UInt64} {v : SourceValue F}, Library.RepU64 h w₁ v → Library.RepU64 h w₂ v → w₁ = w₂
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.repU64_det
/-- info: 'Aiur.Library.IxVMRep.repU64_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.repU64_det

/--
info: @Library.IxVMRep.repAddress_det : ∀ {F : Type} [inst : Field F],
  Library.U32.Compatible F →
    ∀ {h : Heap F} {a₁ a₂ : Library.Bytes.Address} {v : SourceValue F},
      Library.Bytes.RepAddress h a₁ v → Library.Bytes.RepAddress h a₂ v → a₁ = a₂
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.repAddress_det
/-- info: 'Aiur.Library.IxVMRep.repAddress_det' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.repAddress_det

/--
info: @Library.IxVMRep.repAddressRef_det : ∀ {F : Type} [inst : Field F],
  Library.U32.Compatible F →
    ∀ {ty : Ty} {h : Heap F} {a₁ a₂ : Library.Bytes.Address} {ptr : SourceValue F},
      Library.Bytes.RepAddressRef ty h a₁ ptr → Library.Bytes.RepAddressRef ty h a₂ ptr → a₁ = a₂
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.repAddressRef_det
/-- info: 'Aiur.Library.IxVMRep.repAddressRef_det' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.repAddressRef_det

/--
info: @Library.IxVMRep.repOption_det : ∀ {F : Type} {α : Type u_1} {enumName : String} {R : Heap F → α → SourceValue F → Prop}
  {h : Heap F},
  (∀ {x₁ x₂ : α} {v : SourceValue F}, R h x₁ v → R h x₂ v → x₁ = x₂) →
    ∀ {o₁ o₂ : Option α} {v : SourceValue F},
      Library.RepOption enumName R h o₁ v → Library.RepOption enumName R h o₂ v → o₁ = o₂
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.repOption_det
/-- info: 'Aiur.Library.IxVMRep.repOption_det' does not depend on any axioms -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.repOption_det

/--
info: @Library.IxVMRep.repLinkedList_det : ∀ {F : Type} {α : Type u_1} {enumName nilCtor consCtor : String},
  nilCtor ≠ consCtor →
    ∀ {R : Heap F → α → SourceValue F → Prop} {h : Heap F},
      (∀ {x₁ x₂ : α} {v : SourceValue F}, R h x₁ v → R h x₂ v → x₁ = x₂) →
        ∀ {xs₁ xs₂ : List α} {ptr : SourceValue F},
          RepLinkedList enumName nilCtor consCtor R h xs₁ ptr →
            RepLinkedList enumName nilCtor consCtor R h xs₂ ptr → xs₁ = xs₂
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.repLinkedList_det
/-- info: 'Aiur.Library.IxVMRep.repLinkedList_det' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.repLinkedList_det

/--
info: @Library.IxVMRep.repList_det : ∀ {F : Type} {α : Type u_1} {enumName : String} {R : Heap F → α → SourceValue F → Prop}
  {h : Heap F},
  (∀ {x₁ x₂ : α} {v : SourceValue F}, R h x₁ v → R h x₂ v → x₁ = x₂) →
    ∀ {xs₁ xs₂ : List α} {ptr : SourceValue F},
      Library.List.RepList enumName R h xs₁ ptr → Library.List.RepList enumName R h xs₂ ptr → xs₁ = xs₂
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.repList_det
/-- info: 'Aiur.Library.IxVMRep.repList_det' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.repList_det

/--
info: @Library.IxVMRep.repBinaryTree_det : ∀ {F : Type} {α : Type u_1} {enumName leafCtor branchCtor : String},
  leafCtor ≠ branchCtor →
    ∀ {R : Heap F → α → SourceValue F → Prop} {h : Heap F},
      (∀ {x₁ x₂ : α} {v : SourceValue F}, R h x₁ v → R h x₂ v → x₁ = x₂) →
        ∀ {t₁ t₂ : BinaryTree α} {ptr : SourceValue F},
          RepBinaryTree enumName leafCtor branchCtor R h t₁ ptr →
            RepBinaryTree enumName leafCtor branchCtor R h t₂ ptr → t₁ = t₂
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.repBinaryTree_det
/-- info: 'Aiur.Library.IxVMRep.repBinaryTree_det' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.repBinaryTree_det

/--
info: @Library.IxVMRep.repRBTreePtr_det : ∀ {F : Type} {K : Type u_1} {V : Type u_2} {enumName nilCtor nodeCtor : String},
  nilCtor ≠ nodeCtor →
    ∀ {RLabel : Heap F → ℕ × K × V → SourceValue F → Prop} {h : Heap F},
      (∀ {x₁ x₂ : ℕ × K × V} {v : SourceValue F}, RLabel h x₁ v → RLabel h x₂ v → x₁ = x₂) →
        ∀ {t₁ t₂ : Library.RBTreeMap.RBTree K V} {ptr : SourceValue F},
          Library.RBTreeMap.RepRBTreePtr enumName nilCtor nodeCtor RLabel h t₁ ptr →
            Library.RBTreeMap.RepRBTreePtr enumName nilCtor nodeCtor RLabel h t₂ ptr → t₁ = t₂
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.repRBTreePtr_det
/-- info: 'Aiur.Library.IxVMRep.repRBTreePtr_det' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.repRBTreePtr_det

/--
info: @Library.IxVMRep.RepIxVMUniv.mono : ∀ {F : Type} [inst : NatCast F] {h₁ h₂ : Heap F} {u : Library.IxVMRep.IxVMUniv}
  {v : SourceValue F}, h₁.Extends h₂ → Library.IxVMRep.RepIxVMUniv h₁ u v → Library.IxVMRep.RepIxVMUniv h₂ u v
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.RepIxVMUniv.mono
/-- info: 'Aiur.Library.IxVMRep.RepIxVMUniv.mono' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.RepIxVMUniv.mono

/--
info: @Library.IxVMRep.HeapMono.repIxVMUniv : ∀ {F : Type} [inst : NatCast F] (u : Library.IxVMRep.IxVMUniv),
  HeapMono fun h v => Library.IxVMRep.RepIxVMUniv h u v
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.HeapMono.repIxVMUniv
/-- info: 'Aiur.Library.IxVMRep.HeapMono.repIxVMUniv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.HeapMono.repIxVMUniv

/--
info: @Library.IxVMRep.RepIxVMUniv.det : ∀ {F : Type} [inst : Field F],
  Library.U32.Compatible F →
    ∀ {h : Heap F} {u₁ u₂ : Library.IxVMRep.IxVMUniv} {v : SourceValue F},
      Library.IxVMRep.RepIxVMUniv h u₁ v → Library.IxVMRep.RepIxVMUniv h u₂ v → u₁ = u₂
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.RepIxVMUniv.det
/-- info: 'Aiur.Library.IxVMRep.RepIxVMUniv.det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.RepIxVMUniv.det

/--
info: @Library.IxVMRep.RepIxVMIExpr.mono : ∀ {F : Type} [inst : NatCast F] {u64ListEnum : String} {h₁ h₂ : Heap F}
  {e : Library.IxVMRep.IxVMIExpr F} {ptr : SourceValue F},
  h₁.Extends h₂ → Library.IxVMRep.RepIxVMIExpr u64ListEnum h₁ e ptr → Library.IxVMRep.RepIxVMIExpr u64ListEnum h₂ e ptr
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.RepIxVMIExpr.mono
/-- info: 'Aiur.Library.IxVMRep.RepIxVMIExpr.mono' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.RepIxVMIExpr.mono

/--
info: @Library.IxVMRep.HeapMono.repIxVMIExpr : ∀ {F : Type} [inst : NatCast F] (u64ListEnum : String)
  (e : Library.IxVMRep.IxVMIExpr F), HeapMono fun h ptr => Library.IxVMRep.RepIxVMIExpr u64ListEnum h e ptr
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.HeapMono.repIxVMIExpr
/-- info: 'Aiur.Library.IxVMRep.HeapMono.repIxVMIExpr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.HeapMono.repIxVMIExpr

/--
info: @Library.IxVMRep.RepIxVMIExpr.det : ∀ {F : Type} [inst : Field F],
  Library.U32.Compatible F →
    ∀ {u64ListEnum : String} {h : Heap F} {e₁ e₂ : Library.IxVMRep.IxVMIExpr F} {ptr : SourceValue F},
      Library.IxVMRep.RepIxVMIExpr u64ListEnum h e₁ ptr → Library.IxVMRep.RepIxVMIExpr u64ListEnum h e₂ ptr → e₁ = e₂
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.RepIxVMIExpr.det
/-- info: 'Aiur.Library.IxVMRep.RepIxVMIExpr.det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.RepIxVMIExpr.det

/--
info: @Library.IxVMRep.RepIxVMKUniv.mono : ∀ {F : Type} {h₁ h₂ : Heap F} {u : Library.IxVMRep.IxVMKUniv F}
  {ptr : SourceValue F}, h₁.Extends h₂ → Library.IxVMRep.RepIxVMKUniv h₁ u ptr → Library.IxVMRep.RepIxVMKUniv h₂ u ptr
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.RepIxVMKUniv.mono
/-- info: 'Aiur.Library.IxVMRep.RepIxVMKUniv.mono' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.RepIxVMKUniv.mono

/-- info: @Library.IxVMRep.repIxVMKUniv_heapMono₂ : ∀ {F : Type}, HeapMono₂ Library.IxVMRep.RepIxVMKUniv -/
#guard_msgs in
#check @Aiur.Library.IxVMRep.repIxVMKUniv_heapMono₂
/-- info: 'Aiur.Library.IxVMRep.repIxVMKUniv_heapMono₂' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.repIxVMKUniv_heapMono₂

/--
info: @Library.IxVMRep.HeapMono.repIxVMKUniv : ∀ {F : Type} (u : Library.IxVMRep.IxVMKUniv F),
  HeapMono fun h ptr => Library.IxVMRep.RepIxVMKUniv h u ptr
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.HeapMono.repIxVMKUniv
/-- info: 'Aiur.Library.IxVMRep.HeapMono.repIxVMKUniv' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.HeapMono.repIxVMKUniv

/--
info: @Library.IxVMRep.RepIxVMKUniv.det : ∀ {F : Type} {h : Heap F} {u₁ u₂ : Library.IxVMRep.IxVMKUniv F}
  {ptr : SourceValue F}, Library.IxVMRep.RepIxVMKUniv h u₁ ptr → Library.IxVMRep.RepIxVMKUniv h u₂ ptr → u₁ = u₂
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.RepIxVMKUniv.det
/-- info: 'Aiur.Library.IxVMRep.RepIxVMKUniv.det' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.RepIxVMKUniv.det

/--
info: @Library.IxVMRep.RepIxVMKExpr.mono : ∀ {F : Type} [inst : NatCast F] {addrTy : Ty}
  {lvlListEnum limbListEnum byteListEnum : String} {h₁ h₂ : Heap F} {e : Library.IxVMRep.IxVMKExpr F}
  {ptr : SourceValue F},
  h₁.Extends h₂ →
    Library.IxVMRep.RepIxVMKExpr addrTy lvlListEnum limbListEnum byteListEnum h₁ e ptr →
      Library.IxVMRep.RepIxVMKExpr addrTy lvlListEnum limbListEnum byteListEnum h₂ e ptr
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.RepIxVMKExpr.mono
/-- info: 'Aiur.Library.IxVMRep.RepIxVMKExpr.mono' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.RepIxVMKExpr.mono

/--
info: @Library.IxVMRep.HeapMono.repIxVMKExpr : ∀ {F : Type} [inst : NatCast F] (addrTy : Ty)
  (lvlListEnum limbListEnum byteListEnum : String) (e : Library.IxVMRep.IxVMKExpr F),
  HeapMono fun h ptr => Library.IxVMRep.RepIxVMKExpr addrTy lvlListEnum limbListEnum byteListEnum h e ptr
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.HeapMono.repIxVMKExpr
/-- info: 'Aiur.Library.IxVMRep.HeapMono.repIxVMKExpr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.HeapMono.repIxVMKExpr

/--
info: @Library.IxVMRep.RepIxVMKExpr.det : ∀ {F : Type} [inst : Field F],
  Library.U32.Compatible F →
    ∀ {addrTy : Ty} {lvlListEnum limbListEnum byteListEnum : String} {h : Heap F} {e₁ e₂ : Library.IxVMRep.IxVMKExpr F}
      {ptr : SourceValue F},
      Library.IxVMRep.RepIxVMKExpr addrTy lvlListEnum limbListEnum byteListEnum h e₁ ptr →
        Library.IxVMRep.RepIxVMKExpr addrTy lvlListEnum limbListEnum byteListEnum h e₂ ptr → e₁ = e₂
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.RepIxVMKExpr.det
/-- info: 'Aiur.Library.IxVMRep.RepIxVMKExpr.det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.RepIxVMKExpr.det

/--
info: @Library.IxVMRep.RepRoleEvidence.mono : ∀ {F : Type} [inst : NatCast F] {addrTy : Ty} {h₁ h₂ : Heap F}
  {ev : Library.IxVMRep.IxVMRoleEvidence} {v : SourceValue F},
  h₁.Extends h₂ → Library.IxVMRep.RepRoleEvidence addrTy h₁ ev v → Library.IxVMRep.RepRoleEvidence addrTy h₂ ev v
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.RepRoleEvidence.mono
/-- info: 'Aiur.Library.IxVMRep.RepRoleEvidence.mono' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.RepRoleEvidence.mono

/--
info: @Library.IxVMRep.repRoleEvidence_heapMono₂ : ∀ {F : Type} [inst : NatCast F] (addrTy : Ty),
  HeapMono₂ (Library.IxVMRep.RepRoleEvidence addrTy)
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.repRoleEvidence_heapMono₂
/-- info: 'Aiur.Library.IxVMRep.repRoleEvidence_heapMono₂' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.repRoleEvidence_heapMono₂

/--
info: @Library.IxVMRep.RepRoleEvidence.det : ∀ {F : Type} [inst : Field F],
  Library.U32.Compatible F →
    ∀ {addrTy : Ty} {h : Heap F} {ev₁ ev₂ : Library.IxVMRep.IxVMRoleEvidence} {v : SourceValue F},
      Library.IxVMRep.RepRoleEvidence addrTy h ev₁ v → Library.IxVMRep.RepRoleEvidence addrTy h ev₂ v → ev₁ = ev₂
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.RepRoleEvidence.det
/-- info: 'Aiur.Library.IxVMRep.RepRoleEvidence.det' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.RepRoleEvidence.det

/--
info: @Library.IxVMRep.IxVMRoleTable.ext : ∀ {F : Type} {t₁ t₂ : Library.IxVMRep.IxVMRoleTable F},
  t₁.binding = t₂.binding → t₁.byRole = t₂.byRole → t₁.byAddr = t₂.byAddr → t₁ = t₂
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.IxVMRoleTable.ext
/-- info: 'Aiur.Library.IxVMRep.IxVMRoleTable.ext' does not depend on any axioms -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.IxVMRoleTable.ext

/--
info: @Library.IxVMRep.repRoleAddrLabel_heapMono₂ : ∀ {F : Type} [inst : NatCast F] (addrTy : Ty),
  HeapMono₂ (Library.IxVMRep.RepRoleAddrLabel addrTy)
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.repRoleAddrLabel_heapMono₂
/-- info: 'Aiur.Library.IxVMRep.repRoleAddrLabel_heapMono₂' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.repRoleAddrLabel_heapMono₂

/--
info: @Library.IxVMRep.repRoleAddrLabel_det : ∀ {F : Type} [inst : Field F],
  Library.U32.Compatible F →
    ∀ {addrTy : Ty} {h : Heap F} {l₁ l₂ : ℕ × F × Library.Bytes.Address} {v : SourceValue F},
      l₁.1 < 256 →
        l₂.1 < 256 →
          Library.IxVMRep.RepRoleAddrLabel addrTy h l₁ v → Library.IxVMRep.RepRoleAddrLabel addrTy h l₂ v → l₁ = l₂
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.repRoleAddrLabel_det
/-- info: 'Aiur.Library.IxVMRep.repRoleAddrLabel_det' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.repRoleAddrLabel_det

/--
info: @Library.IxVMRep.RepRoleCtx.mono : ∀ {F : Type} [inst : NatCast F] {addrTy : Ty} {byRoleEnum byAddrEnum : String}
  {RByRole : Heap F → ℕ × F × Library.Bytes.Address → SourceValue F → Prop}
  {RByAddr : Heap F → ℕ × Library.Bytes.Address × F → SourceValue F → Prop},
  HeapMono₂ RByRole →
    HeapMono₂ RByAddr →
      ∀ {h₁ h₂ : Heap F} {rc : Library.IxVMRep.IxVMRoleCtx F} {ptr : SourceValue F},
        h₁.Extends h₂ →
          Library.IxVMRep.RepRoleCtx addrTy byRoleEnum byAddrEnum RByRole RByAddr h₁ rc ptr →
            Library.IxVMRep.RepRoleCtx addrTy byRoleEnum byAddrEnum RByRole RByAddr h₂ rc ptr
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.RepRoleCtx.mono
/-- info: 'Aiur.Library.IxVMRep.RepRoleCtx.mono' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.RepRoleCtx.mono

/--
info: @Library.IxVMRep.HeapMono.repRoleCtx : ∀ {F : Type} [inst : NatCast F] (addrTy : Ty) (byRoleEnum byAddrEnum : String)
  {RByRole : Heap F → ℕ × F × Library.Bytes.Address → SourceValue F → Prop}
  {RByAddr : Heap F → ℕ × Library.Bytes.Address × F → SourceValue F → Prop},
  HeapMono₂ RByRole →
    HeapMono₂ RByAddr →
      ∀ (rc : Library.IxVMRep.IxVMRoleCtx F),
        HeapMono fun h ptr => Library.IxVMRep.RepRoleCtx addrTy byRoleEnum byAddrEnum RByRole RByAddr h rc ptr
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.HeapMono.repRoleCtx
/-- info: 'Aiur.Library.IxVMRep.HeapMono.repRoleCtx' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.HeapMono.repRoleCtx

/--
info: @Library.IxVMRep.RepRoleCtx.det : ∀ {F : Type} [inst : Field F],
  Library.U32.Compatible F →
    ∀ {addrTy : Ty} {byRoleEnum byAddrEnum : String}
      {RByRole : Heap F → ℕ × F × Library.Bytes.Address → SourceValue F → Prop}
      {RByAddr : Heap F → ℕ × Library.Bytes.Address × F → SourceValue F → Prop} {h : Heap F},
      (∀ {x₁ x₂ : ℕ × F × Library.Bytes.Address} {v : SourceValue F}, RByRole h x₁ v → RByRole h x₂ v → x₁ = x₂) →
        (∀ {x₁ x₂ : ℕ × Library.Bytes.Address × F} {v : SourceValue F}, RByAddr h x₁ v → RByAddr h x₂ v → x₁ = x₂) →
          ∀ {rc₁ rc₂ : Library.IxVMRep.IxVMRoleCtx F} {ptr : SourceValue F},
            Library.IxVMRep.RepRoleCtx addrTy byRoleEnum byAddrEnum RByRole RByAddr h rc₁ ptr →
              Library.IxVMRep.RepRoleCtx addrTy byRoleEnum byAddrEnum RByRole RByAddr h rc₂ ptr → rc₁ = rc₂
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.RepRoleCtx.det
/-- info: 'Aiur.Library.IxVMRep.RepRoleCtx.det' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.RepRoleCtx.det

/--
info: @Library.IxVMRep.ingress_verify_stream_sound : ∀ {F : Type} [inst : Field F],
  Library.U32.Compatible F →
    ∀ (enumName : String) (stream : ℕ → UInt8) (idx len : ℕ) (h : Heap F) (expectedAddr : Library.Bytes.Address),
      Library.List.Word.depthChecked (Library.Bytes.readByteStream stream idx len) = some len →
        Library.Blake3.addressToFields F (Library.Blake3.digest (Library.Bytes.readByteStream stream idx len)) =
            Library.Blake3.addressToFields F expectedAddr →
          have bytes := Library.Bytes.readByteStream stream idx len;
          have allocated := Library.Bytes.allocByteStream enumName h bytes;
          h.Extends allocated.2 ∧
            Library.Bytes.RepByteStream enumName allocated.2 bytes allocated.1 ∧
              bytes.length = len ∧ len < Library.U32.base ∧ Library.Blake3.digest bytes = expectedAddr
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.ingress_verify_stream_sound
/-- info: 'Aiur.Library.IxVMRep.ingress_verify_stream_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.ingress_verify_stream_sound

/-- info: @Library.IxVMRep.repTag4_heapMono₂ : ∀ {F : Type} [inst : NatCast F], HeapMono₂ Library.IxVMRep.RepTag4 -/
#guard_msgs in
#check @Aiur.Library.IxVMRep.repTag4_heapMono₂
/-- info: 'Aiur.Library.IxVMRep.repTag4_heapMono₂' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.repTag4_heapMono₂

/--
info: @Library.IxVMRep.repTag4_inj : ∀ {F : Type} [inst : Field F],
  Library.U32.Compatible F →
    ∀ {h : Heap F} {t₁ t₂ : UInt8 × UInt64} {v : SourceValue F},
      Library.IxVMRep.RepTag4 h t₁ v → Library.IxVMRep.RepTag4 h t₂ v → t₁ = t₂
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.repTag4_inj
/-- info: 'Aiur.Library.IxVMRep.repTag4_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.repTag4_inj

/--
info: @Library.IxVMRep.tag_header_split_unique : ∀ {f₁ l₁ f₂ l₂ : ℕ},
  l₁ < 32 → l₂ < 32 → f₁ * 32 + l₁ = f₂ * 32 + l₂ → f₁ = f₂ ∧ l₁ = l₂
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.tag_header_split_unique
/-- info: 'Aiur.Library.IxVMRep.tag_header_split_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.tag_header_split_unique

/--
info: @Library.IxVMRep.tagn4_header_split_unique : ∀ {l₁ c₁ f₁ l₂ c₂ f₂ : ℕ},
  l₁ < 8 → c₁ < 2 → l₂ < 8 → c₂ < 2 → l₁ + 8 * c₁ + 16 * f₁ = l₂ + 8 * c₂ + 16 * f₂ → l₁ = l₂ ∧ c₁ = c₂ ∧ f₁ = f₂
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.tagn4_header_split_unique
/-- info: 'Aiur.Library.IxVMRep.tagn4_header_split_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.tagn4_header_split_unique

/--
info: @Library.IxVMRep.tagn2_header_split_unique : ∀ {l₁ c₁ f₁ l₂ c₂ f₂ : ℕ},
  l₁ < 32 → c₁ < 2 → l₂ < 32 → c₂ < 2 → l₁ + 32 * c₁ + 64 * f₁ = l₂ + 32 * c₂ + 64 * f₂ → l₁ = l₂ ∧ c₁ = c₂ ∧ f₁ = f₂
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.tagn2_header_split_unique
/-- info: 'Aiur.Library.IxVMRep.tagn2_header_split_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.tagn2_header_split_unique

/--
info: Library.IxVMRep.u64ValLeBytes_lt : ∀ (bytes : List UInt8), Library.IxVMRep.u64ValLeBytes bytes < 18446744073709551616
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.u64ValLeBytes_lt
/-- info: 'Aiur.Library.IxVMRep.u64ValLeBytes_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.u64ValLeBytes_lt

/--
info: Library.IxVMRep.toNat_u64OfLeBytes : ∀ (bytes : List UInt8),
  (Library.IxVMRep.u64OfLeBytes bytes).toNat = Library.IxVMRep.u64ValLeBytes bytes
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.toNat_u64OfLeBytes
/-- info: 'Aiur.Library.IxVMRep.toNat_u64OfLeBytes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.toNat_u64OfLeBytes

/-- info: Library.IxVMRep.u64OfLeBytes_nil : (Library.IxVMRep.u64OfLeBytes []).toNat = 0 -/
#guard_msgs in
#check @Aiur.Library.IxVMRep.u64OfLeBytes_nil
/-- info: 'Aiur.Library.IxVMRep.u64OfLeBytes_nil' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.u64OfLeBytes_nil

/-- info: Library.IxVMRep.u64OfLeBytes_singleton : ∀ (b0 : UInt8), (Library.IxVMRep.u64OfLeBytes [b0]).toNat = b0.toNat -/
#guard_msgs in
#check @Aiur.Library.IxVMRep.u64OfLeBytes_singleton
/-- info: 'Aiur.Library.IxVMRep.u64OfLeBytes_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.u64OfLeBytes_singleton

/--
info: Library.IxVMRep.u64OfLeBytes_pair : ∀ (b0 b1 : UInt8),
  (Library.IxVMRep.u64OfLeBytes [b0, b1]).toNat = b0.toNat + 256 * b1.toNat
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.u64OfLeBytes_pair
/-- info: 'Aiur.Library.IxVMRep.u64OfLeBytes_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.u64OfLeBytes_pair

/--
info: Library.IxVMRep.tagn_tail_two_byte_spec : ∀ (lo v0 : UInt8) (q h carry : ℕ),
  q < h →
    h ≤ 64 →
      carry < 2 →
        lo.toNat + 2 * h = v0.toNat + 256 * carry →
          (Library.IxVMRep.u64OfLeBytes [v0, UInt8.ofNat (q + carry)]).toNat = lo.toNat + 2 * h + 256 * q
-/
#guard_msgs in
#check @Aiur.Library.IxVMRep.tagn_tail_two_byte_spec
/-- info: 'Aiur.Library.IxVMRep.tagn_tail_two_byte_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Aiur.Library.IxVMRep.tagn_tail_two_byte_spec

end Aiur.Audit
