import IxCC.Ring0
import IxCC.CompileClaim.Proof
import IxCC.X86.Proof.DriverSession
import IxCC.Rt.Proof.Mem

/-!
# `IxCC.Ring0.Proof`: Ring-0 Admission Soundness, Confinement & Frame Invariance

Proves:
1. **Decoded Stream & Instruction-Boundary Properties (`stream_check_cfi`)**:
   Every block instruction and terminator in an accepted `X86.Stream.check`
   output decodes at its canonical block/instruction offset (`instructionMatches`,
   `terminatorMatches`) with all direct `OpEn.D32` targets resolved to valid
   `blockOffset` boundaries, and any `ByteEval.step` executes at an instruction
   pointer `state.rip` inside `D.inText`.
2. **Conditional `ByteEval` / `ObjectEval` / `DriverSession` Frame Theorems**:
   Any step or call trace (`stream_run_framePreserved`, `byteEval_run_framePreserved`,
   `initCall_preserves_unmapped`, `rootCall_preserves_unmapped`,
   `session_runCalls_preserves_unmapped`, `text_preserved_of_canonicalOk`,
   `external_realizes_preserved`, `kernelTablesPreserved_of_session_runCalls`,
   `multi_sip_frame`, `pairwiseDisjointSips_frame`) that
   completes within the model's `D.mapped` permission map preserves every byte
   outside `D.mapped` bit-for-bit.
   - Note (`A3-2`, `A3-5`, `A3-6`): These frame theorems are conditional
     preservation lemmas over runs that succeed (`.ok`) in `X86.Memory` (where
     stores outside `D.mapped` fail `Memory.write?`). Static absence of model
     faults (`¬ GoesWrong`) for admitted SIPs is established by
     `verifyRing0Sip_sound` and `admittedRing0Sip_call_not_goesWrong`.
3. **Non-Vacuous Certified-Compilation Admission (`AdmittedRing0Sip` & `verifyRing0Sip_sound`)**:
   `AdmittedRing0Sip sip P` explicitly binds the parsed certificate `cert` and
   the rechecked artifact `a` (`Recheck.run` / `Recheck.runWithContracts` /
   `Recheck.RcReplay.run`), `Recheck.front`, `CompileClaim.rootParamsAllNat`,
   `root.ty = some (sig, ty)`, `sip.driver.CanonicalOk a.backend.encoded.text.size`,
   `Sem.Refines`, and `Ring0Safety` (`S2`, `A3-1`, `A6-1`).
4. **Admitted-SIP Absence of Faults (`S3`, `A3-2`, `A6-5`)**:
   `admittedRing0Sip_call_not_goesWrong` proves that for any `sip` passing
   `sip.verifyProgram P = true`, the objects `Ring0Sip.artifact?` determines from
   the certificate satisfy: on any source-safe input `i` (`¬ GoesWrong i`),
   `Lang.run linked i k` never faults (`¬ (Lang.run linked i k).GoesWrong`) at any
   clock `k`, with no `.ok` premise. The peer and kernel frame clauses still concern
   runs that return `.ok`, and nothing here covers state carried between calls.
-/

set_option autoImplicit false

namespace IxCC.Ring0

open IxCC.Sem (Result Obs Lang)
open IxCC.Lam.Erase.Proof (CheckedProgram)
open IxCC.X86 (Word GPR Width Memory Core Registers Op Mnemonic Arg Slot Implicit)

/-! ## 1. Stream Validation & Instruction-Pointer Bounds -/

/-- When `D.base.toNat + text.size ≤ 2 ^ 64`, any byte step
`X86.ByteEval.step text D.base state = .ok next` executes at an instruction
pointer `state.rip` inside `D.inText text.size`. -/
theorem step_rip_inText (D : X86.Driver) {text : ByteArray} {state next : X86.ByteEval.State}
    (hbase : D.base.toNat + text.size ≤ 2 ^ 64)
    (hstep : X86.ByteEval.step text D.base state = .ok next) :
    D.inText text.size state.rip = true := by
  have hlt : (state.rip - D.base).toNat < text.size :=
    X86.ObjectEval.step_inText hstep
  have hadd : D.base + (state.rip - D.base) = state.rip := by
    rw [UInt64.add_comm, UInt64.sub_add_cancel]
  have hnat : state.rip.toNat = D.base.toNat + (state.rip - D.base).toNat := by
    calc state.rip.toNat
      _ = (D.base + UInt64.ofNat (state.rip - D.base).toNat).toNat := by
        rw [UInt64.ofNat_toNat, hadd]
      _ = D.base.toNat + (state.rip - D.base).toNat :=
        Rt.Proof.addr_toNat (by omega)
  simp only [X86.Driver.inText, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- `X86.Stream.check` guarantees `X86.Stream.Valid`:
1. Every instruction in every block decodes at its canonical offset
   `blockOffset program blockIndex + instructionOffset block index` (`instructionMatches`),
2. Every block terminator decodes at the end of its block (`terminatorMatches`)
   with every direct control transfer (`OpEn.D32` `jmp`/`jcc`/`call`) targeting
   a valid block offset in `program.blocks` and every fall-through landing on
   the adjacent block boundary (`stream_targets_valid_block`, `stream_falls_valid_block`),
3. Any `ByteEval.step` executes at `state.rip` inside `D.inText output.text.size`.
Note (`A3-4`): `ret` is an indirect control transfer that pops its return address
from `[rsp]`; return-slot integrity is guaranteed by the backend frame simulation
(`Recheck.sound` / `RcReplay.sound`). -/
theorem stream_check_cfi (D : X86.Driver) {program : X86.Program}
    {output : X86.Encode.Output} {externals : X86.Stream.ExternalTargets}
    (hcheck : X86.Stream.check program output externals = true)
    (hbase : D.base.toNat + output.text.size ≤ 2 ^ 64) :
    X86.Stream.Valid program output externals ∧
    output.text.size = X86.Stream.textSize program ∧
    output.blockOffsets = X86.Stream.blockOffsets program ∧
    (∀ blockIndex block, program.blocks[blockIndex]? = some block →
      ∀ index instruction, block.instructions[index]? = some instruction →
        X86.Stream.instructionMatches program output.text externals
          (X86.Stream.blockOffset program blockIndex +
            X86.Stream.instructionOffset block index) instruction = true) ∧
    (∀ blockIndex block, program.blocks[blockIndex]? = some block →
      X86.Stream.terminatorMatches program output.text
        (X86.Stream.blockOffset program blockIndex +
          X86.Stream.instructionOffset block block.instructions.size)
        block.terminator = true) ∧
    ∀ state next, X86.ByteEval.step output.text D.base state = .ok next →
      D.inText output.text.size state.rip = true := by
  have hvalid := X86.Stream.check_sound hcheck
  refine ⟨hvalid, hvalid.textLength, hvalid.offsets,
    hvalid.instruction, hvalid.terminator, ?_⟩
  intro state next hstep
  exact step_rip_inText D hbase hstep

/-! ## 2. Conditional `ByteEval` / `ObjectEval` / `DriverSession` Frame Lemmas -/

attribute [local simp] pure Except.pure Functor.map Except.map bind Except.bind

/-- Any checked memory store `m.write? w a v = .ok after` preserves permissions
and leaves every non-writable byte (`m.writable addr = false`) untouched. -/
theorem write?_framePreserved {m after : Memory} {w : Width} {a v : Word}
    (h : m.write? w a v = .ok after) : FramePreserved m after := by
  unfold Memory.write? at h
  split at h
  · rename_i hallowed
    cases h
    refine ⟨Rt.Proof.writeLittle_readable m a v w.bytes,
            Rt.Proof.writeLittle_writable m a v w.bytes, ?_⟩
    intro addr hw
    apply Memory.writeLittle_bytes_outside
    intro offset hlt heq
    have hperm := (Rt.Proof.rangeAllowed_iff m.writable a w.bytes).mp hallowed offset hlt
    rw [← heq, hw] at hperm
    cases hperm
  · cases h

/-- Storing an instruction operand preserves the frame of all non-writable bytes. -/
theorem store_framePreserved {before core after : Core} {w : Width} {v : Word} {arg : Arg}
    (h : arg.store before w v core = .ok after) : FramePreserved core.memory after.memory := by
  cases arg with
  | reg _ =>
    cases h
    cases w <;> exact FramePreserved.refl _
  | imm _ =>
    cases h
    exact FramePreserved.refl _
  | mem addr =>
    simp only [Arg.store, bind, Except.bind, pure, Except.pure] at h
    cases hw : core.memory.write? w (addr.eval before) v with
    | error _ => rw [hw] at h; cases h
    | ok mem' =>
      rw [hw] at h
      cases h
      exact write?_framePreserved hw

/-- Writing output operand slots preserves the frame of all non-writable bytes. -/
theorem writeSlots_framePreserved (before : Core) (slots : List Slot)
    (args : List Arg) (results : List Word) :
    ∀ {core after : Core}, X86.writeSlots before core slots args results = .ok after →
      FramePreserved core.memory after.memory := by
  induction slots generalizing args results with
  | nil =>
    intro core after h
    cases args <;> (cases h; exact FramePreserved.refl _)
  | cons slot slots ih =>
    intro core after h
    cases args with
    | nil => cases h; exact FramePreserved.refl _
    | cons arg args =>
      unfold X86.writeSlots at h
      cases hrole : slot.role <;> rw [hrole] at h
      case read | address => exact ih args results h
      all_goals
        cases hstore : arg.store before slot.width (results.headD 0) core with
        | error _ => rw [hstore] at h; cases h
        | ok middle =>
          rw [hstore] at h
          exact (store_framePreserved hstore).trans (ih args results.tail h)

/-- Implicit register writes do not modify memory. -/
theorem writeImplicits_framePreserved (core : Core) (implicits : List Implicit) (results : List Word) :
    FramePreserved core.memory (X86.writeImplicits core implicits results).memory := by
  induction implicits generalizing core results with
  | nil =>
    cases results <;> exact FramePreserved.refl _
  | cons implicit implicits ih =>
    simp only [X86.writeImplicits]
    split
    · have hfirst : FramePreserved core.memory (core.writeReg implicit.width implicit.reg (results.headD 0)).memory := by
        cases implicit.width <;> exact FramePreserved.refl _
      exact hfirst.trans (ih _ _)
    · exact ih _ _

/-- Stack staging (`push`, `pop`, `none`) preserves the frame of all non-writable bytes. -/
theorem stage_framePreserved {o : Op} {core after : Core} {out : X86.SemOut}
    (h : o.stage core out = .ok after) : FramePreserved core.memory after.memory := by
  unfold Op.stage at h
  cases hstack : (X86.desc o).stack <;> rw [hstack] at h
  · cases h; exact FramePreserved.refl _
  · cases hw : core.memory.write64? (core.readReg .rsp - 8) (out.results.headD 0) with
    | error _ => rw [hw] at h; cases h
    | ok mem' =>
      rw [hw] at h
      cases h
      exact write?_framePreserved hw
  · cases h; exact FramePreserved.refl _

/-- Running any instruction-table row `Op.run` preserves the frame of all non-writable bytes. -/
theorem op_run_framePreserved {o : Op} {args : List Arg} {core after : Core}
    {observed : X86.ByteEval.Flags} {out : X86.SemOut}
    (h : o.run args core observed = .ok (after, out)) :
    FramePreserved core.memory after.memory := by
  unfold Op.run at h
  cases hinputs : o.inputs args core with
  | error _ => simp [hinputs, Except.mapError] at h
  | ok inputs =>
    cases hsem : (X86.desc o).sem ⟨inputs, observed⟩ with
    | error _ => simp [hinputs, hsem, Except.mapError] at h
    | ok result =>
      cases hstage : o.stage core result with
      | error _ => simp [hinputs, hsem, hstage, Except.mapError] at h
      | ok staged =>
        cases hwrite : X86.writeSlots core staged (X86.desc o).slots args result.results with
        | error _ => simp [hinputs, hsem, hstage, hwrite, Except.mapError] at h
        | ok final =>
          simp [hinputs, hsem, hstage, hwrite, Except.mapError] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ((stage_framePreserved hstage).trans
            (writeSlots_framePreserved core _ args _ hwrite)).trans
            (writeImplicits_framePreserved _ _ _)

/-- Executing any instruction-table row `Op.exec` preserves the frame of all non-writable bytes. -/
theorem op_exec_framePreserved {o : Op} {args : List Arg} {core after : Core}
    {flags flagsAfter : X86.ByteEval.Flags}
    (h : o.exec args core flags = .ok (after, flagsAfter)) :
    FramePreserved core.memory after.memory := by
  obtain ⟨out, hran⟩ := X86.Stream.exec_ok h
  exact op_run_framePreserved hran

/-- Every linear typed instruction step preserves the frame of all non-writable bytes. -/
theorem linear_framePreserved (runtime : X86.Runtime) (checked : X86.Checked)
    (machine : X86.Machine) (instruction : X86.Instr)
    (linear : X86.Encode.linearInstruction instruction = true) :
    FramePreserved machine.core.memory
      (X86.executeInstr runtime checked instruction machine).core.memory := by
  cases instruction with
  | op o args =>
    show FramePreserved machine.core.memory (machine.afterRow (o.exec args machine.core {})).core.memory
    cases hexec : o.exec args machine.core {} with
    | error fault =>
      cases fault <;> exact FramePreserved.refl _
    | ok result =>
      obtain ⟨after, flagsAfter⟩ := result
      have hfp := op_exec_framePreserved hexec
      show FramePreserved machine.core.memory (machine.advanceWith after).core.memory
      unfold X86.Machine.advanceWith
      split
      · exact FramePreserved.refl _
      · exact hfp
  | fused | call | callRuntime | unwind => simp [X86.Encode.linearInstruction] at linear

/-- Every typed block terminator preserves the frame of all non-writable bytes. -/
theorem terminator_framePreserved (checked : X86.Checked) (machine : X86.Machine)
    (terminator : X86.Terminator) :
    FramePreserved machine.core.memory (X86.executeTerminator checked terminator machine).core.memory := by
  cases terminator with
  | branch producer args condition yes no _ =>
    simp only [X86.executeTerminator]
    cases hexec : producer.exec args machine.core {} with
    | error fault => cases fault <;> exact FramePreserved.refl _
    | ok result =>
      obtain ⟨after, flags⟩ := result
      have hfp := op_exec_framePreserved hexec
      simp only
      cases flags.test condition with
      | none => exact FramePreserved.refl _
      | some take =>
        simp only [X86.Machine.goto]
        split <;> split <;> exact hfp
  | jump _ | tailCall _ | ret =>
    simp only [X86.executeTerminator, X86.Machine.goto]
    all_goals (repeat' split) <;> exact FramePreserved.refl _

/-- One step of the typed x86-64 stream machine (`CallFree`) preserves the frame
of all non-writable bytes. -/
theorem stream_step_framePreserved (runtime : X86.Runtime) (checked : X86.Checked)
    (free : X86.Stream.CallFree checked.program) (machine : X86.Machine) :
    FramePreserved machine.core.memory
      (X86.step runtime checked machine).core.memory := by
  cases running : machine.status with
  | halted _ | trapped _ => simp [X86.step, running]
  | running =>
    cases found : checked.program.blocks[machine.pc.block.toNat]? with
    | none => simp [X86.step, running, found, X86.Machine.trap]
    | some block =>
      cases foundInstruction : block.instructions[machine.pc.offset.toNat]? with
      | some instruction =>
        simpa [X86.step, running, found, foundInstruction] using
          linear_framePreserved runtime checked machine instruction (free _ _ found _ _ foundInstruction)
      | none =>
        simp only [X86.step, running, found, foundInstruction]
        split
        · exact terminator_framePreserved checked machine block.terminator
        · simp [X86.Machine.trap]

/-- Any multi-step run of the typed x86-64 stream machine (`CallFree`) preserves
the frame of all non-writable bytes. -/
theorem stream_run_framePreserved (runtime : X86.Runtime) (checked : X86.Checked)
    (free : X86.Stream.CallFree checked.program) (fuel : Nat) (machine : X86.Machine) :
    FramePreserved machine.core.memory
      (X86.run runtime checked fuel machine).core.memory := by
  induction fuel generalizing machine with
  | zero => exact FramePreserved.refl _
  | succ fuel ih =>
    rw [X86.run_succ]
    have first := stream_step_framePreserved runtime checked free machine
    have rest := ih (X86.step runtime checked machine)
    exact first.trans rest

/-- Executing one decoded byte-level x86-64 instruction (`ByteEval.execute`)
preserves permissions and every non-writable byte. -/
theorem byteEval_execute_framePreserved {decoded : X86.Decode.Decoded}
    {state next : X86.ByteEval.State}
    (h : X86.ByteEval.execute decoded state = .ok next) :
    FramePreserved state.core.memory next.core.memory := by
  rcases decoded with ⟨⟨o, opArgs⟩, length⟩
  unfold X86.ByteEval.execute at h
  simp only at h
  split at h
  · -- .call
    simp only [Except.mapError] at h
    cases hw : state.core.memory.write64? (state.core.readReg .rsp - 8)
        (state.rip + UInt64.ofNat length) with
    | error _ => rw [hw] at h; cases h
    | ok mem' =>
      rw [hw] at h
      cases h
      exact write?_framePreserved hw
  · -- .jmp
    cases h
    exact FramePreserved.refl _
  · -- .jcc
    simp only [Except.mapError] at h
    split at h
    · cases h
    · cases h; exact FramePreserved.refl _
  · -- .ret
    simp only [Except.mapError] at h
    split at h
    · cases h
    · cases h; exact FramePreserved.refl _
  · -- linear / other op
    simp only [Except.mapError] at h
    split at h
    · cases h
    · rename_i pair hexec
      cases h
      exact op_exec_framePreserved hexec

/-- One byte-machine step (`ByteEval.step`) preserves the frame of all non-writable bytes. -/
theorem byteEval_step_framePreserved {text : ByteArray} {base : Word}
    {state next : X86.ByteEval.State}
    (h : X86.ByteEval.step text base state = .ok next) :
    FramePreserved state.core.memory next.core.memory := by
  unfold X86.ByteEval.step at h
  cases hd : X86.Decode.decodeAt text (state.rip - base).toNat with
  | none => rw [hd] at h; cases h
  | some decoded =>
    rw [hd] at h
    exact byteEval_execute_framePreserved h

/-- Any `fuel`-step byte-machine execution (`ByteEval.run`) preserves the frame
of all non-writable bytes. -/
theorem byteEval_run_framePreserved {text : ByteArray} {base : Word}
    {fuel : Nat} {state final : X86.ByteEval.State}
    (h : X86.ByteEval.run text base fuel state = .ok final) :
    FramePreserved state.core.memory final.core.memory := by
  induction fuel generalizing state with
  | zero =>
    cases h
    exact FramePreserved.refl _
  | succ fuel ih =>
    unfold X86.ByteEval.run at h
    cases hs : X86.ByteEval.step text base state with
    | error _ => rw [hs] at h; cases h
    | ok next =>
      rw [hs] at h
      exact (byteEval_step_framePreserved hs).trans (ih h)

/-- Running the byte machine up to a return address (`ObjectEval.runTo`)
preserves the frame of all non-writable bytes. -/
theorem runTo_framePreserved {text : ByteArray} {base stop : Word}
    {fuel : Nat} {state final : X86.ByteEval.State}
    (h : X86.ObjectEval.runTo text base stop fuel state = .ok final) :
    FramePreserved state.core.memory final.core.memory := by
  induction fuel generalizing state with
  | zero =>
    cases h
    exact FramePreserved.refl _
  | succ fuel ih =>
    unfold X86.ObjectEval.runTo at h
    split at h
    · cases h; exact FramePreserved.refl _
    · cases hs : X86.ByteEval.step text base state with
      | error _ => rw [hs] at h; cases h
      | ok next =>
        rw [hs] at h
        exact (byteEval_step_framePreserved hs).trans (ih h)

/-- When `ObjectEval.finish` succeeds with `.ok (val, mem')`, `mem'` is the
exact final byte-machine memory `state.core.memory`. -/
theorem finish_mem_eq {core₀ : Core} {retAddr : Word} {state : X86.ByteEval.State}
    {val : Word} {mem' : Memory}
    (h : X86.ObjectEval.finish core₀ retAddr state = .ok (val, mem')) :
    mem' = state.core.memory := by
  unfold X86.ObjectEval.finish X86.ObjectEval.statusResult at h
  split at h
  · split at h
    · split at h
      · simp only [Result.ok.injEq, Prod.mk.injEq] at h
        exact h.2.symm
      · repeat' (split at h <;> try cases h)
    · cases h
  · cases h

/-- Conditional frame lemma: any exported symbol call (`ObjectEval.call`) that
returns `.ok (val, mem')` preserves permissions and leaves every non-writable
byte of `core₀.memory` untouched. -/
theorem objectEval_call_framePreserved {bytes : ByteArray} {name : String}
    {base : Word} {core₀ : Core} {flags : X86.ByteEval.Flags} {k : Nat}
    {val : Word} {mem' : Memory}
    (h : X86.ObjectEval.call bytes name base core₀ flags k = .ok (val, mem')) :
    FramePreserved core₀.memory mem' := by
  unfold X86.ObjectEval.call at h
  cases h1 : X86.ELFRead.text? bytes with
  | none => rw [h1] at h; cases h
  | some text =>
    rw [h1] at h
    cases h2 : X86.ELF.symbol? bytes name with
    | none => rw [h2] at h; cases h
    | some offset =>
      rw [h2] at h
      cases h3 : core₀.memory.read64? (core₀.readReg .rsp) with
      | error _ => rw [h3] at h; cases h
      | ok retAddr =>
        rw [h3] at h
        simp only at h
        cases hrun : X86.ObjectEval.runTo text base retAddr k
            ⟨core₀, base + UInt64.ofNat offset, flags⟩ with
        | error _ => rw [hrun] at h; cases h
        | ok state =>
          rw [hrun] at h
          have hmem := finish_mem_eq h
          subst hmem
          exact runTo_framePreserved hrun

/-- Conditional frame lemma: any entry-point execution (`ObjectEval.exec`) that
returns `.ok (val, mem')` preserves permissions and leaves every non-writable
byte of `core₀.memory` untouched. -/
theorem objectEval_exec_framePreserved {bytes : ByteArray} {name : String}
    {base : Word} {core₀ : Core} {flags : X86.ByteEval.Flags} {k : Nat}
    {val : Word} {mem' : Memory}
    (h : X86.ObjectEval.exec bytes name base core₀ flags k = .ok (val, mem')) :
    FramePreserved core₀.memory mem' := by
  unfold X86.ObjectEval.exec at h
  cases h1 : X86.ELFRead.text? bytes with
  | none => rw [h1] at h; cases h
  | some text =>
    rw [h1] at h
    cases h2 : X86.ELF.entry? bytes name with
    | none => rw [h2] at h; cases h
    | some offset =>
      rw [h2] at h
      cases h3 : core₀.memory.read64? (core₀.readReg .rsp) with
      | error _ => rw [h3] at h; cases h
      | ok retAddr =>
        rw [h3] at h
        simp only at h
        cases hrun : X86.ObjectEval.runTo text base retAddr k
            ⟨core₀, base + UInt64.ofNat offset, flags⟩ with
        | error _ => rw [hrun] at h; cases h
        | ok state =>
          rw [hrun] at h
          have hmem := finish_mem_eq h
          subst hmem
          exact runTo_framePreserved hrun

/-- Under `D.Ok textSize`, every byte outside `D.mapped` is outside the caller
return slot `[D.sp, D.sp + 8)` and is therefore unchanged by `D.mem`. -/
theorem driver_mem_unmapped_bytes {D : X86.Driver} {textSize : Nat}
    (hD : D.Ok textSize) (bytes : Word → UInt8) {addr : Word}
    (hunmapped : D.mapped addr = false) :
    (D.mem bytes).bytes addr = bytes addr := by
  apply D.mem_bytes hD bytes
  have hlow := hD.spLow
  simp only [X86.Driver.mapped, X86.Driver.inRegion, X86.Driver.inStack,
    Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hunmapped
  omega

/-- Under `D.Ok textSize`, every byte outside `D.mapped` is outside the budget
slot `[D.ctx - 48, D.ctx - 40)` and is therefore unchanged by `D.initBytes`. -/
theorem driver_initBytes_unmapped {D : X86.Driver} {textSize : Nat}
    (hD : D.Ok textSize) {addr : Word}
    (hunmapped : D.mapped addr = false) :
    D.initBytes addr = D.init addr := by
  unfold X86.Driver.initBytes
  have hctx := hD.ctx48_toNat
  have hmin := hD.minSize
  have hbelow := hD.below
  simp only [Memory.write]
  apply Rt.Proof.writeLittle_bytes_out (by simp [Width.bytes]) (by simp [Width.bytes]; omega)
  simp only [X86.Driver.mapped, X86.Driver.inRegion, X86.Driver.inStack,
    Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hunmapped
  simp only [Width.bytes]
  omega

/-- Conditional frame lemma: `Linked.initCall` preserves every byte outside `L.driver.mapped`. -/
theorem initCall_preserves_unmapped {L : X86.Linked} {textSize : Nat}
    (hD : L.driver.Ok textSize) {k : Nat} {w : Word} {mem' : Memory}
    (hcall : L.initCall k = .ok (w, mem')) :
    mem'.readable = L.driver.mapped ∧
    mem'.writable = L.driver.mapped ∧
    ∀ addr, L.driver.mapped addr = false → mem'.bytes addr = L.driver.init addr := by
  have hfp := objectEval_call_framePreserved hcall
  have hr : (L.driver.core [L.driver.size, L.driver.budget] L.driver.initBytes).memory.readable = L.driver.mapped :=
    X86.Driver.mem_readable L.driver.initBytes
  have hw : (L.driver.core [L.driver.size, L.driver.budget] L.driver.initBytes).memory.writable = L.driver.mapped :=
    X86.Driver.mem_writable L.driver.initBytes
  refine ⟨hfp.readable.trans hr, hfp.writable.trans hw, ?_⟩
  intro addr hunmapped
  have hw_false : (L.driver.core [L.driver.size, L.driver.budget] L.driver.initBytes).memory.writable addr = false := by
    rw [hw]; exact hunmapped
  rw [hfp.unwritable addr hw_false]
  show (L.driver.mem L.driver.initBytes).bytes addr = L.driver.init addr
  rw [driver_mem_unmapped_bytes hD L.driver.initBytes hunmapped]
  exact driver_initBytes_unmapped hD hunmapped

/-- Conditional frame lemma: `Linked.rootCall` preserves every byte outside `L.driver.mapped`. -/
theorem rootCall_preserves_unmapped {L : X86.Linked} {textSize : Nat}
    (hD : L.driver.Ok textSize) {r : X86.Linked.Root} {ns : List Nat}
    {bytes : Word → UInt8} {k : Nat} {w : Word} {mem' : Memory}
    (hcall : L.rootCall r ns bytes k = .ok (w, mem')) :
    mem'.readable = L.driver.mapped ∧
    mem'.writable = L.driver.mapped ∧
    ∀ addr, L.driver.mapped addr = false → mem'.bytes addr = bytes addr := by
  have hfp := objectEval_call_framePreserved hcall
  have hr : (L.driver.core (ns.map UInt64.ofNat) bytes).memory.readable = L.driver.mapped :=
    X86.Driver.mem_readable bytes
  have hw : (L.driver.core (ns.map UInt64.ofNat) bytes).memory.writable = L.driver.mapped :=
    X86.Driver.mem_writable bytes
  refine ⟨hfp.readable.trans hr, hfp.writable.trans hw, ?_⟩
  intro addr hunmapped
  have hw_false : (L.driver.core (ns.map UInt64.ofNat) bytes).memory.writable addr = false := by
    rw [hw]; exact hunmapped
  rw [hfp.unwritable addr hw_false]
  exact driver_mem_unmapped_bytes hD bytes hunmapped

/-- Conditional frame lemma: `DriverSession.Session.dropCall` preserves every byte outside `s.linked.driver.mapped`. -/
theorem dropCall_preserves_unmapped {s : X86.DriverSession.Session} {textSize : Nat}
    (hD : s.linked.driver.Ok textSize) {word : Word} {bytes : Word → UInt8}
    {k : Nat} {rw : Word} {mem' : Memory}
    (hdrop : s.dropCall word bytes k = .ok (rw, mem')) :
    mem'.readable = s.linked.driver.mapped ∧
    mem'.writable = s.linked.driver.mapped ∧
    ∀ addr, s.linked.driver.mapped addr = false → mem'.bytes addr = bytes addr := by
  have hfp := objectEval_call_framePreserved hdrop
  have hr : (s.linked.driver.core [word] bytes).memory.readable = s.linked.driver.mapped :=
    X86.Driver.mem_readable bytes
  have hw : (s.linked.driver.core [word] bytes).memory.writable = s.linked.driver.mapped :=
    X86.Driver.mem_writable bytes
  refine ⟨hfp.readable.trans hr, hfp.writable.trans hw, ?_⟩
  intro addr hunmapped
  have hw_false : (s.linked.driver.core [word] bytes).memory.writable addr = false := by
    rw [hw]; exact hunmapped
  rw [hfp.unwritable addr hw_false]
  exact driver_mem_unmapped_bytes hD bytes hunmapped

/-- Conditional frame lemma: a single `DriverSession.Session.one` step
preserves every byte outside `s.linked.driver.mapped` in both `event.live` and `event.released`. -/
theorem session_one_preserves_unmapped {s : X86.DriverSession.Session} {textSize : Nat}
    (hD : s.linked.driver.Ok textSize) {input : X86.DriverSession.Input}
    {bytes : Word → UInt8} {k : Nat} {event : X86.DriverSession.Event}
    (hone : s.one input bytes k = .ok event) :
    (∀ addr, s.linked.driver.mapped addr = false → event.live.bytes addr = bytes addr) ∧
    (∀ addr, s.linked.driver.mapped addr = false → event.released.bytes addr = bytes addr) := by
  obtain ⟨root, _, _, _, _, hcall, _, hdrop, _⟩ := X86.DriverSession.Session.one_ok_parts hone
  have hlive := (rootCall_preserves_unmapped hD hcall).2.2
  have hrel := (dropCall_preserves_unmapped hD hdrop).2.2
  refine ⟨hlive, fun addr hunmapped => ?_⟩
  rw [hrel addr hunmapped, hlive addr hunmapped]

/-- `DriverSession.ValidTrace` instantiation for external memory frame preservation
across `Session.runCalls`. -/
theorem session_runCalls_validTrace_frame {s : X86.DriverSession.Session} {textSize : Nat}
    (hD : s.linked.driver.Ok textSize) {inputs : List X86.DriverSession.Input}
    {bytes : Word → UInt8} {k : Nat} {output : X86.DriverSession.Output}
    (hrun : s.runCalls inputs bytes k = .ok output) :
    X86.DriverSession.ValidTrace
      (fun _ m => ∀ addr, s.linked.driver.mapped addr = false → m.bytes addr = bytes addr)
      output.events ∧
    (∀ addr, s.linked.driver.mapped addr = false → output.bytes addr = bytes addr) := by
  exact X86.DriverSession.Session.runCalls_validTrace
    (ownedToken := fun _ m => ∀ addr, s.linked.driver.mapped addr = false → m.bytes addr = bytes addr)
    (Inv := fun b => ∀ addr, s.linked.driver.mapped addr = false → b addr = bytes addr)
    (fun _ _ => rfl)
    (fun _ _ b event hb hone => by
      obtain ⟨hlive, hrel⟩ := session_one_preserves_unmapped hD hone
      refine ⟨fun addr hunmapped => (hlive addr hunmapped).trans (hb addr hunmapped),
              fun addr hunmapped => (hrel addr hunmapped).trans (hb addr hunmapped)⟩)
    hrun

/-- Conditional `DriverSession` frame theorem (`A3-2`): any `Session.runCalls`
execution that returns `.ok output` preserves every byte outside `s.linked.driver.mapped`
across the call sequence and at every intermediate event. -/
theorem session_runCalls_preserves_unmapped {s : X86.DriverSession.Session} {textSize : Nat}
    (hD : s.linked.driver.Ok textSize) {inputs : List X86.DriverSession.Input}
    {bytes : Word → UInt8} {k : Nat} {output : X86.DriverSession.Output}
    (hrun : s.runCalls inputs bytes k = .ok output) :
    (∀ addr, s.linked.driver.mapped addr = false → output.bytes addr = bytes addr) ∧
    (∀ event ∈ output.events, ∀ addr, s.linked.driver.mapped addr = false →
      event.live.bytes addr = bytes addr ∧ event.released.bytes addr = bytes addr) := by
  induction inputs generalizing bytes output with
  | nil =>
    simp only [X86.DriverSession.Session.runCalls, Result.ok.injEq] at hrun
    subst hrun
    refine ⟨fun _ _ => rfl, ?_⟩
    intro event hev
    cases hev
  | cons input rest ih =>
    obtain ⟨event, tail, hone, hrest, rfl⟩ := X86.DriverSession.Session.runCalls_ok_cons hrun
    obtain ⟨hlive, hrel⟩ := session_one_preserves_unmapped hD hone
    obtain ⟨htailBytes, htailEv⟩ := ih hrest
    refine ⟨fun addr hunmapped => (htailBytes addr hunmapped).trans (hrel addr hunmapped), ?_⟩
    intro ev hev addr hunmapped
    rcases List.mem_cons.mp hev with rfl | hmem
    · exact ⟨hlive addr hunmapped, hrel addr hunmapped⟩
    · obtain ⟨hl, hr⟩ := htailEv ev hmem addr hunmapped
      exact ⟨hl.trans (hrel addr hunmapped), hr.trans (hrel addr hunmapped)⟩

/-- Conditional `DriverSession` frame theorem: full session `Session.run`
(`cx_init` followed by `runCalls`) preserves every byte outside
`s.linked.driver.mapped` relative to `s.linked.driver.init`. -/
theorem session_run_preserves_unmapped {s : X86.DriverSession.Session} {textSize : Nat}
    (hD : s.linked.driver.Ok textSize) {inputs : List X86.DriverSession.Input}
    {k : Nat} {output : X86.DriverSession.Output}
    (hrun : s.run inputs k = .ok output) :
    (∀ addr, s.linked.driver.mapped addr = false → output.bytes addr = s.linked.driver.init addr) ∧
    (∀ event ∈ output.events, ∀ addr, s.linked.driver.mapped addr = false →
      event.live.bytes addr = s.linked.driver.init addr ∧
      event.released.bytes addr = s.linked.driver.init addr) := by
  unfold X86.DriverSession.Session.run at hrun
  cases hinit : s.linked.initCall k with
  | ok initialized =>
    simp only [hinit, Result.bind] at hrun
    have hinitBytes := (initCall_preserves_unmapped hD hinit).2.2
    obtain ⟨hout, hev⟩ := session_runCalls_preserves_unmapped hD hrun
    refine ⟨fun addr hunmapped => (hout addr hunmapped).trans (hinitBytes addr hunmapped),
            fun event hevent addr hunmapped => ?_⟩
    obtain ⟨hl, hr⟩ := hev event hevent addr hunmapped
    exact ⟨hl.trans (hinitBytes addr hunmapped), hr.trans (hinitBytes addr hunmapped)⟩
  | timeout | trap | resource _ | stuck =>
    simp [hinit, Result.bind] at hrun

/-- Under `D.CanonicalOk textSize`, `.text` addresses `[D.base, D.base + textSize)`
are disjoint from `D.mapped` (`textApart`), so no data store in `Session.runCalls`
modifies `bytes addr` for `inText textSize addr = true`.
Note (`A3-6`): In `ByteEval`, instruction fetch reads the immutable `text : ByteArray`
while data stores update `Memory.bytes`; hardware W^X (see the assumptions in `IxCC.Ring0`)
identifies the two in unified physical memory. -/
theorem text_preserved_of_canonicalOk {s : X86.DriverSession.Session} {textSize : Nat}
    (hD : s.linked.driver.CanonicalOk textSize) {inputs : List X86.DriverSession.Input}
    {bytes : Word → UInt8} {k : Nat} {output : X86.DriverSession.Output}
    (hrun : s.runCalls inputs bytes k = .ok output)
    {addr : Word} (htext : s.linked.driver.inText textSize addr = true) :
    output.bytes addr = bytes addr :=
  (session_runCalls_preserves_unmapped hD.toOk hrun).1 addr
    (X86.Driver.CanonicalOk.text_disjoint_mapped s.linked.driver hD addr htext)

/-- When a `WordRegion.Layout` is disjoint from `D.mapped` (`ExternalDisjoint D layout`),
any byte update confined to `D.mapped` preserves every 64-bit word
`read64 (layout.address slot)` for `slot < layout.slots`. -/
theorem external_read64_preserved {D : X86.Driver} {layout : X86.WordRegion.Layout}
    (hdisj : ExternalDisjoint D layout) {m m' : Memory}
    (hframe : ∀ addr, D.mapped addr = false → m'.bytes addr = m.bytes addr)
    {slot : Nat} (hslot : slot < layout.slots) :
    m'.read64 (layout.address slot) = m.read64 (layout.address slot) := by
  apply Memory.readLittle_congr
  intro offset hoffset
  apply hframe
  apply hdisj
  exact layout.byteAllowed hslot hoffset

/-- **External `WordRegion.Realizes` Frame Theorem**:
1. If `WordRegion.Realizes layout outside words m` holds for an external word
   region (`ExternalDisjoint D layout`), then by `WordRegion.Realizes.frame`
   every byte inside `D.mapped` agrees between `m` and `outside`.
2. Any execution of `D` producing `m'` that preserves permissions and unmapped
   bytes preserves `WordRegion.Realizes` with the exact same `words`. -/
theorem external_realizes_preserved {D : X86.Driver} {layout : X86.WordRegion.Layout}
    (hdisj : ExternalDisjoint D layout)
    {outside m m' : Memory} {words : X86.WordRegion.Words}
    (hreal : X86.WordRegion.Realizes layout outside words m)
    (hread : m'.readable = m.readable)
    (hwrite : m'.writable = m.writable)
    (hframe : ∀ addr, D.mapped addr = false → m'.bytes addr = m.bytes addr) :
    (∀ addr, D.mapped addr = true → m.bytes addr = outside.bytes addr) ∧
    (∀ slot < layout.slots, m'.read64 (layout.address slot) = words slot) ∧
    X86.WordRegion.Realizes layout
      { outside with bytes := fun a => if layout.allowed a then outside.bytes a else m'.bytes a }
      words m' := by
  refine ⟨?_, ?_, ?_⟩
  · intro addr hmapped
    apply hreal.frame
    cases hall : layout.allowed addr with
    | false => rfl
    | true =>
      have := hdisj addr hall
      rw [this] at hmapped
      cases hmapped
  · intro slot hslot
    rw [external_read64_preserved hdisj hframe hslot]
    exact hreal.view slot hslot
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro slot hslot
      rw [external_read64_preserved hdisj hframe hslot]
      exact hreal.view slot hslot
    · intro slot hslot
      rw [hread]
      exact hreal.readable slot hslot
    · intro slot hslot
      rw [hwrite]
      exact hreal.writable slot hslot
    · intro addr hnotAllowed
      simp [hnotAllowed]

/-- **External `Rt.Proof.WordAt` Frame Theorem**: any `WordAt m b v` whose 8 bytes
lie outside `D.mapped` is preserved bit-for-bit by any execution of `D`. -/
theorem external_wordAt_preserved {D : X86.Driver} {m m' : Memory} {b v : Word}
    (hw : Rt.Proof.WordAt m b v)
    (hdisj : ∀ i < 8, D.mapped (b + UInt64.ofNat i) = false)
    (hread : m'.readable = m.readable)
    (hframe : ∀ addr, D.mapped addr = false → m'.bytes addr = m.bytes addr) :
    Rt.Proof.WordAt m' b v where
  bytes i hi := by
    rw [hframe _ (hdisj i hi)]
    exact hw.bytes i hi
  readable i hi := by
    rw [hread]
    exact hw.readable i hi

namespace KernelRegionLayout

theorem preserved_of_unmapped {kpt : KernelRegionLayout} {D : X86.Driver}
    (hdisj : kpt.DisjointFromDriver D) {before after : Word → UInt8}
    (hunmapped : ∀ addr, D.mapped addr = false → after addr = before addr) :
    kpt.Preserved before after where
  bytes_eq addr hin := hunmapped addr (hdisj addr hin)
  pml4_entries_eq slot hslot :=
    external_read64_preserved
      (fun a ha => hdisj a (by simp [inTables, ha])) hunmapped hslot
  pdpt_entries_eq slot hslot :=
    external_read64_preserved
      (fun a ha => hdisj a (by simp [inTables, ha])) hunmapped hslot
  pd_entries_eq slot hslot :=
    external_read64_preserved
      (fun a ha => hdisj a (by simp [inTables, ha])) hunmapped hslot
  pt_entries_eq slot hslot :=
    external_read64_preserved
      (fun a ha => hdisj a (by simp [inTables, ha])) hunmapped hslot

end KernelRegionLayout

namespace KernelPageTables

export KernelRegionLayout (preserved_of_unmapped)

end KernelPageTables

/-- Conditional frame corollary: running `Session.runCalls` under a driver
disjoint from `kpt` preserves all bytes and 64-bit slots of `kpt`. -/
theorem kernelTablesPreserved_of_session_runCalls {s : X86.DriverSession.Session}
    {textSize : Nat} (hD : s.linked.driver.Ok textSize)
    {kpt : KernelRegionLayout} (hdisj : kpt.DisjointFromDriver s.linked.driver)
    {inputs : List X86.DriverSession.Input} {bytes : Word → UInt8} {k : Nat}
    {output : X86.DriverSession.Output}
    (hrun : s.runCalls inputs bytes k = .ok output) :
    kpt.Preserved bytes output.bytes :=
  KernelRegionLayout.preserved_of_unmapped hdisj
    (session_runCalls_preserves_unmapped hD hrun).1

/-- Conditional frame corollary: running `Session.run` (`cx_init` + `runCalls`)
under a driver disjoint from `kpt` preserves all bytes and 64-bit slots of `kpt`. -/
theorem kernelTablesPreserved_of_session_run {s : X86.DriverSession.Session}
    {textSize : Nat} (hD : s.linked.driver.Ok textSize)
    {kpt : KernelRegionLayout} (hdisj : kpt.DisjointFromDriver s.linked.driver)
    {inputs : List X86.DriverSession.Input} {k : Nat}
    {output : X86.DriverSession.Output}
    (hrun : s.run inputs k = .ok output) :
    kpt.Preserved s.linked.driver.init output.bytes :=
  KernelRegionLayout.preserved_of_unmapped hdisj
    (session_run_preserves_unmapped hD hrun).1

/-! ## 3. Non-Vacuous Ring-0 Certified-Compilation Admission (`S2`, `S3`, `A3-1`, `A3-2`, `A6-1`, `A6-5`) -/

/-- Concrete Ring-0 safety properties for a rechecked artifact's `CheckedProgram`,
`view`, `GoesWrong`, `program`, `encoded`, and `linked = a.linked sip.driver`:
packages unconditional `sip.driver.CanonicalOk encoded.text.size`, semantic
refinement of `CheckedProgram`, absence of model faults/traps (`¬ GoesWrong`)
at every clock `k` on valid source inputs, software resource-guard termination
on divergence, `Stream.Valid` decoded instruction/terminator structure, and
frame preservation of all unmapped memory, `.text`, and `KernelRegionLayout`. -/
structure Ring0Safety (sip : Ring0Sip) (checkedProg : CheckedProgram)
    (view : Nat → Option Obs → Option (Option Obs))
    (GoesWrong : (Nat × List Nat) → Prop)
    (program : X86.Program) (encoded : X86.Encode.Output) (linked : X86.Linked) : Prop where
  driver_eq   : linked.driver = sip.driver
  canonicalOk : sip.driver.CanonicalOk encoded.text.size
  elfHash_eq  : Ixon.Address.blake3Pure linked.object = sip.claim.elfHash
  streamValid : X86.Stream.Valid program encoded
  semantics :
    ∀ (i : Nat × List Nat),
      (∀ k w, Lang.run linked i k = .ok w →
        (∃ k' v, Lang.run checkedProg i k' = .ok v ∧
          view i.1 (Lang.obs v) = some w) ∨ GoesWrong i) ∧
      (¬ GoesWrong i → ∀ k, ¬ (Lang.run linked i k).GoesWrong) ∧
      ((∀ k, Lang.run checkedProg i k = .timeout) →
        (∀ k, Lang.run linked i k = .timeout) ∨
          ∃ k failure, Lang.run linked i k = .resource failure)
  cfi_inText :
    ∀ state next, X86.ByteEval.step encoded.text sip.driver.base state = .ok next →
      sip.driver.inText encoded.text.size state.rip = true
  initCall_frame :
    ∀ k w mem', linked.initCall k = .ok (w, mem') →
      ∀ addr, sip.driver.mapped addr = false → mem'.readByte addr = sip.driver.init addr
  rootCall_frame :
    ∀ r ns bytes k w mem', linked.rootCall r ns bytes k = .ok (w, mem') →
      ∀ addr, sip.driver.mapped addr = false → mem'.readByte addr = bytes addr
  session_frame :
    ∀ (drop : String) inputs bytes k output,
      (X86.DriverSession.Session.mk linked drop).runCalls inputs bytes k = .ok output →
      (∀ addr, sip.driver.mapped addr = false → output.bytes addr = bytes addr) ∧
      (∀ addr, sip.driver.inText encoded.text.size addr = true → output.bytes addr = bytes addr) ∧
      (∀ kpt : KernelRegionLayout, kpt.DisjointFromDriver sip.driver →
        kpt.Preserved bytes output.bytes)

/-- **Strong Non-Vacuous Ring-0 Certified-Compilation Admission Proposition (`S2`, `A3-1`, `A6-1`)**:
Explicitly binds the parsed certificate `cert` and the rechecked artifact `a`
produced by `Recheck.run` (for `.immortal`), `Recheck.runWithContracts` (for `.zeroRc`),
or `Recheck.RcReplay.run` (for `.plainRc`) on `P`, pinning `checkedProg`, `view`,
`GoesWrong`, `program`, `encoded`, and `linked := a.linked sip.driver` directly
to `a` and establishing `sip.driver.CanonicalOk a.backend.encoded.text.size`
and `Sem.Refines a.front.source (a.linked sip.driver)`. -/
def AdmittedRing0Sip (sip : Ring0Sip) (P : Src.Program) : Prop :=
  match sip.claim.policy with
  | .immortal =>
    ∃ (cert : Recheck.Cert) (a : Recheck.Artifact) (rootId : Src.CId) (root : Recheck.Root)
      (sig : Rt.Sig) (ty : Rt.FoTy),
      sip.claim.WellFormed ∧
      P.roots.head? = some (sip.claim.target, rootId) ∧
      Recheck.Cert.ofText sip.certText = .ok cert ∧
      Recheck.run sip.cfg P cert = .ok a ∧
      Recheck.front sip.cfg P cert = .ok (a.src, a.checked) ∧
      a.roots.head? = some root ∧
      CompileClaim.rootParamsAllNat a.src root.const = true ∧
      root.ty = some (sig, ty) ∧
      CompileClaim.isImmortalViewType sig ty = true ∧
      root.params = sip.claim.abiArity ∧
      Ixon.Address.blake3Pure a.object = sip.claim.elfHash ∧
      sip.driver.CanonicalOk a.backend.encoded.text.size ∧
      Sem.Refines a.front.source (a.linked sip.driver) ∧
      Ring0Safety sip ⟨a.src, a.checked⟩ a.front.view a.front.GoesWrong
        a.backend.checked.program a.backend.encoded (a.linked sip.driver)
  | .zeroRc =>
    ∃ (cert : Recheck.Cert) (a : Recheck.Artifact) (rootId : Src.CId) (root : Recheck.Root)
      (sig : Rt.Sig) (ty : Rt.FoTy),
      sip.claim.WellFormed ∧
      P.roots.head? = some (sip.claim.target, rootId) ∧
      Recheck.Cert.ofText sip.certText = .ok cert ∧
      Recheck.runWithContracts sip.cfg P cert = .ok a ∧
      Recheck.run sip.cfg P cert = .ok a ∧
      Recheck.front sip.cfg P cert = .ok (a.src, a.checked) ∧
      Own.Plain.selectRcPolicyForSrc a.src a.front.fir = .zeroRc ∧
      Own.Plain.checkContractPlainMap a.front.fir (Own.Plain.Program.canonical a.front.fir).bodies = true ∧
      a.roots.head? = some root ∧
      CompileClaim.rootParamsAllNat a.src root.const = true ∧
      root.ty = some (sig, ty) ∧
      CompileClaim.isImmortalViewType sig ty = true ∧
      root.params = sip.claim.abiArity ∧
      Ixon.Address.blake3Pure a.object = sip.claim.elfHash ∧
      sip.driver.CanonicalOk a.backend.encoded.text.size ∧
      Sem.Refines (⟨a.src, a.checked⟩ : CheckedProgram) (Own.Plain.Program.canonical a.fir) ∧
      Sem.Refines a.front.source (a.linked sip.driver) ∧
      Ring0Safety sip ⟨a.src, a.checked⟩ a.front.view a.front.GoesWrong
        a.backend.checked.program a.backend.encoded (a.linked sip.driver)
  | .plainRc =>
    ∃ (cert : Recheck.RcReplay.Cert) (a : Recheck.RcReplay.Artifact) (rootId : Src.CId)
      (root : Recheck.Root) (sig : Rt.Sig) (ty : Rt.FoTy),
      sip.claim.WellFormed ∧
      P.roots.head? = some (sip.claim.target, rootId) ∧
      Recheck.RcReplay.Cert.ofText sip.certText = .ok cert ∧
      Recheck.RcReplay.run sip.cfg P cert = .ok a ∧
      Recheck.front sip.cfg P cert.base = .ok (a.front.src, a.front.checked) ∧
      a.roots.head? = some root ∧
      CompileClaim.rootParamsAllNat a.front.src root.const = true ∧
      root.ty = some (sig, ty) ∧
      root.params = sip.claim.abiArity ∧
      Ixon.Address.blake3Pure a.backend.object = sip.claim.elfHash ∧
      sip.driver.CanonicalOk a.backend.encoded.text.size ∧
      Sem.Refines a.front.source (a.linked sip.driver) ∧
      Ring0Safety sip ⟨a.front.src, a.front.checked⟩ a.front.view a.front.GoesWrong
        a.backend.checked.program a.backend.encoded (a.linked sip.driver)

/-- Helper constructing `Ring0Safety` once `sip.driver.CanonicalOk encoded.text.size`
has been discharged. -/
theorem ring0Safety_of_parts {sip : Ring0Sip} {checkedProg : CheckedProgram}
    {view : Nat → Option Obs → Option (Option Obs)}
    {GoesWrong : (Nat × List Nat) → Prop}
    {program : X86.Program} {encoded : X86.Encode.Output} {linked : X86.Linked}
    (hdriver : linked.driver = sip.driver)
    (hCanon : sip.driver.CanonicalOk encoded.text.size)
    (hhash : Ixon.Address.blake3Pure linked.object = sip.claim.elfHash)
    (hstream : X86.Stream.Valid program encoded)
    (hsem :
      ∀ (i : Nat × List Nat),
        (∀ k w, Lang.run linked i k = .ok w →
          (∃ k' v, Lang.run checkedProg i k' = .ok v ∧
            view i.1 (Lang.obs v) = some w) ∨ GoesWrong i) ∧
        (¬ GoesWrong i → ∀ k, ¬ (Lang.run linked i k).GoesWrong) ∧
        ((∀ k, Lang.run checkedProg i k = .timeout) →
          (∀ k, Lang.run linked i k = .timeout) ∨
            ∃ k failure, Lang.run linked i k = .resource failure)) :
    Ring0Safety sip checkedProg view GoesWrong program encoded linked where
  driver_eq := hdriver
  canonicalOk := hCanon
  elfHash_eq := hhash
  streamValid := hstream
  semantics := hsem
  cfi_inText state next hstep := by
    have hbase64 : sip.driver.base.toNat + encoded.text.size ≤ 2 ^ 64 := by
      have := hCanon.below47.2.2; omega
    exact step_rip_inText sip.driver hbase64 hstep
  initCall_frame k w mem' hinit addr hunm := by
    have hOk : linked.driver.Ok encoded.text.size := hdriver ▸ hCanon.toOk
    have h := (initCall_preserves_unmapped hOk hinit).2.2 addr (hdriver ▸ hunm)
    simpa [hdriver] using h
  rootCall_frame r ns bytes k w mem' hroot addr hunm := by
    have hOk : linked.driver.Ok encoded.text.size := hdriver ▸ hCanon.toOk
    exact (rootCall_preserves_unmapped hOk hroot).2.2 addr (hdriver ▸ hunm)
  session_frame drop inputs bytes k output hcalls := by
    let s : X86.DriverSession.Session := ⟨linked, drop⟩
    have hs : s.linked.driver = sip.driver := hdriver
    have hCanon' : s.linked.driver.CanonicalOk encoded.text.size := hs ▸ hCanon
    have hOk' : s.linked.driver.Ok encoded.text.size := hCanon'.toOk
    refine ⟨?_, ?_, ?_⟩
    · intro addr hunm
      exact (session_runCalls_preserves_unmapped (s := s) hOk' hcalls).1 addr (hs ▸ hunm)
    · intro addr htext
      exact text_preserved_of_canonicalOk (s := s) hCanon' hcalls (hs ▸ htext)
    · intro kpt hkpt
      exact kernelTablesPreserved_of_session_runCalls (s := s) hOk' (hs ▸ hkpt) hcalls

/-- **End-to-End Ring-0 Certified-Compilation Admission Theorem (`verifyRing0Sip_sound`)**:
Any `Ring0Sip` that passes `sip.verifyProgram P = true` (under `.immortal`,
`.zeroRc`, or `.plainRc` policy) satisfies the non-vacuous `AdmittedRing0Sip sip P`
(`S2`, `A3-1`, `A3-9`, `A6-1`). -/
theorem verifyRing0Sip_sound {sip : Ring0Sip} {P : Src.Program}
    (hver : sip.verifyProgram P = true) :
    AdmittedRing0Sip sip P := by
  unfold Ring0Sip.verifyProgram at hver
  rw [Bool.and_eq_true] at hver
  rcases hver with ⟨hclaimVer, hcanonCheck⟩
  unfold AdmittedRing0Sip
  cases hpol : sip.claim.policy with
  | immortal =>
    obtain ⟨cert, a, rootId, root, sig, ty, hwf, hhead, hcert, hrun, hfront, hahead,
      hnatParams, hty, htyOk, hparams, hhash, hsem⟩ :=
      CompileClaim.verifyProgram_immortal_sound hpol hclaimVer
    simp only [Ring0Sip.verifiedTextSize?, hpol, hcert, hrun] at hcanonCheck
    have hCanon : sip.driver.CanonicalOk a.backend.encoded.text.size :=
      (X86.Driver.checkCanonical_iff sip.driver _).mp hcanonCheck
    obtain ⟨_, _, _, _, hemit, _⟩ := Recheck.run_parts hrun
    obtain ⟨input, hem⟩ := Backend.emit_parts hemit
    have hstream : X86.Stream.Valid a.backend.checked.program a.backend.encoded :=
      hem.encoded ▸ hem.stream
    have hsemD := hsem sip.driver hCanon.toOk
    exact ⟨cert, a, rootId, root, sig, ty, hwf, hhead, hcert, hrun, hfront, hahead,
      hnatParams, hty, htyOk, hparams, hhash, hCanon, hsemD.1,
      ring0Safety_of_parts rfl hCanon hhash hstream hsemD.2⟩
  | zeroRc =>
    obtain ⟨cert, a, rootId, root, sig, ty, hwf, hhead, hcert, hrunC, hrun, hfront,
      hrcPol, hcheckMap, hahead, hnatParams, hty, htyOk, hparams, hhash, hsem⟩ :=
      CompileClaim.verifyProgram_zeroRc_sound hpol hclaimVer
    simp only [Ring0Sip.verifiedTextSize?, hpol, hcert, hrunC] at hcanonCheck
    have hCanon : sip.driver.CanonicalOk a.backend.encoded.text.size :=
      (X86.Driver.checkCanonical_iff sip.driver _).mp hcanonCheck
    obtain ⟨_, _, _, _, hemit, _⟩ := Recheck.run_parts hrun
    obtain ⟨input, hem⟩ := Backend.emit_parts hemit
    have hstream : X86.Stream.Valid a.backend.checked.program a.backend.encoded :=
      hem.encoded ▸ hem.stream
    have hsemD := hsem sip.driver hCanon.toOk
    exact ⟨cert, a, rootId, root, sig, ty, hwf, hhead, hcert, hrunC, hrun, hfront,
      hrcPol, hcheckMap, hahead, hnatParams, hty, htyOk, hparams, hhash, hCanon,
      hsemD.1, hsemD.2.1,
      ring0Safety_of_parts rfl hCanon hhash hstream hsemD.2.2⟩
  | plainRc =>
    obtain ⟨cert, a, rootId, root, sig, ty, hwf, hhead, hcert, hrun, hfront, hahead,
      hnatParams, hty, hparams, hhash, hsem⟩ :=
      CompileClaim.verifyProgram_plainRc_sound hpol hclaimVer
    simp only [Ring0Sip.verifiedTextSize?, hpol, hcert, hrun] at hcanonCheck
    have hCanon : sip.driver.CanonicalOk a.backend.encoded.text.size :=
      (X86.Driver.checkCanonical_iff sip.driver _).mp hcanonCheck
    obtain ⟨_, _, _, _, _, hemit, _⟩ := Recheck.RcReplay.run_parts hrun
    obtain ⟨input, hem⟩ := Backend.emit_parts hemit
    have hstream : X86.Stream.Valid a.backend.checked.program a.backend.encoded :=
      hem.encoded ▸ hem.stream
    have hsemD := hsem sip.driver hCanon.toOk
    exact ⟨cert, a, rootId, root, sig, ty, hwf, hhead, hcert, hrun, hfront, hahead,
      hnatParams, hty, hparams, hhash, hCanon, hsemD.1,
      ring0Safety_of_parts rfl hCanon hhash hstream hsemD.2⟩

/-- **Byte-Level Ring-0 Certified-Compilation Admission Theorem (`verifyBytesRing0Sip_sound`)**:
Any `Ring0Sip` that passes `sip.verifyBytes envBytes equations typecheck = true`
yields an ingested `Recheck.Input` with `typecheck = true → Ixon.V3.Tc.checkEnv inp.env = .ok ()`
and `Src.Resource.validate inp.program = .ok ()` whose program satisfies the
non-vacuous `AdmittedRing0Sip sip inp.program`. -/
theorem verifyBytesRing0Sip_sound {sip : Ring0Sip} {envBytes : ByteArray}
    {equations : Lean.Json} {typecheck : Bool}
    (hver : sip.verifyBytes envBytes equations typecheck = true) :
    ∃ inp : Recheck.Input,
      Recheck.ingress envBytes equations
        (CompileClaim.selectTargetRoots sip.cfg equations sip.claim.target) typecheck = .ok inp ∧
      Ixon.V3.decodeAnonymousEnv envBytes = .ok inp.env ∧
      (typecheck = true → Ixon.V3.Tc.checkEnv inp.env = .ok ()) ∧
      Src.Resource.validate inp.program = .ok () ∧
      inp.env.root = sip.claim.env ∧
      AdmittedRing0Sip sip inp.program := by
  unfold Ring0Sip.verifyBytes at hver
  cases hing : Recheck.ingress envBytes equations
      (CompileClaim.selectTargetRoots sip.cfg equations sip.claim.target) typecheck with
  | error _ => simp [hing] at hver
  | ok inp =>
    simp only [hing, Bool.and_eq_true, beq_iff_eq] at hver
    obtain ⟨hdec, htc, hres, _⟩ := Recheck.ingress_parts hing
    exact ⟨inp, rfl, hdec, htc, hres, hver.1, verifyRing0Sip_sound hver.2⟩

/-- What a SIP's certificate determines on `P`: the checked source, its `view` and
`GoesWrong`, the checked stream and the linked object. -/
structure Ring0Artifact where
  checkedProg : CheckedProgram
  view : Nat → Option Obs → Option (Option Obs)
  GoesWrong : (Nat × List Nat) → Prop
  program : X86.Program
  encoded : X86.Encode.Output
  linked : X86.Linked

/-- The artifact `sip`'s certificate determines on `P` under its policy, or `none`
when the certificate does not parse or replay. Being a function of `sip` and `P`,
it leaves none of these objects to an existential. -/
noncomputable def Ring0Sip.artifact? (sip : Ring0Sip) (P : Src.Program) : Option Ring0Artifact :=
  match sip.claim.policy with
  | .immortal =>
    match Recheck.Cert.ofText sip.certText with
    | .ok cert =>
      match Recheck.run sip.cfg P cert with
      | .ok a => some ⟨⟨a.src, a.checked⟩, a.front.view, a.front.GoesWrong,
          a.backend.checked.program, a.backend.encoded, a.linked sip.driver⟩
      | .error _ => none
    | .error _ => none
  | .zeroRc =>
    match Recheck.Cert.ofText sip.certText with
    | .ok cert =>
      match Recheck.runWithContracts sip.cfg P cert with
      | .ok a => some ⟨⟨a.src, a.checked⟩, a.front.view, a.front.GoesWrong,
          a.backend.checked.program, a.backend.encoded, a.linked sip.driver⟩
      | .error _ => none
    | .error _ => none
  | .plainRc =>
    match Recheck.RcReplay.Cert.ofText sip.certText with
    | .ok cert =>
      match Recheck.RcReplay.run sip.cfg P cert with
      | .ok a => some ⟨⟨a.front.src, a.front.checked⟩, a.front.view, a.front.GoesWrong,
          a.backend.checked.program, a.backend.encoded, a.linked sip.driver⟩
      | .error _ => none
    | .error _ => none

/-- The guarantees an admitted SIP's artifact carries:
1. **No model faults, with no `.ok` premise.** On a source-safe input
   (`¬ GoesWrong i`), `¬ (Lang.run linked i k).GoesWrong` at every clock `k`.
2. **Source value refinement.** Whenever `Lang.run linked i k = .ok w` on such an
   input, the source produces a value `v` with `view i.1 (Lang.obs v) = some w`.
3. **Conditional frames.** A `rootCall` that returns `.ok` preserves every byte of a
   disjoint peer, and a `Session.runCalls` that returns `.ok` preserves any disjoint
   `KernelRegionLayout`. -/
def Ring0Artifact.Safe (A : Ring0Artifact) (sip : Ring0Sip) : Prop :=
  A.linked.driver = sip.driver ∧
  sip.driver.CanonicalOk A.encoded.text.size ∧
  Ixon.Address.blake3Pure A.linked.object = sip.claim.elfHash ∧
  X86.Stream.Valid A.program A.encoded ∧
  (∀ (i : Nat × List Nat), ¬ A.GoesWrong i →
    (∀ k, ¬ (Lang.run A.linked i k).GoesWrong) ∧
    (∀ k w, Lang.run A.linked i k = .ok w →
      ∃ k' v, Lang.run A.checkedProg i k' = .ok v ∧
        A.view i.1 (Lang.obs v) = some w)) ∧
  (∀ (D_peer : X86.Driver), DisjointDrivers sip.driver D_peer →
    ∀ r ns bytes k w mem', A.linked.rootCall r ns bytes k = .ok (w, mem') →
      ∀ addr, D_peer.mapped addr = true → mem'.readByte addr = bytes addr) ∧
  (∀ (kpt : KernelRegionLayout), kpt.DisjointFromDriver sip.driver →
    ∀ (drop : String) inputs bytes k output,
      (X86.DriverSession.Session.mk A.linked drop).runCalls inputs bytes k = .ok output →
      kpt.Preserved bytes output.bytes)

theorem Ring0Artifact.safe_of_ring0Safety {sip : Ring0Sip} {A : Ring0Artifact}
    (hsafe : Ring0Safety sip A.checkedProg A.view A.GoesWrong A.program A.encoded A.linked) :
    A.Safe sip := by
  refine ⟨hsafe.driver_eq, hsafe.canonicalOk, hsafe.elfHash_eq, hsafe.streamValid, ?_, ?_, ?_⟩
  · intro i hnotGW
    have hsem := hsafe.semantics i
    refine ⟨hsem.2.1 hnotGW, ?_⟩
    intro k w hok
    rcases hsem.1 k w hok with hval | hgw
    · exact hval
    · exact False.elim (hnotGW hgw)
  · intro D_peer hdisj r ns bytes k w mem' hroot addr hpeer
    exact hsafe.rootCall_frame r ns bytes k w mem' hroot addr (hdisj.symm addr hpeer)
  · intro kpt hkpt drop inputs bytes k output hcalls
    exact (hsafe.session_frame drop inputs bytes k output hcalls).2.2 kpt hkpt

/-- **Admitted SIPs do not fault (`S3`, `A3-2`, `A6-5`).** A SIP passing
`sip.verifyProgram P` has the artifact its certificate determines
(`Ring0Sip.artifact?`), and that artifact satisfies `Ring0Artifact.Safe`. The
objects are functions of `sip` and `P`, so `GoesWrong` cannot be chosen to make the
semantic clauses vacuous. -/
theorem admittedRing0Sip_call_not_goesWrong {sip : Ring0Sip} {P : Src.Program}
    (hver : sip.verifyProgram P = true) :
    ∃ A : Ring0Artifact, sip.artifact? P = some A ∧ A.Safe sip := by
  have hadm := verifyRing0Sip_sound hver
  unfold AdmittedRing0Sip at hadm
  cases hpol : sip.claim.policy <;> rw [hpol] at hadm
  · rcases hadm with ⟨cert, a, _, _, _, _, _, _, hcert, hrun, _, _, _, _, _, _, _, _, _, hsafe⟩
    exact ⟨⟨⟨a.src, a.checked⟩, a.front.view, a.front.GoesWrong,
        a.backend.checked.program, a.backend.encoded, a.linked sip.driver⟩,
      by simp only [Ring0Sip.artifact?, hpol, hcert, hrun],
      Ring0Artifact.safe_of_ring0Safety hsafe⟩
  · rcases hadm with
      ⟨cert, a, _, _, _, _, _, _, hcert, hrunC, _, _, _, _, _, _, _, _, _, _, _, _, _, hsafe⟩
    exact ⟨⟨⟨a.src, a.checked⟩, a.front.view, a.front.GoesWrong,
        a.backend.checked.program, a.backend.encoded, a.linked sip.driver⟩,
      by simp only [Ring0Sip.artifact?, hpol, hcert, hrunC],
      Ring0Artifact.safe_of_ring0Safety hsafe⟩
  · rcases hadm with ⟨cert, a, _, _, _, _, _, _, hcert, hrun, _, _, _, _, _, _, _, _, hsafe⟩
    exact ⟨⟨⟨a.front.src, a.front.checked⟩, a.front.view, a.front.GoesWrong,
        a.backend.checked.program, a.backend.encoded, a.linked sip.driver⟩,
      by simp only [Ring0Sip.artifact?, hpol, hcert, hrun],
      Ring0Artifact.safe_of_ring0Safety hsafe⟩

/-! ## 4. Multi-SIP Single-Address-Space Coexistence Theorems -/

/-- **Conditional Multi-SIP Single-Address-Space Frame Theorem (`multi_sip_frame`)**:
When two SIP sessions `s₁` and `s₂` satisfy `CoexistingSipPair` and execute in an
interleaved schedule (`s₁` runs -> `s₂` runs -> `s₁` runs again) in the same
shared byte address space:
1. Running `s₁` preserves every byte of `s₂.linked.driver.mapped`, every byte of
   `s₁`'s `.text`, and every byte of `kernelPageTables`.
2. Running `s₂` on `out₁.bytes` preserves every byte of `s₁.linked.driver.mapped`,
   every byte of `s₂`'s `.text`, and every byte of `kernelPageTables`.
3. Resuming `s₁` on `out₂.bytes` preserves every byte of `s₂.linked.driver.mapped`
   from `out₂.bytes`, and `kernelPageTables` remains bit-for-bit identical to
   `bytes₀` across the entire three-stage schedule. -/
theorem multi_sip_frame {s₁ s₂ : X86.DriverSession.Session}
    {kernelPageTables : Word → Bool} {textSize₁ textSize₂ : Nat}
    (hco : CoexistingSipPair s₁.linked.driver s₂.linked.driver kernelPageTables textSize₁ textSize₂)
    {inputs₁ inputs₂ inputs₃ : List X86.DriverSession.Input}
    {bytes₀ : Word → UInt8} {k₁ k₂ k₃ : Nat}
    {out₁ out₂ out₃ : X86.DriverSession.Output}
    (hrun₁ : s₁.runCalls inputs₁ bytes₀ k₁ = .ok out₁)
    (hrun₂ : s₂.runCalls inputs₂ out₁.bytes k₂ = .ok out₂)
    (hrun₃ : s₁.runCalls inputs₃ out₂.bytes k₃ = .ok out₃) :
    (∀ addr, s₂.linked.driver.mapped addr = true → out₁.bytes addr = bytes₀ addr) ∧
    (∀ addr, s₁.linked.driver.mapped addr = true → out₂.bytes addr = out₁.bytes addr) ∧
    (∀ addr, s₂.linked.driver.mapped addr = true → out₃.bytes addr = out₂.bytes addr) ∧
    (∀ addr, s₁.linked.driver.inText textSize₁ addr = true → out₁.bytes addr = bytes₀ addr) ∧
    (∀ addr, s₂.linked.driver.inText textSize₂ addr = true → out₂.bytes addr = out₁.bytes addr) ∧
    (∀ addr, s₁.linked.driver.inText textSize₁ addr = true → out₃.bytes addr = out₂.bytes addr) ∧
    (∀ addr, kernelPageTables addr = true →
      out₁.bytes addr = bytes₀ addr ∧
      out₂.bytes addr = bytes₀ addr ∧
      out₃.bytes addr = bytes₀ addr) := by
  have h1 := (session_runCalls_preserves_unmapped hco.ok₁.toOk hrun₁).1
  have h2 := (session_runCalls_preserves_unmapped hco.ok₂.toOk hrun₂).1
  have h3 := (session_runCalls_preserves_unmapped hco.ok₁.toOk hrun₃).1
  have hsymm := hco.disjoint.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro addr hm₂
    exact h1 addr (hsymm addr hm₂)
  · intro addr hm₁
    exact h2 addr (hco.disjoint addr hm₁)
  · intro addr hm₂
    exact h3 addr (hsymm addr hm₂)
  · intro addr ht₁
    exact text_preserved_of_canonicalOk hco.ok₁ hrun₁ ht₁
  · intro addr ht₂
    exact text_preserved_of_canonicalOk hco.ok₂ hrun₂ ht₂
  · intro addr ht₁
    exact text_preserved_of_canonicalOk hco.ok₁ hrun₃ ht₁
  · intro addr hk
    have hk1 := h1 addr (hco.kernel₁ addr hk)
    have hk2 := (h2 addr (hco.kernel₂ addr hk)).trans hk1
    have hk3 := (h3 addr (hco.kernel₁ addr hk)).trans hk2
    exact ⟨hk1, hk2, hk3⟩

/-- Word-level corollary of `multi_sip_frame`: any aligned 64-bit word
region (`WordRegion.Layout`) inside `s₂.linked.driver.mapped` or inside
`kernelPageTables` has all of its 64-bit words preserved when `s₁` runs. -/
theorem multi_sip_wordRegion_preserved {s₁ s₂ : X86.DriverSession.Session}
    {kernelPageTables : Word → Bool} {textSize₁ textSize₂ : Nat}
    (hco : CoexistingSipPair s₁.linked.driver s₂.linked.driver kernelPageTables textSize₁ textSize₂)
    {inputs₁ : List X86.DriverSession.Input} {bytes₀ : Word → UInt8} {k₁ : Nat}
    {out₁ : X86.DriverSession.Output}
    (hrun₁ : s₁.runCalls inputs₁ bytes₀ k₁ = .ok out₁)
    {layout₂ layoutK : X86.WordRegion.Layout}
    (hsub₂ : ∀ addr, layout₂.allowed addr = true → s₂.linked.driver.mapped addr = true)
    (hsubK : ∀ addr, layoutK.allowed addr = true → kernelPageTables addr = true) :
    (∀ slot < layout₂.slots,
      (⟨out₁.bytes, s₂.linked.driver.mapped, s₂.linked.driver.mapped⟩ : Memory).read64 (layout₂.address slot) =
      (⟨bytes₀, s₂.linked.driver.mapped, s₂.linked.driver.mapped⟩ : Memory).read64 (layout₂.address slot)) ∧
    (∀ slot < layoutK.slots,
      (⟨out₁.bytes, kernelPageTables, fun _ => false⟩ : Memory).read64 (layoutK.address slot) =
      (⟨bytes₀, kernelPageTables, fun _ => false⟩ : Memory).read64 (layoutK.address slot)) := by
  have h1 := (session_runCalls_preserves_unmapped hco.ok₁.toOk hrun₁).1
  have hdisj₂ : ExternalDisjoint s₁.linked.driver layout₂ :=
    fun addr ha => hco.disjoint.symm addr (hsub₂ addr ha)
  have hdisjK : ExternalDisjoint s₁.linked.driver layoutK :=
    fun addr ha => hco.kernel₁ addr (hsubK addr ha)
  exact ⟨fun slot hslot => external_read64_preserved hdisj₂ h1 hslot,
         fun slot hslot => external_read64_preserved hdisjK h1 hslot⟩

/-- **Conditional $N$-SIP Single-Address-Space Frame Theorem (`pairwiseDisjointSips_frame`)**:
In a `PairwiseDisjointSips` family of $N$ SIPs, executing any SIP $i$ preserves
the private heap and stack (`sips[j].mapped`) of every peer SIP $j \ne i$ as well
as `kernelPageTables` bit-for-bit. -/
theorem pairwiseDisjointSips_frame {sips : List X86.Driver}
    {kernelPageTables : Word → Bool}
    (hfamily : PairwiseDisjointSips sips kernelPageTables)
    {i : Nat} (hi : i < sips.length)
    {s : X86.DriverSession.Session} (hs : s.linked.driver = sips[i])
    {textSize : Nat} (hOk : sips[i].Ok textSize)
    {inputs : List X86.DriverSession.Input} {bytes : Word → UInt8}
    {k : Nat} {output : X86.DriverSession.Output}
    (hrun : s.runCalls inputs bytes k = .ok output) :
    (∀ (j : Nat) (hj : j < sips.length), i ≠ j →
      ∀ addr, sips[j].mapped addr = true → output.bytes addr = bytes addr) ∧
    (∀ addr, kernelPageTables addr = true → output.bytes addr = bytes addr) := by
  have hOk' : s.linked.driver.Ok textSize := hs ▸ hOk
  have hunm := (session_runCalls_preserves_unmapped hOk' hrun).1
  refine ⟨?_, ?_⟩
  · intro j hj hne addr hmj
    have hdisj := (hfamily.1 i j hi hj hne).symm addr hmj
    exact hunm addr (hs ▸ hdisj)
  · intro addr hk
    have hmem : sips[i] ∈ sips := List.getElem_mem hi
    have hdisj := hfamily.2 sips[i] hmem addr hk
    exact hunm addr (hs ▸ hdisj)

end IxCC.Ring0
