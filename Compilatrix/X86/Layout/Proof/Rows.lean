import Compilatrix.X86.StreamEffects

/-!
# Rows on two related cores, and what a row leaves alone

Layout's proofs run one typed program beside a renumbered copy. Their
cores have equal registers and memories that agree outside a mask of
return-slot bytes (`Stream.MemoryRelated`), exactly E2's relation between
the typed and the byte machine with no active frames. So E2's generic
`run_pair` applies: on such cores a row computes the same result, faults
alike, and leaves cores related under the mask with its written bytes
cleared (`exec_pair`).

A row also leaves every byte outside its write footprint (`Op.writes`)
unchanged (`run_bytes_outside`), so the return tokens of active frames,
which no safe row writes, survive it (`TokensAt`).
-/

namespace Compilatrix.X86.Layout.Proof

open Compilatrix.X86
open Compilatrix.X86.Stream

/-! ## Related cores -/

/-- The outcome of a row on two related cores: the same fault, or the same
flags and related cores under the next mask. -/
def ExecPair (holes : Holes) : Except ExecFault (Core × ByteEval.Flags) → Except ExecFault (Core × ByteEval.Flags) → Prop
  | .ok (c, f), .ok (c', f') => f' = f ∧ c'.registers = c.registers ∧ MemoryRelated holes c.memory c'.memory
  | .error e, .error e' => e' = e
  | _, _ => False

theorem OperationSafe.noFrames {holes : Holes} {frames : List ReturnFrame} {op : Decode.Operation} {core : Core}
    (safe : OperationSafe holes frames op core) : OperationSafe holes [] op core :=
  ⟨safe.1, fun _ _ frame member => by simp at member⟩

/-- E2's `run_pair` with no active frames, for `Op.exec`. -/
theorem exec_pair {holes : Holes} {core core' : Core} (registers : core'.registers = core.registers)
    (memory : MemoryRelated holes core.memory core'.memory) (o : Op) (args : List Arg) (flags : ByteEval.Flags)
    {frames : List ReturnFrame} (safe : OperationSafe holes frames (.op o args) core) :
    ExecPair (nextHoles holes (.op o args) core) (o.exec args core flags) (o.exec args core' flags) := by
  have related : CoreRelated default 0 holes [] core core' :=
    ⟨registers.symm, memory, fun frame member => by simp at member⟩
  have pair := run_pair related o args (flags.restrict (desc o).flagsIn) (OperationSafe.noFrames safe)
  unfold Op.exec
  cases h : o.run args core (flags.restrict (desc o).flagsIn) <;>
    cases h' : o.run args core' (flags.restrict (desc o).flagsIn) <;>
    simp only [h, h', RunPair] at pair
  · simp [bind, Except.bind, ExecPair, pair]
  · rename_i r r'
    obtain ⟨c, out⟩ := r
    obtain ⟨c', out'⟩ := r'
    obtain ⟨same, rel⟩ := pair
    subst same
    simp only [bind, Except.bind, pure, Except.pure, ExecPair]
    exact ⟨trivial, rel.registers.symm, rel.memory⟩

/-! ## Bytes a row does not write -/

/-- `a` lies outside every range of an access list. -/
def Outside (a : Word) (accesses : List Access) : Prop :=
  ∀ access ∈ accesses, ∀ i < access.bytes, a ≠ access.address + UInt64.ofNat i

theorem write?_bytes {memory memory' : Memory} {width : Width} {address value a : Word}
    (h : memory.write? width address value = .ok memory') (outside : ∀ i < width.bytes, a ≠ address + UInt64.ofNat i) :
    memory'.bytes a = memory.bytes a := by
  simp only [Memory.write?] at h
  split at h
  · cases h
    exact Memory.writeLittle_bytes_outside _ _ _ _ _ outside
  · cases h

theorem store_bytes {before core core' : Core} {width : Width} {value : Word} {arg : Arg}
    (h : arg.store before width value core = .ok core') {a : Word} (outside : Outside a (arg.access before width)) :
    core'.memory.bytes a = core.memory.bytes a := by
  cases arg with
  | reg r =>
      simp only [Arg.store, Except.ok.injEq] at h
      subst h
      cases width <;> rfl
  | imm v =>
      simp only [Arg.store, Except.ok.injEq] at h
      subst h
      rfl
  | mem address =>
      simp only [Arg.store, bind, Except.bind] at h
      cases hw : core.memory.write? width (address.eval before) value with
      | error e => simp [hw] at h
      | ok mem' =>
          simp only [hw, pure, Except.pure, Except.ok.injEq] at h
          subst h
          exact write?_bytes hw (outside ⟨address.eval before, width.bytes⟩ (by simp [Arg.access]))

theorem writeSlots_bytes (before : Core) :
    ∀ (core : Core) (slots : List Slot) (args : List Arg) (results : List Word) (core' : Core),
      writeSlots before core slots args results = .ok core' → ∀ a, Outside a (slotWrites before slots args) →
        core'.memory.bytes a = core.memory.bytes a
  | core, [], args, results, core', h, a, _ => by
      cases args <;> simp [writeSlots, pure, Except.pure] at h <;> rw [h]
  | core, slot :: slots, [], results, core', h, a, _ => by
      simp [writeSlots, pure, Except.pure] at h
      rw [h]
  | core, slot :: slots, arg :: args, results, core', h, a, outside => by
      simp only [slotWrites] at outside
      cases hrole : slot.role
      case read | address =>
        simp only [writeSlots, hrole] at h
        exact writeSlots_bytes before core slots args results core' h a
          (fun access member => outside access (List.mem_append_right _ (by simpa [hrole] using member)))
      all_goals
        simp only [writeSlots, hrole, bind, Except.bind] at h
        split at h
        · cases h
        · rename_i mid hs
          rw [writeSlots_bytes before mid slots args results.tail core' h a
            (fun access member => outside access (List.mem_append_right _ member))]
          exact store_bytes hs (fun access member => outside access
            (List.mem_append_left _ (by simpa [hrole] using member)))

theorem writeImplicits_memory :
    ∀ (core : Core) (implicits : List Implicit) (results : List Word),
      (writeImplicits core implicits results).memory = core.memory
  | core, [], results => by cases results <;> rfl
  | core, implicit :: implicits, results => by
      simp only [writeImplicits]
      split
      · rw [writeImplicits_memory]
        cases implicit.width <;> rfl
      · exact writeImplicits_memory core implicits results

theorem stage_bytes {o : Op} {core staged : Core} {out : SemOut} (h : o.stage core out = .ok staged) {a : Word}
    (outside : Outside a (o.pushes core)) : staged.memory.bytes a = core.memory.bytes a := by
  unfold Op.stage at h
  unfold Op.pushes at outside
  cases hstack : (desc o).stack with
  | none =>
      simp only [hstack, pure, Except.pure, Except.ok.injEq] at h
      rw [h]
  | pop =>
      simp only [hstack, pure, Except.pure, Except.ok.injEq] at h
      rw [← h]
      rfl
  | push =>
      simp only [hstack] at h outside
      simp only [bind, Except.bind] at h
      split at h
      · cases h
      · rename_i mem hw
        simp only [pure, Except.pure, Except.ok.injEq] at h
        rw [← h]
        exact write?_bytes hw (outside ⟨core.readReg .rsp - 8, 8⟩ (by simp))

/-- A successful row leaves every byte outside its write footprint. -/
theorem run_bytes_outside {o : Op} {args : List Arg} {core core₁ : Core} {observed : ByteEval.Flags}
    {out : SemOut} (h : o.run args core observed = .ok (core₁, out)) {a : Word}
    (outside : Outside a (o.writes args core)) : core₁.memory.bytes a = core.memory.bytes a := by
  unfold Op.run at h
  simp only [bind, Except.bind, Except.mapError] at h
  cases hi : o.inputs args core with
  | error e => simp [hi] at h
  | ok inputs =>
  simp only [hi] at h
  cases hs : (desc o).sem ⟨inputs, observed⟩ with
  | error e => simp [hs] at h
  | ok sout =>
  simp only [hs] at h
  cases hst : o.stage core sout with
  | error e => simp [hst] at h
  | ok staged =>
  simp only [hst] at h
  cases hw : writeSlots core staged (desc o).slots args sout.results with
  | error e => simp [hw] at h
  | ok final =>
  simp only [hw, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  unfold Op.writes at outside
  rw [writeImplicits_memory, writeSlots_bytes core staged _ _ _ final hw a
    (fun access member => outside access (List.mem_append_right _ member))]
  exact stage_bytes hst (fun access member => outside access (List.mem_append_left _ member))

theorem exec_bytes_outside {o : Op} {args : List Arg} {core core₁ : Core} {flags flags₁ : ByteEval.Flags}
    (h : o.exec args core flags = .ok (core₁, flags₁)) {a : Word} (outside : Outside a (o.writes args core)) :
    core₁.memory.bytes a = core.memory.bytes a := by
  unfold Op.exec at h
  simp only [bind, Except.bind] at h
  cases hr : o.run args core (flags.restrict (desc o).flagsIn) with
  | error e => simp [hr] at h
  | ok r =>
      obtain ⟨c, out⟩ := r
      simp only [hr, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact run_bytes_outside hr outside

/-! ## Return tokens -/

/-- Each active frame's return slot holds its continuation token. -/
def TokensAt (memory : Memory) (frames : List ReturnFrame) : Prop :=
  ∀ frame ∈ frames, memory.read64 frame.returnSlot = frame.continuation.encode

theorem TokensAt.bytes {memory memory' : Memory} {frames : List ReturnFrame} (tokens : TokensAt memory frames)
    (same : ∀ frame ∈ frames, ∀ i < 8, memory'.bytes (frame.returnSlot + UInt64.ofNat i) =
      memory.bytes (frame.returnSlot + UInt64.ofNat i)) : TokensAt memory' frames := by
  intro frame member
  rw [← tokens frame member]
  exact Memory.readLittle_congr _ _ _ _ (fun i bound => same frame member i bound)

theorem TokensAt.suffix {memory : Memory} {frames rest : List ReturnFrame} (tokens : TokensAt memory frames)
    (suffix : rest <:+ frames) : TokensAt memory rest :=
  fun frame member => tokens frame (suffix.subset member)

/-- A row whose writes miss every active return slot keeps the tokens. -/
theorem TokensAt.exec {frames : List ReturnFrame} {o : Op} {args : List Arg} {core core₁ : Core}
    {flags flags₁ : ByteEval.Flags} (tokens : TokensAt core.memory frames)
    (h : o.exec args core flags = .ok (core₁, flags₁))
    (disjoint : ∀ access ∈ o.writes args core, FramesDisjoint frames access.address access.bytes) :
    TokensAt core₁.memory frames :=
  tokens.bytes fun frame member i bound => exec_bytes_outside h fun access accessMember j jBound =>
    disjoint access accessMember frame member i bound j jBound

end Compilatrix.X86.Layout.Proof
