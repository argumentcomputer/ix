import IxCC.X86.Layout.Tunnel
import IxCC.X86.SafeStepsObject

/-!
# Tunnelling is a simulation (layout step 1 of 3)

`tunnel` redirects each jump and branch target to the end of the chain of
empty jump blocks it starts (`chase`). It keeps every block, every
instruction, the entry and every call and tail-call target, so a typed run
of the tunnelled program is the original run with the empty jumps it
traverses left out:

- `tunnel_wellFormed`: tunnelling keeps a program well formed (a chased
  target is valid, since it is reached through valid jump targets);
- `TRel k m m'`: the tunnelled machine is the original one, except that
  where the original sits at the head of an empty-jump chain of length `k`,
  the tunnelled one is already at its end (`k = 0` is equality);
- `tunnel_safeSteps`: a `Stream.SafeSteps` run of the original from related
  machines is matched by a `SafeSteps` run of the tunnelled program with the
  same masks, ending in related machines, in at most as many steps and at
  least `1/(blocks + 1)` as many (each tunnelled step stands for itself and
  at most `blocks` skipped empty jumps);
- `tunnel_initial`, `TRel.exit`, `TRel.status`: the runs start from the
  same initial machine, and an `Exit` or a status transfers.

The designs are `CompCert/backend/Tunneling.v` and
`jasmin/proofs/compiler/tunneling.v` (a measured simulation).
-/

namespace IxCC.X86.Layout.Proof

open IxCC.X86
open IxCC.X86.Stream

/-! ## Well-formed programs, block by block -/

/-- What `Program.wellFormed` asks of each block. -/
def BlockOk (p : Program) (b : Block) : Prop :=
  b.offsetsFit = true ∧ b.targetsValid p = true ∧ b.instructionsValid = true ∧ b.terminator.wellFormed = true

theorem wellFormed_iff (p : Program) :
    p.wellFormed = true ↔
      p.blocks.size ≠ 0 ∧ p.blocks.size < 2 ^ 32 ∧ p.hasBlock p.entry = true ∧ ∀ b ∈ p.blocks, BlockOk p b := by
  simp only [Program.wellFormed, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, Array.all_eq_true_iff_forall_mem, BlockOk]
  constructor
  · rintro ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩
    refine ⟨?_, h₂, h₃, fun b hb => ?_⟩
    · simpa using h₁
    · obtain ⟨⟨⟨a, b'⟩, c⟩, d⟩ := h₄ b hb
      exact ⟨a, b', c, d⟩
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    refine ⟨⟨⟨by simpa using h₁, h₂⟩, h₃⟩, fun b hb => ?_⟩
    obtain ⟨a, b', c, d⟩ := h₄ b hb
    exact ⟨⟨⟨a, b'⟩, c⟩, d⟩

theorem wellFormed_block {p : Program} (wf : p.wellFormed = true) {i : Nat} {b : Block}
    (found : p.blocks[i]? = some b) : BlockOk p b :=
  ((wellFormed_iff p).1 wf).2.2.2 b (Array.mem_of_getElem? found)

theorem hasBlock_iff {p : Program} {t : BlockId} : p.hasBlock t = true ↔ t.toNat < p.blocks.size := by
  simp [Program.hasBlock]

/-- The targets of a jump terminator of a well-formed program are blocks. -/
theorem jump_valid {p : Program} (wf : p.wellFormed = true) {i : Nat} {b : Block} {u : BlockId}
    (found : p.blocks[i]? = some b) (jumps : b.terminator = .jump u) : p.hasBlock u = true := by
  have := (wellFormed_block wf found).2.1
  simp only [Block.targetsValid, Bool.and_eq_true, jumps, Terminator.targetsValid] at this
  exact this.2

/-! ## Chains with lengths -/

/-- `u` is reached from `t` by exactly `n` empty jump blocks. -/
inductive ChainN (m : NatMap Block) : Nat → BlockId → BlockId → Prop where
  | refl (t : BlockId) : ChainN m 0 t t
  | step {n : Nat} {t u v : BlockId} {b : Block} (found : m.get? t.toNat = some b)
      (empty : emptyJump? b = some u) (rest : ChainN m n u v) : ChainN m (n + 1) t v

theorem ChainN.zero {m : NatMap Block} {t u : BlockId} (h : ChainN m 0 t u) : t = u := by
  cases h
  rfl

theorem ChainN.chainTo {m : NatMap Block} {n : Nat} {t u : BlockId} (h : ChainN m n t u) : ChainTo m t u := by
  induction h with
  | refl t => exact .refl t
  | step found empty _ ih => exact .step found empty ih

/-- `chase` stops after at most `fuel` empty jumps. -/
theorem chase_chainN (m : NatMap Block) : ∀ (fuel : Nat) (t : BlockId), ∃ n ≤ fuel, ChainN m n t (chase m fuel t)
  | 0, t => ⟨0, Nat.le_refl _, by simpa [chase] using ChainN.refl t⟩
  | fuel + 1, t => by
      simp only [chase]
      cases found : m.get? t.toNat with
      | none => exact ⟨0, Nat.zero_le _, by simpa using ChainN.refl t⟩
      | some b =>
          simp only [Option.bind_some]
          cases empty : emptyJump? b with
          | none => exact ⟨0, Nat.zero_le _, by simpa using ChainN.refl t⟩
          | some u =>
              obtain ⟨n, hn, rest⟩ := chase_chainN m fuel u
              exact ⟨n + 1, by omega, .step found empty rest⟩

/-- A chain from a block of a well-formed program ends at a block. -/
theorem chainTo_valid {p : Program} (wf : p.wellFormed = true) {t u : BlockId}
    (chain : ChainTo (blockMap p) t u) (start : p.hasBlock t = true) : p.hasBlock u = true := by
  induction chain with
  | refl => exact start
  | step found empty _ ih =>
      exact ih (jump_valid wf (blockMap_get found) (emptyJump?_eq empty).2)

theorem chase_valid {p : Program} (wf : p.wellFormed = true) (fuel : Nat) {t : BlockId}
    (start : p.hasBlock t = true) : p.hasBlock (chase (blockMap p) fuel t) = true :=
  chainTo_valid wf (chase_chain _ fuel t) start

/-! ## The tunnelled program -/

/-- A block of the tunnelled program. -/
def tunnelBlock (p : Program) (b : Block) : Block :=
  { b with terminator := tunnelTerminator (blockMap p) p.blocks.size b.terminator }

theorem tunnel_entry (p : Program) : (tunnel p).entry = p.entry := rfl

theorem tunnel_size (p : Program) : (tunnel p).blocks.size = p.blocks.size := by
  simp [tunnel]

theorem tunnel_get (p : Program) (i : Nat) : (tunnel p).blocks[i]? = (p.blocks[i]?).map (tunnelBlock p) := by
  simp [tunnel]
  rfl

theorem tunnel_hasBlock (p : Program) (t : BlockId) : (tunnel p).hasBlock t = p.hasBlock t := by
  simp [Program.hasBlock, tunnel_size]

theorem instr_targetsValid_congr {p q : Program} (h : ∀ t, q.hasBlock t = p.hasBlock t) (i : Instr) :
    i.targetsValid q = i.targetsValid p := by
  cases i <;> simp [Instr.targetsValid, h]

/-- Tunnelling keeps a program well formed. -/
theorem tunnel_wellFormed {p : Program} (wf : p.wellFormed = true) : (tunnel p).wellFormed = true := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := (wellFormed_iff p).1 wf
  refine (wellFormed_iff _).2 ⟨by rwa [tunnel_size], by rwa [tunnel_size], ?_, ?_⟩
  · rwa [tunnel_hasBlock, tunnel_entry]
  · intro b' hb'
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hb'
    have found' : (tunnel p).blocks[i]? = some (tunnel p).blocks[i] := Array.getElem?_eq_getElem hi
    rw [tunnel_get] at found'
    cases found : p.blocks[i]? with
    | none => simp [found] at found'
    | some b =>
      simp only [found, Option.map_some, Option.some.injEq] at found'
      rw [← found']
      obtain ⟨o₁, o₂, o₃, o₄⟩ := wellFormed_block wf found
      have hasEq := tunnel_hasBlock p
      refine ⟨o₁, ?_, o₃, ?_⟩
      · simp only [Block.targetsValid, tunnelBlock, Bool.and_eq_true] at o₂ ⊢
        refine ⟨?_, ?_⟩
        · rw [Array.all_eq_true_iff_forall_mem] at o₂ ⊢
          intro x hx
          rw [instr_targetsValid_congr hasEq]
          exact o₂.1 x hx
        · have term := o₂.2
          cases ht : b.terminator <;>
            simp only [ht, tunnelTerminator, Terminator.targetsValid, hasEq, Bool.and_eq_true] at term ⊢
          · exact chase_valid wf _ term
          · exact ⟨chase_valid wf _ term.1, chase_valid wf _ term.2⟩
          · exact term
      · simp only [tunnelBlock]
        cases ht : b.terminator <;> simp only [ht, tunnelTerminator] at o₄ ⊢ <;> first | exact o₄ | rfl

/-- The tunnelled program as a checked program. -/
def tunnelChecked (c : Checked) : Checked := ⟨tunnel c.program, tunnel_wellFormed c.valid⟩

/-! ## Steps -/

theorem goto_congr {c c' : Checked} (h : ∀ t, c'.program.hasBlock t = c.program.hasBlock t) (m : Machine)
    (t : BlockId) : m.goto c' t = m.goto c t := by
  simp [Machine.goto, h]

theorem executeInstr_congr {c c' : Checked} (h : ∀ t, c'.program.hasBlock t = c.program.hasBlock t)
    (runtime : Runtime) (i : Instr) (m : Machine) :
    executeInstr runtime c' i m = executeInstr runtime c i m := by
  cases i <;> simp [executeInstr, h]

theorem executeTerminator_congr {c c' : Checked} (h : ∀ t, c'.program.hasBlock t = c.program.hasBlock t)
    (term : Terminator) (m : Machine) : executeTerminator c' term m = executeTerminator c term m := by
  cases term <;> simp [executeTerminator, goto_congr h]

theorem goto_valid {c : Checked} {t : BlockId} (valid : c.program.hasBlock t = true) (m : Machine) :
    m.goto c t = { m with pc := ⟨t, 0⟩ } := by
  simp [Machine.goto, valid]

/-- The tunnelled machine is the original one, except that where the
original sits at the head of an empty-jump chain of length `k`, the
tunnelled one is already at its end. -/
structure TRel (p : Program) (k : Nat) (m m' : Machine) : Prop where
  core : m'.core = m.core
  returns : m'.returns = m.returns
  status : m'.status = m.status
  offset : m'.pc.offset = m.pc.offset
  chain : ChainN (blockMap p) k m.pc.block m'.pc.block
  head : k ≠ 0 → m.pc.offset = 0 ∧ m.status = .running

theorem TRel.eq {p : Program} {m m' : Machine} (h : TRel p 0 m m') : m' = m := by
  have hb := h.chain.zero
  obtain ⟨core, pc, returns, status⟩ := m
  obtain ⟨core', pc', returns', status'⟩ := m'
  obtain ⟨block, offset⟩ := pc
  obtain ⟨block', offset'⟩ := pc'
  have := h.core
  have := h.returns
  have := h.status
  have := h.offset
  simp_all

theorem TRel.refl (p : Program) (m : Machine) : TRel p 0 m m :=
  ⟨rfl, rfl, rfl, rfl, .refl _, fun h => absurd rfl h⟩

/-- A step of the tunnelled program from the original's machine: the same
machine, except that a jump or branch lands at the end of the chain its
original target starts. -/
theorem tunnel_step {runtime : Runtime} {c c' : Checked} (hc : c'.program = tunnel c.program)
    (m : Machine) : ∃ k ≤ c.program.blocks.size, TRel c.program k (step runtime c m) (step runtime c' m) := by
  have has : ∀ t, c'.program.hasBlock t = c.program.hasBlock t := fun t => by rw [hc, tunnel_hasBlock]
  cases hs : m.status with
  | halted v =>
      rw [step_of_not_running _ _ _ (by simp [hs]), step_of_not_running _ _ _ (by simp [hs])]
      exact ⟨0, Nat.zero_le _, .refl _ _⟩
  | trapped f =>
      rw [step_of_not_running _ _ _ (by simp [hs]), step_of_not_running _ _ _ (by simp [hs])]
      exact ⟨0, Nat.zero_le _, .refl _ _⟩
  | running =>
  have get' : c'.program.blocks[m.pc.block.toNat]? = (c.program.blocks[m.pc.block.toNat]?).map
      (tunnelBlock c.program) := by rw [hc, tunnel_get]
  cases found : c.program.blocks[m.pc.block.toNat]? with
  | none =>
      have e : step runtime c' m = step runtime c m := by
        simp [step, hs, found, get']
      exact ⟨0, Nat.zero_le _, e ▸ .refl _ _⟩
  | some b =>
  simp only [found, Option.map_some] at get'
  cases hi : b.instructions[m.pc.offset.toNat]? with
  | some i =>
      have e : step runtime c' m = step runtime c m := by
        simp [step, hs, found, get', tunnelBlock, hi, executeInstr_congr has]
      exact ⟨0, Nat.zero_le _, e ▸ .refl _ _⟩
  | none =>
  by_cases pos : m.pc.offset.toNat = b.instructions.size
  · have s₁ : step runtime c m = executeTerminator c b.terminator m := by
      simp [step, hs, found, pos]
    have s₂ : step runtime c' m = executeTerminator c' (tunnelTerminator (blockMap c.program)
        c.program.blocks.size b.terminator) m := by
      simp [step, hs, get', tunnelBlock, pos]
    rw [s₁, s₂]
    have tv := (wellFormed_block c.valid found).2.1
    simp only [Block.targetsValid, Bool.and_eq_true] at tv
    have tv := tv.2
    cases ht : b.terminator with
    | jump t =>
        simp only [ht, Terminator.targetsValid] at tv
        obtain ⟨k, hk, chain⟩ := chase_chainN (blockMap c.program) c.program.blocks.size t
        refine ⟨k, hk, ?_⟩
        simp only [tunnelTerminator, executeTerminator]
        rw [goto_valid tv, goto_valid (by rw [has]; exact chase_valid c.valid _ tv)]
        exact ⟨rfl, rfl, rfl, rfl, chain, fun _ => ⟨rfl, hs⟩⟩
    | branch producer args cond yes no reach =>
        simp only [ht, Terminator.targetsValid, Bool.and_eq_true] at tv
        simp only [tunnelTerminator, executeTerminator]
        cases hp : producer.exec args m.core {} with
        | error e => exact ⟨0, Nat.zero_le _, .refl _ _⟩
        | ok r =>
          obtain ⟨core, flags⟩ := r
          simp only
          cases htest : flags.test cond with
          | none => exact ⟨0, Nat.zero_le _, .refl _ _⟩
          | some taken =>
            simp only
            cases taken
            · obtain ⟨k, hk, chain⟩ := chase_chainN (blockMap c.program) c.program.blocks.size no
              refine ⟨k, hk, ?_⟩
              simp only [Bool.false_eq_true, ite_false]
              rw [goto_valid tv.2, goto_valid (by rw [has]; exact chase_valid c.valid _ tv.2)]
              exact ⟨rfl, rfl, rfl, rfl, chain, fun _ => ⟨rfl, hs⟩⟩
            · obtain ⟨k, hk, chain⟩ := chase_chainN (blockMap c.program) c.program.blocks.size yes
              refine ⟨k, hk, ?_⟩
              simp only [ite_true]
              rw [goto_valid tv.1, goto_valid (by rw [has]; exact chase_valid c.valid _ tv.1)]
              exact ⟨rfl, rfl, rfl, rfl, chain, fun _ => ⟨rfl, hs⟩⟩
    | tailCall t =>
        simp only [tunnelTerminator]
        rw [executeTerminator_congr has]
        exact ⟨0, Nat.zero_le _, .refl _ _⟩
    | ret =>
        simp only [tunnelTerminator]
        rw [executeTerminator_congr has]
        exact ⟨0, Nat.zero_le _, .refl _ _⟩
  · have e : step runtime c' m = step runtime c m := by
      simp [step, hs, found, get', tunnelBlock, hi, pos]
    exact ⟨0, Nat.zero_le _, e ▸ .refl _ _⟩

/-! ## Safety and masks -/

theorem tunnel_safeAt {p : Program} (holes : Holes) (m : Machine) :
    SafeAt (tunnel p) holes m ↔ SafeAt p holes m := by
  unfold SafeAt
  rw [tunnel_get]
  cases p.blocks[m.pc.block.toNat]? with
  | none => simp
  | some b =>
      simp only [Option.map_some, tunnelBlock]
      cases b.instructions[m.pc.offset.toNat]? with
      | some i => cases i <;> rfl
      | none => cases b.terminator <;> rfl

theorem tunnel_holeStep {p : Program} (holes : Holes) (m : Machine) :
    holeStep (tunnel p) m holes = holeStep p m holes := by
  unfold holeStep
  rw [tunnel_get]
  cases p.blocks[m.pc.block.toNat]? with
  | none => rfl
  | some b =>
      simp only [Option.map_some, tunnelBlock]
      cases b.instructions[m.pc.offset.toNat]? with
      | some i => cases i <;> rfl
      | none => cases b.terminator <;> rfl

/-- At the head of a nonempty chain, the original takes the empty jump; the
mask does not change. -/
theorem chain_head_step {runtime : Runtime} {c : Checked} {k : Nat} {m m' : Machine}
    (rel : TRel c.program (k + 1) m m') :
    ∃ u, step runtime c m = { m with pc := ⟨u, 0⟩ } ∧ (∀ holes, holeStep c.program m holes = holes) ∧
      TRel c.program k { m with pc := ⟨u, 0⟩ } m' := by
  obtain ⟨offset, running⟩ := rel.head (by omega)
  have chain := rel.chain
  cases chain with
  | @step _ _ u _ b found empty rest =>
    have inProgram := blockMap_get found
    obtain ⟨noInstr, jumps⟩ := emptyJump?_eq empty
    have valid := jump_valid c.valid inProgram jumps
    have offset0 : m.pc.offset.toNat = 0 := by simp [offset]
    refine ⟨u, step_emptyJump runtime c m running inProgram offset empty valid, ?_, ?_⟩
    · intro holes
      simp [holeStep, inProgram, offset0, noInstr, jumps, terminatorHoles]
    · refine ⟨rel.core, rel.returns, rel.status, ?_, rest, fun _ => ⟨rfl, running⟩⟩
      rw [rel.offset, offset]

/-! ## Transport -/

/-- A `SafeSteps` run of the original program from related machines is
matched by a `SafeSteps` run of the tunnelled program with the same masks,
ending in related machines; the tunnelled run takes at most as many steps,
and each of its steps stands for at most `blocks + 1` original ones. -/
theorem tunnel_safeSteps {runtime : Runtime} {c c' : Checked} (hc : c'.program = tunnel c.program)
    {n : Nat} {holes holes' : Holes} {m m₁ : Machine} (steps : SafeSteps runtime c n holes m holes' m₁) :
    ∀ {k : Nat} {m' : Machine}, TRel c.program k m m' →
      ∃ n' k₁ m₁', SafeSteps runtime c' n' holes m' holes' m₁' ∧ TRel c.program k₁ m₁ m₁' ∧ n' ≤ n ∧
        n + k₁ ≤ (c.program.blocks.size + 1) * n' + k := by
  induction steps with
  | refl holes m =>
      intro k m' rel
      exact ⟨0, k, m', .refl _ _, rel, Nat.le_refl _, by omega⟩
  | @cons before middle after holes finalHoles count safe first rest ih =>
      intro k m' rel
      cases k with
      | zero =>
          rw [rel.eq]
          obtain ⟨k₂, hk₂, rel₂⟩ := tunnel_step (runtime := runtime) hc before
          rw [first] at rel₂
          obtain ⟨n'', k₁, m₁', steps', rel₁, hle, hbound⟩ := ih rel₂
          refine ⟨n'' + 1, k₁, m₁', ?_, rel₁, by omega, ?_⟩
          · refine .cons ((by rw [hc, tunnel_safeAt]; exact safe) : SafeAt c'.program holes before) rfl ?_
            rwa [hc, tunnel_holeStep]
          · have : (c.program.blocks.size + 1) * (n'' + 1) = (c.program.blocks.size + 1) * n'' +
                (c.program.blocks.size + 1) := Nat.mul_succ _ _
            omega
      | succ j =>
          obtain ⟨u, stepped, holesSame, rel₂⟩ := chain_head_step (runtime := runtime) rel
          rw [first] at stepped
          subst stepped
          obtain ⟨n'', k₁, m₁', steps', rel₁, hle, hbound⟩ := ih rel₂
          rw [holesSame] at steps'
          exact ⟨n'', k₁, m₁', steps', rel₁, by omega, by omega⟩

/-- The tunnelled program starts from the original's initial machine. -/
theorem tunnel_initial {c c' : Checked} (hc : c'.program = tunnel c.program) (core : Core) :
    Machine.initial c' core = Machine.initial c core := by
  simp [Machine.initial, hc, tunnel_entry]

/-- A whole run: from the initial machine, the tunnelled program takes at
most as many steps, and at least the original count divided by
`blocks + 1`. -/
theorem tunnel_run {runtime : Runtime} {c c' : Checked} (hc : c'.program = tunnel c.program)
    {n : Nat} {holes holes' : Holes} {core : Core} {m₁ : Machine}
    (steps : SafeSteps runtime c n holes (Machine.initial c core) holes' m₁) :
    ∃ n' k₁ m₁', SafeSteps runtime c' n' holes (Machine.initial c' core) holes' m₁' ∧
      TRel c.program k₁ m₁ m₁' ∧ n' ≤ n ∧ n ≤ (c.program.blocks.size + 1) * n' := by
  obtain ⟨n', k₁, m₁', steps', rel, hle, hbound⟩ := tunnel_safeSteps hc steps (.refl _ _)
  exact ⟨n', k₁, m₁', by rwa [tunnel_initial hc], rel, hle, by omega⟩

/-! ## What transfers -/

theorem TRel.exit {p : Program} {k : Nat} {m m' : Machine} (rel : TRel p k m m') {core₀ : Core}
    {retAddr st val : Word} (exit : Exit core₀ retAddr st val m) : Exit core₀ retAddr st val m' := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := exit
  exact ⟨by rw [rel.status]; exact h₁, by rw [rel.core]; exact h₂, by rw [rel.core]; exact h₃,
    by rw [rel.core]; exact h₄, by rw [rel.core]; exact h₅⟩

theorem TRel.running {p : Program} {k : Nat} {m m' : Machine} (rel : TRel p k m m')
    (running : m.status = .running) : m'.status = .running := by
  rw [rel.status, running]

end IxCC.X86.Layout.Proof
