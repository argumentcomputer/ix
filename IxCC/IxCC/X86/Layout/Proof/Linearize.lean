import IxCC.X86.Layout.Linearize
import IxCC.X86.Layout.Proof.Order
import IxCC.X86.Layout.Proof.Rows
import IxCC.X86.Layout.Proof.Tunnel

/-!
# Linearisation is a simulation (layout step 3 of 3)

`linearize p order` renumbers the blocks by their position in `order`,
maps call, jump, branch and tail-call targets and the entry through the
renumbering, inverts a branch whose true target is next and marks a false
edge to the next block `fall`. Given an order `Order.check` accepts (so the
flattened order is duplicate free, in range, contains the entry and is
closed under block targets), the laid-out program runs in lock step with
the original:

- `LRel`: equal registers and permissions; bytes equal outside the
  return-slot mask (until a trap); the PC's block renumbered, its offset
  kept; the return frames related one to one (renumbered continuations,
  the same return slots and callee-saved snapshots); each active frame of
  the laid-out machine holding its own continuation token in its slot
  (`TokensAt`); and statuses related (equal results, traps to traps);
- `lin_step`: from related machines, a step that is safe at the original is
  safe at the laid-out machine, advances the mask alike, and leads to
  related machines;
- `lin_safeSteps`, `linearize_run`: `Stream.SafeSteps` runs transfer with
  the same step count and masks, from the two initial machines;
- `LRel.exit`, `LRel.running`: an `Exit` (given that the 8 bytes at the
  final `rsp` are not masked) and a running status transfer.

Inversion uses `executeTerminator_negate` and the `fall` mark
`executeTerminator_reach`. Return slots hold different tokens on the two
machines (`PC.encode` of renumbered PCs), which is why the masks of E2
(`holeStep` adds each call's slot) appear here: `SafeAt` forbids ordinary
reads of masked bytes, and at `ret` each machine reads its own token.
-/

namespace IxCC.X86.Layout.Proof

open IxCC.X86
open IxCC.X86.Stream

/-! ## The renumbering and the laid-out blocks -/

/-- The position map `linearize` builds. -/
def posOf (order : List Nat) : NatMap Nat := order.zipIdx.foldl (fun acc (b, i) => acc.insert b i) {}

/-- A block's new number. -/
def renum (order : List Nat) (t : BlockId) : BlockId := UInt32.ofNat (((posOf order).get? t.toNat).getD t.toNat)

def linInstr (rn : BlockId → BlockId) : Instr → Instr
  | .call t => .call (rn t)
  | i => i

def linTerm (rn : BlockId → BlockId) (i : Nat) : Terminator → Terminator
  | .jump t => .jump (rn t)
  | .tailCall t => .tailCall (rn t)
  | .ret => .ret
  | .branch producer args c yes no _ =>
      let yes := rn yes
      let no := rn no
      if yes.toNat == i + 1 && no.toNat != i + 1 then .branch producer args c.negate no yes .fall
      else if no.toNat == i + 1 then .branch producer args c yes no .fall
      else .branch producer args c yes no

/-- The laid-out copy of block `blk` at position `i`. -/
def linBlk (order : List Nat) (i : Nat) (blk : Block) : Block :=
  { instructions := (blk.instructions.toList.map (linInstr (renum order))).toArray
    terminator := linTerm (renum order) i blk.terminator }

/-- The laid-out program. -/
def linProgram (p : Program) (order : List Nat) : Program :=
  { blocks := (order.zipIdx.map fun (b, i) => linBlk order i (((blockMap p).get? b).getD default)).toArray
    entry := renum order p.entry }

theorem linearize_eq (p : Program) (order : List Nat) : linearize p order = (linProgram p order, posOf order) := rfl

theorem run_eq {p : Program} {s : Shape} {o : Order} {q : Program} {pos : NatMap Nat}
    (h : Layout.run p s o = .ok (q, pos)) : Order.check p s o = true ∧ q = linProgram p o.flatten := by
  unfold Layout.run at h
  split at h
  · rename_i hc
    simp only [pure, Except.pure, Except.ok.injEq, linearize_eq, Prod.mk.injEq] at h
    exact ⟨hc, h.1.symm⟩
  · cases h

/-- The block map holds every block of the program at its index. -/
theorem blockMap_get_complete (p : Program) (i : Nat) : (blockMap p).get? i = p.blocks[i]? := by
  have key : ∀ (l : List Block) (off : Nat) (acc : NatMap Block) (k : Nat),
      ((l.zipIdx off).foldl (fun m (x : Block × Nat) => m.insert x.2 x.1) acc).get? k =
        if off ≤ k ∧ k < off + l.length then l[k - off]? else acc.get? k := by
    intro l
    induction l with
    | nil =>
        intro off acc k
        rw [ite_eq_right (by simp)]
        rfl
    | cons b l ih =>
        intro off acc k
        rw [List.zipIdx_cons, List.foldl_cons, ih]
        simp only [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert, List.length_cons]
        by_cases hk : off = k
        · subst hk
          rw [ite_eq_right (show ¬(off + 1 ≤ off ∧ off < off + 1 + l.length) by omega),
            ite_eq_left (show compare off off = .eq by simp),
            ite_eq_left (show off ≤ off ∧ off < off + (l.length + 1) by omega)]
          simp
        · have hne : ¬ compare off k = .eq := by simpa [Nat.compare_eq_eq] using hk
          simp only [hne, ite_false]
          by_cases hr : off + 1 ≤ k ∧ k < off + 1 + l.length
          · rw [ite_eq_left hr, ite_eq_left (by omega)]
            have e : k - off = (k - (off + 1)) + 1 := by omega
            rw [e, List.getElem?_cons_succ]
          · rw [ite_eq_right hr, ite_eq_right (by omega)]
  have := key p.blocks.toList 0 {} i
  simp only [Nat.zero_le, true_and, Nat.zero_add, Nat.sub_zero, Array.length_toList,
    Array.getElem?_toList] at this
  unfold blockMap
  rw [this]
  split
  · rfl
  · rename_i h
    rw [Array.getElem?_eq_none (by omega : p.blocks.size ≤ i)]
    simp

theorem posOf_get {order : List Nat} (nodup : order.Nodup) {i b : Nat} (h : order[i]? = some b) :
    (posOf order).get? b = some i := by
  have key : ∀ (l : List Nat) (off : Nat) (acc : NatMap Nat), l.Nodup →
      (∀ j c, l[j]? = some c → ((l.zipIdx off).foldl (fun m (x : Nat × Nat) => m.insert x.1 x.2) acc).get? c =
        some (off + j)) ∧
      (∀ c, c ∉ l → ((l.zipIdx off).foldl (fun m (x : Nat × Nat) => m.insert x.1 x.2) acc).get? c = acc.get? c) := by
    intro l
    induction l with
    | nil => intro off acc _; simp
    | cons x l ih =>
        intro off acc nd
        rw [List.nodup_cons] at nd
        obtain ⟨ih₁, ih₂⟩ := ih (off + 1) (acc.insert x off) nd.2
        rw [List.zipIdx_cons, List.foldl_cons]
        refine ⟨?_, ?_⟩
        · intro j c hj
          cases j with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
              subst hj
              rw [ih₂ x nd.1, Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert]
              simp
          | succ j =>
              rw [List.getElem?_cons_succ] at hj
              rw [ih₁ j c hj]
              congr 1
              omega
        · intro c hc
          rw [List.mem_cons, not_or] at hc
          rw [ih₂ c hc.2, Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert, ← Std.TreeMap.get?_eq_getElem?]
          have : ¬ compare x c = .eq := by simpa [Nat.compare_eq_eq] using Ne.symm hc.1
          simp [this]
  have := (key order 0 {} nodup).1 i b h
  simpa [posOf] using this

/-! ## The setting -/

/-- What the linearisation proof assumes of the order and the programs:
what `Order.check` and the laid-out program's validity give. -/
structure Setup (p q : Program) (order : List Nat) : Prop where
  wf : p.wellFormed = true
  nodup : order.Nodup
  inRange : ∀ b ∈ order, b < p.blocks.size
  closed : ∀ b ∈ order, ∀ blk, p.blocks[b]? = some blk → ∀ t ∈ blk.targets, t.toNat ∈ order
  program : q = linProgram p order
  small : order.length < 2 ^ 32

variable {p q : Program} {order : List Nat}

theorem Setup.index (setup : Setup p q order) {t : BlockId} (placed : t.toNat ∈ order) :
    ∃ i, order[i]? = some t.toNat ∧ (renum order t).toNat = i ∧ i < order.length := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 placed
  have bound : i < order.length := (List.getElem?_eq_some_iff.1 hi).1
  refine ⟨i, hi, ?_, bound⟩
  simp only [renum, posOf_get setup.nodup hi, Option.getD_some, UInt32.toNat_ofNat']
  have := setup.small
  omega

/-- A placed block and its laid-out copy. -/
theorem Setup.block (setup : Setup p q order) {t : BlockId} (placed : t.toNat ∈ order) :
    ∃ blk i, p.blocks[t.toNat]? = some blk ∧ (renum order t).toNat = i ∧
      q.blocks[(renum order t).toNat]? = some (linBlk order i blk) := by
  obtain ⟨i, hi, hrn, bound⟩ := setup.index placed
  have inRange := setup.inRange _ placed
  refine ⟨p.blocks[t.toNat], i, Array.getElem?_eq_getElem inRange, hrn, ?_⟩
  rw [setup.program, hrn]
  simp only [linProgram, List.getElem?_toArray, List.getElem?_map, List.getElem?_zipIdx, hi, Option.map_some,
    Nat.zero_add, blockMap_get_complete, Array.getElem?_eq_getElem inRange, Option.getD_some]

theorem Setup.hasBlock (setup : Setup p q order) {t : BlockId} (placed : t.toNat ∈ order) :
    q.hasBlock (renum order t) = true := by
  obtain ⟨blk, i, -, -, found⟩ := setup.block placed
  exact hasBlock_iff.2 (Array.getElem?_eq_some_iff.1 found).1

theorem Setup.hasBlock_source (setup : Setup p q order) {t : BlockId} (placed : t.toNat ∈ order) :
    p.hasBlock t = true :=
  hasBlock_iff.2 (setup.inRange _ placed)

theorem Setup.target (setup : Setup p q order) {b : BlockId} {blk : Block} (placed : b.toNat ∈ order)
    (found : p.blocks[b.toNat]? = some blk) {t : BlockId} (ht : t ∈ blk.targets) : t.toNat ∈ order :=
  setup.closed _ placed blk found t ht

theorem linBlk_instr (order : List Nat) (i : Nat) (blk : Block) (j : Nat) :
    (linBlk order i blk).instructions[j]? = (blk.instructions[j]?).map (linInstr (renum order)) := by
  simp [linBlk]

theorem linBlk_size (order : List Nat) (i : Nat) (blk : Block) :
    (linBlk order i blk).instructions.size = blk.instructions.size := by
  simp [linBlk]

theorem linBlk_terminator (order : List Nat) (i : Nat) (blk : Block) :
    (linBlk order i blk).terminator = linTerm (renum order) i blk.terminator := rfl

theorem call_target {blk : Block} {j : Nat} {t : BlockId} (h : blk.instructions[j]? = some (.call t)) :
    t ∈ blk.targets := by
  simp only [Block.targets, List.mem_append, List.mem_filterMap]
  exact .inl ⟨.call t, Array.mem_toList_iff.2 (Array.mem_of_getElem? h), rfl⟩

/-! ## Frames and statuses -/

structure FrameRel (order : List Nat) (f f' : ReturnFrame) : Prop where
  continuation : f'.continuation = ⟨renum order f.continuation.block, f.continuation.offset⟩
  placed : f.continuation.block.toNat ∈ order
  slot : f'.returnSlot = f.returnSlot
  saved : f'.calleeSaved = f.calleeSaved

inductive FramesRel (order : List Nat) : List ReturnFrame → List ReturnFrame → Prop where
  | nil : FramesRel order [] []
  | cons {f f' : ReturnFrame} {fs fs' : List ReturnFrame} (head : FrameRel order f f')
      (tail : FramesRel order fs fs') : FramesRel order (f :: fs) (f' :: fs')

theorem FramesRel.slots {fs fs' : List ReturnFrame} (h : FramesRel order fs fs') :
    fs'.map (·.returnSlot) = fs.map (·.returnSlot) := by
  induction h with
  | nil => rfl
  | cons head _ ih => simp [head.slot, ih]

theorem FramesRel.drop {fs fs' : List ReturnFrame} (h : FramesRel order fs fs') (n : Nat) :
    FramesRel order (fs.drop n) (fs'.drop n) := by
  induction h generalizing n with
  | nil => simpa using FramesRel.nil
  | cons head tail ih =>
      cases n with
      | zero => exact .cons head tail
      | succ n => simpa using ih n

theorem FramesRel.findIdx {fs fs' : List ReturnFrame} (h : FramesRel order fs fs') (sp : Word) :
    fs'.findIdx? (·.returnSlot + 8 == sp) = fs.findIdx? (·.returnSlot + 8 == sp) := by
  induction h with
  | nil => rfl
  | cons head _ ih => simp [List.findIdx?_cons, head.slot, ih]

theorem FramesRel.cutAt {fs fs' : List ReturnFrame} (h : FramesRel order fs fs') (sp : Word) :
    (cutAt sp fs = none ∧ cutAt sp fs' = none) ∨
      ∃ rest rest', cutAt sp fs = some rest ∧ cutAt sp fs' = some rest' ∧ FramesRel order rest rest' := by
  cases h with
  | nil => exact .inr ⟨[], [], rfl, rfl, .nil⟩
  | @cons f f' fs fs' head tail =>
      have hf := (FramesRel.cons head tail).findIdx sp
      simp only [X86.cutAt]
      rw [hf]
      cases hidx : List.findIdx? (fun x : ReturnFrame => x.returnSlot + 8 == sp) (f :: fs) with
      | none => exact .inl ⟨rfl, rfl⟩
      | some i => exact .inr ⟨_, _, rfl, rfl, (FramesRel.cons head tail).drop (i + 1)⟩

theorem FramesRel.disjoint {fs fs' : List ReturnFrame} (h : FramesRel order fs fs') {address : Word}
    {count : Nat} (d : FramesDisjoint fs address count) : FramesDisjoint fs' address count := by
  intro f' member i hi j hj
  have hm : f'.returnSlot ∈ fs'.map (·.returnSlot) := List.mem_map_of_mem member
  rw [h.slots] at hm
  obtain ⟨f, fm, hs⟩ := List.mem_map.1 hm
  rw [← hs]
  exact d f fm i hi j hj

theorem FramesRel.nil_iff {fs fs' : List ReturnFrame} (h : FramesRel order fs fs') : fs = [] ↔ fs' = [] := by
  cases h <;> simp

theorem FramesRel.cons_inv {f : ReturnFrame} {fs fs' : List ReturnFrame} (h : FramesRel order (f :: fs) fs') :
    ∃ f' rest', fs' = f' :: rest' ∧ FrameRel order f f' ∧ FramesRel order fs rest' := by
  cases h with
  | cons head tail => exact ⟨_, _, rfl, head, tail⟩

theorem FramesRel.nil_inv {fs' : List ReturnFrame} (h : FramesRel order [] fs') : fs' = [] := by
  cases h
  rfl

/-- Statuses: the same result, traps to traps. -/
def StatusRel : Status → Status → Prop
  | .running, .running => True
  | .halted v, .halted v' => v' = v
  | .trapped _, .trapped _ => True
  | _, _ => False

/-! ## The machine relation -/

/-- The laid-out machine beside the original under mask `holes`. -/
structure LRel (p : Program) (order : List Nat) (holes : Holes) (m m' : Machine) : Prop where
  registers : m'.core.registers = m.core.registers
  readable : m'.core.memory.readable = m.core.memory.readable
  writable : m'.core.memory.writable = m.core.memory.writable
  bytes : (∀ f, m.status ≠ .trapped f) → ∀ a, ¬holes a → m'.core.memory.bytes a = m.core.memory.bytes a
  pc : m'.pc = ⟨renum order m.pc.block, m.pc.offset⟩
  placed : m.pc.block.toNat ∈ order
  returns : FramesRel order m.returns m'.returns
  status : StatusRel m.status m'.status
  tokens : TokensAt m'.core.memory m'.returns
  atRet : ∀ v, m.status = .halted v → ∃ blk, p.blocks[m.pc.block.toNat]? = some blk ∧
    m.pc.offset.toNat = blk.instructions.size ∧ blk.terminator = .ret

theorem LRel.memory {holes : Holes} {m m' : Machine} (rel : LRel p order holes m m')
    (notTrapped : ∀ f, m.status ≠ .trapped f) : MemoryRelated holes m.core.memory m'.core.memory :=
  ⟨rel.readable.symm, rel.writable.symm, fun a ha => (rel.bytes notTrapped a ha).symm⟩

theorem LRel.readReg {holes : Holes} {m m' : Machine} (rel : LRel p order holes m m') (r : GPR) :
    m'.core.readReg r = m.core.readReg r := by
  simp [Core.readReg, rel.registers]

theorem LRel.running {holes : Holes} {m m' : Machine} (rel : LRel p order holes m m')
    (running : m.status = .running) : m'.status = .running := by
  have := rel.status
  rw [running] at this
  cases h : m'.status <;> simp_all [StatusRel]

theorem LRel.trapped {holes : Holes} {m m' : Machine} (rel : LRel p order holes m m') {f : Trap}
    (trapped : m.status = .trapped f) : ∃ f', m'.status = .trapped f' := by
  have := rel.status
  rw [trapped] at this
  cases h : m'.status <;> simp_all [StatusRel]

theorem LRel.halted {holes : Holes} {m m' : Machine} (rel : LRel p order holes m m') {v : Word}
    (halted : m.status = .halted v) : m'.status = .halted v := by
  have := rel.status
  rw [halted] at this
  cases h : m'.status <;> simp_all [StatusRel]

theorem slots_eq_of_rel {holes : Holes} {m m' : Machine} (rel : LRel p order holes m m') :
    m'.returns.map (·.returnSlot) = m.returns.map (·.returnSlot) := rel.returns.slots

/-! ## Safety and masks transfer -/

theorem OperationSafe.transfer {holes : Holes} {frames frames' : List ReturnFrame} {op : Decode.Operation}
    {core core' : Core} (safe : OperationSafe holes frames op core) (registers : core'.registers = core.registers)
    (rel : FramesRel order frames frames') : OperationSafe holes frames' op core' := by
  obtain ⟨reads, writes⟩ := safe
  refine ⟨?_, ?_⟩
  · rw [operationReads_registers registers]
    exact reads
  · rw [operationWrites_registers registers]
    exact fun access member => rel.disjoint (writes access member)

theorem nextHoles_registers {holes : Holes} {op : Decode.Operation} {core core' : Core}
    (registers : core'.registers = core.registers) : nextHoles holes op core' = nextHoles holes op core := by
  simp only [nextHoles, operationWrites_registers registers]

theorem calleeSavedSnapshot_registers {core core' : Core} (registers : core'.registers = core.registers) :
    core'.calleeSavedSnapshot = core.calleeSavedSnapshot := by
  simp [Core.calleeSavedSnapshot, Core.readReg, registers]

theorem calleeSavedMatch_registers {core core' : Core} (registers : core'.registers = core.registers)
    (snapshot : Array Word) : core'.calleeSavedMatch snapshot = core.calleeSavedMatch snapshot := by
  simp [Core.calleeSavedMatch, calleeSavedSnapshot_registers registers]

theorem read64?_tokens {memory memory' : Memory} {slot token token' : Word}
    (readable : memory'.readable = memory.readable) (read : memory.read64? slot = .ok token')
    (stored : memory'.read64 slot = token) : memory'.read64? slot = .ok token := by
  simp only [Memory.read64?, Memory.read?] at read ⊢
  rw [readable]
  split at read
  · simp only [ite_true, *]
    exact congrArg Except.ok stored
  · cases read

theorem linTerm_branch (rn : BlockId → BlockId) (i : Nat) (producer : Op) (args : List Arg) (c : Condition)
    (yes no : BlockId) (reach : Reach) :
    ∃ c' yes' no' reach', linTerm rn i (.branch producer args c yes no reach) = .branch producer args c' yes' no' reach' ∧
      ((c' = c ∧ yes' = rn yes ∧ no' = rn no) ∨ (c' = c.negate ∧ yes' = rn no ∧ no' = rn yes)) := by
  simp only [linTerm]
  split
  · exact ⟨_, _, _, _, rfl, .inr ⟨rfl, rfl, rfl⟩⟩
  · split
    · exact ⟨_, _, _, _, rfl, .inl ⟨rfl, rfl, rfl⟩⟩
    · exact ⟨_, _, _, _, rfl, .inl ⟨rfl, rfl, rfl⟩⟩

/-- Safety at the original gives safety at the laid-out machine, and both
masks advance alike. -/
theorem lin_safe {holes : Holes} {m m' : Machine} (setup : Setup p q order) (rel : LRel p order holes m m')
    (safe : SafeAt p holes m) : SafeAt q holes m' ∧ holeStep q m' holes = holeStep p m holes := by
  obtain ⟨blk, i, found, hrn, found'⟩ := setup.block rel.placed
  have regs := rel.registers
  have hpc := rel.pc
  unfold SafeAt at safe ⊢
  unfold holeStep
  rw [hpc] at ⊢
  simp only [found, found'] at safe ⊢
  rw [linBlk_instr]
  cases hi : blk.instructions[m.pc.offset.toNat]? with
  | some ins =>
      simp only [hi] at safe
      simp only [Option.map_some]
      cases ins with
      | op o args =>
          exact ⟨OperationSafe.transfer safe regs rel.returns, nextHoles_registers regs⟩
      | fused producer pargs consumer cargs =>
          exact ⟨⟨OperationSafe.transfer safe.1 regs rel.returns, OperationSafe.transfer safe.2 regs rel.returns⟩,
            nextHoles_registers regs⟩
      | call t =>
          refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
          · rw [rel.readReg]; exact safe.1
          · rw [rel.readReg, rel.writable]; exact safe.2.1
          · rw [rel.readReg]; exact rel.returns.disjoint safe.2.2
          · simp only [linInstr]
            rw [rel.readReg]
      | callRuntime r => exact absurd safe id
      | unwind source =>
          exact ⟨OperationSafe.transfer safe regs rel.returns, nextHoles_registers regs⟩
  | none =>
      simp only [hi] at safe
      simp only [Option.map_none, linBlk_size, linBlk_terminator]
      obtain ⟨position, tsafe⟩ := safe
      refine ⟨⟨position, ?_⟩, ?_⟩
      · cases ht : blk.terminator with
        | jump t => simp [linTerm]
        | tailCall t => simp [linTerm]
        | ret =>
            simp only [ht] at tsafe
            simp only [linTerm]
            cases hr : m.returns with
            | nil =>
                have : m'.returns = [] := rel.returns.nil_iff.1 hr
                simp only [hr] at tsafe
                simp only [this]
                rw [rel.readReg]
                exact tsafe
            | cons f fs =>
                have hrel := rel.returns
                rw [hr] at hrel
                obtain ⟨f', fs', hr', head, -⟩ := hrel.cons_inv
                simp only [hr] at tsafe
                simp only [hr']
                obtain ⟨hsp, hread, hmatch⟩ := tsafe
                have tok := rel.tokens f' (by simp [hr'])
                refine ⟨by rw [rel.readReg, head.slot, hsp], ?_, ?_⟩
                · rw [head.slot] at tok ⊢
                  exact read64?_tokens rel.readable hread tok
                · rw [calleeSavedMatch_registers regs, head.saved]
                  exact hmatch
        | branch producer args c yes no reach =>
            simp only [ht] at tsafe
            obtain ⟨c', yes', no', reach', he, -⟩ := linTerm_branch (renum order) i producer args c yes no reach
            rw [he]
            exact OperationSafe.transfer tsafe regs rel.returns
      · cases ht : blk.terminator with
        | jump t => simp [linTerm, terminatorHoles]
        | tailCall t => simp [linTerm, terminatorHoles]
        | ret => simp [linTerm, terminatorHoles]
        | branch producer args c yes no reach =>
            obtain ⟨c', yes', no', reach', he, -⟩ := linTerm_branch (renum order) i producer args c yes no reach
            rw [he]
            simp only [terminatorHoles]
            exact nextHoles_registers regs

/-! ## Steps -/

theorem PC.next?_rename (f : BlockId → BlockId) (pc : PC) :
    (⟨f pc.block, pc.offset⟩ : PC).next? = pc.next?.map (fun n => ⟨f n.block, n.offset⟩) := by
  unfold PC.next?
  split <;> simp_all

theorem PC.next?_block {pc n : PC} (h : pc.next? = some n) : n.block = pc.block := by
  unfold PC.next? at h
  split at h
  · cases h
  · cases h
    rfl

/-- Related machines with trapped statuses: only the frames and what safety
reads (registers, permissions, tokens) are kept. -/
theorem LRel.ofTrapped {holes : Holes} {m m' : Machine} {f f' : Trap} (hs : m.status = .trapped f)
    (hs' : m'.status = .trapped f') (registers : m'.core.registers = m.core.registers)
    (readable : m'.core.memory.readable = m.core.memory.readable)
    (writable : m'.core.memory.writable = m.core.memory.writable)
    (pc : m'.pc = ⟨renum order m.pc.block, m.pc.offset⟩) (placed : m.pc.block.toNat ∈ order)
    (returns : FramesRel order m.returns m'.returns) (tokens : TokensAt m'.core.memory m'.returns) :
    LRel p order holes m m' where
  registers := registers
  readable := readable
  writable := writable
  bytes h := absurd hs (h f)
  pc := pc
  placed := placed
  returns := returns
  status := by rw [hs, hs']; trivial
  tokens := tokens
  atRet v h := by rw [hs] at h; cases h

theorem LRel.trap {holes holes' : Holes} {m m' : Machine} (rel : LRel p order holes m m') (f f' : Trap) :
    LRel p order holes' (m.trap f) (m'.trap f') :=
  LRel.ofTrapped rfl rfl rel.registers rel.readable rel.writable rel.pc rel.placed rel.returns rel.tokens

/-- A row's outcome on related running machines. -/
theorem afterRow_rel {holes holes' : Holes} {m m' : Machine} (rel : LRel p order holes m m')
    (running : m.status = .running) {r r' : Except ExecFault (Core × ByteEval.Flags)}
    (pair : ExecPair holes' r r') (tokens : ∀ c f, r' = .ok (c, f) → TokensAt c.memory m'.returns) :
    LRel p order holes' (m.afterRow r) (m'.afterRow r') := by
  cases r with
  | error e =>
      cases r' with
      | ok _ => cases pair
      | error e' =>
          cases e <;> cases e' <;> simp only [ExecPair, reduceCtorEq] at pair <;>
            exact rel.trap _ _
  | ok res =>
      cases r' with
      | error _ => cases pair
      | ok res' =>
          obtain ⟨c, f⟩ := res
          obtain ⟨c', f'⟩ := res'
          obtain ⟨-, regs, mem⟩ := pair
          simp only [Machine.afterRow, Machine.advanceWith]
          rw [rel.pc, PC.next?_rename]
          cases hn : m.pc.next? with
          | none => exact rel.trap _ _
          | some n =>
              have hb := PC.next?_block hn
              exact {
                registers := regs
                readable := mem.readable.symm
                writable := mem.writable.symm
                bytes := fun _ a ha => (mem.bytes a ha).symm
                pc := rfl
                placed := by rw [hb]; exact rel.placed
                returns := rel.returns
                status := by simp only [running, rel.running running]; trivial
                tokens := tokens c' f' rfl
                atRet := fun v h => by simp only [running] at h; cases h }

theorem exec_flagsOnly {o : Op} (only : o.flagsOnly = true) {args : List Arg} {core c : Core}
    {flags f : ByteEval.Flags} (h : o.exec args core flags = .ok (c, f)) : c = core := by
  unfold Op.exec at h
  simp only [bind, Except.bind] at h
  cases hr : o.run args core (flags.restrict (desc o).flagsIn) with
  | error e => simp [hr] at h
  | ok r =>
      obtain ⟨c₀, out⟩ := r
      simp only [hr, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      exact run_flagsOnly only hr

/-- The fused instructions of a well-formed program have flag-only
producers. -/
theorem fused_flagsOnly {blk : Block} {j : Nat} {producer consumer : Op} {pargs cargs : List Arg}
    (setup : Setup p q order) {b : Nat} (found : p.blocks[b]? = some blk)
    (hi : blk.instructions[j]? = some (.fused producer pargs consumer cargs)) : producer.flagsOnly = true := by
  have valid := (wellFormed_block setup.wf found).2.2.1
  simp only [Block.instructionsValid, Array.all_eq_true_iff_forall_mem] at valid
  have := valid _ (Array.mem_of_getElem? hi)
  simp only [Instr.wellFormed, Bool.and_eq_true] at this
  exact this.1.1.1.1.1.2

theorem write64_bytes_outside' {memory : Memory} {address value a : Word}
    (outside : ¬inRange address 8 a) : (memory.write64 address value).bytes a = memory.bytes a :=
  Memory.write64_bytes_outside _ _ _ _ (outside_range outside)

/-- One step from related machines, safe at the original, leads to related
machines under the next mask. -/
theorem lin_step {runtime : Runtime} {cp cq : Checked} (hp : cp.program = p) (hq : cq.program = q)
    (setup : Setup p q order) {holes : Holes} {m m' : Machine} (rel : LRel p order holes m m')
    (safe : SafeAt p holes m) :
    LRel p order (holeStep p m holes) (step runtime cp m) (step runtime cq m') := by
  obtain ⟨blk, i, found, hrn, found'⟩ := setup.block rel.placed
  have regs := rel.registers
  have hpc := rel.pc
  cases hs : m.status with
  | halted v =>
      have hs' := rel.halted hs
      rw [step_of_not_running _ _ _ (by simp [hs]), step_of_not_running _ _ _ (by simp [hs'])]
      obtain ⟨blk₀, found₀, pos, term⟩ := rel.atRet v hs
      have : holeStep p m holes = holes := by
        simp [holeStep, found₀, pos, term, terminatorHoles]
      rw [this]
      exact rel
  | trapped f =>
      obtain ⟨f', hs'⟩ := rel.trapped hs
      rw [step_of_not_running _ _ _ (by simp [hs]), step_of_not_running _ _ _ (by simp [hs'])]
      exact LRel.ofTrapped hs hs' rel.registers rel.readable rel.writable rel.pc rel.placed rel.returns rel.tokens
  | running =>
  have hs' := rel.running hs
  have notTrapped : ∀ f, m.status ≠ .trapped f := by simp [hs]
  have mem := rel.memory notTrapped
  unfold SafeAt at safe
  simp only [found] at safe
  cases hi : blk.instructions[m.pc.offset.toNat]? with
  | some ins =>
    simp only [hi] at safe
    have s₁ : step runtime cp m = executeInstr runtime cp ins m := by
      simp [step, hs, hp, found, hi]
    have s₂ : step runtime cq m' = executeInstr runtime cq (linInstr (renum order) ins) m' := by
      simp [step, hs', hq, hpc, found', linBlk_instr, hi]
    rw [s₁, s₂]
    cases ins with
    | op o args =>
        have hh : holeStep p m holes = nextHoles holes (.op o args) m.core := by
          simp [holeStep, found, hi, Encode.instructionOperation]
        rw [hh]
        simp only [linInstr, executeInstr]
        refine afterRow_rel rel hs (exec_pair regs mem o args {} safe) ?_
        intro c f h
        exact TokensAt.exec rel.tokens h (OperationSafe.transfer safe regs rel.returns).2
    | fused producer pargs consumer cargs =>
        have only := fused_flagsOnly setup found hi
        have hh : holeStep p m holes = nextHoles holes (.op consumer cargs) m.core := by
          simp [holeStep, found, hi]
        rw [hh]
        simp only [linInstr, executeInstr]
        have pair := exec_pair regs mem producer pargs {} safe.1
        rw [nextHoles_flagsOnly only] at pair
        cases hx : producer.exec pargs m.core {} with
        | error e =>
            cases hx' : producer.exec pargs m'.core {} with
            | ok _ => simp [hx, hx', ExecPair] at pair
            | error e' =>
                simp only [hx, hx'] at pair
                exact afterRow_rel rel hs (r := .error e) (r' := .error e') pair (fun _ _ h => by cases h)
        | ok res =>
            cases hx' : producer.exec pargs m'.core {} with
            | error _ => simp [hx, hx', ExecPair] at pair
            | ok res' =>
                obtain ⟨c, fl⟩ := res
                obtain ⟨c', fl'⟩ := res'
                simp only [hx, hx', ExecPair] at pair
                obtain ⟨hfl, -, -⟩ := pair
                subst fl'
                have hc := exec_flagsOnly only hx
                have hc' := exec_flagsOnly only hx'
                subst hc hc'
                refine afterRow_rel rel hs (exec_pair regs mem consumer cargs fl safe.2) ?_
                intro c₁ f₁ h
                exact TokensAt.exec rel.tokens h (OperationSafe.transfer safe.2 regs rel.returns).2
    | unwind source =>
        have hh : holeStep p m holes = nextHoles holes (.op unwindRow [.reg .rsp, .mem source]) m.core := by
          simp [holeStep, found, hi, Encode.instructionOperation]
        rw [hh]
        simp only [linInstr, executeInstr]
        have pair := exec_pair regs mem unwindRow [.reg .rsp, .mem source] {} safe
        have safe' := OperationSafe.transfer safe regs rel.returns
        cases hx : unwindRow.exec [.reg .rsp, .mem source] m.core {} with
        | error e =>
            cases hx' : unwindRow.exec [.reg .rsp, .mem source] m'.core {} with
            | ok _ => simp [hx, hx', ExecPair] at pair
            | error e' =>
                simp only [hx, hx'] at pair
                exact afterRow_rel rel hs (r := .error e) (r' := .error e') pair (fun _ _ h => by cases h)
        | ok res =>
            cases hx' : unwindRow.exec [.reg .rsp, .mem source] m'.core {} with
            | error _ => simp [hx, hx', ExecPair] at pair
            | ok res' =>
                obtain ⟨c, fl⟩ := res
                obtain ⟨c', fl'⟩ := res'
                simp only [hx, hx', ExecPair] at pair
                obtain ⟨-, regs₁, mem₁⟩ := pair
                have tokens₁ := TokensAt.exec rel.tokens hx' safe'.2
                have sp : c'.readReg .rsp = c.readReg .rsp := by simp [Core.readReg, regs₁]
                simp only
                rw [sp]
                rcases rel.returns.cutAt (c.readReg .rsp) with ⟨h₁, h₂⟩ | ⟨rest, rest', h₁, h₂, hrest⟩
                · rw [h₁, h₂]
                  exact rel.trap _ _
                · rw [h₁, h₂]
                  have suffix' := cutAt_suffix h₂
                  simp only [Machine.advanceWith]
                  rw [rel.pc, PC.next?_rename]
                  cases hn : m.pc.next? with
                  | none =>
                      exact LRel.ofTrapped rfl rfl rel.registers rel.readable rel.writable rel.pc rel.placed hrest
                        (rel.tokens.suffix suffix')
                  | some n =>
                      have hb := PC.next?_block hn
                      exact {
                        registers := regs₁
                        readable := mem₁.readable.symm
                        writable := mem₁.writable.symm
                        bytes := fun _ a ha => (mem₁.bytes a ha).symm
                        pc := rfl
                        placed := by rw [hb]; exact rel.placed
                        returns := hrest
                        status := by simp only [hs, hs']; trivial
                        tokens := tokens₁.suffix suffix'
                        atRet := fun v h => by simp only [hs] at h; cases h }
    | callRuntime r => exact absurd safe id
    | call t =>
        obtain ⟨aligned, allowed, disjoint⟩ := safe
        have placedT : t.toNat ∈ order := setup.target rel.placed found (call_target hi)
        have hh : holeStep p m holes = addRange holes (m.core.readReg .rsp - 8) 8 := by
          simp [holeStep, found, hi]
        rw [hh]
        simp only [linInstr, executeInstr, rel.readReg, aligned, Bool.not_true, Bool.false_eq_true, ite_false,
          hp, hq, setup.hasBlock_source placedT, setup.hasBlock placedT, ite_true]
        rw [rel.pc, PC.next?_rename]
        cases hn : m.pc.next? with
        | none => exact rel.trap _ _
        | some n =>
            have hb := PC.next?_block hn
            simp only [Option.map_some]
            have w₁ : m.core.memory.write64? (m.core.readReg .rsp - 8) n.encode =
                .ok (m.core.memory.write64 (m.core.readReg .rsp - 8) n.encode) := by
              simp [Memory.write64?, Memory.write?, Width.bytes, allowed, Memory.write64]
            have w₂ : m'.core.memory.write64? (m.core.readReg .rsp - 8) (⟨renum order n.block, n.offset⟩ : PC).encode =
                .ok (m'.core.memory.write64 (m.core.readReg .rsp - 8) (⟨renum order n.block, n.offset⟩ : PC).encode) := by
              simp [Memory.write64?, Memory.write?, Width.bytes, rel.writable, allowed, Memory.write64]
            rw [w₁, w₂]
            dsimp only
            exact {
              registers := by simp [Core.setReg, regs]
              readable := by simp [rel.readable]
              writable := by simp [rel.writable]
              bytes := fun _ a ha => by
                simp only [addRange, not_or] at ha
                rw [write64_bytes_outside' ha.2, write64_bytes_outside' ha.2]
                exact rel.bytes notTrapped a ha.1
              pc := rfl
              placed := placedT
              returns := .cons ⟨rfl, by rw [hb]; exact rel.placed, rfl,
                calleeSavedSnapshot_registers regs⟩ rel.returns
              status := by rw [hs, hs']; trivial
              tokens := by
                intro frame member
                simp only [List.mem_cons] at member
                rcases member with rfl | member
                · exact Memory.read64_write64 _ _ _
                · have tok := rel.tokens frame member
                  rw [← tok]
                  apply Memory.readLittle_congr
                  intro k hk
                  apply write64_bytes_outside'
                  rintro ⟨j, hj, e⟩
                  exact rel.returns.disjoint disjoint frame member k hk j hj e
              atRet := fun v h => by simp only [hs] at h; cases h }
  | none =>
    simp only [hi] at safe
    obtain ⟨position, tsafe⟩ := safe
    have s₁ : step runtime cp m = executeTerminator cp blk.terminator m := by
      simp [step, hs, hp, found, position]
    have s₂ : step runtime cq m' = executeTerminator cq (linTerm (renum order) i blk.terminator) m' := by
      simp [step, hs', hq, hpc, found', linBlk_size, linBlk_terminator, position]
    have hh : holeStep p m holes = terminatorHoles holes blk.terminator m.core := by
      simp [holeStep, found, hi]
    rw [s₁, s₂, hh]
    have targets : ∀ t ∈ blk.targets, t.toNat ∈ order := fun t ht => setup.target rel.placed found ht
    cases ht : blk.terminator with
    | jump t =>
        have placedT : t.toNat ∈ order := targets t (by simp [Block.targets, ht])
        simp only [linTerm, executeTerminator, terminatorHoles]
        rw [goto_valid (c := cp) (by rw [hp]; exact setup.hasBlock_source placedT),
          goto_valid (c := cq) (by rw [hq]; exact setup.hasBlock placedT)]
        exact { rel with pc := rfl, placed := placedT, atRet := fun v h => by simp [hs] at h }
    | tailCall t =>
        have placedT : t.toNat ∈ order := targets t (by simp [Block.targets, ht])
        simp only [linTerm, executeTerminator, terminatorHoles]
        rw [goto_valid (c := cp) (by rw [hp]; exact setup.hasBlock_source placedT),
          goto_valid (c := cq) (by rw [hq]; exact setup.hasBlock placedT)]
        exact { rel with pc := rfl, placed := placedT, atRet := fun v h => by simp [hs] at h }
    | ret =>
        simp only [ht] at tsafe
        simp only [linTerm, executeTerminator, terminatorHoles]
        cases hr : m.returns with
        | nil =>
            have hr' : m'.returns = [] := by
              have hrel := rel.returns
              rw [hr] at hrel
              exact hrel.nil_inv
            simp only [hr']
            exact {
              registers := regs
              readable := rel.readable
              writable := rel.writable
              bytes := fun _ => rel.bytes notTrapped
              pc := rel.pc
              placed := rel.placed
              returns := .nil
              status := by simp only [StatusRel, rel.readReg]
              tokens := fun _ h => by cases h
              atRet := fun v h => ⟨blk, found, position, ht⟩ }
        | cons f fs =>
            have hrel := rel.returns
            rw [hr] at hrel
            obtain ⟨f', fs', hr', head, tail⟩ := hrel.cons_inv
            simp only [hr] at tsafe
            obtain ⟨hsp, hread, hmatch⟩ := tsafe
            have tok := rel.tokens f' (by simp [hr'])
            rw [head.slot] at tok
            have hread' := read64?_tokens rel.readable hread tok
            have hmatch' : m'.core.calleeSavedMatch f'.calleeSaved = true := by
              rw [calleeSavedMatch_registers regs, head.saved]
              exact hmatch
            simp only [hr', rel.readReg, hsp, head.slot, bne_self_eq_false, Bool.false_eq_true, ite_false,
              hread, hread', hmatch, hmatch', Bool.not_true]
            exact {
              registers := by simp [Core.setReg, regs]
              readable := rel.readable
              writable := rel.writable
              bytes := fun _ => rel.bytes notTrapped
              pc := by rw [head.continuation]
              placed := head.placed
              returns := tail
              status := by simp only [hs, hs']; trivial
              tokens := rel.tokens.suffix (by rw [hr']; exact List.suffix_cons _ _)
              atRet := fun v h => by simp [hs] at h }
    | branch producer args c yes no reach =>
        have placedY : yes.toNat ∈ order := targets yes (by simp [Block.targets, ht])
        have placedN : no.toNat ∈ order := targets no (by simp [Block.targets, ht])
        simp only [ht] at tsafe
        simp only [terminatorHoles]
        obtain ⟨c', yes', no', reach', he, choice⟩ := linTerm_branch (renum order) i producer args c yes no reach
        rw [he]
        simp only [executeTerminator]
        have pair := exec_pair regs mem producer args {} tsafe
        have safe' := OperationSafe.transfer tsafe regs rel.returns
        cases hx : producer.exec args m.core {} with
        | error e =>
            cases hx' : producer.exec args m'.core {} with
            | ok _ => simp [hx, hx', ExecPair] at pair
            | error e' =>
                simp only [hx, hx'] at pair
                exact afterRow_rel rel hs (r := .error e) (r' := .error e') pair (fun _ _ h => by cases h)
        | ok res =>
            cases hx' : producer.exec args m'.core {} with
            | error _ => simp [hx, hx', ExecPair] at pair
            | ok res' =>
                obtain ⟨c₁, fl⟩ := res
                obtain ⟨c₁', fl'⟩ := res'
                simp only [hx, hx', ExecPair] at pair
                obtain ⟨hfl, regs₁, mem₁⟩ := pair
                subst fl'
                have tokens₁ := TokensAt.exec rel.tokens hx' safe'.2
                simp only
                have related : ∀ (target : BlockId), target.toNat ∈ order →
                    LRel p order (nextHoles holes (.op producer args) m.core)
                      ({ m with core := c₁ }.goto cp target) ({ m' with core := c₁' }.goto cq (renum order target)) := by
                  intro target placedT
                  rw [goto_valid (c := cp) (by rw [hp]; exact setup.hasBlock_source placedT),
                    goto_valid (c := cq) (by rw [hq]; exact setup.hasBlock placedT)]
                  exact {
                    registers := regs₁
                    readable := mem₁.readable.symm
                    writable := mem₁.writable.symm
                    bytes := fun _ a ha => (mem₁.bytes a ha).symm
                    pc := rfl
                    placed := placedT
                    returns := rel.returns
                    status := by simp only [hs, hs']; trivial
                    tokens := tokens₁
                    atRet := fun v h => by simp [hs] at h }
                rcases choice with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ <;> rw [h₁, h₂, h₃]
                · cases htest : fl.test c with
                  | none => exact rel.trap _ _
                  | some taken =>
                      simp only
                      cases taken
                      · exact related no placedN
                      · exact related yes placedY
                · rw [ByteEval.Flags.test_negate]
                  cases htest : fl.test c with
                  | none => exact rel.trap _ _
                  | some taken =>
                      simp only [Option.map_some]
                      cases taken
                      · exact related no placedN
                      · exact related yes placedY

/-! ## Runs -/

/-- `SafeSteps` runs transfer step for step, with the same masks. -/
theorem lin_safeSteps {runtime : Runtime} {cp cq : Checked} (hp : cp.program = p) (hq : cq.program = q)
    (setup : Setup p q order) {n : Nat} {holes holes' : Holes} {m m₁ : Machine}
    (steps : SafeSteps runtime cp n holes m holes' m₁) :
    ∀ {m' : Machine}, LRel p order holes m m' →
      ∃ m₁', SafeSteps runtime cq n holes m' holes' m₁' ∧ LRel p order holes' m₁ m₁' := by
  induction steps with
  | refl holes m => intro m' rel; exact ⟨m', .refl _ _, rel⟩
  | @cons before middle after holes finalHoles count safe first rest ih =>
      intro m' rel
      rw [hp] at safe
      obtain ⟨safe', holesEq⟩ := lin_safe setup rel safe
      have rel' := lin_step (runtime := runtime) hp hq setup rel safe
      rw [first] at rel'
      have rel'' : LRel p order (holeStep cp.program before holes) middle (step runtime cq m') := by
        rw [hp]
        exact rel'
      obtain ⟨m₁', steps', rel₁⟩ := ih rel''
      refine ⟨m₁', .cons (by rw [hq]; exact safe') rfl ?_, rel₁⟩
      rw [hq, holesEq, ← hp]
      exact steps'

/-- The two initial machines are related under any mask. -/
theorem lin_initial {cp cq : Checked} (hp : cp.program = p) (hq : cq.program = q) (setup : Setup p q order)
    (entry : p.entry.toNat ∈ order) (core : Core) (holes : Holes) :
    LRel p order holes (Machine.initial cp core) (Machine.initial cq core) where
  registers := rfl
  readable := rfl
  writable := rfl
  bytes _ _ _ := rfl
  pc := by simp [Machine.initial, hp, hq, setup.program, linProgram]
  placed := by simpa [Machine.initial, hp] using entry
  returns := .nil
  status := trivial
  tokens _ h := by cases h
  atRet _ h := by cases h

/-- What `Layout.run` and the validity of both programs give. -/
theorem setup_of_run {s : Shape} {o : Order} {pos : NatMap Nat} (wf : p.wellFormed = true)
    (h : Layout.run p s o = .ok (q, pos)) (wfq : q.wellFormed = true) : Setup p q o.flatten ∧ OrderSound p s o := by
  obtain ⟨check, eq⟩ := run_eq h
  have sound := Order.check_sound check
  have size : q.blocks.size = o.flatten.length := by simp [eq, linProgram]
  refine ⟨⟨wf, sound.nodup, sound.inRange, sound.closed, eq, ?_⟩, sound⟩
  rw [← size]
  exact ((wellFormed_iff q).1 wfq).2.1

/-- Linearisation as a simulation: a `SafeSteps` run of the original
program from its initial machine is matched, step for step and with the
same masks, by a run of the laid-out program from its initial machine,
ending in related machines. -/
theorem linearize_run {runtime : Runtime} {s : Shape} {o : Order} {pos : NatMap Nat} {cp cq : Checked}
    (hp : cp.program = p) (hq : cq.program = q) (h : Layout.run p s o = .ok (q, pos)) {n : Nat}
    {holes holes' : Holes} {core : Core} {m₁ : Machine}
    (steps : SafeSteps runtime cp n holes (Machine.initial cp core) holes' m₁) :
    ∃ m₁', SafeSteps runtime cq n holes (Machine.initial cq core) holes' m₁' ∧ LRel p o.flatten holes' m₁ m₁' := by
  obtain ⟨setup, sound⟩ := setup_of_run (hp ▸ cp.valid) h (hq ▸ cq.valid)
  exact lin_safeSteps hp hq setup steps (lin_initial hp hq setup sound.entry core holes)

/-! ## What transfers -/

/-- An `Exit` transfers when the 8 bytes at the final `rsp` are not masked
(the caller's return address, which no return slot of the run covers). -/
theorem LRel.exit {holes : Holes} {m m' : Machine} (rel : LRel p order holes m m') {core₀ : Core}
    {retAddr st val : Word} (exit : Exit core₀ retAddr st val m)
    (data : ReadableData holes (m.core.readReg .rsp) 8) : Exit core₀ retAddr st val m' := by
  obtain ⟨halted, value, saved, rsp, slot⟩ := exit
  have notTrapped : ∀ f, m.status ≠ .trapped f := by simp [halted]
  have mem := rel.memory notTrapped
  refine ⟨rel.halted halted, by rw [rel.readReg]; exact value, fun r hr => by rw [rel.readReg]; exact saved r hr,
    by rw [rel.readReg]; exact rsp, ?_⟩
  rw [rel.readReg, ← slot]
  exact (mem.read? .w64 _ data).symm

theorem LRel.status_running {holes : Holes} {m m' : Machine} (rel : LRel p order holes m m')
    (running : m.status = .running) : m'.status = .running := rel.running running

end IxCC.X86.Layout.Proof
