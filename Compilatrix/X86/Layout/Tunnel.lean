import Compilatrix.X86.Layout.Basic
import Compilatrix.X86.Eval

/-!
# Tunnelling (05 §7, step 1)

A jump or branch to an empty block that only jumps on is redirected to
where the chain of such blocks ends, so a failure site reaches its
exit-group block in one transfer and an empty edge block left by
allocation costs nothing. Call and tail-call targets and the entry are
kept: they are function entries. The chain is followed at most once per
block (the fuel), so an empty cycle ends somewhere on the cycle. The
redirected-around blocks stay in the program until the block order drops
them as unreachable.

Tunnelling is a proved-once, re-run pass (P, 05 §1.1). What it preserves
is `ChainTo`: every redirected target is reached from the old one by
executing empty jumps (`chase_chain`), each of which is one typed step
that changes only the PC (`step_emptyJump`, `run_chain`). The designs are
`CompCert/backend/Tunneling.v` and `jasmin/proofs/compiler/tunneling.v`.
-/

namespace Compilatrix.X86.Layout

/-- The target of an empty block that only jumps. -/
def emptyJump? (b : Block) : Option BlockId :=
  match b.terminator with
  | .jump u => if b.instructions.isEmpty then some u else none
  | _ => none

/-- Follow empty jump blocks from `t`, at most `fuel` of them. -/
def chase (m : NatMap Block) : Nat → BlockId → BlockId
  | 0, t => t
  | fuel + 1, t =>
      match (m.get? t.toNat).bind emptyJump? with
      | some u => chase m fuel u
      | none => t

/-- Redirect a terminator's jump and branch targets. Tunnelling runs before
linearisation, which decides fall-through, so a branch leaves it with a
`rel32` false edge. -/
def tunnelTerminator (m : NatMap Block) (fuel : Nat) : Terminator → Terminator
  | .jump t => .jump (chase m fuel t)
  | .branch producer args condition yes no _ => .branch producer args condition (chase m fuel yes) (chase m fuel no)
  | t => t

/-- Tunnel every block of a program. -/
def tunnel (p : Program) : Program :=
  let m := blockMap p
  let fuel := p.blocks.size
  { p with blocks := (p.blocks.toList.map fun b => { b with terminator := tunnelTerminator m fuel b.terminator }).toArray }

/-! ## What tunnelling preserves -/

/-- `u` is reached from `t` by a chain of empty jump blocks. -/
inductive ChainTo (m : NatMap Block) : BlockId → BlockId → Prop where
  | refl (t : BlockId) : ChainTo m t t
  | step {t u v : BlockId} {b : Block} (found : m.get? t.toNat = some b) (empty : emptyJump? b = some u)
      (rest : ChainTo m u v) : ChainTo m t v

/-- Every tunnelled target lies at the end of an empty-jump chain from the
original one. -/
theorem chase_chain (m : NatMap Block) (fuel : Nat) (t : BlockId) : ChainTo m t (chase m fuel t) := by
  induction fuel generalizing t with
  | zero => exact .refl t
  | succ fuel ih =>
      simp only [chase]
      cases found : m.get? t.toNat with
      | none => simp only [Option.bind_none]; exact .refl t
      | some b =>
          simp only [Option.bind_some]
          cases empty : emptyJump? b with
          | none => exact .refl t
          | some u => exact .step found empty (ih u)

theorem emptyJump?_eq {b : Block} {u : BlockId} (empty : emptyJump? b = some u) :
    b.instructions = #[] ∧ b.terminator = .jump u := by
  unfold emptyJump? at empty
  split at empty
  · rename_i target terminator
    split at empty
    · rename_i isEmpty
      simp only [Option.some.injEq] at empty
      subst empty
      exact ⟨by simpa using isEmpty, terminator⟩
    · contradiction
  · contradiction

theorem blockMap_get {p : Program} {i : Nat} {b : Block} (found : (blockMap p).get? i = some b) :
    p.blocks[i]? = some b := by
  have key : ∀ (l : List (Block × Nat)) (acc : NatMap Block),
      (∀ j c, acc.get? j = some c → p.blocks[j]? = some c) →
      (∀ e ∈ l, p.blocks[e.2]? = some e.1) →
      ∀ j c, (l.foldl (fun m (x : Block × Nat) => m.insert x.2 x.1) acc).get? j = some c →
        p.blocks[j]? = some c := by
    intro l
    induction l with
    | nil => intro acc base _ j c h; exact base j c h
    | cons e rest ih =>
        intro acc base members j c h
        simp only [List.foldl_cons] at h
        refine ih _ ?_ (fun x mem => members x (by simp [mem])) j c h
        intro k d hk
        rw [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert] at hk
        split at hk
        · rename_i same
          have := members e (by simp)
          simp only [Option.some.injEq] at hk
          subst hk
          have equal : e.2 = k := Nat.compare_eq_eq.mp same
          rw [← equal]
          exact this
        · rw [← Std.TreeMap.get?_eq_getElem?] at hk
          exact base k d hk
  refine key _ {} (by intro j c h; simp at h) ?_ i b found
  intro e mem
  simpa using List.mem_zipIdx_iff_getElem?.mp mem

/-- An empty jump block is one typed step that only moves the PC. -/
theorem step_emptyJump (runtime : Runtime) (checked : Checked) (machine : Machine)
    (running : machine.status = .running) {b : Block} {u : BlockId}
    (found : checked.program.blocks[machine.pc.block.toNat]? = some b) (start : machine.pc.offset = 0)
    (empty : emptyJump? b = some u) (valid : checked.program.hasBlock u = true) :
    step runtime checked machine = { machine with pc := ⟨u, 0⟩ } := by
  obtain ⟨noInstructions, jumps⟩ := emptyJump?_eq empty
  simp [step, running, found, start, noInstructions, jumps, executeTerminator, Machine.goto, valid]

/-- Following an empty-jump chain in the program's own block map is a run
that changes only the PC, when every block on it is valid. -/
theorem run_chain (runtime : Runtime) (checked : Checked) {t u : BlockId}
    (chain : ChainTo (blockMap checked.program) t u) (valid : checked.program.hasBlock u = true) :
    ∀ machine : Machine, machine.status = .running → machine.pc = ⟨t, 0⟩ →
      ∃ k, run runtime checked k machine = { machine with pc := ⟨u, 0⟩ } := by
  induction chain with
  | refl t =>
      intro machine _ pc
      exact ⟨0, by cases machine; simp_all [run]⟩
  | @step t v w b found empty rest ih =>
      intro machine running pc
      have inProgram := blockMap_get found
      have vValid : checked.program.hasBlock v = true := by
        cases rest with
        | refl => exact valid
        | step found' _ _ =>
            have := blockMap_get found'
            simp [Program.hasBlock, (Array.getElem?_eq_some_iff.mp this).1]
      have stepped := step_emptyJump runtime checked machine running (b := b)
        (by rw [pc]; exact inProgram) (by rw [pc]) empty vValid
      obtain ⟨k, after⟩ := ih valid { machine with pc := ⟨v, 0⟩ } running rfl
      refine ⟨k + 1, ?_⟩
      obtain ⟨core, pc₀, returns, status⟩ := machine
      simp only at running
      subst running
      simpa [run, stepped] using after

end Compilatrix.X86.Layout
