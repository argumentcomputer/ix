import IxCC.Xv.XlSemantics

/-!
# Frame layouts

Stacking turns each Xl function into typed x86 with one `rsp`-relative
frame. Seen from a body instruction (after the prologue's `sub rsp, size`):

```text
[rsp, rsp + 8·outArgs)          outgoing stack arguments (outArg i at rsp + 8i)
[8·outArgs, size)               slots and callee-saved saves, 8-byte cells
[rsp + size]                    the return address
[rsp + size + 8 + 8i]           incoming stack argument inArg i
```

The layout is certificate data (D17): an untrusted oracle
(`FrameLayout.produce`) proposes it and `FrameLayout.check`, on the recheck
path, validates it against facts computed from the function (`Func.facts`):
every slot has a cell, cells are 8-aligned, in bounds and in strictly
increasing order (so pairwise distinct), the saved registers are exactly the callee-saved registers the
allocation writes (as in Cranelift, `machinst/vcode.rs:668-710`), a
function that calls keeps `rsp` 16-aligned at its calls, and the frame is
small enough for disp32 offsets and a non-wrapping stack check. Frameless
functions (size 0) have no cells, no outgoing arguments and no calls.

Everything here is in kernel-evaluable style (D17): lists, folds and
structural recursion. -/

namespace IxCC.Xv.Stacking

open IxCC.Lir (FunId Label)

/-! ## Convention constants -/

/-- The internal callee-saved registers an allocation may write. The
frame pointer `rbp` and the context register `r15` are never written, so
they are never saved. -/
def calleeSaved : List X86.GPR := [.rbx, .r12, .r13, .r14]

/-- Bytes below a checked frame that code without its own check may use: a
frameless leaf's return address, or a small leaf's frame with it.
A callee skips the prologue check exactly when it makes no call and its
frame plus return address fit in the slack. -/
def slack : Nat := 64

/-- The largest frame plus slack. Far below 2^31, so every frame offset is a
disp32 field, and the prologue's `lea` cannot wrap while the driver keeps
`stackLimit ≥ maxFrame + slack`. -/
def maxFrame : Nat := 2 ^ 20

/-! ## Facts about an Xl function -/

/-- What the frame of an Xl function must hold, read off its locations. -/
structure Facts where
  /-- One more than the largest slot index (0: no slots). -/
  slots : Nat := 0
  /-- One more than the largest outgoing-argument cell index. -/
  outArgs : Nat := 0
  /-- One more than the largest incoming-argument cell index read. -/
  inArgsUsed : Nat := 0
  /-- Incoming stack arguments: parameters past the seven argument registers. -/
  inArgs : Nat := 0
  /-- Whether the function makes a call (a tail call does not count). -/
  calls : Bool := false
  /-- Registers the function defines, in first-definition order. -/
  writes : List X86.GPR := []
  deriving DecidableEq, Repr, Inhabited

namespace Facts

/-- Record a location the function names. -/
def noteLoc (a : Facts) : Loc → Facts
  | .reg _ => a
  | .slot i => { a with slots := max a.slots (i + 1) }
  | .outArg i => { a with outArgs := max a.outArgs (i + 1) }
  | .inArg i => { a with inArgsUsed := max a.inArgsUsed (i + 1) }

/-- Record a location the function defines. -/
def noteDef (a : Facts) : Loc → Facts
  | .reg r => if a.writes.contains r then a else { a with writes := a.writes ++ [r] }
  | l => a.noteLoc l

def inst (a : Facts) (i : Inst Loc) : Facts :=
  let a := i.uses.foldl noteLoc a
  let a := i.defs.foldl noteDef a
  match i with
  | .call .. => { a with calls := true }
  | _ => a

def term (a : Facts) (t : Term Loc) : Facts :=
  let a := (t.uses ++ t.edgeUses).foldl noteLoc a
  t.defs.foldl noteDef a

def block (a : Facts) (b : Block Loc) : Facts :=
  let a := b.params.foldl noteDef a
  (b.body.toList.foldl inst a).term b.term

end Facts

/-- The facts of a function: every block, with its parameter count. -/
def _root_.IxCC.Xv.Func.facts (f : Func Loc) : Facts :=
  f.blocks.toList.foldl Facts.block { inArgs := f.params.length - Xl.nArgRegs }

/-- The callee-saved registers a function writes, in `calleeSaved` order:
exactly the registers its frame must save. -/
def saves (a : Facts) : List X86.GPR := calleeSaved.filter a.writes.contains

/-! ## Layouts -/

/-- A frame layout. Offsets are from `rsp` after the prologue. -/
structure FrameLayout where
  /-- Bytes from `rsp` to the return address (`sub rsp, size`); 0 is frameless. -/
  size : Nat
  /-- The cell of each Xl slot, by slot index. -/
  slotOff : List Nat
  /-- The cell of each saved callee-saved register. -/
  saveOff : List (X86.GPR × Nat)
  /-- Outgoing-argument cells at `[rsp, rsp + 8·outArgs)`. -/
  outArgs : Nat
  deriving DecidableEq, Repr, Inhabited

namespace FrameLayout

/-- Every 8-byte cell of the layout: slots, then saves. -/
def cells (l : FrameLayout) : List Nat := l.slotOff ++ l.saveOff.map Prod.snd

/-- The registers the layout saves. -/
def saved (l : FrameLayout) : List X86.GPR := l.saveOff.map Prod.fst

/-- A cell is 8-aligned and lies between the outgoing arguments and the
return address. -/
def cellOk (l : FrameLayout) (o : Nat) : Bool :=
  o % 8 == 0 && decide (8 * l.outArgs ≤ o) && decide (o + 8 ≤ l.size)

/-- Offsets in strictly increasing order: a loop, linear in the list. A
frame may hold 2^17 cells, too many for a pairwise distinctness test; the
oracle's cells are in increasing order, which implies distinct
(`ascending_nodup`). -/
def ascending : List Nat → Bool
  | a :: b :: rest => decide (a < b) && ascending (b :: rest)
  | _ => true

theorem ascending_cons {a : Nat} {s : List Nat} (h : ascending (a :: s) = true) :
    ascending s = true ∧ ∀ y ∈ s, a < y := by
  induction s generalizing a with
  | nil => simp [ascending]
  | cons b rest ih =>
    simp only [ascending, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hab, hrest⟩ := h
    obtain ⟨-, hb⟩ := ih hrest
    refine ⟨hrest, fun y hy => ?_⟩
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hab
    · exact Nat.lt_trans hab (hb y hy)

theorem ascending_nodup : ∀ {s : List Nat}, ascending s = true → s.Nodup
  | [], _ => List.nodup_nil
  | a :: s, h => by
    obtain ⟨hs, ha⟩ := ascending_cons h
    exact List.nodup_cons.2 ⟨fun m => Nat.lt_irrefl a (ha a m), ascending_nodup hs⟩

/-- The recheck-path validator of a proposed layout. -/
def check (a : Facts) (l : FrameLayout) : Bool :=
  decide (l.size + slack ≤ maxFrame) &&
  l.slotOff.length == a.slots &&
  decide (l.saveOff.length ≤ (saves a).length) &&
  decide (a.outArgs ≤ l.outArgs) &&
  decide (8 * l.outArgs ≤ l.size) &&
  (!a.calls || l.size != 0) &&
  (l.size == 0 || (l.size + 8) % 16 == 0) &&
  l.saved.all (saves a).contains &&
  (saves a).all l.saved.contains &&
  decide l.saved.Nodup &&
  l.cells.all l.cellOk &&
  decide (8 * l.cells.length ≤ l.size) &&
  ascending l.cells

/-- The untrusted oracle: outgoing arguments at the bottom, then the slots
in index order, then the saves, rounded up so that `rsp` is 16-aligned at a
call. A function with no cells and no call is frameless. -/
def produce (a : Facts) : FrameLayout :=
  let base := 8 * a.outArgs
  let slotOff := (List.range a.slots).map fun i => base + 8 * i
  let saveBase := base + 8 * a.slots
  let saveOff := (saves a).zipIdx.map fun (r, j) => (r, saveBase + 8 * j)
  let raw := saveBase + 8 * (saves a).length
  let size :=
    if raw == 0 && !a.calls then 0
    else if (raw + 8) % 16 == 0 then raw else raw + 8
  { size, slotOff, saveOff, outArgs := a.outArgs }

/-- Whether the prologue checks the stack: a frame with a call, or one too
big for the caller's slack. Frameless functions never check. -/
def checked (a : Facts) (l : FrameLayout) : Bool :=
  l.size != 0 && (a.calls || decide (slack < l.size + 8))

/-! ## What `check` guarantees -/

/-- The properties `check` establishes (disjoint, aligned, in bounds,
saves exact), with the coverage, alignment and size facts stacking uses. -/
structure Sound (a : Facts) (l : FrameLayout) : Prop where
  covers : l.slotOff.length = a.slots
  outArgs : a.outArgs ≤ l.outArgs
  outArgsFit : 8 * l.outArgs ≤ l.size
  aligned : ∀ o ∈ l.cells, o % 8 = 0
  inBounds : ∀ o ∈ l.cells, 8 * l.outArgs ≤ o ∧ o + 8 ≤ l.size
  distinct : l.cells.Nodup
  savesDistinct : l.saved.Nodup
  savesExact : ∀ r, r ∈ l.saved ↔ r ∈ saves a
  calls : a.calls = true → l.size ≠ 0
  aligned16 : l.size ≠ 0 → (l.size + 8) % 16 = 0
  bounded : l.size + slack ≤ maxFrame

theorem check_sound {a : Facts} {l : FrameLayout} (h : l.check a = true) : l.Sound a := by
  simp only [check, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨bounded, covers⟩, _⟩, outArgs⟩, fit⟩, calls⟩, aligned16⟩, sub⟩, sup⟩,
    savesDistinct⟩, cells⟩, _⟩, distinct⟩ := h
  refine ⟨covers, outArgs, fit, ?_, ?_, ascending_nodup distinct, savesDistinct, ?_, ?_, ?_, bounded⟩
  · intro o member
    have ok := cells o member
    simp only [cellOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ok
    exact ok.1.1
  · intro o member
    have ok := cells o member
    simp only [cellOk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ok
    exact ⟨ok.1.2, ok.2⟩
  · intro r
    constructor
    · intro member
      simpa using sub r member
    · intro member
      simpa using sup r member
  · intro called
    rcases calls with notCalled | nonzero
    · simp [called] at notCalled
    · exact nonzero
  · intro nonzero
    rcases aligned16 with zero | aligned
    · exact absurd zero nonzero
    · exact aligned

/-- Distinct cells of a sound layout do not overlap: their offsets are
distinct multiples of 8. -/
theorem Sound.separated {a : Facts} {l : FrameLayout} (sound : l.Sound a) {o₁ o₂ : Nat}
    (m₁ : o₁ ∈ l.cells) (m₂ : o₂ ∈ l.cells) (different : o₁ ≠ o₂) : o₁ + 8 ≤ o₂ ∨ o₂ + 8 ≤ o₁ := by
  have a₁ := sound.aligned o₁ m₁
  have a₂ := sound.aligned o₂ m₂
  omega

/-- A frameless layout has no cells, no outgoing arguments, no saves and no
calls (frameless ↔ size 0 with no calls, slots or saves). -/
theorem Sound.frameless {a : Facts} {l : FrameLayout} (sound : l.Sound a) (zero : l.size = 0) :
    a.slots = 0 ∧ l.outArgs = 0 ∧ a.outArgs = 0 ∧ saves a = [] ∧ a.calls = false := by
  have noCells : l.cells = [] := by
    cases cells : l.cells with
    | nil => rfl
    | cons o rest =>
        have bound := (sound.inBounds o (by simp [cells])).2
        omega
  have noSlots : l.slotOff = [] := by
    simp only [cells, List.append_eq_nil_iff] at noCells
    exact noCells.1
  have noSaved : l.saved = [] := by
    simp only [cells, List.append_eq_nil_iff, List.map_eq_nil_iff] at noCells
    simp [saved, noCells.2]
  have outZero : l.outArgs = 0 := by
    have := sound.outArgsFit
    omega
  refine ⟨?_, outZero, ?_, ?_, ?_⟩
  · have := sound.covers
    simp [noSlots] at this
    omega
  · have := sound.outArgs
    omega
  · cases savesList : saves a with
    | nil => rfl
    | cons r rest =>
        have := (sound.savesExact r).2 (by simp [savesList])
        simp [noSaved] at this
  · cases called : a.calls with
    | false => rfl
    | true => exact absurd zero (sound.calls called)

end FrameLayout

end IxCC.Xv.Stacking
