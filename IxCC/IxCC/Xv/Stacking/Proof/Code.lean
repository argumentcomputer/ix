import IxCC.Xv.Stacking.Proof.Shape
import IxCC.Xv.Stacking.Proof.InstXl

/-!
# Where the stacked code of an Xl position is

A program Stacking accepted (`Stk`) puts label `L` of function `k` at block
`labelBase + L` of the function's context (`ctxOf`), with the prologue
before label 0's body, each body instruction's code in order, and the
terminator's code after (`block_at`, `block_ok`). A checked function's stack
check is its first block (`check_at`); calls find a function's first block
and arity in the entry map (`entry_of`).
-/

namespace IxCC.Xv.Stacking.Proof

open IxCC.X86

/-- A program Stacking accepted, with the layouts, export passing and
convention it ran with. -/
structure Stk where
  p : LProgram
  layouts : List FrameLayout
  reps : Lir.FunId → Option (List ArgRep)
  env : Xl.Env
  st : Stacked
  ok : run p layouts reps env = .ok st

/-- The placed functions. -/
def Stk.placed (S : Stk) : List Placed := runPlaced S.p S.layouts S.reps

/-- Whether a placed function's prologue checks the stack, as a block shift. -/
def shiftOf (pl : Placed) : Nat := if FrameLayout.checked pl.facts pl.layout then 1 else 0

/-- The context Stacking emits a placed function with. -/
def ctxOf (placed : List Placed) (pl : Placed) : FnCtx :=
  ⟨pl.layout, pl.facts.inArgs, pl.start + shiftOf pl, pl.func.blocks.size, entriesOf placed, 0⟩

/-- Label `L`'s block, at `labelBase + L`. -/
theorem block_at (S : Stk) {k : Lir.FunId} {f : Func Loc} {l : FrameLayout} (hf : S.p.funcs[k]? = some f)
    (hl : S.layouts[k]? = some l) {L : Nat} {b : Block Loc} (hb : f.blocks[L]? = some b) :
    ∃ pl blk, S.placed[k]? = some pl ∧ pl.func = f ∧ pl.fn = k ∧ pl.layout = l ∧ pl.facts = f.facts ∧
      (ctxOf S.placed pl).block (if L = 0 then prologue l else []) b = .ok blk ∧
      S.st.program.blocks[(ctxOf S.placed pl).labelBase + L]? = some blk := by
  obtain ⟨pl, blks, hpl, hfunc, hfn, hlay, hfacts, hemit, hat⟩ := func_at S.ok hf hl
  obtain ⟨-, -, -, body, hbody, rfl⟩ := emitFunc_ok hemit
  obtain ⟨hlen, hget⟩ := mapM_ok hbody
  have hz : f.blocks.toList.zipIdx[L]? = some (b, L) := by
    simp [List.getElem?_zipIdx, hb]
  obtain ⟨blk, hblk, hok⟩ := hget L _ hz
  have hctx : ctxOf S.placed pl =
      FnCtx.mk l f.facts.inArgs (pl.start + if FrameLayout.checked f.facts l then 1 else 0) f.blocks.size
        (entriesOf (runPlaced S.p S.layouts S.reps)) 0 := by
    simp [ctxOf, shiftOf, hfunc, hlay, hfacts, Stk.placed]
  refine ⟨pl, blk, hpl, hfunc, hfn, hlay, hfacts, ?_, ?_⟩
  · rw [hctx]
    have := mapError_ok.1 hok
    by_cases h0 : L = 0
    · subst h0; simpa using this
    · simpa [h0] using this
  · have hL : L < body.length := by
      have := (List.getElem?_eq_some_iff.1 hblk).1
      exact this
    have hj : (if FrameLayout.checked f.facts l then 1 else 0) + L <
        ((if FrameLayout.checked f.facts l then
          [stackCheck l (FnCtx.failBlock (FnCtx.mk l f.facts.inArgs (pl.start + 1) f.blocks.size
            (entriesOf (runPlaced S.p S.layouts S.reps)) 0) 2) (UInt32.ofNat (pl.start + 1))] else []) ++
          body).length := by
      split <;> simp <;> omega
    have := hat _ hj
    rw [hctx]
    simp only [Nat.add_assoc] at this ⊢
    rw [this]
    split
    · simp [List.getElem?_cons_succ, hblk, Nat.add_comm]
    · simpa using hblk

/-- A checked function's first block is its stack check. -/
theorem check_at (S : Stk) {k : Lir.FunId} {f : Func Loc} {l : FrameLayout} (hf : S.p.funcs[k]? = some f)
    (hl : S.layouts[k]? = some l) (hc : FrameLayout.checked f.facts l = true) :
    ∃ pl, S.placed[k]? = some pl ∧ pl.func = f ∧ pl.layout = l ∧ pl.facts = f.facts ∧
      S.st.program.blocks[pl.start]? = some (stackCheck l 1 (UInt32.ofNat (pl.start + 1))) := by
  obtain ⟨pl, blks, hpl, hfunc, -, hlay, hfacts, hemit, hat⟩ := func_at S.ok hf hl
  obtain ⟨-, -, -, body, -, rfl⟩ := emitFunc_ok hemit
  refine ⟨pl, hpl, hfunc, hlay, hfacts, ?_⟩
  have := hat 0 (by simp [hc])
  rw [Nat.add_zero] at this
  rw [this]
  simp [hc, FnCtx.failBlock]

/-- A function's first block and arity, as calls find them. -/
theorem entry_of (S : Stk) (g : Lir.FunId) :
    (entriesOf S.placed).get? g = (S.placed[g]?).map fun pl => (pl.start, pl.func.params.length) :=
  entries_get g


/-- What `FnCtx.block` emits: the prefix, each instruction's code, and the
terminator's code. -/
theorem block_ok {c : FnCtx} {pre : List Instr} {b : Block Loc} {blk : X86.Block} (h : c.block pre b = .ok blk) :
    b.params = [] ∧ ∃ (codes : List (List Instr)) (post : List Instr) (t : X86.Terminator),
      codes.length = b.body.size ∧
      (∀ (i : Nat) (x : Inst Loc), b.body[i]? = some x → ∃ code, codes[i]? = some code ∧ c.inst x = .ok code) ∧
      c.term b.term = .ok (post, t) ∧
      blk = { instructions := (pre ++ codes.flatten ++ post).toArray, terminator := t } := by
  unfold FnCtx.block at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · rename_i hp
    split at h
    · simp at h
    · rename_i codes hcodes
      split at h
      · simp at h
      · rename_i pt hterm
        simp only [Except.ok.injEq] at h
        obtain ⟨hlen, hget⟩ := mapM_ok hcodes
        refine ⟨by simpa using hp, codes, pt.1, pt.2, by simpa using hlen, fun i x hx => ?_,
          mapError_ok.1 hterm, h.symm⟩
        have hz : b.body.toList.zipIdx[i]? = some (x, i) := by
          simp [List.getElem?_zipIdx, hx]
        obtain ⟨code, hc, hok⟩ := hget i _ hz
        exact ⟨code, hc, mapError_ok.1 hok⟩
  · simp [throw, throwThe, MonadExceptOf.throw] at h

end IxCC.Xv.Stacking.Proof
