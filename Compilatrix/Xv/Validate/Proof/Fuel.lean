import Compilatrix.Xv.Validate.Proof.Frames

/-!
# Fuel for Xv and Xl runs

`Xv.eval` and `Xl.eval` run with fuel `(2k + 3)·(size + 1)` at clock `k`.
This is enough: between two charges an activation moves forward through its
function, so the positions left to each frame form a `Sem.Potential` with
bound `size` (`Move.potential`). Both runs are therefore the clocked
outcomes of their steps (`Xv.runs_eval`, `Xl.runs_eval`) and clock monotone
(`Xv.eval_mono`, `Xl.eval_mono`).
-/

namespace Compilatrix.Xv

open Compilatrix.Lir (VReg Word)

variable {ρ : Type}

/-! ## Positions left -/

/-- The block sizes before label `L`. -/
def Func.before (f : Func ρ) (L : Nat) : Nat := ((f.blocks.toList.map Block.size).take L).sum

/-- The body size of block `L`, or zero. -/
def Func.bodyAt (f : Func ρ) (L : Nat) : Nat := (f.blocks[L]?.map (·.body.size)).getD 0

/-- Positions left in `f` going forward from label `L`, instruction `i`. -/
def Func.left (f : Func ρ) (L i : Nat) : Nat := f.size - (f.before L + min i (f.bodyAt L))

/-- Positions left in function `fn` of `p`. -/
def Program.left (p : Program ρ) (fn L i : Nat) : Nat :=
  match p.funcs[fn]? with
  | some f => f.left L i
  | none => 0

/-- The potential of a stack of positions (function, label, instruction). -/
def Program.potential (p : Program ρ) (st : List (Nat × Nat × Nat)) : Nat :=
  (st.map fun x => p.left x.1 x.2.1 x.2.2).sum

theorem foldl_add_eq {α : Type} (g : α → Nat) :
    ∀ (l : List α) (n : Nat), l.foldl (fun n b => n + g b) n = n + (l.map g).sum
  | [], n => by simp
  | b :: l, n => by simp [foldl_add_eq g l, Nat.add_assoc]

theorem Func.size_eq (f : Func ρ) : f.size = (f.blocks.toList.map Block.size).sum := by
  simp [Func.size, ← Array.foldl_toList, foldl_add_eq]

theorem Program.size_eq (p : Program ρ) : p.size = (p.funcs.toList.map Func.size).sum := by
  simp [Program.size, ← Array.foldl_toList, foldl_add_eq]

theorem sum_take_le : ∀ (l : List Nat) (n : Nat), (l.take n).sum ≤ l.sum
  | [], _ => by simp
  | _ :: _, 0 => by simp
  | x :: l, n + 1 => by
      have := sum_take_le l n
      simp only [List.take_succ_cons, List.sum_cons]
      omega

theorem le_sum_of_getElem? : ∀ {l : List Nat} {i x : Nat}, l[i]? = some x → x ≤ l.sum
  | [], _, _, h => by simp at h
  | y :: l, 0, x, h => by simp at h; subst h; simp
  | y :: l, i + 1, x, h => by
      have := le_sum_of_getElem? (l := l) (i := i) (by simpa using h)
      simp only [List.sum_cons]
      omega

namespace Func

variable {f : Func ρ} {L : Nat} {b : Block ρ}

theorem before_le (f : Func ρ) (L : Nat) : f.before L ≤ f.size := by
  rw [size_eq]
  exact sum_take_le _ _

theorem before_succ (hb : f.blocks[L]? = some b) : f.before (L + 1) = f.before L + b.size := by
  simp only [before]
  have hL : L < (f.blocks.toList.map Block.size).length := by
    simp only [List.length_map, Array.length_toList]
    exact (Array.getElem?_eq_some_iff.1 hb).1
  rw [List.take_add_one, List.sum_append, List.getElem?_eq_getElem hL]
  simp only [Option.toList_some, List.sum_cons, List.sum_nil, Nat.add_zero, List.getElem_map,
    Array.getElem_toList]
  rw [(Array.getElem?_eq_some_iff.1 hb).2]

theorem before_mono (f : Func ρ) {L L' : Nat} (h : L ≤ L') : f.before L ≤ f.before L' := by
  simp only [before]
  have := sum_take_le ((f.blocks.toList.map Block.size).take L') L
  rwa [List.take_take, Nat.min_eq_left h] at this

theorem bodyAt_eq (hb : f.blocks[L]? = some b) : f.bodyAt L = b.body.size := by
  simp [bodyAt, hb]

theorem at_lt (hb : f.blocks[L]? = some b) (i : Nat) :
    f.before L + min i (f.bodyAt L) < f.before (L + 1) := by
  rw [before_succ hb, bodyAt_eq hb]
  simp only [Block.size]
  omega

theorem left_le (f : Func ρ) (L i : Nat) : f.left L i ≤ f.size := Nat.sub_le _ _

theorem left_succ (hb : f.blocks[L]? = some b) {i : Nat} (hi : i < b.body.size) :
    f.left L (i + 1) < f.left L i := by
  have h1 := at_lt hb (i + 1)
  have h2 := before_le f (L + 1)
  simp only [left, bodyAt_eq hb] at h1 ⊢
  omega

theorem left_fwd (hb : f.blocks[L]? = some b) {L' : Nat} (hL : L < L') (i : Nat) :
    f.left L' 0 < f.left L i := by
  have h1 := at_lt hb i
  have h2 := before_mono f (show L + 1 ≤ L' by omega)
  have h3 := before_le f L'
  simp only [left] at h1 ⊢
  omega

theorem left_pos (hb : f.blocks[L]? = some b) (i : Nat) : 0 < f.left L i := by
  have h1 := at_lt hb i
  have h2 := before_le f (L + 1)
  simp only [left]
  omega

end Func

theorem Program.left_le (p : Program ρ) (fn L i : Nat) : p.left fn L i ≤ p.size := by
  unfold Program.left
  split
  · rename_i f hf
    refine Nat.le_trans (f.left_le L i) ?_
    rw [Program.size_eq]
    exact le_sum_of_getElem? (i := fn) (by simp [hf])
  · exact Nat.zero_le _

theorem Program.left_of {p : Program ρ} {fn : Nat} {f : Func ρ} (hf : p.funcs[fn]? = some f) (L i : Nat) :
    p.left fn L i = f.left L i := by
  simp [Program.left, hf]

/-! ## Moves -/

/-- The shape of a `next` step on the positions of the frames (function,
label, instruction): past an instruction, a call, an edge, a return or a
tail call. -/
inductive Move (p : Program ρ) : List (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool → Prop
  | inst {fn L i : Nat} {rest : List (Nat × Nat × Nat)} {f : Func ρ} {b : Block ρ} :
      p.funcs[fn]? = some f → f.blocks[L]? = some b → i < b.body.size →
      Move p ((fn, L, i) :: rest) ((fn, L, i + 1) :: rest) false
  | call {fn L i : Nat} {rest : List (Nat × Nat × Nat)} {f : Func ρ} {b : Block ρ} (callee : Nat × Nat × Nat) :
      p.funcs[fn]? = some f → f.blocks[L]? = some b → i < b.body.size →
      Move p ((fn, L, i) :: rest) (callee :: (fn, L, i + 1) :: rest) true
  | edge {fn L i L' : Nat} {rest : List (Nat × Nat × Nat)} {f : Func ρ} {b b' : Block ρ} :
      p.funcs[fn]? = some f → f.blocks[L]? = some b → f.blocks[L']? = some b' →
      Move p ((fn, L, i) :: rest) ((fn, L', 0) :: rest) (decide (L' ≤ L))
  | ret {fn L i : Nat} {f : Func ρ} {b : Block ρ} (caller : Nat × Nat × Nat) {rest : List (Nat × Nat × Nat)} :
      p.funcs[fn]? = some f → f.blocks[L]? = some b →
      Move p ((fn, L, i) :: caller :: rest) (caller :: rest) false
  | tail (top callee : Nat × Nat × Nat) {rest : List (Nat × Nat × Nat)} :
      Move p (top :: rest) (callee :: rest) true

/-- A free move lowers the potential; any move raises it by at most the
program's size. -/
theorem Move.potential {p : Program ρ} {st st' : List (Nat × Nat × Nat)} {c : Bool} (h : Move p st st' c) :
    (c = false → p.potential st' < p.potential st) ∧ p.potential st' ≤ p.potential st + p.size := by
  cases h with
  | inst hf hb hi =>
    rename_i fn L i rest f b
    have := Func.left_succ hb hi
    simp only [Program.potential, List.map_cons, List.sum_cons, Program.left_of hf]
    omega
  | call callee hf hb hi =>
    rename_i fn L i rest f b
    have h1 := Func.left_succ hb hi
    have h2 := p.left_le callee.1 callee.2.1 callee.2.2
    simp only [Program.potential, List.map_cons, List.sum_cons, Program.left_of hf]
    refine ⟨(fun h => nomatch h), ?_⟩
    omega
  | edge hf hb hb' =>
    rename_i fn L i L' rest f b b'
    have h2 := p.left_le fn L' 0
    refine ⟨fun hc => ?_, ?_⟩
    · have hL : L < L' := by simpa using hc
      have := Func.left_fwd hb hL i
      simp only [Program.potential, List.map_cons, List.sum_cons, Program.left_of hf]
      omega
    · simp only [Program.potential, List.map_cons, List.sum_cons] at h2 ⊢
      omega
  | ret caller hf hb =>
    rename_i fn L i f b rest
    have := Func.left_pos hb i
    simp only [Program.potential, List.map_cons, List.sum_cons, Program.left_of hf]
    omega
  | tail top callee =>
    have := p.left_le callee.1 callee.2.1 callee.2.2
    simp only [Program.potential, List.map_cons, List.sum_cons]
    refine ⟨(fun h => nomatch h), ?_⟩
    omega

/-- Fuel `(2k + 3)·(size + 1)` covers a potential of at most `size` and `k`
charges of at most `size` each. -/
theorem fuel_enough {φ size k : Nat} (h : φ ≤ size) : φ + k * (size + 1) < (2 * k + 3) * (size + 1) := by
  rw [Nat.add_mul, Nat.mul_assoc]
  omega

/-! ## Xv -/

/-- A frame's position: function, label, instruction. -/
def lirPos (fr : Lir.Frame) : Nat × Nat × Nat := (fr.fn, fr.label, fr.pos)

theorem xv_edge_move {p : VProgram} {f : Func VReg} {s s' : Lir.State} {fr : Lir.Frame}
    {rest : List Lir.Frame} {ρ : Lir.Env} {e : Edge VReg} {c : Bool} {blk : Block VReg}
    (hf : p.funcs[fr.fn]? = some f) (hb : f.blocks[fr.label]? = some blk)
    (h : Xv.takeEdge f s fr rest ρ e = .next s' c) :
    Move p ((fr :: rest).map lirPos) (s'.stack.map lirPos) c := by
  obtain ⟨vals, b', ρ', -, hb', -, rfl, rfl⟩ := Validate.takeEdge_next h
  exact Move.edge hf hb hb'

/-- Every Xv `next` step is a move. -/
theorem xv_move {p : VProgram} {s s' : Lir.State} {c : Bool} (h : Xv.step p s = .next s' c) :
    Move p (s.stack.map lirPos) (s'.stack.map lirPos) c := by
  unfold Xv.step at h
  cases hst : s.stack with
  | nil => simp [hst] at h
  | cons fr rest =>
  simp only [hst] at h
  cases hf : p.funcs[fr.fn]? with
  | none => simp [hf] at h
  | some f =>
  simp only [hf] at h
  cases hb : f.blocks[fr.label]? with
  | none => simp [hb] at h
  | some blk =>
  simp only [hb] at h
  by_cases hpos : fr.pos < blk.body.size
  · simp only [hpos, ↓reduceDIte] at h
    split at h
    · split at h
      · simp only [Sem.Step.next.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Move.call _ hf hb hpos
      · simp at h
    · split at h
      · simp only [Sem.Step.next.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Move.inst hf hb hpos
      · simp at h
  · simp only [hpos, ↓reduceDIte] at h
    cases hT : blk.term with
    | jmp e =>
      simp only [hT] at h
      exact xv_edge_move hf hb h
    | jcc p' pargs defs cond e₁ e₂ =>
      simp only [hT] at h
      split at h
      · exact xv_edge_move hf hb h
      · simp at h
    | ret vs =>
      simp only [hT] at h
      split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · simp only [Sem.Step.next.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact Move.ret _ hf hb
          · simp at h
    | tail g' args =>
      simp only [hT] at h
      split at h
      · simp only [Sem.Step.next.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Move.tail _ _
      · simp at h
    | fail r => simp [hT] at h
    | trap => simp [hT] at h

/-- The potential of an Xv state: the positions left to its frames. -/
def potential (p : VProgram) (s : Lir.State) : Nat := p.potential (s.stack.map lirPos)

theorem potential_step (p : VProgram) :
    Sem.Potential (Xv.step p) (fun _ => True) (potential p) p.size where
  free _ h := ⟨trivial, (xv_move h).potential.1 rfl⟩
  charge _ h := ⟨trivial, (xv_move h).potential.2⟩

/-- `Xv.eval` from an initial state is its clocked outcome. -/
theorem runs_eval {p : VProgram} {args : List Word} {mem : X86.Memory} {ctx : Word} {s : Lir.State}
    (h : Xv.State.initial p args mem ctx = some s) :
    Sem.Runs (Xv.step p) s (fun k => Xv.eval p k args mem ctx) := by
  have hφ : potential p s ≤ p.size := by
    simp only [Xv.State.initial, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨fr, -, rfl⟩ := h
    simpa [potential, Program.potential, lirPos] using p.left_le fr.fn fr.label fr.pos
  have := (potential_step p).runs (s := s) trivial (fuel := fun k => Xv.fuelFor p k)
    (fun k => fuel_enough hφ)
  intro k
  simpa [Xv.eval, h] using this k

/-- `Xv.eval` is clock monotone. -/
theorem eval_mono (p : VProgram) (args : List Word) (mem : X86.Memory) (ctx : Word) :
    Sem.ClockMono (fun k => Xv.eval p k args mem ctx) := by
  cases h : Xv.State.initial p args mem ctx with
  | none => intro k k' _ _; simp [Xv.eval, h]
  | some s => exact (runs_eval h).clockMono

/-! ## Xl -/

namespace Xl

theorem write_ctl {regs regs' : Regs} {fr fr' : Frame} {l : Loc} {v : Word}
    (h : write regs fr l v = some (regs', fr')) : fr'.fn = fr.fn ∧ fr'.label = fr.label := by
  cases l with
  | reg r =>
    simp only [write] at h
    split at h
    · simp at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ⟨rfl, rfl⟩
  | slot i =>
    simp only [write, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | inArg i =>
    simp only [write] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ⟨rfl, rfl⟩
    · simp at h
  | outArg i =>
    simp only [write, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨rfl, rfl⟩

theorem writeAll_ctl : ∀ {regs : Regs} {fr : Frame} {ls : List Loc} {vs : List Word} {regs' : Regs}
    {fr' : Frame}, writeAll regs fr ls vs = some (regs', fr') → fr'.fn = fr.fn ∧ fr'.label = fr.label
  | _, _, [], [], _, _, h => by
      simp only [writeAll, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact ⟨rfl, rfl⟩
  | _, _, [], _ :: _, _, _, h => by simp [writeAll] at h
  | _, _, _ :: _, [], _, _, h => by simp [writeAll] at h
  | regs, fr, l :: ls, v :: vs, regs', fr', h => by
      simp only [writeAll, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨r₁, f₁⟩, hw, h⟩ := h
      have h₁ := write_ctl hw
      have h₂ := writeAll_ctl h
      exact ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩

theorem writeBacks_ctl {core : X86.Core} :
    ∀ {L : List (Loc × Option X86.GPR)} {acc res : Regs × Frame},
      L.foldlM (writeBack core) acc = some res → res.2.fn = acc.2.fn ∧ res.2.label = acc.2.label
  | [], acc, res, h => by
      simp only [List.foldlM_nil, pure, Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl⟩
  | x :: L, acc, res, h => by
      simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨r₁, f₁⟩, h₁, h₂⟩ := h
      obtain ⟨regs, fr⟩ := acc
      obtain ⟨l, r⟩ := x
      simp only [writeBack, Option.bind_eq_bind, Option.bind_eq_some_iff] at h₁
      obtain ⟨_, -, hw⟩ := h₁
      have e₁ := write_ctl hw
      have e₂ := writeBacks_ctl h₂
      exact ⟨e₂.1.trans e₁.1, e₂.2.trans e₁.2⟩

theorem execBound_ctl {parts : List (X86.Op × List (Bound Loc))} {regs : Regs} {fr : Frame}
    {mem : X86.Memory} {ctx : Word} {zf : Bool} {regs' : Regs} {fr' : Frame} {mem' : X86.Memory}
    {flags : X86.ByteEval.Flags} (h : execBound parts regs fr mem ctx zf = some (regs', fr', mem', flags)) :
    fr'.fn = fr.fn ∧ fr'.label = fr.label := by
  rw [Xl.execBound_eq] at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨_, -, _, -, _, -, _, -, _, -, _, -, _, -, rf, hrf, h⟩ := h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl, -, -⟩ := h
  exact writeBacks_ctl hrf

theorem execInst_ctl {regs : Regs} {fr : Frame} {mem : X86.Memory} {ctx : Word} {x : Inst Loc}
    {regs' : Regs} {fr' : Frame} {mem' : X86.Memory} (h : execInst regs fr mem ctx x = some (regs', fr', mem')) :
    fr'.fn = fr.fn ∧ fr'.label = fr.label := by
  cases x with
  | op o defs args =>
    simp only [execInst, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, -, ⟨r₁, f₁, m₁, fl₁⟩, hx, h⟩ := h
    simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    exact execBound_ctl hx
  | fused p pargs c defs cargs =>
    simp only [execInst, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, -, _, -, ⟨r₁, f₁, m₁, fl₁⟩, hx, h⟩ := h
    simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    exact execBound_ctl hx
  | move dst src =>
    simp only [execInst, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, -, ⟨r₁, f₁⟩, hw, h⟩ := h
    simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, -⟩ := h
    exact write_ctl hw
  | zero y =>
    simp only [execInst] at h
    split at h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨_, -, _, -, h⟩ := h
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      exact ⟨rfl, rfl⟩
    · simp at h
  | call g args rets => simp [execInst] at h

/-- A frame's position: function, label, instruction. -/
def xlPos (fr : Frame) : Nat × Nat × Nat := (fr.fn, fr.label, fr.pos)

theorem xl_edge_move {q : LProgram} {g : Func Loc} {s s' : State} {fr fr₀ : Frame} {rest : List Frame}
    {regs : Regs} {e : Edge Loc} {c : Bool} {blk : Block Loc}
    (hf : q.funcs[fr₀.fn]? = some g) (hb : g.blocks[fr₀.label]? = some blk)
    (hfn : fr.fn = fr₀.fn) (hlab : fr.label = fr₀.label)
    (h : takeEdge g s fr rest regs e = .next s' c) :
    Move q (xlPos fr₀ :: rest.map xlPos) (s'.stack.map xlPos) c := by
  unfold takeEdge at h
  split at h
  · rename_i vals target _ htarget
    split at h
    · rename_i regs' fr' hw
      simp only [Sem.Step.next.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have := writeAll_ctl hw
      simp only [List.map_cons, xlPos]
      rw [this.1, hfn, hlab]
      exact Move.edge hf hb htarget
    · simp at h
  · simp at h

/-- Every Xl `next` step is a move. -/
theorem xl_move {q : LProgram} {env : Env} {s s' : State} {c : Bool} (h : step q env s = .next s' c) :
    Move q (s.stack.map xlPos) (s'.stack.map xlPos) c := by
  unfold step at h
  cases hst : s.stack with
  | nil => simp [hst] at h
  | cons fr rest =>
  simp only [hst] at h
  cases hf : q.funcs[fr.fn]? with
  | none => simp [hf] at h
  | some g =>
  simp only [hf] at h
  cases hb : g.blocks[fr.label]? with
  | none => simp [hb] at h
  | some blk =>
  simp only [hb] at h
  by_cases hpos : fr.pos < blk.body.size
  · simp only [hpos, ↓reduceDIte] at h
    split at h
    · split at h
      · simp at h
      · split at h
        · simp only [Sem.Step.next.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact Move.call _ hf hb hpos
        · simp at h
    · split at h
      · rename_i regs' fr' mem' hx
        simp only [Sem.Step.next.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have := execInst_ctl hx
        simp only [List.map_cons, xlPos]
        rw [this.1, this.2]
        exact Move.inst hf hb hpos
      · simp at h
  · simp only [hpos, ↓reduceDIte] at h
    cases hT : blk.term with
    | jmp e =>
      simp only [hT] at h
      exact xl_edge_move hf hb rfl rfl h
    | jcc p' pargs defs cond e₁ e₂ =>
      simp only [hT] at h
      split at h
      · rename_i regs' fr' mem' taken hrun
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hrun
        obtain ⟨_, -, ⟨r₁, f₁, m₁, fl₁⟩, hx, hrun⟩ := hrun
        simp only [pure, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨_, -, -, rfl, -, -⟩ := hrun
        have := execBound_ctl hx
        exact xl_edge_move hf hb this.1 this.2 h
      · simp at h
    | ret vs =>
      simp only [hT] at h
      split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · split at h
            · simp at h
            · simp only [Sem.Step.next.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact Move.ret _ hf hb
    | tail g' args =>
      simp only [hT] at h
      split at h
      · simp at h
      · split at h
        · simp only [Sem.Step.next.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact Move.tail _ _
        · simp at h
    | fail r => simp [hT] at h
    | trap => simp [hT] at h

/-- The potential of an Xl state: the positions left to its frames. -/
def potential (q : LProgram) (s : State) : Nat := q.potential (s.stack.map xlPos)

theorem potential_step (q : LProgram) (env : Env) :
    Sem.Potential (step q env) (fun _ => True) (potential q) q.size where
  free _ h := ⟨trivial, (xl_move h).potential.1 rfl⟩
  charge _ h := ⟨trivial, (xl_move h).potential.2⟩

/-- `Xl.eval` from an initial state is its clocked outcome. -/
theorem runs_eval {q : LProgram} {env : Env} {args : List Word} {mem : X86.Memory} {ctx : Word}
    {s : State} (h : State.initial q args mem ctx = some s) :
    Sem.Runs (step q env) s (fun k => eval q env k args mem ctx) := by
  have hφ : potential q s ≤ q.size := by
    simp only [State.initial, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨⟨fr, regs⟩, -, rfl⟩ := h
    simpa [potential, Program.potential, xlPos] using q.left_le fr.fn fr.label fr.pos
  have := (potential_step q env).runs (s := s) trivial (fuel := fun k => fuelFor q k)
    (fun k => fuel_enough hφ)
  intro k
  simpa [eval, h] using this k

/-- `Xl.eval` is clock monotone. -/
theorem eval_mono (q : LProgram) (env : Env) (args : List Word) (mem : X86.Memory) (ctx : Word) :
    Sem.ClockMono (fun k => eval q env k args mem ctx) := by
  cases h : State.initial q args mem ctx with
  | none => intro k k' _ _; simp [eval, h]
  | some s => exact (runs_eval h).clockMono

end Xl

end Compilatrix.Xv
