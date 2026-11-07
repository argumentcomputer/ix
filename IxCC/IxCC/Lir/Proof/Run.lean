import IxCC.Lir.Semantics
import IxCC.Sem.Smallstep

/-!
# Lir's run loop is the shared clocked runner

`Lir.run` is its own copy of `Sem.runClocked` (`Lir.Semantics`), with the
final step `done vals mem` in place of `done (vals, mem)`. This module
proves the two loops equal (`Lir.run_eq_runClocked`), so the small-step core
of `IxCC.Sem` (`Star`, `Reaches`, `Potential`, `Runs`, `Diagram`,
`Sim.ofStar`) applies to Lir through `Lir.semStep`.

It also proves the step bound sufficient: between two charges an activation
moves forward through its function, so the positions left to the frames are
a `Sem.Potential` with bound `size` (`Lir.potential_step`), and the fuel
`(2k + 3)·(size + 1)` of `Lir.eval` outlasts clock `k`. Every `Lir.eval` is
therefore the clocked outcome of its steps (`Lir.runs_eval`) and clock
monotone (`Lir.eval_mono`). The argument is the one of
`Xv.Validate.Proof.Fuel`, on Lir's own syntax.
-/

namespace IxCC.Lir

/-! ## The loop -/

/-- A Lir step as a step of the shared runner: `done vals mem` is the value
`(vals, mem)`. -/
def Step.toSem : Step → Sem.Step State (List Word × X86.Memory)
  | .next s c => .next s c
  | .done vals mem => .done (vals, mem)
  | .fail r => .fail r
  | .trap => .trap
  | .stuck => .stuck

/-- Lir's step function in the shared vocabulary. -/
def semStep (p : Program) (s : State) : Sem.Step State (List Word × X86.Memory) :=
  (step p s).toSem

@[simp] theorem semStep_next {p : Program} {s s' : State} {c : Bool} :
    semStep p s = .next s' c ↔ step p s = .next s' c := by
  unfold semStep
  cases step p s <;> simp [Step.toSem]

@[simp] theorem semStep_fail {p : Program} {s : State} {r : Sem.Resource} :
    semStep p s = .fail r ↔ step p s = .fail r := by
  unfold semStep
  cases step p s <;> simp [Step.toSem]

@[simp] theorem semStep_trap {p : Program} {s : State} : semStep p s = .trap ↔ step p s = .trap := by
  unfold semStep
  cases step p s <;> simp [Step.toSem]

@[simp] theorem semStep_done {p : Program} {s : State} {vals : List Word} {mem : X86.Memory} :
    semStep p s = .done (vals, mem) ↔ step p s = .done vals mem := by
  unfold semStep
  cases step p s <;> simp [Step.toSem]

/-- `Lir.run` is `Sem.runClocked` over `semStep`. -/
theorem run_eq_runClocked (p : Program) :
    ∀ (fuel k : Nat) (s : State), run p fuel k s = Sem.runClocked (semStep p) fuel k s
  | 0, _, _ => rfl
  | fuel + 1, k, s => by
    unfold run Sem.runClocked semStep
    cases step p s with
    | next s' c =>
      cases c with
      | false => exact run_eq_runClocked p fuel k s'
      | true =>
        cases k with
        | zero => rfl
        | succ k => exact run_eq_runClocked p fuel k s'
    | done vals mem => rfl
    | fail r => rfl
    | trap => rfl
    | stuck => rfl

/-- `Lir.eval` through the shared runner. -/
theorem eval_eq (p : Program) (k : Nat) (args : List Word) (mem : X86.Memory) (ctx : Word) :
    eval p k args mem ctx =
      match State.initial p args mem ctx with
      | some s => Sem.runClocked (semStep p) (fuelFor p k) k s
      | none => .stuck := by
  cases h : State.initial p args mem ctx <;> simp [eval, h, run_eq_runClocked]

/-! ## Positions left -/

/-- The block sizes before label `L`. -/
def Func.before (f : Func) (L : Nat) : Nat := ((f.blocks.toList.map Block.size).take L).sum

/-- The body size of block `L`, or zero. -/
def Func.bodyAt (f : Func) (L : Nat) : Nat := (f.blocks[L]?.map (·.body.size)).getD 0

/-- Positions left in `f` going forward from label `L`, statement `i`. -/
def Func.left (f : Func) (L i : Nat) : Nat := f.size - (f.before L + min i (f.bodyAt L))

/-- Positions left in function `fn` of `p`. -/
def Program.left (p : Program) (fn L i : Nat) : Nat :=
  match p.funcs[fn]? with
  | some f => f.left L i
  | none => 0

/-- The potential of a stack of positions (function, label, statement). -/
def Program.potential (p : Program) (st : List (Nat × Nat × Nat)) : Nat :=
  (st.map fun x => p.left x.1 x.2.1 x.2.2).sum

theorem foldl_add_eq {α : Type} (g : α → Nat) :
    ∀ (l : List α) (n : Nat), l.foldl (fun n b => n + g b) n = n + (l.map g).sum
  | [], n => by simp
  | b :: l, n => by simp [foldl_add_eq g l, Nat.add_assoc]

theorem Func.size_eq (f : Func) : f.size = (f.blocks.toList.map Block.size).sum := by
  simp [Func.size, ← Array.foldl_toList, foldl_add_eq]

theorem Program.size_eq (p : Program) : p.size = (p.funcs.toList.map Func.size).sum := by
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

variable {f : Func} {L : Nat} {b : Block}

theorem before_le (f : Func) (L : Nat) : f.before L ≤ f.size := by
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

theorem before_mono (f : Func) {L L' : Nat} (h : L ≤ L') : f.before L ≤ f.before L' := by
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

theorem left_le (f : Func) (L i : Nat) : f.left L i ≤ f.size := Nat.sub_le _ _

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

theorem Program.left_le (p : Program) (fn L i : Nat) : p.left fn L i ≤ p.size := by
  unfold Program.left
  split
  · rename_i f hf
    refine Nat.le_trans (f.left_le L i) ?_
    rw [Program.size_eq]
    exact le_sum_of_getElem? (i := fn) (by simp [hf])
  · exact Nat.zero_le _

theorem Program.left_of {p : Program} {fn : Nat} {f : Func} (hf : p.funcs[fn]? = some f) (L i : Nat) :
    p.left fn L i = f.left L i := by
  simp [Program.left, hf]

/-! ## Moves -/

/-- The shape of a `next` step on the positions of the frames (function,
label, statement): past a statement, a call, an edge, a return or a tail
call. -/
inductive Move (p : Program) : List (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool → Prop
  | stmt {fn L i : Nat} {rest : List (Nat × Nat × Nat)} {f : Func} {b : Block} :
      p.funcs[fn]? = some f → f.blocks[L]? = some b → i < b.body.size →
      Move p ((fn, L, i) :: rest) ((fn, L, i + 1) :: rest) false
  | call {fn L i : Nat} {rest : List (Nat × Nat × Nat)} {f : Func} {b : Block} (callee : Nat × Nat × Nat) :
      p.funcs[fn]? = some f → f.blocks[L]? = some b → i < b.body.size →
      Move p ((fn, L, i) :: rest) (callee :: (fn, L, i + 1) :: rest) true
  | edge {fn L i L' : Nat} {rest : List (Nat × Nat × Nat)} {f : Func} {b b' : Block} :
      p.funcs[fn]? = some f → f.blocks[L]? = some b → f.blocks[L']? = some b' →
      Move p ((fn, L, i) :: rest) ((fn, L', 0) :: rest) (decide (L' ≤ L))
  | ret {fn L i : Nat} {f : Func} {b : Block} (caller : Nat × Nat × Nat) {rest : List (Nat × Nat × Nat)} :
      p.funcs[fn]? = some f → f.blocks[L]? = some b →
      Move p ((fn, L, i) :: caller :: rest) (caller :: rest) false
  | tail (top callee : Nat × Nat × Nat) {rest : List (Nat × Nat × Nat)} :
      Move p (top :: rest) (callee :: rest) true

/-- A free move lowers the potential; any move raises it by at most the
program's size. -/
theorem Move.potential {p : Program} {st st' : List (Nat × Nat × Nat)} {c : Bool} (h : Move p st st' c) :
    (c = false → p.potential st' < p.potential st) ∧ p.potential st' ≤ p.potential st + p.size := by
  cases h with
  | stmt hf hb hi =>
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

/-- A frame's position: function, label, statement. -/
def Frame.pos3 (fr : Frame) : Nat × Nat × Nat := (fr.fn, fr.label, fr.pos)

/-- What a `next` step of `takeEdge` is: the running frame at the target's
first statement, with the edge's charge. -/
theorem takeEdge_next {f : Func} {s s' : State} {fr : Frame} {rest : List Frame} {ρ : Env}
    {e : Edge} {c : Bool} (h : takeEdge f s fr rest ρ e = .next s' c) :
    ∃ target ρ', f.blocks[e.target]? = some target ∧
      s' = { s with stack := { fr with label := e.target, pos := 0, env := ρ' } :: rest } ∧
      c = decide (e.target ≤ fr.label) := by
  unfold takeEdge at h
  split at h
  · rename_i vals target _ htarget
    split at h
    · rename_i ρ' _
      simp only [Step.next.injEq] at h
      exact ⟨target, ρ', htarget, h.1.symm, h.2.symm⟩
    · simp at h
  · simp at h

theorem edge_move {p : Program} {f : Func} {s s' : State} {fr : Frame} {rest : List Frame} {ρ : Env}
    {e : Edge} {c : Bool} {blk : Block} (hf : p.funcs[fr.fn]? = some f) (hb : f.blocks[fr.label]? = some blk)
    (h : takeEdge f s fr rest ρ e = .next s' c) :
    Move p ((fr :: rest).map Frame.pos3) (s'.stack.map Frame.pos3) c := by
  obtain ⟨target, ρ', hb', rfl, rfl⟩ := takeEdge_next h
  exact Move.edge hf hb hb'

/-- Every Lir `next` step is a move. -/
theorem step_move {p : Program} {s s' : State} {c : Bool} (h : step p s = .next s' c) :
    Move p (s.stack.map Frame.pos3) (s'.stack.map Frame.pos3) c := by
  unfold step at h
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
      · simp only [Step.next.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Move.call _ hf hb hpos
      · simp at h
    · split at h
      · simp only [Step.next.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Move.stmt hf hb hpos
      · simp at h
  · simp only [hpos, ↓reduceDIte] at h
    cases hT : blk.term with
    | jump e =>
      simp only [hT] at h
      exact edge_move hf hb h
    | br c' w a b' t e =>
      simp only [hT] at h
      split at h
      · exact edge_move hf hb h
      · simp at h
    | brOvf o x a b' ok ovf =>
      simp only [hT] at h
      split at h
      · exact edge_move hf hb h
      · simp at h
    | ret as =>
      simp only [hT] at h
      split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · simp only [Step.next.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact Move.ret _ hf hb
          · simp at h
    | tail g as =>
      simp only [hT] at h
      split at h
      · simp only [Step.next.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Move.tail _ _
      · simp at h
    | fail r => simp [hT] at h
    | trap => simp [hT] at h

/-- The potential of a Lir state: the positions left to its frames. -/
def potential (p : Program) (s : State) : Nat := p.potential (s.stack.map Frame.pos3)

theorem potential_step (p : Program) :
    Sem.Potential (semStep p) (fun _ => True) (potential p) p.size where
  free _ h := ⟨trivial, (step_move (semStep_next.1 h)).potential.1 rfl⟩
  charge _ h := ⟨trivial, (step_move (semStep_next.1 h)).potential.2⟩

/-- A state with a single frame starts within the bound. -/
theorem potential_single (p : Program) {mem : X86.Memory} {ctx : Word} (fr : Frame) :
    potential p { mem, ctx, stack := [fr] } ≤ p.size := by
  simpa [potential, Program.potential, Frame.pos3] using p.left_le fr.fn fr.label fr.pos

/-- From a state within the bound, `run` with `fuelFor` fuel is the clocked
outcome of the steps. -/
theorem runs_of_potential {p : Program} {s : State} (hφ : potential p s ≤ p.size) :
    Sem.Runs (semStep p) s (fun k => run p (fuelFor p k) k s) := by
  have := (potential_step p).runs (s := s) trivial (fuel := fun k => fuelFor p k)
    (fun k => fuel_enough hφ)
  intro k
  simpa [run_eq_runClocked] using this k

/-- `Lir.eval` from an initial state is its clocked outcome. -/
theorem runs_eval {p : Program} {args : List Word} {mem : X86.Memory} {ctx : Word} {s : State}
    (h : State.initial p args mem ctx = some s) :
    Sem.Runs (semStep p) s (fun k => eval p k args mem ctx) := by
  have hφ : potential p s ≤ p.size := by
    simp only [State.initial, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨fr, -, rfl⟩ := h
    exact potential_single p fr
  intro k
  simpa [eval, h] using runs_of_potential hφ k

/-- `Lir.eval` is clock monotone. -/
theorem eval_mono (p : Program) (args : List Word) (mem : X86.Memory) (ctx : Word) :
    Sem.ClockMono (fun k => eval p k args mem ctx) := by
  cases h : State.initial p args mem ctx with
  | none => intro k k' _ _; simp [eval, h]
  | some s => exact (runs_eval h).clockMono

end IxCC.Lir
