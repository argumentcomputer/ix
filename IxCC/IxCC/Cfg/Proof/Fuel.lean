import IxCC.Cfg.Semantics
import IxCC.Sem.Smallstep

/-!
# Fuel for Cfg runs

`Cfg.run` runs `Sem.runClocked` with the step bound `fuelFor P k = (2k +
6)·(instrs + 1)` (`Cfg.Semantics`). This module proves it
sufficient: under `Cfg.Ordered P` (every forward edge goes to a
higher label, and every function of the program is counted in `instrs`),
the positions left to the frames form a `Sem.Potential` with bound
`1 + instrs` (`Cfg.potential_step`), so

* every `Cfg.run` is the clocked outcome of its steps (`Cfg.runs_run`), the
  connective `Sem.Diagram.sim` and `Sem.Sim.ofStar` take for a small-step
  side, and
* `Cfg.run` is clock monotone (`Cfg.run_mono`).

`Cfg.lower_correct` (by `Sim.ofStar`) and `Rt.lower_correct` (by a forward
diagram) both use it.

**The potential.** A frame at block `b` with `rest` left in it has
`2 + |rest| + Σ_{j > b} (|body j| + 1)` positions left: an instruction
removes one, a forward edge (to a higher label, by `Ordered`) lands in a
later block, and leaving the frame (`ret`, `tcall`) costs at most what is
left. A call leaves its caller one position lower, a `ret` state counts
one, and the charged steps (entering a function, taking a back edge) start
a fresh frame of at most `1 + size` positions.
-/

set_option autoImplicit false

namespace IxCC.Cfg

open IxCC.Sem (Result)
open IxCC.Own (AllocPol)
open IxCC.Fir (FunId)

/-- What the step bound needs of a program: forward edges go to higher
labels (`Cfg.lower`'s numbering, checked by `Cfg.WellFormed` and by
`Rt.lower`), and every function is below `size`, so `instrs` counts it. -/
structure Ordered (P : Program) : Prop where
  forward : ∀ {f : FunId} {fd : Fun} {b : BlockId} {blk : Block} {e : Edge}, P.fun? f = some fd →
    fd.block? b = some blk → e ∈ blk.term.edges → e.back = false → b < e.target
  dense : ∀ {f : FunId} {fd : Fun}, P.fun? f = some fd → f < P.size

/-! ## Sizes -/

/-- A block's positions: its instructions and its terminator. -/
def Block.positions (b : Block) : Nat := b.body.length + 1

theorem foldl_add_eq {α : Type} (g : α → Nat) :
    ∀ (l : List α) (n : Nat), l.foldl (fun n b => n + g b) n = n + (l.map g).sum
  | [], n => by simp
  | b :: l, n => by simp [foldl_add_eq g l, Nat.add_assoc]

theorem Fun.size_eq (fd : Fun) : fd.size = (fd.blocks.map Block.positions).sum := by
  have := foldl_add_eq Block.positions fd.blocks 0
  simp only [Nat.zero_add, Block.positions] at this
  simp only [Fun.size, ← this, Nat.add_assoc]

/-- The positions of the blocks after `b`. -/
def Fun.after (fd : Fun) (b : BlockId) : Nat := ((fd.blocks.map Block.positions).drop (b + 1)).sum

theorem sum_drop_le : ∀ (l : List Nat) {m n : Nat}, m ≤ n → (l.drop n).sum ≤ (l.drop m).sum
  | [], _, _, _ => by simp
  | x :: l, 0, 0, _ => Nat.le_refl _
  | x :: l, 0, n + 1, _ => by
    have := sum_drop_le l (Nat.zero_le n)
    simp only [List.drop_succ_cons, List.drop_zero, List.sum_cons] at this ⊢
    omega
  | x :: l, m + 1, n + 1, h => by
    simpa using sum_drop_le l (Nat.le_of_succ_le_succ h)

theorem sum_drop_eq : ∀ {l : List Nat} {t x : Nat}, l[t]? = some x →
    (l.drop t).sum = x + (l.drop (t + 1)).sum
  | [], _, _, h => by simp at h
  | y :: l, 0, x, h => by simp at h; subst h; simp
  | y :: l, t + 1, x, h => by
    simpa using sum_drop_eq (l := l) (t := t) (by simpa using h)

theorem le_sum_of_mem : ∀ {l : List Nat} {x : Nat}, x ∈ l → x ≤ l.sum
  | [], _, h => by simp at h
  | y :: l, x, h => by
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · have := le_sum_of_mem h
      simp only [List.sum_cons]
      omega

theorem Fun.block?_positions {fd : Fun} {t : BlockId} {blk : Block} (h : fd.block? t = some blk) :
    (fd.blocks.map Block.positions)[t]? = some blk.positions := by
  simp only [Fun.block?] at h
  simp [h]

/-- A block's fresh frame has at most `1 + size` positions. -/
theorem Fun.fresh_le {fd : Fun} {t : BlockId} {blk : Block} (h : fd.block? t = some blk) :
    blk.body.length + fd.after t + 1 ≤ fd.size := by
  have h1 := sum_drop_eq (Fun.block?_positions h)
  have h2 := sum_drop_le (fd.blocks.map Block.positions) (Nat.zero_le t)
  simp only [List.drop_zero] at h2
  rw [Fun.size_eq]
  simp only [Fun.after, Block.positions] at h1 h2 ⊢
  omega

/-- A later block's fresh frame has fewer positions than any frame of an
earlier block. -/
theorem Fun.fresh_lt {fd : Fun} {b t : BlockId} {blk : Block} (h : fd.block? t = some blk)
    (hbt : b < t) : blk.body.length + fd.after t + 1 ≤ fd.after b := by
  have h1 := sum_drop_eq (Fun.block?_positions h)
  have hle : b + 1 ≤ t := hbt
  have h2 := sum_drop_le (fd.blocks.map Block.positions) hle
  simp only [Fun.after, Block.positions] at h1 h2 ⊢
  omega

/-! ## The potential -/

/-- Positions left to a frame. -/
def framePot (P : Program) (fr : Frame) : Nat :=
  2 + fr.rest.length + ((P.fun? fr.fn).map (·.after fr.blk)).getD 0

def stackPot (P : Program) (stk : List (Frame × Fir.Var)) : Nat := (stk.map (framePot P ·.1)).sum

def potential (P : Program) : State → Nat
  | .call _ _ stk _ => stackPot P stk
  | .run fr stk _ => framePot P fr + stackPot P stk
  | .ret _ stk _ => 1 + stackPot P stk

theorem takeEdge_next {fd : Fun} {fr : Frame} {stk : List (Frame × Fir.Var)} {H : Own.Heap} {e : Edge}
    {s' : State} {c : Bool} (h : takeEdge fd fr stk H e = .next s' c) :
    ∃ blk env, fd.block? e.target = some blk ∧
      s' = .run { fr with blk := e.target, rest := blk.body, env } stk H ∧ c = e.back := by
  unfold takeEdge at h
  split at h
  · rename_i b vs hb _
    split at h
    · simp only [Sem.Step.next.injEq] at h
      exact ⟨b, _, hb, h.1.symm, h.2.symm⟩
    · simp at h
  · simp at h

theorem mem_edges_of_select {key : Key.CtorKey} :
    ∀ {alts : List (Key.CtorKey × Edge)} {d : Option Edge} {e : Edge},
      selectEdge key alts d = some e → e ∈ alts.map (·.2) ++ d.toList
  | [], d, e, h => by simp only [selectEdge] at h; simp [h]
  | (k, e') :: alts, d, e, h => by
    simp only [selectEdge] at h
    split at h
    · cases h; simp
    · have := mem_edges_of_select h
      simp only [List.mem_append, List.mem_map, Option.mem_toList] at this ⊢
      rcases this with ⟨a, ha, rfl⟩ | hd
      · exact .inl ⟨a, by simp [ha], rfl⟩
      · exact .inr hd

/-- Each step keeps the potential's discipline: a free step lowers it and a
charge raises it by at most `1 + B`, where `B` bounds every function's
size. -/
theorem potential_next {pol : AllocPol} {P : Program} (hP : ∀ {f fd}, P.fun? f = some fd → ∀ {b blk e},
      fd.block? b = some blk → e ∈ blk.term.edges → e.back = false → b < e.target)
    {B : Nat} (hB : ∀ {f fd}, P.fun? f = some fd → fd.size ≤ B)
    {s s' : State} {c : Bool} (h : step pol P s = .next s' c) :
    (c = false → potential P s' < potential P s) ∧ potential P s' ≤ potential P s + (1 + B) := by
  -- the edge cases share one argument
  have edge : ∀ {fr : Frame} {stk : List (Frame × Fir.Var)} {H : Own.Heap} {fd : Fun} {b : Block} {e : Edge},
      P.fun? fr.fn = some fd → fd.block? fr.blk = some b → e ∈ b.term.edges → fr.rest = [] →
      takeEdge fd fr stk H e = .next s' c →
      (c = false → potential P s' < potential P (.run fr stk H)) ∧
        potential P s' ≤ potential P (.run fr stk H) + (1 + B) := by
    intro fr stk H fd b e hf hb he hrest ht
    obtain ⟨blk, env, hblk, rfl, rfl⟩ := takeEdge_next ht
    simp only [potential, framePot, hf, hrest, List.length_nil, Option.map_some, Option.getD_some]
    have hfresh := Fun.fresh_le hblk
    have hsize := hB hf
    refine ⟨fun hback => ?_, by omega⟩
    have := Fun.fresh_lt hblk (hP hf hb he hback)
    omega
  cases s with
  | call f args stk H =>
    simp only [step] at h
    split at h
    · rename_i fd hf
      split at h
      · rename_i b hb
        split at h
        · simp only [Sem.Step.next.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hfresh := Fun.fresh_le hb
          have hsize := hB hf
          refine ⟨(fun h => nomatch h), ?_⟩
          simp only [potential, framePot, hf, Option.map_some, Option.getD_some]
          omega
        · simp at h
      · simp at h
    · simp at h
  | ret v stk H =>
    cases stk with
    | nil => simp [step] at h
    | cons top stk =>
      obtain ⟨fr, x⟩ := top
      simp only [step, Sem.Step.next.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [potential, stackPot, List.map_cons, List.sum_cons, framePot]
      refine ⟨fun _ => by omega, by omega⟩
  | run fr stk H =>
    simp only [step] at h
    split at h
    · -- a call
      rename_i x g as is hrest
      split at h
      · simp only [Sem.Step.next.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [potential, stackPot, List.map_cons, List.sum_cons, framePot, hrest,
          List.length_cons]
        refine ⟨fun _ => by omega, by omega⟩
      · simp at h
    · -- another instruction
      rename_i x r is _ hrest
      split at h
      · simp only [Sem.Step.next.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [potential, framePot, hrest, List.length_cons]
        refine ⟨fun _ => by omega, by omega⟩
      all_goals simp at h
    · -- the terminator
      rename_i hrest
      split at h
      · rename_i fd hf
        split at h
        · rename_i b hb
          split at h
          · rename_i e hT
            exact edge hf hb (by simp [hT, Term.edges]) hrest h
          · rename_i x alts d hT
            split at h
            · split at h
              · split at h
                · rename_i e he
                  refine edge hf hb ?_ hrest h
                  rw [hT]
                  exact mem_edges_of_select he
                · simp at h
              · simp at h
            · simp at h
          · split at h
            · simp only [Sem.Step.next.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              simp only [potential, framePot, hf, hrest, List.length_nil, Option.map_some,
                Option.getD_some]
              refine ⟨fun _ => by omega, by omega⟩
            · simp at h
          · split at h
            · simp only [Sem.Step.next.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              simp only [potential, framePot, hf, hrest, List.length_nil, Option.map_some,
                Option.getD_some]
              refine ⟨fun _ => by omega, by omega⟩
            · simp at h
          · simp at h
        · simp at h
      · simp at h

/-- Every function of an ordered program is counted in `instrs`. -/
theorem size_le_instrs {P : Program} (hP : Ordered P) {f : FunId} {fd : Fun} (hf : P.fun? f = some fd) :
    fd.size ≤ P.instrs := by
  have hmem : (f, fd) ∈ P.funList := by
    simp only [Program.funList, List.mem_filterMap, List.mem_range, Option.map_eq_some_iff,
      Prod.mk.injEq]
    exact ⟨f, hP.dense hf, fd, hf, rfl, rfl⟩
  have := foldl_add_eq (fun (x : FunId × Fun) => x.2.size) P.funList 0
  simp only [Nat.zero_add] at this
  simp only [Program.instrs, this]
  exact le_sum_of_mem (List.mem_map_of_mem hmem)

theorem potential_step (pol : AllocPol) {P : Program} (hP : Ordered P) :
    Sem.Potential (step pol P) (fun _ => True) (potential P) (1 + P.instrs) where
  free _ h := ⟨trivial, (potential_next (fun hf _ _ _ hb he hback => hP.forward hf hb he hback)
    (fun hf => size_le_instrs hP hf) h).1 rfl⟩
  charge _ h := ⟨trivial, (potential_next (fun hf _ _ _ hb he hback => hP.forward hf hb he hback)
    (fun hf => size_le_instrs hP hf) h).2⟩

/-- `fuelFor` covers clock `k` from a state with no suspended callers. -/
theorem fuel_enough (P : Program) (k : Nat) : 0 + k * (1 + P.instrs + 1) < fuelFor P k := by
  unfold fuelFor
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one]
  have : 2 * k * P.instrs = 2 * (k * P.instrs) := Nat.mul_assoc 2 k P.instrs
  omega

/-- **`Cfg.run` is the clocked outcome of its steps** (the step bound is
enough), for every entry, argument list and heap of an ordered program. -/
theorem runs_run (pol : AllocPol) {P : Program} (hP : Ordered P) (f : FunId) (args : List Own.RVal)
    (H : Own.Heap) :
    Sem.Runs (step pol P) (.call f args [] H) (fun k => run pol P k f args H) := fun k =>
  (potential_step pol hP).runClocked (s := .call f args [] H) trivial
    (by simpa [potential, stackPot] using fuel_enough P k)

/-- `Cfg.run` is clock monotone on ordered programs. -/
theorem run_mono (pol : AllocPol) {P : Program} (hP : Ordered P) (f : FunId) (args : List Own.RVal)
    (H : Own.Heap) : Sem.ClockMono (fun k => run pol P k f args H) :=
  (runs_run pol hP f args H).clockMono

end IxCC.Cfg
