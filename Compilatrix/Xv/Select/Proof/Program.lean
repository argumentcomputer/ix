import Compilatrix.Xv.Select.Proof.Block

/-!
# A selected program

`select_spec` and `run_spec`: selection keeps the program's functions and
their parameters, and each block is selected as `selectBlock_spec`
describes (`FuncSel`), with every register the function names below
`maxVReg f + 1`, the first fresh register. A function's folded registers
(`dead`) are read by none of its selected instructions: `selectFunc`
declines the function otherwise.
-/

namespace Compilatrix.Xv.Select.Proof

open Compilatrix.Lir (VReg Word Env)
open Compilatrix.Xv.Select

/-! ## State monads over `Except` -/

theorem tbind_ok {σ α β : Type} {f : StateT σ (Except Error) α} {g : α → StateT σ (Except Error) β} {s s'' : σ}
    {b : β} : (f >>= g) s = .ok (b, s'') ↔ ∃ a s', f s = .ok (a, s') ∧ g a s' = .ok (b, s'') := by
  show (do let (a, s) ← f s; g a s) = _ ↔ _
  cases h : f s with
  | error e => simp [bind, Except.bind]
  | ok p =>
    obtain ⟨a, s₁⟩ := p
    simp only [bind, Except.bind, Except.ok.injEq]
    constructor
    · intro hg; exact ⟨a, s₁, rfl, hg⟩
    · rintro ⟨a', s', he, hg⟩
      cases he
      exact hg

/-! ## Registers below the first fresh one -/

theorem foldl_max_ge : ∀ (L : List Nat) (init : Nat), init ≤ L.foldl max init
  | [], _ => Nat.le_refl _
  | a :: L, init => Nat.le_trans (Nat.le_max_left init a) (foldl_max_ge L (max init a))

theorem foldl_max_mem : ∀ {L : List Nat} {x : Nat} (init : Nat), x ∈ L → x ≤ L.foldl max init
  | [], _, _, h => absurd h (List.not_mem_nil)
  | a :: L, x, init, h => by
      rcases List.mem_cons.1 h with rfl | h
      · exact Nat.le_trans (Nat.le_max_right init x) (foldl_max_ge L _)
      · show x ≤ L.foldl max (max init a); exact foldl_max_mem _ h

/-- The registers a block names. -/
def blockRegs (b : Lir.Block) : List VReg :=
  b.params ++ b.body.toList.flatMap (fun s => s.uses ++ s.defs) ++ b.term.uses ++ b.term.defs ++ b.term.edgeUses

theorem foldl_blocks_ge : ∀ (bs : List Lir.Block) (g : Lir.Block → Nat) (init : Nat),
    init ≤ bs.foldl (fun m b => max m (g b)) init
  | [], _, _ => Nat.le_refl _
  | b :: bs, g, init => Nat.le_trans (Nat.le_max_left init (g b)) (foldl_blocks_ge bs g _)

theorem foldl_blocks_mem : ∀ {bs : List Lir.Block} {b : Lir.Block} (g : Lir.Block → Nat) (init : Nat), b ∈ bs →
    g b ≤ bs.foldl (fun m b => max m (g b)) init
  | [], _, _, _, h => absurd h (List.not_mem_nil)
  | b' :: bs, b, g, init, h => by
      rcases List.mem_cons.1 h with rfl | h
      · exact Nat.le_trans (Nat.le_max_right init (g b)) (foldl_blocks_ge bs g _)
      · show g b ≤ bs.foldl (fun m b => max m (g b)) (max init (g b')); exact foldl_blocks_mem g _ h

theorem maxVReg_params {f : Lir.Func} {u : VReg} (h : u ∈ f.params) : u < maxVReg f + 1 := by
  unfold maxVReg
  exact Nat.lt_succ_of_le (Nat.le_trans (foldl_max_mem 0 h) (foldl_blocks_ge _ _ _))

theorem maxVReg_block {f : Lir.Func} {l : Nat} {b : Lir.Block} (hb : f.blocks[l]? = some b) {u : VReg}
    (h : u ∈ blockRegs b) : u < maxVReg f + 1 := by
  unfold maxVReg
  refine Nat.lt_succ_of_le (Nat.le_trans (foldl_max_mem 0 h) ?_)
  exact foldl_blocks_mem (fun b => (blockRegs b).foldl max 0) _
    (Array.mem_toList_iff.2 (Array.mem_of_getElem? hb))

/-- Every register of the context's assignments is below `N`. -/
theorem ctxLow_block {f : Lir.Func} {l : Nat} {b : Lir.Block} (hb : f.blocks[l]? = some b) (fn : Lir.FunId)
    (uses : NatMap Nat) (label : Lir.Label) : CtxLow (blockCtx fn uses label b.body.toList) (maxVReg f + 1) := by
  intro y j r hd
  have hs := defSites_spec hd
  have hmem : Lir.Stmt.assign y r ∈ b.body.toList := List.mem_of_getElem? hs
  refine ⟨maxVReg_block hb ?_, fun u hu => maxVReg_block hb ?_⟩
  · simp only [blockRegs, List.mem_append, List.mem_flatMap]
    exact .inl (.inl (.inl (.inr ⟨_, hmem, by simp [Lir.Stmt.defs]⟩)))
  · simp only [blockRegs, List.mem_append, List.mem_flatMap]
    exact .inl (.inl (.inl (.inr ⟨_, hmem, by simp [Lir.Stmt.uses, hu]⟩)))


/-! ## Blocks and functions -/

theorem selectBlocks_spec {fn : Lir.FunId} {uses : NatMap Nat} :
    ∀ {L : List (Lir.Block × Lir.Label)} {st st' : St} {sel : List (Block VReg × List VReg)},
      selectBlocks fn uses L st = .ok (sel, st') →
      sel.length = L.length ∧ st.next ≤ st'.next ∧
        ∀ (k : Nat) b l, L[k]? = some (b, l) → ∃ stk stk' xbd, st.next ≤ stk.next ∧ sel[k]? = some xbd ∧
          selectBlock fn uses l b stk = .ok (xbd, stk')
  | [], st, st', sel, h => by
      simp only [selectBlocks, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, Nat.le_refl _, fun k b l h => by simp at h⟩
  | (b, l) :: rest, st, st', sel, h => by
      simp only [selectBlocks] at h
      rw [tbind_ok] at h
      obtain ⟨xbd, st₁, h₁, h⟩ := h
      rw [tbind_ok] at h
      obtain ⟨sel', st₂, h₂, h⟩ := h
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hn₁ := (selectBlock_spec h₁).1
      obtain ⟨hlen, hn₂, hsel⟩ := selectBlocks_spec h₂
      refine ⟨by simp [hlen], Nat.le_trans hn₁ hn₂, fun k b' l' hk => ?_⟩
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
        obtain ⟨rfl, rfl⟩ := hk
        exact ⟨st, st₁, xbd, Nat.le_refl _, rfl, h₁⟩
      | succ k =>
        simp only [List.getElem?_cons_succ] at hk
        obtain ⟨stk, stk', xbd', hle, hs, hb⟩ := hsel k b' l' hk
        exact ⟨stk, stk', xbd', Nat.le_trans hn₁ hle, by simpa using hs, hb⟩

theorem BlockSel.mono {c : Ctx} {n₀ n₁ : Nat} {term : Lir.Term} {segs : List (List (Inst VReg))}
    {pre : List (Inst VReg)} {xterm : Term VReg} {C : List Nat} (h : BlockSel c n₁ term segs pre xterm C)
    (hn : n₀ ≤ n₁) : BlockSel c n₀ term segs pre xterm C := by
  refine ⟨h.len, h.cons, h.skip, fun i s hs hi => ?_, ?_⟩
  · obtain ⟨sti, sti', seg, hle, hseg, hsl⟩ := h.stmt i s hs hi
    exact ⟨sti, sti', seg, Nat.le_trans hn hle, hseg, hsl⟩
  · obtain ⟨stT, stT', hle, hT⟩ := h.term
    exact ⟨stT, stT', Nat.le_trans hn hle, hT⟩

/-- What selection established for a function: its parameters, and each
block selected from a state whose fresh registers start at or above the
function's first, reading none of the function's folded registers `D`. -/
structure FuncSel (fn : Lir.FunId) (f : Lir.Func) (xf : Func VReg) (D : List VReg) : Prop where
  params : xf.params = f.params
  size : xf.blocks.size = f.blocks.size
  block : ∀ l b, f.blocks[l]? = some b → ∃ xb segs pre C, xf.blocks[l]? = some xb ∧ xb.params = b.params ∧
    BlockSel (blockCtx fn (useCounts f) l b.body.toList) (maxVReg f + 1) b.term segs pre xb.term C ∧
    xb.body.toList = segs.flatten ++ pre ∧ (∀ u ∈ consumedDefs b.body.toList C, u ∈ D) ∧ xb.avoids D = true

theorem selectFunc_spec {stats : Bool} {fn : Lir.FunId} {f : Lir.Func} {fired fired' : Std.TreeMap String Nat compare}
    {xf : Func VReg} (h : selectFunc stats fn f fired = .ok (xf, fired')) : ∃ D, FuncSel fn f xf D := by
  unfold selectFunc at h
  rw [tbind_ok] at h
  obtain ⟨d, s₁, h₀, h⟩ := h
  simp only [get, getThe, MonadStateOf.get, StateT.get, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h₀
  obtain ⟨rfl, rfl⟩ := h₀
  rw [tbind_ok] at h
  obtain ⟨⟨sel, st⟩, s₂, h₁, h⟩ := h
  cases hr : (selectBlocks fn (useCounts f) f.blocks.toList.zipIdx).run
      { next := maxVReg f + 1, fired := fired, stats := stats } with
  | error e =>
    rw [hr] at h₁
    cases h₁
  | ok p =>
    rw [hr] at h₁
    simp only [liftM, monadLift, MonadLift.monadLift, StateT.lift, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at h₁
    obtain ⟨rfl, rfl⟩ := h₁
    have hsb : selectBlocks fn (useCounts f) f.blocks.toList.zipIdx
        { next := maxVReg f + 1, fired := fired, stats := stats } = .ok (sel, st) := hr
    obtain ⟨hlen, -, hsel⟩ := selectBlocks_spec hsb
    simp only at h
    cases hf : List.find? (fun x => match x with | (b, _) => !Block.avoids (List.flatMap (fun x => x.snd) sel) b)
        (List.map (fun x => x.fst) sel).zipIdx with
    | some p =>
      obtain ⟨b, l⟩ := p
      rw [hf] at h
      simp only [throw, throwThe, MonadExceptOf.throw, StateT.instMonadExceptOf, bind, StateT.bind, Except.bind,
        StateT.lift] at h
      cases h
    | none =>
      rw [hf] at h
      simp only [set, MonadStateOf.set, StateT.set, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure,
        Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      refine ⟨List.flatMap (fun x => x.snd) sel, ⟨rfl, by simp [hlen], fun l b hb => ?_⟩⟩
      have hk : f.blocks.toList.zipIdx[l]? = some (b, l) := by
        rw [List.getElem?_zipIdx, Array.getElem?_toList, hb]; simp
      obtain ⟨stk, stk', ⟨xb, dl⟩, hle, hs, hbl⟩ := hsel l b l hk
      obtain ⟨-, hpar, -, segs, pre, C, hbs, hbody, rfl⟩ := selectBlock_spec hbl
      have havoid : ∀ y ∈ List.map (fun x => x.fst) sel, Block.avoids (List.flatMap (fun x => x.snd) sel) y = true := by
        intro y hy
        obtain ⟨k, hk'⟩ := List.getElem?_of_mem hy
        have := List.find?_eq_none.1 hf (y, k) (List.mk_mem_zipIdx_iff_getElem?.2 hk')
        simpa using this
      refine ⟨xb, segs, pre, C, ?_, hpar, ?_, hbody, ?_, havoid xb ?_⟩
      · simp [hs]
      · exact hbs.mono hle
      · intro u hu
        exact List.mem_flatMap.2 ⟨(xb, consumedDefs b.body.toList C), List.mem_of_getElem? hs, hu⟩
      · exact List.mem_map.2 ⟨_, List.mem_of_getElem? hs, rfl⟩


theorem selectFuncs_spec {stats : Bool} :
    ∀ {L : List (Lir.Func × Lir.FunId)} {fired fired' : Std.TreeMap String Nat compare} {fs : List (Func VReg)},
      selectFuncs stats L fired = .ok (fs, fired') →
      fs.length = L.length ∧ ∀ (k : Nat) f fn, L[k]? = some (f, fn) → ∃ xf, fs[k]? = some xf ∧ ∃ D, FuncSel fn f xf D
  | [], fired, fired', fs, h => by
      simp only [selectFuncs, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, fun k f fn h => by simp at h⟩
  | (f, fn) :: rest, fired, fired', fs, h => by
      simp only [selectFuncs] at h
      rw [tbind_ok] at h
      obtain ⟨xf, s₁, h₁, h⟩ := h
      rw [tbind_ok] at h
      obtain ⟨fs', s₂, h₂, h⟩ := h
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hlen, hsel⟩ := selectFuncs_spec h₂
      refine ⟨by simp [hlen], fun k f' fn' hk => ?_⟩
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
        obtain ⟨rfl, rfl⟩ := hk
        exact ⟨xf, rfl, selectFunc_spec h₁⟩
      | succ k =>
        simp only [List.getElem?_cons_succ] at hk
        obtain ⟨xf', hs, hD⟩ := hsel k f' fn' hk
        exact ⟨xf', by simpa using hs, hD⟩

/-- What selection established for a program. -/
structure ProgSel (p : Lir.Program) (q : VProgram) : Prop where
  main : q.main = p.main
  size : q.funcs.size = p.funcs.size
  func : ∀ fn f, p.funcs[fn]? = some f → ∃ xf D, q.funcs[fn]? = some xf ∧ FuncSel fn f xf D

theorem progSel_of_funcs {p : Lir.Program} {fs : List (Func VReg)} {stats : Bool}
    {fired fired' : Std.TreeMap String Nat compare}
    (h : selectFuncs stats p.funcs.toList.zipIdx fired = .ok (fs, fired')) :
    ProgSel p { funcs := fs.toArray, main := p.main } := by
  obtain ⟨hlen, hsel⟩ := selectFuncs_spec h
  refine ⟨rfl, by simp [hlen], fun fn f hf => ?_⟩
  have hk : p.funcs.toList.zipIdx[fn]? = some (f, fn) := by
    rw [List.getElem?_zipIdx, Array.getElem?_toList, hf]; simp
  obtain ⟨xf, hs, D, hD⟩ := hsel fn f fn hk
  exact ⟨xf, D, by simpa using hs, hD⟩

/-- Selection on the recheck path keeps the program's shape (`ProgSel`). -/
theorem select_spec {p : Lir.Program} {q : VProgram} (h : select p = .ok q) : ProgSel p q := by
  unfold select at h
  cases hr : (selectFuncs false p.funcs.toList.zipIdx).run ∅ with
  | error e => rw [hr] at h; cases h
  | ok r =>
    obtain ⟨fs, fired⟩ := r
    rw [hr] at h
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact progSel_of_funcs hr

/-- The statistics-counting run selects the same way. -/
theorem run_spec {p : Lir.Program} {q : VProgram} {fired : Std.TreeMap String Nat compare}
    (h : run p = .ok (q, fired)) : ProgSel p q := by
  unfold run at h
  cases hr : (selectFuncs true p.funcs.toList.zipIdx).run {} with
  | error e => rw [hr] at h; cases h
  | ok r =>
    obtain ⟨fs, fired'⟩ := r
    rw [hr] at h
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact progSel_of_funcs hr

end Compilatrix.Xv.Select.Proof
