import IxCC.Xv.Stacking.Run

/-!
# The shape of a stacked program

What a successful `Stacking.run` builds, as the stacking simulation reads
it: the exit group at blocks 0–4, each export's wrapper and each function's
blocks at the first block the placement gave them (`run_ok`, `funcBlocks_at`,
`wrapper_at`), the entry map, and the checks that passed (layouts, clobbers,
well-formedness).
-/

namespace IxCC.Xv.Stacking.Proof

open IxCC.Lir (FunId)
open IxCC.Xv.Stacking

/-! ## `Except` helpers -/

theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {y : β} :
    (x >>= f) = .ok y ↔ ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x <;> simp [bind, Except.bind]

theorem mapError_ok {ε ε' α : Type} {x : Except ε α} {g : ε → ε'} {y : α} :
    x.mapError g = .ok y ↔ x = .ok y := by
  cases x <;> simp [Except.mapError]

theorem mapM_ok {ε α β : Type} {f : α → Except ε β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys →
      ys.length = xs.length ∧ ∀ (i : Nat) x, xs[i]? = some x → ∃ y, ys[i]? = some y ∧ f x = .ok y
  | [], ys, h => by
    rw [List.mapM_nil] at h
    cases h
    exact ⟨rfl, fun _ _ h => by simp at h⟩
  | x :: xs, ys, h => by
    rw [List.mapM_cons] at h
    obtain ⟨y, hy, h'⟩ := bind_ok.1 h
    obtain ⟨ys', hys, h''⟩ := bind_ok.1 h'
    cases h''
    obtain ⟨hl, hi⟩ := mapM_ok hys
    refine ⟨by simp [hl], fun i z hz => ?_⟩
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hz
      subst hz
      exact ⟨y, rfl, hy⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hz ⊢
      exact hi i z hz

/-! ## Placement -/

/-- Lay items out one after another from block `n`. -/
def placeList {α β : Type} (mk : α → Nat → β) (sz : α → Nat) : List α → Nat → List β
  | [], _ => []
  | x :: xs, n => mk x n :: placeList mk sz xs (n + sz x)

theorem foldl_place {α β : Type} (mk : α → Nat → β) (sz : α → Nat) :
    ∀ (xs : List α) (acc : List β) (n : Nat),
      xs.foldl (fun (p : List β × Nat) x => (p.1 ++ [mk x p.2], p.2 + sz x)) (acc, n) =
        (acc ++ placeList mk sz xs n, n + (xs.map sz).sum)
  | [], acc, n => by simp [placeList]
  | x :: xs, acc, n => by
      rw [List.foldl_cons, foldl_place mk sz xs]
      simp [placeList, Nat.add_assoc]

theorem placeList_length {α β : Type} (mk : α → Nat → β) (sz : α → Nat) :
    ∀ (xs : List α) (n : Nat), (placeList mk sz xs n).length = xs.length
  | [], _ => rfl
  | _ :: xs, n => by simp [placeList, placeList_length mk sz xs]

theorem placeList_get {α β : Type} (mk : α → Nat → β) (sz : α → Nat) :
    ∀ (xs : List α) (n i : Nat) (x : α), xs[i]? = some x →
      (placeList mk sz xs n)[i]? = some (mk x (n + ((xs.take i).map sz).sum))
  | [], _, _, _, h => by simp at h
  | y :: xs, n, 0, x, h => by simp at h; subst h; simp [placeList]
  | y :: xs, n, i + 1, x, h => by
      simp only [List.getElem?_cons_succ] at h
      simp only [placeList, List.getElem?_cons_succ, placeList_get mk sz xs (n + sz y) i x h,
        List.take_succ_cons, List.map_cons, List.sum_cons, Nat.add_assoc]

theorem placeExports_eq (exports : List (FunId × String × List ArgRep × Func Loc)) :
    placeExports exports =
      (placeList (fun (e : FunId × String × List ArgRep × Func Loc) n =>
          ({ fn := e.1, symbol := e.2.1, reps := e.2.2.1, start := n } : PlacedExport))
        (fun e => wrapperBlocks e.2.2.1) exports exitBlocks,
       exitBlocks + (exports.map fun e => wrapperBlocks e.2.2.1).sum) := by
  unfold placeExports
  exact foldl_place _ _ exports [] exitBlocks

theorem placeFuncs_eq (fns : List (Func Loc × FunId × FrameLayout × Facts)) (next : Nat) :
    placeFuncs fns next =
      (placeList (fun (e : Func Loc × FunId × FrameLayout × Facts) n =>
          ({ func := e.1, fn := e.2.1, layout := e.2.2.1, facts := e.2.2.2, start := n } : Placed))
        (fun e => funcBlocks e.1 e.2.2.1 e.2.2.2) fns next,
       next + (fns.map fun e => funcBlocks e.1 e.2.2.1 e.2.2.2).sum) := by
  unfold placeFuncs
  exact foldl_place _ _ fns [] next

/-! ## Functions with their layouts -/

theorem withLayouts_length {p : LProgram} {layouts : List FrameLayout} (h : layouts.length = p.funcs.size) :
    (withLayouts p layouts).length = p.funcs.size := by
  simp [withLayouts, h]

theorem withLayouts_get {p : LProgram} {layouts : List FrameLayout} {fn : FunId} {f : Func Loc}
    {l : FrameLayout} (hf : p.funcs[fn]? = some f) (hl : layouts[fn]? = some l) :
    (withLayouts p layouts)[fn]? = some (f, fn, l, f.facts) := by
  simp [withLayouts, List.getElem?_zip_eq_some, List.getElem?_zipIdx, hf, hl]
  exact ⟨f, fn, l, ⟨⟨rfl, rfl⟩, rfl⟩, rfl, rfl, rfl, rfl⟩

/-! ## What `run` checked and built -/

/-- The wrappers' placements of a run. -/
def runWrappers (p : LProgram) (layouts : List FrameLayout) (reps : FunId → Option (List ArgRep)) :
    List PlacedExport :=
  (placeExports (exportsOf reps (withLayouts p layouts))).1

/-- The functions' placements of a run. -/
def runPlaced (p : LProgram) (layouts : List FrameLayout) (reps : FunId → Option (List ArgRep)) : List Placed :=
  (placeFuncs (withLayouts p layouts) (placeExports (exportsOf reps (withLayouts p layouts))).2).1

theorem run_ok {p : LProgram} {layouts : List FrameLayout} {reps : FunId → Option (List ArgRep)} {env : Xl.Env}
    {st : Stacked} (h : run p layouts reps env = .ok st) :
    layouts.length = p.funcs.size ∧
    (∀ x ∈ withLayouts p layouts, x.2.2.1.check x.2.2.2 = true) ∧
    (∀ x ∈ withLayouts p layouts, extraChanges p env x.1 x.2.1 x.2.2.1 x.2.2.2 = []) ∧
    (∀ x ∈ withLayouts p layouts, aritiesOk p x.1 = true) ∧
    (placeFuncs (withLayouts p layouts) (placeExports (exportsOf reps (withLayouts p layouts))).2).2 < 2 ^ 32 ∧
    ∃ (wrapperCode funcCode : List (List X86.Block)) (main : PlacedExport),
      ((runWrappers p layouts reps).zip (exportsOf reps (withLayouts p layouts))).mapM
          (fun (w, (_, _, _, f)) => wrapperOf (entriesOf (runPlaced p layouts reps)) w f) = .ok wrapperCode ∧
      (runPlaced p layouts reps).mapM (fun pl =>
          (emitFunc (entriesOf (runPlaced p layouts reps)) 0 pl.func pl.layout pl.facts pl.start).mapError
            (Error.func pl.fn)) = .ok funcCode ∧
      (runWrappers p layouts reps).find? (·.fn == p.main) = some main ∧
      st.program = { blocks := (exitGroup 0 ++ wrapperCode.flatten ++ funcCode.flatten).toArray,
                     entry := UInt32.ofNat main.start } ∧
      st.program.wellFormed = true := by
  unfold run at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · rename_i hlen
    have hlen : layouts.length = p.funcs.size := by simpa using hlen
    split at h
    · cases h
    · rename_i hcheck
      split at h
      · cases h
      · rename_i hclob
        split at h
        · cases h
        · rename_i harity
          split at h
          · rename_i htotal
            split at h
            · cases h
            · rename_i wrapperCode hwc
              split at h
              · cases h
              · rename_i funcCode hfc
                split at h
                · rename_i main hmain
                  split at h
                  · rename_i hwf
                    simp only [Except.ok.injEq] at h
                    subst h
                    refine ⟨hlen, ?_, ?_, ?_, by simpa using htotal, wrapperCode, funcCode, main, hwc, hfc, hmain,
                      rfl, ?_⟩
                    · intro x hx
                      have := List.find?_eq_none.1 hcheck x hx
                      simpa using this
                    · intro x hx
                      have := List.find?_eq_none.1 hclob x hx
                      simpa using this
                    · intro x hx
                      have := List.find?_eq_none.1 harity x hx
                      simpa using this
                    · rw [← X86.Program.wellFormedK_eq]; simpa using hwf
                  · cases h
                · cases h
          · cases h
  · cases h

/-! ## Lists of blocks -/

theorem flatten_getElem? {α : Type} :
    ∀ (Ls : List (List α)) (i j : Nat) (L : List α), Ls[i]? = some L → j < L.length →
      Ls.flatten[((Ls.take i).map List.length).sum + j]? = L[j]?
  | [], _, _, _, h, _ => by simp at h
  | L' :: Ls, 0, j, L, h, hj => by
      simp at h; subst h
      simp [List.getElem?_append_left hj]
  | L' :: Ls, i + 1, j, L, h, hj => by
      simp only [List.getElem?_cons_succ] at h
      simp only [List.flatten_cons, List.take_succ_cons, List.map_cons, List.sum_cons]
      rw [Nat.add_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
      exact flatten_getElem? Ls i j L h hj

theorem take_sum_eq {α β : Type} {Ls : List (List α)} {xs : List β} {sz : β → Nat}
    (h : Ls.map List.length = xs.map sz) (i : Nat) :
    ((Ls.take i).map List.length).sum = ((xs.take i).map sz).sum := by
  rw [List.map_take, List.map_take, h]

theorem flatten_length {α β : Type} {Ls : List (List α)} {xs : List β} {sz : β → Nat}
    (h : Ls.map List.length = xs.map sz) : Ls.flatten.length = (xs.map sz).sum := by
  rw [List.length_flatten, h]

/-- The lengths of `mapM`'s outputs, from a length per input. -/
theorem mapM_lengths {ε α β : Type} {f : α → Except ε (List β)} {sz : α → Nat}
    (hf : ∀ x ys, f x = .ok ys → ys.length = sz x) :
    ∀ {xs : List α} {Ls : List (List β)}, xs.mapM f = .ok Ls → Ls.map List.length = xs.map sz
  | [], Ls, h => by rw [List.mapM_nil] at h; cases h; rfl
  | x :: xs, Ls, h => by
    rw [List.mapM_cons] at h
    obtain ⟨y, hy, h'⟩ := bind_ok.1 h
    obtain ⟨ys', hys, h''⟩ := bind_ok.1 h'
    cases h''
    simp [hf x y hy, mapM_lengths hf hys]

/-! ## Entries -/

theorem foldl_insert_get {β γ : Type} (key : β → Nat) (val : β → γ) :
    ∀ (l : List β) (off : Nat) (m : NatMap γ), (∀ i (x : β), l[i]? = some x → key x = off + i) →
      ∀ k, (l.foldl (fun m x => m.insert (key x) (val x)) m).get? k =
        if off ≤ k ∧ k < off + l.length then (l[k - off]?).map val else m.get? k
  | [], off, m, _, k => by simp; intro h1 h2; omega
  | x :: xs, off, m, hk, k => by
      rw [List.foldl_cons]
      have hx : key x = off := by simpa using hk 0 x rfl
      have hxs : ∀ i (y : β), xs[i]? = some y → key y = (off + 1) + i := fun i y hy => by
        have := hk (i + 1) y (by simpa using hy); omega
      rw [foldl_insert_get key val xs (off + 1) _ hxs k]
      rw [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert, hx, ← Std.TreeMap.get?_eq_getElem?]
      by_cases h1 : off + 1 ≤ k ∧ k < off + 1 + xs.length
      · simp only [h1, and_self, ↓reduceIte, List.length_cons]
        have hk' : k - off = (k - (off + 1)) + 1 := by omega
        rw [if_pos (by omega), hk', List.getElem?_cons_succ]
      · simp only [h1, ↓reduceIte, List.length_cons]
        by_cases h2 : k = off
        · subst h2
          simp
        · have hc : compare off k ≠ .eq := fun e => h2 (Nat.compare_eq_eq.1 e).symm
          simp only [hc, ↓reduceIte]
          rw [if_neg (by omega)]

/-! ## Emitted lengths -/

/-- What `emitFunc` checked and emitted. -/
theorem emitFunc_ok {funcs : NatMap (Nat × Nat)} {exit : Nat} {f : Func Loc} {l : FrameLayout} {a : Facts}
    {start : Nat} {blks : List X86.Block} (h : emitFunc funcs exit f l a start = .ok blks) :
    f.blocks.size ≠ 0 ∧ a.inArgsUsed ≤ a.inArgs ∧ (∀ b ∈ f.blocks.toList, 0 ∉ b.term.succs) ∧
      ∃ body, f.blocks.toList.zipIdx.mapM (fun (b, lbl) =>
          ((FnCtx.mk l a.inArgs (start + if FrameLayout.checked a l then 1 else 0) f.blocks.size funcs exit).block
            (if lbl == 0 then prologue l else []) b).mapError (s!"block {lbl}: " ++ ·)) = .ok body ∧
        blks = (if FrameLayout.checked a l then
          [stackCheck l (FnCtx.failBlock (FnCtx.mk l a.inArgs (start + 1) f.blocks.size funcs exit) 2)
            (UInt32.ofNat (start + 1))] else []) ++ body := by
  unfold emitFunc at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · rename_i hne
    split at h
    · rename_i hin
      split at h
      · rename_i hsucc
        split at h
        · cases h
        · rename_i body hbody
          simp only [Except.ok.injEq] at h
          refine ⟨by simpa using hne, by simpa using hin, ?_, body, ?_, ?_⟩
          · intro b hb hm
            simp at hsucc
            obtain ⟨i, hi, hb'⟩ := List.getElem_of_mem hb
            rw [Array.getElem_toList] at hb'
            subst hb'
            exact hsucc i (by simpa using hi) hm
          · simpa using hbody
          · rw [← h]
            by_cases hc : FrameLayout.checked a l = true <;> simp [hc, FnCtx.failBlock]
      · cases h
    · cases h
  · cases h

theorem emitFunc_length {funcs : NatMap (Nat × Nat)} {exit : Nat} {f : Func Loc} {l : FrameLayout} {a : Facts}
    {start : Nat} {blks : List X86.Block} (h : emitFunc funcs exit f l a start = .ok blks) :
    blks.length = funcBlocks f l a := by
  obtain ⟨-, -, -, body, hbody, rfl⟩ := emitFunc_ok h
  have := (mapM_ok hbody).1
  simp only [List.length_zipIdx, Array.length_toList] at this
  by_cases hc : FrameLayout.checked a l = true <;> simp [hc, funcBlocks, this] <;> omega

theorem wrapper_length {entry fail₃ : X86.BlockId} {reps : List ArgRep} {start : Nat} {blks : List X86.Block}
    (h : wrapper entry fail₃ reps start = .ok blks) : blks.length = wrapperBlocks reps := by
  unfold wrapper at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · rename_i hlen
    split at h
    · cases h
    · rename_i marshal hm
      have hpairs : ((sysvArgs.zip Lir.Conv.argRegs).zip reps).length = reps.length := by
        simp [sysvArgs, Lir.Conv.argRegs] at hlen ⊢
        omega
      split at h
      · rename_i hnil
        simp only [Except.ok.injEq] at h
        subst h
        have : hasNatArg reps = false := by
          rw [hasNatArg, Bool.eq_false_iff]
          intro hc
          obtain ⟨i, hi, hri⟩ := List.getElem_of_mem (List.contains_iff_mem.1 hc)
          have hz : ((sysvArgs.zip Lir.Conv.argRegs).zip reps)[i]? ≠ none := by
            simp only [ne_eq, List.getElem?_eq_none_iff, Nat.not_le, hpairs]; exact hi
          obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.1 hz
          have hmem := List.mem_of_getElem? hq
          have hq2 : q.2 = .nat := by
            have := List.getElem?_zip_eq_some.1 hq
            rw [List.getElem?_eq_getElem hi, hri] at this
            simpa using this.2.symm
          obtain ⟨⟨s, d⟩, r⟩ := q
          simp only at hq2
          subst hq2
          have := List.filterMap_eq_nil_iff.1 hnil _ hmem
          simp at this
        simp [wrapperBlocks, this]
      · rename_i first rest hcons
        simp only [Except.ok.injEq] at h
        subst h
        have : hasNatArg reps = true := by
          have hm : first ∈ (((sysvArgs.zip Lir.Conv.argRegs).zip reps).filterMap
              (fun x => if x.2 == .nat then some x.1.1 else none)) := by
            rw [hcons]; simp
          obtain ⟨q, hq, hqe⟩ := List.mem_filterMap.1 hm
          split at hqe
          · rename_i hn
            exact List.contains_iff_mem.2 (by
              have := List.of_mem_zip hq
              simpa [beq_iff_eq.1 hn] using this.2)
          · cases hqe
        simp [wrapperBlocks, this]
  · cases h

/-! ## Blocks at their placements -/

theorem wrapperOf_ok {entries : NatMap (Nat × Nat)} {w : PlacedExport} {f : Func Loc} {blks : List X86.Block}
    (h : wrapperOf entries w f = .ok blks) :
    f.results = 1 ∧ w.reps.length = f.params.length ∧ ∃ entry arity, entries.get? w.fn = some (entry, arity) ∧
      wrapper (UInt32.ofNat entry) (UInt32.ofNat (0 + statusOf .natOverflow - 1)) w.reps w.start = .ok blks := by
  unfold wrapperOf at h
  simp only [bind, Except.bind] at h
  split at h
  · rename_i h1
    split at h
    · rename_i h2
      split at h
      · rename_i entry arity he
        refine ⟨by simpa using h1, by simpa using h2, entry, arity, he, ?_⟩
        exact mapError_ok.1 h
      · cases h
    · cases h
  · cases h

theorem placed_get {p : LProgram} {layouts : List FrameLayout} {reps : FunId → Option (List ArgRep)} {k : FunId}
    {f : Func Loc} {l : FrameLayout} (hf : p.funcs[k]? = some f) (hl : layouts[k]? = some l) :
    (runPlaced p layouts reps)[k]? = some ⟨f, k, l, f.facts,
      (placeExports (exportsOf reps (withLayouts p layouts))).2 +
        (((withLayouts p layouts).take k).map fun e => funcBlocks e.1 e.2.2.1 e.2.2.2).sum⟩ := by
  rw [runPlaced, placeFuncs_eq]
  exact placeList_get _ _ _ _ k _ (withLayouts_get hf hl)

theorem placed_fn {p : LProgram} {layouts : List FrameLayout} {reps : FunId → Option (List ArgRep)} :
    ∀ i (pl : Placed), (runPlaced p layouts reps)[i]? = some pl → pl.fn = 0 + i := by
  intro i pl h
  rw [runPlaced, placeFuncs_eq] at h
  have hl : i < (withLayouts p layouts).length := by
    have := (List.getElem?_eq_some_iff.1 h).1
    rwa [placeList_length] at this
  obtain ⟨e, he⟩ : ∃ e, (withLayouts p layouts)[i]? = some e := ⟨_, List.getElem?_eq_getElem hl⟩
  rw [placeList_get _ _ _ _ i e he] at h
  simp only [Option.some.injEq] at h
  subst h
  simp only [withLayouts, List.getElem?_map, Option.map_eq_some_iff, List.getElem?_zip_eq_some,
    List.getElem?_zipIdx] at he
  obtain ⟨⟨⟨f, fn⟩, l⟩, ⟨hz, -⟩, rfl⟩ := he
  simp only [Prod.mk.injEq] at hz
  obtain ⟨_, _, rfl, rfl⟩ := hz
  simp

/-- A function's entry in the entry map: its first block and arity. -/
theorem entries_get {p : LProgram} {layouts : List FrameLayout} {reps : FunId → Option (List ArgRep)}
    (g : FunId) :
    (entriesOf (runPlaced p layouts reps)).get? g =
      ((runPlaced p layouts reps)[g]?).map fun pl => (pl.start, pl.func.params.length) := by
  unfold entriesOf
  rw [foldl_insert_get (fun pl : Placed => pl.fn) (fun pl => (pl.start, pl.func.params.length)) _ 0 _
    placed_fn g]
  by_cases hg : g < (runPlaced p layouts reps).length
  · rw [if_pos ⟨Nat.zero_le _, by simpa using hg⟩]; simp
  · rw [if_neg (by simpa using hg), List.getElem?_eq_none (by simpa using hg)]
    simp [Std.TreeMap.get?_eq_getElem?]

/-- Each function's blocks sit at its placement. -/
theorem func_at {p : LProgram} {layouts : List FrameLayout} {reps : FunId → Option (List ArgRep)} {env : Xl.Env}
    {st : Stacked} (h : run p layouts reps env = .ok st) {k : FunId} {f : Func Loc} {l : FrameLayout}
    (hf : p.funcs[k]? = some f) (hl : layouts[k]? = some l) :
    ∃ pl blks, (runPlaced p layouts reps)[k]? = some pl ∧ pl.func = f ∧ pl.fn = k ∧ pl.layout = l ∧
      pl.facts = f.facts ∧
      emitFunc (entriesOf (runPlaced p layouts reps)) 0 f l f.facts pl.start = .ok blks ∧
      ∀ j, j < blks.length → st.program.blocks[pl.start + j]? = blks[j]? := by
  obtain ⟨hlen, -, -, -, -, wrapperCode, funcCode, main, hwc, hfc, -, hprog, -⟩ := run_ok h
  have hpl := placed_get (reps := reps) hf hl
  obtain ⟨-, hget⟩ := mapM_ok hfc
  obtain ⟨blks, hblks, hemit⟩ := hget k _ hpl
  refine ⟨_, blks, hpl, rfl, rfl, rfl, rfl, mapError_ok.1 hemit, fun j hj => ?_⟩
  rw [hprog]
  simp only [List.getElem?_toArray]
  -- The prefix: the exit group and the wrappers.
  have hwl : wrapperCode.map List.length =
      (exportsOf reps (withLayouts p layouts)).map fun e => wrapperBlocks e.2.2.1 := by
    have := mapM_lengths (sz := fun (x : PlacedExport × (FunId × String × List ArgRep × Func Loc)) =>
        wrapperBlocks x.1.reps)
      (fun x ys hx => by
        obtain ⟨w, fn, s, rs, f⟩ := x
        have hx' : wrapperOf (entriesOf (runPlaced p layouts reps)) w f = .ok ys := hx
        obtain ⟨-, -, _, _, -, hw⟩ := wrapperOf_ok hx'
        exact wrapper_length hw) hwc
    rw [this, runWrappers, placeExports_eq]
    apply List.ext_getElem
    · simp [List.length_zip, placeList_length]
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_zip]
      have hi : i < (exportsOf reps (withLayouts p layouts)).length := by
        simp [List.length_zip, placeList_length] at h1; omega
      have := placeList_get (fun (e : FunId × String × List ArgRep × Func Loc) n =>
          ({ fn := e.1, symbol := e.2.1, reps := e.2.2.1, start := n } : PlacedExport))
        (fun e => wrapperBlocks e.2.2.1) _ exitBlocks i _ (List.getElem?_eq_getElem hi)
      rw [List.getElem?_eq_getElem (by rwa [placeList_length])] at this
      simp only [Option.some.injEq] at this
      rw [this]
  have hfl : funcCode.map List.length =
      (withLayouts p layouts).map fun e => funcBlocks e.1 e.2.2.1 e.2.2.2 := by
    have := mapM_lengths (sz := fun pl : Placed => funcBlocks pl.func pl.layout pl.facts)
      (fun x ys hx => emitFunc_length (mapError_ok.1 hx)) hfc
    rw [this, runPlaced, placeFuncs_eq]
    apply List.ext_getElem
    · simp [placeList_length]
    · intro i h1 h2
      simp only [List.getElem_map]
      have hi : i < (withLayouts p layouts).length := by simpa [placeList_length] using h1
      have := placeList_get (fun (e : Func Loc × FunId × FrameLayout × Facts) n =>
          ({ func := e.1, fn := e.2.1, layout := e.2.2.1, facts := e.2.2.2, start := n } : Placed))
        (fun e => funcBlocks e.1 e.2.2.1 e.2.2.2) _ (placeExports (exportsOf reps (withLayouts p layouts))).2 i _
        (List.getElem?_eq_getElem hi)
      rw [List.getElem?_eq_getElem (by rwa [placeList_length])] at this
      simp only [Option.some.injEq] at this
      rw [this]
  have hpre : (exitGroup 0 ++ wrapperCode.flatten).length = (placeExports (exportsOf reps (withLayouts p layouts))).2 := by
    rw [List.length_append, flatten_length hwl, placeExports_eq]
    simp [exitGroup, exitBlocks]
  rw [List.append_assoc, ← List.append_assoc (exitGroup 0), ← hpre, Nat.add_assoc,
    List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, ← take_sum_eq hfl k]
  exact flatten_getElem? funcCode k j blks hblks hj

/-- The exit group's blocks come first. -/
theorem exit_at {p : LProgram} {layouts : List FrameLayout} {reps : FunId → Option (List ArgRep)} {env : Xl.Env}
    {st : Stacked} (h : run p layouts reps env = .ok st) {j : Nat} (hj : j < exitBlocks) :
    st.program.blocks[j]? = (exitGroup 0)[j]? := by
  obtain ⟨-, -, -, -, -, wrapperCode, funcCode, main, -, -, -, hprog, -⟩ := run_ok h
  simp only [hprog, List.getElem?_toArray, List.append_assoc]
  exact List.getElem?_append_left (by simpa [exitGroup, exitBlocks] using hj)

theorem withLayouts_mem {p : LProgram} {layouts : List FrameLayout} {x : Func Loc × FunId × FrameLayout × Facts}
    (h : x ∈ withLayouts p layouts) : p.funcs[x.2.1]? = some x.1 ∧ layouts[x.2.1]? = some x.2.2.1 ∧
      x.2.2.2 = x.1.facts := by
  simp only [withLayouts, List.mem_map] at h
  obtain ⟨⟨⟨f, fn⟩, l⟩, hm, rfl⟩ := h
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem hm
  simp only [List.getElem_zip, List.getElem_zipIdx, Prod.mk.injEq] at he
  obtain ⟨⟨hf, hfn⟩, hl⟩ := he
  subst hfn
  have hil : i < layouts.length := by simp [List.length_zip] at hi; omega
  dsimp only
  refine ⟨?_, ?_, rfl⟩
  · rw [← hf]; simp
  · rw [← hl, Nat.zero_add, List.getElem?_eq_getElem hil]

/-- The export of `main`: its wrapper's blocks sit at its placement, and the
program starts there. -/
theorem main_at {p : LProgram} {layouts : List FrameLayout} {reps : FunId → Option (List ArgRep)} {env : Xl.Env}
    {st : Stacked} (h : run p layouts reps env = .ok st) :
    ∃ (f : Func Loc) (s : String) (w : PlacedExport) (blks : List X86.Block),
      p.funcs[p.main]? = some f ∧ f.conv = .sysvExport s ∧ w.fn = p.main ∧
      w.reps = exportReps reps p.main f ∧ st.program.entry = UInt32.ofNat w.start ∧
      wrapperOf (entriesOf (runPlaced p layouts reps)) w f = .ok blks ∧
      ∀ j, j < blks.length → st.program.blocks[w.start + j]? = blks[j]? := by
  obtain ⟨hlen, -, -, -, -, wrapperCode, funcCode, main, hwc, hfc, hmain, hprog, -⟩ := run_ok h
  have hmem := List.mem_of_find?_eq_some hmain
  have hfn : main.fn = p.main := by simpa using List.find?_some hmain
  obtain ⟨i, hi, hmi⟩ := List.getElem_of_mem hmem
  have hwi : (runWrappers p layouts reps)[i]? = some main := by rw [List.getElem?_eq_getElem hi, hmi]
  have hilen : i < (exportsOf reps (withLayouts p layouts)).length := by
    rw [runWrappers, placeExports_eq] at hi
    simpa [placeList_length] using hi
  obtain ⟨e, he⟩ : ∃ e, (exportsOf reps (withLayouts p layouts))[i]? = some e :=
    ⟨_, List.getElem?_eq_getElem hilen⟩
  have hwe := placeList_get (fun (e : FunId × String × List ArgRep × Func Loc) n =>
      ({ fn := e.1, symbol := e.2.1, reps := e.2.2.1, start := n } : PlacedExport))
    (fun e => wrapperBlocks e.2.2.1) _ exitBlocks i e he
  have hwi' := hwi
  rw [runWrappers, placeExports_eq] at hwi'
  rw [hwi', Option.some.injEq] at hwe
  -- The export is a SysV function of the program.
  obtain ⟨fn, s, rs, f⟩ := e
  have hem := List.mem_of_getElem? he
  simp only [exportsOf, List.mem_filterMap] at hem
  obtain ⟨x, hx, hxe⟩ := hem
  obtain ⟨hxf, -, -⟩ := withLayouts_mem hx
  split at hxe
  · rename_i s' hconv
    simp only [Option.some.injEq, Prod.mk.injEq] at hxe
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hxe
    have hfn' : x.2.1 = p.main := by rw [← hfn, hwe]
    rw [hfn'] at hxf
    -- Its wrapper's blocks.
    obtain ⟨-, hget⟩ := mapM_ok hwc
    have hz : ((runWrappers p layouts reps).zip (exportsOf reps (withLayouts p layouts)))[i]? =
        some (main, (x.2.1, s', exportReps reps x.2.1 x.1, x.1)) := by
      rw [List.getElem?_zip_eq_some]; exact ⟨hwi, he⟩
    obtain ⟨blks, hblks, hwo⟩ := hget i _ hz
    refine ⟨x.1, s', main, blks, hxf, hconv, hfn, by rw [hwe]; simp [hfn'], ?_, hwo, fun j hj => ?_⟩
    · rw [hprog]
    · rw [hprog]
      simp only [List.getElem?_toArray, List.append_assoc]
      have hwl : wrapperCode.map List.length =
          (exportsOf reps (withLayouts p layouts)).map fun e => wrapperBlocks e.2.2.1 := by
        have := mapM_lengths (sz := fun (x : PlacedExport × (FunId × String × List ArgRep × Func Loc)) =>
            wrapperBlocks x.1.reps)
          (fun x ys hx => by
            obtain ⟨w, fn, s, rs, f⟩ := x
            have hx' : wrapperOf (entriesOf (runPlaced p layouts reps)) w f = .ok ys := hx
            obtain ⟨-, -, _, _, -, hw⟩ := wrapperOf_ok hx'
            exact wrapper_length hw) hwc
        rw [this, runWrappers, placeExports_eq]
        apply List.ext_getElem
        · simp [List.length_zip, placeList_length]
        · intro i h1 h2
          simp only [List.getElem_map, List.getElem_zip]
          have hi : i < (exportsOf reps (withLayouts p layouts)).length := by
            simp [List.length_zip, placeList_length] at h1; omega
          have := placeList_get (fun (e : FunId × String × List ArgRep × Func Loc) n =>
              ({ fn := e.1, symbol := e.2.1, reps := e.2.2.1, start := n } : PlacedExport))
            (fun e => wrapperBlocks e.2.2.1) _ exitBlocks i _ (List.getElem?_eq_getElem hi)
          rw [List.getElem?_eq_getElem (by rwa [placeList_length])] at this
          simp only [Option.some.injEq] at this
          rw [this]
      have hlen5 : (exitGroup 0).length = exitBlocks := by simp [exitGroup, exitBlocks]
      rw [hwe]
      simp only
      rw [← hlen5, Nat.add_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
        ← take_sum_eq hwl i]
      have hidx := flatten_getElem? wrapperCode i j blks hblks hj
      have hlt : ((wrapperCode.take i).map List.length).sum + j < wrapperCode.flatten.length :=
        (List.getElem?_eq_some_iff.1 (hidx.trans (List.getElem?_eq_getElem hj))).1
      rw [List.getElem?_append_left hlt]
      exact hidx
  · simp at hxe

end IxCC.Xv.Stacking.Proof
