import Compilatrix.Rt.Proof.Block

/-!
# The layout of a lowered function

`functionRaw` lowers each Cfg block to a chunk of Lir blocks, places the
chunks in Cfg's block order after the entry block (if block 0 has
predecessors), and resolves the targets. `Lowered T f fd F starts` collects
what the simulation reads off that: each block's chunk at its start label
(`Holds`), the state its lowering started from and the chunk it finished
(`Ext`), start labels monotone in the block number (so a Cfg back edge is a
backward Lir edge), each chunk's head block taking the Cfg block's
parameters, the entry, and the edges' back flags (checked by `misordered`).
`functionRaw_lowered` proves it.
-/

set_option autoImplicit false

namespace Compilatrix.Rt.Proof

open Compilatrix.Lir (Word)
open Compilatrix.Rt.Lower
open Compilatrix.Src (NatMap)

/-! ## `mapM` in `Except` -/

theorem except_mapM {α β ε : Type} {g : α → Except ε β} :
    ∀ {l : List α} {r : List β}, l.mapM g = .ok r →
      r.length = l.length ∧ ∀ {j : Nat} {x : α}, l[j]? = some x → ∃ y, g x = .ok y ∧ r[j]? = some y
  | [], r, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun hx => by simp at hx⟩
  | a :: l, r, h => by
    simp only [List.mapM_cons, bind, Except.bind] at h
    cases hg : g a with
    | error e => simp [hg] at h
    | ok y =>
      cases hl : l.mapM g with
      | error e => simp [hg, hl] at h
      | ok ys =>
        simp only [hg, hl, pure, Except.pure, Except.ok.injEq] at h
        subst h
        obtain ⟨hlen, hys⟩ := except_mapM hl
        refine ⟨by simp [hlen], fun {j x} hx => ?_⟩
        cases j with
        | zero => simp at hx; subst hx; exact ⟨y, hg, rfl⟩
        | succ j => simpa using hys (by simpa using hx)

/-! ## A chunk's blocks -/


/-- **A chunk is the final state's blocks**: every finished block of the
state is in the chunk, and its last block is closed. -/
theorem chunkBlocks_ok {f : Fir.FunId} {st : St} {C : List PBlock} (h : chunkBlocks f st = .ok C) :
    Ext C st ∧ ¬ Open st ∧ C.length = st.next := by
  unfold chunkBlocks at h
  by_cases hc : ((st.done.toList.all fun x => decide (x.fst < st.next)) && (st.done.get? st.cur).isSome) = true
  · simp only [hc, ↓reduceIte] at h
    obtain ⟨hlen, hget⟩ := except_mapM h
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hkeys, hcur⟩ := hc
    have hno : ¬ Open st := by
      intro ho
      unfold Open at ho
      rw [ho] at hcur
      cases hcur
    refine ⟨⟨fun {j b} hj => ?_, fun ho => absurd ho hno⟩, hno, by simpa using hlen⟩
    have hjn : j < st.next := hkeys (j, b) (NatMap.mem_toList hj)
    obtain ⟨y, hy, hCj⟩ := hget (j := j) (x := j) (by simp [hjn])
    simp only [hj, pure, Except.pure, Except.ok.injEq] at hy
    subst hy
    exact hCj
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
    simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

/-! ## Chunks -/

/-- The state a block's lowering starts from: its first block open at
label 0 with parameters `ps`. -/
def openSt (fr : Nat) (ps : List Nat) : St := { fresh := fr, params := ps }

theorem labels_openSt (fr : Nat) (ps : List Nat) : Labels (openSt fr ps) where
  cur := by simp [openSt]
  done {j b} h := by simp [openSt, NatMap.get?] at h

theorem open_openSt (fr : Nat) (ps : List Nat) : Open (openSt fr ps) := by
  simp [Open, openSt, NatMap.get?]

theorem block_run (f : Fir.FunId) (T : Tables) (uses : NatMap Nat) (i : Nat) (e : Bool) (b : Cfg.Block) (fr : Nat) :
    (block f T uses i e b).run { fresh := fr } =
      (blockCode f T uses i b).run (openSt fr (if e then [] else b.params.map (·.1))) := rfl

theorem blockCode_grows {f : Fir.FunId} {T : Tables} {uses : NatMap Nat} {i : Nat} {b : Cfg.Block} {st stF : St}
    (h : (blockCode f T uses i b).run st = .ok ((), stF)) (hl : Labels st) (ho : Open st) : Grows st stF := by
  rw [← restAct_body] at h
  exact rest_grows h hl ho

/-- **Each Cfg block's chunk**, from the supply threaded so far. -/
theorem chunks_spec {f : Fir.FunId} {T : Tables} {uses : NatMap Nat} {merged : Bool} :
    ∀ {bs : List Cfg.Block} {k fresh : Nat} {cs : List (List PBlock)} {fresh' : Nat},
      chunks f T uses merged (bs.zipIdx k) fresh = .ok (cs, fresh') →
      cs.length = bs.length ∧ ∀ {i : Nat} {b : Cfg.Block}, bs[i]? = some b → ∃ C fr stF, cs[i]? = some C ∧
        fresh ≤ fr ∧ (blockCode f T uses (k + i) b).run
          (openSt fr (if merged && k + i == 0 then [] else b.params.map (·.1))) = .ok ((), stF) ∧
        chunkBlocks f stF = .ok C
  | [], k, fresh, cs, fresh', h => by
    simp only [List.zipIdx_nil, chunks, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨rfl, fun hb => by simp at hb⟩
  | b :: bs, k, fresh, cs, fresh', h => by
    simp only [List.zipIdx_cons, chunks, bind, Except.bind] at h
    cases hb : (block f T uses k (merged && k == 0) b).run { fresh } with
    | error e => simp [hb] at h
    | ok p =>
      obtain ⟨u, st⟩ := p
      simp only [hb] at h
      cases hC : chunkBlocks f st with
      | error e => simp [hC] at h
      | ok C =>
        simp only [hC] at h
        cases hr : chunks f T uses merged (bs.zipIdx (k + 1)) st.fresh with
        | error e => simp [hr] at h
        | ok q =>
          obtain ⟨rest, fr'⟩ := q
          simp only [hr, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          rw [block_run] at hb
          have hg := blockCode_grows hb (labels_openSt _ _) (open_openSt _ _)
          obtain ⟨hlen, hrest⟩ := chunks_spec hr
          refine ⟨by simp [hlen], fun {i b'} hb' => ?_⟩
          cases i with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hb'
            subst hb'
            exact ⟨C, fresh, st, rfl, Nat.le_refl _, by simpa using hb, hC⟩
          | succ i =>
            simp only [List.getElem?_cons_succ] at hb'
            obtain ⟨C', fr, stF, hC', hfr, hrun, hcb⟩ := hrest hb'
            refine ⟨C', fr, stF, by simpa using hC', Nat.le_trans hg.fresh hfr, ?_, hcb⟩
            rw [show k + (i + 1) = k + 1 + i by omega]
            exact hrun

/-! ## Start labels -/

/-- Where chunk `i` starts. -/
def chunkOff (first : Nat) (cs : List (List PBlock)) (i : Nat) : Nat := first + ((cs.take i).map List.length).sum

theorem chunkStarts_foldl : ∀ (cs : List (List PBlock)) (k : Nat) (m : NatMap Nat) (l : Nat) (n : Nat),
    ((cs.zipIdx k).foldl (fun (p : NatMap Nat × Nat) (ci : List PBlock × Nat) => (p.1.insert ci.2 p.2, p.2 + ci.1.length))
      (m, l)).1.get? n =
      if k ≤ n ∧ n < k + cs.length then some (l + ((cs.take (n - k)).map List.length).sum) else m.get? n
  | [], k, m, l, n => by
    simp only [List.zipIdx_nil, List.foldl_nil, List.length_nil, Nat.add_zero]
    rw [if_neg (by omega)]
  | c :: cs, k, m, l, n => by
    simp only [List.zipIdx_cons, List.foldl_cons]
    rw [chunkStarts_foldl cs (k + 1) _ _ n]
    simp only [NatMap.get?_insert, List.length_cons]
    by_cases hn : n = k
    · subst hn
      rw [if_neg (by omega), if_pos rfl, if_pos (by omega)]
      simp
    · by_cases hlo : k + 1 ≤ n ∧ n < k + 1 + cs.length
      · rw [if_pos hlo, if_pos ⟨by omega, by omega⟩]
        obtain ⟨j, rfl⟩ : ∃ j, n = k + 1 + j := ⟨n - (k + 1), by omega⟩
        simp only [show k + 1 + j - k = j + 1 by omega, show k + 1 + j - (k + 1) = j by omega, List.take_succ_cons,
          List.map_cons, List.sum_cons]
        rw [Nat.add_assoc]
      · rw [if_neg hlo, if_neg hn, if_neg (by omega)]

theorem chunkStarts_get (first : Nat) (cs : List (List PBlock)) (i : Nat) :
    (chunkStarts first cs).1.get? i = if i < cs.length then some (chunkOff first cs i) else none := by
  unfold chunkStarts chunkOff
  have := chunkStarts_foldl cs 0 .leaf first i
  simp only [Nat.zero_le, true_and, Nat.zero_add, Nat.sub_zero] at this
  rw [this]
  split <;> simp [NatMap.get?]

theorem chunkOff_mono (first : Nat) (cs : List (List PBlock)) {i j : Nat} (h : i ≤ j) :
    chunkOff first cs i ≤ chunkOff first cs j := by
  unfold chunkOff
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
  rw [List.take_add, List.map_append, List.sum_append]
  omega

/-! ## Resolved chunks -/

theorem resolveChunks_spec {f : Fir.FunId} {starts : NatMap Nat} :
    ∀ {cs : List (List PBlock)} {k : Nat} {body : List Lir.Block}, resolveChunks f starts (cs.zipIdx k) = .ok body →
      ∀ {i : Nat} {C : List PBlock} {j : Nat} {b : PBlock}, cs[i]? = some C → C[j]? = some b →
        ∃ lb, resolveBlock f (starts.getD (k + i) 0) starts b = .ok lb ∧
          body[((cs.take i).map List.length).sum + j]? = some lb
  | [], k, body, h, i, C, j, b, hC, _ => by simp at hC
  | c :: cs, k, body, h, i, C, j, b, hC, hb => by
    simp only [List.zipIdx_cons, resolveChunks, bind, Except.bind] at h
    cases hm : c.mapM (resolveBlock f (starts.getD k 0) starts) with
    | error e => simp [hm] at h
    | ok bs =>
      simp only [hm] at h
      cases hr : resolveChunks f starts (cs.zipIdx (k + 1)) with
      | error e => simp [hr] at h
      | ok body' =>
        simp only [hr, pure, Except.pure, Except.ok.injEq] at h
        subst h
        obtain ⟨hlen, hget⟩ := except_mapM hm
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hC
          subst hC
          obtain ⟨lb, hlb, hbs⟩ := hget hb
          refine ⟨lb, by simpa using hlb, ?_⟩
          have hj : j < bs.length := (List.getElem?_eq_some_iff.1 hbs).1
          simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add]
          rw [List.getElem?_append_left hj]
          exact hbs
        | succ i =>
          simp only [List.getElem?_cons_succ] at hC
          obtain ⟨lb, hlb, hbody⟩ := resolveChunks_spec hr hC hb
          refine ⟨lb, by rw [show k + (i + 1) = k + 1 + i by omega]; exact hlb, ?_⟩
          simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
          rw [Nat.add_assoc, List.getElem?_append_right (by omega), hlen]
          simpa using hbody

end Compilatrix.Rt.Proof
