import Compilatrix.Rt.Proof.Layout

/-!
# A lowered function's layout

`Lowered T f fd F starts`: what the simulation reads off `functionRaw`'s
function `F` (before pruning) for Cfg function `fd`. `functionRaw_lowered`
proves it.
-/

set_option autoImplicit false

namespace Compilatrix.Rt.Proof

open Compilatrix.Lir (Word)
open Compilatrix.Rt.Lower
open Compilatrix.Src (NatMap)

/-- No edge enters block 0, which is then the Lir entry itself. -/
def mergedOf (fd : Cfg.Fun) : Bool := !(fd.blocks.any fun b => b.term.edges.any fun x => x.target == 0)

/-- The variable supply: Cfg's variables are below it. -/
def supOf (fd : Cfg.Fun) : Nat := max fd.vars (maxVar fd + 1)

/-- The parameters of a block's chunk head. -/
def headParams (fd : Cfg.Fun) (i : Nat) (b : Cfg.Block) : List Nat :=
  if mergedOf fd && i == 0 then [] else b.params.map (·.1)

/-- **What a function's lowering lays out.** -/
structure Lowered (T : Tables) (f : Nat) (fd : Cfg.Fun) (F : Lir.Func) (starts : NatMap Nat) : Prop where
  edges : ∀ {i : Nat} {b : Cfg.Block} {e : Cfg.Edge}, fd.blocks[i]? = some b → e ∈ b.term.edges →
    e.back = decide (e.target ≤ i)
  chunk : ∀ {i : Nat} {b : Cfg.Block}, fd.blocks[i]? = some b → ∃ off C fr stF, starts.get? i = some off ∧
    Holds f F off starts C ∧ supOf fd ≤ fr ∧
    (blockCode f T (useCounts fd) i b).run (openSt fr (headParams fd i b)) = .ok ((), stF) ∧ Ext C stF ∧
    ¬ Open stF
  mono : ∀ {i j oi oj : Nat}, starts.get? i = some oi → starts.get? j = some oj → i ≤ j → oi ≤ oj
  head : ∀ {i : Nat} {b : Cfg.Block} {oi : Nat}, fd.blocks[i]? = some b → starts.get? i = some oi →
    ∃ tb, F.blocks[oi]? = some tb ∧ tb.params = headParams fd i b
  entry : ∀ {b0 : Cfg.Block}, fd.blocks[0]? = some b0 → ∃ o0, starts.get? 0 = some o0 ∧
    ((mergedOf fd = true ∧ o0 = 0 ∧ F.params = b0.params.map (·.1)) ∨
     (mergedOf fd = false ∧ F.blocks[0]? = some { term := .jump { target := o0, args := F.params.map .v } } ∧
      0 < o0 ∧ F.params.Nodup ∧ (∀ p ∈ F.params, supOf fd ≤ p) ∧ F.params.length = b0.params.length))

theorem misordered_none {fd : Cfg.Fun} (h : misordered fd = none) {i : Nat} {b : Cfg.Block} {e : Cfg.Edge}
    (hb : fd.blocks[i]? = some b) (he : e ∈ b.term.edges) : e.back = decide (e.target ≤ i) := by
  unfold misordered at h
  simp only [Option.map_eq_none_iff, List.find?_eq_none] at h
  have hmem : (b, i) ∈ fd.blocks.zipIdx := List.mem_zipIdx_iff_getElem?.2 (by simpa using hb)
  have := h (b, i) hmem
  simp at this
  exact this e he

/-- The head of a chunk: the block its lowering opened first. -/
theorem chunk_head {f : Fir.FunId} {F : Lir.Func} {off : Nat} {starts : NatMap Nat} {C : List PBlock}
    (hH : Holds f F off starts C) {fr : Nat} {ps : List Nat} {stF : St} (hg : Grows (openSt fr ps) stF)
    (hC : Ext C stF) (hno : ¬ Open stF) : ∃ tb, F.blocks[off]? = some tb ∧ tb.params = ps := by
  rcases hg.cur (open_openSt fr ps) with ⟨-, ho, -⟩ | ⟨b, hb, hp, -⟩
  · exact absurd ho hno
  · obtain ⟨lb, hres, hlb⟩ := hH (hC.done hb)
    obtain ⟨hlp, -, -⟩ := resolveBlock_ok hres
    exact ⟨lb, by simpa [openSt] using hlb, hlp.trans (by simpa [openSt] using hp)⟩


/-- The layout facts from the chunks and their placement, after the entry
blocks `entry` (`first` of them). -/
theorem lowered_of {T : Tables} {f : Nat} {fd : Cfg.Fun} {F : Lir.Func} {cs : List (List PBlock)}
    {sup' fr' first : Nat} {entry body : List Lir.Block} (hm : misordered fd = none)
    (hc : chunks f T (useCounts fd) (mergedOf fd) fd.blocks.zipIdx sup' = .ok (cs, fr'))
    (hr : resolveChunks f (chunkStarts first cs).1 cs.zipIdx = .ok body) (hsup : supOf fd ≤ sup')
    (hF : F.blocks = (entry ++ body).toArray) (hfirst : entry.length = first)
    (hentry : ∀ {b0 : Cfg.Block}, fd.blocks[0]? = some b0 →
      (mergedOf fd = true ∧ first = 0 ∧ F.params = b0.params.map (·.1)) ∨
      (mergedOf fd = false ∧ F.blocks[0]? = some { term := .jump { target := first, args := F.params.map .v } } ∧
        0 < first ∧ F.params.Nodup ∧ (∀ p ∈ F.params, supOf fd ≤ p) ∧ F.params.length = b0.params.length)) :
    Lowered T f fd F (chunkStarts first cs).1 ∧ cs.length = fd.blocks.length ∧
      ∀ i < cs.length, (chunkStarts first cs).1.get? i = some (chunkOff first cs i) := by
  obtain ⟨hlen, hcs⟩ := chunks_spec (k := 0) hc
  have hst : ∀ i < cs.length, (chunkStarts first cs).1.get? i = some (chunkOff first cs i) := by
    intro i hi
    rw [chunkStarts_get, if_pos hi]
  have hchunk : ∀ {i : Nat} {b : Cfg.Block}, fd.blocks[i]? = some b → ∃ off C fr stF,
      (chunkStarts first cs).1.get? i = some off ∧ Holds f F off (chunkStarts first cs).1 C ∧ supOf fd ≤ fr ∧
      (blockCode f T (useCounts fd) i b).run (openSt fr (headParams fd i b)) = .ok ((), stF) ∧ Ext C stF ∧
      ¬ Open stF := by
    intro i b hb
    obtain ⟨C, fr, stF, hC, hfr, hrun, hcb⟩ := hcs hb
    have hi : i < cs.length := (List.getElem?_eq_some_iff.1 hC).1
    obtain ⟨hext, hno, -⟩ := chunkBlocks_ok hcb
    refine ⟨chunkOff first cs i, C, fr, stF, hst i hi, fun {j b'} hj => ?_, Nat.le_trans hsup hfr,
      by simpa [headParams] using hrun, hext, hno⟩
    obtain ⟨lb, hres, hbody⟩ := resolveChunks_spec (k := 0) hr hC hj
    refine ⟨lb, ?_, ?_⟩
    · rw [Nat.zero_add] at hres
      simpa [NatMap.getD, hst i hi] using hres
    · rw [hF, List.getElem?_toArray, chunkOff, ← hfirst, Nat.add_assoc, List.getElem?_append_right (by omega)]
      simpa using hbody
  refine ⟨⟨fun hb he => misordered_none hm hb he, hchunk, ?_, ?_, ?_⟩, by simpa using hlen, hst⟩
  · intro i j oi oj hi hj hij
    rw [chunkStarts_get] at hi hj
    split at hi
    · split at hj
      · cases hi; cases hj; exact chunkOff_mono first cs hij
      · cases hj
    · cases hi
  · intro i b oi hb hoi
    obtain ⟨off, C, fr, stF, hoff, hH, -, hrun, hext, hno⟩ := hchunk hb
    rw [hoi] at hoff
    cases hoff
    exact chunk_head hH (blockCode_grows hrun (labels_openSt _ _) (open_openSt _ _)) hext hno
  · intro b0 hb0
    have h0 : 0 < cs.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.1 hb0).1
    refine ⟨first, by simpa [chunkOff] using hst 0 h0, ?_⟩
    rcases hentry hb0 with ⟨h1, h2, h3⟩ | h
    · exact .inl ⟨h1, h2, h3⟩
    · exact .inr h


/-- **`functionRaw` lays its function out as `Lowered` says.** -/
theorem functionRaw_lowered {T : Tables} {f : Nat} {fd : Cfg.Fun} {params : List Nat} {raw : List Lir.Block}
    (h : functionRaw T f fd = .ok (params, raw)) (name : String) (conv : Lir.Conv) :
    ∃ starts, Lowered T f fd { name, params, results := 1, blocks := raw.toArray, conv } starts := by
  unfold functionRaw at h
  cases hb : fd.blocks.head? with
  | none => simp [hb, throw, throwThe, MonadExceptOf.throw, Except.bind] at h
  | some b0 =>
    have hb0 : fd.blocks[0]? = some b0 := by
      cases hbl : fd.blocks with
      | nil => simp [hbl] at hb
      | cons c l => simp only [hbl, List.head?_cons, Option.some.injEq] at hb; simp [hb]
    simp only [hb, bind, Except.bind] at h
    cases hm : misordered fd with
    | some b => simp [hm, throw, throwThe, MonadExceptOf.throw, Except.bind] at h
    | none =>
      simp only [hm] at h
      generalize hmg : (!fd.blocks.any fun b => b.term.edges.any fun x => x.target == 0) = mg at h
      have hmerged : mergedOf fd = mg := hmg
      generalize hsup : max fd.vars (maxVar fd + 1) = sup at h
      have hsupOf : supOf fd = sup := hsup
      cases mg with
      | true =>
        simp only [↓reduceIte] at h
        cases hc : chunks f T (useCounts fd) true fd.blocks.zipIdx sup with
        | error e => simp [hc] at h
        | ok v =>
          obtain ⟨cs, fr'⟩ := v
          simp only [hc] at h
          cases hr : resolveChunks f (chunkStarts 0 cs).1 cs.zipIdx with
          | error e => simp [hr] at h
          | ok body =>
            simp only [hr, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨_, (lowered_of (entry := []) (first := 0) hm (by rw [hmerged]; exact hc) hr
              (Nat.le_of_eq hsupOf) rfl rfl ?_).1⟩
            intro b0' hb0'
            rw [hb0] at hb0'
            cases hb0'
            exact .inl ⟨hmerged, rfl, rfl⟩
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        cases hc : chunks f T (useCounts fd) false fd.blocks.zipIdx (sup + b0.params.length) with
        | error e => simp [hc] at h
        | ok v =>
          obtain ⟨cs, fr'⟩ := v
          simp only [hc] at h
          cases hr : resolveChunks f (chunkStarts 1 cs).1 cs.zipIdx with
          | error e => simp [hr] at h
          | ok body =>
            simp only [hr, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hlen, -⟩ := chunks_spec (k := 0) hc
            have h0 : 0 < cs.length := by rw [hlen]; exact (List.getElem?_eq_some_iff.1 hb0).1
            have hs0 : (chunkStarts 1 cs).1.getD 0 1 = 1 := by
              simp [NatMap.getD, chunkStarts_get, h0, chunkOff]
            refine ⟨_, (lowered_of (first := 1) hm (by rw [hmerged]; exact hc) hr
              (by rw [hsupOf]; omega) rfl rfl ?_).1⟩
            intro b0' hb0'
            rw [hb0] at hb0'
            cases hb0'
            refine .inr ⟨hmerged, by simp [hs0], by omega, ?_, ?_, by simp⟩
            · exact List.Pairwise.map _ (fun a b h e => h (by simp at e; omega)) List.nodup_range
            · intro p hp
              simp only [List.mem_map, List.mem_range] at hp
              obtain ⟨a, -, rfl⟩ := hp
              rw [hsupOf]
              omega

/-- Variables a block defines are below the supply. -/
theorem foldl_max_ge : ∀ (l : List Nat) (a : Nat), a ≤ l.foldl max a ∧ ∀ y ∈ l, y ≤ l.foldl max a
  | [], a => ⟨Nat.le_refl _, fun y h => by simp at h⟩
  | x :: l, a => by
    obtain ⟨h1, h2⟩ := foldl_max_ge l (max a x)
    refine ⟨by simp only [List.foldl_cons]; omega, fun y hy => ?_⟩
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hy with rfl | hy
    · omega
    · exact h2 y hy

theorem defs_lt_sup {fd : Cfg.Fun} {i : Nat} {b : Cfg.Block} (hb : fd.blocks[i]? = some b) {y : Nat}
    (hy : y ∈ Cfg.Check.blockDefs b) : y < supOf fd := by
  have hmem : y ∈ fd.blocks.flatMap Cfg.Check.blockDefs :=
    List.mem_flatMap.2 ⟨b, List.mem_of_getElem? hb, hy⟩
  have := (foldl_max_ge _ 0).2 y hmem
  unfold supOf maxVar
  omega

end Compilatrix.Rt.Proof
