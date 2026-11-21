import IxVMRefinement.Ingress.Prim
import IxVMRefinement.Obs.Blake3

/-! # BLAKE3's compression function at source level

`Blake3::g_function`, `Blake3::compress_inner_j`, `Blake3::compress` and
`Blake3::compress_init` as the observed source semantics evaluates them, against
`Blake3.Pure.compress` (through the models of `Aiur.Library.Blake3`: `compressInnerJ`,
`permute`, `finalizeState`, `compress_spec`).

`compress_inner_j` has no generated path lemmas (its eight `g` steps and thirty-two
updates exceed the generator's variable-lookup budget); it is inverted here one `g` step
at a time (`gStep_inv`), against its elaborated body (`cij_body`).
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

open Aiur Aiur.Generic Aiur.Generic.SourceSemantics

namespace IxVM.Refinement.Ingress

open IxVM (F)
open IxVM.Refinement.Obs
open Aiur.Library.Blake3 (wordOfBytes wordOfBytes_toNat)

/-! ## Vectors of words and the compression state -/

/-- **A vector of words** (a chaining value `[U32; 8]`, a block `[U32; 16]`). -/
def vecV {n : Nat} (v : Vector UInt32 n) : SourceValue F :=
  .tuple (List.ofFn fun k : Fin n => wv v[k])

/-- **`compress`'s state** `[U32; 32]`: the sixteen state words, then the sixteen message
words. -/
def stateV (s m : Blake3.Pure.Block) : SourceValue F :=
  .tuple (List.ofFn (fun k : Fin 16 => (wv s[k] : SourceValue F)) ++
    List.ofFn (fun k : Fin 16 => (wv m[k] : SourceValue F)))

theorem vecV_four (v : Vector UInt32 4) :
    (vecV v : SourceValue F) = .tuple [wv v[0], wv v[1], wv v[2], wv v[3]] := rfl

theorem proj_vecV {n : Nat} (v : Vector UInt32 n) (i : Nat) (hi : i < n) :
    projectValue (vecV v : SourceValue F) i = .ok (wv v[i]) := by
  have hl : i < (List.ofFn fun k : Fin n => (wv v[k] : SourceValue F)).length := by simpa using hi
  rw [vecV, proj_getElem _ _ hl]
  simp

/-- The state's word list. -/
def stateL (s m : Blake3.Pure.Block) : List (SourceValue F) :=
  List.ofFn (fun k : Fin 16 => (wv s[k] : SourceValue F)) ++
    List.ofFn (fun k : Fin 16 => (wv m[k] : SourceValue F))

theorem stateV_eq (s m : Blake3.Pure.Block) : (stateV s m : SourceValue F) = .tuple (stateL s m) :=
  rfl

theorem stateL_length (s m : Blake3.Pure.Block) : (stateL s m : List (SourceValue F)).length = 32 := by
  simp [stateL]

theorem proj_stateV_lo (s m : Blake3.Pure.Block) (i : Nat) (hi : i < 16) :
    projectValue (stateV s m : SourceValue F) i = .ok (wv s[i]) := by
  have hl : i < (stateL s m : List (SourceValue F)).length := by rw [stateL_length]; omega
  have hl' : i < (List.ofFn (fun k : Fin 16 => (wv s[k] : SourceValue F))).length := by
    simpa using hi
  rw [stateV_eq, proj_getElem _ _ hl]
  simp only [stateL]
  rw [List.getElem_append_left hl', List.getElem_ofFn]
  first
  | rfl
  | (simp [Fin.getElem_fin]; done)

theorem proj_stateV_hi (s m : Blake3.Pure.Block) (j : Nat) (hj : j < 16) :
    projectValue (stateV s m : SourceValue F) (16 + j) = .ok (wv m[j]) := by
  have hl : 16 + j < (stateL s m : List (SourceValue F)).length := by rw [stateL_length]; omega
  have hl' : (List.ofFn (fun k : Fin 16 => (wv s[k] : SourceValue F))).length ≤ 16 + j := by
    simp
  rw [stateV_eq, proj_getElem _ _ hl]
  simp only [stateL]
  rw [List.getElem_append_right hl', List.getElem_ofFn]
  first
  | (simp [Fin.getElem_fin]; done)
  | (simp; done)

/-! ## Updates of a tuple -/

theorem mapM_some_eq {α β : Type} (f : α → Option β) (g : α → β) (hfg : ∀ a, f a = some (g a)) :
    ∀ l : List α, l.mapM f = some (l.map g)
  | [] => rfl
  | a :: l => by simp [List.mapM_cons, hfg, mapM_some_eq f g hfg l]

theorem zipIdx_map_set {α : Type} (vs : List α) (i : Nat) (x : α) :
    (vs.zipIdx.map fun p => if p.2 == i then x else p.1) = vs.set i x := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.getElem_map, List.getElem_zipIdx, List.getElem_set]
  by_cases hij : i = j
  · subst hij; simp
  · have hji : j ≠ i := fun e => hij e.symm
    simp [hij, hji]

theorem mapM_zipIdx_set {α : Type} (vs : List α) (i : Nat) (x : α) :
    (vs.zipIdx.mapM fun p => if (p.2 == i) = true then (some x : Option α) else some p.1) =
      some (vs.set i x) := by
  rw [mapM_some_eq _ (fun p => if (p.2 == i) = true then x else p.1)
    (fun p => by by_cases h : (p.2 == i) = true <;> simp [h]), zipIdx_map_set]

theorem mapM_zipIdx_set' {α : Type} (vs : List α) (i : Nat) (x : α) :
    (vs.zipIdx.mapM fun p => if p.2 = i then (some x : Option α) else some p.1) =
      some (vs.set i x) := by
  simpa using mapM_zipIdx_set vs i x

/-- **An update of one component of a tuple** replaces it. -/
theorem update_index (types : List (String × Aiur.Generic.Ty)) (vs : List (SourceValue F))
    (i n : Nat) (x : SourceValue F) (hn : vs.length = n) :
    Update.value types [[.index i n]] [.tuple vs, x] = .ok (.tuple (vs.set i x)) := by
  subst hn
  simp only [Update.value, Update.apply, Update.replace, Update.unpack, Update.pack,
    UpdateStep.owner, UpdateStep.width, UpdateStep.position]
  first
  | (simp only [Option.bind_some, mapM_zipIdx_set]; rfl)
  | (simp only [Option.bind_some, mapM_zipIdx_set]; done)
  | (simp only [ite_true, Option.bind_some, mapM_zipIdx_set]; rfl)
  | (simp [mapM_zipIdx_set, mapM_zipIdx_set']; done)
  | (simp [mapM_zipIdx_set']; rfl)

theorem update_inv {types : List (String × Aiur.Generic.Ty)} {vs : List (SourceValue F)}
    {i n : Nat} {x v : SourceValue F} (hn : vs.length = n)
    (h : Update.value types [[.index i n]] [.tuple vs, x] = .ok v) : v = .tuple (vs.set i x) := by
  rw [update_index types vs i n x hn] at h
  exact (Except.ok.inj h).symm

theorem ofFn_set (v : Vector UInt32 16) (i : Nat) (hi : i < 16) (w : UInt32) :
    (List.ofFn fun k : Fin 16 => (wv v[k] : SourceValue F)).set i (wv w) =
      List.ofFn fun k : Fin 16 => (wv (v.set i w hi)[k] : SourceValue F) := by
  apply List.ext_getElem (by simp)
  intro k h1 h2
  simp only [List.getElem_set, List.getElem_ofFn, Fin.getElem_fin, Vector.getElem_set]
  by_cases h : i = k <;> simp [h]

theorem update_stateV (types : List (String × Aiur.Generic.Ty)) (s m : Blake3.Pure.Block)
    (i : Fin 16) (w : UInt32) :
    Update.value types [[.index i.val 32]] [stateV s m, wv w] = .ok (stateV (s.set i w) m) := by
  rw [stateV_eq, update_index types (stateL s m) i.val 32 (wv w) (stateL_length s m), stateV_eq]
  congr 2
  have hi : i.val < (List.ofFn (fun k : Fin 16 => (wv s[k] : SourceValue F))).length := by simp
  simp only [stateL]
  rw [List.set_append_left i.val (wv w) hi, ofFn_set s i.val i.isLt w]

theorem update_stateV_hi (types : List (String × Aiur.Generic.Ty)) (s m : Blake3.Pure.Block)
    (j : Fin 16) (w : UInt32) :
    Update.value types [[.index (16 + j.val) 32]] [stateV s m, wv w] = .ok (stateV s (m.set j w)) := by
  rw [stateV_eq, update_index types (stateL s m) (16 + j.val) 32 (wv w) (stateL_length s m), stateV_eq]
  congr 2
  apply List.ext_getElem (by simp [stateL])
  intro k h1 h2
  simp only [stateL, List.getElem_set]
  by_cases hlt : k < 16
  · have hne : 16 + j.val ≠ k := by omega
    have hl : k < (List.ofFn (fun i : Fin 16 => (wv s[i] : SourceValue F))).length := by simpa using hlt
    simp only [hne, ↓reduceIte, List.getElem_append_left hl]
  · have hge : (List.ofFn (fun i : Fin 16 => (wv s[i] : SourceValue F))).length ≤ k := by simp; omega
    rw [List.getElem_append_right hge, List.getElem_append_right hge]
    simp only [List.length_ofFn, List.getElem_ofFn, Fin.getElem_fin, Vector.getElem_set]
    by_cases heq : 16 + j.val = k
    · subst heq; simp
    · have hj' : j.val ≠ k - 16 := by omega
      simp [heq, hj']

theorem update_stateV_hi_inv {s m : Blake3.Pure.Block} {j : Fin 16} {w : UInt32} {v : SourceValue F}
    (h : Update.value [] [[.index (16 + j.val) 32]] [stateV s m, wv w] = .ok v) :
    v = stateV s (m.set j w) := by
  rw [update_stateV_hi [] s m j w] at h
  exact (Except.ok.inj h).symm

theorem permute_eq_sets (m : Blake3.Pure.Block) :
    ((((((((((((((((m.set 0 m[2]).set 1 m[6]).set 2 m[3]).set 3 m[10]).set 4 m[7]).set
      5 m[0]).set 6 m[4]).set 7 m[13]).set 8 m[1]).set 9 m[11]).set 10 m[12]).set
      11 m[5]).set 12 m[9]).set 13 m[14]).set 14 m[15]).set 15 m[8]) =
      Aiur.Library.Blake3.permute m := by
  apply Vector.ext
  intro i hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
      i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Aiur.Library.Blake3.permute, Vector.getElem_set]

theorem permute16_inv {s m s1 : Blake3.Pure.Block}
    {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15
      u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 : SourceValue F}
    (pr0 : projectValue (stateV s m : SourceValue F) 18 = .ok x0)
    (up0 : Update.value [] [[.index 16 32]] [stateV s1 m, x0] = .ok u0)
    (pr1 : projectValue (stateV s m : SourceValue F) 22 = .ok x1)
    (up1 : Update.value [] [[.index 17 32]] [u0, x1] = .ok u1)
    (pr2 : projectValue (stateV s m : SourceValue F) 19 = .ok x2)
    (up2 : Update.value [] [[.index 18 32]] [u1, x2] = .ok u2)
    (pr3 : projectValue (stateV s m : SourceValue F) 26 = .ok x3)
    (up3 : Update.value [] [[.index 19 32]] [u2, x3] = .ok u3)
    (pr4 : projectValue (stateV s m : SourceValue F) 23 = .ok x4)
    (up4 : Update.value [] [[.index 20 32]] [u3, x4] = .ok u4)
    (pr5 : projectValue (stateV s m : SourceValue F) 16 = .ok x5)
    (up5 : Update.value [] [[.index 21 32]] [u4, x5] = .ok u5)
    (pr6 : projectValue (stateV s m : SourceValue F) 20 = .ok x6)
    (up6 : Update.value [] [[.index 22 32]] [u5, x6] = .ok u6)
    (pr7 : projectValue (stateV s m : SourceValue F) 29 = .ok x7)
    (up7 : Update.value [] [[.index 23 32]] [u6, x7] = .ok u7)
    (pr8 : projectValue (stateV s m : SourceValue F) 17 = .ok x8)
    (up8 : Update.value [] [[.index 24 32]] [u7, x8] = .ok u8)
    (pr9 : projectValue (stateV s m : SourceValue F) 27 = .ok x9)
    (up9 : Update.value [] [[.index 25 32]] [u8, x9] = .ok u9)
    (pr10 : projectValue (stateV s m : SourceValue F) 28 = .ok x10)
    (up10 : Update.value [] [[.index 26 32]] [u9, x10] = .ok u10)
    (pr11 : projectValue (stateV s m : SourceValue F) 21 = .ok x11)
    (up11 : Update.value [] [[.index 27 32]] [u10, x11] = .ok u11)
    (pr12 : projectValue (stateV s m : SourceValue F) 25 = .ok x12)
    (up12 : Update.value [] [[.index 28 32]] [u11, x12] = .ok u12)
    (pr13 : projectValue (stateV s m : SourceValue F) 30 = .ok x13)
    (up13 : Update.value [] [[.index 29 32]] [u12, x13] = .ok u13)
    (pr14 : projectValue (stateV s m : SourceValue F) 31 = .ok x14)
    (up14 : Update.value [] [[.index 30 32]] [u13, x14] = .ok u14)
    (pr15 : projectValue (stateV s m : SourceValue F) 24 = .ok x15)
    (up15 : Update.value [] [[.index 31 32]] [u14, x15] = .ok u15) :
    u15 = stateV s1 (Aiur.Library.Blake3.permute m) := by
  obtain rfl := ok_inj ((proj_stateV_hi s m 2 (by decide)).symm.trans pr0)
  obtain rfl := update_stateV_hi_inv (j := 0) up0
  obtain rfl := ok_inj ((proj_stateV_hi s m 6 (by decide)).symm.trans pr1)
  obtain rfl := update_stateV_hi_inv (j := 1) up1
  obtain rfl := ok_inj ((proj_stateV_hi s m 3 (by decide)).symm.trans pr2)
  obtain rfl := update_stateV_hi_inv (j := 2) up2
  obtain rfl := ok_inj ((proj_stateV_hi s m 10 (by decide)).symm.trans pr3)
  obtain rfl := update_stateV_hi_inv (j := 3) up3
  obtain rfl := ok_inj ((proj_stateV_hi s m 7 (by decide)).symm.trans pr4)
  obtain rfl := update_stateV_hi_inv (j := 4) up4
  obtain rfl := ok_inj ((proj_stateV_hi s m 0 (by decide)).symm.trans pr5)
  obtain rfl := update_stateV_hi_inv (j := 5) up5
  obtain rfl := ok_inj ((proj_stateV_hi s m 4 (by decide)).symm.trans pr6)
  obtain rfl := update_stateV_hi_inv (j := 6) up6
  obtain rfl := ok_inj ((proj_stateV_hi s m 13 (by decide)).symm.trans pr7)
  obtain rfl := update_stateV_hi_inv (j := 7) up7
  obtain rfl := ok_inj ((proj_stateV_hi s m 1 (by decide)).symm.trans pr8)
  obtain rfl := update_stateV_hi_inv (j := 8) up8
  obtain rfl := ok_inj ((proj_stateV_hi s m 11 (by decide)).symm.trans pr9)
  obtain rfl := update_stateV_hi_inv (j := 9) up9
  obtain rfl := ok_inj ((proj_stateV_hi s m 12 (by decide)).symm.trans pr10)
  obtain rfl := update_stateV_hi_inv (j := 10) up10
  obtain rfl := ok_inj ((proj_stateV_hi s m 5 (by decide)).symm.trans pr11)
  obtain rfl := update_stateV_hi_inv (j := 11) up11
  obtain rfl := ok_inj ((proj_stateV_hi s m 9 (by decide)).symm.trans pr12)
  obtain rfl := update_stateV_hi_inv (j := 12) up12
  obtain rfl := ok_inj ((proj_stateV_hi s m 14 (by decide)).symm.trans pr13)
  obtain rfl := update_stateV_hi_inv (j := 13) up13
  obtain rfl := ok_inj ((proj_stateV_hi s m 15 (by decide)).symm.trans pr14)
  obtain rfl := update_stateV_hi_inv (j := 14) up14
  obtain rfl := ok_inj ((proj_stateV_hi s m 8 (by decide)).symm.trans pr15)
  obtain rfl := update_stateV_hi_inv (j := 15) up15
  exact congrArg (stateV s1) (permute_eq_sets m)

/-! ## Matching the four results of `g` -/

theorem matchArray4 {types : List (String × Aiur.Generic.Ty)} (heap : Heap F)
    (x0 x1 x2 x3 : SourceValue F) :
    W.matchPattern types heap (.array [.bind "a", .bind "b", .bind "c", .bind "d"])
        (.tuple [x0, x1, x2, x3]) =
      .ok (some [("a", x0), ("b", x1), ("c", x2), ("d", x3)]) := by
  rw [matchPattern_array]
  simp [matchListWith, matchPattern_bind, bind, Except.bind, pure, Except.pure]

/-! ## `Blake3::iv` and `Blake3::g_function` -/

theorem iv_bytes : (Blake3.Pure.iv : Blake3.Pure.CV) =
    #v[wordOfBytes 103 230 9 106, wordOfBytes 133 174 103 187, wordOfBytes 114 243 110 60,
      wordOfBytes 58 245 79 165, wordOfBytes 127 82 14 81, wordOfBytes 140 104 5 155,
      wordOfBytes 171 217 131 31, wordOfBytes 25 205 224 91] :=
  Aiur.Library.Blake3.iv_spec.symm

/-- A literal byte as the circuit writes it. -/
theorem w4_lit (b0 b1 b2 b3 : UInt8) :
    (w4 b0 b1 b2 b3 : SourceValue F) =
      .tuple [.field (b0.toNat : F), .field (b1.toNat : F), .field (b2.toNat : F),
        .field (b3.toNat : F)] := rfl

/-- **`Blake3::iv()`** is BLAKE3's initialization vector. -/
theorem iv_src {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)}
    (ev : ObsFn W "Blake3::iv" [] h r h' cs) : r = vecV Blake3.Pure.iv ∧ h' = h := by
  obtain ⟨v3, v4, v5, v6, v7, v8, v9, v10, m13, cs21, m62, cs70, m111, cs119, m160, cs168, m209,
    cs217, m258, cs266, m307, cs315, m356, cs364, rfl, ev23, ev72, ev121, ev170, ev219, ev268,
    ev317, ev366, rfl, -⟩ := «Blake3::iv».obs ev
  obtain ⟨rfl, rfl⟩ := u32_fromBytes ev23
  obtain ⟨rfl, rfl⟩ := u32_fromBytes ev72
  obtain ⟨rfl, rfl⟩ := u32_fromBytes ev121
  obtain ⟨rfl, rfl⟩ := u32_fromBytes ev170
  obtain ⟨rfl, rfl⟩ := u32_fromBytes ev219
  obtain ⟨rfl, rfl⟩ := u32_fromBytes ev268
  obtain ⟨rfl, rfl⟩ := u32_fromBytes ev317
  obtain ⟨rfl, rfl⟩ := u32_fromBytes ev366
  refine ⟨?_, rfl⟩
  rw [iv_bytes]
  have e : (vecV #v[wordOfBytes 103 230 9 106, wordOfBytes 133 174 103 187, wordOfBytes 114 243 110 60,
      wordOfBytes 58 245 79 165, wordOfBytes 127 82 14 81, wordOfBytes 140 104 5 155,
      wordOfBytes 171 217 131 31, wordOfBytes 25 205 224 91] : SourceValue F) =
      .tuple [wv (wordOfBytes 103 230 9 106), wv (wordOfBytes 133 174 103 187),
        wv (wordOfBytes 114 243 110 60), wv (wordOfBytes 58 245 79 165),
        wv (wordOfBytes 127 82 14 81), wv (wordOfBytes 140 104 5 155),
        wv (wordOfBytes 171 217 131 31), wv (wordOfBytes 25 205 224 91)] := rfl
  rw [e]
  simp only [wv_wordOfBytes, w4_lit]
  first
  | (simp; done)
  | (norm_num; done)
  | rfl

/-- **`Blake3::g_function` computes BLAKE3's `mix`** on words. -/
theorem g_function_spec {a b c d x y : UInt32} {r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W "Blake3::g_function" [wv a, wv b, wv c, wv d, wv x, wv y] h r h' cs) :
    r = vecV (Blake3.Pure.mix a b c d x y) ∧ h' = h := by
  obtain ⟨v1, m2, cs12, v39, m40, cs50, v53, m55, cs63, v82, m83, cs93, v112, m113, cs123, v142,
    m143, cs153, v180, m181, cs191, v194, m196, cs204, v223, m224, cs234, v253, m254, cs264, ev14,
    ev65, ev52, ev95, ev125, ev155, ev206, ev193, ev236, ev266, rfl, rfl, -⟩ :=
    «Blake3::g_function».obs ev
  obtain ⟨rfl, rfl⟩ := u32_add3 ev14
  obtain ⟨rfl, rfl⟩ := u32_xor ev65
  obtain ⟨rfl, rfl⟩ := u32_rotr16 ev52
  obtain ⟨rfl, rfl⟩ := u32_add ev95
  obtain ⟨rfl, rfl⟩ := u32_xor_rotr12 ev125
  obtain ⟨rfl, rfl⟩ := u32_add3 ev155
  obtain ⟨rfl, rfl⟩ := u32_xor ev206
  obtain ⟨rfl, rfl⟩ := u32_rotr8 ev193
  obtain ⟨rfl, rfl⟩ := u32_add ev236
  obtain ⟨rfl, rfl⟩ := u32_xor_rotr7 ev266
  exact ⟨rfl, rfl⟩

/-! ## `Blake3::compress_inner_j`, one `g` step at a time -/

/-- One `g` step of `compress_inner_j`'s body: `g_function` on four state words and two
message words, then the four updates. -/
def gStep (a b c d : Fin 16) (jx jy : Nat) (rest : Aiur.Generic.Expr F) : Aiur.Generic.Expr F :=
  .letValue (.array [.bind "a", .bind "b", .bind "c", .bind "d"])
    (.call "Blake3::g_function" (some [])
      [.index (.var "state") a.val, .index (.var "state") b.val, .index (.var "state") c.val,
        .index (.var "state") d.val, .index (.var "state") (16 + jx),
        .index (.var "state") (16 + jy)])
    (.letValue (.bind "state") (.update [[.index a.val 32]] [.var "state", .var "a"])
      (.letValue (.bind "state") (.update [[.index b.val 32]] [.var "state", .var "b"])
        (.letValue (.bind "state") (.update [[.index c.val 32]] [.var "state", .var "c"])
          (.letValue (.bind "state") (.update [[.index d.val 32]] [.var "state", .var "d"])
            rest))))

/-- The elaborated body of `compress_inner_j`: its eight `g` steps. -/
def cijExpr : Aiur.Generic.Expr F :=
  gStep 0 4 8 12 0 1 (gStep 1 5 9 13 2 3 (gStep 2 6 10 14 4 5 (gStep 3 7 11 15 6 7
    (gStep 0 5 10 15 8 9 (gStep 1 6 11 12 10 11 (gStep 2 7 8 13 12 13 (gStep 3 4 9 14 14 15
      (.var "state"))))))))

theorem cij_body : IxVM.Blake3.compress_inner_j.body = cijExpr := rfl

theorem idx_inv {types : List (String × Aiur.Generic.Ty)} {locals : Environment F Nat}
    {st : SourceValue F} (hloc : locals.find? (·.1 == "state") = some ("state", st)) {k : Nat}
    {before after : Heap F} {v : SourceValue F} {c : List (Call F)}
    (d : ObsExpr W types locals (.index (.var "state") k) before v after c) :
    projectValue st k = .ok v ∧ after = before := by
  obtain ⟨inp, dv, pr⟩ := d.index_inv
  obtain ⟨l, rfl, rfl⟩ := dv.var_inv
  obtain rfl := (Prod.mk.inj (Option.some.inj (hloc.symm.trans l))).2
  exact ⟨pr, rfl⟩

/-- **One update step of `compress_inner_j`**: `let state = (state with { [i] = n })`. -/
theorem updStep_inv {types : List (String × Aiur.Generic.Ty)} {locals : Environment F Nat}
    {s m : Blake3.Pure.Block} {i : Fin 16} {n : String} {w : UInt32} {rest : Aiur.Generic.Expr F}
    {before after : Heap F} {result : SourceValue F} {calls : List (Call F)}
    (hs : locals.find? (·.1 == "state") = some ("state", stateV s m))
    (hn : locals.find? (·.1 == n) = some (n, wv w))
    (ev : ObsExpr W types locals (.letValue (.bind "state")
      (.update [[.index i.val 32]] [.var "state", .var n]) rest) before result after calls) :
    ∃ calls', ObsExpr W types (("state", stateV (s.set i w) m) :: locals) rest before result after
      calls' := by
  obtain ⟨v, m1, bs, c1, c2, dx, mt, db, rfl⟩ := ev.letValue_inv
  obtain ⟨vals, au, up⟩ := dx.update_inv
  obtain ⟨v1, vs1, m2, c3, c4, rfl, d1, a1, rfl⟩ := au.cons_inv
  obtain ⟨l1, rfl, rfl⟩ := d1.var_inv
  obtain rfl := (Prod.mk.inj (Option.some.inj (hs.symm.trans l1))).2
  obtain ⟨v2, vs2, m3, c5, c6, rfl, d2, a2, rfl⟩ := a1.cons_inv
  obtain ⟨l2, rfl, rfl⟩ := d2.var_inv
  obtain rfl := (Prod.mk.inj (Option.some.inj (hn.symm.trans l2))).2
  obtain ⟨rfl, rfl, rfl⟩ := a2.nil_inv
  rw [update_stateV] at up
  cases up
  rw [matchPattern_bind] at mt
  cases mt
  exact ⟨_, db⟩

theorem find_skip4 {locals : Environment F Nat} {st : SourceValue F}
    (hloc : locals.find? (·.1 == "state") = some ("state", st)) (x0 x1 x2 x3 : SourceValue F) :
    ([("a", x0), ("b", x1), ("c", x2), ("d", x3)] ++ locals).find? (·.1 == "state") =
      some ("state", st) := by
  first
  | simpa using hloc
  | (simp only [List.cons_append, List.nil_append, List.find?_cons]; simpa using hloc)
  | exact hloc

/-- **One `g` step of `compress_inner_j`** computes `Blake3.Pure.g` on the state it reads. -/
theorem gStep_inv {types : List (String × Aiur.Generic.Ty)} {locals : Environment F Nat}
    {s m : Blake3.Pure.Block} {a b c d : Fin 16} {jx jy : Nat} (hjx : jx < 16) (hjy : jy < 16)
    {rest : Aiur.Generic.Expr F} {before after : Heap F} {result : SourceValue F}
    {calls : List (Call F)}
    (hloc : locals.find? (·.1 == "state") = some ("state", stateV s m))
    (ev : ObsExpr W types locals (gStep a b c d jx jy rest) before result after calls) :
    ∃ (locals' : Environment F Nat) (calls' : List (Call F)),
      locals'.find? (·.1 == "state") =
        some ("state", stateV (Blake3.Pure.g s a b c d m[jx] m[jy]) m) ∧
      ObsExpr W types locals' rest before result after calls' := by
  unfold gStep at ev
  obtain ⟨v, m1, bs, c1, c2, dx, mt, db, rfl⟩ := ev.letValue_inv
  obtain ⟨vs, mid, ca, cg, args, evg, rfl⟩ := dx.call_inv
  rw [instanceName_plain_some] at evg
  obtain ⟨u1, us1, n1, e1, f1, rfl, d1, a1, rfl⟩ := args.cons_inv
  obtain ⟨p1, rfl⟩ := idx_inv hloc d1
  obtain rfl := ok_inj ((proj_stateV_lo s m a.val a.isLt).symm.trans p1)
  obtain ⟨u2, us2, n2, e2, f2, rfl, d2, a2, rfl⟩ := a1.cons_inv
  obtain ⟨p2, rfl⟩ := idx_inv hloc d2
  obtain rfl := ok_inj ((proj_stateV_lo s m b.val b.isLt).symm.trans p2)
  obtain ⟨u3, us3, n3, e3, f3, rfl, d3, a3, rfl⟩ := a2.cons_inv
  obtain ⟨p3, rfl⟩ := idx_inv hloc d3
  obtain rfl := ok_inj ((proj_stateV_lo s m c.val c.isLt).symm.trans p3)
  obtain ⟨u4, us4, n4, e4, f4, rfl, d4, a4, rfl⟩ := a3.cons_inv
  obtain ⟨p4, rfl⟩ := idx_inv hloc d4
  obtain rfl := ok_inj ((proj_stateV_lo s m d.val d.isLt).symm.trans p4)
  obtain ⟨u5, us5, n5, e5, f5, rfl, d5, a5, rfl⟩ := a4.cons_inv
  obtain ⟨p5, rfl⟩ := idx_inv hloc d5
  obtain rfl := ok_inj ((proj_stateV_hi s m jx hjx).symm.trans p5)
  obtain ⟨u6, us6, n6, e6, f6, rfl, d6, a6, rfl⟩ := a5.cons_inv
  obtain ⟨p6, rfl⟩ := idx_inv hloc d6
  obtain rfl := ok_inj ((proj_stateV_hi s m jy hjy).symm.trans p6)
  obtain ⟨rfl, rfl, rfl⟩ := a6.nil_inv
  obtain ⟨rfl, rfl⟩ := g_function_spec evg
  rw [vecV_four, matchArray4] at mt
  cases mt
  obtain ⟨c5, db1⟩ := updStep_inv (i := a) (n := "a") (find_skip4 hloc _ _ _ _)
    (by first | rfl | simp) db
  obtain ⟨c6, db2⟩ := updStep_inv (i := b) (n := "b") (by first | rfl | simp)
    (by first | rfl | simp) db1
  obtain ⟨c7, db3⟩ := updStep_inv (i := c) (n := "c") (by first | rfl | simp)
    (by first | rfl | simp) db2
  obtain ⟨c8, db4⟩ := updStep_inv (i := d) (n := "d") (by first | rfl | simp)
    (by first | rfl | simp) db3
  exact ⟨_, _, by first | rfl | simp, db4⟩

/-- **`Blake3::compress_inner_j` computes one BLAKE3 round** (`compressInnerJ`, which is
`Blake3.Pure.round` at the first schedule), leaving the message words in place. -/
theorem cij_spec {s m : Blake3.Pure.Block} {r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W "Blake3::compress_inner_j" [stateV s m] h r h' cs) :
    r = stateV (Aiur.Library.Blake3.compressInnerJ s m) m ∧ h' = h := by
  have d0 := ObsFn.function_inv (s := IxVM.source) IxVM.Blake3.compress_inner_j.lookup
    (by first | rfl | decide | simp [IxVM.Blake3.compress_inner_j, ControlLower.hasControl]) ev
  rw [cij_body] at d0
  obtain ⟨l1, k1, h1, d1⟩ := gStep_inv (s := s) (m := m) (a := 0) (b := 4) (c := 8) (d := 12)
    (jx := 0) (jy := 1) (by decide) (by decide)
    (by first | rfl | simp [IxVM.Blake3.compress_inner_j]) d0
  obtain ⟨l2, k2, h2, d2⟩ := gStep_inv (a := 1) (b := 5) (c := 9) (d := 13) (jx := 2) (jy := 3)
    (by decide) (by decide) h1 d1
  obtain ⟨l3, k3, h3, d3⟩ := gStep_inv (a := 2) (b := 6) (c := 10) (d := 14) (jx := 4) (jy := 5)
    (by decide) (by decide) h2 d2
  obtain ⟨l4, k4, h4, d4⟩ := gStep_inv (a := 3) (b := 7) (c := 11) (d := 15) (jx := 6) (jy := 7)
    (by decide) (by decide) h3 d3
  obtain ⟨l5, k5, h5, d5⟩ := gStep_inv (a := 0) (b := 5) (c := 10) (d := 15) (jx := 8) (jy := 9)
    (by decide) (by decide) h4 d4
  obtain ⟨l6, k6, h6, d6⟩ := gStep_inv (a := 1) (b := 6) (c := 11) (d := 12) (jx := 10) (jy := 11)
    (by decide) (by decide) h5 d5
  obtain ⟨l7, k7, h7, d7⟩ := gStep_inv (a := 2) (b := 7) (c := 8) (d := 13) (jx := 12) (jy := 13)
    (by decide) (by decide) h6 d6
  obtain ⟨l8, k8, h8, d8⟩ := gStep_inv (a := 3) (b := 4) (c := 9) (d := 14) (jx := 14) (jy := 15)
    (by decide) (by decide) h7 d7
  obtain ⟨l9, rfl, -⟩ := d8.var_inv
  obtain rfl := (Prod.mk.inj (Option.some.inj (h8.symm.trans l9))).2
  exact ⟨rfl, rfl⟩

/-! ## `Blake3::compress`: seven rounds and the finalization -/

/-- `n` rounds of `compress` from state `s` and message `m`: a round, then the message
permutation. -/
def compressRounds : Nat → Blake3.Pure.Block → Blake3.Pure.Block →
    Blake3.Pure.Block × Blake3.Pure.Block
  | 0, s, m => (s, m)
  | n + 1, s, m =>
    compressRounds n (Aiur.Library.Blake3.compressInnerJ s m) (Aiur.Library.Blake3.permute m)

theorem compressRounds_seven (s m : Blake3.Pure.Block) :
    (compressRounds 7 s m).1 = Aiur.Library.Blake3.compressInnerI s m := rfl

theorem natCast_three_inj {k : Nat} (hk : k < 1024) (h : (k : F) = 3) : k = 3 :=
  IxVM.natCast_inj hk (by omega) (by simpa using h)

/-- **`Blake3::compress(stage, state)`** runs two rounds per row for `stage = 0, 1, 2` and the
seventh round plus finalization on `stage = 3`. -/
theorem compress_spec : ∀ (n : Nat) {k : Nat} {s m : Blake3.Pure.Block} {stage state : SourceValue F}
    {r : SourceValue F} {h h' : Heap F} {cs : List (Call F)},
    k + n = 3 → stage = .field (k : F) → state = stateV s m →
    ObsFn W "Blake3::compress" [stage, state] h r h' cs →
    r = vecV (Aiur.Library.Blake3.finalizeState (compressRounds (2 * n + 1) s m).1) ∧ h' = h
  | 0, k, s, m, stage, state, r, h, h', cs, hk, hst, hs, ev => by
    subst hst hs
    match «Blake3::compress».obs ev with
    | .n3 (ev_dvofuqkd := ev_cij) (pr_njzqpwrp := pr0) (pr_qfwgamjs := pr8) (ev_eivanbct := ev0)
        (pr_obofuzfz := pr1) (pr_mkyihnzl := pr9) (ev_tntdione := ev1)
        (pr_hjgthcwx := pr2) (pr_zfjaetll := pr10) (ev_vmctzhlb := ev2)
        (pr_fioqavae := pr3) (pr_gaktyhno := pr11) (ev_avlhnzjc := ev3)
        (pr_yjarziwq := pr4) (pr_burzeget := pr12) (ev_ldgkpcww := ev4)
        (pr_hzyowqlj := pr5) (pr_wzbkbmxq := pr13) (ev_udyyazlz := ev5)
        (pr_mrczlzpg := pr6) (pr_dfrejsih := pr14) (ev_uezofdbl := ev6)
        (pr_vkzelvai := pr7) (pr_uzfksbwl := pr15) (ev_traeuqin := ev7)
        (he_vlxpmxsg := hr) (he_yfauhqhw := hh) .. =>
      subst hr hh
      obtain ⟨rfl, rfl⟩ := cij_spec ev_cij
      let s1 := Aiur.Library.Blake3.compressInnerJ s m
      obtain rfl := ok_inj ((proj_stateV_lo s1 m 0 (by decide)).symm.trans pr0)
      obtain rfl := ok_inj ((proj_stateV_lo s1 m 8 (by decide)).symm.trans pr8)
      obtain rfl := ok_inj ((proj_stateV_lo s1 m 1 (by decide)).symm.trans pr1)
      obtain rfl := ok_inj ((proj_stateV_lo s1 m 9 (by decide)).symm.trans pr9)
      obtain rfl := ok_inj ((proj_stateV_lo s1 m 2 (by decide)).symm.trans pr2)
      obtain rfl := ok_inj ((proj_stateV_lo s1 m 10 (by decide)).symm.trans pr10)
      obtain rfl := ok_inj ((proj_stateV_lo s1 m 3 (by decide)).symm.trans pr3)
      obtain rfl := ok_inj ((proj_stateV_lo s1 m 11 (by decide)).symm.trans pr11)
      obtain rfl := ok_inj ((proj_stateV_lo s1 m 4 (by decide)).symm.trans pr4)
      obtain rfl := ok_inj ((proj_stateV_lo s1 m 12 (by decide)).symm.trans pr12)
      obtain rfl := ok_inj ((proj_stateV_lo s1 m 5 (by decide)).symm.trans pr5)
      obtain rfl := ok_inj ((proj_stateV_lo s1 m 13 (by decide)).symm.trans pr13)
      obtain rfl := ok_inj ((proj_stateV_lo s1 m 6 (by decide)).symm.trans pr6)
      obtain rfl := ok_inj ((proj_stateV_lo s1 m 14 (by decide)).symm.trans pr14)
      obtain rfl := ok_inj ((proj_stateV_lo s1 m 7 (by decide)).symm.trans pr7)
      obtain rfl := ok_inj ((proj_stateV_lo s1 m 15 (by decide)).symm.trans pr15)
      obtain ⟨rfl, rfl⟩ := u32_xor ev0
      obtain ⟨rfl, rfl⟩ := u32_xor ev1
      obtain ⟨rfl, rfl⟩ := u32_xor ev2
      obtain ⟨rfl, rfl⟩ := u32_xor ev3
      obtain ⟨rfl, rfl⟩ := u32_xor ev4
      obtain ⟨rfl, rfl⟩ := u32_xor ev5
      obtain ⟨rfl, rfl⟩ := u32_xor ev6
      obtain ⟨rfl, rfl⟩ := u32_xor ev7
      refine ⟨?_, rfl⟩
      first
      | rfl
      | (simp only [vecV, compressRounds, Aiur.Library.Blake3.finalizeState, List.ofFn_succ,
          List.ofFn_zero, Vector.getElem_ofFn]; rfl)
      | (simp [vecV, compressRounds, Aiur.Library.Blake3.finalizeState, List.ofFn_succ]; done)
    | .other (hne_wcyktvnc := hne) .. =>
      exact absurd (by rw [show k = 3 by omega]; simp) hne
  | n + 1, k, s, m, stage, state, r, h, h', cs, hk, hst, hs, ev => by
    subst hst hs
    match «Blake3::compress».obs ev with
    | .n3 (hv_gzlcrgnw := hv) .. =>
      exact absurd (natCast_three_inj (by omega) (Value.field.inj hv)) (by omega)
    | .other (ev_dvofuqkd := ev_cij1)
        (pr_sgqwmyus := pr1_0) (up_xzpdfarf := up1_0)
        (pr_pndutyrr := pr1_1) (up_slfzhdpx := up1_1)
        (pr_bxpolqud := pr1_2) (up_wsfuzhfm := up1_2)
        (pr_emizxcqn := pr1_3) (up_xblbnued := up1_3)
        (pr_xzujbylr := pr1_4) (up_rwahsmou := up1_4)
        (pr_lnxhnhrd := pr1_5) (up_qqubcvhq := up1_5)
        (pr_hvjojxdj := pr1_6) (up_jscbfxyw := up1_6)
        (pr_oaqvodci := pr1_7) (up_moxtlxdi := up1_7)
        (pr_vvosxcop := pr1_8) (up_qykirevw := up1_8)
        (pr_bfskddqp := pr1_9) (up_hsuajdsb := up1_9)
        (pr_wuwpcbuu := pr1_10) (up_vnzlavqv := up1_10)
        (pr_sfatmnvo := pr1_11) (up_hvltbocb := up1_11)
        (pr_fdtnsydw := pr1_12) (up_eeiizmdg := up1_12)
        (pr_gictyovo := pr1_13) (up_bnydasqr := up1_13)
        (pr_ldnsrrez := pr1_14) (up_axypzgzn := up1_14)
        (pr_msfffviz := pr1_15) (up_rabiteud := up1_15)
        (ev_hrylbewr := ev_cij2)
        (pr_ugxzlhyq := pr2_0) (up_qpqqgspo := up2_0)
        (pr_usfpkqut := pr2_1) (up_oldrnsbq := up2_1)
        (pr_bakjnyeb := pr2_2) (up_pibrrdif := up2_2)
        (pr_jequrpzo := pr2_3) (up_abnsggug := up2_3)
        (pr_zhctjbrh := pr2_4) (up_zpytthqk := up2_4)
        (pr_ikgxoafb := pr2_5) (up_xcjesrbn := up2_5)
        (pr_iibeucwm := pr2_6) (up_kwbjymhb := up2_6)
        (pr_gkvokumf := pr2_7) (up_eevnwvxd := up2_7)
        (pr_hgzynked := pr2_8) (up_ufogrewt := up2_8)
        (pr_iszgjjug := pr2_9) (up_elvfkxvk := up2_9)
        (pr_wownnrhg := pr2_10) (up_wziwovxw := up2_10)
        (pr_ldsuuiuo := pr2_11) (up_vadvnjyh := up2_11)
        (pr_tsswjcdu := pr2_12) (up_djgiyexu := up2_12)
        (pr_ypkhuztl := pr2_13) (up_lxhluajx := up2_13)
        (pr_tldtxcku := pr2_14) (up_quardhga := up2_14)
        (pr_crnndaqj := pr2_15) (up_mtwijpxk := up2_15)
        (op899 := op899) (ev883 := ev883) .. =>
      obtain ⟨rfl, rfl⟩ := cij_spec ev_cij1
      have hst1 := permute16_inv pr1_0 up1_0 pr1_1 up1_1 pr1_2 up1_2 pr1_3 up1_3
        pr1_4 up1_4 pr1_5 up1_5 pr1_6 up1_6 pr1_7 up1_7
        pr1_8 up1_8 pr1_9 up1_9 pr1_10 up1_10 pr1_11 up1_11
        pr1_12 up1_12 pr1_13 up1_13 pr1_14 up1_14 pr1_15 up1_15
      rw [hst1] at ev_cij2 pr2_0 pr2_1 pr2_2 pr2_3 pr2_4 pr2_5 pr2_6 pr2_7
      rw [hst1] at pr2_8 pr2_9 pr2_10 pr2_11 pr2_12 pr2_13 pr2_14 pr2_15
      obtain ⟨rfl, rfl⟩ := cij_spec ev_cij2
      have hst2 := permute16_inv pr2_0 up2_0 pr2_1 up2_1 pr2_2 up2_2 pr2_3 up2_3
        pr2_4 up2_4 pr2_5 up2_5 pr2_6 up2_6 pr2_7 up2_7
        pr2_8 up2_8 pr2_9 up2_9 pr2_10 up2_10 pr2_11 up2_11
        pr2_12 up2_12 pr2_13 up2_13 pr2_14 up2_14 pr2_15 up2_15
      obtain rfl := binop_add op899
      have ih := compress_spec n (k := k + 1)
        (s := Aiur.Library.Blake3.compressInnerJ (Aiur.Library.Blake3.compressInnerJ s m) (Aiur.Library.Blake3.permute m))
        (m := Aiur.Library.Blake3.permute (Aiur.Library.Blake3.permute m))
        (by omega) (by first | simp | (push_cast; rfl)) hst2 ev883
      have h2 : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by omega
      rw [h2]
      exact ⟨ih.1, ih.2⟩

/-! ## `Blake3::compress_init` -/

/-- Byte `i` of a 64-bit counter. -/
def u64b (c : UInt64) (i : Nat) : UInt8 := (c.toNat / 256 ^ i).toUInt8

/-- **A 64-bit counter** (`UInt64::U64 = [U8; 8]`) as IxVM holds it. -/
def u64v (c : UInt64) : SourceValue F := .tuple (List.ofFn fun i : Fin 8 => bv (u64b c i))

theorem u64b_toNat (c : UInt64) (i : Nat) : (u64b c i).toNat = c.toNat / 256 ^ i % 256 := by
  simp [u64b, Nat.toUInt8_eq, UInt8.toNat_ofNat']

theorem lo_word (c : UInt64) :
    wordOfBytes (u64b c 0) (u64b c 1) (u64b c 2) (u64b c 3) = c.toUInt32 := by
  apply UInt32.ext
  rw [wordOfBytes_toNat, UInt64.toNat_toUInt32]
  simp only [u64b_toNat, Aiur.Library.U32.pack]
  first
  | (norm_num; omega)
  | omega
  | (simp; omega)

theorem hi_word (c : UInt64) :
    wordOfBytes (u64b c 4) (u64b c 5) (u64b c 6) (u64b c 7) = (c >>> 32).toUInt32 := by
  apply UInt32.ext
  rw [wordOfBytes_toNat, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight]
  have hshift : (32 : UInt64).toNat % 64 = 32 := by decide
  rw [hshift, Nat.shiftRight_eq_div_pow]
  simp only [u64b_toNat, Aiur.Library.U32.pack]
  first
  | (norm_num; omega)
  | omega
  | (simp; omega)

theorem small_word {n : Nat} (hn : n < 256) :
    (.tuple [.field (n : F), .field 0, .field 0, .field 0] : SourceValue F) = wv n.toUInt32 := by
  have e : wordOfBytes (UInt8.ofNat n) 0 0 0 = n.toUInt32 := by
    apply UInt32.ext
    rw [wordOfBytes_toNat, toNat_ofNat_lt hn]
    simp only [Aiur.Library.U32.pack]
    first
    | (simp; omega)
    | (simp; done)
    | (rw [Nat.toUInt32_eq, UInt32.toNat_ofNat']; simp; omega)
  rw [← e, wv_wordOfBytes, w4]
  simp [bv_ofNat hn]

theorem u8_fromField_lit {x : Nat} (hx : x < 256) {r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)} (ev : ObsFn W "UInt8::from_field" [.field (x : F)] h r h' cs) :
    r = .field (x : F) ∧ h' = h := by
  obtain ⟨rfl, rfl⟩ := obs_map_row fromField_none (fromField_row hx) ev
  exact ⟨by simp [Constant.toValue, Value.mapAddress], rfl⟩

/-- **`Blake3::compress_init`** is `Blake3.Pure.compress` of its chaining value, block,
counter, block length and flags (the last two checked bytes). -/
theorem compress_init_spec {cv : Blake3.Pure.CV} {m : Blake3.Pure.Block} {c : UInt64}
    {len fl : Nat} (hlen : len < 256) (hfl : fl < 256) {r : SourceValue F} {h h' : Heap F}
    {cs : List (Call F)}
    (ev : ObsFn W "Blake3::compress_init" [vecV cv, vecV m, u64v c, .field (len : F), .field (fl : F)]
      h r h' cs) :
    r = vecV (Blake3.Pure.compress cv m c len.toUInt32 fl.toUInt32) ∧ h' = h := by
  obtain ⟨v1, m2, cs12, v15, v27, v39, v51, v63, m64, cs74, v77, v88, m89, cs99, v102, v113, m114,
    cs124, v136, m141, cs149, v178, m179, cs189, v201, m206, cs214, v263, v264, v265, v266, v267,
    v268, v269, v270, v279, v280, v281, v282, v283, v284, v285, v286, v287, v288, v289, v290, v291,
    v292, v293, v294, cs595, ev14, pr25, pr37, pr49, pr61, sl86, ev76, sl111, ev101, ev151, ev126,
    ev216, ev191, pr303, pr313, pr323, pr333, pr343, pr353, pr363, pr373, pr439, pr449, pr459,
    pr469, pr479, pr489, pr499, pr509, pr519, pr529, pr539, pr549, pr559, pr569, pr579, pr589,
    ev597, -⟩ := «Blake3::compress_init».obs ev
  obtain ⟨rfl, rfl⟩ := iv_src ev14
  obtain rfl := ok_inj ((proj_vecV Blake3.Pure.iv 0 (by decide)).symm.trans pr25)
  obtain rfl := ok_inj ((proj_vecV Blake3.Pure.iv 1 (by decide)).symm.trans pr37)
  obtain rfl := ok_inj ((proj_vecV Blake3.Pure.iv 2 (by decide)).symm.trans pr49)
  obtain rfl := ok_inj ((proj_vecV Blake3.Pure.iv 3 (by decide)).symm.trans pr61)
  obtain rfl := ok_inj ((show sliceValue (u64v c : SourceValue F) 0 (some 4) =
    .ok (w4 (u64b c 0) (u64b c 1) (u64b c 2) (u64b c 3)) from rfl).symm.trans sl86)
  obtain ⟨rfl, rfl⟩ := u32_fromBytes ev76
  obtain rfl := ok_inj ((show sliceValue (u64v c : SourceValue F) 4 (some 8) =
    .ok (w4 (u64b c 4) (u64b c 5) (u64b c 6) (u64b c 7)) from rfl).symm.trans sl111)
  obtain ⟨rfl, rfl⟩ := u32_fromBytes ev101
  obtain ⟨rfl, rfl⟩ := u8_fromField_lit hlen ev151
  obtain ⟨rfl, rfl⟩ := u32_fromBytes ev126
  obtain ⟨rfl, rfl⟩ := u8_fromField_lit hfl ev216
  obtain ⟨rfl, rfl⟩ := u32_fromBytes ev191
  obtain rfl := ok_inj ((proj_vecV cv 0 (by decide)).symm.trans pr303)
  obtain rfl := ok_inj ((proj_vecV cv 1 (by decide)).symm.trans pr313)
  obtain rfl := ok_inj ((proj_vecV cv 2 (by decide)).symm.trans pr323)
  obtain rfl := ok_inj ((proj_vecV cv 3 (by decide)).symm.trans pr333)
  obtain rfl := ok_inj ((proj_vecV cv 4 (by decide)).symm.trans pr343)
  obtain rfl := ok_inj ((proj_vecV cv 5 (by decide)).symm.trans pr353)
  obtain rfl := ok_inj ((proj_vecV cv 6 (by decide)).symm.trans pr363)
  obtain rfl := ok_inj ((proj_vecV cv 7 (by decide)).symm.trans pr373)
  obtain rfl := ok_inj ((proj_vecV m 0 (by decide)).symm.trans pr439)
  obtain rfl := ok_inj ((proj_vecV m 1 (by decide)).symm.trans pr449)
  obtain rfl := ok_inj ((proj_vecV m 2 (by decide)).symm.trans pr459)
  obtain rfl := ok_inj ((proj_vecV m 3 (by decide)).symm.trans pr469)
  obtain rfl := ok_inj ((proj_vecV m 4 (by decide)).symm.trans pr479)
  obtain rfl := ok_inj ((proj_vecV m 5 (by decide)).symm.trans pr489)
  obtain rfl := ok_inj ((proj_vecV m 6 (by decide)).symm.trans pr499)
  obtain rfl := ok_inj ((proj_vecV m 7 (by decide)).symm.trans pr509)
  obtain rfl := ok_inj ((proj_vecV m 8 (by decide)).symm.trans pr519)
  obtain rfl := ok_inj ((proj_vecV m 9 (by decide)).symm.trans pr529)
  obtain rfl := ok_inj ((proj_vecV m 10 (by decide)).symm.trans pr539)
  obtain rfl := ok_inj ((proj_vecV m 11 (by decide)).symm.trans pr549)
  obtain rfl := ok_inj ((proj_vecV m 12 (by decide)).symm.trans pr559)
  obtain rfl := ok_inj ((proj_vecV m 13 (by decide)).symm.trans pr569)
  obtain rfl := ok_inj ((proj_vecV m 14 (by decide)).symm.trans pr579)
  obtain rfl := ok_inj ((proj_vecV m 15 (by decide)).symm.trans pr589)
  have hst : (.tuple [wv cv[0], wv cv[1], wv cv[2], wv cv[3], wv cv[4], wv cv[5], wv cv[6], wv cv[7],
      wv Blake3.Pure.iv[0], wv Blake3.Pure.iv[1], wv Blake3.Pure.iv[2], wv Blake3.Pure.iv[3],
      w4 (u64b c 0) (u64b c 1) (u64b c 2) (u64b c 3), w4 (u64b c 4) (u64b c 5) (u64b c 6) (u64b c 7),
      .tuple [.field (len : F), .field 0, .field 0, .field 0],
      .tuple [.field (fl : F), .field 0, .field 0, .field 0],
      wv m[0], wv m[1], wv m[2], wv m[3], wv m[4], wv m[5], wv m[6], wv m[7], wv m[8], wv m[9],
      wv m[10], wv m[11], wv m[12], wv m[13], wv m[14], wv m[15]] : SourceValue F) =
      stateV (Blake3.Pure.initialWords cv c len.toUInt32 fl.toUInt32) m := by
    rw [small_word hlen, small_word hfl, ← wv_wordOfBytes (u64b c 0), lo_word,
      ← wv_wordOfBytes (u64b c 4), hi_word]
    rfl
  have spec := compress_spec 3 (k := 0) (by rfl) (by simp) hst ev597
  refine ⟨?_, spec.2⟩
  rw [spec.1, compressRounds_seven, Aiur.Library.Blake3.compress_spec]

end IxVM.Refinement.Ingress
