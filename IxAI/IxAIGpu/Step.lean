import IxAIGpu.Reduce
import IxAICore.Gather

/-!
# The GPU step, kernel by kernel, and its equality with `Model.step`

`gpuStep g lr m batch` is the algorithm of `gpu/cuda/step.cu`: device buffers are read by index
(`Mat`, `Vec`, zero outside the stored range), every kernel computes one output element per warp
with `blockReduce g`, and the host assembles the parameters from the final buffers. Each
definition below names the kernel that implements it.

`gpuStep_eq`: for every launch geometry, on a well-shaped model and batch, `gpuStep` is
`Model.step`. `gpuTrain_eq_train`: folding it over the gathered batches is `IxAICore.train`.
-/

namespace IxAIGpu
open IxAICore Finset

/-- A device matrix, read at `(row, column)`. -/
abbrev Mat := Nat → Nat → Int
/-- A device vector. -/
abbrev Vec := Nat → Int

/-- The host's upload of a list of rows: row-major, zero outside. -/
def Mat.ofRows (rows : List (List Fx)) : Mat := fun r c => ((rows.getD r []).getD c Fx.zero).raw
def Vec.ofList (v : List Fx) : Vec := fun i => (v.getD i Fx.zero).raw
/-- The host's download of `n` entries. -/
def Vec.toList (n : Nat) (v : Vec) : List Fx := (List.range n).map fun i => ⟨v i⟩
def Mat.toRows (rows cols : Nat) (a : Mat) : List (List Fx) :=
  (List.range rows).map fun r => Vec.toList cols (a r)

def relu (v : Int) : Int := if v > 0 then v else 0

/-- `transpose_kernel`. -/
def transposeK (a : Mat) : Mat := fun r c => a c r

/-- `hidden_kernel`, the exact sum (an `fx.shr8` key): `Σ_i w1[j][i] · x[b][i]`. -/
def hiddenKey (g : Geometry) (nI : Nat) (W1 X : Mat) : Mat :=
  fun b j => blockReduce g (fun i => W1 j i * X b i) nI

/-- `hidden_kernel`: `z[b][j]`. -/
def hiddenZ (g : Geometry) (nI : Nat) (W1 : Mat) (B1 : Vec) (X : Mat) : Mat :=
  fun b j => (hiddenKey g nI W1 X b j >>> (8 : Nat)) + B1 j

/-- `output_kernel`, the exact sum: `Σ_j w2[k][j] · h[b][j]`. -/
def outputKey (g : Geometry) (nH : Nat) (W2 Hm : Mat) : Mat :=
  fun b k => blockReduce g (fun j => W2 k j * Hm b j) nH

/-- `output_kernel`: `dout[b][k]`. -/
def outputDelta (g : Geometry) (nH : Nat) (W2 : Mat) (B2 : Vec) (Hm T : Mat) : Mat :=
  fun b k => (outputKey g nH W2 Hm b k >>> (8 : Nat)) + B2 k - T b k

/-- `dz_kernel`, the exact sum: `Σ_k w2T[j][k] · dout[b][k]`. -/
def dzKey (g : Geometry) (nO : Nat) (W2T Dout : Mat) : Mat :=
  fun b j => blockReduce g (fun k => W2T j k * Dout b k) nO

/-- `dz_kernel`: `dz[b][j]`. -/
def dzK (g : Geometry) (nO : Nat) (W2T Z Dout : Mat) : Mat :=
  fun b j => if Z b j > 0 then dzKey g nO W2T Dout b j >>> (8 : Nat) else 0

/-- `update_w_kernel`, the gradient sum: `Σ_b gT[r][b] · aT[c][b]`. -/
def gradKey (g : Geometry) (nB : Nat) (GT AT : Mat) : Mat :=
  fun r c => blockReduce g (fun b => GT r b * AT c b) nB

/-- `update_w_kernel`: `w[r][c] − (lr · (grad >>> 8)) >>> 8`. -/
def updateW (g : Geometry) (lr : Int) (nB : Nat) (W GT AT : Mat) : Mat :=
  fun r c => W r c - ((lr * (gradKey g nB GT AT r c >>> (8 : Nat))) >>> (8 : Nat))

/-- `update_b_kernel`: `b[r] − (lr · Σ_b gT[r][b]) >>> 8`. -/
def updateB (g : Geometry) (lr : Int) (nB : Nat) (Bv : Vec) (GT : Mat) : Vec :=
  fun r => Bv r - ((lr * blockReduce g (fun b => GT r b) nB) >>> (8 : Nat))

/-- `ixai_gpu_step`: the kernels in launch order. -/
def gpuStep (g : Geometry) (lr : Fx) (m : Model) (batch : List (List Fx × List Fx)) : Model :=
  if batch.isEmpty then m else
  let nB := batch.length
  let nH := m.b1.length
  let nI := (getD m.w1 0 []).length
  let nO := m.b2.length
  let W1 := Mat.ofRows m.w1
  let B1 := Vec.ofList m.b1
  let W2 := Mat.ofRows m.w2
  let B2 := Vec.ofList m.b2
  let X := Mat.ofRows (batch.map (·.1))
  let T := Mat.ofRows (batch.map (·.2))
  let Z := hiddenZ g nI W1 B1 X
  let Hm : Mat := fun b j => relu (Z b j)
  let Dout := outputDelta g nH W2 B2 Hm T
  let Dz := dzK g nO (transposeK W2) Z Dout
  { w1 := Mat.toRows nH nI (updateW g lr.raw nB W1 (transposeK Dz) (transposeK X))
    b1 := Vec.toList nH (updateB g lr.raw nB B1 (transposeK Dz))
    w2 := Mat.toRows nO nH (updateW g lr.raw nB W2 (transposeK Dout) (transposeK Hm))
    b2 := Vec.toList nO (updateB g lr.raw nB B2 (transposeK Dout)) }

/-- Training on the GPU: the step folded over gathered batches. -/
def gpuTrain (g : Geometry) (lr : Fx) (init : Model) (batches : List (List (List Fx × List Fx))) :
    Model :=
  batches.foldl (gpuStep g lr) init

/-! ## Shapes -/

/-- `nI` inputs, `m.b1.length` hidden units, `m.b2.length` outputs. -/
structure Shaped (m : Model) (nI : Nat) : Prop where
  w1_len : m.w1.length = m.b1.length
  w1_rows : ∀ r ∈ m.w1, r.length = nI
  width : (getD m.w1 0 []).length = nI
  w2_len : m.w2.length = m.b2.length
  w2_rows : ∀ r ∈ m.w2, r.length = m.b1.length

def BatchShaped (m : Model) (nI : Nat) (batch : List (List Fx × List Fx)) : Prop :=
  ∀ e ∈ batch, e.1.length = nI ∧ e.2.length = m.b2.length

/-! ## Lists as index functions -/

theorem getD_eq (l : List α) (i : Nat) (d : α) : getD l i d = l.getD i d := by
  induction l generalizing i with
  | nil => simp [IxAICore.getD]
  | cons a l ih => cases i <;> simp [IxAICore.getD, ih]

theorem list_eq_toList (v : List Fx) : v = Vec.toList v.length (Vec.ofList v) := by
  apply List.ext_getElem (by simp [Vec.toList])
  intro i h1 h2
  simp only [Vec.toList, Vec.ofList, List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h1, Option.getD_some]

theorem rows_eq_toRows (rows : List (List Fx)) (n : Nat) (h : ∀ r ∈ rows, r.length = n) :
    rows = Mat.toRows rows.length n (Mat.ofRows rows) := by
  apply List.ext_getElem (by simp [Mat.toRows])
  intro r h1 h2
  simp only [Mat.toRows, List.getElem_map, List.getElem_range]
  have hr := h _ (List.getElem_mem h1)
  conv => lhs; rw [list_eq_toList rows[r]]
  rw [hr]
  congr 1
  funext c
  simp [Mat.ofRows, Vec.ofList, List.getElem?_eq_getElem h1]

theorem getD_toList (n : Nat) (v : Vec) (i : Nat) (h : i < n) :
    (Vec.toList n v).getD i Fx.zero = ⟨v i⟩ := by
  simp [Vec.toList, h]

theorem transposeN_eq (n : Nat) (rows : List (List Fx)) :
    transposeN n rows = (List.range n).map fun i => rows.map fun r => r.getD i Fx.zero := by
  induction n generalizing rows with
  | zero => rfl
  | succ n ih =>
    rw [transposeN, ih, List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map]
    congr 1
    · apply List.map_congr_left; intro r _; cases r <;> rfl
    · apply List.map_congr_left; intro i _
      simp only [Function.comp]
      apply List.map_congr_left; intro r _; cases r <;> simp

theorem transposeN_toRows (R C : Nat) (a : Mat) :
    transposeN C (Mat.toRows R C a) = Mat.toRows C R (transposeK a) := by
  rw [transposeN_eq]
  simp only [Mat.toRows, Vec.toList, List.map_map]
  apply List.map_congr_left; intro c hc
  apply List.map_congr_left; intro r _
  simp only [Function.comp]
  rw [← Vec.toList, getD_toList _ _ _ (by simpa using hc)]
  rfl

theorem zipWith_range {α β γ : Type} (n : Nat) (f : α → β → γ) (a : Nat → α) (b : Nat → β) :
    List.zipWith f ((List.range n).map a) ((List.range n).map b) = (List.range n).map fun i => f (a i) (b i) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

theorem dotRaw_toList (n : Nat) (a b : Vec) :
    Fx.dotRaw (Vec.toList n a) (Vec.toList n b) = ∑ i ∈ range n, a i * b i := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    have h := ih (fun i => a (i + 1)) (fun i => b (i + 1))
    simp only [Vec.toList, List.range_succ_eq_map, List.map_cons, List.map_map, Function.comp_def,
      Nat.succ_eq_add_one] at h ⊢
    rw [Fx.dotRaw, Finset.sum_range_succ']
    rw [h]; ring

theorem sumRaw_toList (n : Nat) (a : Vec) : Fx.sumRaw (Vec.toList n a) = ∑ i ∈ range n, a i := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    have h := ih (fun i => a (i + 1))
    simp only [Vec.toList, List.range_succ_eq_map, List.map_cons, List.map_map, Function.comp_def,
      Nat.succ_eq_add_one] at h ⊢
    rw [Fx.sumRaw, Finset.sum_range_succ']
    rw [h]; ring

theorem dotRaw_range (n : Nat) (a b : Vec) :
    Fx.dotRaw ((List.range n).map fun i => (⟨a i⟩ : Fx)) ((List.range n).map fun i => ⟨b i⟩) =
      ∑ i ∈ range n, a i * b i := by
  simpa only [Vec.toList] using dotRaw_toList n a b

theorem sumRaw_range (n : Nat) (a : Vec) :
    Fx.sumRaw ((List.range n).map fun i => (⟨a i⟩ : Fx)) = ∑ i ∈ range n, a i := by
  simpa only [Vec.toList] using sumRaw_toList n a

theorem dot_range (n : Nat) (a b : Vec) :
    Fx.dot ((List.range n).map fun i => (⟨a i⟩ : Fx)) ((List.range n).map fun i => ⟨b i⟩) =
      ⟨(∑ i ∈ range n, a i * b i) >>> (8 : Nat)⟩ := by
  have := dotRaw_toList n a b
  simp only [Vec.toList] at this
  simp [Fx.dot, this]

theorem sum_range (n : Nat) (a : Vec) :
    Fx.sum ((List.range n).map fun i => (⟨a i⟩ : Fx)) = ⟨∑ i ∈ range n, a i⟩ := by
  have := sumRaw_toList n a
  simp only [Vec.toList] at this
  simp [Fx.sum, this]

theorem transposeN_range (R C : Nat) (a : Mat) :
    transposeN C ((List.range R).map fun r => (List.range C).map fun c => (⟨a r c⟩ : Fx)) =
      (List.range C).map fun c => (List.range R).map fun r => ⟨a r c⟩ := by
  have := transposeN_toRows R C a
  simpa only [Mat.toRows, Vec.toList, transposeK] using this

theorem relu_mk (v : Int) : Fx.relu ⟨v⟩ = ⟨relu v⟩ := by
  simp only [Fx.relu, relu]; split <;> rfl

theorem pos_mk (v : Int) : Fx.pos ⟨v⟩ = decide (v > 0) := rfl

theorem ite_raw (c : Prop) [Decidable c] (a b : Fx) : (if c then a else b).raw = if c then a.raw else b.raw := by
  split <;> rfl

theorem w1_eq (m : Model) (nI : Nat) (hm : Shaped m nI) :
    m.w1 = Mat.toRows m.b1.length nI (Mat.ofRows m.w1) := by
  conv => lhs; rw [rows_eq_toRows m.w1 nI hm.w1_rows]
  rw [hm.w1_len]

theorem w2_eq (m : Model) (nI : Nat) (hm : Shaped m nI) :
    m.w2 = Mat.toRows m.b2.length m.b1.length (Mat.ofRows m.w2) := by
  conv => lhs; rw [rows_eq_toRows m.w2 _ hm.w2_rows]
  rw [hm.w2_len]

theorem batch_eq (m : Model) (nI : Nat) (batch : List (List Fx × List Fx)) (hb : BatchShaped m nI batch) :
    batch = (List.range batch.length).map fun b =>
      (Vec.toList nI (Mat.ofRows (batch.map (·.1)) b), Vec.toList m.b2.length (Mat.ofRows (batch.map (·.2)) b)) := by
  apply List.ext_getElem (by simp)
  intro b h1 h2
  simp only [List.getElem_map, List.getElem_range]
  have he := hb _ (List.getElem_mem h1)
  have hx : (batch.map (·.1)).getD b [] = batch[b].1 := by
    simp [List.getElem?_eq_getElem h1]
  have ht : (batch.map (·.2)).getD b [] = batch[b].2 := by
    simp [List.getElem?_eq_getElem h1]
  have e1 := list_eq_toList batch[b].1
  have e2 := list_eq_toList batch[b].2
  rw [he.1] at e1
  rw [he.2] at e2
  ext1
  · unfold Mat.ofRows; rw [hx]; exact e1
  · unfold Mat.ofRows; rw [ht]; exact e2

/-! ## The step -/

/-- The step on index functions: what both `gpuStep` and `Model.step` compute. -/
def closedStep (lr : Int) (nB nI nH nO : Nat) (W1 : Mat) (B1 : Vec) (W2 : Mat) (B2 : Vec)
    (X T : Mat) : Model :=
  let z : Mat := fun b j => ((∑ i ∈ range nI, W1 j i * X b i) >>> (8 : Nat)) + B1 j
  let h : Mat := fun b j => relu (z b j)
  let dout : Mat := fun b k => ((∑ j ∈ range nH, W2 k j * h b j) >>> (8 : Nat)) + B2 k - T b k
  let dz : Mat := fun b j => if z b j > 0 then (∑ k ∈ range nO, W2 k j * dout b k) >>> (8 : Nat) else 0
  { w1 := Mat.toRows nH nI fun r c => W1 r c - ((lr * ((∑ b ∈ range nB, dz b r * X b c) >>> (8 : Nat))) >>> (8 : Nat))
    b1 := Vec.toList nH fun r => B1 r - ((lr * ∑ b ∈ range nB, dz b r) >>> (8 : Nat))
    w2 := Mat.toRows nO nH fun r c => W2 r c - ((lr * ((∑ b ∈ range nB, dout b r * h b c) >>> (8 : Nat))) >>> (8 : Nat))
    b2 := Vec.toList nO fun r => B2 r - ((lr * ∑ b ∈ range nB, dout b r) >>> (8 : Nat)) }

theorem gpuStep_closed (g : Geometry) (lr : Fx) (m : Model) (batch : List (List Fx × List Fx))
    (hne : batch.isEmpty = false) :
    gpuStep g lr m batch = closedStep lr.raw batch.length (getD m.w1 0 []).length m.b1.length
      m.b2.length (Mat.ofRows m.w1) (Vec.ofList m.b1) (Mat.ofRows m.w2) (Vec.ofList m.b2)
      (Mat.ofRows (batch.map (·.1))) (Mat.ofRows (batch.map (·.2))) := by
  unfold gpuStep hiddenZ hiddenKey outputDelta outputKey dzK dzKey updateW updateB gradKey transposeK
  simp only [hne, Bool.false_eq_true, ↓reduceIte, blockReduce_eq]
  rfl

theorem map_range_eq {α β : Type} {n : Nat} {f : α → β} {F : Nat → α} {D : Nat → β}
    (h : ∀ b < n, f (F b) = D b) : ((List.range n).map F).map f = (List.range n).map D := by
  rw [List.map_map]
  apply List.map_congr_left
  intro b hb
  exact h b (List.mem_range.mp hb)

theorem step_closed (lr : Fx) (m : Model) (nI nB : Nat) (hm : Shaped m nI) (X T : Mat) (hB : 0 < nB) :
    m.step lr ((List.range nB).map fun b => (Vec.toList nI (X b), Vec.toList m.b2.length (T b))) =
      closedStep lr.raw nB nI m.b1.length m.b2.length (Mat.ofRows m.w1) (Vec.ofList m.b1)
        (Mat.ofRows m.w2) (Vec.ofList m.b2) X T := by
  have hw1 := w1_eq m nI hm
  have hw2 := w2_eq m nI hm
  have hb1 := list_eq_toList m.b1
  have hb2 := list_eq_toList m.b2
  have hwidth := hm.width
  obtain ⟨w1, b1, w2, b2⟩ := m
  simp only at hw1 hw2 hb1 hb2 hwidth ⊢
  unfold Model.step
  obtain ⟨k, rfl⟩ : ∃ k, nB = k + 1 := ⟨nB - 1, by omega⟩
  split
  · rename_i h
    simp [List.range_succ_eq_map] at h
  simp only [hwidth]
  generalize Mat.ofRows w1 = W1 at hw1 ⊢
  generalize Vec.ofList b1 = B1 at hb1 ⊢
  generalize Mat.ofRows w2 = W2 at hw2 ⊢
  generalize Vec.ofList b2 = B2 at hb2 ⊢
  generalize b1.length = nH at hb1 hw1 hw2 ⊢
  generalize b2.length = nO at hb2 hw2 ⊢
  subst hw1 hw2 hb1 hb2
  simp only [Model.delta, Model.hidden, Mat.toRows, Vec.toList, List.map_map, Function.comp_def,
    zipWith_range, dot_range, sum_range, transposeN_range, closedStep, Fx.add, Fx.sub, Fx.mul, relu_mk,
    Fx.pos, decide_eq_true_eq, ite_raw, Fx.zero]

/-- **The GPU step is the spec's step**, for every launch geometry. -/
theorem gpuStep_eq (g : Geometry) (lr : Fx) (m : Model) (nI : Nat) (batch : List (List Fx × List Fx))
    (hm : Shaped m nI) (hb : BatchShaped m nI batch) : gpuStep g lr m batch = m.step lr batch := by
  cases hne : batch.isEmpty
  · rw [gpuStep_closed g lr m batch hne, hm.width]
    conv => rhs; rw [batch_eq m nI batch hb]
    rw [step_closed lr m nI batch.length hm _ _ (by cases batch <;> simp_all)]
  · simp [gpuStep, Model.step, hne]

theorem gpuStep_shaped (g : Geometry) (lr : Fx) (m : Model) (nI : Nat) (batch : List (List Fx × List Fx))
    (hm : Shaped m nI) :
    Shaped (gpuStep g lr m batch) nI ∧ (gpuStep g lr m batch).b2.length = m.b2.length := by
  cases hne : batch.isEmpty
  · rw [gpuStep_closed g lr m batch hne, hm.width]
    have hwidth := hm.width
    have hlen := hm.w1_len
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp only [closedStep, Mat.toRows, Vec.toList, List.length_map,
      List.length_range, List.mem_map, List.mem_range, forall_exists_index, and_imp]
    · intro r _ _ h; rw [← h]; simp
    · rw [getD_eq] at hwidth ⊢
      cases h : m.b1.length with
      | zero =>
        rw [h] at hlen
        rw [List.length_eq_zero_iff.mp hlen] at hwidth
        simp at hwidth
        simp [← hwidth]
      | succ n => simp
    · intro r _ _ h; rw [← h]; simp
  · simp only [gpuStep, hne, ↓reduceIte]
    exact ⟨hm, trivial⟩

/-- **Training on the GPU is training in the spec**, for every launch geometry, from a well-shaped
model over well-shaped batches. -/
theorem gpuTrain_eq (g : Geometry) (lr : Fx) (init : Model) (nI : Nat)
    (batches : List (List (List Fx × List Fx))) (hm : Shaped init nI)
    (hb : ∀ b ∈ batches, BatchShaped init nI b) :
    gpuTrain g lr init batches = batches.foldl (fun m b => m.step lr b) init := by
  induction batches generalizing init with
  | nil => rfl
  | cons b bs ih =>
    simp only [gpuTrain, List.foldl_cons] at ih ⊢
    have hb0 := hb b List.mem_cons_self
    obtain ⟨hm', hlen⟩ := gpuStep_shaped g lr init nI b hm
    rw [← gpuStep_eq g lr init nI b hm hb0]
    apply ih _ hm'
    intro b' h' e he
    rw [hlen]
    exact hb b' (List.mem_cons_of_mem _ h') e he

/-- `IxAICore.train` is the GPU fold over the gathered batches (`train_eq_foldl_gather`). -/
theorem train_eq_gpuTrain {σ : Type} [Inhabited σ] (g : Geometry) (s : Spec σ) (c : Config)
    (hm : Shaped (c.init s) s.numFeatures)
    (hb : ∀ b ∈ gather ((c.data s).map s.example) c.schedule (s.example default),
      BatchShaped (c.init s) s.numFeatures b) :
    train s c = gpuTrain g ⟨c.lrRaw⟩ (c.init s) (gather ((c.data s).map s.example) c.schedule (s.example default)) := by
  rw [train_eq_foldl_gather, gpuTrain_eq g _ _ _ _ hm hb]

end IxAIGpu
